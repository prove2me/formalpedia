-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T20:42:37.927413+00:00
-- url     : https://prove2.me/submissions/4680da81-30f7-4caa-9ee1-eb82b78bc1a0

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E118
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound1397_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound1399_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound1478_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical86 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw86 raw86Labels = mixedMoment B node1307 node1307Labels := by
  calc
    mixedMoment B raw86 raw86Labels = mixedMoment B raw86step0 raw86step0Labels := by
      have ha : raw86step0 = (fun i j => raw86 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw86step0 raw86; decide +kernel
      have hl : raw86step0Labels = raw86Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw86 raw86Labels permutation2 permutation5
    mixedMoment B raw86step0 raw86step0Labels = mixedMoment B raw86step1 raw86step1Labels := by
      have ha : raw86step1 = raw86step0 := by apply Matrix.ext; unfold raw86step1 raw86step0; decide +kernel
      have hl : raw86step0Labels = labelEmbedding1 ∘ raw86step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw86step0 raw86step0Labels raw86step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1307 node1307Labels := by rfl

theorem canonical87 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw87 raw87Labels = mixedMoment B node158 node158Labels := by
  calc
    mixedMoment B raw87 raw87Labels = mixedMoment B raw87step0 raw87step0Labels := by
      have ha : raw87step0 = (fun i j => raw87 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw87step0 raw87; decide +kernel
      have hl : raw87step0Labels = raw87Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw87 raw87Labels permutation2 permutation4
    _ = mixedMoment B node158 node158Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw132 raw132Labels = mixedMoment B node1413 node1413Labels := by
  calc
    mixedMoment B raw132 raw132Labels = mixedMoment B raw132step0 raw132step0Labels := by
      have ha : raw132step0 = (fun i j => raw132 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw132step0 raw132; decide +kernel
      have hl : raw132step0Labels = raw132Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw132 raw132Labels permutation8 permutation5
    mixedMoment B raw132step0 raw132step0Labels = mixedMoment B raw132step1 raw132step1Labels := by
      have ha : raw132step1 = raw132step0 := by apply Matrix.ext; unfold raw132step1 raw132step0; decide +kernel
      have hl : raw132step0Labels = labelEmbedding1 ∘ raw132step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw132step0 raw132step0Labels raw132step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1413 node1413Labels := by rfl

theorem canonical133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw133 raw133Labels = mixedMoment B node96 node96Labels := by
  calc
    mixedMoment B raw133 raw133Labels = mixedMoment B raw133step0 raw133step0Labels := by
      have ha : raw133step0 = (fun i j => raw133 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw133step0 raw133; decide +kernel
      have hl : raw133step0Labels = raw133Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw133 raw133Labels permutation8 permutation4
    _ = mixedMoment B node96 node96Labels := by rfl

theorem canonical136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw136 raw136Labels = mixedMoment B node1416 node1416Labels := by
  calc
    mixedMoment B raw136 raw136Labels = mixedMoment B raw136step0 raw136step0Labels := by
      have ha : raw136step0 = (fun i j => raw136 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw136step0 raw136; decide +kernel
      have hl : raw136step0Labels = raw136Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw136 raw136Labels permutation8 permutation5
    mixedMoment B raw136step0 raw136step0Labels = mixedMoment B raw136step1 raw136step1Labels := by
      have ha : raw136step1 = raw136step0 := by apply Matrix.ext; unfold raw136step1 raw136step0; decide +kernel
      have hl : raw136step0Labels = labelEmbedding1 ∘ raw136step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw136step0 raw136step0Labels raw136step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1416 node1416Labels := by rfl

theorem canonical137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw137 raw137Labels = mixedMoment B node94 node94Labels := by
  calc
    mixedMoment B raw137 raw137Labels = mixedMoment B raw137step0 raw137step0Labels := by
      have ha : raw137step0 = (fun i j => raw137 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw137step0 raw137; decide +kernel
      have hl : raw137step0Labels = raw137Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw137 raw137Labels permutation8 permutation4
    _ = mixedMoment B node94 node94Labels := by rfl

theorem canonical138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw138 raw138Labels = mixedMoment B node1417 node1417Labels := by
  calc
    mixedMoment B raw138 raw138Labels = mixedMoment B raw138step0 raw138step0Labels := by
      have ha : raw138step0 = (fun i j => raw138 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw138step0 raw138; decide +kernel
      have hl : raw138step0Labels = raw138Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw138 raw138Labels permutation8 permutation5
    mixedMoment B raw138step0 raw138step0Labels = mixedMoment B raw138step1 raw138step1Labels := by
      have ha : raw138step1 = raw138step0 := by apply Matrix.ext; unfold raw138step1 raw138step0; decide +kernel
      have hl : raw138step0Labels = labelEmbedding1 ∘ raw138step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw138step0 raw138step0Labels raw138step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1417 node1417Labels := by rfl

theorem canonical139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw139 raw139Labels = mixedMoment B node90 node90Labels := by
  calc
    mixedMoment B raw139 raw139Labels = mixedMoment B raw139step0 raw139step0Labels := by
      have ha : raw139step0 = (fun i j => raw139 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw139step0 raw139; decide +kernel
      have hl : raw139step0Labels = raw139Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw139 raw139Labels permutation8 permutation4
    _ = mixedMoment B node90 node90Labels := by rfl

theorem canonical176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw176 raw176Labels = mixedMoment B node1471 node1471Labels := by
  calc
    mixedMoment B raw176 raw176Labels = mixedMoment B raw176step0 raw176step0Labels := by
      have ha : raw176step0 = (fun i j => raw176 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw176step0 raw176; decide +kernel
      have hl : raw176step0Labels = raw176Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw176 raw176Labels permutation8 permutation5
    mixedMoment B raw176step0 raw176step0Labels = mixedMoment B raw176step1 raw176step1Labels := by
      have ha : raw176step1 = raw176step0 := by apply Matrix.ext; unfold raw176step1 raw176step0; decide +kernel
      have hl : raw176step0Labels = labelEmbedding1 ∘ raw176step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw176step0 raw176step0Labels raw176step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1471 node1471Labels := by rfl

theorem canonical177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw177 raw177Labels = mixedMoment B node53 node53Labels := by
  calc
    mixedMoment B raw177 raw177Labels = mixedMoment B raw177step0 raw177step0Labels := by
      have ha : raw177step0 = (fun i j => raw177 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw177step0 raw177; decide +kernel
      have hl : raw177step0Labels = raw177Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw177 raw177Labels permutation10 permutation6
    mixedMoment B raw177step0 raw177step0Labels = mixedMoment B raw177step1 raw177step1Labels := by
      have ha : raw177step1 = -raw177step0 := by apply Matrix.ext; change ∀ i j, raw177step1 i j = -(raw177step0 i j); unfold raw177step1 raw177step0; decide +kernel
      have hl : raw177step1Labels = raw177step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node53 node53Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical159
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20450 raw20450Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw20450 raw20450Labels = mixedMoment B raw20450step0 raw20450step0Labels := by
      have hz : ∀ j, raw20450 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20450step0 = (fun i j => raw20450 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20450step0 raw20450; decide +kernel
      have hl : raw20450step0Labels = raw20450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20450 raw20450Labels permutation434 hz
    mixedMoment B raw20450step0 raw20450step0Labels = mixedMoment B raw20450step1 raw20450step1Labels := by
      have ha : raw20450step1 = (fun i j => raw20450step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20450step1 raw20450step0; decide +kernel
      have hl : raw20450step1Labels = raw20450step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20450step0 raw20450step0Labels permutation32 permutation7
    mixedMoment B raw20450step1 raw20450step1Labels = mixedMoment B raw20450step2 raw20450step2Labels := by
      have ha : raw20450step2 = raw20450step1 := by apply Matrix.ext; unfold raw20450step2 raw20450step1; decide +kernel
      have hl : raw20450step1Labels = labelEmbedding1 ∘ raw20450step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20450step1 raw20450step1Labels raw20450step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1217 node1217Labels := by rfl

theorem canonical20451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20451 raw20451Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw20451 raw20451Labels = mixedMoment B raw20451step0 raw20451step0Labels := by
      have hz : ∀ j, raw20451 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20451step0 = (fun i j => raw20451 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20451step0 raw20451; decide +kernel
      have hl : raw20451step0Labels = raw20451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20451 raw20451Labels permutation346 hz
    mixedMoment B raw20451step0 raw20451step0Labels = mixedMoment B raw20451step1 raw20451step1Labels := by
      have ha : raw20451step1 = (fun i j => raw20451step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20451step1 raw20451step0; decide +kernel
      have hl : raw20451step1Labels = raw20451step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20451step0 raw20451step0Labels permutation32 permutation7
    mixedMoment B raw20451step1 raw20451step1Labels = mixedMoment B raw20451step2 raw20451step2Labels := by
      have ha : raw20451step2 = raw20451step1 := by apply Matrix.ext; unfold raw20451step2 raw20451step1; decide +kernel
      have hl : raw20451step1Labels = labelEmbedding1 ∘ raw20451step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20451step1 raw20451step1Labels raw20451step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1217 node1217Labels := by rfl

theorem canonical20452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20452 raw20452Labels = mixedMoment B node1243 node1243Labels := by
  calc
    mixedMoment B raw20452 raw20452Labels = mixedMoment B raw20452step0 raw20452step0Labels := by
      have hz : ∀ j, raw20452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20452step0 = (fun i j => raw20452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20452step0 raw20452; decide +kernel
      have hl : raw20452step0Labels = raw20452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20452 raw20452Labels permutation434 hz
    mixedMoment B raw20452step0 raw20452step0Labels = mixedMoment B raw20452step1 raw20452step1Labels := by
      have hz : ∀ j, raw20452step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20452step1 = (fun i j => raw20452step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20452step1 raw20452step0; decide +kernel
      have hl : raw20452step1Labels = raw20452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20452step0 raw20452step0Labels permutation80 hz
    mixedMoment B raw20452step1 raw20452step1Labels = mixedMoment B raw20452step2 raw20452step2Labels := by
      have ha : raw20452step2 = (fun i j => raw20452step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20452step2 raw20452step1; decide +kernel
      have hl : raw20452step2Labels = raw20452step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20452step1 raw20452step1Labels permutation8 permutation7
    mixedMoment B raw20452step2 raw20452step2Labels = mixedMoment B raw20452step3 raw20452step3Labels := by
      have ha : raw20452step3 = raw20452step2 := by apply Matrix.ext; unfold raw20452step3 raw20452step2; decide +kernel
      have hl : raw20452step2Labels = labelEmbedding1 ∘ raw20452step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20452step2 raw20452step2Labels raw20452step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1243 node1243Labels := by rfl

theorem canonical20453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20453 raw20453Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw20453 raw20453Labels = mixedMoment B raw20453step0 raw20453step0Labels := by
      have hz : ∀ j, raw20453 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20453step0 = (fun i j => raw20453 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20453step0 raw20453; decide +kernel
      have hl : raw20453step0Labels = raw20453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20453 raw20453Labels permutation434 hz
    mixedMoment B raw20453step0 raw20453step0Labels = mixedMoment B raw20453step1 raw20453step1Labels := by
      have hz : ∀ j, raw20453step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20453step1 = (fun i j => raw20453step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20453step1 raw20453step0; decide +kernel
      have hl : raw20453step1Labels = raw20453step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20453step0 raw20453step0Labels permutation80 hz
    mixedMoment B raw20453step1 raw20453step1Labels = mixedMoment B raw20453step2 raw20453step2Labels := by
      have ha : raw20453step2 = (fun i j => raw20453step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20453step2 raw20453step1; decide +kernel
      have hl : raw20453step2Labels = raw20453step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20453step1 raw20453step1Labels permutation8 permutation7
    mixedMoment B raw20453step2 raw20453step2Labels = mixedMoment B raw20453step3 raw20453step3Labels := by
      have ha : raw20453step3 = raw20453step2 := by apply Matrix.ext; unfold raw20453step3 raw20453step2; decide +kernel
      have hl : raw20453step2Labels = labelEmbedding1 ∘ raw20453step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20453step2 raw20453step2Labels raw20453step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1242 node1242Labels := by rfl

theorem canonical20454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20454 raw20454Labels = mixedMoment B node1416 node1416Labels := by
  calc
    mixedMoment B raw20454 raw20454Labels = mixedMoment B raw20454step0 raw20454step0Labels := by
      have hz : ∀ j, raw20454 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20454step0 = (fun i j => raw20454 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20454step0 raw20454; decide +kernel
      have hl : raw20454step0Labels = raw20454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20454 raw20454Labels permutation434 hz
    mixedMoment B raw20454step0 raw20454step0Labels = mixedMoment B raw20454step1 raw20454step1Labels := by
      have hz : ∀ j, raw20454step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20454step1 = (fun i j => raw20454step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20454step1 raw20454step0; decide +kernel
      have hl : raw20454step1Labels = raw20454step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20454step0 raw20454step0Labels permutation56 hz
    mixedMoment B raw20454step1 raw20454step1Labels = mixedMoment B raw20454step2 raw20454step2Labels := by
      have ha : raw20454step2 = (fun i j => raw20454step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20454step2 raw20454step1; decide +kernel
      have hl : raw20454step2Labels = raw20454step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20454step1 raw20454step1Labels permutation8 permutation7
    mixedMoment B raw20454step2 raw20454step2Labels = mixedMoment B raw20454step3 raw20454step3Labels := by
      have ha : raw20454step3 = raw20454step2 := by apply Matrix.ext; unfold raw20454step3 raw20454step2; decide +kernel
      have hl : raw20454step2Labels = labelEmbedding1 ∘ raw20454step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20454step2 raw20454step2Labels raw20454step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1416 node1416Labels := by rfl

theorem canonical20459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20459 raw20459Labels = mixedMoment B node1416 node1416Labels := by
  calc
    mixedMoment B raw20459 raw20459Labels = mixedMoment B raw20459step0 raw20459step0Labels := by
      have hz : ∀ j, raw20459 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20459step0 = (fun i j => raw20459 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20459step0 raw20459; decide +kernel
      have hl : raw20459step0Labels = raw20459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20459 raw20459Labels permutation346 hz
    mixedMoment B raw20459step0 raw20459step0Labels = mixedMoment B raw20459step1 raw20459step1Labels := by
      have hz : ∀ j, raw20459step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20459step1 = (fun i j => raw20459step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20459step1 raw20459step0; decide +kernel
      have hl : raw20459step1Labels = raw20459step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20459step0 raw20459step0Labels permutation56 hz
    mixedMoment B raw20459step1 raw20459step1Labels = mixedMoment B raw20459step2 raw20459step2Labels := by
      have ha : raw20459step2 = (fun i j => raw20459step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20459step2 raw20459step1; decide +kernel
      have hl : raw20459step2Labels = raw20459step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20459step1 raw20459step1Labels permutation8 permutation7
    mixedMoment B raw20459step2 raw20459step2Labels = mixedMoment B raw20459step3 raw20459step3Labels := by
      have ha : raw20459step3 = raw20459step2 := by apply Matrix.ext; unfold raw20459step3 raw20459step2; decide +kernel
      have hl : raw20459step2Labels = labelEmbedding1 ∘ raw20459step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20459step2 raw20459step2Labels raw20459step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1416 node1416Labels := by rfl

theorem canonical20464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20464 raw20464Labels = mixedMoment B node1450 node1450Labels := by
  calc
    mixedMoment B raw20464 raw20464Labels = mixedMoment B raw20464step0 raw20464step0Labels := by
      have hz : ∀ j, raw20464 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20464step0 = (fun i j => raw20464 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20464step0 raw20464; decide +kernel
      have hl : raw20464step0Labels = raw20464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20464 raw20464Labels permutation434 hz
    mixedMoment B raw20464step0 raw20464step0Labels = mixedMoment B raw20464step1 raw20464step1Labels := by
      have hz : ∀ j, raw20464step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20464step1 = (fun i j => raw20464step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20464step1 raw20464step0; decide +kernel
      have hl : raw20464step1Labels = raw20464step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20464step0 raw20464step0Labels permutation80 hz
    mixedMoment B raw20464step1 raw20464step1Labels = mixedMoment B raw20464step2 raw20464step2Labels := by
      have hz : ∀ j, raw20464step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20464step2 = (fun i j => raw20464step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20464step2 raw20464step1; decide +kernel
      have hl : raw20464step2Labels = raw20464step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20464step1 raw20464step1Labels permutation14 hz
    mixedMoment B raw20464step2 raw20464step2Labels = mixedMoment B raw20464step3 raw20464step3Labels := by
      have ha : raw20464step3 = (fun i j => raw20464step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20464step3 raw20464step2; decide +kernel
      have hl : raw20464step3Labels = raw20464step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20464step2 raw20464step2Labels permutation2 permutation7
    mixedMoment B raw20464step3 raw20464step3Labels = mixedMoment B raw20464step4 raw20464step4Labels := by
      have ha : raw20464step4 = raw20464step3 := by apply Matrix.ext; unfold raw20464step4 raw20464step3; decide +kernel
      have hl : raw20464step3Labels = labelEmbedding1 ∘ raw20464step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20464step3 raw20464step3Labels raw20464step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1450 node1450Labels := by rfl

theorem canonical20469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20469 raw20469Labels = mixedMoment B node1452 node1452Labels := by
  calc
    mixedMoment B raw20469 raw20469Labels = mixedMoment B raw20469step0 raw20469step0Labels := by
      have hz : ∀ j, raw20469 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20469step0 = (fun i j => raw20469 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20469step0 raw20469; decide +kernel
      have hl : raw20469step0Labels = raw20469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20469 raw20469Labels permutation434 hz
    mixedMoment B raw20469step0 raw20469step0Labels = mixedMoment B raw20469step1 raw20469step1Labels := by
      have hz : ∀ j, raw20469step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20469step1 = (fun i j => raw20469step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20469step1 raw20469step0; decide +kernel
      have hl : raw20469step1Labels = raw20469step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20469step0 raw20469step0Labels permutation80 hz
    mixedMoment B raw20469step1 raw20469step1Labels = mixedMoment B raw20469step2 raw20469step2Labels := by
      have hz : ∀ j, raw20469step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20469step2 = (fun i j => raw20469step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20469step2 raw20469step1; decide +kernel
      have hl : raw20469step2Labels = raw20469step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20469step1 raw20469step1Labels permutation14 hz
    mixedMoment B raw20469step2 raw20469step2Labels = mixedMoment B raw20469step3 raw20469step3Labels := by
      have ha : raw20469step3 = (fun i j => raw20469step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20469step3 raw20469step2; decide +kernel
      have hl : raw20469step3Labels = raw20469step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20469step2 raw20469step2Labels permutation2 permutation7
    mixedMoment B raw20469step3 raw20469step3Labels = mixedMoment B raw20469step4 raw20469step4Labels := by
      have ha : raw20469step4 = raw20469step3 := by apply Matrix.ext; unfold raw20469step4 raw20469step3; decide +kernel
      have hl : raw20469step3Labels = labelEmbedding1 ∘ raw20469step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20469step3 raw20469step3Labels raw20469step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1452 node1452Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20624 raw20624Labels = mixedMoment B node1417 node1417Labels := by
  calc
    mixedMoment B raw20624 raw20624Labels = mixedMoment B raw20624step0 raw20624step0Labels := by
      have hz : ∀ j, raw20624 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20624step0 = (fun i j => raw20624 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20624step0 raw20624; decide +kernel
      have hl : raw20624step0Labels = raw20624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20624 raw20624Labels permutation434 hz
    mixedMoment B raw20624step0 raw20624step0Labels = mixedMoment B raw20624step1 raw20624step1Labels := by
      have hz : ∀ j, raw20624step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20624step1 = (fun i j => raw20624step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20624step1 raw20624step0; decide +kernel
      have hl : raw20624step1Labels = raw20624step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20624step0 raw20624step0Labels permutation80 hz
    mixedMoment B raw20624step1 raw20624step1Labels = mixedMoment B raw20624step2 raw20624step2Labels := by
      have ha : raw20624step2 = (fun i j => raw20624step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20624step2 raw20624step1; decide +kernel
      have hl : raw20624step2Labels = raw20624step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20624step1 raw20624step1Labels permutation8 permutation7
    mixedMoment B raw20624step2 raw20624step2Labels = mixedMoment B raw20624step3 raw20624step3Labels := by
      have ha : raw20624step3 = raw20624step2 := by apply Matrix.ext; unfold raw20624step3 raw20624step2; decide +kernel
      have hl : raw20624step2Labels = labelEmbedding1 ∘ raw20624step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20624step2 raw20624step2Labels raw20624step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1417 node1417Labels := by rfl

theorem canonical20636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20636 raw20636Labels = mixedMoment B node1307 node1307Labels := by
  calc
    mixedMoment B raw20636 raw20636Labels = mixedMoment B raw20636step0 raw20636step0Labels := by
      have hz : ∀ j, raw20636 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20636step0 = (fun i j => raw20636 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20636step0 raw20636; decide +kernel
      have hl : raw20636step0Labels = raw20636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20636 raw20636Labels permutation434 hz
    mixedMoment B raw20636step0 raw20636step0Labels = mixedMoment B raw20636step1 raw20636step1Labels := by
      have hz : ∀ j, raw20636step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20636step1 = (fun i j => raw20636step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20636step1 raw20636step0; decide +kernel
      have hl : raw20636step1Labels = raw20636step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20636step0 raw20636step0Labels permutation80 hz
    mixedMoment B raw20636step1 raw20636step1Labels = mixedMoment B raw20636step2 raw20636step2Labels := by
      have hz : ∀ j, raw20636step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20636step2 = (fun i j => raw20636step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20636step2 raw20636step1; decide +kernel
      have hl : raw20636step2Labels = raw20636step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20636step1 raw20636step1Labels permutation14 hz
    mixedMoment B raw20636step2 raw20636step2Labels = mixedMoment B raw20636step3 raw20636step3Labels := by
      have ha : raw20636step3 = (fun i j => raw20636step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20636step3 raw20636step2; decide +kernel
      have hl : raw20636step3Labels = raw20636step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20636step2 raw20636step2Labels permutation2 permutation7
    mixedMoment B raw20636step3 raw20636step3Labels = mixedMoment B raw20636step4 raw20636step4Labels := by
      have ha : raw20636step4 = raw20636step3 := by apply Matrix.ext; unfold raw20636step4 raw20636step3; decide +kernel
      have hl : raw20636step3Labels = labelEmbedding1 ∘ raw20636step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20636step3 raw20636step3Labels raw20636step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1307 node1307Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical163
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20980 raw20980Labels = mixedMoment B node1399 node1399Labels := by
  calc
    mixedMoment B raw20980 raw20980Labels = mixedMoment B raw20980step0 raw20980step0Labels := by
      have hz : ∀ j, raw20980 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20980step0 = (fun i j => raw20980 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20980step0 raw20980; decide +kernel
      have hl : raw20980step0Labels = raw20980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20980 raw20980Labels permutation346 hz
    mixedMoment B raw20980step0 raw20980step0Labels = mixedMoment B raw20980step1 raw20980step1Labels := by
      have ha : raw20980step1 = (fun i j => raw20980step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20980step1 raw20980step0; decide +kernel
      have hl : raw20980step1Labels = raw20980step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20980step0 raw20980step0Labels permutation32 permutation7
    mixedMoment B raw20980step1 raw20980step1Labels = mixedMoment B raw20980step2 raw20980step2Labels := by
      have ha : raw20980step2 = raw20980step1 := by apply Matrix.ext; unfold raw20980step2 raw20980step1; decide +kernel
      have hl : raw20980step1Labels = labelEmbedding1 ∘ raw20980step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20980step1 raw20980step1Labels raw20980step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1399 node1399Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical166
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21347 raw21347Labels = mixedMoment B node1372 node1372Labels := by
  calc
    mixedMoment B raw21347 raw21347Labels = mixedMoment B raw21347step0 raw21347step0Labels := by
      have hz : ∀ j, raw21347 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21347step0 = (fun i j => raw21347 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21347step0 raw21347; decide +kernel
      have hl : raw21347step0Labels = raw21347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21347 raw21347Labels permutation434 hz
    mixedMoment B raw21347step0 raw21347step0Labels = mixedMoment B raw21347step1 raw21347step1Labels := by
      have hz : ∀ j, raw21347step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21347step1 = (fun i j => raw21347step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21347step1 raw21347step0; decide +kernel
      have hl : raw21347step1Labels = raw21347step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21347step0 raw21347step0Labels permutation80 hz
    mixedMoment B raw21347step1 raw21347step1Labels = mixedMoment B raw21347step2 raw21347step2Labels := by
      have ha : raw21347step2 = (fun i j => raw21347step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21347step2 raw21347step1; decide +kernel
      have hl : raw21347step2Labels = raw21347step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21347step1 raw21347step1Labels permutation8 permutation7
    mixedMoment B raw21347step2 raw21347step2Labels = mixedMoment B raw21347step3 raw21347step3Labels := by
      have ha : raw21347step3 = raw21347step2 := by apply Matrix.ext; unfold raw21347step3 raw21347step2; decide +kernel
      have hl : raw21347step2Labels = labelEmbedding1 ∘ raw21347step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21347step2 raw21347step2Labels raw21347step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1372 node1372Labels := by rfl

theorem canonical21352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21352 raw21352Labels = mixedMoment B node1388 node1388Labels := by
  calc
    mixedMoment B raw21352 raw21352Labels = mixedMoment B raw21352step0 raw21352step0Labels := by
      have hz : ∀ j, raw21352 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21352step0 = (fun i j => raw21352 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21352step0 raw21352; decide +kernel
      have hl : raw21352step0Labels = raw21352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21352 raw21352Labels permutation434 hz
    mixedMoment B raw21352step0 raw21352step0Labels = mixedMoment B raw21352step1 raw21352step1Labels := by
      have ha : raw21352step1 = (fun i j => raw21352step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21352step1 raw21352step0; decide +kernel
      have hl : raw21352step1Labels = raw21352step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21352step0 raw21352step0Labels permutation32 permutation7
    mixedMoment B raw21352step1 raw21352step1Labels = mixedMoment B raw21352step2 raw21352step2Labels := by
      have ha : raw21352step2 = raw21352step1 := by apply Matrix.ext; unfold raw21352step2 raw21352step1; decide +kernel
      have hl : raw21352step1Labels = labelEmbedding1 ∘ raw21352step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21352step1 raw21352step1Labels raw21352step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1388 node1388Labels := by rfl

theorem canonical21357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21357 raw21357Labels = mixedMoment B node1388 node1388Labels := by
  calc
    mixedMoment B raw21357 raw21357Labels = mixedMoment B raw21357step0 raw21357step0Labels := by
      have hz : ∀ j, raw21357 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21357step0 = (fun i j => raw21357 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21357step0 raw21357; decide +kernel
      have hl : raw21357step0Labels = raw21357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21357 raw21357Labels permutation346 hz
    mixedMoment B raw21357step0 raw21357step0Labels = mixedMoment B raw21357step1 raw21357step1Labels := by
      have ha : raw21357step1 = (fun i j => raw21357step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21357step1 raw21357step0; decide +kernel
      have hl : raw21357step1Labels = raw21357step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21357step0 raw21357step0Labels permutation32 permutation7
    mixedMoment B raw21357step1 raw21357step1Labels = mixedMoment B raw21357step2 raw21357step2Labels := by
      have ha : raw21357step2 = raw21357step1 := by apply Matrix.ext; unfold raw21357step2 raw21357step1; decide +kernel
      have hl : raw21357step1Labels = labelEmbedding1 ∘ raw21357step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21357step1 raw21357step1Labels raw21357step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1388 node1388Labels := by rfl

theorem canonical21364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21364 raw21364Labels = mixedMoment B node1484 node1484Labels := by
  calc
    mixedMoment B raw21364 raw21364Labels = mixedMoment B raw21364step0 raw21364step0Labels := by
      have hz : ∀ j, raw21364 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21364step0 = (fun i j => raw21364 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21364step0 raw21364; decide +kernel
      have hl : raw21364step0Labels = raw21364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21364 raw21364Labels permutation434 hz
    mixedMoment B raw21364step0 raw21364step0Labels = mixedMoment B raw21364step1 raw21364step1Labels := by
      have hz : ∀ j, raw21364step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21364step1 = (fun i j => raw21364step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21364step1 raw21364step0; decide +kernel
      have hl : raw21364step1Labels = raw21364step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21364step0 raw21364step0Labels permutation80 hz
    mixedMoment B raw21364step1 raw21364step1Labels = mixedMoment B raw21364step2 raw21364step2Labels := by
      have ha : raw21364step2 = (fun i j => raw21364step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21364step2 raw21364step1; decide +kernel
      have hl : raw21364step2Labels = raw21364step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21364step1 raw21364step1Labels permutation8 permutation7
    mixedMoment B raw21364step2 raw21364step2Labels = mixedMoment B raw21364step3 raw21364step3Labels := by
      have ha : raw21364step3 = raw21364step2 := by apply Matrix.ext; unfold raw21364step3 raw21364step2; decide +kernel
      have hl : raw21364step2Labels = labelEmbedding1 ∘ raw21364step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21364step2 raw21364step2Labels raw21364step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1484 node1484Labels := by rfl

theorem canonical21365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21365 raw21365Labels = mixedMoment B node1397 node1397Labels := by
  calc
    mixedMoment B raw21365 raw21365Labels = mixedMoment B raw21365step0 raw21365step0Labels := by
      have hz : ∀ j, raw21365 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21365step0 = (fun i j => raw21365 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21365step0 raw21365; decide +kernel
      have hl : raw21365step0Labels = raw21365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21365 raw21365Labels permutation434 hz
    mixedMoment B raw21365step0 raw21365step0Labels = mixedMoment B raw21365step1 raw21365step1Labels := by
      have ha : raw21365step1 = (fun i j => raw21365step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21365step1 raw21365step0; decide +kernel
      have hl : raw21365step1Labels = raw21365step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21365step0 raw21365step0Labels permutation32 permutation7
    mixedMoment B raw21365step1 raw21365step1Labels = mixedMoment B raw21365step2 raw21365step2Labels := by
      have ha : raw21365step2 = raw21365step1 := by apply Matrix.ext; unfold raw21365step2 raw21365step1; decide +kernel
      have hl : raw21365step1Labels = labelEmbedding1 ∘ raw21365step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21365step1 raw21365step1Labels raw21365step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1397 node1397Labels := by rfl

theorem canonical21366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21366 raw21366Labels = mixedMoment B node1397 node1397Labels := by
  calc
    mixedMoment B raw21366 raw21366Labels = mixedMoment B raw21366step0 raw21366step0Labels := by
      have hz : ∀ j, raw21366 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21366step0 = (fun i j => raw21366 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21366step0 raw21366; decide +kernel
      have hl : raw21366step0Labels = raw21366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21366 raw21366Labels permutation346 hz
    mixedMoment B raw21366step0 raw21366step0Labels = mixedMoment B raw21366step1 raw21366step1Labels := by
      have ha : raw21366step1 = (fun i j => raw21366step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21366step1 raw21366step0; decide +kernel
      have hl : raw21366step1Labels = raw21366step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21366step0 raw21366step0Labels permutation32 permutation7
    mixedMoment B raw21366step1 raw21366step1Labels = mixedMoment B raw21366step2 raw21366step2Labels := by
      have ha : raw21366step2 = raw21366step1 := by apply Matrix.ext; unfold raw21366step2 raw21366step1; decide +kernel
      have hl : raw21366step1Labels = labelEmbedding1 ∘ raw21366step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21366step1 raw21366step1Labels raw21366step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1397 node1397Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21550 raw21550Labels = mixedMoment B node1471 node1471Labels := by
  calc
    mixedMoment B raw21550 raw21550Labels = mixedMoment B raw21550step0 raw21550step0Labels := by
      have hz : ∀ j, raw21550 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21550step0 = (fun i j => raw21550 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21550step0 raw21550; decide +kernel
      have hl : raw21550step0Labels = raw21550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21550 raw21550Labels permutation434 hz
    mixedMoment B raw21550step0 raw21550step0Labels = mixedMoment B raw21550step1 raw21550step1Labels := by
      have hz : ∀ j, raw21550step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21550step1 = (fun i j => raw21550step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21550step1 raw21550step0; decide +kernel
      have hl : raw21550step1Labels = raw21550step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21550step0 raw21550step0Labels permutation80 hz
    mixedMoment B raw21550step1 raw21550step1Labels = mixedMoment B raw21550step2 raw21550step2Labels := by
      have ha : raw21550step2 = (fun i j => raw21550step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21550step2 raw21550step1; decide +kernel
      have hl : raw21550step2Labels = raw21550step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21550step1 raw21550step1Labels permutation8 permutation7
    mixedMoment B raw21550step2 raw21550step2Labels = mixedMoment B raw21550step3 raw21550step3Labels := by
      have ha : raw21550step3 = raw21550step2 := by apply Matrix.ext; unfold raw21550step3 raw21550step2; decide +kernel
      have hl : raw21550step2Labels = labelEmbedding1 ∘ raw21550step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21550step2 raw21550step2Labels raw21550step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1471 node1471Labels := by rfl

theorem canonical21551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21551 raw21551Labels = mixedMoment B node1361 node1361Labels := by
  calc
    mixedMoment B raw21551 raw21551Labels = mixedMoment B raw21551step0 raw21551step0Labels := by
      have hz : ∀ j, raw21551 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21551step0 = (fun i j => raw21551 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21551step0 raw21551; decide +kernel
      have hl : raw21551step0Labels = raw21551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21551 raw21551Labels permutation434 hz
    mixedMoment B raw21551step0 raw21551step0Labels = mixedMoment B raw21551step1 raw21551step1Labels := by
      have ha : raw21551step1 = (fun i j => raw21551step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21551step1 raw21551step0; decide +kernel
      have hl : raw21551step1Labels = raw21551step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21551step0 raw21551step0Labels permutation32 permutation7
    mixedMoment B raw21551step1 raw21551step1Labels = mixedMoment B raw21551step2 raw21551step2Labels := by
      have ha : raw21551step2 = raw21551step1 := by apply Matrix.ext; unfold raw21551step2 raw21551step1; decide +kernel
      have hl : raw21551step1Labels = labelEmbedding1 ∘ raw21551step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21551step1 raw21551step1Labels raw21551step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1361 node1361Labels := by rfl

theorem canonical21552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21552 raw21552Labels = mixedMoment B node1361 node1361Labels := by
  calc
    mixedMoment B raw21552 raw21552Labels = mixedMoment B raw21552step0 raw21552step0Labels := by
      have hz : ∀ j, raw21552 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21552step0 = (fun i j => raw21552 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21552step0 raw21552; decide +kernel
      have hl : raw21552step0Labels = raw21552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21552 raw21552Labels permutation346 hz
    mixedMoment B raw21552step0 raw21552step0Labels = mixedMoment B raw21552step1 raw21552step1Labels := by
      have ha : raw21552step1 = (fun i j => raw21552step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21552step1 raw21552step0; decide +kernel
      have hl : raw21552step1Labels = raw21552step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21552step0 raw21552step0Labels permutation32 permutation7
    mixedMoment B raw21552step1 raw21552step1Labels = mixedMoment B raw21552step2 raw21552step2Labels := by
      have ha : raw21552step2 = raw21552step1 := by apply Matrix.ext; unfold raw21552step2 raw21552step1; decide +kernel
      have hl : raw21552step1Labels = labelEmbedding1 ∘ raw21552step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21552step1 raw21552step1Labels raw21552step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1361 node1361Labels := by rfl

theorem canonical21553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21553 raw21553Labels = mixedMoment B node1373 node1373Labels := by
  calc
    mixedMoment B raw21553 raw21553Labels = mixedMoment B raw21553step0 raw21553step0Labels := by
      have hz : ∀ j, raw21553 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21553step0 = (fun i j => raw21553 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21553step0 raw21553; decide +kernel
      have hl : raw21553step0Labels = raw21553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21553 raw21553Labels permutation434 hz
    mixedMoment B raw21553step0 raw21553step0Labels = mixedMoment B raw21553step1 raw21553step1Labels := by
      have hz : ∀ j, raw21553step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21553step1 = (fun i j => raw21553step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21553step1 raw21553step0; decide +kernel
      have hl : raw21553step1Labels = raw21553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21553step0 raw21553step0Labels permutation80 hz
    mixedMoment B raw21553step1 raw21553step1Labels = mixedMoment B raw21553step2 raw21553step2Labels := by
      have ha : raw21553step2 = (fun i j => raw21553step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21553step2 raw21553step1; decide +kernel
      have hl : raw21553step2Labels = raw21553step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21553step1 raw21553step1Labels permutation8 permutation7
    mixedMoment B raw21553step2 raw21553step2Labels = mixedMoment B raw21553step3 raw21553step3Labels := by
      have ha : raw21553step3 = raw21553step2 := by apply Matrix.ext; unfold raw21553step3 raw21553step2; decide +kernel
      have hl : raw21553step2Labels = labelEmbedding1 ∘ raw21553step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21553step2 raw21553step2Labels raw21553step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1373 node1373Labels := by rfl

theorem canonical21554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21554 raw21554Labels = mixedMoment B node1478 node1478Labels := by
  calc
    mixedMoment B raw21554 raw21554Labels = mixedMoment B raw21554step0 raw21554step0Labels := by
      have hz : ∀ j, raw21554 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21554step0 = (fun i j => raw21554 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21554step0 raw21554; decide +kernel
      have hl : raw21554step0Labels = raw21554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21554 raw21554Labels permutation434 hz
    mixedMoment B raw21554step0 raw21554step0Labels = mixedMoment B raw21554step1 raw21554step1Labels := by
      have ha : raw21554step1 = (fun i j => raw21554step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21554step1 raw21554step0; decide +kernel
      have hl : raw21554step1Labels = raw21554step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21554step0 raw21554step0Labels permutation32 permutation7
    mixedMoment B raw21554step1 raw21554step1Labels = mixedMoment B raw21554step2 raw21554step2Labels := by
      have ha : raw21554step2 = raw21554step1 := by apply Matrix.ext; unfold raw21554step2 raw21554step1; decide +kernel
      have hl : raw21554step1Labels = labelEmbedding1 ∘ raw21554step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21554step1 raw21554step1Labels raw21554step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1478 node1478Labels := by rfl

theorem canonical21555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21555 raw21555Labels = mixedMoment B node1379 node1379Labels := by
  calc
    mixedMoment B raw21555 raw21555Labels = mixedMoment B raw21555step0 raw21555step0Labels := by
      have ha : raw21555step0 = (fun i j => raw21555 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21555step0 raw21555; decide +kernel
      have hl : raw21555step0Labels = raw21555Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21555 raw21555Labels permutation152 permutation7
    mixedMoment B raw21555step0 raw21555step0Labels = mixedMoment B raw21555step1 raw21555step1Labels := by
      have ha : raw21555step1 = raw21555step0 := by apply Matrix.ext; unfold raw21555step1 raw21555step0; decide +kernel
      have hl : raw21555step0Labels = labelEmbedding1 ∘ raw21555step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21555step0 raw21555step0Labels raw21555step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1379 node1379Labels := by rfl

theorem canonical21556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21556 raw21556Labels = mixedMoment B node1389 node1389Labels := by
  calc
    mixedMoment B raw21556 raw21556Labels = mixedMoment B raw21556step0 raw21556step0Labels := by
      have hz : ∀ j, raw21556 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21556step0 = (fun i j => raw21556 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21556step0 raw21556; decide +kernel
      have hl : raw21556step0Labels = raw21556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21556 raw21556Labels permutation434 hz
    mixedMoment B raw21556step0 raw21556step0Labels = mixedMoment B raw21556step1 raw21556step1Labels := by
      have ha : raw21556step1 = (fun i j => raw21556step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21556step1 raw21556step0; decide +kernel
      have hl : raw21556step1Labels = raw21556step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21556step0 raw21556step0Labels permutation32 permutation7
    mixedMoment B raw21556step1 raw21556step1Labels = mixedMoment B raw21556step2 raw21556step2Labels := by
      have ha : raw21556step2 = raw21556step1 := by apply Matrix.ext; unfold raw21556step2 raw21556step1; decide +kernel
      have hl : raw21556step1Labels = labelEmbedding1 ∘ raw21556step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21556step1 raw21556step1Labels raw21556step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1389 node1389Labels := by rfl

theorem canonical21557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21557 raw21557Labels = mixedMoment B node1478 node1478Labels := by
  calc
    mixedMoment B raw21557 raw21557Labels = mixedMoment B raw21557step0 raw21557step0Labels := by
      have hz : ∀ j, raw21557 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21557step0 = (fun i j => raw21557 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21557step0 raw21557; decide +kernel
      have hl : raw21557step0Labels = raw21557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21557 raw21557Labels permutation346 hz
    mixedMoment B raw21557step0 raw21557step0Labels = mixedMoment B raw21557step1 raw21557step1Labels := by
      have ha : raw21557step1 = (fun i j => raw21557step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21557step1 raw21557step0; decide +kernel
      have hl : raw21557step1Labels = raw21557step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21557step0 raw21557step0Labels permutation32 permutation7
    mixedMoment B raw21557step1 raw21557step1Labels = mixedMoment B raw21557step2 raw21557step2Labels := by
      have ha : raw21557step2 = raw21557step1 := by apply Matrix.ext; unfold raw21557step2 raw21557step1; decide +kernel
      have hl : raw21557step1Labels = labelEmbedding1 ∘ raw21557step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21557step1 raw21557step1Labels raw21557step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1478 node1478Labels := by rfl

theorem canonical21558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21558 raw21558Labels = mixedMoment B node1379 node1379Labels := by
  calc
    mixedMoment B raw21558 raw21558Labels = mixedMoment B raw21558step0 raw21558step0Labels := by
      have ha : raw21558step0 = (fun i j => raw21558 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21558step0 raw21558; decide +kernel
      have hl : raw21558step0Labels = raw21558Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21558 raw21558Labels permutation158 permutation7
    mixedMoment B raw21558step0 raw21558step0Labels = mixedMoment B raw21558step1 raw21558step1Labels := by
      have ha : raw21558step1 = raw21558step0 := by apply Matrix.ext; unfold raw21558step1 raw21558step0; decide +kernel
      have hl : raw21558step0Labels = labelEmbedding1 ∘ raw21558step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21558step0 raw21558step0Labels raw21558step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1379 node1379Labels := by rfl

theorem canonical21559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21559 raw21559Labels = mixedMoment B node1389 node1389Labels := by
  calc
    mixedMoment B raw21559 raw21559Labels = mixedMoment B raw21559step0 raw21559step0Labels := by
      have hz : ∀ j, raw21559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21559step0 = (fun i j => raw21559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21559step0 raw21559; decide +kernel
      have hl : raw21559step0Labels = raw21559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21559 raw21559Labels permutation346 hz
    mixedMoment B raw21559step0 raw21559step0Labels = mixedMoment B raw21559step1 raw21559step1Labels := by
      have ha : raw21559step1 = (fun i j => raw21559step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21559step1 raw21559step0; decide +kernel
      have hl : raw21559step1Labels = raw21559step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21559step0 raw21559step0Labels permutation32 permutation7
    mixedMoment B raw21559step1 raw21559step1Labels = mixedMoment B raw21559step2 raw21559step2Labels := by
      have ha : raw21559step2 = raw21559step1 := by apply Matrix.ext; unfold raw21559step2 raw21559step1; decide +kernel
      have hl : raw21559step1Labels = labelEmbedding1 ∘ raw21559step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21559step1 raw21559step1Labels raw21559step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1389 node1389Labels := by rfl

theorem canonical21560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21560 raw21560Labels = mixedMoment B node1413 node1413Labels := by
  calc
    mixedMoment B raw21560 raw21560Labels = mixedMoment B raw21560step0 raw21560step0Labels := by
      have hz : ∀ j, raw21560 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21560step0 = (fun i j => raw21560 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21560step0 raw21560; decide +kernel
      have hl : raw21560step0Labels = raw21560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21560 raw21560Labels permutation434 hz
    mixedMoment B raw21560step0 raw21560step0Labels = mixedMoment B raw21560step1 raw21560step1Labels := by
      have hz : ∀ j, raw21560step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21560step1 = (fun i j => raw21560step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21560step1 raw21560step0; decide +kernel
      have hl : raw21560step1Labels = raw21560step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21560step0 raw21560step0Labels permutation80 hz
    mixedMoment B raw21560step1 raw21560step1Labels = mixedMoment B raw21560step2 raw21560step2Labels := by
      have ha : raw21560step2 = (fun i j => raw21560step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21560step2 raw21560step1; decide +kernel
      have hl : raw21560step2Labels = raw21560step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21560step1 raw21560step1Labels permutation8 permutation7
    mixedMoment B raw21560step2 raw21560step2Labels = mixedMoment B raw21560step3 raw21560step3Labels := by
      have ha : raw21560step3 = raw21560step2 := by apply Matrix.ext; unfold raw21560step3 raw21560step2; decide +kernel
      have hl : raw21560step2Labels = labelEmbedding1 ∘ raw21560step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21560step2 raw21560step2Labels raw21560step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1413 node1413Labels := by rfl

theorem canonical21561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21561 raw21561Labels = mixedMoment B node1485 node1485Labels := by
  calc
    mixedMoment B raw21561 raw21561Labels = mixedMoment B raw21561step0 raw21561step0Labels := by
      have hz : ∀ j, raw21561 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21561step0 = (fun i j => raw21561 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21561step0 raw21561; decide +kernel
      have hl : raw21561step0Labels = raw21561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21561 raw21561Labels permutation434 hz
    mixedMoment B raw21561step0 raw21561step0Labels = mixedMoment B raw21561step1 raw21561step1Labels := by
      have hz : ∀ j, raw21561step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21561step1 = (fun i j => raw21561step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21561step1 raw21561step0; decide +kernel
      have hl : raw21561step1Labels = raw21561step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21561step0 raw21561step0Labels permutation80 hz
    mixedMoment B raw21561step1 raw21561step1Labels = mixedMoment B raw21561step2 raw21561step2Labels := by
      have ha : raw21561step2 = (fun i j => raw21561step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw21561step2 raw21561step1; decide +kernel
      have hl : raw21561step2Labels = raw21561step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21561step1 raw21561step1Labels permutation10 permutation5
    mixedMoment B raw21561step2 raw21561step2Labels = mixedMoment B raw21561step3 raw21561step3Labels := by
      have ha : raw21561step3 = -raw21561step2 := by apply Matrix.ext; change ∀ i j, raw21561step3 i j = -(raw21561step2 i j); unfold raw21561step3 raw21561step2; decide +kernel
      have hl : raw21561step3Labels = raw21561step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21561step3 raw21561step3Labels = mixedMoment B raw21561step4 raw21561step4Labels := by
      have ha : raw21561step4 = raw21561step3 := by apply Matrix.ext; unfold raw21561step4 raw21561step3; decide +kernel
      have hl : raw21561step3Labels = labelEmbedding1 ∘ raw21561step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21561step3 raw21561step3Labels raw21561step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1485 node1485Labels := by rfl

theorem canonical21562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21562 raw21562Labels = mixedMoment B node1399 node1399Labels := by
  calc
    mixedMoment B raw21562 raw21562Labels = mixedMoment B raw21562step0 raw21562step0Labels := by
      have hz : ∀ j, raw21562 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21562step0 = (fun i j => raw21562 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21562step0 raw21562; decide +kernel
      have hl : raw21562step0Labels = raw21562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21562 raw21562Labels permutation434 hz
    mixedMoment B raw21562step0 raw21562step0Labels = mixedMoment B raw21562step1 raw21562step1Labels := by
      have ha : raw21562step1 = (fun i j => raw21562step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21562step1 raw21562step0; decide +kernel
      have hl : raw21562step1Labels = raw21562step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21562step0 raw21562step0Labels permutation32 permutation7
    mixedMoment B raw21562step1 raw21562step1Labels = mixedMoment B raw21562step2 raw21562step2Labels := by
      have ha : raw21562step2 = raw21562step1 := by apply Matrix.ext; unfold raw21562step2 raw21562step1; decide +kernel
      have hl : raw21562step1Labels = labelEmbedding1 ∘ raw21562step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21562step1 raw21562step1Labels raw21562step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1399 node1399Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical69 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw69 = injectiveMoment H node217 := by
  calc
    injectiveMoment H raw69 = injectiveMoment H raw69step0 := by
      have heq : raw69step0 = (fun i j => raw69 (permutation22 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw69 permutation22 permutation6
    _ = injectiveMoment H node217 := by rfl

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

theorem canonical7979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7979 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7979 = injectiveMoment H raw7979step0 := by
      have hz : ∀ j, raw7979 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7979step0 = (fun i j => raw7979 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979 permutation7 hz
    injectiveMoment H raw7979step0 = injectiveMoment H raw7979step1 := by
      have hz : ∀ j, raw7979step0 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7979step1 = (fun i j => raw7979step0 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step0 permutation2 hz
    injectiveMoment H raw7979step1 = injectiveMoment H raw7979step2 := by
      have hz : ∀ j, raw7979step1 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7979step2 = (fun i j => raw7979step1 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step1 permutation0 hz
    injectiveMoment H raw7979step2 = injectiveMoment H raw7979step3 := by
      have hz : ∀ i, raw7979step2 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7979step3 = (fun i j => raw7979step2 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7979step2 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical900 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw900 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw900 = injectiveMoment H raw900step0 := by
      have hz : ∀ j, raw900 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw900step0 = (fun i j => raw900 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw900 permutation5 hz
    _ = injectiveMoment H node3 := by rfl

theorem canonical903 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw903 = injectiveMoment H node24 := by
  calc
    injectiveMoment H raw903 = injectiveMoment H raw903step0 := by
      have heq : raw903step0 = (fun i j => raw903 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw903 permutation11 permutation1
    _ = injectiveMoment H node24 := by rfl

theorem canonical909 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw909 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw909 = injectiveMoment H raw909step0 := by
      have hz : ∀ j, raw909 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw909step0 = (fun i j => raw909 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw909 permutation21 hz
    _ = injectiveMoment H node10 := by rfl

theorem canonical914 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw914 = injectiveMoment H node26 := by
  rfl

theorem canonical917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw917 = injectiveMoment H node10 := by
  rfl

theorem canonical924 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw924 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw924 = injectiveMoment H raw924step0 := by
      have heq : raw924step0 = (fun i j => raw924 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw924 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
  rfl

end MUB6.Certificate.PairSemantics

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

theorem canonical9032 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9032 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw9032 = injectiveMoment H raw9032step0 := by
      have hz : ∀ j, raw9032 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw9032step0 = (fun i j => raw9032 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9032 permutation9 hz
    injectiveMoment H raw9032step0 = injectiveMoment H raw9032step1 := by
      have heq : raw9032step1 = (fun i j => raw9032step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9032step0 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

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

theorem canonical198 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw198 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw198 = injectiveMoment H raw198step0 := by
      have hz : ∀ j, raw198 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw198step0 = (fun i j => raw198 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw198 permutation15 hz
    _ = injectiveMoment H node8 := by rfl

theorem canonical199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw199 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw199 = injectiveMoment H raw199step0 := by
      have hz : ∀ j, raw199 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw199step0 = (fun i j => raw199 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw199 permutation15 hz
    _ = injectiveMoment H node9 := by rfl

theorem canonical203 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw203 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw203 = injectiveMoment H raw203step0 := by
      have hz : ∀ j, raw203 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw203step0 = (fun i j => raw203 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw203 permutation21 hz
    _ = injectiveMoment H node8 := by rfl

theorem canonical211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw211 = injectiveMoment H node8 := by
  rfl

theorem canonical215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw215 = injectiveMoment H node2 := by
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

theorem canonical5459 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5459 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw5459 = injectiveMoment H raw5459step0 := by
      have heq : raw5459step0 = raw5459.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5459).symm
    injectiveMoment H raw5459step0 = injectiveMoment H raw5459step1 := by
      have heq : raw5459step1 = (fun i j => raw5459step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5459step0 permutation5 permutation2
    _ = injectiveMoment H node9 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical173
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5540 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5540 = injectiveMoment H node51 := by
  rfl

theorem canonical5554 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5554 = injectiveMoment H node53 := by
  calc
    injectiveMoment H raw5554 = injectiveMoment H raw5554step0 := by
      have heq : raw5554step0 = (fun i j => raw5554 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5554 permutation4 permutation3
    _ = injectiveMoment H node53 := by rfl

theorem canonical5556 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5556 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw5556 = injectiveMoment H raw5556step0 := by
      have heq : raw5556step0 = raw5556.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5556).symm
    injectiveMoment H raw5556step0 = injectiveMoment H raw5556step1 := by
      have heq : raw5556step1 = (fun i j => raw5556step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5556step0 permutation7 permutation2
    _ = injectiveMoment H node8 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical250
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8005 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8005 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw8005 = injectiveMoment H raw8005step0 := by
      have hz : ∀ i, raw8005 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8005step0 = (fun i j => raw8005 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8005 permutation3 hz
    _ = injectiveMoment H node3 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical928 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw928 = injectiveMoment H node8 := by
  calc
    injectiveMoment H raw928 = injectiveMoment H raw928step0 := by
      have heq : raw928step0 = raw928.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw928).symm
    injectiveMoment H raw928step0 = injectiveMoment H raw928step1 := by
      have heq : raw928step1 = (fun i j => raw928step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw928step0 permutation6 permutation2
    _ = injectiveMoment H node8 := by rfl

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

theorem canonical176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw176 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw176 = injectiveMoment H raw176step0 := by
      have heq : raw176step0 = raw176.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw176).symm
    injectiveMoment H raw176step0 = injectiveMoment H raw176step1 := by
      have heq : raw176step1 = -raw176step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw176step0).symm
    injectiveMoment H raw176step1 = injectiveMoment H raw176step2 := by
      have heq : raw176step2 = (fun i j => raw176step1 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw176step1 permutation4 permutation6
    _ = injectiveMoment H node52 := by rfl

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

theorem sound24 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node24 = Sparse.eval value24 (momentVector H) := by
  have heq : pivotMatrix24 = (fun u v => node24 (pivotPermutation24 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node24 = injectiveMoment H pivotMatrix24 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix24 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix24 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix24 (0 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix24 (0 : Fin 3) = raw211 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical211 hH).trans (sound8 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix24 (1 : Fin 3)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix24 (1 : Fin 3) = raw900 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical900 hH).trans (sound3 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix24 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix24 (2 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node24 + (injectiveMoment H (mergeFirst pivotMatrix24 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix24 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix24 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value24, value10, value3, value8, Sparse.eval] at hc ⊢
  linarith

theorem sound26 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node26 = Sparse.eval value26 (momentVector H) := by
  have heq : pivotMatrix26 = (fun u v => node26 (pivotPermutation26 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node26 = injectiveMoment H pivotMatrix26 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix26 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix26 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix26 (0 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (0 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix26 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (1 : Fin 3) = raw924 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical924 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix26 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix26 (2 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node26 + (injectiveMoment H (mergeFirst pivotMatrix26 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix26 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix26 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value26, value10, value11, Sparse.eval] at hc ⊢
  linarith

theorem sound32 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node32 = Sparse.eval value32 (momentVector H) := by
  have hc : momentVector H 35 = injectiveMoment H node32 := rfl
  simp [value32, Sparse.eval, hc]

theorem sound33 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node33 = Sparse.eval value33 (momentVector H) := by
  have hc : momentVector H 82 = injectiveMoment H node33 := rfl
  simp [value33, Sparse.eval, hc]

theorem sound40 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node40 = Sparse.eval value40 (momentVector H) := by
  have hc : momentVector H 52 = injectiveMoment H node40 := rfl
  simp [value40, Sparse.eval, hc]

theorem sound42 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node42 = Sparse.eval value42 (momentVector H) := by
  have hc : momentVector H 11 = injectiveMoment H node42 := rfl
  simp [value42, Sparse.eval, hc]

theorem sound51 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node51 = Sparse.eval value51 (momentVector H) := by
  have heq : pivotMatrix51 = (fun u v => node51 (pivotPermutation51 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node51 = injectiveMoment H pivotMatrix51 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix51 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix51 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix51 (0 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix51 (0 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix51 (1 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix51 (1 : Fin 2) = raw5556 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5556 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node51 + (injectiveMoment H (mergeFirst pivotMatrix51 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix51 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value51, value10, value8, Sparse.eval] at hc ⊢
  linarith

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

theorem sound53 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node53 = Sparse.eval value53 (momentVector H) := by
  have heq : pivotMatrix53 = (fun u v => node53 (pivotPermutation53 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node53 = injectiveMoment H pivotMatrix53 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix53 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix53 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix53 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix53 (0 : Fin 2) = raw8005 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8005 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix53 (1 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix53 (1 : Fin 2) = raw5556 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5556 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node53 + (injectiveMoment H (mergeFirst pivotMatrix53 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix53 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value53, value3, value8, Sparse.eval] at hc ⊢
  linarith

theorem sound59 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node59 = Sparse.eval value59 (momentVector H) := by
  have heq : pivotMatrix59 = (fun u v => node59.transpose (pivotPermutation59 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node59 = injectiveMoment H pivotMatrix59 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix59 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix59 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix59 (0 : Fin 2)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix59 (0 : Fin 2) = raw928 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical928 hH).trans (sound8 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix59 (1 : Fin 2)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix59 (1 : Fin 2) = raw5459 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5459 hH).trans (sound9 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node59 + (injectiveMoment H (mergeFirst pivotMatrix59 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix59 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value59, value8, value9, Sparse.eval] at hc ⊢
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

theorem canonical4151 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4151 = injectiveMoment H node33 := by
  calc
    injectiveMoment H raw4151 = injectiveMoment H raw4151step0 := by
      have heq : raw4151step0 = -raw4151 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4151).symm
    injectiveMoment H raw4151step0 = injectiveMoment H raw4151step1 := by
      have heq : raw4151step1 = (fun i j => raw4151step0 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4151step0 permutation8 permutation4
    _ = injectiveMoment H node33 := by rfl

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

theorem canonical7685 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7685 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7685 = injectiveMoment H raw7685step0 := by
      have hz : ∀ j, raw7685 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7685step0 = (fun i j => raw7685 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7685 permutation27 hz
    injectiveMoment H raw7685step0 = injectiveMoment H raw7685step1 := by
      have heq : raw7685step1 = (fun i j => raw7685step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7685step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1446 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1446 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw1446 = injectiveMoment H raw1446step0 := by
      have heq : raw1446step0 = raw1446.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1446).symm
    injectiveMoment H raw1446step0 = injectiveMoment H raw1446step1 := by
      have heq : raw1446step1 = (fun i j => raw1446step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1446step0 permutation6 permutation5
    _ = injectiveMoment H node59 := by rfl

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

theorem canonical2860 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2860 = injectiveMoment H node40 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical153
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4908 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4908 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw4908 = injectiveMoment H raw4908step0 := by
      have heq : raw4908step0 = -raw4908 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4908).symm
    injectiveMoment H raw4908step0 = injectiveMoment H raw4908step1 := by
      have heq : raw4908step1 = (fun i j => raw4908step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4908step0 permutation8 permutation3
    _ = injectiveMoment H node32 := by rfl

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

theorem canonical4963 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4963 = injectiveMoment H node42 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical231
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7408 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7408 = injectiveMoment H node53 := by
  calc
    injectiveMoment H raw7408 = injectiveMoment H raw7408step0 := by
      have heq : raw7408step0 = -raw7408 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7408).symm
    injectiveMoment H raw7408step0 = injectiveMoment H raw7408step1 := by
      have heq : raw7408step1 = (fun i j => raw7408step0 (permutation8 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7408step0 permutation8 permutation3
    _ = injectiveMoment H node53 := by rfl

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

theorem canonical4162 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4162 = injectiveMoment H node32 := by
  calc
    injectiveMoment H raw4162 = injectiveMoment H raw4162step0 := by
      have heq : raw4162step0 = raw4162.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4162).symm
    injectiveMoment H raw4162step0 = injectiveMoment H raw4162step1 := by
      have heq : raw4162step1 = -raw4162step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4162step0).symm
    injectiveMoment H raw4162step1 = injectiveMoment H raw4162step2 := by
      have heq : raw4162step2 = (fun i j => raw4162step1 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4162step1 permutation8 permutation4
    _ = injectiveMoment H node32 := by rfl

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

theorem canonical6875 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6875 = injectiveMoment H node59 := by
  calc
    injectiveMoment H raw6875 = injectiveMoment H raw6875step0 := by
      have heq : raw6875step0 = -raw6875 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6875).symm
    injectiveMoment H raw6875step0 = injectiveMoment H raw6875step1 := by
      have heq : raw6875step1 = (fun i j => raw6875step0 (permutation8 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6875step0 permutation8 permutation4
    _ = injectiveMoment H node59 := by rfl

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

theorem sound173 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node173 = Sparse.eval value173 (momentVector H) := by
  have heq : pivotMatrix173 = (fun u v => node173 (pivotPermutation173 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node173 = injectiveMoment H pivotMatrix173 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix173 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix173 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix173 (0 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix173 (0 : Fin 3) = raw1446 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1446 hH).trans (sound59 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix173 (1 : Fin 3)) =
      Sparse.eval value40 (momentVector H) := by
    have heq : mergeFirst pivotMatrix173 (1 : Fin 3) = raw2860 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2860 hH).trans (sound40 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix173 (2 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix173 (2 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node173 + (injectiveMoment H (mergeFirst pivotMatrix173 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix173 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix173 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value173, value40, value59, value63, Sparse.eval] at hc ⊢
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

theorem sound217 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node217 = Sparse.eval value217 (momentVector H) := by
  have heq : pivotMatrix217 = (fun u v => node217 (pivotPermutation217 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node217 = injectiveMoment H pivotMatrix217 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix217 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix217 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix217 (0 : Fin 3)) =
      Sparse.eval value59 (momentVector H) := by
    have heq : mergeFirst pivotMatrix217 (0 : Fin 3) = raw6875 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6875 hH).trans (sound59 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix217 (1 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix217 (1 : Fin 3) = raw4162 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4162 hH).trans (sound32 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix217 (2 : Fin 3)) =
      Sparse.eval value33 (momentVector H) := by
    have heq : mergeFirst pivotMatrix217 (2 : Fin 3) = raw4151 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4151 hH).trans (sound33 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node217 + (injectiveMoment H (mergeFirst pivotMatrix217 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix217 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix217 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value217, value32, value33, value59, Sparse.eval] at hc ⊢
  linarith

theorem sound221 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node221 = Sparse.eval value221 (momentVector H) := by
  have heq : pivotMatrix221 = (fun u v => node221 (pivotPermutation221 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node221 = injectiveMoment H pivotMatrix221 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix221 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix221 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix221 (0 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix221 (0 : Fin 3) = raw7408 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7408 hH).trans (sound53 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix221 (1 : Fin 3)) =
      Sparse.eval value42 (momentVector H) := by
    have heq : mergeFirst pivotMatrix221 (1 : Fin 3) = raw4963 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4963 hH).trans (sound42 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix221 (2 : Fin 3)) =
      Sparse.eval value32 (momentVector H) := by
    have heq : mergeFirst pivotMatrix221 (2 : Fin 3) = raw4908 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4908 hH).trans (sound32 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node221 + (injectiveMoment H (mergeFirst pivotMatrix221 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix221 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix221 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value221, value32, value42, value53, Sparse.eval] at hc ⊢
  linarith

theorem sound243 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node243 = Sparse.eval value243 (momentVector H) := by
  have heq : pivotMatrix243 = (fun u v => node243 (pivotPermutation243 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node243 = injectiveMoment H pivotMatrix243 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix243 0 = Pi.single (1 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix243 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix243 (0 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix243 (0 : Fin 3) = raw1447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1447 hH).trans (sound52 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix243 (1 : Fin 3)) =
      Sparse.eval value51 (momentVector H) := by
    have heq : mergeFirst pivotMatrix243 (1 : Fin 3) = raw5540 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5540 hH).trans (sound51 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix243 (2 : Fin 3)) =
      Sparse.eval value53 (momentVector H) := by
    have heq : mergeFirst pivotMatrix243 (2 : Fin 3) = raw5554 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5554 hH).trans (sound53 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node243 + (injectiveMoment H (mergeFirst pivotMatrix243 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix243 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix243 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value243, value51, value52, value53, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical7671 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7671 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7671 = injectiveMoment H raw7671step0 := by
      have hz : ∀ j, raw7671 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw7671step0 = (fun i j => raw7671 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7671 permutation21 hz
    injectiveMoment H raw7671step0 = injectiveMoment H raw7671step1 := by
      have heq : raw7671step1 = (fun i j => raw7671step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7671step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

theorem canonical7678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7678 = injectiveMoment H node65 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair53 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node53 node53Labels = Sparse.eval singlePairValue53 (familyPairVector B) := by
  have hp := single_label_three B hB node53
  have hl : node53Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node53 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node53 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node53 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node53 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node53 (EqualityPatterns.family3.label 1) = PairSemantics.raw203 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node53 PairSemantics.raw203; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical203 hH).trans (PairSemantics.sound8 hH)
  have hm2 : familyPairMoment B (groupedColumns node53 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node53 (EqualityPatterns.family3.label 2) = PairSemantics.raw9032 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node53 PairSemantics.raw9032; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9032 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node53 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value9 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node53 (EqualityPatterns.family3.label 3) = PairSemantics.raw199 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node53 PairSemantics.raw199; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical199 hH).trans (PairSemantics.sound9 hH)
  have hm4 : familyPairMoment B (groupedColumns node53 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value217 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node53 (EqualityPatterns.family3.label 4) = PairSemantics.raw69 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node53 PairSemantics.raw69; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical69 hH).trans (PairSemantics.sound217 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue53, PairSemantics.value0, PairSemantics.value8, PairSemantics.value9, PairSemantics.value11, PairSemantics.value217, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical108 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw108 = injectiveMoment H node221 := by
  calc
    injectiveMoment H raw108 = injectiveMoment H raw108step0 := by
      have heq : raw108step0 = (fun i j => raw108 (permutation26 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw108 permutation26 permutation6
    _ = injectiveMoment H node221 := by rfl

theorem canonical112 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw112 = injectiveMoment H node243 := by
  calc
    injectiveMoment H raw112 = injectiveMoment H raw112step0 := by
      have heq : raw112step0 = -raw112 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw112).symm
    injectiveMoment H raw112step0 = injectiveMoment H raw112step1 := by
      have heq : raw112step1 = (fun i j => raw112step0 (permutation9 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw112step0 permutation9 permutation6
    _ = injectiveMoment H node243 := by rfl

theorem canonical114 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw114 = injectiveMoment H node173 := by
  calc
    injectiveMoment H raw114 = injectiveMoment H raw114step0 := by
      have heq : raw114step0 = (fun i j => raw114 (permutation32 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw114 permutation32 permutation6
    _ = injectiveMoment H node173 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair90 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node90 node90Labels = Sparse.eval singlePairValue90 (familyPairVector B) := by
  have hp := single_label_three B hB node90
  have hl : node90Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node90 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node90 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node90 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node90 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value24 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node90 (EqualityPatterns.family3.label 1) = PairSemantics.raw903 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node90 PairSemantics.raw903; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical903 hH).trans (PairSemantics.sound24 hH)
  have hm2 : familyPairMoment B (groupedColumns node90 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node90 (EqualityPatterns.family3.label 2) = PairSemantics.raw7685 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node90 PairSemantics.raw7685; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7685 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node90 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node90 (EqualityPatterns.family3.label 3) = PairSemantics.raw198 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node90 PairSemantics.raw198; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical198 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node90 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value221 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node90 (EqualityPatterns.family3.label 4) = PairSemantics.raw108 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node90 PairSemantics.raw108; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical108 hH).trans (PairSemantics.sound221 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue90, PairSemantics.value0, PairSemantics.value8, PairSemantics.value11, PairSemantics.value24, PairSemantics.value221, Sparse.eval] at hp ⊢
  linarith only [hp]

theorem singlePair94 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node94 node94Labels = Sparse.eval singlePairValue94 (familyPairVector B) := by
  have hp := single_label_three B hB node94
  have hl : node94Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node94 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node94 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node94 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node94 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node94 (EqualityPatterns.family3.label 1) = PairSemantics.raw909 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node94 PairSemantics.raw909; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical909 hH).trans (PairSemantics.sound10 hH)
  have hm2 : familyPairMoment B (groupedColumns node94 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node94 (EqualityPatterns.family3.label 2) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node94 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node94 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node94 (EqualityPatterns.family3.label 3) = PairSemantics.raw198 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node94 PairSemantics.raw198; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical198 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node94 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value243 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node94 (EqualityPatterns.family3.label 4) = PairSemantics.raw112 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node94 PairSemantics.raw112; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical112 hH).trans (PairSemantics.sound243 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue94, PairSemantics.value0, PairSemantics.value8, PairSemantics.value10, PairSemantics.value65, PairSemantics.value243, Sparse.eval] at hp ⊢
  linarith only [hp]

theorem singlePair96 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node96 node96Labels = Sparse.eval singlePairValue96 (familyPairVector B) := by
  have hp := single_label_three B hB node96
  have hl : node96Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node96 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node96 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node96 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node96 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node96 (EqualityPatterns.family3.label 1) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node96 PairSemantics.raw914; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm2 : familyPairMoment B (groupedColumns node96 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node96 (EqualityPatterns.family3.label 2) = PairSemantics.raw7671 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node96 PairSemantics.raw7671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7671 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node96 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node96 (EqualityPatterns.family3.label 3) = PairSemantics.raw198 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node96 PairSemantics.raw198; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical198 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node96 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value173 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node96 (EqualityPatterns.family3.label 4) = PairSemantics.raw114 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node96 PairSemantics.raw114; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical114 hH).trans (PairSemantics.sound173 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue96, PairSemantics.value0, PairSemantics.value8, PairSemantics.value11, PairSemantics.value26, PairSemantics.value173, Sparse.eval] at hp ⊢
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

theorem singlePair158 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node158 node158Labels = Sparse.eval singlePairValue158 (familyPairVector B) := by
  have hp := single_label_three B hB node158
  have hl : node158Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node158 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node158 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node158 PairSemantics.raw7979
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node158 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node158 (EqualityPatterns.family3.label 1) = PairSemantics.raw5183 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node158 PairSemantics.raw5183
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5183 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node158 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node158 (EqualityPatterns.family3.label 2) = PairSemantics.raw5199 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node158 PairSemantics.raw5199
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node158 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node158 (EqualityPatterns.family3.label 3) = PairSemantics.raw211 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node158 PairSemantics.raw211
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical211 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node158 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value52 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node158 (EqualityPatterns.family3.label 4) = PairSemantics.raw176 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node158 PairSemantics.raw176
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical176 hH).trans (PairSemantics.sound52 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue158, PairSemantics.value0, PairSemantics.value4, PairSemantics.value8, PairSemantics.value11, PairSemantics.value52, Sparse.eval] at hp ⊢
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

theorem singleton1307 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1307 node1307Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node158 node158Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw86 singletonSmall1307
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1307) = raw86Labels := by decide +kernel
  rw [hl, canonical86 B hB] at h
  have hc0 : mixedMoment B raw86 (Fin.cases (0 : Fin 1) singletonSmall1307) =
      mixedMoment B node158 node158Labels := by
    have ha : raw86 = raw87 := by apply Matrix.ext; unfold raw86 raw87; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1307 = raw87Labels := by decide +kernel
    rw [ha, hj, canonical87 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton1413 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1413 node1413Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node96 node96Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw132 singletonSmall1413
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1413) = raw132Labels := by decide +kernel
  rw [hl, canonical132 B hB] at h
  have hc0 : mixedMoment B raw132 (Fin.cases (0 : Fin 1) singletonSmall1413) =
      mixedMoment B node96 node96Labels := by
    have ha : raw132 = raw133 := by apply Matrix.ext; unfold raw132 raw133; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1413 = raw133Labels := by decide +kernel
    rw [ha, hj, canonical133 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton1416 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1416 node1416Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node94 node94Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw136 singletonSmall1416
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1416) = raw136Labels := by decide +kernel
  rw [hl, canonical136 B hB] at h
  have hc0 : mixedMoment B raw136 (Fin.cases (0 : Fin 1) singletonSmall1416) =
      mixedMoment B node94 node94Labels := by
    have ha : raw136 = raw137 := by apply Matrix.ext; unfold raw136 raw137; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1416 = raw137Labels := by decide +kernel
    rw [ha, hj, canonical137 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton1417 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1417 node1417Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node90 node90Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw138 singletonSmall1417
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1417) = raw138Labels := by decide +kernel
  rw [hl, canonical138 B hB] at h
  have hc0 : mixedMoment B raw138 (Fin.cases (0 : Fin 1) singletonSmall1417) =
      mixedMoment B node90 node90Labels := by
    have ha : raw138 = raw139 := by apply Matrix.ext; unfold raw138 raw139; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1417 = raw139Labels := by decide +kernel
    rw [ha, hj, canonical139 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton1471 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1471 node1471Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node53 node53Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw176 singletonSmall1471
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1471) = raw176Labels := by decide +kernel
  rw [hl, canonical176 B hB] at h
  have hc0 : mixedMoment B raw176 (Fin.cases (0 : Fin 1) singletonSmall1471) =
      mixedMoment B node53 node53Labels := by
    have ha : raw176 = raw177 := by apply Matrix.ext; unfold raw176 raw177; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1471 = raw177Labels := by decide +kernel
    rw [ha, hj, canonical177 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound53 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node53 node53Labels = Sparse.eval nodeValue53 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue53 (familyPairVector B) := singlePair53 B _hB
    _ = _ := by norm_num [singlePairValue53, nodeValue53, Sparse.eval, mixedVector] <;> ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound90 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node90 node90Labels = Sparse.eval nodeValue90 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue90 (familyPairVector B) := singlePair90 B _hB
    _ = _ := by norm_num [singlePairValue90, nodeValue90, Sparse.eval, mixedVector] <;> ring

theorem sound94 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node94 node94Labels = Sparse.eval nodeValue94 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue94 (familyPairVector B) := singlePair94 B _hB
    _ = _ := by norm_num [singlePairValue94, nodeValue94, Sparse.eval, mixedVector] <;> ring

theorem sound96 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node96 node96Labels = Sparse.eval nodeValue96 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue96 (familyPairVector B) := singlePair96 B _hB
    _ = _ := by norm_num [singlePairValue96, nodeValue96, Sparse.eval, mixedVector] <;> ring

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

theorem sound158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node158 node158Labels = Sparse.eval nodeValue158 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue158 (familyPairVector B) := singlePair158 B _hB
    _ = _ := by
      norm_num [singlePairValue158, nodeValue158, Sparse.eval, mixedVector]
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

theorem sound1217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1217 node1217Labels = Sparse.eval nodeValue1217 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1217) = mixedMoment B node1217 node1217Labels := rfl
  simpa [nodeValue1217, Sparse.eval] using hc.symm

theorem sound1242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1242 node1242Labels = Sparse.eval nodeValue1242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1242) = mixedMoment B node1242 node1242Labels := rfl
  simpa [nodeValue1242, Sparse.eval] using hc.symm

theorem sound1243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1243 node1243Labels = Sparse.eval nodeValue1243 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1243) = mixedMoment B node1243 node1243Labels := rfl
  simpa [nodeValue1243, Sparse.eval] using hc.symm

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

theorem sound1307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1307 node1307Labels = Sparse.eval nodeValue1307 (mixedVector B) := by
  have h := singleton1307 B _hB
  rw [sound158 B _hB _hF] at h
  norm_num [nodeValue1307, nodeValue158, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1379 node1379Labels = 0 := by
  exact mixedMoment_alpha B hF node1379 node1379Labels 2 permutation152
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1361 node1361Labels = Sparse.eval nodeValue1361 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1361) = mixedMoment B node1361 node1361Labels := rfl
  simpa [nodeValue1361, Sparse.eval] using hc.symm

theorem sound1372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1372 node1372Labels = Sparse.eval nodeValue1372 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1372) = mixedMoment B node1372 node1372Labels := rfl
  simpa [nodeValue1372, Sparse.eval] using hc.symm

theorem sound1373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1373 node1373Labels = Sparse.eval nodeValue1373 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1373) = mixedMoment B node1373 node1373Labels := rfl
  simpa [nodeValue1373, Sparse.eval] using hc.symm

theorem sound1379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1379 node1379Labels = Sparse.eval nodeValue1379 (mixedVector B) := by
  simpa only [nodeValue1379, Sparse.eval_nil] using zero1379 B _hB _hF

theorem sound1388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1388 node1388Labels = Sparse.eval nodeValue1388 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1388) = mixedMoment B node1388 node1388Labels := rfl
  simpa [nodeValue1388, Sparse.eval] using hc.symm

theorem sound1389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1389 node1389Labels = Sparse.eval nodeValue1389 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1389) = mixedMoment B node1389 node1389Labels := rfl
  simpa [nodeValue1389, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1450 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1450 node1450Labels = 0 := by
  exact mixedMoment_order_one B hB node1450 node1450Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero1452 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1452 node1452Labels = 0 := by
  exact mixedMoment_order_one B hB node1452 node1452Labels 2
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1413 node1413Labels = Sparse.eval nodeValue1413 (mixedVector B) := by
  have h := singleton1413 B _hB
  rw [sound96 B _hB _hF] at h
  norm_num [nodeValue1413, nodeValue96, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1416 node1416Labels = Sparse.eval nodeValue1416 (mixedVector B) := by
  have h := singleton1416 B _hB
  rw [sound94 B _hB _hF] at h
  norm_num [nodeValue1416, nodeValue94, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1417 node1417Labels = Sparse.eval nodeValue1417 (mixedVector B) := by
  have h := singleton1417 B _hB
  rw [sound90 B _hB _hF] at h
  norm_num [nodeValue1417, nodeValue90, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1450 node1450Labels = Sparse.eval nodeValue1450 (mixedVector B) := by
  simpa only [nodeValue1450, Sparse.eval_nil] using zero1450 B _hB _hF

theorem sound1452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1452 node1452Labels = Sparse.eval nodeValue1452 (mixedVector B) := by
  simpa only [nodeValue1452, Sparse.eval_nil] using zero1452 B _hB _hF

theorem sound1471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1471 node1471Labels = Sparse.eval nodeValue1471 (mixedVector B) := by
  have h := singleton1471 B _hB
  rw [sound53 B _hB _hF] at h
  norm_num [nodeValue1471, nodeValue53, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1484 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1484 node1484Labels = 0 := by
  exact mixedMoment_order_one B hB node1484 node1484Labels 2
    (by decide +kernel) (by decide +kernel)

theorem zero1485 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1485 node1485Labels = 0 := by
  exact mixedMoment_order_one B hB node1485 node1485Labels 2
    (by decide +kernel) (by decide +kernel)

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

theorem sound1484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1484 node1484Labels = Sparse.eval nodeValue1484 (mixedVector B) := by
  simpa only [nodeValue1484, Sparse.eval_nil] using zero1484 B _hB _hF

theorem sound1485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1485 node1485Labels = Sparse.eval nodeValue1485 (mixedVector B) := by
  simpa only [nodeValue1485, Sparse.eval_nil] using zero1485 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources42
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1360 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1360 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1360 + difference 0 1) (sourceB1360 + difference 1 0) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1360 + difference 0 1) (sourceB1360 + difference 1 0) sourceC1360) = raw20636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20636; decide +kernel
    rw [ha]
    exact (canonical20636 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1360 + difference 0 2) (sourceB1360 + difference 2 0) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1360 + difference 0 2) (sourceB1360 + difference 2 0) sourceC1360) = raw20450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20450; decide +kernel
    rw [ha]
    exact (canonical20450 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1360 + difference 0 3) (sourceB1360 + difference 3 0) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1360 + difference 0 3) (sourceB1360 + difference 3 0) sourceC1360) = raw20451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20451; decide +kernel
    rw [ha]
    exact (canonical20451 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1360 + difference 0 4) (sourceB1360 + difference 4 0) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA1360 + difference 0 4) (sourceB1360 + difference 4 0) sourceC1360) = raw20452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20452; decide +kernel
    rw [ha]
    exact (canonical20452 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1360 + difference 0 5) (sourceB1360 + difference 5 0) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1360 + difference 0 5) (sourceB1360 + difference 5 0) sourceC1360) = raw20453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20453; decide +kernel
    rw [ha]
    exact (canonical20453 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1360 + difference 1 0) (sourceB1360 + difference 0 1) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1471) := by
    have ha : (tripleCharges (sourceA1360 + difference 1 0) (sourceB1360 + difference 0 1) sourceC1360) = raw21550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21550; decide +kernel
    rw [ha]
    exact (canonical21550 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1360 + difference 1 2) (sourceB1360 + difference 2 1) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1361) := by
    have ha : (tripleCharges (sourceA1360 + difference 1 2) (sourceB1360 + difference 2 1) sourceC1360) = raw21551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21551; decide +kernel
    rw [ha]
    exact (canonical21551 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1360 + difference 1 3) (sourceB1360 + difference 3 1) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1361) := by
    have ha : (tripleCharges (sourceA1360 + difference 1 3) (sourceB1360 + difference 3 1) sourceC1360) = raw21552 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21552; decide +kernel
    rw [ha]
    exact (canonical21552 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1360 + difference 1 4) (sourceB1360 + difference 4 1) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1373) := by
    have ha : (tripleCharges (sourceA1360 + difference 1 4) (sourceB1360 + difference 4 1) sourceC1360) = raw21553 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21553; decide +kernel
    rw [ha]
    exact (canonical21553 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1360 + difference 1 5) (sourceB1360 + difference 5 1) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1372) := by
    have ha : (tripleCharges (sourceA1360 + difference 1 5) (sourceB1360 + difference 5 1) sourceC1360) = raw21347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21347; decide +kernel
    rw [ha]
    exact (canonical21347 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1360 + difference 2 0) (sourceB1360 + difference 0 2) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1478) := by
    have ha : (tripleCharges (sourceA1360 + difference 2 0) (sourceB1360 + difference 0 2) sourceC1360) = raw21554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21554; decide +kernel
    rw [ha]
    exact (canonical21554 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1360 + difference 2 1) (sourceB1360 + difference 1 2) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA1360 + difference 2 1) (sourceB1360 + difference 1 2) sourceC1360) = raw20454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20454; decide +kernel
    rw [ha]
    exact (canonical20454 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1360 + difference 2 3) (sourceB1360 + difference 3 2) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1379) := by
    have ha : (tripleCharges (sourceA1360 + difference 2 3) (sourceB1360 + difference 3 2) sourceC1360) = raw21555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21555; decide +kernel
    rw [ha]
    exact (canonical21555 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1360 + difference 2 4) (sourceB1360 + difference 4 2) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1389) := by
    have ha : (tripleCharges (sourceA1360 + difference 2 4) (sourceB1360 + difference 4 2) sourceC1360) = raw21556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21556; decide +kernel
    rw [ha]
    exact (canonical21556 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1360 + difference 2 5) (sourceB1360 + difference 5 2) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA1360 + difference 2 5) (sourceB1360 + difference 5 2) sourceC1360) = raw21352 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21352; decide +kernel
    rw [ha]
    exact (canonical21352 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1360 + difference 3 0) (sourceB1360 + difference 0 3) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1478) := by
    have ha : (tripleCharges (sourceA1360 + difference 3 0) (sourceB1360 + difference 0 3) sourceC1360) = raw21557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21557; decide +kernel
    rw [ha]
    exact (canonical21557 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1360 + difference 3 1) (sourceB1360 + difference 1 3) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA1360 + difference 3 1) (sourceB1360 + difference 1 3) sourceC1360) = raw20459 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20459; decide +kernel
    rw [ha]
    exact (canonical20459 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1360 + difference 3 2) (sourceB1360 + difference 2 3) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1379) := by
    have ha : (tripleCharges (sourceA1360 + difference 3 2) (sourceB1360 + difference 2 3) sourceC1360) = raw21558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21558; decide +kernel
    rw [ha]
    exact (canonical21558 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1360 + difference 3 4) (sourceB1360 + difference 4 3) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1389) := by
    have ha : (tripleCharges (sourceA1360 + difference 3 4) (sourceB1360 + difference 4 3) sourceC1360) = raw21559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21559; decide +kernel
    rw [ha]
    exact (canonical21559 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1360 + difference 3 5) (sourceB1360 + difference 5 3) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA1360 + difference 3 5) (sourceB1360 + difference 5 3) sourceC1360) = raw21357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21357; decide +kernel
    rw [ha]
    exact (canonical21357 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1360 + difference 4 0) (sourceB1360 + difference 0 4) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1484) := by
    have ha : (tripleCharges (sourceA1360 + difference 4 0) (sourceB1360 + difference 0 4) sourceC1360) = raw21364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21364; decide +kernel
    rw [ha]
    exact (canonical21364 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1360 + difference 4 1) (sourceB1360 + difference 1 4) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1450) := by
    have ha : (tripleCharges (sourceA1360 + difference 4 1) (sourceB1360 + difference 1 4) sourceC1360) = raw20464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20464; decide +kernel
    rw [ha]
    exact (canonical20464 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1360 + difference 4 2) (sourceB1360 + difference 2 4) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1397) := by
    have ha : (tripleCharges (sourceA1360 + difference 4 2) (sourceB1360 + difference 2 4) sourceC1360) = raw21365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21365; decide +kernel
    rw [ha]
    exact (canonical21365 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1360 + difference 4 3) (sourceB1360 + difference 3 4) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1397) := by
    have ha : (tripleCharges (sourceA1360 + difference 4 3) (sourceB1360 + difference 3 4) sourceC1360) = raw21366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21366; decide +kernel
    rw [ha]
    exact (canonical21366 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1360 + difference 4 5) (sourceB1360 + difference 5 4) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1413) := by
    have ha : (tripleCharges (sourceA1360 + difference 4 5) (sourceB1360 + difference 5 4) sourceC1360) = raw21560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21560; decide +kernel
    rw [ha]
    exact (canonical21560 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1360 + difference 5 0) (sourceB1360 + difference 0 5) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1485) := by
    have ha : (tripleCharges (sourceA1360 + difference 5 0) (sourceB1360 + difference 0 5) sourceC1360) = raw21561 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21561; decide +kernel
    rw [ha]
    exact (canonical21561 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1360 + difference 5 1) (sourceB1360 + difference 1 5) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1452) := by
    have ha : (tripleCharges (sourceA1360 + difference 5 1) (sourceB1360 + difference 1 5) sourceC1360) = raw20469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20469; decide +kernel
    rw [ha]
    exact (canonical20469 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1360 + difference 5 2) (sourceB1360 + difference 2 5) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1399) := by
    have ha : (tripleCharges (sourceA1360 + difference 5 2) (sourceB1360 + difference 2 5) sourceC1360) = raw21562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw21562; decide +kernel
    rw [ha]
    exact (canonical21562 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1360 + difference 5 3) (sourceB1360 + difference 3 5) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1399) := by
    have ha : (tripleCharges (sourceA1360 + difference 5 3) (sourceB1360 + difference 3 5) sourceC1360) = raw20980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20980; decide +kernel
    rw [ha]
    exact (canonical20980 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1360 + difference 5 4) (sourceB1360 + difference 4 5) sourceC1360) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1417) := by
    have ha : (tripleCharges (sourceA1360 + difference 5 4) (sourceB1360 + difference 4 5) sourceC1360) = raw20624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1360 sourceB1360 sourceC1360 difference raw20624; decide +kernel
    rw [ha]
    exact (canonical20624 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1360 sourceB1360 sourceC1360
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1360, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1179 : Integer.Sparse.reindex keyMap MixedData.row1179 = numericRow1179 := by decide +kernel

theorem numericCheck1179 (x : Master → ℝ) : Integer.Sparse.eval numericRow1179 x =
    (540 : ℝ) * reducedSource1179 x := by
  norm_num [numericRow1179, reducedSource1179, Integer.Sparse.eval, Sparse.eval, nodeValue1217, nodeValue1242, nodeValue1243, nodeValue1307, nodeValue1361, nodeValue1372, nodeValue1373, nodeValue1379, nodeValue1388, nodeValue1389, nodeValue1397, nodeValue1399, nodeValue1413, nodeValue1416, nodeValue1417, nodeValue1450, nodeValue1452, nodeValue1471, nodeValue1478, nodeValue1484, nodeValue1485]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1179 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1179 (mixedVector B) = 0 := by
  have h1217 : mixedVector B (Sum.inr 1217) = Sparse.eval nodeValue1217 (mixedVector B) := by
    change mixedMoment B node1217 node1217Labels = _
    exact sound1217 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h1243 : mixedVector B (Sum.inr 1243) = Sparse.eval nodeValue1243 (mixedVector B) := by
    change mixedMoment B node1243 node1243Labels = _
    exact sound1243 B hB hF
  have h1307 : mixedVector B (Sum.inr 1307) = Sparse.eval nodeValue1307 (mixedVector B) := by
    change mixedMoment B node1307 node1307Labels = _
    exact sound1307 B hB hF
  have h1361 : mixedVector B (Sum.inr 1361) = Sparse.eval nodeValue1361 (mixedVector B) := by
    change mixedMoment B node1361 node1361Labels = _
    exact sound1361 B hB hF
  have h1372 : mixedVector B (Sum.inr 1372) = Sparse.eval nodeValue1372 (mixedVector B) := by
    change mixedMoment B node1372 node1372Labels = _
    exact sound1372 B hB hF
  have h1373 : mixedVector B (Sum.inr 1373) = Sparse.eval nodeValue1373 (mixedVector B) := by
    change mixedMoment B node1373 node1373Labels = _
    exact sound1373 B hB hF
  have h1379 : mixedVector B (Sum.inr 1379) = Sparse.eval nodeValue1379 (mixedVector B) := by
    change mixedMoment B node1379 node1379Labels = _
    exact sound1379 B hB hF
  have h1388 : mixedVector B (Sum.inr 1388) = Sparse.eval nodeValue1388 (mixedVector B) := by
    change mixedMoment B node1388 node1388Labels = _
    exact sound1388 B hB hF
  have h1389 : mixedVector B (Sum.inr 1389) = Sparse.eval nodeValue1389 (mixedVector B) := by
    change mixedMoment B node1389 node1389Labels = _
    exact sound1389 B hB hF
  have h1397 : mixedVector B (Sum.inr 1397) = Sparse.eval nodeValue1397 (mixedVector B) := by
    change mixedMoment B node1397 node1397Labels = _
    exact sound1397_e B hB hF
  have h1399 : mixedVector B (Sum.inr 1399) = Sparse.eval nodeValue1399 (mixedVector B) := by
    change mixedMoment B node1399 node1399Labels = _
    exact sound1399_e B hB hF
  have h1413 : mixedVector B (Sum.inr 1413) = Sparse.eval nodeValue1413 (mixedVector B) := by
    change mixedMoment B node1413 node1413Labels = _
    exact sound1413 B hB hF
  have h1416 : mixedVector B (Sum.inr 1416) = Sparse.eval nodeValue1416 (mixedVector B) := by
    change mixedMoment B node1416 node1416Labels = _
    exact sound1416 B hB hF
  have h1417 : mixedVector B (Sum.inr 1417) = Sparse.eval nodeValue1417 (mixedVector B) := by
    change mixedMoment B node1417 node1417Labels = _
    exact sound1417 B hB hF
  have h1450 : mixedVector B (Sum.inr 1450) = Sparse.eval nodeValue1450 (mixedVector B) := by
    change mixedMoment B node1450 node1450Labels = _
    exact sound1450 B hB hF
  have h1452 : mixedVector B (Sum.inr 1452) = Sparse.eval nodeValue1452 (mixedVector B) := by
    change mixedMoment B node1452 node1452Labels = _
    exact sound1452 B hB hF
  have h1471 : mixedVector B (Sum.inr 1471) = Sparse.eval nodeValue1471 (mixedVector B) := by
    change mixedMoment B node1471 node1471Labels = _
    exact sound1471 B hB hF
  have h1478 : mixedVector B (Sum.inr 1478) = Sparse.eval nodeValue1478 (mixedVector B) := by
    change mixedMoment B node1478 node1478Labels = _
    exact sound1478_e B hB hF
  have h1484 : mixedVector B (Sum.inr 1484) = Sparse.eval nodeValue1484 (mixedVector B) := by
    change mixedMoment B node1484 node1484Labels = _
    exact sound1484 B hB hF
  have h1485 : mixedVector B (Sum.inr 1485) = Sparse.eval nodeValue1485 (mixedVector B) := by
    change mixedMoment B node1485 node1485Labels = _
    exact sound1485 B hB hF
  simpa only [sourceForm1360, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1217, h1242, h1243, h1307, h1361, h1372, h1373, h1379, h1388, h1389, h1397, h1399, h1413, h1416, h1417, h1450, h1452, h1471, h1478, h1484, h1485, reducedSource1179] using sourceEq1360 B hB

theorem rowSound1179_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1179 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1179, numericCheck1179, reducedZero1179 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179_e_oai
