-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:50:45.649254+00:00
-- url     : https://prove2.me/submissions/516f8870-eda9-4a33-97cf-11f845697d95

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_reducedZero1785_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1780_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1781_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1782_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1783_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1784_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1786_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1787_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1788_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1789_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Orthogonality
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

/-- The finite orthogonality contraction underlying equation (same-matrix). -/
theorem weighted_contraction {H : CMatrix} (hH : IsHadamard H)
    (u v : Coord → ℂ) (i : Coord) :
    (∑ j, (∑ k, u k * H i k * conj (H j k)) *
      (∑ l, v l * conj (H i l) * H j l)) =
      6 * ∑ k, u k * v k := by
  have hexpand :
      (∑ j, (∑ k, u k * H i k * conj (H j k)) *
        (∑ l, v l * conj (H i l) * H j l)) =
      ∑ l, ∑ k, (u k * v l * H i k * conj (H i l)) *
        (∑ j, conj (H j k) * H j l) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand]
  simp_rw [hH.column_orthogonal]
  have hunit (k : Coord) : H i k * conj (H i k) = 1 := by
    rw [Complex.mul_conj, hH.1]
    norm_num
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    u k * v k * H i k * conj (H i k) * 6 =
      6 * (u k * v k) * (H i k * conj (H i k)) := by ring
    _ = _ := by rw [hunit, mul_one]

theorem g_add_difference {H : CMatrix} (hH : IsHadamard H)
    (a : Charge) (i j : Coord) :
    g H (a + difference i j) = (6 : ℂ)⁻¹ *
      ∑ k, character (fun r => H r k) a * H i k * conj (H j k) := by
  simp only [g]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [character_add _ (fun r => unit_ne_zero (hH.1 r k)),
    character_difference _ (fun r => hH.1 r k)]
  ring

/-- Source Lemma (basic), equation (same-matrix), for arbitrary integral charges. -/
theorem same_matrix_identity {H : CMatrix} (hH : IsHadamard H)
    (a b : Charge) (i : Coord) :
    ∑ j, g H (a + difference i j) * g H (b + difference j i) = g H (a + b) := by
  simp_rw [g_add_difference hH]
  have hexpand :
      (∑ j, ((6 : ℂ)⁻¹ * ∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
        ((6 : ℂ)⁻¹ * ∑ l, character (fun r => H r l) b * H j l * conj (H i l))) =
      (6 : ℂ)⁻¹ * (6 : ℂ)⁻¹ *
        (∑ j, (∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
          (∑ l, character (fun r => H r l) b * conj (H i l) * H j l)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have he : (∑ l, character (fun r => H r l) b * H j l * conj (H i l)) =
        ∑ l, character (fun r => H r l) b * conj (H i l) * H j l := by
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [he]
    ring
  rw [hexpand, weighted_contraction hH]
  unfold g
  have hs : (∑ k, character (fun r => H r k) a * character (fun r => H r k) b) =
      ∑ k, character (fun r => H r k) (a + b) := by
    apply Finset.sum_congr rfl
    intro k _
    exact (character_add _ (fun r => unit_ne_zero (hH.1 r k)) a b).symm
  rw [hs]
  ring

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

theorem mixedIntegrand_two {l : ℕ} (B : Fin 7 → Basis) (a b : Charge)
    (s t : Fin l) (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
    mixedIntegrand B (doubleCharges a b) ![s, t] r ρ τ =
      g (sampledMatrix B r ρ (τ s)) a * g (sampledMatrix B r ρ (τ t)) b := by
  simp [mixedIntegrand, doubleCharges, Fin.prod_univ_succ, rowFourier, g, character, sampledMatrix]

theorem mixedMoment_same {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference i j) (b + difference j i) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  rw [same_matrix_identity (sampledMatrix_isHadamard B hB r ρ _) a b i]

theorem mixedMoment_same_reversed {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference j i) (b + difference i j) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  have h := same_matrix_identity (sampledMatrix_isHadamard B hB r ρ (τ s)) b a i
  simpa only [mul_comm, add_comm] using congrArg
    (fun z => (z * g (sampledMatrix B r ρ (τ u)) c).re) h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw246 raw246Labels = mixedMoment B node2604 node2604Labels := by
  calc
    mixedMoment B raw246 raw246Labels = mixedMoment B raw246step0 raw246step0Labels := by
      have ha : raw246step0 = (fun i j => raw246 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw246step0 raw246; decide +kernel
      have hl : raw246step0Labels = raw246Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw246 raw246Labels permutation8 permutation5
    mixedMoment B raw246step0 raw246step0Labels = mixedMoment B raw246step1 raw246step1Labels := by
      have ha : raw246step1 = raw246step0 := by apply Matrix.ext; unfold raw246step1 raw246step0; decide +kernel
      have hl : raw246step0Labels = labelEmbedding1 ∘ raw246step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw246step0 raw246step0Labels raw246step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2604 node2604Labels := by rfl

theorem canonical247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw247 raw247Labels = mixedMoment B node343 node343Labels := by
  calc
    mixedMoment B raw247 raw247Labels = mixedMoment B raw247step0 raw247step0Labels := by
      have ha : raw247step0 = (fun i j => raw247 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw247step0 raw247; decide +kernel
      have hl : raw247step0Labels = raw247Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw247 raw247Labels permutation8 permutation5
    _ = mixedMoment B node343 node343Labels := by rfl

theorem canonical248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw248 raw248Labels = mixedMoment B node2605 node2605Labels := by
  calc
    mixedMoment B raw248 raw248Labels = mixedMoment B raw248step0 raw248step0Labels := by
      have ha : raw248step0 = (fun i j => raw248 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw248step0 raw248; decide +kernel
      have hl : raw248step0Labels = raw248Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw248 raw248Labels permutation8 permutation5
    mixedMoment B raw248step0 raw248step0Labels = mixedMoment B raw248step1 raw248step1Labels := by
      have ha : raw248step1 = raw248step0 := by apply Matrix.ext; unfold raw248step1 raw248step0; decide +kernel
      have hl : raw248step0Labels = labelEmbedding1 ∘ raw248step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw248step0 raw248step0Labels raw248step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2605 node2605Labels := by rfl

theorem canonical249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw249 raw249Labels = mixedMoment B node344 node344Labels := by
  calc
    mixedMoment B raw249 raw249Labels = mixedMoment B raw249step0 raw249step0Labels := by
      have ha : raw249step0 = (fun i j => raw249 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw249step0 raw249; decide +kernel
      have hl : raw249step0Labels = raw249Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw249 raw249Labels permutation8 permutation5
    _ = mixedMoment B node344 node344Labels := by rfl

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

theorem canonical1749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1749 raw1749Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw1749 raw1749Labels = mixedMoment B raw1749step0 raw1749step0Labels := by
      have ha : raw1749step0 = (fun i j => raw1749 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1749step0 raw1749; decide +kernel
      have hl : raw1749step0Labels = raw1749Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1749 raw1749Labels permutation32 permutation4
    mixedMoment B raw1749step0 raw1749step0Labels = mixedMoment B raw1749step1 raw1749step1Labels := by
      have ha : raw1749step1 = raw1749step0 := by apply Matrix.ext; unfold raw1749step1 raw1749step0; decide +kernel
      have hl : raw1749step0Labels = labelEmbedding7 ∘ raw1749step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1749step0 raw1749step0Labels raw1749step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

theorem canonical1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1750 raw1750Labels = mixedMoment B node2029 node2029Labels := by
  calc
    mixedMoment B raw1750 raw1750Labels = mixedMoment B raw1750step0 raw1750step0Labels := by
      have ha : raw1750step0 = (fun i j => raw1750 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1750step0 raw1750; decide +kernel
      have hl : raw1750step0Labels = raw1750Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1750 raw1750Labels permutation32 permutation4
    _ = mixedMoment B node2029 node2029Labels := by rfl

theorem canonical1751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1751 raw1751Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw1751 raw1751Labels = mixedMoment B raw1751step0 raw1751step0Labels := by
      have ha : raw1751step0 = (fun i j => raw1751 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1751step0 raw1751; decide +kernel
      have hl : raw1751step0Labels = raw1751Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1751 raw1751Labels permutation32 permutation6
    mixedMoment B raw1751step0 raw1751step0Labels = mixedMoment B raw1751step1 raw1751step1Labels := by
      have ha : raw1751step1 = -raw1751step0 := by apply Matrix.ext; change ∀ i j, raw1751step1 i j = -(raw1751step0 i j); unfold raw1751step1 raw1751step0; decide +kernel
      have hl : raw1751step1Labels = raw1751step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1751step1 raw1751step1Labels = mixedMoment B raw1751step2 raw1751step2Labels := by
      have ha : raw1751step2 = raw1751step1 := by apply Matrix.ext; unfold raw1751step2 raw1751step1; decide +kernel
      have hl : raw1751step1Labels = labelEmbedding1 ∘ raw1751step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1751step1 raw1751step1Labels raw1751step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2225 node2225Labels := by rfl

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

theorem canonical2109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2109 raw2109Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw2109 raw2109Labels = mixedMoment B raw2109step0 raw2109step0Labels := by
      have ha : raw2109step0 = (fun i j => raw2109 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2109step0 raw2109; decide +kernel
      have hl : raw2109step0Labels = raw2109Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2109 raw2109Labels permutation32 permutation4
    mixedMoment B raw2109step0 raw2109step0Labels = mixedMoment B raw2109step1 raw2109step1Labels := by
      have ha : raw2109step1 = raw2109step0 := by apply Matrix.ext; unfold raw2109step1 raw2109step0; decide +kernel
      have hl : raw2109step0Labels = labelEmbedding7 ∘ raw2109step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2109step0 raw2109step0Labels raw2109step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

theorem canonical2110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2110 raw2110Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw2110 raw2110Labels = mixedMoment B raw2110step0 raw2110step0Labels := by
      have ha : raw2110step0 = (fun i j => raw2110 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2110step0 raw2110; decide +kernel
      have hl : raw2110step0Labels = raw2110Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2110 raw2110Labels permutation32 permutation4
    _ = mixedMoment B node2489 node2489Labels := by rfl

theorem canonical2111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2111 raw2111Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw2111 raw2111Labels = mixedMoment B raw2111step0 raw2111step0Labels := by
      have ha : raw2111step0 = (fun i j => raw2111 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2111step0 raw2111; decide +kernel
      have hl : raw2111step0Labels = raw2111Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2111 raw2111Labels permutation32 permutation6
    mixedMoment B raw2111step0 raw2111step0Labels = mixedMoment B raw2111step1 raw2111step1Labels := by
      have ha : raw2111step1 = -raw2111step0 := by apply Matrix.ext; change ∀ i j, raw2111step1 i j = -(raw2111step0 i j); unfold raw2111step1 raw2111step0; decide +kernel
      have hl : raw2111step1Labels = raw2111step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2111step1 raw2111step1Labels = mixedMoment B raw2111step2 raw2111step2Labels := by
      have ha : raw2111step2 = raw2111step1 := by apply Matrix.ext; unfold raw2111step2 raw2111step1; decide +kernel
      have hl : raw2111step1Labels = labelEmbedding1 ∘ raw2111step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2111step1 raw2111step1Labels raw2111step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3482 node3482Labels := by rfl

theorem canonical2169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2169 raw2169Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw2169 raw2169Labels = mixedMoment B raw2169step0 raw2169step0Labels := by
      have ha : raw2169step0 = (fun i j => raw2169 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2169step0 raw2169; decide +kernel
      have hl : raw2169step0Labels = raw2169Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2169 raw2169Labels permutation32 permutation4
    mixedMoment B raw2169step0 raw2169step0Labels = mixedMoment B raw2169step1 raw2169step1Labels := by
      have ha : raw2169step1 = raw2169step0 := by apply Matrix.ext; unfold raw2169step1 raw2169step0; decide +kernel
      have hl : raw2169step0Labels = labelEmbedding7 ∘ raw2169step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2169step0 raw2169step0Labels raw2169step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical2170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2170 raw2170Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw2170 raw2170Labels = mixedMoment B raw2170step0 raw2170step0Labels := by
      have ha : raw2170step0 = (fun i j => raw2170 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2170step0 raw2170; decide +kernel
      have hl : raw2170step0Labels = raw2170Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2170 raw2170Labels permutation32 permutation4
    _ = mixedMoment B node2561 node2561Labels := by rfl

theorem canonical2171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2171 raw2171Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw2171 raw2171Labels = mixedMoment B raw2171step0 raw2171step0Labels := by
      have ha : raw2171step0 = (fun i j => raw2171 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2171step0 raw2171; decide +kernel
      have hl : raw2171step0Labels = raw2171Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2171 raw2171Labels permutation38 permutation6
    mixedMoment B raw2171step0 raw2171step0Labels = mixedMoment B raw2171step1 raw2171step1Labels := by
      have ha : raw2171step1 = -raw2171step0 := by apply Matrix.ext; change ∀ i j, raw2171step1 i j = -(raw2171step0 i j); unfold raw2171step1 raw2171step0; decide +kernel
      have hl : raw2171step1Labels = raw2171step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2171step1 raw2171step1Labels = mixedMoment B raw2171step2 raw2171step2Labels := by
      have ha : raw2171step2 = raw2171step1 := by apply Matrix.ext; unfold raw2171step2 raw2171step1; decide +kernel
      have hl : raw2171step1Labels = labelEmbedding1 ∘ raw2171step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2171step1 raw2171step1Labels raw2171step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

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

theorem canonical2178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2178 raw2178Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw2178 raw2178Labels = mixedMoment B raw2178step0 raw2178step0Labels := by
      have ha : raw2178step0 = (fun i j => raw2178 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2178step0 raw2178; decide +kernel
      have hl : raw2178step0Labels = raw2178Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2178 raw2178Labels permutation32 permutation5
    mixedMoment B raw2178step0 raw2178step0Labels = mixedMoment B raw2178step1 raw2178step1Labels := by
      have ha : raw2178step1 = raw2178step0 := by apply Matrix.ext; unfold raw2178step1 raw2178step0; decide +kernel
      have hl : raw2178step0Labels = labelEmbedding8 ∘ raw2178step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2178step0 raw2178step0Labels raw2178step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

theorem canonical2179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2179 raw2179Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw2179 raw2179Labels = mixedMoment B raw2179step0 raw2179step0Labels := by
      have ha : raw2179step0 = (fun i j => raw2179 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2179step0 raw2179; decide +kernel
      have hl : raw2179step0Labels = raw2179Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2179 raw2179Labels permutation33 permutation4
    _ = mixedMoment B node2931 node2931Labels := by rfl

theorem canonical2180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2180 raw2180Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw2180 raw2180Labels = mixedMoment B raw2180step0 raw2180step0Labels := by
      have ha : raw2180step0 = (fun i j => raw2180 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2180step0 raw2180; decide +kernel
      have hl : raw2180step0Labels = raw2180Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2180 raw2180Labels permutation34 permutation3
    mixedMoment B raw2180step0 raw2180step0Labels = mixedMoment B raw2180step1 raw2180step1Labels := by
      have ha : raw2180step1 = -raw2180step0 := by apply Matrix.ext; change ∀ i j, raw2180step1 i j = -(raw2180step0 i j); unfold raw2180step1 raw2180step0; decide +kernel
      have hl : raw2180step1Labels = raw2180step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2180step1 raw2180step1Labels = mixedMoment B raw2180step2 raw2180step2Labels := by
      have ha : raw2180step2 = raw2180step1 := by apply Matrix.ext; unfold raw2180step2 raw2180step1; decide +kernel
      have hl : raw2180step1Labels = labelEmbedding1 ∘ raw2180step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2180step1 raw2180step1Labels raw2180step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

theorem canonical2214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2214 raw2214Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw2214 raw2214Labels = mixedMoment B raw2214step0 raw2214step0Labels := by
      have ha : raw2214step0 = (fun i j => raw2214 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2214step0 raw2214; decide +kernel
      have hl : raw2214step0Labels = raw2214Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2214 raw2214Labels permutation8 permutation4
    mixedMoment B raw2214step0 raw2214step0Labels = mixedMoment B raw2214step1 raw2214step1Labels := by
      have ha : raw2214step1 = raw2214step0 := by apply Matrix.ext; unfold raw2214step1 raw2214step0; decide +kernel
      have hl : raw2214step0Labels = labelEmbedding7 ∘ raw2214step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2214step0 raw2214step0Labels raw2214step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

theorem canonical2215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2215 raw2215Labels = mixedMoment B node2604 node2604Labels := by
  calc
    mixedMoment B raw2215 raw2215Labels = mixedMoment B raw2215step0 raw2215step0Labels := by
      have ha : raw2215step0 = (fun i j => raw2215 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2215step0 raw2215; decide +kernel
      have hl : raw2215step0Labels = raw2215Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2215 raw2215Labels permutation8 permutation4
    _ = mixedMoment B node2604 node2604Labels := by rfl

theorem canonical2216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2216 raw2216Labels = mixedMoment B node3614 node3614Labels := by
  calc
    mixedMoment B raw2216 raw2216Labels = mixedMoment B raw2216step0 raw2216step0Labels := by
      have ha : raw2216step0 = (fun i j => raw2216 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2216step0 raw2216; decide +kernel
      have hl : raw2216step0Labels = raw2216Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2216 raw2216Labels permutation8 permutation6
    mixedMoment B raw2216step0 raw2216step0Labels = mixedMoment B raw2216step1 raw2216step1Labels := by
      have ha : raw2216step1 = -raw2216step0 := by apply Matrix.ext; change ∀ i j, raw2216step1 i j = -(raw2216step0 i j); unfold raw2216step1 raw2216step0; decide +kernel
      have hl : raw2216step1Labels = raw2216step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2216step1 raw2216step1Labels = mixedMoment B raw2216step2 raw2216step2Labels := by
      have ha : raw2216step2 = raw2216step1 := by apply Matrix.ext; unfold raw2216step2 raw2216step1; decide +kernel
      have hl : raw2216step1Labels = labelEmbedding1 ∘ raw2216step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2216step1 raw2216step1Labels raw2216step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3614 node3614Labels := by rfl

theorem canonical2217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2217 raw2217Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw2217 raw2217Labels = mixedMoment B raw2217step0 raw2217step0Labels := by
      have ha : raw2217step0 = (fun i j => raw2217 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2217step0 raw2217; decide +kernel
      have hl : raw2217step0Labels = raw2217Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2217 raw2217Labels permutation8 permutation4
    mixedMoment B raw2217step0 raw2217step0Labels = mixedMoment B raw2217step1 raw2217step1Labels := by
      have ha : raw2217step1 = raw2217step0 := by apply Matrix.ext; unfold raw2217step1 raw2217step0; decide +kernel
      have hl : raw2217step0Labels = labelEmbedding7 ∘ raw2217step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2217step0 raw2217step0Labels raw2217step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5177 node5177Labels := by rfl

theorem canonical2218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2218 raw2218Labels = mixedMoment B node2605 node2605Labels := by
  calc
    mixedMoment B raw2218 raw2218Labels = mixedMoment B raw2218step0 raw2218step0Labels := by
      have ha : raw2218step0 = (fun i j => raw2218 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2218step0 raw2218; decide +kernel
      have hl : raw2218step0Labels = raw2218Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2218 raw2218Labels permutation8 permutation4
    _ = mixedMoment B node2605 node2605Labels := by rfl

theorem canonical2219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2219 raw2219Labels = mixedMoment B node3616 node3616Labels := by
  calc
    mixedMoment B raw2219 raw2219Labels = mixedMoment B raw2219step0 raw2219step0Labels := by
      have ha : raw2219step0 = (fun i j => raw2219 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2219step0 raw2219; decide +kernel
      have hl : raw2219step0Labels = raw2219Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2219 raw2219Labels permutation8 permutation6
    mixedMoment B raw2219step0 raw2219step0Labels = mixedMoment B raw2219step1 raw2219step1Labels := by
      have ha : raw2219step1 = -raw2219step0 := by apply Matrix.ext; change ∀ i j, raw2219step1 i j = -(raw2219step0 i j); unfold raw2219step1 raw2219step0; decide +kernel
      have hl : raw2219step1Labels = raw2219step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2219step1 raw2219step1Labels = mixedMoment B raw2219step2 raw2219step2Labels := by
      have ha : raw2219step2 = raw2219step1 := by apply Matrix.ext; unfold raw2219step2 raw2219step1; decide +kernel
      have hl : raw2219step1Labels = labelEmbedding1 ∘ raw2219step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2219step1 raw2219step1Labels raw2219step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3616 node3616Labels := by rfl

theorem canonical2235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2235 raw2235Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw2235 raw2235Labels = mixedMoment B raw2235step0 raw2235step0Labels := by
      have ha : raw2235step0 = (fun i j => raw2235 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2235step0 raw2235; decide +kernel
      have hl : raw2235step0Labels = raw2235Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2235 raw2235Labels permutation8 permutation5
    mixedMoment B raw2235step0 raw2235step0Labels = mixedMoment B raw2235step1 raw2235step1Labels := by
      have ha : raw2235step1 = raw2235step0 := by apply Matrix.ext; unfold raw2235step1 raw2235step0; decide +kernel
      have hl : raw2235step0Labels = labelEmbedding8 ∘ raw2235step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2235step0 raw2235step0Labels raw2235step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

theorem canonical2236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2236 raw2236Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw2236 raw2236Labels = mixedMoment B raw2236step0 raw2236step0Labels := by
      have ha : raw2236step0 = (fun i j => raw2236 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2236step0 raw2236; decide +kernel
      have hl : raw2236step0Labels = raw2236Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2236 raw2236Labels permutation9 permutation4
    _ = mixedMoment B node2889 node2889Labels := by rfl

theorem canonical2237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2237 raw2237Labels = mixedMoment B node3631 node3631Labels := by
  calc
    mixedMoment B raw2237 raw2237Labels = mixedMoment B raw2237step0 raw2237step0Labels := by
      have ha : raw2237step0 = (fun i j => raw2237 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2237step0 raw2237; decide +kernel
      have hl : raw2237step0Labels = raw2237Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2237 raw2237Labels permutation10 permutation3
    mixedMoment B raw2237step0 raw2237step0Labels = mixedMoment B raw2237step1 raw2237step1Labels := by
      have ha : raw2237step1 = -raw2237step0 := by apply Matrix.ext; change ∀ i j, raw2237step1 i j = -(raw2237step0 i j); unfold raw2237step1 raw2237step0; decide +kernel
      have hl : raw2237step1Labels = raw2237step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2237step1 raw2237step1Labels = mixedMoment B raw2237step2 raw2237step2Labels := by
      have ha : raw2237step2 = raw2237step1 := by apply Matrix.ext; unfold raw2237step2 raw2237step1; decide +kernel
      have hl : raw2237step1Labels = labelEmbedding1 ∘ raw2237step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2237step1 raw2237step1Labels raw2237step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3631 node3631Labels := by rfl

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

theorem canonical24552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24552 raw24552Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw24552 raw24552Labels = mixedMoment B raw24552step0 raw24552step0Labels := by
      have hz : ∀ j, raw24552 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24552step0 = (fun i j => raw24552 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24552step0 raw24552; decide +kernel
      have hl : raw24552step0Labels = raw24552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24552 raw24552Labels permutation265 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical24553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24553 raw24553Labels = mixedMoment B node2556 node2556Labels := by
  calc
    _ = mixedMoment B node2556 node2556Labels := by rfl

theorem canonical24556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24556 raw24556Labels = mixedMoment B node1152 node1152Labels := by
  calc
    _ = mixedMoment B node1152 node1152Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical229
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29317 raw29317Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw29317 raw29317Labels = mixedMoment B raw29317step0 raw29317step0Labels := by
      have hz : ∀ j, raw29317 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29317step0 = (fun i j => raw29317 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29317step0 raw29317; decide +kernel
      have hl : raw29317step0Labels = raw29317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29317 raw29317Labels permutation346 hz
    mixedMoment B raw29317step0 raw29317step0Labels = mixedMoment B raw29317step1 raw29317step1Labels := by
      have ha : raw29317step1 = (fun i j => raw29317step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29317step1 raw29317step0; decide +kernel
      have hl : raw29317step1Labels = raw29317step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29317step0 raw29317step0Labels permutation32 permutation4
    mixedMoment B raw29317step1 raw29317step1Labels = mixedMoment B raw29317step2 raw29317step2Labels := by
      have ha : raw29317step2 = -raw29317step1 := by apply Matrix.ext; change ∀ i j, raw29317step2 i j = -(raw29317step1 i j); unfold raw29317step2 raw29317step1; decide +kernel
      have hl : raw29317step2Labels = raw29317step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2225 node2225Labels := by rfl

theorem canonical29319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29319 raw29319Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw29319 raw29319Labels = mixedMoment B raw29319step0 raw29319step0Labels := by
      have hz : ∀ j, raw29319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29319step0 = (fun i j => raw29319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29319step0 raw29319; decide +kernel
      have hl : raw29319step0Labels = raw29319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29319 raw29319Labels permutation434 hz
    mixedMoment B raw29319step0 raw29319step0Labels = mixedMoment B raw29319step1 raw29319step1Labels := by
      have hz : ∀ j, raw29319step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29319step1 = (fun i j => raw29319step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29319step1 raw29319step0; decide +kernel
      have hl : raw29319step1Labels = raw29319step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29319step0 raw29319step0Labels permutation80 hz
    mixedMoment B raw29319step1 raw29319step1Labels = mixedMoment B raw29319step2 raw29319step2Labels := by
      have ha : raw29319step2 = -raw29319step1 := by apply Matrix.ext; change ∀ i j, raw29319step2 i j = -(raw29319step1 i j); unfold raw29319step2 raw29319step1; decide +kernel
      have hl : raw29319step2Labels = raw29319step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical230
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29454 raw29454Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw29454 raw29454Labels = mixedMoment B raw29454step0 raw29454step0Labels := by
      have hz : ∀ j, raw29454 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29454step0 = (fun i j => raw29454 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29454step0 raw29454; decide +kernel
      have hl : raw29454step0Labels = raw29454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29454 raw29454Labels permutation434 hz
    mixedMoment B raw29454step0 raw29454step0Labels = mixedMoment B raw29454step1 raw29454step1Labels := by
      have ha : raw29454step1 = (fun i j => raw29454step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29454step1 raw29454step0; decide +kernel
      have hl : raw29454step1Labels = raw29454step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29454step0 raw29454step0Labels permutation38 permutation4
    mixedMoment B raw29454step1 raw29454step1Labels = mixedMoment B raw29454step2 raw29454step2Labels := by
      have ha : raw29454step2 = -raw29454step1 := by apply Matrix.ext; change ∀ i j, raw29454step2 i j = -(raw29454step1 i j); unfold raw29454step2 raw29454step1; decide +kernel
      have hl : raw29454step2Labels = raw29454step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3522 node3522Labels := by rfl

theorem canonical29477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29477 raw29477Labels = mixedMoment B node1997 node1997Labels := by
  calc
    mixedMoment B raw29477 raw29477Labels = mixedMoment B raw29477step0 raw29477step0Labels := by
      have ha : raw29477step0 = (fun i j => raw29477 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29477step0 raw29477; decide +kernel
      have hl : raw29477step0Labels = raw29477Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29477 raw29477Labels permutation176 permutation4
    mixedMoment B raw29477step0 raw29477step0Labels = mixedMoment B raw29477step1 raw29477step1Labels := by
      have ha : raw29477step1 = -raw29477step0 := by apply Matrix.ext; change ∀ i j, raw29477step1 i j = -(raw29477step0 i j); unfold raw29477step1 raw29477step0; decide +kernel
      have hl : raw29477step1Labels = raw29477step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1997 node1997Labels := by rfl

theorem canonical29480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29480 raw29480Labels = mixedMoment B node3520 node3520Labels := by
  calc
    mixedMoment B raw29480 raw29480Labels = mixedMoment B raw29480step0 raw29480step0Labels := by
      have ha : raw29480step0 = (fun i j => raw29480 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29480step0 raw29480; decide +kernel
      have hl : raw29480step0Labels = raw29480Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29480 raw29480Labels permutation176 permutation4
    mixedMoment B raw29480step0 raw29480step0Labels = mixedMoment B raw29480step1 raw29480step1Labels := by
      have ha : raw29480step1 = -raw29480step0 := by apply Matrix.ext; change ∀ i j, raw29480step1 i j = -(raw29480step0 i j); unfold raw29480step1 raw29480step0; decide +kernel
      have hl : raw29480step1Labels = raw29480step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3520 node3520Labels := by rfl

theorem canonical29484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29484 raw29484Labels = mixedMoment B node2546 node2546Labels := by
  calc
    _ = mixedMoment B node2546 node2546Labels := by rfl

theorem canonical29485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29485 raw29485Labels = mixedMoment B node2432 node2432Labels := by
  calc
    mixedMoment B raw29485 raw29485Labels = mixedMoment B raw29485step0 raw29485step0Labels := by
      have ha : raw29485step0 = (fun i j => raw29485 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29485step0 raw29485; decide +kernel
      have hl : raw29485step0Labels = raw29485Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29485 raw29485Labels permutation176 permutation2
    _ = mixedMoment B node2432 node2432Labels := by rfl

theorem canonical29487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29487 raw29487Labels = mixedMoment B node2351 node2351Labels := by
  calc
    _ = mixedMoment B node2351 node2351Labels := by rfl

theorem canonical29488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29488 raw29488Labels = mixedMoment B node2556 node2556Labels := by
  calc
    mixedMoment B raw29488 raw29488Labels = mixedMoment B raw29488step0 raw29488step0Labels := by
      have ha : raw29488step0 = (fun i j => raw29488 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29488step0 raw29488; decide +kernel
      have hl : raw29488step0Labels = raw29488Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29488 raw29488Labels permutation153 permutation2
    _ = mixedMoment B node2556 node2556Labels := by rfl

theorem canonical29491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29491 raw29491Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw29491 raw29491Labels = mixedMoment B raw29491step0 raw29491step0Labels := by
      have hz : ∀ j, raw29491 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29491step0 = (fun i j => raw29491 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29491step0 raw29491; decide +kernel
      have hl : raw29491step0Labels = raw29491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29491 raw29491Labels permutation434 hz
    mixedMoment B raw29491step0 raw29491step0Labels = mixedMoment B raw29491step1 raw29491step1Labels := by
      have ha : raw29491step1 = -raw29491step0 := by apply Matrix.ext; change ∀ i j, raw29491step1 i j = -(raw29491step0 i j); unfold raw29491step1 raw29491step0; decide +kernel
      have hl : raw29491step1Labels = raw29491step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3482 node3482Labels := by rfl

theorem canonical29493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29493 raw29493Labels = mixedMoment B node2044 node2044Labels := by
  calc
    mixedMoment B raw29493 raw29493Labels = mixedMoment B raw29493step0 raw29493step0Labels := by
      have ha : raw29493step0 = (fun i j => raw29493 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29493step0 raw29493; decide +kernel
      have hl : raw29493step0Labels = raw29493Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29493 raw29493Labels permutation176 permutation4
    mixedMoment B raw29493step0 raw29493step0Labels = mixedMoment B raw29493step1 raw29493step1Labels := by
      have ha : raw29493step1 = -raw29493step0 := by apply Matrix.ext; change ∀ i j, raw29493step1 i j = -(raw29493step0 i j); unfold raw29493step1 raw29493step0; decide +kernel
      have hl : raw29493step1Labels = raw29493step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2044 node2044Labels := by rfl

theorem canonical29494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29494 raw29494Labels = mixedMoment B node2002 node2002Labels := by
  calc
    mixedMoment B raw29494 raw29494Labels = mixedMoment B raw29494step0 raw29494step0Labels := by
      have ha : raw29494step0 = (fun i j => raw29494 (permutation179 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29494step0 raw29494; decide +kernel
      have hl : raw29494step0Labels = raw29494Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29494 raw29494Labels permutation179 permutation4
    mixedMoment B raw29494step0 raw29494step0Labels = mixedMoment B raw29494step1 raw29494step1Labels := by
      have ha : raw29494step1 = -raw29494step0 := by apply Matrix.ext; change ∀ i j, raw29494step1 i j = -(raw29494step0 i j); unfold raw29494step1 raw29494step0; decide +kernel
      have hl : raw29494step1Labels = raw29494step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2002 node2002Labels := by rfl

theorem canonical29495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29495 raw29495Labels = mixedMoment B node1997 node1997Labels := by
  calc
    mixedMoment B raw29495 raw29495Labels = mixedMoment B raw29495step0 raw29495step0Labels := by
      have ha : raw29495step0 = (fun i j => raw29495 (permutation177 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29495step0 raw29495; decide +kernel
      have hl : raw29495step0Labels = raw29495Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29495 raw29495Labels permutation177 permutation4
    mixedMoment B raw29495step0 raw29495step0Labels = mixedMoment B raw29495step1 raw29495step1Labels := by
      have ha : raw29495step1 = -raw29495step0 := by apply Matrix.ext; change ∀ i j, raw29495step1 i j = -(raw29495step0 i j); unfold raw29495step1 raw29495step0; decide +kernel
      have hl : raw29495step1Labels = raw29495step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1997 node1997Labels := by rfl

theorem canonical29496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29496 raw29496Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw29496 raw29496Labels = mixedMoment B raw29496step0 raw29496step0Labels := by
      have hz : ∀ j, raw29496 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29496step0 = (fun i j => raw29496 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29496step0 raw29496; decide +kernel
      have hl : raw29496step0Labels = raw29496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29496 raw29496Labels permutation434 hz
    mixedMoment B raw29496step0 raw29496step0Labels = mixedMoment B raw29496step1 raw29496step1Labels := by
      have ha : raw29496step1 = (fun i j => raw29496step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29496step1 raw29496step0; decide +kernel
      have hl : raw29496step1Labels = raw29496step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29496step0 raw29496step0Labels permutation38 permutation4
    mixedMoment B raw29496step1 raw29496step1Labels = mixedMoment B raw29496step2 raw29496step2Labels := by
      have ha : raw29496step2 = -raw29496step1 := by apply Matrix.ext; change ∀ i j, raw29496step2 i j = -(raw29496step1 i j); unfold raw29496step2 raw29496step1; decide +kernel
      have hl : raw29496step2Labels = raw29496step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3542 node3542Labels := by rfl

theorem canonical29497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29497 raw29497Labels = mixedMoment B node3616 node3616Labels := by
  calc
    mixedMoment B raw29497 raw29497Labels = mixedMoment B raw29497step0 raw29497step0Labels := by
      have hz : ∀ j, raw29497 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29497step0 = (fun i j => raw29497 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29497step0 raw29497; decide +kernel
      have hl : raw29497step0Labels = raw29497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29497 raw29497Labels permutation434 hz
    mixedMoment B raw29497step0 raw29497step0Labels = mixedMoment B raw29497step1 raw29497step1Labels := by
      have hz : ∀ j, raw29497step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29497step1 = (fun i j => raw29497step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29497step1 raw29497step0; decide +kernel
      have hl : raw29497step1Labels = raw29497step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29497step0 raw29497step0Labels permutation80 hz
    mixedMoment B raw29497step1 raw29497step1Labels = mixedMoment B raw29497step2 raw29497step2Labels := by
      have ha : raw29497step2 = (fun i j => raw29497step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29497step2 raw29497step1; decide +kernel
      have hl : raw29497step2Labels = raw29497step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29497step1 raw29497step1Labels permutation8 permutation4
    mixedMoment B raw29497step2 raw29497step2Labels = mixedMoment B raw29497step3 raw29497step3Labels := by
      have ha : raw29497step3 = -raw29497step2 := by apply Matrix.ext; change ∀ i j, raw29497step3 i j = -(raw29497step2 i j); unfold raw29497step3 raw29497step2; decide +kernel
      have hl : raw29497step3Labels = raw29497step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3616 node3616Labels := by rfl

theorem canonical29498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29498 raw29498Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw29498 raw29498Labels = mixedMoment B raw29498step0 raw29498step0Labels := by
      have hz : ∀ j, raw29498 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29498step0 = (fun i j => raw29498 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29498step0 raw29498; decide +kernel
      have hl : raw29498step0Labels = raw29498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29498 raw29498Labels permutation434 hz
    mixedMoment B raw29498step0 raw29498step0Labels = mixedMoment B raw29498step1 raw29498step1Labels := by
      have ha : raw29498step1 = (fun i j => raw29498step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29498step1 raw29498step0; decide +kernel
      have hl : raw29498step1Labels = raw29498step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29498step0 raw29498step0Labels permutation39 permutation4
    mixedMoment B raw29498step1 raw29498step1Labels = mixedMoment B raw29498step2 raw29498step2Labels := by
      have ha : raw29498step2 = -raw29498step1 := by apply Matrix.ext; change ∀ i j, raw29498step2 i j = -(raw29498step1 i j); unfold raw29498step2 raw29498step1; decide +kernel
      have hl : raw29498step2Labels = raw29498step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3522 node3522Labels := by rfl

theorem canonical29499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29499 raw29499Labels = mixedMoment B node2905 node2905Labels := by
  calc
    mixedMoment B raw29499 raw29499Labels = mixedMoment B raw29499step0 raw29499step0Labels := by
      have ha : raw29499step0 = (fun i j => raw29499 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29499step0 raw29499; decide +kernel
      have hl : raw29499step0Labels = raw29499Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29499 raw29499Labels permutation159 permutation2
    _ = mixedMoment B node2905 node2905Labels := by rfl

theorem canonical29500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29500 raw29500Labels = mixedMoment B node3680 node3680Labels := by
  calc
    mixedMoment B raw29500 raw29500Labels = mixedMoment B raw29500step0 raw29500step0Labels := by
      have ha : raw29500step0 = (fun i j => raw29500 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29500step0 raw29500; decide +kernel
      have hl : raw29500step0Labels = raw29500Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29500 raw29500Labels permutation583 permutation2
    mixedMoment B raw29500step0 raw29500step0Labels = mixedMoment B raw29500step1 raw29500step1Labels := by
      have ha : raw29500step1 = -raw29500step0 := by apply Matrix.ext; change ∀ i j, raw29500step1 i j = -(raw29500step0 i j); unfold raw29500step1 raw29500step0; decide +kernel
      have hl : raw29500step1Labels = raw29500step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3680 node3680Labels := by rfl

theorem canonical29501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29501 raw29501Labels = mixedMoment B node3696 node3696Labels := by
  calc
    mixedMoment B raw29501 raw29501Labels = mixedMoment B raw29501step0 raw29501step0Labels := by
      have ha : raw29501step0 = (fun i j => raw29501 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29501step0 raw29501; decide +kernel
      have hl : raw29501step0Labels = raw29501Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29501 raw29501Labels permutation589 permutation2
    mixedMoment B raw29501step0 raw29501step0Labels = mixedMoment B raw29501step1 raw29501step1Labels := by
      have ha : raw29501step1 = -raw29501step0 := by apply Matrix.ext; change ∀ i j, raw29501step1 i j = -(raw29501step0 i j); unfold raw29501step1 raw29501step0; decide +kernel
      have hl : raw29501step1Labels = raw29501step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3696 node3696Labels := by rfl

theorem canonical29502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29502 raw29502Labels = mixedMoment B node3683 node3683Labels := by
  calc
    mixedMoment B raw29502 raw29502Labels = mixedMoment B raw29502step0 raw29502step0Labels := by
      have ha : raw29502step0 = (fun i j => raw29502 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29502step0 raw29502; decide +kernel
      have hl : raw29502step0Labels = raw29502Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29502 raw29502Labels permutation582 permutation2
    mixedMoment B raw29502step0 raw29502step0Labels = mixedMoment B raw29502step1 raw29502step1Labels := by
      have ha : raw29502step1 = -raw29502step0 := by apply Matrix.ext; change ∀ i j, raw29502step1 i j = -(raw29502step0 i j); unfold raw29502step1 raw29502step0; decide +kernel
      have hl : raw29502step1Labels = raw29502step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3683 node3683Labels := by rfl

theorem canonical29503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29503 raw29503Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw29503 raw29503Labels = mixedMoment B raw29503step0 raw29503step0Labels := by
      have ha : raw29503step0 = (fun i j => raw29503 (permutation508 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29503step0 raw29503; decide +kernel
      have hl : raw29503step0Labels = raw29503Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29503 raw29503Labels permutation508 permutation4
    _ = mixedMoment B node3873 node3873Labels := by rfl

theorem canonical29504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29504 raw29504Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw29504 raw29504Labels = mixedMoment B raw29504step0 raw29504step0Labels := by
      have ha : raw29504step0 = (fun i j => raw29504 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29504step0 raw29504; decide +kernel
      have hl : raw29504step0Labels = raw29504Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29504 raw29504Labels permutation584 permutation2
    mixedMoment B raw29504step0 raw29504step0Labels = mixedMoment B raw29504step1 raw29504step1Labels := by
      have ha : raw29504step1 = -raw29504step0 := by apply Matrix.ext; change ∀ i j, raw29504step1 i j = -(raw29504step0 i j); unfold raw29504step1 raw29504step0; decide +kernel
      have hl : raw29504step1Labels = raw29504step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3796 node3796Labels := by rfl

theorem canonical29505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29505 raw29505Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw29505 raw29505Labels = mixedMoment B raw29505step0 raw29505step0Labels := by
      have ha : raw29505step0 = (fun i j => raw29505 (permutation435 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29505step0 raw29505; decide +kernel
      have hl : raw29505step0Labels = raw29505Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29505 raw29505Labels permutation435 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical29566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29566 raw29566Labels = mixedMoment B node5111 node5111Labels := by
  calc
    mixedMoment B raw29566 raw29566Labels = mixedMoment B raw29566step0 raw29566step0Labels := by
      have hz : ∀ j, raw29566 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29566step0 = (fun i j => raw29566 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29566step0 raw29566; decide +kernel
      have hl : raw29566step0Labels = raw29566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29566 raw29566Labels permutation434 hz
    mixedMoment B raw29566step0 raw29566step0Labels = mixedMoment B raw29566step1 raw29566step1Labels := by
      have hz : ∀ j, raw29566step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29566step1 = (fun i j => raw29566step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29566step1 raw29566step0; decide +kernel
      have hl : raw29566step1Labels = raw29566step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29566step0 raw29566step0Labels permutation80 hz
    mixedMoment B raw29566step1 raw29566step1Labels = mixedMoment B raw29566step2 raw29566step2Labels := by
      have ha : raw29566step2 = (fun i j => raw29566step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29566step2 raw29566step1; decide +kernel
      have hl : raw29566step2Labels = raw29566step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29566step1 raw29566step1Labels permutation9 permutation7
    mixedMoment B raw29566step2 raw29566step2Labels = mixedMoment B raw29566step3 raw29566step3Labels := by
      have ha : raw29566step3 = raw29566step2 := by apply Matrix.ext; unfold raw29566step3 raw29566step2; decide +kernel
      have hl : raw29566step2Labels = labelEmbedding10 ∘ raw29566step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29566step2 raw29566step2Labels raw29566step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5111 node5111Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical231
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29571 raw29571Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw29571 raw29571Labels = mixedMoment B raw29571step0 raw29571step0Labels := by
      have hz : ∀ j, raw29571 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29571step0 = (fun i j => raw29571 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29571step0 raw29571; decide +kernel
      have hl : raw29571step0Labels = raw29571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29571 raw29571Labels permutation434 hz
    mixedMoment B raw29571step0 raw29571step0Labels = mixedMoment B raw29571step1 raw29571step1Labels := by
      have hz : ∀ j, raw29571step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29571step1 = (fun i j => raw29571step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29571step1 raw29571step0; decide +kernel
      have hl : raw29571step1Labels = raw29571step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29571step0 raw29571step0Labels permutation80 hz
    mixedMoment B raw29571step1 raw29571step1Labels = mixedMoment B raw29571step2 raw29571step2Labels := by
      have ha : raw29571step2 = (fun i j => raw29571step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29571step2 raw29571step1; decide +kernel
      have hl : raw29571step2Labels = raw29571step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29571step1 raw29571step1Labels permutation8 permutation6
    mixedMoment B raw29571step2 raw29571step2Labels = mixedMoment B raw29571step3 raw29571step3Labels := by
      have ha : raw29571step3 = raw29571step2 := by apply Matrix.ext; unfold raw29571step3 raw29571step2; decide +kernel
      have hl : raw29571step2Labels = labelEmbedding9 ∘ raw29571step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29571step2 raw29571step2Labels raw29571step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

theorem canonical29576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29576 raw29576Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw29576 raw29576Labels = mixedMoment B raw29576step0 raw29576step0Labels := by
      have hz : ∀ j, raw29576 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29576step0 = (fun i j => raw29576 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29576step0 raw29576; decide +kernel
      have hl : raw29576step0Labels = raw29576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29576 raw29576Labels permutation434 hz
    mixedMoment B raw29576step0 raw29576step0Labels = mixedMoment B raw29576step1 raw29576step1Labels := by
      have ha : raw29576step1 = (fun i j => raw29576step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29576step1 raw29576step0; decide +kernel
      have hl : raw29576step1Labels = raw29576step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29576step0 raw29576step0Labels permutation32 permutation6
    mixedMoment B raw29576step1 raw29576step1Labels = mixedMoment B raw29576step2 raw29576step2Labels := by
      have ha : raw29576step2 = raw29576step1 := by apply Matrix.ext; unfold raw29576step2 raw29576step1; decide +kernel
      have hl : raw29576step1Labels = labelEmbedding9 ∘ raw29576step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29576step1 raw29576step1Labels raw29576step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

theorem canonical29581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29581 raw29581Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw29581 raw29581Labels = mixedMoment B raw29581step0 raw29581step0Labels := by
      have hz : ∀ j, raw29581 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29581step0 = (fun i j => raw29581 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29581step0 raw29581; decide +kernel
      have hl : raw29581step0Labels = raw29581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29581 raw29581Labels permutation346 hz
    mixedMoment B raw29581step0 raw29581step0Labels = mixedMoment B raw29581step1 raw29581step1Labels := by
      have ha : raw29581step1 = (fun i j => raw29581step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29581step1 raw29581step0; decide +kernel
      have hl : raw29581step1Labels = raw29581step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29581step0 raw29581step0Labels permutation32 permutation6
    mixedMoment B raw29581step1 raw29581step1Labels = mixedMoment B raw29581step2 raw29581step2Labels := by
      have ha : raw29581step2 = raw29581step1 := by apply Matrix.ext; unfold raw29581step2 raw29581step1; decide +kernel
      have hl : raw29581step1Labels = labelEmbedding9 ∘ raw29581step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29581step1 raw29581step1Labels raw29581step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

theorem canonical29582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29582 raw29582Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw29582 raw29582Labels = mixedMoment B raw29582step0 raw29582step0Labels := by
      have hz : ∀ j, raw29582 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29582step0 = (fun i j => raw29582 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29582step0 raw29582; decide +kernel
      have hl : raw29582step0Labels = raw29582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29582 raw29582Labels permutation434 hz
    mixedMoment B raw29582step0 raw29582step0Labels = mixedMoment B raw29582step1 raw29582step1Labels := by
      have hz : ∀ j, raw29582step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29582step1 = (fun i j => raw29582step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29582step1 raw29582step0; decide +kernel
      have hl : raw29582step1Labels = raw29582step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29582step0 raw29582step0Labels permutation80 hz
    mixedMoment B raw29582step1 raw29582step1Labels = mixedMoment B raw29582step2 raw29582step2Labels := by
      have ha : raw29582step2 = (fun i j => raw29582step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29582step2 raw29582step1; decide +kernel
      have hl : raw29582step2Labels = raw29582step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29582step1 raw29582step1Labels permutation8 permutation6
    mixedMoment B raw29582step2 raw29582step2Labels = mixedMoment B raw29582step3 raw29582step3Labels := by
      have ha : raw29582step3 = raw29582step2 := by apply Matrix.ext; unfold raw29582step3 raw29582step2; decide +kernel
      have hl : raw29582step2Labels = labelEmbedding9 ∘ raw29582step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29582step2 raw29582step2Labels raw29582step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4846 node4846Labels := by rfl

theorem canonical29583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29583 raw29583Labels = mixedMoment B node5111 node5111Labels := by
  calc
    mixedMoment B raw29583 raw29583Labels = mixedMoment B raw29583step0 raw29583step0Labels := by
      have hz : ∀ j, raw29583 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29583step0 = (fun i j => raw29583 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29583step0 raw29583; decide +kernel
      have hl : raw29583step0Labels = raw29583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29583 raw29583Labels permutation434 hz
    mixedMoment B raw29583step0 raw29583step0Labels = mixedMoment B raw29583step1 raw29583step1Labels := by
      have hz : ∀ j, raw29583step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29583step1 = (fun i j => raw29583step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29583step1 raw29583step0; decide +kernel
      have hl : raw29583step1Labels = raw29583step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29583step0 raw29583step0Labels permutation80 hz
    mixedMoment B raw29583step1 raw29583step1Labels = mixedMoment B raw29583step2 raw29583step2Labels := by
      have ha : raw29583step2 = (fun i j => raw29583step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29583step2 raw29583step1; decide +kernel
      have hl : raw29583step2Labels = raw29583step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29583step1 raw29583step1Labels permutation8 permutation6
    mixedMoment B raw29583step2 raw29583step2Labels = mixedMoment B raw29583step3 raw29583step3Labels := by
      have ha : raw29583step3 = raw29583step2 := by apply Matrix.ext; unfold raw29583step3 raw29583step2; decide +kernel
      have hl : raw29583step2Labels = labelEmbedding9 ∘ raw29583step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29583step2 raw29583step2Labels raw29583step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5111 node5111Labels := by rfl

theorem canonical29584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29584 raw29584Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw29584 raw29584Labels = mixedMoment B raw29584step0 raw29584step0Labels := by
      have hz : ∀ j, raw29584 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29584step0 = (fun i j => raw29584 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29584step0 raw29584; decide +kernel
      have hl : raw29584step0Labels = raw29584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29584 raw29584Labels permutation434 hz
    mixedMoment B raw29584step0 raw29584step0Labels = mixedMoment B raw29584step1 raw29584step1Labels := by
      have ha : raw29584step1 = (fun i j => raw29584step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29584step1 raw29584step0; decide +kernel
      have hl : raw29584step1Labels = raw29584step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29584step0 raw29584step0Labels permutation32 permutation6
    mixedMoment B raw29584step1 raw29584step1Labels = mixedMoment B raw29584step2 raw29584step2Labels := by
      have ha : raw29584step2 = raw29584step1 := by apply Matrix.ext; unfold raw29584step2 raw29584step1; decide +kernel
      have hl : raw29584step1Labels = labelEmbedding9 ∘ raw29584step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29584step1 raw29584step1Labels raw29584step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical29585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29585 raw29585Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw29585 raw29585Labels = mixedMoment B raw29585step0 raw29585step0Labels := by
      have hz : ∀ j, raw29585 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29585step0 = (fun i j => raw29585 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29585step0 raw29585; decide +kernel
      have hl : raw29585step0Labels = raw29585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29585 raw29585Labels permutation346 hz
    mixedMoment B raw29585step0 raw29585step0Labels = mixedMoment B raw29585step1 raw29585step1Labels := by
      have ha : raw29585step1 = (fun i j => raw29585step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29585step1 raw29585step0; decide +kernel
      have hl : raw29585step1Labels = raw29585step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29585step0 raw29585step0Labels permutation32 permutation6
    mixedMoment B raw29585step1 raw29585step1Labels = mixedMoment B raw29585step2 raw29585step2Labels := by
      have ha : raw29585step2 = raw29585step1 := by apply Matrix.ext; unfold raw29585step2 raw29585step1; decide +kernel
      have hl : raw29585step1Labels = labelEmbedding9 ∘ raw29585step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29585step1 raw29585step1Labels raw29585step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical29674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29674 raw29674Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw29674 raw29674Labels = mixedMoment B raw29674step0 raw29674step0Labels := by
      have hz : ∀ j, raw29674 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29674step0 = (fun i j => raw29674 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29674step0 raw29674; decide +kernel
      have hl : raw29674step0Labels = raw29674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29674 raw29674Labels permutation434 hz
    mixedMoment B raw29674step0 raw29674step0Labels = mixedMoment B raw29674step1 raw29674step1Labels := by
      have hz : ∀ j, raw29674step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29674step1 = (fun i j => raw29674step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29674step1 raw29674step0; decide +kernel
      have hl : raw29674step1Labels = raw29674step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29674step0 raw29674step0Labels permutation80 hz
    mixedMoment B raw29674step1 raw29674step1Labels = mixedMoment B raw29674step2 raw29674step2Labels := by
      have ha : raw29674step2 = (fun i j => raw29674step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29674step2 raw29674step1; decide +kernel
      have hl : raw29674step2Labels = raw29674step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29674step1 raw29674step1Labels permutation8 permutation7
    mixedMoment B raw29674step2 raw29674step2Labels = mixedMoment B raw29674step3 raw29674step3Labels := by
      have ha : raw29674step3 = raw29674step2 := by apply Matrix.ext; unfold raw29674step3 raw29674step2; decide +kernel
      have hl : raw29674step2Labels = labelEmbedding10 ∘ raw29674step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29674step2 raw29674step2Labels raw29674step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5177 node5177Labels := by rfl

theorem canonical29675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29675 raw29675Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw29675 raw29675Labels = mixedMoment B raw29675step0 raw29675step0Labels := by
      have hz : ∀ j, raw29675 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29675step0 = (fun i j => raw29675 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29675step0 raw29675; decide +kernel
      have hl : raw29675step0Labels = raw29675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29675 raw29675Labels permutation434 hz
    mixedMoment B raw29675step0 raw29675step0Labels = mixedMoment B raw29675step1 raw29675step1Labels := by
      have ha : raw29675step1 = (fun i j => raw29675step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29675step1 raw29675step0; decide +kernel
      have hl : raw29675step1Labels = raw29675step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29675step0 raw29675step0Labels permutation32 permutation7
    mixedMoment B raw29675step1 raw29675step1Labels = mixedMoment B raw29675step2 raw29675step2Labels := by
      have ha : raw29675step2 = raw29675step1 := by apply Matrix.ext; unfold raw29675step2 raw29675step1; decide +kernel
      have hl : raw29675step1Labels = labelEmbedding10 ∘ raw29675step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29675step1 raw29675step1Labels raw29675step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

theorem canonical29676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29676 raw29676Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw29676 raw29676Labels = mixedMoment B raw29676step0 raw29676step0Labels := by
      have hz : ∀ j, raw29676 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29676step0 = (fun i j => raw29676 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29676step0 raw29676; decide +kernel
      have hl : raw29676step0Labels = raw29676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29676 raw29676Labels permutation346 hz
    mixedMoment B raw29676step0 raw29676step0Labels = mixedMoment B raw29676step1 raw29676step1Labels := by
      have ha : raw29676step1 = (fun i j => raw29676step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29676step1 raw29676step0; decide +kernel
      have hl : raw29676step1Labels = raw29676step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29676step0 raw29676step0Labels permutation32 permutation7
    mixedMoment B raw29676step1 raw29676step1Labels = mixedMoment B raw29676step2 raw29676step2Labels := by
      have ha : raw29676step2 = raw29676step1 := by apply Matrix.ext; unfold raw29676step2 raw29676step1; decide +kernel
      have hl : raw29676step1Labels = labelEmbedding10 ∘ raw29676step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29676step1 raw29676step1Labels raw29676step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

theorem canonical29677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29677 raw29677Labels = mixedMoment B node5111 node5111Labels := by
  calc
    mixedMoment B raw29677 raw29677Labels = mixedMoment B raw29677step0 raw29677step0Labels := by
      have hz : ∀ j, raw29677 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29677step0 = (fun i j => raw29677 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29677step0 raw29677; decide +kernel
      have hl : raw29677step0Labels = raw29677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29677 raw29677Labels permutation434 hz
    mixedMoment B raw29677step0 raw29677step0Labels = mixedMoment B raw29677step1 raw29677step1Labels := by
      have hz : ∀ j, raw29677step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29677step1 = (fun i j => raw29677step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29677step1 raw29677step0; decide +kernel
      have hl : raw29677step1Labels = raw29677step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29677step0 raw29677step0Labels permutation80 hz
    mixedMoment B raw29677step1 raw29677step1Labels = mixedMoment B raw29677step2 raw29677step2Labels := by
      have ha : raw29677step2 = (fun i j => raw29677step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29677step2 raw29677step1; decide +kernel
      have hl : raw29677step2Labels = raw29677step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29677step1 raw29677step1Labels permutation8 permutation7
    mixedMoment B raw29677step2 raw29677step2Labels = mixedMoment B raw29677step3 raw29677step3Labels := by
      have ha : raw29677step3 = raw29677step2 := by apply Matrix.ext; unfold raw29677step3 raw29677step2; decide +kernel
      have hl : raw29677step2Labels = labelEmbedding10 ∘ raw29677step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29677step2 raw29677step2Labels raw29677step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5111 node5111Labels := by rfl

theorem canonical29678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29678 raw29678Labels = mixedMoment B node4875 node4875Labels := by
  calc
    mixedMoment B raw29678 raw29678Labels = mixedMoment B raw29678step0 raw29678step0Labels := by
      have hz : ∀ j, raw29678 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29678step0 = (fun i j => raw29678 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29678step0 raw29678; decide +kernel
      have hl : raw29678step0Labels = raw29678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29678 raw29678Labels permutation434 hz
    mixedMoment B raw29678step0 raw29678step0Labels = mixedMoment B raw29678step1 raw29678step1Labels := by
      have hz : ∀ j, raw29678step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29678step1 = (fun i j => raw29678step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29678step1 raw29678step0; decide +kernel
      have hl : raw29678step1Labels = raw29678step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29678step0 raw29678step0Labels permutation80 hz
    mixedMoment B raw29678step1 raw29678step1Labels = mixedMoment B raw29678step2 raw29678step2Labels := by
      have ha : raw29678step2 = (fun i j => raw29678step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29678step2 raw29678step1; decide +kernel
      have hl : raw29678step2Labels = raw29678step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29678step1 raw29678step1Labels permutation8 permutation6
    mixedMoment B raw29678step2 raw29678step2Labels = mixedMoment B raw29678step3 raw29678step3Labels := by
      have ha : raw29678step3 = raw29678step2 := by apply Matrix.ext; unfold raw29678step3 raw29678step2; decide +kernel
      have hl : raw29678step2Labels = labelEmbedding9 ∘ raw29678step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29678step2 raw29678step2Labels raw29678step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4875 node4875Labels := by rfl

theorem canonical29679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29679 raw29679Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw29679 raw29679Labels = mixedMoment B raw29679step0 raw29679step0Labels := by
      have hz : ∀ j, raw29679 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29679step0 = (fun i j => raw29679 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29679step0 raw29679; decide +kernel
      have hl : raw29679step0Labels = raw29679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29679 raw29679Labels permutation434 hz
    mixedMoment B raw29679step0 raw29679step0Labels = mixedMoment B raw29679step1 raw29679step1Labels := by
      have ha : raw29679step1 = (fun i j => raw29679step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29679step1 raw29679step0; decide +kernel
      have hl : raw29679step1Labels = raw29679step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29679step0 raw29679step0Labels permutation32 permutation6
    mixedMoment B raw29679step1 raw29679step1Labels = mixedMoment B raw29679step2 raw29679step2Labels := by
      have ha : raw29679step2 = raw29679step1 := by apply Matrix.ext; unfold raw29679step2 raw29679step1; decide +kernel
      have hl : raw29679step1Labels = labelEmbedding9 ∘ raw29679step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29679step1 raw29679step1Labels raw29679step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5189 node5189Labels := by rfl

theorem canonical29680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29680 raw29680Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw29680 raw29680Labels = mixedMoment B raw29680step0 raw29680step0Labels := by
      have hz : ∀ j, raw29680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29680step0 = (fun i j => raw29680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29680step0 raw29680; decide +kernel
      have hl : raw29680step0Labels = raw29680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29680 raw29680Labels permutation346 hz
    mixedMoment B raw29680step0 raw29680step0Labels = mixedMoment B raw29680step1 raw29680step1Labels := by
      have ha : raw29680step1 = (fun i j => raw29680step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29680step1 raw29680step0; decide +kernel
      have hl : raw29680step1Labels = raw29680step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29680step0 raw29680step0Labels permutation32 permutation6
    mixedMoment B raw29680step1 raw29680step1Labels = mixedMoment B raw29680step2 raw29680step2Labels := by
      have ha : raw29680step2 = raw29680step1 := by apply Matrix.ext; unfold raw29680step2 raw29680step1; decide +kernel
      have hl : raw29680step1Labels = labelEmbedding9 ∘ raw29680step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29680step1 raw29680step1Labels raw29680step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5189 node5189Labels := by rfl

theorem canonical29681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29681 raw29681Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw29681 raw29681Labels = mixedMoment B raw29681step0 raw29681step0Labels := by
      have hz : ∀ j, raw29681 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29681step0 = (fun i j => raw29681 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29681step0 raw29681; decide +kernel
      have hl : raw29681step0Labels = raw29681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29681 raw29681Labels permutation434 hz
    mixedMoment B raw29681step0 raw29681step0Labels = mixedMoment B raw29681step1 raw29681step1Labels := by
      have hz : ∀ j, raw29681step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29681step1 = (fun i j => raw29681step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29681step1 raw29681step0; decide +kernel
      have hl : raw29681step1Labels = raw29681step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29681step0 raw29681step0Labels permutation80 hz
    mixedMoment B raw29681step1 raw29681step1Labels = mixedMoment B raw29681step2 raw29681step2Labels := by
      have ha : raw29681step2 = (fun i j => raw29681step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29681step2 raw29681step1; decide +kernel
      have hl : raw29681step2Labels = raw29681step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29681step1 raw29681step1Labels permutation9 permutation6
    mixedMoment B raw29681step2 raw29681step2Labels = mixedMoment B raw29681step3 raw29681step3Labels := by
      have ha : raw29681step3 = raw29681step2 := by apply Matrix.ext; unfold raw29681step3 raw29681step2; decide +kernel
      have hl : raw29681step2Labels = labelEmbedding9 ∘ raw29681step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29681step2 raw29681step2Labels raw29681step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

theorem canonical29682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29682 raw29682Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw29682 raw29682Labels = mixedMoment B raw29682step0 raw29682step0Labels := by
      have hz : ∀ j, raw29682 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29682step0 = (fun i j => raw29682 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29682step0 raw29682; decide +kernel
      have hl : raw29682step0Labels = raw29682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29682 raw29682Labels permutation434 hz
    mixedMoment B raw29682step0 raw29682step0Labels = mixedMoment B raw29682step1 raw29682step1Labels := by
      have ha : raw29682step1 = (fun i j => raw29682step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29682step1 raw29682step0; decide +kernel
      have hl : raw29682step1Labels = raw29682step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29682step0 raw29682step0Labels permutation32 permutation6
    mixedMoment B raw29682step1 raw29682step1Labels = mixedMoment B raw29682step2 raw29682step2Labels := by
      have ha : raw29682step2 = raw29682step1 := by apply Matrix.ext; unfold raw29682step2 raw29682step1; decide +kernel
      have hl : raw29682step1Labels = labelEmbedding9 ∘ raw29682step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29682step1 raw29682step1Labels raw29682step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

theorem canonical29683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29683 raw29683Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw29683 raw29683Labels = mixedMoment B raw29683step0 raw29683step0Labels := by
      have hz : ∀ j, raw29683 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29683step0 = (fun i j => raw29683 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29683step0 raw29683; decide +kernel
      have hl : raw29683step0Labels = raw29683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29683 raw29683Labels permutation434 hz
    mixedMoment B raw29683step0 raw29683step0Labels = mixedMoment B raw29683step1 raw29683step1Labels := by
      have ha : raw29683step1 = (fun i j => raw29683step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29683step1 raw29683step0; decide +kernel
      have hl : raw29683step1Labels = raw29683step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29683step0 raw29683step0Labels permutation32 permutation6
    mixedMoment B raw29683step1 raw29683step1Labels = mixedMoment B raw29683step2 raw29683step2Labels := by
      have ha : raw29683step2 = raw29683step1 := by apply Matrix.ext; unfold raw29683step2 raw29683step1; decide +kernel
      have hl : raw29683step1Labels = labelEmbedding9 ∘ raw29683step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29683step1 raw29683step1Labels raw29683step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

theorem canonical29684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29684 raw29684Labels = mixedMoment B node5130 node5130Labels := by
  calc
    mixedMoment B raw29684 raw29684Labels = mixedMoment B raw29684step0 raw29684step0Labels := by
      have ha : raw29684step0 = (fun i j => raw29684 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29684step0 raw29684; decide +kernel
      have hl : raw29684step0Labels = raw29684Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29684 raw29684Labels permutation158 permutation6
    mixedMoment B raw29684step0 raw29684step0Labels = mixedMoment B raw29684step1 raw29684step1Labels := by
      have ha : raw29684step1 = raw29684step0 := by apply Matrix.ext; unfold raw29684step1 raw29684step0; decide +kernel
      have hl : raw29684step0Labels = labelEmbedding9 ∘ raw29684step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29684step0 raw29684step0Labels raw29684step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5130 node5130Labels := by rfl

theorem canonical29685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29685 raw29685Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw29685 raw29685Labels = mixedMoment B raw29685step0 raw29685step0Labels := by
      have hz : ∀ j, raw29685 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29685step0 = (fun i j => raw29685 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29685step0 raw29685; decide +kernel
      have hl : raw29685step0Labels = raw29685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29685 raw29685Labels permutation434 hz
    mixedMoment B raw29685step0 raw29685step0Labels = mixedMoment B raw29685step1 raw29685step1Labels := by
      have ha : raw29685step1 = (fun i j => raw29685step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29685step1 raw29685step0; decide +kernel
      have hl : raw29685step1Labels = raw29685step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29685step0 raw29685step0Labels permutation33 permutation6
    mixedMoment B raw29685step1 raw29685step1Labels = mixedMoment B raw29685step2 raw29685step2Labels := by
      have ha : raw29685step2 = raw29685step1 := by apply Matrix.ext; unfold raw29685step2 raw29685step1; decide +kernel
      have hl : raw29685step1Labels = labelEmbedding9 ∘ raw29685step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29685step1 raw29685step1Labels raw29685step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

theorem canonical29686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29686 raw29686Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw29686 raw29686Labels = mixedMoment B raw29686step0 raw29686step0Labels := by
      have hz : ∀ j, raw29686 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29686step0 = (fun i j => raw29686 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29686step0 raw29686; decide +kernel
      have hl : raw29686step0Labels = raw29686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29686 raw29686Labels permutation346 hz
    mixedMoment B raw29686step0 raw29686step0Labels = mixedMoment B raw29686step1 raw29686step1Labels := by
      have ha : raw29686step1 = (fun i j => raw29686step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29686step1 raw29686step0; decide +kernel
      have hl : raw29686step1Labels = raw29686step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29686step0 raw29686step0Labels permutation32 permutation6
    mixedMoment B raw29686step1 raw29686step1Labels = mixedMoment B raw29686step2 raw29686step2Labels := by
      have ha : raw29686step2 = raw29686step1 := by apply Matrix.ext; unfold raw29686step2 raw29686step1; decide +kernel
      have hl : raw29686step1Labels = labelEmbedding9 ∘ raw29686step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29686step1 raw29686step1Labels raw29686step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

theorem canonical29687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29687 raw29687Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw29687 raw29687Labels = mixedMoment B raw29687step0 raw29687step0Labels := by
      have hz : ∀ j, raw29687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29687step0 = (fun i j => raw29687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29687step0 raw29687; decide +kernel
      have hl : raw29687step0Labels = raw29687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29687 raw29687Labels permutation346 hz
    mixedMoment B raw29687step0 raw29687step0Labels = mixedMoment B raw29687step1 raw29687step1Labels := by
      have ha : raw29687step1 = (fun i j => raw29687step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29687step1 raw29687step0; decide +kernel
      have hl : raw29687step1Labels = raw29687step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29687step0 raw29687step0Labels permutation32 permutation6
    mixedMoment B raw29687step1 raw29687step1Labels = mixedMoment B raw29687step2 raw29687step2Labels := by
      have ha : raw29687step2 = raw29687step1 := by apply Matrix.ext; unfold raw29687step2 raw29687step1; decide +kernel
      have hl : raw29687step1Labels = labelEmbedding9 ∘ raw29687step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29687step1 raw29687step1Labels raw29687step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

theorem canonical29688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29688 raw29688Labels = mixedMoment B node5130 node5130Labels := by
  calc
    mixedMoment B raw29688 raw29688Labels = mixedMoment B raw29688step0 raw29688step0Labels := by
      have ha : raw29688step0 = (fun i j => raw29688 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29688step0 raw29688; decide +kernel
      have hl : raw29688step0Labels = raw29688Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29688 raw29688Labels permutation152 permutation6
    mixedMoment B raw29688step0 raw29688step0Labels = mixedMoment B raw29688step1 raw29688step1Labels := by
      have ha : raw29688step1 = raw29688step0 := by apply Matrix.ext; unfold raw29688step1 raw29688step0; decide +kernel
      have hl : raw29688step0Labels = labelEmbedding9 ∘ raw29688step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29688step0 raw29688step0Labels raw29688step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5130 node5130Labels := by rfl

theorem canonical29689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29689 raw29689Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw29689 raw29689Labels = mixedMoment B raw29689step0 raw29689step0Labels := by
      have hz : ∀ j, raw29689 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29689step0 = (fun i j => raw29689 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29689step0 raw29689; decide +kernel
      have hl : raw29689step0Labels = raw29689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29689 raw29689Labels permutation346 hz
    mixedMoment B raw29689step0 raw29689step0Labels = mixedMoment B raw29689step1 raw29689step1Labels := by
      have ha : raw29689step1 = (fun i j => raw29689step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29689step1 raw29689step0; decide +kernel
      have hl : raw29689step1Labels = raw29689step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29689step0 raw29689step0Labels permutation33 permutation6
    mixedMoment B raw29689step1 raw29689step1Labels = mixedMoment B raw29689step2 raw29689step2Labels := by
      have ha : raw29689step2 = raw29689step1 := by apply Matrix.ext; unfold raw29689step2 raw29689step1; decide +kernel
      have hl : raw29689step1Labels = labelEmbedding9 ∘ raw29689step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29689step1 raw29689step1Labels raw29689step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

theorem canonical29690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29690 raw29690Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw29690 raw29690Labels = mixedMoment B raw29690step0 raw29690step0Labels := by
      have hz : ∀ j, raw29690 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29690step0 = (fun i j => raw29690 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29690step0 raw29690; decide +kernel
      have hl : raw29690step0Labels = raw29690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29690 raw29690Labels permutation434 hz
    mixedMoment B raw29690step0 raw29690step0Labels = mixedMoment B raw29690step1 raw29690step1Labels := by
      have hz : ∀ j, raw29690step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29690step1 = (fun i j => raw29690step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29690step1 raw29690step0; decide +kernel
      have hl : raw29690step1Labels = raw29690step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29690step0 raw29690step0Labels permutation80 hz
    mixedMoment B raw29690step1 raw29690step1Labels = mixedMoment B raw29690step2 raw29690step2Labels := by
      have ha : raw29690step2 = (fun i j => raw29690step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29690step2 raw29690step1; decide +kernel
      have hl : raw29690step2Labels = raw29690step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29690step1 raw29690step1Labels permutation9 permutation6
    mixedMoment B raw29690step2 raw29690step2Labels = mixedMoment B raw29690step3 raw29690step3Labels := by
      have ha : raw29690step3 = raw29690step2 := by apply Matrix.ext; unfold raw29690step3 raw29690step2; decide +kernel
      have hl : raw29690step2Labels = labelEmbedding9 ∘ raw29690step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29690step2 raw29690step2Labels raw29690step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4846 node4846Labels := by rfl

theorem canonical29691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29691 raw29691Labels = mixedMoment B node5111 node5111Labels := by
  calc
    mixedMoment B raw29691 raw29691Labels = mixedMoment B raw29691step0 raw29691step0Labels := by
      have hz : ∀ j, raw29691 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29691step0 = (fun i j => raw29691 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29691step0 raw29691; decide +kernel
      have hl : raw29691step0Labels = raw29691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29691 raw29691Labels permutation434 hz
    mixedMoment B raw29691step0 raw29691step0Labels = mixedMoment B raw29691step1 raw29691step1Labels := by
      have hz : ∀ j, raw29691step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29691step1 = (fun i j => raw29691step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29691step1 raw29691step0; decide +kernel
      have hl : raw29691step1Labels = raw29691step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29691step0 raw29691step0Labels permutation80 hz
    mixedMoment B raw29691step1 raw29691step1Labels = mixedMoment B raw29691step2 raw29691step2Labels := by
      have ha : raw29691step2 = (fun i j => raw29691step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29691step2 raw29691step1; decide +kernel
      have hl : raw29691step2Labels = raw29691step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29691step1 raw29691step1Labels permutation9 permutation6
    mixedMoment B raw29691step2 raw29691step2Labels = mixedMoment B raw29691step3 raw29691step3Labels := by
      have ha : raw29691step3 = raw29691step2 := by apply Matrix.ext; unfold raw29691step3 raw29691step2; decide +kernel
      have hl : raw29691step2Labels = labelEmbedding9 ∘ raw29691step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29691step2 raw29691step2Labels raw29691step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5111 node5111Labels := by rfl

theorem canonical29692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29692 raw29692Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw29692 raw29692Labels = mixedMoment B raw29692step0 raw29692step0Labels := by
      have hz : ∀ j, raw29692 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29692step0 = (fun i j => raw29692 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29692step0 raw29692; decide +kernel
      have hl : raw29692step0Labels = raw29692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29692 raw29692Labels permutation434 hz
    mixedMoment B raw29692step0 raw29692step0Labels = mixedMoment B raw29692step1 raw29692step1Labels := by
      have ha : raw29692step1 = (fun i j => raw29692step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29692step1 raw29692step0; decide +kernel
      have hl : raw29692step1Labels = raw29692step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29692step0 raw29692step0Labels permutation33 permutation6
    mixedMoment B raw29692step1 raw29692step1Labels = mixedMoment B raw29692step2 raw29692step2Labels := by
      have ha : raw29692step2 = raw29692step1 := by apply Matrix.ext; unfold raw29692step2 raw29692step1; decide +kernel
      have hl : raw29692step1Labels = labelEmbedding9 ∘ raw29692step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29692step1 raw29692step1Labels raw29692step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical29693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29693 raw29693Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw29693 raw29693Labels = mixedMoment B raw29693step0 raw29693step0Labels := by
      have hz : ∀ j, raw29693 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29693step0 = (fun i j => raw29693 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29693step0 raw29693; decide +kernel
      have hl : raw29693step0Labels = raw29693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29693 raw29693Labels permutation346 hz
    mixedMoment B raw29693step0 raw29693step0Labels = mixedMoment B raw29693step1 raw29693step1Labels := by
      have ha : raw29693step1 = (fun i j => raw29693step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29693step1 raw29693step0; decide +kernel
      have hl : raw29693step1Labels = raw29693step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29693step0 raw29693step0Labels permutation33 permutation6
    mixedMoment B raw29693step1 raw29693step1Labels = mixedMoment B raw29693step2 raw29693step2Labels := by
      have ha : raw29693step2 = raw29693step1 := by apply Matrix.ext; unfold raw29693step2 raw29693step1; decide +kernel
      have hl : raw29693step1Labels = labelEmbedding9 ∘ raw29693step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29693step1 raw29693step1Labels raw29693step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical29694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29694 raw29694Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw29694 raw29694Labels = mixedMoment B raw29694step0 raw29694step0Labels := by
      have hz : ∀ j, raw29694 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29694step0 = (fun i j => raw29694 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29694step0 raw29694; decide +kernel
      have hl : raw29694step0Labels = raw29694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29694 raw29694Labels permutation434 hz
    mixedMoment B raw29694step0 raw29694step0Labels = mixedMoment B raw29694step1 raw29694step1Labels := by
      have hz : ∀ j, raw29694step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29694step1 = (fun i j => raw29694step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29694step1 raw29694step0; decide +kernel
      have hl : raw29694step1Labels = raw29694step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29694step0 raw29694step0Labels permutation80 hz
    mixedMoment B raw29694step1 raw29694step1Labels = mixedMoment B raw29694step2 raw29694step2Labels := by
      have ha : raw29694step2 = (fun i j => raw29694step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29694step2 raw29694step1; decide +kernel
      have hl : raw29694step2Labels = raw29694step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29694step1 raw29694step1Labels permutation9 permutation6
    mixedMoment B raw29694step2 raw29694step2Labels = mixedMoment B raw29694step3 raw29694step3Labels := by
      have ha : raw29694step3 = raw29694step2 := by apply Matrix.ext; unfold raw29694step3 raw29694step2; decide +kernel
      have hl : raw29694step2Labels = labelEmbedding9 ∘ raw29694step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29694step2 raw29694step2Labels raw29694step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

theorem canonical29695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29695 raw29695Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw29695 raw29695Labels = mixedMoment B raw29695step0 raw29695step0Labels := by
      have hz : ∀ j, raw29695 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29695step0 = (fun i j => raw29695 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29695step0 raw29695; decide +kernel
      have hl : raw29695step0Labels = raw29695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29695 raw29695Labels permutation434 hz
    mixedMoment B raw29695step0 raw29695step0Labels = mixedMoment B raw29695step1 raw29695step1Labels := by
      have hz : ∀ j, raw29695step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29695step1 = (fun i j => raw29695step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29695step1 raw29695step0; decide +kernel
      have hl : raw29695step1Labels = raw29695step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29695step0 raw29695step0Labels permutation80 hz
    mixedMoment B raw29695step1 raw29695step1Labels = mixedMoment B raw29695step2 raw29695step2Labels := by
      have ha : raw29695step2 = (fun i j => raw29695step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29695step2 raw29695step1; decide +kernel
      have hl : raw29695step2Labels = raw29695step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29695step1 raw29695step1Labels permutation8 permutation6
    mixedMoment B raw29695step2 raw29695step2Labels = mixedMoment B raw29695step3 raw29695step3Labels := by
      have ha : raw29695step3 = raw29695step2 := by apply Matrix.ext; unfold raw29695step3 raw29695step2; decide +kernel
      have hl : raw29695step2Labels = labelEmbedding9 ∘ raw29695step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29695step2 raw29695step2Labels raw29695step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical232
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29696 raw29696Labels = mixedMoment B node3616 node3616Labels := by
  calc
    mixedMoment B raw29696 raw29696Labels = mixedMoment B raw29696step0 raw29696step0Labels := by
      have hz : ∀ j, raw29696 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29696step0 = (fun i j => raw29696 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29696step0 raw29696; decide +kernel
      have hl : raw29696step0Labels = raw29696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29696 raw29696Labels permutation434 hz
    mixedMoment B raw29696step0 raw29696step0Labels = mixedMoment B raw29696step1 raw29696step1Labels := by
      have hz : ∀ j, raw29696step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29696step1 = (fun i j => raw29696step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29696step1 raw29696step0; decide +kernel
      have hl : raw29696step1Labels = raw29696step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29696step0 raw29696step0Labels permutation80 hz
    mixedMoment B raw29696step1 raw29696step1Labels = mixedMoment B raw29696step2 raw29696step2Labels := by
      have ha : raw29696step2 = -raw29696step1 := by apply Matrix.ext; change ∀ i j, raw29696step2 i j = -(raw29696step1 i j); unfold raw29696step2 raw29696step1; decide +kernel
      have hl : raw29696step2Labels = raw29696step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3616 node3616Labels := by rfl

theorem canonical29697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29697 raw29697Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw29697 raw29697Labels = mixedMoment B raw29697step0 raw29697step0Labels := by
      have hz : ∀ j, raw29697 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29697step0 = (fun i j => raw29697 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29697step0 raw29697; decide +kernel
      have hl : raw29697step0Labels = raw29697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29697 raw29697Labels permutation346 hz
    mixedMoment B raw29697step0 raw29697step0Labels = mixedMoment B raw29697step1 raw29697step1Labels := by
      have ha : raw29697step1 = -raw29697step0 := by apply Matrix.ext; change ∀ i j, raw29697step1 i j = -(raw29697step0 i j); unfold raw29697step1 raw29697step0; decide +kernel
      have hl : raw29697step1Labels = raw29697step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3482 node3482Labels := by rfl

theorem canonical29698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29698 raw29698Labels = mixedMoment B node3485 node3485Labels := by
  calc
    mixedMoment B raw29698 raw29698Labels = mixedMoment B raw29698step0 raw29698step0Labels := by
      have hz : ∀ j, raw29698 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29698step0 = (fun i j => raw29698 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29698step0 raw29698; decide +kernel
      have hl : raw29698step0Labels = raw29698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29698 raw29698Labels permutation434 hz
    mixedMoment B raw29698step0 raw29698step0Labels = mixedMoment B raw29698step1 raw29698step1Labels := by
      have hz : ∀ j, raw29698step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29698step1 = (fun i j => raw29698step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29698step1 raw29698step0; decide +kernel
      have hl : raw29698step1Labels = raw29698step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29698step0 raw29698step0Labels permutation80 hz
    mixedMoment B raw29698step1 raw29698step1Labels = mixedMoment B raw29698step2 raw29698step2Labels := by
      have ha : raw29698step2 = (fun i j => raw29698step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29698step2 raw29698step1; decide +kernel
      have hl : raw29698step2Labels = raw29698step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29698step1 raw29698step1Labels permutation9 permutation2
    mixedMoment B raw29698step2 raw29698step2Labels = mixedMoment B raw29698step3 raw29698step3Labels := by
      have ha : raw29698step3 = -raw29698step2 := by apply Matrix.ext; change ∀ i j, raw29698step3 i j = -(raw29698step2 i j); unfold raw29698step3 raw29698step2; decide +kernel
      have hl : raw29698step3Labels = raw29698step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3485 node3485Labels := by rfl

theorem canonical29699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29699 raw29699Labels = mixedMoment B node3485 node3485Labels := by
  calc
    mixedMoment B raw29699 raw29699Labels = mixedMoment B raw29699step0 raw29699step0Labels := by
      have hz : ∀ j, raw29699 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29699step0 = (fun i j => raw29699 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29699step0 raw29699; decide +kernel
      have hl : raw29699step0Labels = raw29699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29699 raw29699Labels permutation434 hz
    mixedMoment B raw29699step0 raw29699step0Labels = mixedMoment B raw29699step1 raw29699step1Labels := by
      have hz : ∀ j, raw29699step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29699step1 = (fun i j => raw29699step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29699step1 raw29699step0; decide +kernel
      have hl : raw29699step1Labels = raw29699step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29699step0 raw29699step0Labels permutation80 hz
    mixedMoment B raw29699step1 raw29699step1Labels = mixedMoment B raw29699step2 raw29699step2Labels := by
      have ha : raw29699step2 = -raw29699step1 := by apply Matrix.ext; change ∀ i j, raw29699step2 i j = -(raw29699step1 i j); unfold raw29699step2 raw29699step1; decide +kernel
      have hl : raw29699step2Labels = raw29699step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3485 node3485Labels := by rfl

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

theorem sum_fin_six {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical671 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw671 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw671 = injectiveMoment H raw671step0 := by
      have heq : raw671step0 = -raw671 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw671).symm
    injectiveMoment H raw671step0 = injectiveMoment H raw671step1 := by
      have heq : raw671step1 = (fun i j => raw671step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw671step0 permutation9 permutation8
    _ = injectiveMoment H node169 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical872 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw872 = injectiveMoment H node25 := by
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw214 = injectiveMoment H node9 := by
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

theorem sound25 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node25 = Sparse.eval value25 (momentVector H) := by
  have heq : pivotMatrix25 = (fun u v => node25 (pivotPermutation25 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node25 = injectiveMoment H pivotMatrix25 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix25 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix25 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix25 (0 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (0 : Fin 3) = raw214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical214 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix25 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (1 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix25 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (2 : Fin 3) = raw924 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical924 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node25 + (injectiveMoment H (mergeFirst pivotMatrix25 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix25 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix25 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value25, value10, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound31 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node31 = Sparse.eval value31 (momentVector H) := by
  have hc : momentVector H 7 = injectiveMoment H node31 := rfl
  simp [value31, Sparse.eval, hc]

theorem sound35 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node35 = Sparse.eval value35 (momentVector H) := by
  have hc : momentVector H 8 = injectiveMoment H node35 := rfl
  simp [value35, Sparse.eval, hc]

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

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

theorem sound57 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node57 = Sparse.eval value57 (momentVector H) := by
  have heq : pivotMatrix57 = (fun u v => node57 (pivotPermutation57 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node57 = injectiveMoment H pivotMatrix57 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix57 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix57 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node57 + (injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value57, value10, value4, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1435 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1435 = injectiveMoment H node31 := by
  rfl

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

theorem canonical2862 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2862 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2862 = injectiveMoment H raw2862step0 := by
      have heq : raw2862step0 = (fun i j => raw2862 (permutation3 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2862 permutation3 permutation5
    _ = injectiveMoment H node56 := by rfl

theorem canonical2863 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2863 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2863 = injectiveMoment H raw2863step0 := by
      have heq : raw2863step0 = (fun i j => raw2863 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2863 permutation4 permutation5
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2823 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw2823 = injectiveMoment H raw2823step0 := by
      have heq : raw2823step0 = (fun i j => raw2823 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2823 permutation4 permutation5
    _ = injectiveMoment H node57 := by rfl

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

theorem sound169 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node169 = Sparse.eval value169 (momentVector H) := by
  have heq : pivotMatrix169 = (fun u v => node169 (pivotPermutation169 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node169 = injectiveMoment H pivotMatrix169 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix169 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix169 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix169 (0 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix169 (0 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix169 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix169 (1 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix169 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix169 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node169 + (injectiveMoment H (mergeFirst pivotMatrix169 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix169 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix169 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value169, value31, value36, value57, Sparse.eval] at hc ⊢
  linarith

theorem sound175 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node175 = Sparse.eval value175 (momentVector H) := by
  have heq : pivotMatrix175 = (fun u v => node175 (pivotPermutation175 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node175 = injectiveMoment H pivotMatrix175 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix175 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix175 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix175 (0 : Fin 3)) =
      Sparse.eval value35 (momentVector H) := by
    have heq : mergeFirst pivotMatrix175 (0 : Fin 3) = raw1449 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1449 hH).trans (sound35 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix175 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix175 (1 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix175 (2 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix175 (2 : Fin 3) = raw2863 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2863 hH).trans (sound56 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node175 + (injectiveMoment H (mergeFirst pivotMatrix175 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix175 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix175 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value175, value35, value56, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical672 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw672 = injectiveMoment H node175 := by
  calc
    injectiveMoment H raw672 = injectiveMoment H raw672step0 := by
      have heq : raw672step0 = -raw672 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw672).symm
    injectiveMoment H raw672step0 = injectiveMoment H raw672step1 := by
      have heq : raw672step1 = (fun i j => raw672step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw672step0 permutation9 permutation8
    _ = injectiveMoment H node175 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair343 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node343 node343Labels = Sparse.eval singlePairValue343 (familyPairVector B) := by
  have hp := single_label_three B hB node343
  have hl : node343Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node343 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 1) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node343 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 2) = PairSemantics.raw7685 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node343 PairSemantics.raw7685; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7685 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 3) = PairSemantics.raw872 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node343 PairSemantics.raw872; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical872 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value169 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 4) = PairSemantics.raw671 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node343 PairSemantics.raw671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical671 hH).trans (PairSemantics.sound169 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue343, PairSemantics.value0, PairSemantics.value4, PairSemantics.value11, PairSemantics.value25, PairSemantics.value169, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node344 node344Labels = Sparse.eval singlePairValue344 (familyPairVector B) := by
  have hp := single_label_three B hB node344
  have hl : node344Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node344 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node344 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node344 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node344 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node344 (EqualityPatterns.family3.label 1) = PairSemantics.raw5177 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node344 PairSemantics.raw5177; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5177 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node344 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node344 (EqualityPatterns.family3.label 2) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node344 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node344 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node344 (EqualityPatterns.family3.label 3) = PairSemantics.raw872 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node344 PairSemantics.raw872; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical872 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node344 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value175 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node344 (EqualityPatterns.family3.label 4) = PairSemantics.raw672 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node344 PairSemantics.raw672; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical672 hH).trans (PairSemantics.sound175 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue344, PairSemantics.value0, PairSemantics.value11, PairSemantics.value25, PairSemantics.value65, PairSemantics.value175, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton2604 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2604 node2604Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node343 node343Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw246 singletonSmall2604
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2604) = raw246Labels := by decide +kernel
  rw [hl, canonical246 B hB] at h
  have hc0 : mixedMoment B raw246 (Fin.cases (0 : Fin 1) singletonSmall2604) =
      mixedMoment B node343 node343Labels := by
    have ha : raw246 = raw247 := by apply Matrix.ext; unfold raw246 raw247; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2604 = raw247Labels := by decide +kernel
    rw [ha, hj, canonical247 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton2605 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2605 node2605Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node344 node344Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw248 singletonSmall2605
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2605) = raw248Labels := by decide +kernel
  rw [hl, canonical248 B hB] at h
  have hc0 : mixedMoment B raw248 (Fin.cases (0 : Fin 1) singletonSmall2605) =
      mixedMoment B node344 node344Labels := by
    have ha : raw248 = raw249 := by apply Matrix.ext; unfold raw248 raw249; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2605 = raw249Labels := by decide +kernel
    rw [ha, hj, canonical249 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
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

theorem singleton4811 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4811 node4811Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2029 node2029Labels + mixedMoment B node2225 node2225Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1749 singletonSmall4811
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4811) = raw1749Labels := by decide +kernel
  rw [hl, canonical1749 B hB] at h
  have hc0 : mixedMoment B raw1749 (Fin.cases (0 : Fin 2) singletonSmall4811) =
      mixedMoment B node2029 node2029Labels := by
    have ha : raw1749 = raw1750 := by apply Matrix.ext; unfold raw1749 raw1750; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4811 = raw1750Labels := by decide +kernel
    rw [ha, hj, canonical1750 B hB]
  have hc1 : mixedMoment B raw1749 (Fin.cases (1 : Fin 2) singletonSmall4811) =
      mixedMoment B node2225 node2225Labels := by
    have ha : raw1749 = raw1751 := by apply Matrix.ext; unfold raw1749 raw1751; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4811 = raw1751Labels := by decide +kernel
    rw [ha, hj, canonical1751 B hB]
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

theorem singleton5081 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5081 node5081Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2489 node2489Labels + mixedMoment B node3482 node3482Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2109 singletonSmall5081
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5081) = raw2109Labels := by decide +kernel
  rw [hl, canonical2109 B hB] at h
  have hc0 : mixedMoment B raw2109 (Fin.cases (0 : Fin 2) singletonSmall5081) =
      mixedMoment B node2489 node2489Labels := by
    have ha : raw2109 = raw2110 := by apply Matrix.ext; unfold raw2109 raw2110; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5081 = raw2110Labels := by decide +kernel
    rw [ha, hj, canonical2110 B hB]
  have hc1 : mixedMoment B raw2109 (Fin.cases (1 : Fin 2) singletonSmall5081) =
      mixedMoment B node3482 node3482Labels := by
    have ha : raw2109 = raw2111 := by apply Matrix.ext; unfold raw2109 raw2111; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5081 = raw2111Labels := by decide +kernel
    rw [ha, hj, canonical2111 B hB]
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

theorem singleton5141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5141 node5141Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2561 node2561Labels + mixedMoment B node3522 node3522Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2169 singletonSmall5141
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5141) = raw2169Labels := by decide +kernel
  rw [hl, canonical2169 B hB] at h
  have hc0 : mixedMoment B raw2169 (Fin.cases (0 : Fin 2) singletonSmall5141) =
      mixedMoment B node2561 node2561Labels := by
    have ha : raw2169 = raw2170 := by apply Matrix.ext; unfold raw2169 raw2170; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5141 = raw2170Labels := by decide +kernel
    rw [ha, hj, canonical2170 B hB]
  have hc1 : mixedMoment B raw2169 (Fin.cases (1 : Fin 2) singletonSmall5141) =
      mixedMoment B node3522 node3522Labels := by
    have ha : raw2169 = raw2171 := by apply Matrix.ext; unfold raw2169 raw2171; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5141 = raw2171Labels := by decide +kernel
    rw [ha, hj, canonical2171 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5152 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5152 node5152Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2931 node2931Labels + mixedMoment B node3612 node3612Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2178 singletonSmall5152
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5152) = raw2178Labels := by decide +kernel
  rw [hl, canonical2178 B hB] at h
  have hc0 : mixedMoment B raw2178 (Fin.cases (0 : Fin 2) singletonSmall5152) =
      mixedMoment B node2931 node2931Labels := by
    have ha : raw2178 = raw2179 := by apply Matrix.ext; unfold raw2178 raw2179; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5152 = raw2179Labels := by decide +kernel
    rw [ha, hj, canonical2179 B hB]
  have hc1 : mixedMoment B raw2178 (Fin.cases (1 : Fin 2) singletonSmall5152) =
      mixedMoment B node3612 node3612Labels := by
    have ha : raw2178 = raw2180 := by apply Matrix.ext; unfold raw2178 raw2180; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5152 = raw2180Labels := by decide +kernel
    rw [ha, hj, canonical2180 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5176 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5176 node5176Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2604 node2604Labels + mixedMoment B node3614 node3614Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2214 singletonSmall5176
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5176) = raw2214Labels := by decide +kernel
  rw [hl, canonical2214 B hB] at h
  have hc0 : mixedMoment B raw2214 (Fin.cases (0 : Fin 2) singletonSmall5176) =
      mixedMoment B node2604 node2604Labels := by
    have ha : raw2214 = raw2215 := by apply Matrix.ext; unfold raw2214 raw2215; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5176 = raw2215Labels := by decide +kernel
    rw [ha, hj, canonical2215 B hB]
  have hc1 : mixedMoment B raw2214 (Fin.cases (1 : Fin 2) singletonSmall5176) =
      mixedMoment B node3614 node3614Labels := by
    have ha : raw2214 = raw2216 := by apply Matrix.ext; unfold raw2214 raw2216; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5176 = raw2216Labels := by decide +kernel
    rw [ha, hj, canonical2216 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5177 node5177Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2605 node2605Labels + mixedMoment B node3616 node3616Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2217 singletonSmall5177
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5177) = raw2217Labels := by decide +kernel
  rw [hl, canonical2217 B hB] at h
  have hc0 : mixedMoment B raw2217 (Fin.cases (0 : Fin 2) singletonSmall5177) =
      mixedMoment B node2605 node2605Labels := by
    have ha : raw2217 = raw2218 := by apply Matrix.ext; unfold raw2217 raw2218; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5177 = raw2218Labels := by decide +kernel
    rw [ha, hj, canonical2218 B hB]
  have hc1 : mixedMoment B raw2217 (Fin.cases (1 : Fin 2) singletonSmall5177) =
      mixedMoment B node3616 node3616Labels := by
    have ha : raw2217 = raw2219 := by apply Matrix.ext; unfold raw2217 raw2219; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5177 = raw2219Labels := by decide +kernel
    rw [ha, hj, canonical2219 B hB]
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

theorem singleton5207 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5207 node5207Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2889 node2889Labels + mixedMoment B node3631 node3631Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2235 singletonSmall5207
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5207) = raw2235Labels := by decide +kernel
  rw [hl, canonical2235 B hB] at h
  have hc0 : mixedMoment B raw2235 (Fin.cases (0 : Fin 2) singletonSmall5207) =
      mixedMoment B node2889 node2889Labels := by
    have ha : raw2235 = raw2236 := by apply Matrix.ext; unfold raw2235 raw2236; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5207 = raw2236Labels := by decide +kernel
    rw [ha, hj, canonical2236 B hB]
  have hc1 : mixedMoment B raw2235 (Fin.cases (1 : Fin 2) singletonSmall5207) =
      mixedMoment B node3631 node3631Labels := by
    have ha : raw2235 = raw2237 := by apply Matrix.ext; unfold raw2235 raw2237; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5207 = raw2237Labels := by decide +kernel
    rw [ha, hj, canonical2237 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1152 node1152Labels = Sparse.eval nodeValue1152 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1152) = mixedMoment B node1152 node1152Labels := rfl
  simpa [nodeValue1152, Sparse.eval] using hc.symm

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

theorem sound1997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1997 node1997Labels = Sparse.eval nodeValue1997 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1997) = mixedMoment B node1997 node1997Labels := rfl
  simpa [nodeValue1997, Sparse.eval] using hc.symm

theorem sound2002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2002 node2002Labels = Sparse.eval nodeValue2002 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2002) = mixedMoment B node2002 node2002Labels := rfl
  simpa [nodeValue2002, Sparse.eval] using hc.symm

theorem sound2029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2029 node2029Labels = Sparse.eval nodeValue2029 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2029) = mixedMoment B node2029 node2029Labels := rfl
  simpa [nodeValue2029, Sparse.eval] using hc.symm

theorem sound2044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2044 node2044Labels = Sparse.eval nodeValue2044 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2044) = mixedMoment B node2044 node2044Labels := rfl
  simpa [nodeValue2044, Sparse.eval] using hc.symm

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

theorem sound2225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2225 node2225Labels = Sparse.eval nodeValue2225 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2225) = mixedMoment B node2225 node2225Labels := rfl
  simpa [nodeValue2225, Sparse.eval] using hc.symm

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

theorem sound2288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2288 node2288Labels = Sparse.eval nodeValue2288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2288) = mixedMoment B node2288 node2288Labels := rfl
  simpa [nodeValue2288, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2351 node2351Labels = Sparse.eval nodeValue2351 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2351) = mixedMoment B node2351 node2351Labels := rfl
  simpa [nodeValue2351, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2432 node2432Labels = Sparse.eval nodeValue2432 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2432) = mixedMoment B node2432 node2432Labels := rfl
  simpa [nodeValue2432, Sparse.eval] using hc.symm

theorem sound2489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2489 node2489Labels = Sparse.eval nodeValue2489 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2489) = mixedMoment B node2489 node2489Labels := rfl
  simpa [nodeValue2489, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2546 node2546Labels = 0 := by
  exact mixedMoment_alpha B hF node2546 node2546Labels 1 permutation158
    (by decide +kernel)

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

theorem sound2546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2546 node2546Labels = Sparse.eval nodeValue2546 (mixedVector B) := by
  simpa only [nodeValue2546, Sparse.eval_nil] using zero2546 B _hB _hF

theorem sound2556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2556 node2556Labels = Sparse.eval nodeValue2556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2556) = mixedMoment B node2556 node2556Labels := rfl
  simpa [nodeValue2556, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node343 node343Labels = Sparse.eval nodeValue343 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue343 (familyPairVector B) := singlePair343 B _hB
    _ = _ := by norm_num [singlePairValue343, nodeValue343, Sparse.eval, mixedVector] <;> ring

theorem sound344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node344 node344Labels = Sparse.eval nodeValue344 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue344 (familyPairVector B) := singlePair344 B _hB
    _ = _ := by norm_num [singlePairValue344, nodeValue344, Sparse.eval, mixedVector] <;> ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2561 node2561Labels = Sparse.eval nodeValue2561 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2561) = mixedMoment B node2561 node2561Labels := rfl
  simpa [nodeValue2561, Sparse.eval] using hc.symm

theorem sound2604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2604 node2604Labels = Sparse.eval nodeValue2604 (mixedVector B) := by
  have h := singleton2604 B _hB
  rw [sound343 B _hB _hF] at h
  norm_num [nodeValue2604, nodeValue343, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2605 node2605Labels = Sparse.eval nodeValue2605 (mixedVector B) := by
  have h := singleton2605 B _hB
  rw [sound344 B _hB _hF] at h
  norm_num [nodeValue2605, nodeValue344, Sparse.eval] at h ⊢
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

theorem sound2889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2889 node2889Labels = Sparse.eval nodeValue2889 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2889) = mixedMoment B node2889 node2889Labels := rfl
  simpa [nodeValue2889, Sparse.eval] using hc.symm

theorem sound2905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2905 node2905Labels = Sparse.eval nodeValue2905 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2905) = mixedMoment B node2905 node2905Labels := rfl
  simpa [nodeValue2905, Sparse.eval] using hc.symm

theorem sound2931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2931 node2931Labels = Sparse.eval nodeValue2931 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2931) = mixedMoment B node2931 node2931Labels := rfl
  simpa [nodeValue2931, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3485 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3485 node3485Labels = 0 := by
  exact mixedMoment_order_one B hB node3485 node3485Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3482 node3482Labels = Sparse.eval nodeValue3482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3482) = mixedMoment B node3482 node3482Labels := rfl
  simpa [nodeValue3482, Sparse.eval] using hc.symm

theorem sound3485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3485 node3485Labels = Sparse.eval nodeValue3485 (mixedVector B) := by
  simpa only [nodeValue3485, Sparse.eval_nil] using zero3485 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3520 node3520Labels = 0 := by
  exact mixedMoment_alpha B hF node3520 node3520Labels 1 permutation446
    (by decide +kernel)

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

theorem sound3520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3520 node3520Labels = Sparse.eval nodeValue3520 (mixedVector B) := by
  simpa only [nodeValue3520, Sparse.eval_nil] using zero3520 B _hB _hF

theorem sound3522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3522 node3522Labels = Sparse.eval nodeValue3522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3522) = mixedMoment B node3522 node3522Labels := rfl
  simpa [nodeValue3522, Sparse.eval] using hc.symm

theorem sound3542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3542 node3542Labels = Sparse.eval nodeValue3542 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3542) = mixedMoment B node3542 node3542Labels := rfl
  simpa [nodeValue3542, Sparse.eval] using hc.symm

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

theorem sound3612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3612 node3612Labels = Sparse.eval nodeValue3612 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3612) = mixedMoment B node3612 node3612Labels := rfl
  simpa [nodeValue3612, Sparse.eval] using hc.symm

theorem sound3614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3614 node3614Labels = Sparse.eval nodeValue3614 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3614) = mixedMoment B node3614 node3614Labels := rfl
  simpa [nodeValue3614, Sparse.eval] using hc.symm

theorem sound3616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3616 node3616Labels = Sparse.eval nodeValue3616 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3616) = mixedMoment B node3616 node3616Labels := rfl
  simpa [nodeValue3616, Sparse.eval] using hc.symm

theorem sound3631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3631 node3631Labels = Sparse.eval nodeValue3631 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3631) = mixedMoment B node3631 node3631Labels := rfl
  simpa [nodeValue3631, Sparse.eval] using hc.symm

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

theorem sound3680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3680 node3680Labels = Sparse.eval nodeValue3680 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3680) = mixedMoment B node3680 node3680Labels := rfl
  simpa [nodeValue3680, Sparse.eval] using hc.symm

theorem sound3683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3683 node3683Labels = Sparse.eval nodeValue3683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3683) = mixedMoment B node3683 node3683Labels := rfl
  simpa [nodeValue3683, Sparse.eval] using hc.symm

theorem sound3696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3696 node3696Labels = Sparse.eval nodeValue3696 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3696) = mixedMoment B node3696 node3696Labels := rfl
  simpa [nodeValue3696, Sparse.eval] using hc.symm

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

theorem sound3796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3796 node3796Labels = Sparse.eval nodeValue3796 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3796) = mixedMoment B node3796 node3796Labels := rfl
  simpa [nodeValue3796, Sparse.eval] using hc.symm

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

theorem sound3873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3873 node3873Labels = Sparse.eval nodeValue3873 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3873) = mixedMoment B node3873 node3873Labels := rfl
  simpa [nodeValue3873, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4082 node4082Labels = Sparse.eval nodeValue4082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4082) = mixedMoment B node4082 node4082Labels := rfl
  simpa [nodeValue4082, Sparse.eval] using hc.symm

theorem sound4090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4090 node4090Labels = Sparse.eval nodeValue4090 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4090) = mixedMoment B node4090 node4090Labels := rfl
  simpa [nodeValue4090, Sparse.eval] using hc.symm

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

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

theorem zero4846 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4846 node4846Labels = 0 := by
  exact mixedMoment_order_one B hB node4846 node4846Labels 1
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

theorem sound4811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4811 node4811Labels = Sparse.eval nodeValue4811 (mixedVector B) := by
  have h := singleton4811 B _hB
  rw [sound2029 B _hB _hF, sound2225 B _hB _hF] at h
  norm_num [nodeValue4811, nodeValue2029, nodeValue2225, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4846 node4846Labels = Sparse.eval nodeValue4846 (mixedVector B) := by
  simpa only [nodeValue4846, Sparse.eval_nil] using zero4846 B _hB _hF

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

theorem sound4875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4875 node4875Labels = Sparse.eval nodeValue4875 (mixedVector B) := by
  have h := singleton4875 B _hB
  rw [sound2116 B _hB _hF, sound2288 B _hB _hF] at h
  norm_num [nodeValue4875, nodeValue2116, nodeValue2288, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5111 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5111 node5111Labels = 0 := by
  exact mixedMoment_order_one B hB node5111 node5111Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5081 node5081Labels = Sparse.eval nodeValue5081 (mixedVector B) := by
  have h := singleton5081 B _hB
  rw [sound2489 B _hB _hF, sound3482 B _hB _hF] at h
  norm_num [nodeValue5081, nodeValue2489, nodeValue3482, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5111 node5111Labels = Sparse.eval nodeValue5111 (mixedVector B) := by
  simpa only [nodeValue5111, Sparse.eval_nil] using zero5111 B _hB _hF

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

theorem zero5130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5130 node5130Labels = 0 := by
  exact mixedMoment_alpha B hF node5130 node5130Labels 1 permutation158
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

theorem sound5130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5130 node5130Labels = Sparse.eval nodeValue5130 (mixedVector B) := by
  simpa only [nodeValue5130, Sparse.eval_nil] using zero5130 B _hB _hF

theorem sound5141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5141 node5141Labels = Sparse.eval nodeValue5141 (mixedVector B) := by
  have h := singleton5141 B _hB
  rw [sound2561 B _hB _hF, sound3522 B _hB _hF] at h
  norm_num [nodeValue5141, nodeValue2561, nodeValue3522, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5152 node5152Labels = Sparse.eval nodeValue5152 (mixedVector B) := by
  have h := singleton5152 B _hB
  rw [sound2931 B _hB _hF, sound3612 B _hB _hF] at h
  norm_num [nodeValue5152, nodeValue2931, nodeValue3612, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5176 node5176Labels = Sparse.eval nodeValue5176 (mixedVector B) := by
  have h := singleton5176 B _hB
  rw [sound2604 B _hB _hF, sound3614 B _hB _hF] at h
  norm_num [nodeValue5176, nodeValue2604, nodeValue3614, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5177 node5177Labels = Sparse.eval nodeValue5177 (mixedVector B) := by
  have h := singleton5177 B _hB
  rw [sound2605 B _hB _hF, sound3616 B _hB _hF] at h
  norm_num [nodeValue5177, nodeValue2605, nodeValue3616, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5189 node5189Labels = Sparse.eval nodeValue5189 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5189) = mixedMoment B node5189 node5189Labels := rfl
  simpa [nodeValue5189, Sparse.eval] using hc.symm

theorem sound5207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5207 node5207Labels = Sparse.eval nodeValue5207 (mixedVector B) := by
  have h := singleton5207 B _hB
  rw [sound2889 B _hB _hF, sound3631 B _hB _hF] at h
  norm_num [nodeValue5207, nodeValue2889, nodeValue3631, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources66
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2130 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2130 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2130 + difference 3 0) (sourceB2130 + difference 0 3) sourceC2130) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1152) := by
    have ha : (tripleCharges (sourceA2130 + difference 3 0) (sourceB2130 + difference 0 3) sourceC2130) = raw24556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2130 sourceB2130 sourceC2130 difference raw24556; decide +kernel
    rw [ha]
    exact (canonical24556 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2130 + difference 3 1) (sourceB2130 + difference 1 3) sourceC2130) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2351) := by
    have ha : (tripleCharges (sourceA2130 + difference 3 1) (sourceB2130 + difference 1 3) sourceC2130) = raw29487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2130 sourceB2130 sourceC2130 difference raw29487; decide +kernel
    rw [ha]
    exact (canonical29487 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2130 + difference 3 2) (sourceB2130 + difference 2 3) sourceC2130) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2432) := by
    have ha : (tripleCharges (sourceA2130 + difference 3 2) (sourceB2130 + difference 2 3) sourceC2130) = raw29485 := by
      apply Matrix.ext; unfold tripleCharges sourceA2130 sourceB2130 sourceC2130 difference raw29485; decide +kernel
    rw [ha]
    exact (canonical29485 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2130 + difference 3 3) (sourceB2130 + difference 3 3) sourceC2130) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2546) := by
    have ha : (tripleCharges (sourceA2130 + difference 3 3) (sourceB2130 + difference 3 3) sourceC2130) = raw29484 := by
      apply Matrix.ext; unfold tripleCharges sourceA2130 sourceB2130 sourceC2130 difference raw29484; decide +kernel
    rw [ha]
    exact (canonical29484 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2130 + difference 3 4) (sourceB2130 + difference 4 3) sourceC2130) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA2130 + difference 3 4) (sourceB2130 + difference 4 3) sourceC2130) = raw24553 := by
      apply Matrix.ext; unfold tripleCharges sourceA2130 sourceB2130 sourceC2130 difference raw24553; decide +kernel
    rw [ha]
    exact (canonical24553 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2130 + difference 3 5) (sourceB2130 + difference 5 3) sourceC2130) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA2130 + difference 3 5) (sourceB2130 + difference 5 3) sourceC2130) = raw29488 := by
      apply Matrix.ext; unfold tripleCharges sourceA2130 sourceB2130 sourceC2130 difference raw29488; decide +kernel
    rw [ha]
    exact (canonical29488 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2130 + sourceB2130) sourceC2130) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2130 + sourceB2130) sourceC2130) = raw24552 := by
      apply Matrix.ext; unfold doubleCharges sourceA2130 sourceB2130 sourceC2130 raw24552; decide +kernel
    rw [ha]
    exact (canonical24552 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2130 sourceB2130 sourceC2130
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2130, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2132 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2132 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2132 + difference 0 0) (sourceB2132 + difference 0 0) sourceC2132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3520) := by
    have ha : (tripleCharges (sourceA2132 + difference 0 0) (sourceB2132 + difference 0 0) sourceC2132) = raw29480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2132 sourceB2132 sourceC2132 difference raw29480; decide +kernel
    rw [ha]
    exact (canonical29480 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2132 + difference 1 0) (sourceB2132 + difference 0 1) sourceC2132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2044) := by
    have ha : (tripleCharges (sourceA2132 + difference 1 0) (sourceB2132 + difference 0 1) sourceC2132) = raw29493 := by
      apply Matrix.ext; unfold tripleCharges sourceA2132 sourceB2132 sourceC2132 difference raw29493; decide +kernel
    rw [ha]
    exact (canonical29493 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2132 + difference 2 0) (sourceB2132 + difference 0 2) sourceC2132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA2132 + difference 2 0) (sourceB2132 + difference 0 2) sourceC2132) = raw29317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2132 sourceB2132 sourceC2132 difference raw29317; decide +kernel
    rw [ha]
    exact (canonical29317 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2132 + difference 3 0) (sourceB2132 + difference 0 3) sourceC2132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2002) := by
    have ha : (tripleCharges (sourceA2132 + difference 3 0) (sourceB2132 + difference 0 3) sourceC2132) = raw29494 := by
      apply Matrix.ext; unfold tripleCharges sourceA2132 sourceB2132 sourceC2132 difference raw29494; decide +kernel
    rw [ha]
    exact (canonical29494 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2132 + difference 4 0) (sourceB2132 + difference 0 4) sourceC2132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1997) := by
    have ha : (tripleCharges (sourceA2132 + difference 4 0) (sourceB2132 + difference 0 4) sourceC2132) = raw29495 := by
      apply Matrix.ext; unfold tripleCharges sourceA2132 sourceB2132 sourceC2132 difference raw29495; decide +kernel
    rw [ha]
    exact (canonical29495 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2132 + difference 5 0) (sourceB2132 + difference 0 5) sourceC2132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1997) := by
    have ha : (tripleCharges (sourceA2132 + difference 5 0) (sourceB2132 + difference 0 5) sourceC2132) = raw29477 := by
      apply Matrix.ext; unfold tripleCharges sourceA2132 sourceB2132 sourceC2132 difference raw29477; decide +kernel
    rw [ha]
    exact (canonical29477 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2132 + sourceB2132) sourceC2132) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2132 + sourceB2132) sourceC2132) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2132 sourceB2132 sourceC2132 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2132 sourceB2132 sourceC2132
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2132, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2133 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2133 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2133 + difference 0 3) (sourceB2133 + difference 3 0) sourceC2133) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2133 + difference 0 3) (sourceB2133 + difference 3 0) sourceC2133) = raw29491 := by
      apply Matrix.ext; unfold tripleCharges sourceA2133 sourceB2133 sourceC2133 difference raw29491; decide +kernel
    rw [ha]
    exact (canonical29491 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2133 + difference 1 3) (sourceB2133 + difference 3 1) sourceC2133) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3542) := by
    have ha : (tripleCharges (sourceA2133 + difference 1 3) (sourceB2133 + difference 3 1) sourceC2133) = raw29496 := by
      apply Matrix.ext; unfold tripleCharges sourceA2133 sourceB2133 sourceC2133 difference raw29496; decide +kernel
    rw [ha]
    exact (canonical29496 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2133 + difference 2 3) (sourceB2133 + difference 3 2) sourceC2133) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3616) := by
    have ha : (tripleCharges (sourceA2133 + difference 2 3) (sourceB2133 + difference 3 2) sourceC2133) = raw29497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2133 sourceB2133 sourceC2133 difference raw29497; decide +kernel
    rw [ha]
    exact (canonical29497 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2133 + difference 3 3) (sourceB2133 + difference 3 3) sourceC2133) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3520) := by
    have ha : (tripleCharges (sourceA2133 + difference 3 3) (sourceB2133 + difference 3 3) sourceC2133) = raw29480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2133 sourceB2133 sourceC2133 difference raw29480; decide +kernel
    rw [ha]
    exact (canonical29480 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2133 + difference 4 3) (sourceB2133 + difference 3 4) sourceC2133) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2133 + difference 4 3) (sourceB2133 + difference 3 4) sourceC2133) = raw29498 := by
      apply Matrix.ext; unfold tripleCharges sourceA2133 sourceB2133 sourceC2133 difference raw29498; decide +kernel
    rw [ha]
    exact (canonical29498 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2133 + difference 5 3) (sourceB2133 + difference 3 5) sourceC2133) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2133 + difference 5 3) (sourceB2133 + difference 3 5) sourceC2133) = raw29454 := by
      apply Matrix.ext; unfold tripleCharges sourceA2133 sourceB2133 sourceC2133 difference raw29454; decide +kernel
    rw [ha]
    exact (canonical29454 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2133 + sourceB2133) sourceC2133) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2133 + sourceB2133) sourceC2133) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2133 sourceB2133 sourceC2133 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2133 sourceB2133 sourceC2133
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2133, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2134 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2134 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2134 + difference 0 0) (sourceB2134 + difference 0 0) sourceC2134) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2905) := by
    have ha : (tripleCharges (sourceA2134 + difference 0 0) (sourceB2134 + difference 0 0) sourceC2134) = raw29499 := by
      apply Matrix.ext; unfold tripleCharges sourceA2134 sourceB2134 sourceC2134 difference raw29499; decide +kernel
    rw [ha]
    exact (canonical29499 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2134 + difference 0 1) (sourceB2134 + difference 1 0) sourceC2134) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3680) := by
    have ha : (tripleCharges (sourceA2134 + difference 0 1) (sourceB2134 + difference 1 0) sourceC2134) = raw29500 := by
      apply Matrix.ext; unfold tripleCharges sourceA2134 sourceB2134 sourceC2134 difference raw29500; decide +kernel
    rw [ha]
    exact (canonical29500 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2134 + difference 0 2) (sourceB2134 + difference 2 0) sourceC2134) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3696) := by
    have ha : (tripleCharges (sourceA2134 + difference 0 2) (sourceB2134 + difference 2 0) sourceC2134) = raw29501 := by
      apply Matrix.ext; unfold tripleCharges sourceA2134 sourceB2134 sourceC2134 difference raw29501; decide +kernel
    rw [ha]
    exact (canonical29501 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2134 + difference 0 3) (sourceB2134 + difference 3 0) sourceC2134) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3683) := by
    have ha : (tripleCharges (sourceA2134 + difference 0 3) (sourceB2134 + difference 3 0) sourceC2134) = raw29502 := by
      apply Matrix.ext; unfold tripleCharges sourceA2134 sourceB2134 sourceC2134 difference raw29502; decide +kernel
    rw [ha]
    exact (canonical29502 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2134 + difference 0 4) (sourceB2134 + difference 4 0) sourceC2134) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA2134 + difference 0 4) (sourceB2134 + difference 4 0) sourceC2134) = raw29503 := by
      apply Matrix.ext; unfold tripleCharges sourceA2134 sourceB2134 sourceC2134 difference raw29503; decide +kernel
    rw [ha]
    exact (canonical29503 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2134 + difference 0 5) (sourceB2134 + difference 5 0) sourceC2134) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA2134 + difference 0 5) (sourceB2134 + difference 5 0) sourceC2134) = raw29504 := by
      apply Matrix.ext; unfold tripleCharges sourceA2134 sourceB2134 sourceC2134 difference raw29504; decide +kernel
    rw [ha]
    exact (canonical29504 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2134 + sourceB2134) sourceC2134) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA2134 + sourceB2134) sourceC2134) = raw29505 := by
      apply Matrix.ext; unfold doubleCharges sourceA2134 sourceB2134 sourceC2134 raw29505; decide +kernel
    rw [ha]
    exact (canonical29505 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2134 sourceB2134 sourceC2134
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2134, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources67
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2145 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2145 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2145 + difference 0 1) (sourceB2145 + difference 1 0) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2145 + difference 0 1) (sourceB2145 + difference 1 0) sourceC2145) = raw29674 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29674; decide +kernel
    rw [ha]
    exact (canonical29674 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2145 + difference 0 2) (sourceB2145 + difference 2 0) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2145 + difference 0 2) (sourceB2145 + difference 2 0) sourceC2145) = raw29675 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29675; decide +kernel
    rw [ha]
    exact (canonical29675 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2145 + difference 0 3) (sourceB2145 + difference 3 0) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2145 + difference 0 3) (sourceB2145 + difference 3 0) sourceC2145) = raw29676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29676; decide +kernel
    rw [ha]
    exact (canonical29676 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2145 + difference 0 4) (sourceB2145 + difference 4 0) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2145 + difference 0 4) (sourceB2145 + difference 4 0) sourceC2145) = raw29566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29566; decide +kernel
    rw [ha]
    exact (canonical29566 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2145 + difference 0 5) (sourceB2145 + difference 5 0) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2145 + difference 0 5) (sourceB2145 + difference 5 0) sourceC2145) = raw29677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29677; decide +kernel
    rw [ha]
    exact (canonical29677 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2145 + difference 1 0) (sourceB2145 + difference 0 1) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4875) := by
    have ha : (tripleCharges (sourceA2145 + difference 1 0) (sourceB2145 + difference 0 1) sourceC2145) = raw29678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29678; decide +kernel
    rw [ha]
    exact (canonical29678 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2145 + difference 1 2) (sourceB2145 + difference 2 1) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA2145 + difference 1 2) (sourceB2145 + difference 2 1) sourceC2145) = raw29679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29679; decide +kernel
    rw [ha]
    exact (canonical29679 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2145 + difference 1 3) (sourceB2145 + difference 3 1) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA2145 + difference 1 3) (sourceB2145 + difference 3 1) sourceC2145) = raw29680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29680; decide +kernel
    rw [ha]
    exact (canonical29680 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2145 + difference 1 4) (sourceB2145 + difference 4 1) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2145 + difference 1 4) (sourceB2145 + difference 4 1) sourceC2145) = raw29571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29571; decide +kernel
    rw [ha]
    exact (canonical29571 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2145 + difference 1 5) (sourceB2145 + difference 5 1) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2145 + difference 1 5) (sourceB2145 + difference 5 1) sourceC2145) = raw29681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29681; decide +kernel
    rw [ha]
    exact (canonical29681 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2145 + difference 2 0) (sourceB2145 + difference 0 2) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2145 + difference 2 0) (sourceB2145 + difference 0 2) sourceC2145) = raw29682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29682; decide +kernel
    rw [ha]
    exact (canonical29682 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2145 + difference 2 1) (sourceB2145 + difference 1 2) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2145 + difference 2 1) (sourceB2145 + difference 1 2) sourceC2145) = raw29683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29683; decide +kernel
    rw [ha]
    exact (canonical29683 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2145 + difference 2 3) (sourceB2145 + difference 3 2) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5130) := by
    have ha : (tripleCharges (sourceA2145 + difference 2 3) (sourceB2145 + difference 3 2) sourceC2145) = raw29684 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29684; decide +kernel
    rw [ha]
    exact (canonical29684 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2145 + difference 2 4) (sourceB2145 + difference 4 2) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2145 + difference 2 4) (sourceB2145 + difference 4 2) sourceC2145) = raw29576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29576; decide +kernel
    rw [ha]
    exact (canonical29576 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2145 + difference 2 5) (sourceB2145 + difference 5 2) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2145 + difference 2 5) (sourceB2145 + difference 5 2) sourceC2145) = raw29685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29685; decide +kernel
    rw [ha]
    exact (canonical29685 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2145 + difference 3 0) (sourceB2145 + difference 0 3) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2145 + difference 3 0) (sourceB2145 + difference 0 3) sourceC2145) = raw29686 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29686; decide +kernel
    rw [ha]
    exact (canonical29686 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2145 + difference 3 1) (sourceB2145 + difference 1 3) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2145 + difference 3 1) (sourceB2145 + difference 1 3) sourceC2145) = raw29687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29687; decide +kernel
    rw [ha]
    exact (canonical29687 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2145 + difference 3 2) (sourceB2145 + difference 2 3) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5130) := by
    have ha : (tripleCharges (sourceA2145 + difference 3 2) (sourceB2145 + difference 2 3) sourceC2145) = raw29688 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29688; decide +kernel
    rw [ha]
    exact (canonical29688 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2145 + difference 3 4) (sourceB2145 + difference 4 3) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2145 + difference 3 4) (sourceB2145 + difference 4 3) sourceC2145) = raw29581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29581; decide +kernel
    rw [ha]
    exact (canonical29581 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2145 + difference 3 5) (sourceB2145 + difference 5 3) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2145 + difference 3 5) (sourceB2145 + difference 5 3) sourceC2145) = raw29689 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29689; decide +kernel
    rw [ha]
    exact (canonical29689 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2145 + difference 4 0) (sourceB2145 + difference 0 4) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2145 + difference 4 0) (sourceB2145 + difference 0 4) sourceC2145) = raw29690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29690; decide +kernel
    rw [ha]
    exact (canonical29690 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2145 + difference 4 1) (sourceB2145 + difference 1 4) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2145 + difference 4 1) (sourceB2145 + difference 1 4) sourceC2145) = raw29691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29691; decide +kernel
    rw [ha]
    exact (canonical29691 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2145 + difference 4 2) (sourceB2145 + difference 2 4) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2145 + difference 4 2) (sourceB2145 + difference 2 4) sourceC2145) = raw29692 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29692; decide +kernel
    rw [ha]
    exact (canonical29692 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2145 + difference 4 3) (sourceB2145 + difference 3 4) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2145 + difference 4 3) (sourceB2145 + difference 3 4) sourceC2145) = raw29693 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29693; decide +kernel
    rw [ha]
    exact (canonical29693 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2145 + difference 4 5) (sourceB2145 + difference 5 4) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2145 + difference 4 5) (sourceB2145 + difference 5 4) sourceC2145) = raw29694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29694; decide +kernel
    rw [ha]
    exact (canonical29694 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2145 + difference 5 0) (sourceB2145 + difference 0 5) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2145 + difference 5 0) (sourceB2145 + difference 0 5) sourceC2145) = raw29582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29582; decide +kernel
    rw [ha]
    exact (canonical29582 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2145 + difference 5 1) (sourceB2145 + difference 1 5) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2145 + difference 5 1) (sourceB2145 + difference 1 5) sourceC2145) = raw29583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29583; decide +kernel
    rw [ha]
    exact (canonical29583 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2145 + difference 5 2) (sourceB2145 + difference 2 5) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2145 + difference 5 2) (sourceB2145 + difference 2 5) sourceC2145) = raw29584 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29584; decide +kernel
    rw [ha]
    exact (canonical29584 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2145 + difference 5 3) (sourceB2145 + difference 3 5) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2145 + difference 5 3) (sourceB2145 + difference 3 5) sourceC2145) = raw29585 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29585; decide +kernel
    rw [ha]
    exact (canonical29585 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2145 + difference 5 4) (sourceB2145 + difference 4 5) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2145 + difference 5 4) (sourceB2145 + difference 4 5) sourceC2145) = raw29695 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29695; decide +kernel
    rw [ha]
    exact (canonical29695 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2145 sourceB2145 sourceC2145
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2145, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2146 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2146 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2146 + difference 0 0) (sourceB2146 + difference 0 0) sourceC2146) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3616) := by
    have ha : (tripleCharges (sourceA2146 + difference 0 0) (sourceB2146 + difference 0 0) sourceC2146) = raw29497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2146 sourceB2146 sourceC2146 difference raw29497; decide +kernel
    rw [ha]
    exact (canonical29497 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2146 + difference 0 1) (sourceB2146 + difference 1 0) sourceC2146) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3616) := by
    have ha : (tripleCharges (sourceA2146 + difference 0 1) (sourceB2146 + difference 1 0) sourceC2146) = raw29696 := by
      apply Matrix.ext; unfold tripleCharges sourceA2146 sourceB2146 sourceC2146 difference raw29696; decide +kernel
    rw [ha]
    exact (canonical29696 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2146 + difference 0 2) (sourceB2146 + difference 2 0) sourceC2146) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2146 + difference 0 2) (sourceB2146 + difference 2 0) sourceC2146) = raw29491 := by
      apply Matrix.ext; unfold tripleCharges sourceA2146 sourceB2146 sourceC2146 difference raw29491; decide +kernel
    rw [ha]
    exact (canonical29491 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2146 + difference 0 3) (sourceB2146 + difference 3 0) sourceC2146) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2146 + difference 0 3) (sourceB2146 + difference 3 0) sourceC2146) = raw29697 := by
      apply Matrix.ext; unfold tripleCharges sourceA2146 sourceB2146 sourceC2146 difference raw29697; decide +kernel
    rw [ha]
    exact (canonical29697 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2146 + difference 0 4) (sourceB2146 + difference 4 0) sourceC2146) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3485) := by
    have ha : (tripleCharges (sourceA2146 + difference 0 4) (sourceB2146 + difference 4 0) sourceC2146) = raw29698 := by
      apply Matrix.ext; unfold tripleCharges sourceA2146 sourceB2146 sourceC2146 difference raw29698; decide +kernel
    rw [ha]
    exact (canonical29698 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2146 + difference 0 5) (sourceB2146 + difference 5 0) sourceC2146) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3485) := by
    have ha : (tripleCharges (sourceA2146 + difference 0 5) (sourceB2146 + difference 5 0) sourceC2146) = raw29699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2146 sourceB2146 sourceC2146 difference raw29699; decide +kernel
    rw [ha]
    exact (canonical29699 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2146 + sourceB2146) sourceC2146) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2146 + sourceB2146) sourceC2146) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2146 sourceB2146 sourceC2146 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2146 sourceB2146 sourceC2146
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2146, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1776 : Integer.Sparse.reindex keyMap MixedData.row1776 = numericRow1776 := by decide +kernel

theorem numericCheck1776 (x : Master → ℝ) : Integer.Sparse.eval numericRow1776 x =
    (1 : ℝ) * reducedSource1776 x := by
  norm_num [numericRow1776, reducedSource1776, Integer.Sparse.eval, Sparse.eval, nodeValue1152, nodeValue2351, nodeValue2432, nodeValue2546, nodeValue2556, nodeValue4091]

theorem reindexCheck1777 : Integer.Sparse.reindex keyMap MixedData.row1777 = numericRow1777 := by decide +kernel

theorem numericCheck1777 (x : Master → ℝ) : Integer.Sparse.eval numericRow1777 x =
    (1 : ℝ) * reducedSource1777 x := by
  norm_num [numericRow1777, reducedSource1777, Integer.Sparse.eval, Sparse.eval, nodeValue1997, nodeValue2002, nodeValue2044, nodeValue2225, nodeValue3520, nodeValue4082]

theorem reindexCheck1778 : Integer.Sparse.reindex keyMap MixedData.row1778 = numericRow1778 := by decide +kernel

theorem numericCheck1778 (x : Master → ℝ) : Integer.Sparse.eval numericRow1778 x =
    (1 : ℝ) * reducedSource1778 x := by
  norm_num [numericRow1778, reducedSource1778, Integer.Sparse.eval, Sparse.eval, nodeValue3482, nodeValue3520, nodeValue3522, nodeValue3542, nodeValue3616, nodeValue4082]

theorem reindexCheck1779 : Integer.Sparse.reindex keyMap MixedData.row1779 = numericRow1779 := by decide +kernel

theorem numericCheck1779 (x : Master → ℝ) : Integer.Sparse.eval numericRow1779 x =
    (1 : ℝ) * reducedSource1779 x := by
  norm_num [numericRow1779, reducedSource1779, Integer.Sparse.eval, Sparse.eval, nodeValue2905, nodeValue3680, nodeValue3683, nodeValue3696, nodeValue3796, nodeValue3873, nodeValue4090]

theorem reindexCheck1785 : Integer.Sparse.reindex keyMap MixedData.row1785 = numericRow1785 := by decide +kernel

theorem numericCheck1785 (x : Master → ℝ) : Integer.Sparse.eval numericRow1785 x =
    (720 : ℝ) * reducedSource1785 x := by
  norm_num [numericRow1785, reducedSource1785, Integer.Sparse.eval, Sparse.eval, nodeValue2488, nodeValue2522, nodeValue2523, nodeValue2604, nodeValue2867, nodeValue2888, nodeValue2889, nodeValue2916, nodeValue2930, nodeValue2931, nodeValue2942, nodeValue2943, nodeValue2967, nodeValue2969, nodeValue2990, nodeValue3005, nodeValue3006, nodeValue3095, nodeValue3187, nodeValue3206, nodeValue3216]
  ring

theorem reindexCheck1790 : Integer.Sparse.reindex keyMap MixedData.row1790 = numericRow1790 := by decide +kernel

theorem numericCheck1790 (x : Master → ℝ) : Integer.Sparse.eval numericRow1790 x =
    (4320 : ℝ) * reducedSource1790 x := by
  norm_num [numericRow1790, reducedSource1790, Integer.Sparse.eval, Sparse.eval, nodeValue4811, nodeValue4846, nodeValue4875, nodeValue5081, nodeValue5111, nodeValue5130, nodeValue5141, nodeValue5152, nodeValue5176, nodeValue5177, nodeValue5189, nodeValue5207]
  ring

theorem reindexCheck1791 : Integer.Sparse.reindex keyMap MixedData.row1791 = numericRow1791 := by decide +kernel

theorem numericCheck1791 (x : Master → ℝ) : Integer.Sparse.eval numericRow1791 x =
    (1 : ℝ) * reducedSource1791 x := by
  norm_num [numericRow1791, reducedSource1791, Integer.Sparse.eval, Sparse.eval, nodeValue3482, nodeValue3485, nodeValue3616, nodeValue4082]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1776 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1776 (mixedVector B) = 0 := by
  have h1152 : mixedVector B (Sum.inr 1152) = Sparse.eval nodeValue1152 (mixedVector B) := by
    change mixedMoment B node1152 node1152Labels = _
    exact sound1152 B hB hF
  have h2351 : mixedVector B (Sum.inr 2351) = Sparse.eval nodeValue2351 (mixedVector B) := by
    change mixedMoment B node2351 node2351Labels = _
    exact sound2351 B hB hF
  have h2432 : mixedVector B (Sum.inr 2432) = Sparse.eval nodeValue2432 (mixedVector B) := by
    change mixedMoment B node2432 node2432Labels = _
    exact sound2432 B hB hF
  have h2546 : mixedVector B (Sum.inr 2546) = Sparse.eval nodeValue2546 (mixedVector B) := by
    change mixedMoment B node2546 node2546Labels = _
    exact sound2546 B hB hF
  have h2556 : mixedVector B (Sum.inr 2556) = Sparse.eval nodeValue2556 (mixedVector B) := by
    change mixedMoment B node2556 node2556Labels = _
    exact sound2556 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2130, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1152, h2351, h2432, h2546, h2556, h4091, reducedSource1776] using sourceEq2130 B hB

theorem rowSound1776 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1776 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1776, numericCheck1776, reducedZero1776 B hB hF, mul_zero]

theorem reducedZero1777 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1777 (mixedVector B) = 0 := by
  have h1997 : mixedVector B (Sum.inr 1997) = Sparse.eval nodeValue1997 (mixedVector B) := by
    change mixedMoment B node1997 node1997Labels = _
    exact sound1997 B hB hF
  have h2002 : mixedVector B (Sum.inr 2002) = Sparse.eval nodeValue2002 (mixedVector B) := by
    change mixedMoment B node2002 node2002Labels = _
    exact sound2002 B hB hF
  have h2044 : mixedVector B (Sum.inr 2044) = Sparse.eval nodeValue2044 (mixedVector B) := by
    change mixedMoment B node2044 node2044Labels = _
    exact sound2044 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h3520 : mixedVector B (Sum.inr 3520) = Sparse.eval nodeValue3520 (mixedVector B) := by
    change mixedMoment B node3520 node3520Labels = _
    exact sound3520 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2132, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1997, h2002, h2044, h2225, h3520, h4082, reducedSource1777] using sourceEq2132 B hB

theorem rowSound1777 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1777 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1777, numericCheck1777, reducedZero1777 B hB hF, mul_zero]

theorem reducedZero1778 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1778 (mixedVector B) = 0 := by
  have h3482 : mixedVector B (Sum.inr 3482) = Sparse.eval nodeValue3482 (mixedVector B) := by
    change mixedMoment B node3482 node3482Labels = _
    exact sound3482 B hB hF
  have h3520 : mixedVector B (Sum.inr 3520) = Sparse.eval nodeValue3520 (mixedVector B) := by
    change mixedMoment B node3520 node3520Labels = _
    exact sound3520 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3542 : mixedVector B (Sum.inr 3542) = Sparse.eval nodeValue3542 (mixedVector B) := by
    change mixedMoment B node3542 node3542Labels = _
    exact sound3542 B hB hF
  have h3616 : mixedVector B (Sum.inr 3616) = Sparse.eval nodeValue3616 (mixedVector B) := by
    change mixedMoment B node3616 node3616Labels = _
    exact sound3616 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2133, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3482, h3520, h3522, h3542, h3616, h4082, reducedSource1778] using sourceEq2133 B hB

theorem rowSound1778 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1778 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1778, numericCheck1778, reducedZero1778 B hB hF, mul_zero]

theorem reducedZero1779 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1779 (mixedVector B) = 0 := by
  have h2905 : mixedVector B (Sum.inr 2905) = Sparse.eval nodeValue2905 (mixedVector B) := by
    change mixedMoment B node2905 node2905Labels = _
    exact sound2905 B hB hF
  have h3680 : mixedVector B (Sum.inr 3680) = Sparse.eval nodeValue3680 (mixedVector B) := by
    change mixedMoment B node3680 node3680Labels = _
    exact sound3680 B hB hF
  have h3683 : mixedVector B (Sum.inr 3683) = Sparse.eval nodeValue3683 (mixedVector B) := by
    change mixedMoment B node3683 node3683Labels = _
    exact sound3683 B hB hF
  have h3696 : mixedVector B (Sum.inr 3696) = Sparse.eval nodeValue3696 (mixedVector B) := by
    change mixedMoment B node3696 node3696Labels = _
    exact sound3696 B hB hF
  have h3796 : mixedVector B (Sum.inr 3796) = Sparse.eval nodeValue3796 (mixedVector B) := by
    change mixedMoment B node3796 node3796Labels = _
    exact sound3796 B hB hF
  have h3873 : mixedVector B (Sum.inr 3873) = Sparse.eval nodeValue3873 (mixedVector B) := by
    change mixedMoment B node3873 node3873Labels = _
    exact sound3873 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm2134, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2905, h3680, h3683, h3696, h3796, h3873, h4090, reducedSource1779] using sourceEq2134 B hB

theorem rowSound1779 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1779 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1779, numericCheck1779, reducedZero1779 B hB hF, mul_zero]

theorem rowSound1785 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1785 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1785, numericCheck1785, reducedZero1785_e B hB hF, mul_zero]

theorem reducedZero1790 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1790 (mixedVector B) = 0 := by
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h4875 : mixedVector B (Sum.inr 4875) = Sparse.eval nodeValue4875 (mixedVector B) := by
    change mixedMoment B node4875 node4875Labels = _
    exact sound4875 B hB hF
  have h5081 : mixedVector B (Sum.inr 5081) = Sparse.eval nodeValue5081 (mixedVector B) := by
    change mixedMoment B node5081 node5081Labels = _
    exact sound5081 B hB hF
  have h5111 : mixedVector B (Sum.inr 5111) = Sparse.eval nodeValue5111 (mixedVector B) := by
    change mixedMoment B node5111 node5111Labels = _
    exact sound5111 B hB hF
  have h5130 : mixedVector B (Sum.inr 5130) = Sparse.eval nodeValue5130 (mixedVector B) := by
    change mixedMoment B node5130 node5130Labels = _
    exact sound5130 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5152 : mixedVector B (Sum.inr 5152) = Sparse.eval nodeValue5152 (mixedVector B) := by
    change mixedMoment B node5152 node5152Labels = _
    exact sound5152 B hB hF
  have h5176 : mixedVector B (Sum.inr 5176) = Sparse.eval nodeValue5176 (mixedVector B) := by
    change mixedMoment B node5176 node5176Labels = _
    exact sound5176 B hB hF
  have h5177 : mixedVector B (Sum.inr 5177) = Sparse.eval nodeValue5177 (mixedVector B) := by
    change mixedMoment B node5177 node5177Labels = _
    exact sound5177 B hB hF
  have h5189 : mixedVector B (Sum.inr 5189) = Sparse.eval nodeValue5189 (mixedVector B) := by
    change mixedMoment B node5189 node5189Labels = _
    exact sound5189 B hB hF
  have h5207 : mixedVector B (Sum.inr 5207) = Sparse.eval nodeValue5207 (mixedVector B) := by
    change mixedMoment B node5207 node5207Labels = _
    exact sound5207 B hB hF
  simpa only [sourceForm2145, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4811, h4846, h4875, h5081, h5111, h5130, h5141, h5152, h5176, h5177, h5189, h5207, reducedSource1790] using sourceEq2145 B hB

theorem rowSound1790 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1790 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1790, numericCheck1790, reducedZero1790 B hB hF, mul_zero]

theorem reducedZero1791 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1791 (mixedVector B) = 0 := by
  have h3482 : mixedVector B (Sum.inr 3482) = Sparse.eval nodeValue3482 (mixedVector B) := by
    change mixedMoment B node3482 node3482Labels = _
    exact sound3482 B hB hF
  have h3485 : mixedVector B (Sum.inr 3485) = Sparse.eval nodeValue3485 (mixedVector B) := by
    change mixedMoment B node3485 node3485Labels = _
    exact sound3485 B hB hF
  have h3616 : mixedVector B (Sum.inr 3616) = Sparse.eval nodeValue3616 (mixedVector B) := by
    change mixedMoment B node3616 node3616Labels = _
    exact sound3616 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2146, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3482, h3485, h3616, h4082, reducedSource1791] using sourceEq2146 B hB

theorem rowSound1791 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1791 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1791, numericCheck1791, reducedZero1791 B hB hF, mul_zero]

theorem sourceRowsAt1776 : MixedData.sourceRows (1776 : Fin 2425) =
    MixedData.row1776 := by decide +kernel

theorem sourceRowsAt1777 : MixedData.sourceRows (1777 : Fin 2425) =
    MixedData.row1777 := by decide +kernel

theorem sourceRowsAt1778 : MixedData.sourceRows (1778 : Fin 2425) =
    MixedData.row1778 := by decide +kernel

theorem sourceRowsAt1779 : MixedData.sourceRows (1779 : Fin 2425) =
    MixedData.row1779 := by decide +kernel

theorem sourceRowsAt1780 : MixedData.sourceRows (1780 : Fin 2425) =
    MixedData.row1780 := by decide +kernel

theorem sourceRowsAt1781 : MixedData.sourceRows (1781 : Fin 2425) =
    MixedData.row1781 := by decide +kernel

theorem sourceRowsAt1782 : MixedData.sourceRows (1782 : Fin 2425) =
    MixedData.row1782 := by decide +kernel

theorem sourceRowsAt1783 : MixedData.sourceRows (1783 : Fin 2425) =
    MixedData.row1783 := by decide +kernel

theorem sourceRowsAt1784 : MixedData.sourceRows (1784 : Fin 2425) =
    MixedData.row1784 := by decide +kernel

theorem sourceRowsAt1785 : MixedData.sourceRows (1785 : Fin 2425) =
    MixedData.row1785 := by decide +kernel

theorem sourceRowsAt1786 : MixedData.sourceRows (1786 : Fin 2425) =
    MixedData.row1786 := by decide +kernel

theorem sourceRowsAt1787 : MixedData.sourceRows (1787 : Fin 2425) =
    MixedData.row1787 := by decide +kernel

theorem sourceRowsAt1788 : MixedData.sourceRows (1788 : Fin 2425) =
    MixedData.row1788 := by decide +kernel

theorem sourceRowsAt1789 : MixedData.sourceRows (1789 : Fin 2425) =
    MixedData.row1789 := by decide +kernel

theorem sourceRowsAt1790 : MixedData.sourceRows (1790 : Fin 2425) =
    MixedData.row1790 := by decide +kernel

theorem sourceRowsAt1791 : MixedData.sourceRows (1791 : Fin 2425) =
    MixedData.row1791 := by decide +kernel

theorem chunkSound111_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 111) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1776 ∨ k.val = 1777 ∨ k.val = 1778 ∨ k.val = 1779 ∨ k.val = 1780 ∨ k.val = 1781 ∨ k.val = 1782 ∨ k.val = 1783 ∨ k.val = 1784 ∨ k.val = 1785 ∨ k.val = 1786 ∨ k.val = 1787 ∨ k.val = 1788 ∨ k.val = 1789 ∨ k.val = 1790 ∨ k.val = 1791 := by omega
  rcases heq with h1776 | h1777 | h1778 | h1779 | h1780 | h1781 | h1782 | h1783 | h1784 | h1785 | h1786 | h1787 | h1788 | h1789 | h1790 | h1791
  · have he : k = (1776 : Fin 2425) := Fin.ext h1776
    subst k
    rw [sourceRowsAt1776]
    exact rowSound1776 B hB hF
  · have he : k = (1777 : Fin 2425) := Fin.ext h1777
    subst k
    rw [sourceRowsAt1777]
    exact rowSound1777 B hB hF
  · have he : k = (1778 : Fin 2425) := Fin.ext h1778
    subst k
    rw [sourceRowsAt1778]
    exact rowSound1778 B hB hF
  · have he : k = (1779 : Fin 2425) := Fin.ext h1779
    subst k
    rw [sourceRowsAt1779]
    exact rowSound1779 B hB hF
  · have he : k = (1780 : Fin 2425) := Fin.ext h1780
    subst k
    rw [sourceRowsAt1780]
    exact rowSound1780_e B hB hF
  · have he : k = (1781 : Fin 2425) := Fin.ext h1781
    subst k
    rw [sourceRowsAt1781]
    exact rowSound1781_e B hB hF
  · have he : k = (1782 : Fin 2425) := Fin.ext h1782
    subst k
    rw [sourceRowsAt1782]
    exact rowSound1782_e B hB hF
  · have he : k = (1783 : Fin 2425) := Fin.ext h1783
    subst k
    rw [sourceRowsAt1783]
    exact rowSound1783_e B hB hF
  · have he : k = (1784 : Fin 2425) := Fin.ext h1784
    subst k
    rw [sourceRowsAt1784]
    exact rowSound1784_e B hB hF
  · have he : k = (1785 : Fin 2425) := Fin.ext h1785
    subst k
    rw [sourceRowsAt1785]
    exact rowSound1785 B hB hF
  · have he : k = (1786 : Fin 2425) := Fin.ext h1786
    subst k
    rw [sourceRowsAt1786]
    exact rowSound1786_e B hB hF
  · have he : k = (1787 : Fin 2425) := Fin.ext h1787
    subst k
    rw [sourceRowsAt1787]
    exact rowSound1787_e B hB hF
  · have he : k = (1788 : Fin 2425) := Fin.ext h1788
    subst k
    rw [sourceRowsAt1788]
    exact rowSound1788_e B hB hF
  · have he : k = (1789 : Fin 2425) := Fin.ext h1789
    subst k
    rw [sourceRowsAt1789]
    exact rowSound1789_e B hB hF
  · have he : k = (1790 : Fin 2425) := Fin.ext h1790
    subst k
    rw [sourceRowsAt1790]
    exact rowSound1790 B hB hF
  · have he : k = (1791 : Fin 2425) := Fin.ext h1791
    subst k
    rw [sourceRowsAt1791]
    exact rowSound1791 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e_oai
