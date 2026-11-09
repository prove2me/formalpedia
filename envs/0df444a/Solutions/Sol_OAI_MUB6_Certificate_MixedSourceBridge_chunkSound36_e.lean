-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:34:43.287043+00:00
-- url     : https://prove2.me/submissions/65f1af56-2fe6-4793-b389-526aaad2b3ed

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E150
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E171
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound578_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound579_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound580_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound581_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound582_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound584_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound585_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound587_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound588_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound589_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound591_e

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

theorem mixedMoment_zero_first_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (hA : ∀ i, A i 0 = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A i j.succ) (fun j => label j.succ) := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  unfold mixedIntegrand
  rw [Fin.prod_univ_succ]
  have hz : (fun i => A i 0) = 0 := funext hA
  rw [hz, rowFourier_zero, one_mul]

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

theorem pattern2_0 {B : Type*} (f : Fin 2 → B)
    (h10 : f 1 = f 0)
    : ∀ i j, family2.label 0 i = family2.label 0 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family2, label2, raw2, blocks2, eq_comm]

theorem pattern2_1 {B : Type*} (f : Fin 2 → B)
    (h10 : f 1 ≠ f 0)
    : ∀ i j, family2.label 1 i = family2.label 1 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family2, label2, raw2, blocks2, eq_comm]

theorem covers2 {B : Type*} (f : Fin 2 → B) :
    ∃ p, ∀ i j, (family2.label p i = family2.label p j ↔ f i = f j) := by
  classical
  by_cases h10 : f 1 = f 0
  ·
    refine ⟨0, ?_⟩
    apply pattern2_0 f; simp_all [eq_comm]
  ·
    refine ⟨1, ?_⟩
    apply pattern2_1 f; simp_all [eq_comm]

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

theorem delete_zero_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (σ : Equiv.Perm (Fin (n + 1))) (hz : ∀ i, A i (σ 0) = 0) :
    mixedMoment B A label =
      mixedMoment B (fun i j => A i (σ j.succ)) (fun j => label (σ j.succ)) := by
  rw [← mixedMoment_factor_permutation B A label σ]
  exact mixedMoment_zero_first_factor B _ _ hz

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2914 raw2914Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2914 raw2914Labels = mixedMoment B raw2914step0 raw2914step0Labels := by
      have hz : ∀ j, raw2914 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2914step0 = (fun i j => raw2914 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2914step0 raw2914; decide +kernel
      have hl : raw2914step0Labels = raw2914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2914 raw2914Labels permutation520 hz
    mixedMoment B raw2914step0 raw2914step0Labels = mixedMoment B raw2914step1 raw2914step1Labels := by
      have hz : ∀ j, raw2914step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2914step1 = (fun i j => raw2914step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2914step1 raw2914step0; decide +kernel
      have hl : raw2914step1Labels = raw2914step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2914step0 raw2914step0Labels permutation104 hz
    mixedMoment B raw2914step1 raw2914step1Labels = mixedMoment B raw2914step2 raw2914step2Labels := by
      have hz : ∀ j, raw2914step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2914step2 = (fun i j => raw2914step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2914step2 raw2914step1; decide +kernel
      have hl : raw2914step2Labels = raw2914step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2914step1 raw2914step1Labels permutation20 hz
    mixedMoment B raw2914step2 raw2914step2Labels = mixedMoment B raw2914step3 raw2914step3Labels := by
      have hz : ∀ i, raw2914step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2914step3 = (fun i j => raw2914step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2914step3 raw2914step2; decide +kernel
      have hl : raw2914step3Labels = (fun j => raw2914step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2914step2 raw2914step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical2919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2919 raw2919Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2919 raw2919Labels = mixedMoment B raw2919step0 raw2919step0Labels := by
      have hz : ∀ j, raw2919 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2919step0 = (fun i j => raw2919 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2919step0 raw2919; decide +kernel
      have hl : raw2919step0Labels = raw2919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2919 raw2919Labels permutation520 hz
    mixedMoment B raw2919step0 raw2919step0Labels = mixedMoment B raw2919step1 raw2919step1Labels := by
      have hz : ∀ j, raw2919step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2919step1 = (fun i j => raw2919step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2919step1 raw2919step0; decide +kernel
      have hl : raw2919step1Labels = raw2919step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2919step0 raw2919step0Labels permutation104 hz
    mixedMoment B raw2919step1 raw2919step1Labels = mixedMoment B raw2919step2 raw2919step2Labels := by
      have hz : ∀ j, raw2919step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2919step2 = (fun i j => raw2919step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2919step2 raw2919step1; decide +kernel
      have hl : raw2919step2Labels = raw2919step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2919step1 raw2919step1Labels permutation14 hz
    mixedMoment B raw2919step2 raw2919step2Labels = mixedMoment B raw2919step3 raw2919step3Labels := by
      have hz : ∀ i, raw2919step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2919step3 = (fun i j => raw2919step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2919step3 raw2919step2; decide +kernel
      have hl : raw2919step3Labels = (fun j => raw2919step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2919step2 raw2919step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical2924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2924 raw2924Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2924 raw2924Labels = mixedMoment B raw2924step0 raw2924step0Labels := by
      have hz : ∀ j, raw2924 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2924step0 = (fun i j => raw2924 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2924step0 raw2924; decide +kernel
      have hl : raw2924step0Labels = raw2924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2924 raw2924Labels permutation520 hz
    mixedMoment B raw2924step0 raw2924step0Labels = mixedMoment B raw2924step1 raw2924step1Labels := by
      have hz : ∀ j, raw2924step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2924step1 = (fun i j => raw2924step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2924step1 raw2924step0; decide +kernel
      have hl : raw2924step1Labels = raw2924step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2924step0 raw2924step0Labels permutation80 hz
    mixedMoment B raw2924step1 raw2924step1Labels = mixedMoment B raw2924step2 raw2924step2Labels := by
      have hz : ∀ j, raw2924step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2924step2 = (fun i j => raw2924step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2924step2 raw2924step1; decide +kernel
      have hl : raw2924step2Labels = raw2924step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2924step1 raw2924step1Labels permutation14 hz
    mixedMoment B raw2924step2 raw2924step2Labels = mixedMoment B raw2924step3 raw2924step3Labels := by
      have hz : ∀ i, raw2924step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2924step3 = (fun i j => raw2924step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2924step3 raw2924step2; decide +kernel
      have hl : raw2924step3Labels = (fun j => raw2924step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2924step2 raw2924step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical2930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2930 raw2930Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2930 raw2930Labels = mixedMoment B raw2930step0 raw2930step0Labels := by
      have hz : ∀ j, raw2930 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2930step0 = (fun i j => raw2930 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2930step0 raw2930; decide +kernel
      have hl : raw2930step0Labels = raw2930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2930 raw2930Labels permutation434 hz
    mixedMoment B raw2930step0 raw2930step0Labels = mixedMoment B raw2930step1 raw2930step1Labels := by
      have hz : ∀ j, raw2930step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2930step1 = (fun i j => raw2930step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2930step1 raw2930step0; decide +kernel
      have hl : raw2930step1Labels = raw2930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2930step0 raw2930step0Labels permutation80 hz
    mixedMoment B raw2930step1 raw2930step1Labels = mixedMoment B raw2930step2 raw2930step2Labels := by
      have hz : ∀ i, raw2930step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2930step2 = (fun i j => raw2930step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2930step2 raw2930step1; decide +kernel
      have hl : raw2930step2Labels = (fun j => raw2930step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2930step1 raw2930step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2931 raw2931Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2931 raw2931Labels = mixedMoment B raw2931step0 raw2931step0Labels := by
      have hz : ∀ j, raw2931 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2931step0 = (fun i j => raw2931 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2931step0 raw2931; decide +kernel
      have hl : raw2931step0Labels = raw2931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2931 raw2931Labels permutation434 hz
    mixedMoment B raw2931step0 raw2931step0Labels = mixedMoment B raw2931step1 raw2931step1Labels := by
      have hz : ∀ j, raw2931step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2931step1 = (fun i j => raw2931step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2931step1 raw2931step0; decide +kernel
      have hl : raw2931step1Labels = raw2931step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2931step0 raw2931step0Labels permutation56 hz
    mixedMoment B raw2931step1 raw2931step1Labels = mixedMoment B raw2931step2 raw2931step2Labels := by
      have hz : ∀ i, raw2931step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2931step2 = (fun i j => raw2931step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2931step2 raw2931step1; decide +kernel
      have hl : raw2931step2Labels = (fun j => raw2931step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2931step1 raw2931step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2932 raw2932Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2932 raw2932Labels = mixedMoment B raw2932step0 raw2932step0Labels := by
      have hz : ∀ j, raw2932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2932step0 = (fun i j => raw2932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2932step0 raw2932; decide +kernel
      have hl : raw2932step0Labels = raw2932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2932 raw2932Labels permutation346 hz
    mixedMoment B raw2932step0 raw2932step0Labels = mixedMoment B raw2932step1 raw2932step1Labels := by
      have hz : ∀ j, raw2932step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2932step1 = (fun i j => raw2932step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2932step1 raw2932step0; decide +kernel
      have hl : raw2932step1Labels = raw2932step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2932step0 raw2932step0Labels permutation56 hz
    mixedMoment B raw2932step1 raw2932step1Labels = mixedMoment B raw2932step2 raw2932step2Labels := by
      have hz : ∀ i, raw2932step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2932step2 = (fun i j => raw2932step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2932step2 raw2932step1; decide +kernel
      have hl : raw2932step2Labels = (fun j => raw2932step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2932step1 raw2932step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical2933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2933 raw2933Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2933 raw2933Labels = mixedMoment B raw2933step0 raw2933step0Labels := by
      have hz : ∀ j, raw2933 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2933step0 = (fun i j => raw2933 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2933step0 raw2933; decide +kernel
      have hl : raw2933step0Labels = raw2933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2933 raw2933Labels permutation434 hz
    mixedMoment B raw2933step0 raw2933step0Labels = mixedMoment B raw2933step1 raw2933step1Labels := by
      have hz : ∀ j, raw2933step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2933step1 = (fun i j => raw2933step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2933step1 raw2933step0; decide +kernel
      have hl : raw2933step1Labels = raw2933step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2933step0 raw2933step0Labels permutation80 hz
    mixedMoment B raw2933step1 raw2933step1Labels = mixedMoment B raw2933step2 raw2933step2Labels := by
      have hz : ∀ j, raw2933step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2933step2 = (fun i j => raw2933step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2933step2 raw2933step1; decide +kernel
      have hl : raw2933step2Labels = raw2933step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2933step1 raw2933step1Labels permutation14 hz
    mixedMoment B raw2933step2 raw2933step2Labels = mixedMoment B raw2933step3 raw2933step3Labels := by
      have hz : ∀ i, raw2933step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2933step3 = (fun i j => raw2933step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2933step3 raw2933step2; decide +kernel
      have hl : raw2933step3Labels = (fun j => raw2933step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2933step2 raw2933step2Labels permutation6 hz
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical2934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2934 raw2934Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw2934 raw2934Labels = mixedMoment B raw2934step0 raw2934step0Labels := by
      have hz : ∀ j, raw2934 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2934step0 = (fun i j => raw2934 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2934step0 raw2934; decide +kernel
      have hl : raw2934step0Labels = raw2934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934 raw2934Labels permutation520 hz
    mixedMoment B raw2934step0 raw2934step0Labels = mixedMoment B raw2934step1 raw2934step1Labels := by
      have hz : ∀ j, raw2934step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2934step1 = (fun i j => raw2934step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2934step1 raw2934step0; decide +kernel
      have hl : raw2934step1Labels = raw2934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934step0 raw2934step0Labels permutation104 hz
    mixedMoment B raw2934step1 raw2934step1Labels = mixedMoment B raw2934step2 raw2934step2Labels := by
      have hz : ∀ j, raw2934step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2934step2 = (fun i j => raw2934step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2934step2 raw2934step1; decide +kernel
      have hl : raw2934step2Labels = raw2934step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934step1 raw2934step1Labels permutation20 hz
    mixedMoment B raw2934step2 raw2934step2Labels = mixedMoment B raw2934step3 raw2934step3Labels := by
      have hz : ∀ j, raw2934step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw2934step3 = (fun i j => raw2934step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw2934step3 raw2934step2; decide +kernel
      have hl : raw2934step3Labels = raw2934step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934step2 raw2934step2Labels permutation4 hz
    mixedMoment B raw2934step3 raw2934step3Labels = mixedMoment B raw2934step4 raw2934step4Labels := by
      have hz : ∀ i, raw2934step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2934step4 = (fun i j => raw2934step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2934step4 raw2934step3; decide +kernel
      have hl : raw2934step4Labels = (fun j => raw2934step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2934step3 raw2934step3Labels permutation6 hz
    _ = mixedMoment B node4085 node4085Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3323 raw3323Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw3323 raw3323Labels = mixedMoment B raw3323step0 raw3323step0Labels := by
      have hz : ∀ j, raw3323 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3323step0 = (fun i j => raw3323 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3323step0 raw3323; decide +kernel
      have hl : raw3323step0Labels = raw3323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3323 raw3323Labels permutation434 hz
    mixedMoment B raw3323step0 raw3323step0Labels = mixedMoment B raw3323step1 raw3323step1Labels := by
      have hz : ∀ j, raw3323step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3323step1 = (fun i j => raw3323step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3323step1 raw3323step0; decide +kernel
      have hl : raw3323step1Labels = raw3323step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3323step0 raw3323step0Labels permutation80 hz
    mixedMoment B raw3323step1 raw3323step1Labels = mixedMoment B raw3323step2 raw3323step2Labels := by
      have hz : ∀ i, raw3323step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3323step2 = (fun i j => raw3323step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3323step2 raw3323step1; decide +kernel
      have hl : raw3323step2Labels = (fun j => raw3323step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3323step1 raw3323step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical3327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3327 raw3327Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw3327 raw3327Labels = mixedMoment B raw3327step0 raw3327step0Labels := by
      have hz : ∀ j, raw3327 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3327step0 = (fun i j => raw3327 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3327step0 raw3327; decide +kernel
      have hl : raw3327step0Labels = raw3327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3327 raw3327Labels permutation434 hz
    mixedMoment B raw3327step0 raw3327step0Labels = mixedMoment B raw3327step1 raw3327step1Labels := by
      have hz : ∀ j, raw3327step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3327step1 = (fun i j => raw3327step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3327step1 raw3327step0; decide +kernel
      have hl : raw3327step1Labels = raw3327step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3327step0 raw3327step0Labels permutation56 hz
    mixedMoment B raw3327step1 raw3327step1Labels = mixedMoment B raw3327step2 raw3327step2Labels := by
      have hz : ∀ i, raw3327step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3327step2 = (fun i j => raw3327step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3327step2 raw3327step1; decide +kernel
      have hl : raw3327step2Labels = (fun j => raw3327step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3327step1 raw3327step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3331 raw3331Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw3331 raw3331Labels = mixedMoment B raw3331step0 raw3331step0Labels := by
      have hz : ∀ j, raw3331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3331step0 = (fun i j => raw3331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3331step0 raw3331; decide +kernel
      have hl : raw3331step0Labels = raw3331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3331 raw3331Labels permutation346 hz
    mixedMoment B raw3331step0 raw3331step0Labels = mixedMoment B raw3331step1 raw3331step1Labels := by
      have hz : ∀ j, raw3331step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3331step1 = (fun i j => raw3331step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3331step1 raw3331step0; decide +kernel
      have hl : raw3331step1Labels = raw3331step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3331step0 raw3331step0Labels permutation56 hz
    mixedMoment B raw3331step1 raw3331step1Labels = mixedMoment B raw3331step2 raw3331step2Labels := by
      have hz : ∀ i, raw3331step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3331step2 = (fun i j => raw3331step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3331step2 raw3331step1; decide +kernel
      have hl : raw3331step2Labels = (fun j => raw3331step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3331step1 raw3331step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical3335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3335 raw3335Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw3335 raw3335Labels = mixedMoment B raw3335step0 raw3335step0Labels := by
      have hz : ∀ j, raw3335 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3335step0 = (fun i j => raw3335 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3335step0 raw3335; decide +kernel
      have hl : raw3335step0Labels = raw3335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3335 raw3335Labels permutation434 hz
    mixedMoment B raw3335step0 raw3335step0Labels = mixedMoment B raw3335step1 raw3335step1Labels := by
      have hz : ∀ j, raw3335step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3335step1 = (fun i j => raw3335step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3335step1 raw3335step0; decide +kernel
      have hl : raw3335step1Labels = raw3335step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3335step0 raw3335step0Labels permutation80 hz
    mixedMoment B raw3335step1 raw3335step1Labels = mixedMoment B raw3335step2 raw3335step2Labels := by
      have hz : ∀ j, raw3335step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3335step2 = (fun i j => raw3335step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3335step2 raw3335step1; decide +kernel
      have hl : raw3335step2Labels = raw3335step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3335step1 raw3335step1Labels permutation14 hz
    mixedMoment B raw3335step2 raw3335step2Labels = mixedMoment B raw3335step3 raw3335step3Labels := by
      have hz : ∀ i, raw3335step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3335step3 = (fun i j => raw3335step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3335step3 raw3335step2; decide +kernel
      have hl : raw3335step3Labels = (fun j => raw3335step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3335step2 raw3335step2Labels permutation6 hz
    mixedMoment B raw3335step3 raw3335step3Labels = mixedMoment B raw3335step4 raw3335step4Labels := by
      have ha : raw3335step4 = (fun i j => raw3335step3 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3335step4 raw3335step3; decide +kernel
      have hl : raw3335step4Labels = raw3335step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3335step3 raw3335step3Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical3340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3340 raw3340Labels = mixedMoment B node4094 node4094Labels := by
  calc
    mixedMoment B raw3340 raw3340Labels = mixedMoment B raw3340step0 raw3340step0Labels := by
      have hz : ∀ j, raw3340 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3340step0 = (fun i j => raw3340 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3340step0 raw3340; decide +kernel
      have hl : raw3340step0Labels = raw3340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3340 raw3340Labels permutation520 hz
    mixedMoment B raw3340step0 raw3340step0Labels = mixedMoment B raw3340step1 raw3340step1Labels := by
      have hz : ∀ j, raw3340step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3340step1 = (fun i j => raw3340step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3340step1 raw3340step0; decide +kernel
      have hl : raw3340step1Labels = raw3340step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3340step0 raw3340step0Labels permutation104 hz
    mixedMoment B raw3340step1 raw3340step1Labels = mixedMoment B raw3340step2 raw3340step2Labels := by
      have hz : ∀ j, raw3340step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3340step2 = (fun i j => raw3340step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3340step2 raw3340step1; decide +kernel
      have hl : raw3340step2Labels = raw3340step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3340step1 raw3340step1Labels permutation20 hz
    mixedMoment B raw3340step2 raw3340step2Labels = mixedMoment B raw3340step3 raw3340step3Labels := by
      have hz : ∀ j, raw3340step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw3340step3 = (fun i j => raw3340step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw3340step3 raw3340step2; decide +kernel
      have hl : raw3340step3Labels = raw3340step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3340step2 raw3340step2Labels permutation4 hz
    mixedMoment B raw3340step3 raw3340step3Labels = mixedMoment B raw3340step4 raw3340step4Labels := by
      have hz : ∀ i, raw3340step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3340step4 = (fun i j => raw3340step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3340step4 raw3340step3; decide +kernel
      have hl : raw3340step4Labels = (fun j => raw3340step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3340step3 raw3340step3Labels permutation6 hz
    _ = mixedMoment B node4094 node4094Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5209 raw5209Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw5209 raw5209Labels = mixedMoment B raw5209step0 raw5209step0Labels := by
      have hz : ∀ j, raw5209 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5209step0 = (fun i j => raw5209 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5209step0 raw5209; decide +kernel
      have hl : raw5209step0Labels = raw5209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5209 raw5209Labels permutation434 hz
    mixedMoment B raw5209step0 raw5209step0Labels = mixedMoment B raw5209step1 raw5209step1Labels := by
      have hz : ∀ j, raw5209step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5209step1 = (fun i j => raw5209step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5209step1 raw5209step0; decide +kernel
      have hl : raw5209step1Labels = raw5209step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5209step0 raw5209step0Labels permutation80 hz
    mixedMoment B raw5209step1 raw5209step1Labels = mixedMoment B raw5209step2 raw5209step2Labels := by
      have hz : ∀ j, raw5209step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5209step2 = (fun i j => raw5209step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5209step2 raw5209step1; decide +kernel
      have hl : raw5209step2Labels = raw5209step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5209step1 raw5209step1Labels permutation14 hz
    mixedMoment B raw5209step2 raw5209step2Labels = mixedMoment B raw5209step3 raw5209step3Labels := by
      have hz : ∀ i, raw5209step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5209step3 = (fun i j => raw5209step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5209step3 raw5209step2; decide +kernel
      have hl : raw5209step3Labels = (fun j => raw5209step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5209step2 raw5209step2Labels permutation6 hz
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical5210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5210 raw5210Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5210 raw5210Labels = mixedMoment B raw5210step0 raw5210step0Labels := by
      have hz : ∀ j, raw5210 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5210step0 = (fun i j => raw5210 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5210step0 raw5210; decide +kernel
      have hl : raw5210step0Labels = raw5210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5210 raw5210Labels permutation434 hz
    mixedMoment B raw5210step0 raw5210step0Labels = mixedMoment B raw5210step1 raw5210step1Labels := by
      have hz : ∀ j, raw5210step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5210step1 = (fun i j => raw5210step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5210step1 raw5210step0; decide +kernel
      have hl : raw5210step1Labels = raw5210step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5210step0 raw5210step0Labels permutation80 hz
    mixedMoment B raw5210step1 raw5210step1Labels = mixedMoment B raw5210step2 raw5210step2Labels := by
      have hz : ∀ i, raw5210step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5210step2 = (fun i j => raw5210step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5210step2 raw5210step1; decide +kernel
      have hl : raw5210step2Labels = (fun j => raw5210step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5210step1 raw5210step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical5211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5211 raw5211Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5211 raw5211Labels = mixedMoment B raw5211step0 raw5211step0Labels := by
      have hz : ∀ j, raw5211 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5211step0 = (fun i j => raw5211 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5211step0 raw5211; decide +kernel
      have hl : raw5211step0Labels = raw5211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5211 raw5211Labels permutation434 hz
    mixedMoment B raw5211step0 raw5211step0Labels = mixedMoment B raw5211step1 raw5211step1Labels := by
      have hz : ∀ j, raw5211step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5211step1 = (fun i j => raw5211step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5211step1 raw5211step0; decide +kernel
      have hl : raw5211step1Labels = raw5211step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5211step0 raw5211step0Labels permutation56 hz
    mixedMoment B raw5211step1 raw5211step1Labels = mixedMoment B raw5211step2 raw5211step2Labels := by
      have hz : ∀ i, raw5211step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5211step2 = (fun i j => raw5211step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5211step2 raw5211step1; decide +kernel
      have hl : raw5211step2Labels = (fun j => raw5211step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5211step1 raw5211step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical5212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5212 raw5212Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw5212 raw5212Labels = mixedMoment B raw5212step0 raw5212step0Labels := by
      have hz : ∀ j, raw5212 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5212step0 = (fun i j => raw5212 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5212step0 raw5212; decide +kernel
      have hl : raw5212step0Labels = raw5212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5212 raw5212Labels permutation346 hz
    mixedMoment B raw5212step0 raw5212step0Labels = mixedMoment B raw5212step1 raw5212step1Labels := by
      have hz : ∀ j, raw5212step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5212step1 = (fun i j => raw5212step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5212step1 raw5212step0; decide +kernel
      have hl : raw5212step1Labels = raw5212step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5212step0 raw5212step0Labels permutation56 hz
    mixedMoment B raw5212step1 raw5212step1Labels = mixedMoment B raw5212step2 raw5212step2Labels := by
      have hz : ∀ i, raw5212step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw5212step2 = (fun i j => raw5212step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw5212step2 raw5212step1; decide +kernel
      have hl : raw5212step2Labels = (fun j => raw5212step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5212step1 raw5212step1Labels permutation6 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5754 raw5754Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5754 raw5754Labels = mixedMoment B raw5754step0 raw5754step0Labels := by
      have hz : ∀ j, raw5754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5754step0 = (fun i j => raw5754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5754step0 raw5754; decide +kernel
      have hl : raw5754step0Labels = raw5754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754 raw5754Labels permutation434 hz
    mixedMoment B raw5754step0 raw5754step0Labels = mixedMoment B raw5754step1 raw5754step1Labels := by
      have hz : ∀ j, raw5754step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5754step1 = (fun i j => raw5754step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5754step1 raw5754step0; decide +kernel
      have hl : raw5754step1Labels = raw5754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754step0 raw5754step0Labels permutation80 hz
    mixedMoment B raw5754step1 raw5754step1Labels = mixedMoment B raw5754step2 raw5754step2Labels := by
      have hz : ∀ j, raw5754step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5754step2 = (fun i j => raw5754step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5754step2 raw5754step1; decide +kernel
      have hl : raw5754step2Labels = raw5754step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754step1 raw5754step1Labels permutation14 hz
    mixedMoment B raw5754step2 raw5754step2Labels = mixedMoment B raw5754step3 raw5754step3Labels := by
      have ha : raw5754step3 = -raw5754step2 := by apply Matrix.ext; change ∀ i j, raw5754step3 i j = -(raw5754step2 i j); unfold raw5754step3 raw5754step2; decide +kernel
      have hl : raw5754step3Labels = raw5754step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical5759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5759 raw5759Labels = mixedMoment B node1038 node1038Labels := by
  calc
    mixedMoment B raw5759 raw5759Labels = mixedMoment B raw5759step0 raw5759step0Labels := by
      have ha : raw5759step0 = (fun i j => raw5759 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5759step0 raw5759; decide +kernel
      have hl : raw5759step0Labels = raw5759Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5759 raw5759Labels permutation224 permutation4
    mixedMoment B raw5759step0 raw5759step0Labels = mixedMoment B raw5759step1 raw5759step1Labels := by
      have ha : raw5759step1 = -raw5759step0 := by apply Matrix.ext; change ∀ i j, raw5759step1 i j = -(raw5759step0 i j); unfold raw5759step1 raw5759step0; decide +kernel
      have hl : raw5759step1Labels = raw5759step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1038 node1038Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5770 raw5770Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw5770 raw5770Labels = mixedMoment B raw5770step0 raw5770step0Labels := by
      have hz : ∀ j, raw5770 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5770step0 = (fun i j => raw5770 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5770step0 raw5770; decide +kernel
      have hl : raw5770step0Labels = raw5770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5770 raw5770Labels permutation434 hz
    mixedMoment B raw5770step0 raw5770step0Labels = mixedMoment B raw5770step1 raw5770step1Labels := by
      have ha : raw5770step1 = (fun i j => raw5770step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5770step1 raw5770step0; decide +kernel
      have hl : raw5770step1Labels = raw5770step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5770step0 raw5770step0Labels permutation44 permutation4
    mixedMoment B raw5770step1 raw5770step1Labels = mixedMoment B raw5770step2 raw5770step2Labels := by
      have ha : raw5770step2 = -raw5770step1 := by apply Matrix.ext; change ∀ i j, raw5770step2 i j = -(raw5770step1 i j); unfold raw5770step2 raw5770step1; decide +kernel
      have hl : raw5770step2Labels = raw5770step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2262 node2262Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw660 raw660Labels = mixedMoment B node4093 node4093Labels := by
  calc
    _ = mixedMoment B node4093 node4093Labels := by rfl

theorem canonical661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw661 raw661Labels = mixedMoment B node5 node5Labels := by
  calc
    _ = mixedMoment B node5 node5Labels := by rfl

theorem canonical662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw662 raw662Labels = mixedMoment B node4094 node4094Labels := by
  calc
    _ = mixedMoment B node4094 node4094Labels := by rfl

theorem canonical663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw663 raw663Labels = mixedMoment B node6 node6Labels := by
  calc
    _ = mixedMoment B node6 node6Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11016 raw11016Labels = mixedMoment B node1042 node1042Labels := by
  calc
    mixedMoment B raw11016 raw11016Labels = mixedMoment B raw11016step0 raw11016step0Labels := by
      have hz : ∀ j, raw11016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11016step0 = (fun i j => raw11016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11016step0 raw11016; decide +kernel
      have hl : raw11016step0Labels = raw11016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11016 raw11016Labels permutation434 hz
    mixedMoment B raw11016step0 raw11016step0Labels = mixedMoment B raw11016step1 raw11016step1Labels := by
      have ha : raw11016step1 = (fun i j => raw11016step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11016step1 raw11016step0; decide +kernel
      have hl : raw11016step1Labels = raw11016step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11016step0 raw11016step0Labels permutation47 permutation4
    mixedMoment B raw11016step1 raw11016step1Labels = mixedMoment B raw11016step2 raw11016step2Labels := by
      have ha : raw11016step2 = -raw11016step1 := by apply Matrix.ext; change ∀ i j, raw11016step2 i j = -(raw11016step1 i j); unfold raw11016step2 raw11016step1; decide +kernel
      have hl : raw11016step2Labels = raw11016step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1042 node1042Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11201 raw11201Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw11201 raw11201Labels = mixedMoment B raw11201step0 raw11201step0Labels := by
      have hz : ∀ j, raw11201 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11201step0 = (fun i j => raw11201 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11201step0 raw11201; decide +kernel
      have hl : raw11201step0Labels = raw11201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11201 raw11201Labels permutation434 hz
    mixedMoment B raw11201step0 raw11201step0Labels = mixedMoment B raw11201step1 raw11201step1Labels := by
      have ha : raw11201step1 = (fun i j => raw11201step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11201step1 raw11201step0; decide +kernel
      have hl : raw11201step1Labels = raw11201step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11201step0 raw11201step0Labels permutation32 permutation4
    mixedMoment B raw11201step1 raw11201step1Labels = mixedMoment B raw11201step2 raw11201step2Labels := by
      have ha : raw11201step2 = -raw11201step1 := by apply Matrix.ext; change ∀ i j, raw11201step2 i j = -(raw11201step1 i j); unfold raw11201step2 raw11201step1; decide +kernel
      have hl : raw11201step2Labels = raw11201step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1079 node1079Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11292 raw11292Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw11292 raw11292Labels = mixedMoment B raw11292step0 raw11292step0Labels := by
      have hz : ∀ j, raw11292 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11292step0 = (fun i j => raw11292 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11292step0 raw11292; decide +kernel
      have hl : raw11292step0Labels = raw11292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11292 raw11292Labels permutation434 hz
    _ = mixedMoment B node2244 node2244Labels := by rfl

theorem canonical11293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11293 raw11293Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw11293 raw11293Labels = mixedMoment B raw11293step0 raw11293step0Labels := by
      have hz : ∀ j, raw11293 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11293step0 = (fun i j => raw11293 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11293step0 raw11293; decide +kernel
      have hl : raw11293step0Labels = raw11293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11293 raw11293Labels permutation434 hz
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical11298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11298 raw11298Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw11298 raw11298Labels = mixedMoment B raw11298step0 raw11298step0Labels := by
      have hz : ∀ j, raw11298 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11298step0 = (fun i j => raw11298 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11298step0 raw11298; decide +kernel
      have hl : raw11298step0Labels = raw11298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11298 raw11298Labels permutation520 hz
    mixedMoment B raw11298step0 raw11298step0Labels = mixedMoment B raw11298step1 raw11298step1Labels := by
      have hz : ∀ j, raw11298step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11298step1 = (fun i j => raw11298step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11298step1 raw11298step0; decide +kernel
      have hl : raw11298step1Labels = raw11298step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11298step0 raw11298step0Labels permutation104 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical11301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11301 raw11301Labels = mixedMoment B node1020 node1020Labels := by
  calc
    _ = mixedMoment B node1020 node1020Labels := by rfl

theorem canonical11308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11308 raw11308Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw11308 raw11308Labels = mixedMoment B raw11308step0 raw11308step0Labels := by
      have hz : ∀ j, raw11308 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11308step0 = (fun i j => raw11308 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11308step0 raw11308; decide +kernel
      have hl : raw11308step0Labels = raw11308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11308 raw11308Labels permutation434 hz
    mixedMoment B raw11308step0 raw11308step0Labels = mixedMoment B raw11308step1 raw11308step1Labels := by
      have ha : raw11308step1 = (fun i j => raw11308step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11308step1 raw11308step0; decide +kernel
      have hl : raw11308step1Labels = raw11308step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11308step0 raw11308step0Labels permutation34 permutation2
    _ = mixedMoment B node2107 node2107Labels := by rfl

theorem canonical11309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11309 raw11309Labels = mixedMoment B node2088 node2088Labels := by
  calc
    _ = mixedMoment B node2088 node2088Labels := by rfl

theorem canonical11310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11310 raw11310Labels = mixedMoment B node2094 node2094Labels := by
  calc
    mixedMoment B raw11310 raw11310Labels = mixedMoment B raw11310step0 raw11310step0Labels := by
      have hz : ∀ j, raw11310 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11310step0 = (fun i j => raw11310 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11310step0 raw11310; decide +kernel
      have hl : raw11310step0Labels = raw11310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11310 raw11310Labels permutation434 hz
    _ = mixedMoment B node2094 node2094Labels := by rfl

theorem canonical11311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11311 raw11311Labels = mixedMoment B node2090 node2090Labels := by
  calc
    mixedMoment B raw11311 raw11311Labels = mixedMoment B raw11311step0 raw11311step0Labels := by
      have hz : ∀ j, raw11311 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11311step0 = (fun i j => raw11311 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11311step0 raw11311; decide +kernel
      have hl : raw11311step0Labels = raw11311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11311 raw11311Labels permutation434 hz
    _ = mixedMoment B node2090 node2090Labels := by rfl

theorem canonical11312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11312 raw11312Labels = mixedMoment B node2088 node2088Labels := by
  calc
    mixedMoment B raw11312 raw11312Labels = mixedMoment B raw11312step0 raw11312step0Labels := by
      have ha : raw11312step0 = (fun i j => raw11312 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11312step0 raw11312; decide +kernel
      have hl : raw11312step0Labels = raw11312Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11312 raw11312Labels permutation176 permutation2
    _ = mixedMoment B node2088 node2088Labels := by rfl

theorem canonical11313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11313 raw11313Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw11313 raw11313Labels = mixedMoment B raw11313step0 raw11313step0Labels := by
      have hz : ∀ j, raw11313 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11313step0 = (fun i j => raw11313 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11313step0 raw11313; decide +kernel
      have hl : raw11313step0Labels = raw11313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11313 raw11313Labels permutation520 hz
    _ = mixedMoment B node2244 node2244Labels := by rfl

theorem canonical11314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11314 raw11314Labels = mixedMoment B node2243 node2243Labels := by
  calc
    _ = mixedMoment B node2243 node2243Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11396 raw11396Labels = mixedMoment B node1042 node1042Labels := by
  calc
    mixedMoment B raw11396 raw11396Labels = mixedMoment B raw11396step0 raw11396step0Labels := by
      have hz : ∀ j, raw11396 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11396step0 = (fun i j => raw11396 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11396step0 raw11396; decide +kernel
      have hl : raw11396step0Labels = raw11396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11396 raw11396Labels permutation434 hz
    mixedMoment B raw11396step0 raw11396step0Labels = mixedMoment B raw11396step1 raw11396step1Labels := by
      have ha : raw11396step1 = (fun i j => raw11396step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11396step1 raw11396step0; decide +kernel
      have hl : raw11396step1Labels = raw11396step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11396step0 raw11396step0Labels permutation45 permutation4
    mixedMoment B raw11396step1 raw11396step1Labels = mixedMoment B raw11396step2 raw11396step2Labels := by
      have ha : raw11396step2 = -raw11396step1 := by apply Matrix.ext; change ∀ i j, raw11396step2 i j = -(raw11396step1 i j); unfold raw11396step2 raw11396step1; decide +kernel
      have hl : raw11396step2Labels = raw11396step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1042 node1042Labels := by rfl

theorem canonical11397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11397 raw11397Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw11397 raw11397Labels = mixedMoment B raw11397step0 raw11397step0Labels := by
      have hz : ∀ j, raw11397 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11397step0 = (fun i j => raw11397 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11397step0 raw11397; decide +kernel
      have hl : raw11397step0Labels = raw11397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11397 raw11397Labels permutation434 hz
    mixedMoment B raw11397step0 raw11397step0Labels = mixedMoment B raw11397step1 raw11397step1Labels := by
      have ha : raw11397step1 = (fun i j => raw11397step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11397step1 raw11397step0; decide +kernel
      have hl : raw11397step1Labels = raw11397step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11397step0 raw11397step0Labels permutation44 permutation4
    mixedMoment B raw11397step1 raw11397step1Labels = mixedMoment B raw11397step2 raw11397step2Labels := by
      have ha : raw11397step2 = -raw11397step1 := by apply Matrix.ext; change ∀ i j, raw11397step2 i j = -(raw11397step1 i j); unfold raw11397step2 raw11397step1; decide +kernel
      have hl : raw11397step2Labels = raw11397step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1040 node1040Labels := by rfl

theorem canonical11458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11458 raw11458Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw11458 raw11458Labels = mixedMoment B raw11458step0 raw11458step0Labels := by
      have hz : ∀ j, raw11458 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11458step0 = (fun i j => raw11458 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11458step0 raw11458; decide +kernel
      have hl : raw11458step0Labels = raw11458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11458 raw11458Labels permutation434 hz
    mixedMoment B raw11458step0 raw11458step0Labels = mixedMoment B raw11458step1 raw11458step1Labels := by
      have hz : ∀ j, raw11458step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11458step1 = (fun i j => raw11458step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11458step1 raw11458step0; decide +kernel
      have hl : raw11458step1Labels = raw11458step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11458step0 raw11458step0Labels permutation80 hz
    _ = mixedMoment B node3583 node3583Labels := by rfl

theorem canonical11459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11459 raw11459Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw11459 raw11459Labels = mixedMoment B raw11459step0 raw11459step0Labels := by
      have hz : ∀ j, raw11459 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11459step0 = (fun i j => raw11459 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11459step0 raw11459; decide +kernel
      have hl : raw11459step0Labels = raw11459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11459 raw11459Labels permutation434 hz
    mixedMoment B raw11459step0 raw11459step0Labels = mixedMoment B raw11459step1 raw11459step1Labels := by
      have hz : ∀ j, raw11459step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11459step1 = (fun i j => raw11459step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11459step1 raw11459step0; decide +kernel
      have hl : raw11459step1Labels = raw11459step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11459step0 raw11459step0Labels permutation80 hz
    _ = mixedMoment B node2265 node2265Labels := by rfl

theorem canonical11460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11460 raw11460Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw11460 raw11460Labels = mixedMoment B raw11460step0 raw11460step0Labels := by
      have hz : ∀ j, raw11460 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11460step0 = (fun i j => raw11460 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11460step0 raw11460; decide +kernel
      have hl : raw11460step0Labels = raw11460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11460 raw11460Labels permutation434 hz
    _ = mixedMoment B node2107 node2107Labels := by rfl

theorem canonical11461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11461 raw11461Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw11461 raw11461Labels = mixedMoment B raw11461step0 raw11461step0Labels := by
      have hz : ∀ j, raw11461 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11461step0 = (fun i j => raw11461 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11461step0 raw11461; decide +kernel
      have hl : raw11461step0Labels = raw11461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11461 raw11461Labels permutation346 hz
    _ = mixedMoment B node2107 node2107Labels := by rfl

theorem canonical11462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11462 raw11462Labels = mixedMoment B node2116 node2116Labels := by
  calc
    mixedMoment B raw11462 raw11462Labels = mixedMoment B raw11462step0 raw11462step0Labels := by
      have hz : ∀ j, raw11462 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11462step0 = (fun i j => raw11462 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11462step0 raw11462; decide +kernel
      have hl : raw11462step0Labels = raw11462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11462 raw11462Labels permutation434 hz
    mixedMoment B raw11462step0 raw11462step0Labels = mixedMoment B raw11462step1 raw11462step1Labels := by
      have hz : ∀ j, raw11462step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11462step1 = (fun i j => raw11462step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11462step1 raw11462step0; decide +kernel
      have hl : raw11462step1Labels = raw11462step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11462step0 raw11462step0Labels permutation80 hz
    _ = mixedMoment B node2116 node2116Labels := by rfl

theorem canonical11463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11463 raw11463Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw11463 raw11463Labels = mixedMoment B raw11463step0 raw11463step0Labels := by
      have hz : ∀ j, raw11463 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11463step0 = (fun i j => raw11463 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11463step0 raw11463; decide +kernel
      have hl : raw11463step0Labels = raw11463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11463 raw11463Labels permutation434 hz
    mixedMoment B raw11463step0 raw11463step0Labels = mixedMoment B raw11463step1 raw11463step1Labels := by
      have hz : ∀ j, raw11463step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11463step1 = (fun i j => raw11463step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11463step1 raw11463step0; decide +kernel
      have hl : raw11463step1Labels = raw11463step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11463step0 raw11463step0Labels permutation80 hz
    _ = mixedMoment B node2112 node2112Labels := by rfl

theorem canonical11464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11464 raw11464Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw11464 raw11464Labels = mixedMoment B raw11464step0 raw11464step0Labels := by
      have hz : ∀ j, raw11464 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11464step0 = (fun i j => raw11464 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11464step0 raw11464; decide +kernel
      have hl : raw11464step0Labels = raw11464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11464 raw11464Labels permutation434 hz
    mixedMoment B raw11464step0 raw11464step0Labels = mixedMoment B raw11464step1 raw11464step1Labels := by
      have hz : ∀ j, raw11464step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11464step1 = (fun i j => raw11464step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11464step1 raw11464step0; decide +kernel
      have hl : raw11464step1Labels = raw11464step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11464step0 raw11464step0Labels permutation80 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11531 raw11531Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw11531 raw11531Labels = mixedMoment B raw11531step0 raw11531step0Labels := by
      have hz : ∀ j, raw11531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11531step0 = (fun i j => raw11531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11531step0 raw11531; decide +kernel
      have hl : raw11531step0Labels = raw11531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11531 raw11531Labels permutation434 hz
    mixedMoment B raw11531step0 raw11531step0Labels = mixedMoment B raw11531step1 raw11531step1Labels := by
      have hz : ∀ j, raw11531step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11531step1 = (fun i j => raw11531step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11531step1 raw11531step0; decide +kernel
      have hl : raw11531step1Labels = raw11531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11531step0 raw11531step0Labels permutation80 hz
    mixedMoment B raw11531step1 raw11531step1Labels = mixedMoment B raw11531step2 raw11531step2Labels := by
      have hz : ∀ i, raw11531step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11531step2 = (fun i j => raw11531step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11531step2 raw11531step1; decide +kernel
      have hl : raw11531step2Labels = (fun j => raw11531step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11531step1 raw11531step1Labels permutation6 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical11532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11532 raw11532Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw11532 raw11532Labels = mixedMoment B raw11532step0 raw11532step0Labels := by
      have hz : ∀ j, raw11532 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11532step0 = (fun i j => raw11532 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11532step0 raw11532; decide +kernel
      have hl : raw11532step0Labels = raw11532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11532 raw11532Labels permutation434 hz
    mixedMoment B raw11532step0 raw11532step0Labels = mixedMoment B raw11532step1 raw11532step1Labels := by
      have hz : ∀ i, raw11532step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11532step1 = (fun i j => raw11532step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11532step1 raw11532step0; decide +kernel
      have hl : raw11532step1Labels = (fun j => raw11532step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11532step0 raw11532step0Labels permutation6 hz
    mixedMoment B raw11532step1 raw11532step1Labels = mixedMoment B raw11532step2 raw11532step2Labels := by
      have ha : raw11532step2 = (fun i j => raw11532step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw11532step2 raw11532step1; decide +kernel
      have hl : raw11532step2Labels = raw11532step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11532step1 raw11532step1Labels permutation38 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical11533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11533 raw11533Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw11533 raw11533Labels = mixedMoment B raw11533step0 raw11533step0Labels := by
      have hz : ∀ j, raw11533 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11533step0 = (fun i j => raw11533 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11533step0 raw11533; decide +kernel
      have hl : raw11533step0Labels = raw11533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11533 raw11533Labels permutation346 hz
    mixedMoment B raw11533step0 raw11533step0Labels = mixedMoment B raw11533step1 raw11533step1Labels := by
      have hz : ∀ i, raw11533step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11533step1 = (fun i j => raw11533step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11533step1 raw11533step0; decide +kernel
      have hl : raw11533step1Labels = (fun j => raw11533step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11533step0 raw11533step0Labels permutation6 hz
    mixedMoment B raw11533step1 raw11533step1Labels = mixedMoment B raw11533step2 raw11533step2Labels := by
      have ha : raw11533step2 = (fun i j => raw11533step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw11533step2 raw11533step1; decide +kernel
      have hl : raw11533step2Labels = raw11533step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11533step1 raw11533step1Labels permutation38 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical11534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11534 raw11534Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw11534 raw11534Labels = mixedMoment B raw11534step0 raw11534step0Labels := by
      have hz : ∀ j, raw11534 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11534step0 = (fun i j => raw11534 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11534step0 raw11534; decide +kernel
      have hl : raw11534step0Labels = raw11534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11534 raw11534Labels permutation434 hz
    mixedMoment B raw11534step0 raw11534step0Labels = mixedMoment B raw11534step1 raw11534step1Labels := by
      have hz : ∀ j, raw11534step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11534step1 = (fun i j => raw11534step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11534step1 raw11534step0; decide +kernel
      have hl : raw11534step1Labels = raw11534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11534step0 raw11534step0Labels permutation56 hz
    mixedMoment B raw11534step1 raw11534step1Labels = mixedMoment B raw11534step2 raw11534step2Labels := by
      have hz : ∀ i, raw11534step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11534step2 = (fun i j => raw11534step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11534step2 raw11534step1; decide +kernel
      have hl : raw11534step2Labels = (fun j => raw11534step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11534step1 raw11534step1Labels permutation6 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical11535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11535 raw11535Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw11535 raw11535Labels = mixedMoment B raw11535step0 raw11535step0Labels := by
      have hz : ∀ j, raw11535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11535step0 = (fun i j => raw11535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11535step0 raw11535; decide +kernel
      have hl : raw11535step0Labels = raw11535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11535 raw11535Labels permutation434 hz
    mixedMoment B raw11535step0 raw11535step0Labels = mixedMoment B raw11535step1 raw11535step1Labels := by
      have hz : ∀ i, raw11535step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11535step1 = (fun i j => raw11535step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11535step1 raw11535step0; decide +kernel
      have hl : raw11535step1Labels = (fun j => raw11535step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11535step0 raw11535step0Labels permutation6 hz
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical11536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11536 raw11536Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw11536 raw11536Labels = mixedMoment B raw11536step0 raw11536step0Labels := by
      have hz : ∀ j, raw11536 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11536step0 = (fun i j => raw11536 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11536step0 raw11536; decide +kernel
      have hl : raw11536step0Labels = raw11536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11536 raw11536Labels permutation265 hz
    mixedMoment B raw11536step0 raw11536step0Labels = mixedMoment B raw11536step1 raw11536step1Labels := by
      have hz : ∀ i, raw11536step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11536step1 = (fun i j => raw11536step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11536step1 raw11536step0; decide +kernel
      have hl : raw11536step1Labels = (fun j => raw11536step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11536step0 raw11536step0Labels permutation6 hz
    mixedMoment B raw11536step1 raw11536step1Labels = mixedMoment B raw11536step2 raw11536step2Labels := by
      have ha : raw11536step2 = (fun i j => raw11536step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw11536step2 raw11536step1; decide +kernel
      have hl : raw11536step2Labels = raw11536step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11536step1 raw11536step1Labels permutation38 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical11537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11537 raw11537Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw11537 raw11537Labels = mixedMoment B raw11537step0 raw11537step0Labels := by
      have hz : ∀ j, raw11537 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11537step0 = (fun i j => raw11537 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11537step0 raw11537; decide +kernel
      have hl : raw11537step0Labels = raw11537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11537 raw11537Labels permutation346 hz
    mixedMoment B raw11537step0 raw11537step0Labels = mixedMoment B raw11537step1 raw11537step1Labels := by
      have hz : ∀ j, raw11537step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11537step1 = (fun i j => raw11537step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11537step1 raw11537step0; decide +kernel
      have hl : raw11537step1Labels = raw11537step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11537step0 raw11537step0Labels permutation56 hz
    mixedMoment B raw11537step1 raw11537step1Labels = mixedMoment B raw11537step2 raw11537step2Labels := by
      have hz : ∀ i, raw11537step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11537step2 = (fun i j => raw11537step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11537step2 raw11537step1; decide +kernel
      have hl : raw11537step2Labels = (fun j => raw11537step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11537step1 raw11537step1Labels permutation6 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical11538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11538 raw11538Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw11538 raw11538Labels = mixedMoment B raw11538step0 raw11538step0Labels := by
      have hz : ∀ j, raw11538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11538step0 = (fun i j => raw11538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11538step0 raw11538; decide +kernel
      have hl : raw11538step0Labels = raw11538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11538 raw11538Labels permutation346 hz
    mixedMoment B raw11538step0 raw11538step0Labels = mixedMoment B raw11538step1 raw11538step1Labels := by
      have hz : ∀ i, raw11538step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11538step1 = (fun i j => raw11538step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11538step1 raw11538step0; decide +kernel
      have hl : raw11538step1Labels = (fun j => raw11538step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11538step0 raw11538step0Labels permutation6 hz
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical11539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11539 raw11539Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw11539 raw11539Labels = mixedMoment B raw11539step0 raw11539step0Labels := by
      have hz : ∀ j, raw11539 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11539step0 = (fun i j => raw11539 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11539step0 raw11539; decide +kernel
      have hl : raw11539step0Labels = raw11539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11539 raw11539Labels permutation265 hz
    mixedMoment B raw11539step0 raw11539step0Labels = mixedMoment B raw11539step1 raw11539step1Labels := by
      have hz : ∀ i, raw11539step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11539step1 = (fun i j => raw11539step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11539step1 raw11539step0; decide +kernel
      have hl : raw11539step1Labels = (fun j => raw11539step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11539step0 raw11539step0Labels permutation6 hz
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical11540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11540 raw11540Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw11540 raw11540Labels = mixedMoment B raw11540step0 raw11540step0Labels := by
      have hz : ∀ j, raw11540 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11540step0 = (fun i j => raw11540 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11540step0 raw11540; decide +kernel
      have hl : raw11540step0Labels = raw11540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11540 raw11540Labels permutation434 hz
    mixedMoment B raw11540step0 raw11540step0Labels = mixedMoment B raw11540step1 raw11540step1Labels := by
      have hz : ∀ j, raw11540step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11540step1 = (fun i j => raw11540step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11540step1 raw11540step0; decide +kernel
      have hl : raw11540step1Labels = raw11540step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11540step0 raw11540step0Labels permutation80 hz
    mixedMoment B raw11540step1 raw11540step1Labels = mixedMoment B raw11540step2 raw11540step2Labels := by
      have hz : ∀ j, raw11540step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw11540step2 = (fun i j => raw11540step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw11540step2 raw11540step1; decide +kernel
      have hl : raw11540step2Labels = raw11540step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11540step1 raw11540step1Labels permutation14 hz
    mixedMoment B raw11540step2 raw11540step2Labels = mixedMoment B raw11540step3 raw11540step3Labels := by
      have hz : ∀ i, raw11540step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11540step3 = (fun i j => raw11540step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11540step3 raw11540step2; decide +kernel
      have hl : raw11540step3Labels = (fun j => raw11540step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11540step2 raw11540step2Labels permutation6 hz
    _ = mixedMoment B node4071 node4071Labels := by rfl

theorem canonical11541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11541 raw11541Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw11541 raw11541Labels = mixedMoment B raw11541step0 raw11541step0Labels := by
      have hz : ∀ j, raw11541 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11541step0 = (fun i j => raw11541 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11541step0 raw11541; decide +kernel
      have hl : raw11541step0Labels = raw11541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11541 raw11541Labels permutation434 hz
    mixedMoment B raw11541step0 raw11541step0Labels = mixedMoment B raw11541step1 raw11541step1Labels := by
      have hz : ∀ j, raw11541step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11541step1 = (fun i j => raw11541step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11541step1 raw11541step0; decide +kernel
      have hl : raw11541step1Labels = raw11541step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11541step0 raw11541step0Labels permutation80 hz
    mixedMoment B raw11541step1 raw11541step1Labels = mixedMoment B raw11541step2 raw11541step2Labels := by
      have hz : ∀ i, raw11541step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11541step2 = (fun i j => raw11541step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11541step2 raw11541step1; decide +kernel
      have hl : raw11541step2Labels = (fun j => raw11541step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11541step1 raw11541step1Labels permutation6 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical11542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11542 raw11542Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw11542 raw11542Labels = mixedMoment B raw11542step0 raw11542step0Labels := by
      have hz : ∀ j, raw11542 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11542step0 = (fun i j => raw11542 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11542step0 raw11542; decide +kernel
      have hl : raw11542step0Labels = raw11542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11542 raw11542Labels permutation434 hz
    mixedMoment B raw11542step0 raw11542step0Labels = mixedMoment B raw11542step1 raw11542step1Labels := by
      have hz : ∀ j, raw11542step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11542step1 = (fun i j => raw11542step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11542step1 raw11542step0; decide +kernel
      have hl : raw11542step1Labels = raw11542step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11542step0 raw11542step0Labels permutation56 hz
    mixedMoment B raw11542step1 raw11542step1Labels = mixedMoment B raw11542step2 raw11542step2Labels := by
      have hz : ∀ i, raw11542step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11542step2 = (fun i j => raw11542step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11542step2 raw11542step1; decide +kernel
      have hl : raw11542step2Labels = (fun j => raw11542step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11542step1 raw11542step1Labels permutation6 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical11543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11543 raw11543Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw11543 raw11543Labels = mixedMoment B raw11543step0 raw11543step0Labels := by
      have hz : ∀ j, raw11543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11543step0 = (fun i j => raw11543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11543step0 raw11543; decide +kernel
      have hl : raw11543step0Labels = raw11543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11543 raw11543Labels permutation346 hz
    mixedMoment B raw11543step0 raw11543step0Labels = mixedMoment B raw11543step1 raw11543step1Labels := by
      have hz : ∀ j, raw11543step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11543step1 = (fun i j => raw11543step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11543step1 raw11543step0; decide +kernel
      have hl : raw11543step1Labels = raw11543step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11543step0 raw11543step0Labels permutation56 hz
    mixedMoment B raw11543step1 raw11543step1Labels = mixedMoment B raw11543step2 raw11543step2Labels := by
      have hz : ∀ i, raw11543step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw11543step2 = (fun i j => raw11543step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw11543step2 raw11543step1; decide +kernel
      have hl : raw11543step2Labels = (fun j => raw11543step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11543step1 raw11543step1Labels permutation6 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

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

theorem sum_fin_two {R : Type*} [AddCommMonoid R] (f : Fin 2 → R) :
    ∑ i, f i = f 0 + f 1 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

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

theorem groupedColumns_family2_0 {p : ℕ} (A : Matrix (Fin p) (Fin 2) ℤ) :
    groupedColumns A (EqualityPatterns.family2.label 0) =
      (fun i (_ : Fin 1) => A i 0 + A i 1) := by
  change groupedColumns A (fun _ : Fin 2 => (0 : Fin 1)) = _
  ext i b
  have hb : b = 0 := Subsingleton.elim _ _
  subst b
  simp [groupedColumns, Fin.sum_univ_succ]

theorem groupedColumns_family2_1 {p : ℕ} (A : Matrix (Fin p) (Fin 2) ℤ) :
    groupedColumns A (EqualityPatterns.family2.label 1) = A := by
  change groupedColumns A (fun j : Fin 2 => j) = _
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

/-- The two equality patterns for the sampled column indices. -/
theorem single_label_two {p : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin 2) ℤ) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      (1 / 6 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family2.label 0)) +
      (5 / 6 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family2.label 1)) := by
  have h := mixedMoment_single_label_partition B hB A
    EqualityPatterns.family2 EqualityPatterns.covers2
  rw [sum_fin_two] at h
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family2,
    EqualityPatterns.blocks2, Nat.descFactorial] at h
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

theorem canonical7978 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7978 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7978 = injectiveMoment H raw7978step0 := by
      have hz : ∀ j, raw7978 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7978step0 = (fun i j => raw7978 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7978 permutation2 hz
    injectiveMoment H raw7978step0 = injectiveMoment H raw7978step1 := by
      have hz : ∀ j, raw7978step0 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7978step1 = (fun i j => raw7978step0 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7978step0 permutation0 hz
    injectiveMoment H raw7978step1 = injectiveMoment H raw7978step2 := by
      have hz : ∀ i, raw7978step1 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7978step2 = (fun i j => raw7978step1 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7978step1 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

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

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Single5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5 node5Labels = Sparse.eval singlePairValue5 (familyPairVector B) := by
  have hp := single_label_two B hB node5
  have hl : node5Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node5 (EqualityPatterns.family2.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node5 (EqualityPatterns.family2.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family2_0]
      apply Matrix.ext
      unfold node5 PairSemantics.raw7979
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node5 (EqualityPatterns.family2.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node5 (EqualityPatterns.family2.label 1) = PairSemantics.raw5199 := by
      rw [groupedColumns_family2_1]
      apply Matrix.ext
      unfold node5 PairSemantics.raw5199
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  rw [hm0, hm1] at hp
  norm_num [singlePairValue5, PairSemantics.value0, PairSemantics.value11, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Single6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node6 node6Labels = Sparse.eval singlePairValue6 (familyPairVector B) := by
  have hp := single_label_two B hB node6
  have hl : node6Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node6 (EqualityPatterns.family2.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node6 (EqualityPatterns.family2.label 0) = PairSemantics.raw7978 := by
      rw [groupedColumns_family2_0]
      apply Matrix.ext; unfold node6 PairSemantics.raw7978; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7978 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node6 (EqualityPatterns.family2.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node6 (EqualityPatterns.family2.label 1) = PairSemantics.raw5210 := by
      rw [groupedColumns_family2_1]
      apply Matrix.ext; unfold node6 PairSemantics.raw5210; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5210 hH).trans (PairSemantics.sound4 hH)
  rw [hm0, hm1] at hp
  norm_num [singlePairValue6, PairSemantics.value0, PairSemantics.value4, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4093 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4093 node4093Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node5 node5Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw660 singletonSmall4093
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4093) = raw660Labels := by decide +kernel
  rw [hl, canonical660 B hB] at h
  have hc0 : mixedMoment B raw660 (Fin.cases (0 : Fin 1) singletonSmall4093) =
      mixedMoment B node5 node5Labels := by
    have ha : raw660 = raw661 := by apply Matrix.ext; unfold raw660 raw661; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4093 = raw661Labels := by decide +kernel
    rw [ha, hj, canonical661 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton4094 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4094 node4094Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node6 node6Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw662 singletonSmall4094
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4094) = raw662Labels := by decide +kernel
  rw [hl, canonical662 B hB] at h
  have hc0 : mixedMoment B raw662 (Fin.cases (0 : Fin 1) singletonSmall4094) =
      mixedMoment B node6 node6Labels := by
    have ha : raw662 = raw663 := by apply Matrix.ext; unfold raw662 raw663; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall4094 = raw663Labels := by decide +kernel
    rw [ha, hj, canonical663 B hB]
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

theorem sound5 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5 node5Labels = Sparse.eval nodeValue5 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue5 (familyPairVector B) := singlePair5 B _hB
    _ = _ := by norm_num [singlePairValue5, nodeValue5, Sparse.eval, mixedVector]

theorem sound6 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node6 node6Labels = Sparse.eval nodeValue6 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue6 (familyPairVector B) := singlePair6 B _hB
    _ = _ := by norm_num [singlePairValue6, nodeValue6, Sparse.eval, mixedVector]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1020 node1020Labels = 0 := by
  exact mixedMoment_alpha B hF node1020 node1020Labels 1 permutation152
    (by decide +kernel)

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

theorem sound1020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1020 node1020Labels = Sparse.eval nodeValue1020 (mixedVector B) := by
  simpa only [nodeValue1020, Sparse.eval_nil] using zero1020 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1038 node1038Labels = 0 := by
  exact mixedMoment_alpha B hF node1038 node1038Labels 1 permutation161
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1038 node1038Labels = Sparse.eval nodeValue1038 (mixedVector B) := by
  simpa only [nodeValue1038, Sparse.eval_nil] using zero1038 B _hB _hF

theorem sound1040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1040 node1040Labels = Sparse.eval nodeValue1040 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1040) = mixedMoment B node1040 node1040Labels := rfl
  simpa [nodeValue1040, Sparse.eval] using hc.symm

theorem sound1042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1042 node1042Labels = Sparse.eval nodeValue1042 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1042) = mixedMoment B node1042 node1042Labels := rfl
  simpa [nodeValue1042, Sparse.eval] using hc.symm

theorem sound1079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1079 node1079Labels = Sparse.eval nodeValue1079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1079) = mixedMoment B node1079 node1079Labels := rfl
  simpa [nodeValue1079, Sparse.eval] using hc.symm

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

theorem sound2088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2088 node2088Labels = Sparse.eval nodeValue2088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2088) = mixedMoment B node2088 node2088Labels := rfl
  simpa [nodeValue2088, Sparse.eval] using hc.symm

theorem sound2090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2090 node2090Labels = Sparse.eval nodeValue2090 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2090) = mixedMoment B node2090 node2090Labels := rfl
  simpa [nodeValue2090, Sparse.eval] using hc.symm

theorem sound2094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2094 node2094Labels = Sparse.eval nodeValue2094 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2094) = mixedMoment B node2094 node2094Labels := rfl
  simpa [nodeValue2094, Sparse.eval] using hc.symm

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

theorem sound2112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2112 node2112Labels = Sparse.eval nodeValue2112 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2112) = mixedMoment B node2112 node2112Labels := rfl
  simpa [nodeValue2112, Sparse.eval] using hc.symm

theorem sound2116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2116 node2116Labels = Sparse.eval nodeValue2116 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2116) = mixedMoment B node2116 node2116Labels := rfl
  simpa [nodeValue2116, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2265 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2265 node2265Labels = 0 := by
  exact mixedMoment_order_one B hB node2265 node2265Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2243 node2243Labels = Sparse.eval nodeValue2243 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2243) = mixedMoment B node2243 node2243Labels := rfl
  simpa [nodeValue2243, Sparse.eval] using hc.symm

theorem sound2244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2244 node2244Labels = Sparse.eval nodeValue2244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2244) = mixedMoment B node2244 node2244Labels := rfl
  simpa [nodeValue2244, Sparse.eval] using hc.symm

theorem sound2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2262 node2262Labels = Sparse.eval nodeValue2262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2262) = mixedMoment B node2262 node2262Labels := rfl
  simpa [nodeValue2262, Sparse.eval] using hc.symm

theorem sound2265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2265 node2265Labels = Sparse.eval nodeValue2265 (mixedVector B) := by
  simpa only [nodeValue2265, Sparse.eval_nil] using zero2265 B _hB _hF

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

theorem sound3572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3572 node3572Labels = Sparse.eval nodeValue3572 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3572) = mixedMoment B node3572 node3572Labels := rfl
  simpa [nodeValue3572, Sparse.eval] using hc.symm

theorem sound3583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3583 node3583Labels = Sparse.eval nodeValue3583 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3583) = mixedMoment B node3583 node3583Labels := rfl
  simpa [nodeValue3583, Sparse.eval] using hc.symm

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

theorem sound4069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4069 node4069Labels = Sparse.eval nodeValue4069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4069) = mixedMoment B node4069 node4069Labels := rfl
  simpa [nodeValue4069, Sparse.eval] using hc.symm

theorem sound4070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4070 node4070Labels = Sparse.eval nodeValue4070 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4070) = mixedMoment B node4070 node4070Labels := rfl
  simpa [nodeValue4070, Sparse.eval] using hc.symm

theorem sound4071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4071 node4071Labels = Sparse.eval nodeValue4071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4071) = mixedMoment B node4071 node4071Labels := rfl
  simpa [nodeValue4071, Sparse.eval] using hc.symm

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

theorem sound4081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4081 node4081Labels = Sparse.eval nodeValue4081 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4081) = mixedMoment B node4081 node4081Labels := rfl
  simpa [nodeValue4081, Sparse.eval] using hc.symm

theorem sound4082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4082 node4082Labels = Sparse.eval nodeValue4082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4082) = mixedMoment B node4082 node4082Labels := rfl
  simpa [nodeValue4082, Sparse.eval] using hc.symm

theorem sound4083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4083 node4083Labels = Sparse.eval nodeValue4083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4083) = mixedMoment B node4083 node4083Labels := rfl
  simpa [nodeValue4083, Sparse.eval] using hc.symm

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

theorem sound4085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4085 node4085Labels = Sparse.eval nodeValue4085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4085) = mixedMoment B node4085 node4085Labels := rfl
  simpa [nodeValue4085, Sparse.eval] using hc.symm

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

theorem sound4093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4093 node4093Labels = Sparse.eval nodeValue4093 (mixedVector B) := by
  have h := singleton4093 B _hB
  rw [sound5 B _hB _hF] at h
  norm_num [nodeValue4093, nodeValue5, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4094 node4094Labels = Sparse.eval nodeValue4094 (mixedVector B) := by
  have h := singleton4094 B _hB
  rw [sound6 B _hB _hF] at h
  norm_num [nodeValue4094, nodeValue6, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources20
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq667 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm667 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA667 + difference 0 1) (sourceB667 + difference 1 0) sourceC667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA667 + difference 0 1) (sourceB667 + difference 1 0) sourceC667) = raw11293 := by
      apply Matrix.ext; unfold tripleCharges sourceA667 sourceB667 sourceC667 difference raw11293; decide +kernel
    rw [ha]
    exact (canonical11293 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA667 + difference 1 1) (sourceB667 + difference 1 1) sourceC667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA667 + difference 1 1) (sourceB667 + difference 1 1) sourceC667) = raw11292 := by
      apply Matrix.ext; unfold tripleCharges sourceA667 sourceB667 sourceC667 difference raw11292; decide +kernel
    rw [ha]
    exact (canonical11292 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA667 + difference 2 1) (sourceB667 + difference 1 2) sourceC667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA667 + difference 2 1) (sourceB667 + difference 1 2) sourceC667) = raw11308 := by
      apply Matrix.ext; unfold tripleCharges sourceA667 sourceB667 sourceC667 difference raw11308; decide +kernel
    rw [ha]
    exact (canonical11308 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA667 + difference 3 1) (sourceB667 + difference 1 3) sourceC667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2088) := by
    have ha : (tripleCharges (sourceA667 + difference 3 1) (sourceB667 + difference 1 3) sourceC667) = raw11309 := by
      apply Matrix.ext; unfold tripleCharges sourceA667 sourceB667 sourceC667 difference raw11309; decide +kernel
    rw [ha]
    exact (canonical11309 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA667 + difference 4 1) (sourceB667 + difference 1 4) sourceC667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2094) := by
    have ha : (tripleCharges (sourceA667 + difference 4 1) (sourceB667 + difference 1 4) sourceC667) = raw11310 := by
      apply Matrix.ext; unfold tripleCharges sourceA667 sourceB667 sourceC667 difference raw11310; decide +kernel
    rw [ha]
    exact (canonical11310 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA667 + difference 5 1) (sourceB667 + difference 1 5) sourceC667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2090) := by
    have ha : (tripleCharges (sourceA667 + difference 5 1) (sourceB667 + difference 1 5) sourceC667) = raw11311 := by
      apply Matrix.ext; unfold tripleCharges sourceA667 sourceB667 sourceC667 difference raw11311; decide +kernel
    rw [ha]
    exact (canonical11311 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA667 + sourceB667) sourceC667) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA667 + sourceB667) sourceC667) = raw11298 := by
      apply Matrix.ext; unfold doubleCharges sourceA667 sourceB667 sourceC667 raw11298; decide +kernel
    rw [ha]
    exact (canonical11298 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA667 sourceB667 sourceC667
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm667, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq668 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm668 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA668 + difference 3 0) (sourceB668 + difference 0 3) sourceC668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1020) := by
    have ha : (tripleCharges (sourceA668 + difference 3 0) (sourceB668 + difference 0 3) sourceC668) = raw11301 := by
      apply Matrix.ext; unfold tripleCharges sourceA668 sourceB668 sourceC668 difference raw11301; decide +kernel
    rw [ha]
    exact (canonical11301 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA668 + difference 3 1) (sourceB668 + difference 1 3) sourceC668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2088) := by
    have ha : (tripleCharges (sourceA668 + difference 3 1) (sourceB668 + difference 1 3) sourceC668) = raw11309 := by
      apply Matrix.ext; unfold tripleCharges sourceA668 sourceB668 sourceC668 difference raw11309; decide +kernel
    rw [ha]
    exact (canonical11309 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA668 + difference 3 2) (sourceB668 + difference 2 3) sourceC668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2088) := by
    have ha : (tripleCharges (sourceA668 + difference 3 2) (sourceB668 + difference 2 3) sourceC668) = raw11312 := by
      apply Matrix.ext; unfold tripleCharges sourceA668 sourceB668 sourceC668 difference raw11312; decide +kernel
    rw [ha]
    exact (canonical11312 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA668 + difference 3 3) (sourceB668 + difference 3 3) sourceC668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA668 + difference 3 3) (sourceB668 + difference 3 3) sourceC668) = raw11292 := by
      apply Matrix.ext; unfold tripleCharges sourceA668 sourceB668 sourceC668 difference raw11292; decide +kernel
    rw [ha]
    exact (canonical11292 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA668 + difference 3 4) (sourceB668 + difference 4 3) sourceC668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA668 + difference 3 4) (sourceB668 + difference 4 3) sourceC668) = raw11313 := by
      apply Matrix.ext; unfold tripleCharges sourceA668 sourceB668 sourceC668 difference raw11313; decide +kernel
    rw [ha]
    exact (canonical11313 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA668 + difference 3 5) (sourceB668 + difference 5 3) sourceC668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA668 + difference 3 5) (sourceB668 + difference 5 3) sourceC668) = raw11314 := by
      apply Matrix.ext; unfold tripleCharges sourceA668 sourceB668 sourceC668 difference raw11314; decide +kernel
    rw [ha]
    exact (canonical11314 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA668 + sourceB668) sourceC668) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA668 + sourceB668) sourceC668) = raw11298 := by
      apply Matrix.ext; unfold doubleCharges sourceA668 sourceB668 sourceC668 raw11298; decide +kernel
    rw [ha]
    exact (canonical11298 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA668 sourceB668 sourceC668
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm668, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources21
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq674 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm674 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA674 + difference 0 0) (sourceB674 + difference 0 0) sourceC674) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA674 + difference 0 0) (sourceB674 + difference 0 0) sourceC674) = raw5770 := by
      apply Matrix.ext; unfold tripleCharges sourceA674 sourceB674 sourceC674 difference raw5770; decide +kernel
    rw [ha]
    exact (canonical5770 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA674 + difference 1 0) (sourceB674 + difference 0 1) sourceC674) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA674 + difference 1 0) (sourceB674 + difference 0 1) sourceC674) = raw11016 := by
      apply Matrix.ext; unfold tripleCharges sourceA674 sourceB674 sourceC674 difference raw11016; decide +kernel
    rw [ha]
    exact (canonical11016 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA674 + difference 2 0) (sourceB674 + difference 0 2) sourceC674) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA674 + difference 2 0) (sourceB674 + difference 0 2) sourceC674) = raw11396 := by
      apply Matrix.ext; unfold tripleCharges sourceA674 sourceB674 sourceC674 difference raw11396; decide +kernel
    rw [ha]
    exact (canonical11396 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA674 + difference 3 0) (sourceB674 + difference 0 3) sourceC674) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1038) := by
    have ha : (tripleCharges (sourceA674 + difference 3 0) (sourceB674 + difference 0 3) sourceC674) = raw5759 := by
      apply Matrix.ext; unfold tripleCharges sourceA674 sourceB674 sourceC674 difference raw5759; decide +kernel
    rw [ha]
    exact (canonical5759 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA674 + difference 4 0) (sourceB674 + difference 0 4) sourceC674) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA674 + difference 4 0) (sourceB674 + difference 0 4) sourceC674) = raw11201 := by
      apply Matrix.ext; unfold tripleCharges sourceA674 sourceB674 sourceC674 difference raw11201; decide +kernel
    rw [ha]
    exact (canonical11201 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA674 + difference 5 0) (sourceB674 + difference 0 5) sourceC674) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA674 + difference 5 0) (sourceB674 + difference 0 5) sourceC674) = raw11397 := by
      apply Matrix.ext; unfold tripleCharges sourceA674 sourceB674 sourceC674 difference raw11397; decide +kernel
    rw [ha]
    exact (canonical11397 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA674 + sourceB674) sourceC674) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA674 + sourceB674) sourceC674) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA674 sourceB674 sourceC674 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA674 sourceB674 sourceC674
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm674, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq677 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm677 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA677 + difference 0 1) (sourceB677 + difference 1 0) sourceC677) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA677 + difference 0 1) (sourceB677 + difference 1 0) sourceC677) = raw11458 := by
      apply Matrix.ext; unfold tripleCharges sourceA677 sourceB677 sourceC677 difference raw11458; decide +kernel
    rw [ha]
    exact (canonical11458 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA677 + difference 1 1) (sourceB677 + difference 1 1) sourceC677) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA677 + difference 1 1) (sourceB677 + difference 1 1) sourceC677) = raw11459 := by
      apply Matrix.ext; unfold tripleCharges sourceA677 sourceB677 sourceC677 difference raw11459; decide +kernel
    rw [ha]
    exact (canonical11459 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA677 + difference 2 1) (sourceB677 + difference 1 2) sourceC677) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA677 + difference 2 1) (sourceB677 + difference 1 2) sourceC677) = raw11460 := by
      apply Matrix.ext; unfold tripleCharges sourceA677 sourceB677 sourceC677 difference raw11460; decide +kernel
    rw [ha]
    exact (canonical11460 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA677 + difference 3 1) (sourceB677 + difference 1 3) sourceC677) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA677 + difference 3 1) (sourceB677 + difference 1 3) sourceC677) = raw11461 := by
      apply Matrix.ext; unfold tripleCharges sourceA677 sourceB677 sourceC677 difference raw11461; decide +kernel
    rw [ha]
    exact (canonical11461 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA677 + difference 4 1) (sourceB677 + difference 1 4) sourceC677) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2116) := by
    have ha : (tripleCharges (sourceA677 + difference 4 1) (sourceB677 + difference 1 4) sourceC677) = raw11462 := by
      apply Matrix.ext; unfold tripleCharges sourceA677 sourceB677 sourceC677 difference raw11462; decide +kernel
    rw [ha]
    exact (canonical11462 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA677 + difference 5 1) (sourceB677 + difference 1 5) sourceC677) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA677 + difference 5 1) (sourceB677 + difference 1 5) sourceC677) = raw11463 := by
      apply Matrix.ext; unfold tripleCharges sourceA677 sourceB677 sourceC677 difference raw11463; decide +kernel
    rw [ha]
    exact (canonical11463 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA677 + sourceB677) sourceC677) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA677 + sourceB677) sourceC677) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA677 sourceB677 sourceC677 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA677 sourceB677 sourceC677
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm677, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq681 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm681 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA681 + difference 0 1) (sourceB681 + difference 1 0) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA681 + difference 0 1) (sourceB681 + difference 1 0) sourceC681) = raw2930 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw2930; decide +kernel
    rw [ha]
    exact (canonical2930 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA681 + difference 0 2) (sourceB681 + difference 2 0) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA681 + difference 0 2) (sourceB681 + difference 2 0) sourceC681) = raw2931 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw2931; decide +kernel
    rw [ha]
    exact (canonical2931 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA681 + difference 0 3) (sourceB681 + difference 3 0) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA681 + difference 0 3) (sourceB681 + difference 3 0) sourceC681) = raw2932 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw2932; decide +kernel
    rw [ha]
    exact (canonical2932 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA681 + difference 0 4) (sourceB681 + difference 4 0) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4094) := by
    have ha : (tripleCharges (sourceA681 + difference 0 4) (sourceB681 + difference 4 0) sourceC681) = raw3340 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw3340; decide +kernel
    rw [ha]
    exact (canonical3340 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA681 + difference 0 5) (sourceB681 + difference 5 0) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA681 + difference 0 5) (sourceB681 + difference 5 0) sourceC681) = raw2933 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw2933; decide +kernel
    rw [ha]
    exact (canonical2933 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA681 + difference 1 0) (sourceB681 + difference 0 1) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA681 + difference 1 0) (sourceB681 + difference 0 1) sourceC681) = raw11531 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11531; decide +kernel
    rw [ha]
    exact (canonical11531 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA681 + difference 1 2) (sourceB681 + difference 2 1) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA681 + difference 1 2) (sourceB681 + difference 2 1) sourceC681) = raw11532 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11532; decide +kernel
    rw [ha]
    exact (canonical11532 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA681 + difference 1 3) (sourceB681 + difference 3 1) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA681 + difference 1 3) (sourceB681 + difference 3 1) sourceC681) = raw11533 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11533; decide +kernel
    rw [ha]
    exact (canonical11533 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA681 + difference 1 4) (sourceB681 + difference 4 1) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA681 + difference 1 4) (sourceB681 + difference 4 1) sourceC681) = raw2914 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw2914; decide +kernel
    rw [ha]
    exact (canonical2914 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA681 + difference 1 5) (sourceB681 + difference 5 1) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA681 + difference 1 5) (sourceB681 + difference 5 1) sourceC681) = raw3323 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw3323; decide +kernel
    rw [ha]
    exact (canonical3323 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA681 + difference 2 0) (sourceB681 + difference 0 2) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA681 + difference 2 0) (sourceB681 + difference 0 2) sourceC681) = raw11534 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11534; decide +kernel
    rw [ha]
    exact (canonical11534 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA681 + difference 2 1) (sourceB681 + difference 1 2) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA681 + difference 2 1) (sourceB681 + difference 1 2) sourceC681) = raw11535 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11535; decide +kernel
    rw [ha]
    exact (canonical11535 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA681 + difference 2 3) (sourceB681 + difference 3 2) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA681 + difference 2 3) (sourceB681 + difference 3 2) sourceC681) = raw11536 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11536; decide +kernel
    rw [ha]
    exact (canonical11536 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA681 + difference 2 4) (sourceB681 + difference 4 2) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA681 + difference 2 4) (sourceB681 + difference 4 2) sourceC681) = raw2919 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw2919; decide +kernel
    rw [ha]
    exact (canonical2919 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA681 + difference 2 5) (sourceB681 + difference 5 2) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA681 + difference 2 5) (sourceB681 + difference 5 2) sourceC681) = raw3327 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw3327; decide +kernel
    rw [ha]
    exact (canonical3327 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA681 + difference 3 0) (sourceB681 + difference 0 3) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA681 + difference 3 0) (sourceB681 + difference 0 3) sourceC681) = raw11537 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11537; decide +kernel
    rw [ha]
    exact (canonical11537 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA681 + difference 3 1) (sourceB681 + difference 1 3) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA681 + difference 3 1) (sourceB681 + difference 1 3) sourceC681) = raw11538 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11538; decide +kernel
    rw [ha]
    exact (canonical11538 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA681 + difference 3 2) (sourceB681 + difference 2 3) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA681 + difference 3 2) (sourceB681 + difference 2 3) sourceC681) = raw11539 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11539; decide +kernel
    rw [ha]
    exact (canonical11539 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA681 + difference 3 4) (sourceB681 + difference 4 3) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA681 + difference 3 4) (sourceB681 + difference 4 3) sourceC681) = raw2924 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw2924; decide +kernel
    rw [ha]
    exact (canonical2924 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA681 + difference 3 5) (sourceB681 + difference 5 3) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA681 + difference 3 5) (sourceB681 + difference 5 3) sourceC681) = raw3331 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw3331; decide +kernel
    rw [ha]
    exact (canonical3331 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA681 + difference 4 0) (sourceB681 + difference 0 4) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (tripleCharges (sourceA681 + difference 4 0) (sourceB681 + difference 0 4) sourceC681) = raw11540 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11540; decide +kernel
    rw [ha]
    exact (canonical11540 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA681 + difference 4 1) (sourceB681 + difference 1 4) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA681 + difference 4 1) (sourceB681 + difference 1 4) sourceC681) = raw11541 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11541; decide +kernel
    rw [ha]
    exact (canonical11541 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA681 + difference 4 2) (sourceB681 + difference 2 4) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA681 + difference 4 2) (sourceB681 + difference 2 4) sourceC681) = raw11542 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11542; decide +kernel
    rw [ha]
    exact (canonical11542 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA681 + difference 4 3) (sourceB681 + difference 3 4) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA681 + difference 4 3) (sourceB681 + difference 3 4) sourceC681) = raw11543 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw11543; decide +kernel
    rw [ha]
    exact (canonical11543 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA681 + difference 4 5) (sourceB681 + difference 5 4) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA681 + difference 4 5) (sourceB681 + difference 5 4) sourceC681) = raw3335 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw3335; decide +kernel
    rw [ha]
    exact (canonical3335 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA681 + difference 5 0) (sourceB681 + difference 0 5) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA681 + difference 5 0) (sourceB681 + difference 0 5) sourceC681) = raw5209 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw5209; decide +kernel
    rw [ha]
    exact (canonical5209 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA681 + difference 5 1) (sourceB681 + difference 1 5) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA681 + difference 5 1) (sourceB681 + difference 1 5) sourceC681) = raw5210 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw5210; decide +kernel
    rw [ha]
    exact (canonical5210 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA681 + difference 5 2) (sourceB681 + difference 2 5) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA681 + difference 5 2) (sourceB681 + difference 2 5) sourceC681) = raw5211 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw5211; decide +kernel
    rw [ha]
    exact (canonical5211 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA681 + difference 5 3) (sourceB681 + difference 3 5) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA681 + difference 5 3) (sourceB681 + difference 3 5) sourceC681) = raw5212 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw5212; decide +kernel
    rw [ha]
    exact (canonical5212 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA681 + difference 5 4) (sourceB681 + difference 4 5) sourceC681) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA681 + difference 5 4) (sourceB681 + difference 4 5) sourceC681) = raw2934 := by
      apply Matrix.ext; unfold tripleCharges sourceA681 sourceB681 sourceC681 difference raw2934; decide +kernel
    rw [ha]
    exact (canonical2934 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA681 sourceB681 sourceC681
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm681, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck576 : Integer.Sparse.reindex keyMap MixedData.row576 = numericRow576 := by decide +kernel

theorem numericCheck576 (x : Master → ℝ) : Integer.Sparse.eval numericRow576 x =
    (1 : ℝ) * reducedSource576 x := by
  norm_num [numericRow576, reducedSource576, Integer.Sparse.eval, Sparse.eval, nodeValue2088, nodeValue2090, nodeValue2094, nodeValue2107, nodeValue2244, nodeValue3572, nodeValue4083]

theorem reindexCheck577 : Integer.Sparse.reindex keyMap MixedData.row577 = numericRow577 := by decide +kernel

theorem numericCheck577 (x : Master → ℝ) : Integer.Sparse.eval numericRow577 x =
    (1 : ℝ) * reducedSource577 x := by
  norm_num [numericRow577, reducedSource577, Integer.Sparse.eval, Sparse.eval, nodeValue1020, nodeValue2088, nodeValue2243, nodeValue2244, nodeValue4083]

theorem reindexCheck583 : Integer.Sparse.reindex keyMap MixedData.row583 = numericRow583 := by decide +kernel

theorem numericCheck583 (x : Master → ℝ) : Integer.Sparse.eval numericRow583 x =
    (1 : ℝ) * reducedSource583 x := by
  norm_num [numericRow583, reducedSource583, Integer.Sparse.eval, Sparse.eval, nodeValue1038, nodeValue1040, nodeValue1042, nodeValue1079, nodeValue2262, nodeValue4084]

theorem reindexCheck586 : Integer.Sparse.reindex keyMap MixedData.row586 = numericRow586 := by decide +kernel

theorem numericCheck586 (x : Master → ℝ) : Integer.Sparse.eval numericRow586 x =
    (1 : ℝ) * reducedSource586 x := by
  norm_num [numericRow586, reducedSource586, Integer.Sparse.eval, Sparse.eval, nodeValue2107, nodeValue2112, nodeValue2116, nodeValue2265, nodeValue3583, nodeValue4083]

theorem reindexCheck590 : Integer.Sparse.reindex keyMap MixedData.row590 = numericRow590 := by decide +kernel

theorem numericCheck590 (x : Master → ℝ) : Integer.Sparse.eval numericRow590 x =
    (40 : ℝ) * reducedSource590 x := by
  norm_num [numericRow590, reducedSource590, Integer.Sparse.eval, Sparse.eval, nodeValue4069, nodeValue4070, nodeValue4071, nodeValue4080, nodeValue4081, nodeValue4082, nodeValue4083, nodeValue4084, nodeValue4085, nodeValue4092, nodeValue4093, nodeValue4094] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero576 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource576 (mixedVector B) = 0 := by
  have h2088 : mixedVector B (Sum.inr 2088) = Sparse.eval nodeValue2088 (mixedVector B) := by
    change mixedMoment B node2088 node2088Labels = _
    exact sound2088 B hB hF
  have h2090 : mixedVector B (Sum.inr 2090) = Sparse.eval nodeValue2090 (mixedVector B) := by
    change mixedMoment B node2090 node2090Labels = _
    exact sound2090 B hB hF
  have h2094 : mixedVector B (Sum.inr 2094) = Sparse.eval nodeValue2094 (mixedVector B) := by
    change mixedMoment B node2094 node2094Labels = _
    exact sound2094 B hB hF
  have h2107 : mixedVector B (Sum.inr 2107) = Sparse.eval nodeValue2107 (mixedVector B) := by
    change mixedMoment B node2107 node2107Labels = _
    exact sound2107 B hB hF
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm667, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2088, h2090, h2094, h2107, h2244, h3572, h4083, reducedSource576] using sourceEq667 B hB

theorem rowSound576 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row576 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck576, numericCheck576, reducedZero576 B hB hF, mul_zero]

theorem reducedZero577 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource577 (mixedVector B) = 0 := by
  have h1020 : mixedVector B (Sum.inr 1020) = Sparse.eval nodeValue1020 (mixedVector B) := by
    change mixedMoment B node1020 node1020Labels = _
    exact sound1020 B hB hF
  have h2088 : mixedVector B (Sum.inr 2088) = Sparse.eval nodeValue2088 (mixedVector B) := by
    change mixedMoment B node2088 node2088Labels = _
    exact sound2088 B hB hF
  have h2243 : mixedVector B (Sum.inr 2243) = Sparse.eval nodeValue2243 (mixedVector B) := by
    change mixedMoment B node2243 node2243Labels = _
    exact sound2243 B hB hF
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm668, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1020, h2088, h2243, h2244, h4083, reducedSource577] using sourceEq668 B hB

theorem rowSound577 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row577 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck577, numericCheck577, reducedZero577 B hB hF, mul_zero]

theorem reducedZero583 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource583 (mixedVector B) = 0 := by
  have h1038 : mixedVector B (Sum.inr 1038) = Sparse.eval nodeValue1038 (mixedVector B) := by
    change mixedMoment B node1038 node1038Labels = _
    exact sound1038 B hB hF
  have h1040 : mixedVector B (Sum.inr 1040) = Sparse.eval nodeValue1040 (mixedVector B) := by
    change mixedMoment B node1040 node1040Labels = _
    exact sound1040 B hB hF
  have h1042 : mixedVector B (Sum.inr 1042) = Sparse.eval nodeValue1042 (mixedVector B) := by
    change mixedMoment B node1042 node1042Labels = _
    exact sound1042 B hB hF
  have h1079 : mixedVector B (Sum.inr 1079) = Sparse.eval nodeValue1079 (mixedVector B) := by
    change mixedMoment B node1079 node1079Labels = _
    exact sound1079 B hB hF
  have h2262 : mixedVector B (Sum.inr 2262) = Sparse.eval nodeValue2262 (mixedVector B) := by
    change mixedMoment B node2262 node2262Labels = _
    exact sound2262 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm674, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1038, h1040, h1042, h1079, h2262, h4084, reducedSource583] using sourceEq674 B hB

theorem rowSound583 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row583 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck583, numericCheck583, reducedZero583 B hB hF, mul_zero]

theorem reducedZero586 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource586 (mixedVector B) = 0 := by
  have h2107 : mixedVector B (Sum.inr 2107) = Sparse.eval nodeValue2107 (mixedVector B) := by
    change mixedMoment B node2107 node2107Labels = _
    exact sound2107 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h2116 : mixedVector B (Sum.inr 2116) = Sparse.eval nodeValue2116 (mixedVector B) := by
    change mixedMoment B node2116 node2116Labels = _
    exact sound2116 B hB hF
  have h2265 : mixedVector B (Sum.inr 2265) = Sparse.eval nodeValue2265 (mixedVector B) := by
    change mixedMoment B node2265 node2265Labels = _
    exact sound2265 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm677, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2107, h2112, h2116, h2265, h3583, h4083, reducedSource586] using sourceEq677 B hB

theorem rowSound586 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row586 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck586, numericCheck586, reducedZero586 B hB hF, mul_zero]

theorem reducedZero590 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource590 (mixedVector B) = 0 := by
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  have h4093 : mixedVector B (Sum.inr 4093) = Sparse.eval nodeValue4093 (mixedVector B) := by
    change mixedMoment B node4093 node4093Labels = _
    exact sound4093 B hB hF
  have h4094 : mixedVector B (Sum.inr 4094) = Sparse.eval nodeValue4094 (mixedVector B) := by
    change mixedMoment B node4094 node4094Labels = _
    exact sound4094 B hB hF
  simpa only [sourceForm681, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4069, h4070, h4071, h4080, h4081, h4082, h4083, h4084, h4085, h4092, h4093, h4094, reducedSource590] using sourceEq681 B hB

theorem rowSound590 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row590 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck590, numericCheck590, reducedZero590 B hB hF, mul_zero]

theorem sourceRowsAt576 : MixedData.sourceRows (576 : Fin 2425) =
    MixedData.row576 := by decide +kernel

theorem sourceRowsAt577 : MixedData.sourceRows (577 : Fin 2425) =
    MixedData.row577 := by decide +kernel

theorem sourceRowsAt578 : MixedData.sourceRows (578 : Fin 2425) =
    MixedData.row578 := by decide +kernel

theorem sourceRowsAt579 : MixedData.sourceRows (579 : Fin 2425) =
    MixedData.row579 := by decide +kernel

theorem sourceRowsAt580 : MixedData.sourceRows (580 : Fin 2425) =
    MixedData.row580 := by decide +kernel

theorem sourceRowsAt581 : MixedData.sourceRows (581 : Fin 2425) =
    MixedData.row581 := by decide +kernel

theorem sourceRowsAt582 : MixedData.sourceRows (582 : Fin 2425) =
    MixedData.row582 := by decide +kernel

theorem sourceRowsAt583 : MixedData.sourceRows (583 : Fin 2425) =
    MixedData.row583 := by decide +kernel

theorem sourceRowsAt584 : MixedData.sourceRows (584 : Fin 2425) =
    MixedData.row584 := by decide +kernel

theorem sourceRowsAt585 : MixedData.sourceRows (585 : Fin 2425) =
    MixedData.row585 := by decide +kernel

theorem sourceRowsAt586 : MixedData.sourceRows (586 : Fin 2425) =
    MixedData.row586 := by decide +kernel

theorem sourceRowsAt587 : MixedData.sourceRows (587 : Fin 2425) =
    MixedData.row587 := by decide +kernel

theorem sourceRowsAt588 : MixedData.sourceRows (588 : Fin 2425) =
    MixedData.row588 := by decide +kernel

theorem sourceRowsAt589 : MixedData.sourceRows (589 : Fin 2425) =
    MixedData.row589 := by decide +kernel

theorem sourceRowsAt590 : MixedData.sourceRows (590 : Fin 2425) =
    MixedData.row590 := by decide +kernel

theorem sourceRowsAt591 : MixedData.sourceRows (591 : Fin 2425) =
    MixedData.row591 := by decide +kernel

theorem chunkSound36_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 36) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 576 ∨ k.val = 577 ∨ k.val = 578 ∨ k.val = 579 ∨ k.val = 580 ∨ k.val = 581 ∨ k.val = 582 ∨ k.val = 583 ∨ k.val = 584 ∨ k.val = 585 ∨ k.val = 586 ∨ k.val = 587 ∨ k.val = 588 ∨ k.val = 589 ∨ k.val = 590 ∨ k.val = 591 := by omega
  rcases heq with h576 | h577 | h578 | h579 | h580 | h581 | h582 | h583 | h584 | h585 | h586 | h587 | h588 | h589 | h590 | h591
  · have he : k = (576 : Fin 2425) := Fin.ext h576
    subst k
    rw [sourceRowsAt576]
    exact rowSound576 B hB hF
  · have he : k = (577 : Fin 2425) := Fin.ext h577
    subst k
    rw [sourceRowsAt577]
    exact rowSound577 B hB hF
  · have he : k = (578 : Fin 2425) := Fin.ext h578
    subst k
    rw [sourceRowsAt578]
    exact rowSound578_e B hB hF
  · have he : k = (579 : Fin 2425) := Fin.ext h579
    subst k
    rw [sourceRowsAt579]
    exact rowSound579_e B hB hF
  · have he : k = (580 : Fin 2425) := Fin.ext h580
    subst k
    rw [sourceRowsAt580]
    exact rowSound580_e B hB hF
  · have he : k = (581 : Fin 2425) := Fin.ext h581
    subst k
    rw [sourceRowsAt581]
    exact rowSound581_e B hB hF
  · have he : k = (582 : Fin 2425) := Fin.ext h582
    subst k
    rw [sourceRowsAt582]
    exact rowSound582_e B hB hF
  · have he : k = (583 : Fin 2425) := Fin.ext h583
    subst k
    rw [sourceRowsAt583]
    exact rowSound583 B hB hF
  · have he : k = (584 : Fin 2425) := Fin.ext h584
    subst k
    rw [sourceRowsAt584]
    exact rowSound584_e B hB hF
  · have he : k = (585 : Fin 2425) := Fin.ext h585
    subst k
    rw [sourceRowsAt585]
    exact rowSound585_e B hB hF
  · have he : k = (586 : Fin 2425) := Fin.ext h586
    subst k
    rw [sourceRowsAt586]
    exact rowSound586 B hB hF
  · have he : k = (587 : Fin 2425) := Fin.ext h587
    subst k
    rw [sourceRowsAt587]
    exact rowSound587_e B hB hF
  · have he : k = (588 : Fin 2425) := Fin.ext h588
    subst k
    rw [sourceRowsAt588]
    exact rowSound588_e B hB hF
  · have he : k = (589 : Fin 2425) := Fin.ext h589
    subst k
    rw [sourceRowsAt589]
    exact rowSound589_e B hB hF
  · have he : k = (590 : Fin 2425) := Fin.ext h590
    subst k
    rw [sourceRowsAt590]
    exact rowSound590 B hB hF
  · have he : k = (591 : Fin 2425) := Fin.ext h591
    subst k
    rw [sourceRowsAt591]
    exact rowSound591_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound36_e_oai
