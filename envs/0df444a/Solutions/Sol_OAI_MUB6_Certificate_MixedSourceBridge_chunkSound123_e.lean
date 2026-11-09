-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:43:03.906197+00:00
-- url     : https://prove2.me/submissions/cd8b0d0c-44db-455c-84e3-a5fb68cd340f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1968_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1969_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1970_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1971_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1972_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1976_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1977_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1978_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1983_e

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

theorem canonical1734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1734 raw1734Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw1734 raw1734Labels = mixedMoment B raw1734step0 raw1734step0Labels := by
      have ha : raw1734step0 = (fun i j => raw1734 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1734step0 raw1734; decide +kernel
      have hl : raw1734step0Labels = raw1734Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1734 raw1734Labels permutation152 permutation4
    mixedMoment B raw1734step0 raw1734step0Labels = mixedMoment B raw1734step1 raw1734step1Labels := by
      have ha : raw1734step1 = raw1734step0 := by apply Matrix.ext; unfold raw1734step1 raw1734step0; decide +kernel
      have hl : raw1734step0Labels = labelEmbedding7 ∘ raw1734step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1734step0 raw1734step0Labels raw1734step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical1735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1735 raw1735Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw1735 raw1735Labels = mixedMoment B raw1735step0 raw1735step0Labels := by
      have ha : raw1735step0 = (fun i j => raw1735 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1735step0 raw1735; decide +kernel
      have hl : raw1735step0Labels = raw1735Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1735 raw1735Labels permutation152 permutation4
    _ = mixedMoment B node2020 node2020Labels := by rfl

theorem canonical1736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1736 raw1736Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw1736 raw1736Labels = mixedMoment B raw1736step0 raw1736step0Labels := by
      have ha : raw1736step0 = (fun i j => raw1736 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1736step0 raw1736; decide +kernel
      have hl : raw1736step0Labels = raw1736Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1736 raw1736Labels permutation158 permutation6
    mixedMoment B raw1736step0 raw1736step0Labels = mixedMoment B raw1736step1 raw1736step1Labels := by
      have ha : raw1736step1 = -raw1736step0 := by apply Matrix.ext; change ∀ i j, raw1736step1 i j = -(raw1736step0 i j); unfold raw1736step1 raw1736step0; decide +kernel
      have hl : raw1736step1Labels = raw1736step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1736step1 raw1736step1Labels = mixedMoment B raw1736step2 raw1736step2Labels := by
      have ha : raw1736step2 = raw1736step1 := by apply Matrix.ext; unfold raw1736step2 raw1736step1; decide +kernel
      have hl : raw1736step1Labels = labelEmbedding1 ∘ raw1736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1736step1 raw1736step1Labels raw1736step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical167
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21425 raw21425Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw21425 raw21425Labels = mixedMoment B raw21425step0 raw21425step0Labels := by
      have hz : ∀ j, raw21425 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21425step0 = (fun i j => raw21425 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21425step0 raw21425; decide +kernel
      have hl : raw21425step0Labels = raw21425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21425 raw21425Labels permutation434 hz
    mixedMoment B raw21425step0 raw21425step0Labels = mixedMoment B raw21425step1 raw21425step1Labels := by
      have hz : ∀ j, raw21425step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21425step1 = (fun i j => raw21425step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21425step1 raw21425step0; decide +kernel
      have hl : raw21425step1Labels = raw21425step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21425step0 raw21425step0Labels permutation80 hz
    mixedMoment B raw21425step1 raw21425step1Labels = mixedMoment B raw21425step2 raw21425step2Labels := by
      have ha : raw21425step2 = (fun i j => raw21425step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21425step2 raw21425step1; decide +kernel
      have hl : raw21425step2Labels = raw21425step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21425step1 raw21425step1Labels permutation10 permutation7
    mixedMoment B raw21425step2 raw21425step2Labels = mixedMoment B raw21425step3 raw21425step3Labels := by
      have ha : raw21425step3 = -raw21425step2 := by apply Matrix.ext; change ∀ i j, raw21425step3 i j = -(raw21425step2 i j); unfold raw21425step3 raw21425step2; decide +kernel
      have hl : raw21425step3Labels = raw21425step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21425step3 raw21425step3Labels = mixedMoment B raw21425step4 raw21425step4Labels := by
      have ha : raw21425step4 = raw21425step3 := by apply Matrix.ext; unfold raw21425step4 raw21425step3; decide +kernel
      have hl : raw21425step3Labels = labelEmbedding1 ∘ raw21425step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21425step3 raw21425step3Labels raw21425step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical21429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21429 raw21429Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw21429 raw21429Labels = mixedMoment B raw21429step0 raw21429step0Labels := by
      have hz : ∀ j, raw21429 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21429step0 = (fun i j => raw21429 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21429step0 raw21429; decide +kernel
      have hl : raw21429step0Labels = raw21429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21429 raw21429Labels permutation434 hz
    mixedMoment B raw21429step0 raw21429step0Labels = mixedMoment B raw21429step1 raw21429step1Labels := by
      have hz : ∀ j, raw21429step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21429step1 = (fun i j => raw21429step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21429step1 raw21429step0; decide +kernel
      have hl : raw21429step1Labels = raw21429step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21429step0 raw21429step0Labels permutation80 hz
    mixedMoment B raw21429step1 raw21429step1Labels = mixedMoment B raw21429step2 raw21429step2Labels := by
      have ha : raw21429step2 = (fun i j => raw21429step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21429step2 raw21429step1; decide +kernel
      have hl : raw21429step2Labels = raw21429step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21429step1 raw21429step1Labels permutation10 permutation7
    mixedMoment B raw21429step2 raw21429step2Labels = mixedMoment B raw21429step3 raw21429step3Labels := by
      have ha : raw21429step3 = -raw21429step2 := by apply Matrix.ext; change ∀ i j, raw21429step3 i j = -(raw21429step2 i j); unfold raw21429step3 raw21429step2; decide +kernel
      have hl : raw21429step3Labels = raw21429step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21429step3 raw21429step3Labels = mixedMoment B raw21429step4 raw21429step4Labels := by
      have ha : raw21429step4 = raw21429step3 := by apply Matrix.ext; unfold raw21429step4 raw21429step3; decide +kernel
      have hl : raw21429step3Labels = labelEmbedding1 ∘ raw21429step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21429step3 raw21429step3Labels raw21429step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

theorem canonical21441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21441 raw21441Labels = mixedMoment B node1704 node1704Labels := by
  calc
    mixedMoment B raw21441 raw21441Labels = mixedMoment B raw21441step0 raw21441step0Labels := by
      have hz : ∀ j, raw21441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21441step0 = (fun i j => raw21441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21441step0 raw21441; decide +kernel
      have hl : raw21441step0Labels = raw21441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21441 raw21441Labels permutation346 hz
    mixedMoment B raw21441step0 raw21441step0Labels = mixedMoment B raw21441step1 raw21441step1Labels := by
      have ha : raw21441step1 = (fun i j => raw21441step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21441step1 raw21441step0; decide +kernel
      have hl : raw21441step1Labels = raw21441step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21441step0 raw21441step0Labels permutation40 permutation7
    mixedMoment B raw21441step1 raw21441step1Labels = mixedMoment B raw21441step2 raw21441step2Labels := by
      have ha : raw21441step2 = -raw21441step1 := by apply Matrix.ext; change ∀ i j, raw21441step2 i j = -(raw21441step1 i j); unfold raw21441step2 raw21441step1; decide +kernel
      have hl : raw21441step2Labels = raw21441step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21441step2 raw21441step2Labels = mixedMoment B raw21441step3 raw21441step3Labels := by
      have ha : raw21441step3 = raw21441step2 := by apply Matrix.ext; unfold raw21441step3 raw21441step2; decide +kernel
      have hl : raw21441step2Labels = labelEmbedding1 ∘ raw21441step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21441step2 raw21441step2Labels raw21441step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1704 node1704Labels := by rfl

theorem canonical21444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21444 raw21444Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw21444 raw21444Labels = mixedMoment B raw21444step0 raw21444step0Labels := by
      have hz : ∀ j, raw21444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21444step0 = (fun i j => raw21444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21444step0 raw21444; decide +kernel
      have hl : raw21444step0Labels = raw21444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21444 raw21444Labels permutation346 hz
    mixedMoment B raw21444step0 raw21444step0Labels = mixedMoment B raw21444step1 raw21444step1Labels := by
      have ha : raw21444step1 = (fun i j => raw21444step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21444step1 raw21444step0; decide +kernel
      have hl : raw21444step1Labels = raw21444step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21444step0 raw21444step0Labels permutation40 permutation7
    mixedMoment B raw21444step1 raw21444step1Labels = mixedMoment B raw21444step2 raw21444step2Labels := by
      have ha : raw21444step2 = -raw21444step1 := by apply Matrix.ext; change ∀ i j, raw21444step2 i j = -(raw21444step1 i j); unfold raw21444step2 raw21444step1; decide +kernel
      have hl : raw21444step2Labels = raw21444step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21444step2 raw21444step2Labels = mixedMoment B raw21444step3 raw21444step3Labels := by
      have ha : raw21444step3 = raw21444step2 := by apply Matrix.ext; unfold raw21444step3 raw21444step2; decide +kernel
      have hl : raw21444step2Labels = labelEmbedding1 ∘ raw21444step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21444step2 raw21444step2Labels raw21444step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

theorem canonical21461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21461 raw21461Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw21461 raw21461Labels = mixedMoment B raw21461step0 raw21461step0Labels := by
      have hz : ∀ j, raw21461 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21461step0 = (fun i j => raw21461 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21461step0 raw21461; decide +kernel
      have hl : raw21461step0Labels = raw21461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21461 raw21461Labels permutation520 hz
    mixedMoment B raw21461step0 raw21461step0Labels = mixedMoment B raw21461step1 raw21461step1Labels := by
      have hz : ∀ j, raw21461step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21461step1 = (fun i j => raw21461step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21461step1 raw21461step0; decide +kernel
      have hl : raw21461step1Labels = raw21461step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21461step0 raw21461step0Labels permutation104 hz
    mixedMoment B raw21461step1 raw21461step1Labels = mixedMoment B raw21461step2 raw21461step2Labels := by
      have hz : ∀ j, raw21461step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21461step2 = (fun i j => raw21461step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21461step2 raw21461step1; decide +kernel
      have hl : raw21461step2Labels = raw21461step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21461step1 raw21461step1Labels permutation20 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical198
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25392 raw25392Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw25392 raw25392Labels = mixedMoment B raw25392step0 raw25392step0Labels := by
      have ha : raw25392step0 = (fun i j => raw25392 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25392step0 raw25392; decide +kernel
      have hl : raw25392step0Labels = raw25392Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25392 raw25392Labels permutation184 permutation7
    mixedMoment B raw25392step0 raw25392step0Labels = mixedMoment B raw25392step1 raw25392step1Labels := by
      have ha : raw25392step1 = -raw25392step0 := by apply Matrix.ext; change ∀ i j, raw25392step1 i j = -(raw25392step0 i j); unfold raw25392step1 raw25392step0; decide +kernel
      have hl : raw25392step1Labels = raw25392step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25392step1 raw25392step1Labels = mixedMoment B raw25392step2 raw25392step2Labels := by
      have ha : raw25392step2 = raw25392step1 := by apply Matrix.ext; unfold raw25392step2 raw25392step1; decide +kernel
      have hl : raw25392step1Labels = labelEmbedding1 ∘ raw25392step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25392step1 raw25392step1Labels raw25392step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2190 node2190Labels := by rfl

theorem canonical25393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25393 raw25393Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw25393 raw25393Labels = mixedMoment B raw25393step0 raw25393step0Labels := by
      have hz : ∀ j, raw25393 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25393step0 = (fun i j => raw25393 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25393step0 raw25393; decide +kernel
      have hl : raw25393step0Labels = raw25393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25393 raw25393Labels permutation520 hz
    mixedMoment B raw25393step0 raw25393step0Labels = mixedMoment B raw25393step1 raw25393step1Labels := by
      have hz : ∀ j, raw25393step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25393step1 = (fun i j => raw25393step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25393step1 raw25393step0; decide +kernel
      have hl : raw25393step1Labels = raw25393step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25393step0 raw25393step0Labels permutation80 hz
    mixedMoment B raw25393step1 raw25393step1Labels = mixedMoment B raw25393step2 raw25393step2Labels := by
      have ha : raw25393step2 = (fun i j => raw25393step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25393step2 raw25393step1; decide +kernel
      have hl : raw25393step2Labels = raw25393step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25393step1 raw25393step1Labels permutation10 permutation7
    mixedMoment B raw25393step2 raw25393step2Labels = mixedMoment B raw25393step3 raw25393step3Labels := by
      have ha : raw25393step3 = -raw25393step2 := by apply Matrix.ext; change ∀ i j, raw25393step3 i j = -(raw25393step2 i j); unfold raw25393step3 raw25393step2; decide +kernel
      have hl : raw25393step3Labels = raw25393step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25393step3 raw25393step3Labels = mixedMoment B raw25393step4 raw25393step4Labels := by
      have ha : raw25393step4 = raw25393step3 := by apply Matrix.ext; unfold raw25393step4 raw25393step3; decide +kernel
      have hl : raw25393step3Labels = labelEmbedding1 ∘ raw25393step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25393step3 raw25393step3Labels raw25393step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

theorem canonical25394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25394 raw25394Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw25394 raw25394Labels = mixedMoment B raw25394step0 raw25394step0Labels := by
      have hz : ∀ j, raw25394 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25394step0 = (fun i j => raw25394 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25394step0 raw25394; decide +kernel
      have hl : raw25394step0Labels = raw25394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25394 raw25394Labels permutation346 hz
    mixedMoment B raw25394step0 raw25394step0Labels = mixedMoment B raw25394step1 raw25394step1Labels := by
      have ha : raw25394step1 = (fun i j => raw25394step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25394step1 raw25394step0; decide +kernel
      have hl : raw25394step1Labels = raw25394step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25394step0 raw25394step0Labels permutation40 permutation7
    mixedMoment B raw25394step1 raw25394step1Labels = mixedMoment B raw25394step2 raw25394step2Labels := by
      have ha : raw25394step2 = -raw25394step1 := by apply Matrix.ext; change ∀ i j, raw25394step2 i j = -(raw25394step1 i j); unfold raw25394step2 raw25394step1; decide +kernel
      have hl : raw25394step2Labels = raw25394step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25394step2 raw25394step2Labels = mixedMoment B raw25394step3 raw25394step3Labels := by
      have ha : raw25394step3 = raw25394step2 := by apply Matrix.ext; unfold raw25394step3 raw25394step2; decide +kernel
      have hl : raw25394step2Labels = labelEmbedding1 ∘ raw25394step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25394step2 raw25394step2Labels raw25394step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2244 node2244Labels := by rfl

theorem canonical25400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25400 raw25400Labels = mixedMoment B node1697 node1697Labels := by
  calc
    mixedMoment B raw25400 raw25400Labels = mixedMoment B raw25400step0 raw25400step0Labels := by
      have ha : raw25400step0 = (fun i j => raw25400 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25400step0 raw25400; decide +kernel
      have hl : raw25400step0Labels = raw25400Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25400 raw25400Labels permutation184 permutation7
    mixedMoment B raw25400step0 raw25400step0Labels = mixedMoment B raw25400step1 raw25400step1Labels := by
      have ha : raw25400step1 = -raw25400step0 := by apply Matrix.ext; change ∀ i j, raw25400step1 i j = -(raw25400step0 i j); unfold raw25400step1 raw25400step0; decide +kernel
      have hl : raw25400step1Labels = raw25400step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25400step1 raw25400step1Labels = mixedMoment B raw25400step2 raw25400step2Labels := by
      have ha : raw25400step2 = raw25400step1 := by apply Matrix.ext; unfold raw25400step2 raw25400step1; decide +kernel
      have hl : raw25400step1Labels = labelEmbedding1 ∘ raw25400step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25400step1 raw25400step1Labels raw25400step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1697 node1697Labels := by rfl

theorem canonical25404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25404 raw25404Labels = mixedMoment B node1712 node1712Labels := by
  calc
    mixedMoment B raw25404 raw25404Labels = mixedMoment B raw25404step0 raw25404step0Labels := by
      have hz : ∀ j, raw25404 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25404step0 = (fun i j => raw25404 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25404step0 raw25404; decide +kernel
      have hl : raw25404step0Labels = raw25404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25404 raw25404Labels permutation346 hz
    mixedMoment B raw25404step0 raw25404step0Labels = mixedMoment B raw25404step1 raw25404step1Labels := by
      have ha : raw25404step1 = (fun i j => raw25404step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25404step1 raw25404step0; decide +kernel
      have hl : raw25404step1Labels = raw25404step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25404step0 raw25404step0Labels permutation46 permutation7
    mixedMoment B raw25404step1 raw25404step1Labels = mixedMoment B raw25404step2 raw25404step2Labels := by
      have ha : raw25404step2 = -raw25404step1 := by apply Matrix.ext; change ∀ i j, raw25404step2 i j = -(raw25404step1 i j); unfold raw25404step2 raw25404step1; decide +kernel
      have hl : raw25404step2Labels = raw25404step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25404step2 raw25404step2Labels = mixedMoment B raw25404step3 raw25404step3Labels := by
      have ha : raw25404step3 = raw25404step2 := by apply Matrix.ext; unfold raw25404step3 raw25404step2; decide +kernel
      have hl : raw25404step2Labels = labelEmbedding1 ∘ raw25404step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25404step2 raw25404step2Labels raw25404step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1712 node1712Labels := by rfl

theorem canonical25409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25409 raw25409Labels = mixedMoment B node1712 node1712Labels := by
  calc
    mixedMoment B raw25409 raw25409Labels = mixedMoment B raw25409step0 raw25409step0Labels := by
      have hz : ∀ j, raw25409 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25409step0 = (fun i j => raw25409 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25409step0 raw25409; decide +kernel
      have hl : raw25409step0Labels = raw25409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25409 raw25409Labels permutation346 hz
    mixedMoment B raw25409step0 raw25409step0Labels = mixedMoment B raw25409step1 raw25409step1Labels := by
      have ha : raw25409step1 = (fun i j => raw25409step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25409step1 raw25409step0; decide +kernel
      have hl : raw25409step1Labels = raw25409step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25409step0 raw25409step0Labels permutation40 permutation7
    mixedMoment B raw25409step1 raw25409step1Labels = mixedMoment B raw25409step2 raw25409step2Labels := by
      have ha : raw25409step2 = -raw25409step1 := by apply Matrix.ext; change ∀ i j, raw25409step2 i j = -(raw25409step1 i j); unfold raw25409step2 raw25409step1; decide +kernel
      have hl : raw25409step2Labels = raw25409step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25409step2 raw25409step2Labels = mixedMoment B raw25409step3 raw25409step3Labels := by
      have ha : raw25409step3 = raw25409step2 := by apply Matrix.ext; unfold raw25409step3 raw25409step2; decide +kernel
      have hl : raw25409step2Labels = labelEmbedding1 ∘ raw25409step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25409step2 raw25409step2Labels raw25409step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1712 node1712Labels := by rfl

theorem canonical25421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25421 raw25421Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw25421 raw25421Labels = mixedMoment B raw25421step0 raw25421step0Labels := by
      have hz : ∀ j, raw25421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25421step0 = (fun i j => raw25421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25421step0 raw25421; decide +kernel
      have hl : raw25421step0Labels = raw25421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25421 raw25421Labels permutation346 hz
    _ = mixedMoment B node2106 node2106Labels := by rfl

theorem canonical25422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25422 raw25422Labels = mixedMoment B node941 node941Labels := by
  calc
    _ = mixedMoment B node941 node941Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical199
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25524 raw25524Labels = mixedMoment B node2077 node2077Labels := by
  calc
    _ = mixedMoment B node2077 node2077Labels := by rfl

theorem canonical25525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25525 raw25525Labels = mixedMoment B node1912 node1912Labels := by
  calc
    mixedMoment B raw25525 raw25525Labels = mixedMoment B raw25525step0 raw25525step0Labels := by
      have ha : raw25525step0 = (fun i j => raw25525 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25525step0 raw25525; decide +kernel
      have hl : raw25525step0Labels = raw25525Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25525 raw25525Labels permutation176 permutation2
    _ = mixedMoment B node1912 node1912Labels := by rfl

theorem canonical25529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25529 raw25529Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw25529 raw25529Labels = mixedMoment B raw25529step0 raw25529step0Labels := by
      have ha : raw25529step0 = (fun i j => raw25529 (permutation176 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25529step0 raw25529; decide +kernel
      have hl : raw25529step0Labels = raw25529Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25529 raw25529Labels permutation176 permutation0
    _ = mixedMoment B node4079 node4079Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical212
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27171 raw27171Labels = mixedMoment B node4833 node4833Labels := by
  calc
    mixedMoment B raw27171 raw27171Labels = mixedMoment B raw27171step0 raw27171step0Labels := by
      have ha : raw27171step0 = (fun i j => raw27171 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27171step0 raw27171; decide +kernel
      have hl : raw27171step0Labels = raw27171Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27171 raw27171Labels permutation170 permutation2
    _ = mixedMoment B node4833 node4833Labels := by rfl

theorem canonical27172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27172 raw27172Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw27172 raw27172Labels = mixedMoment B raw27172step0 raw27172step0Labels := by
      have hz : ∀ j, raw27172 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27172step0 = (fun i j => raw27172 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27172step0 raw27172; decide +kernel
      have hl : raw27172step0Labels = raw27172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27172 raw27172Labels permutation265 hz
    mixedMoment B raw27172step0 raw27172step0Labels = mixedMoment B raw27172step1 raw27172step1Labels := by
      have ha : raw27172step1 = (fun i j => raw27172step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27172step1 raw27172step0; decide +kernel
      have hl : raw27172step1Labels = raw27172step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27172step0 raw27172step0Labels permutation36 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

theorem canonical27197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27197 raw27197Labels = mixedMoment B node4351 node4351Labels := by
  calc
    _ = mixedMoment B node4351 node4351Labels := by rfl

theorem canonical27198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27198 raw27198Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw27198 raw27198Labels = mixedMoment B raw27198step0 raw27198step0Labels := by
      have hz : ∀ j, raw27198 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27198step0 = (fun i j => raw27198 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27198step0 raw27198; decide +kernel
      have hl : raw27198step0Labels = raw27198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27198 raw27198Labels permutation265 hz
    _ = mixedMoment B node4461 node4461Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical263
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33691 raw33691Labels = mixedMoment B node2748 node2748Labels := by
  calc
    mixedMoment B raw33691 raw33691Labels = mixedMoment B raw33691step0 raw33691step0Labels := by
      have hz : ∀ j, raw33691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33691step0 = (fun i j => raw33691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33691step0 raw33691; decide +kernel
      have hl : raw33691step0Labels = raw33691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33691 raw33691Labels permutation346 hz
    mixedMoment B raw33691step0 raw33691step0Labels = mixedMoment B raw33691step1 raw33691step1Labels := by
      have ha : raw33691step1 = (fun i j => raw33691step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33691step1 raw33691step0; decide +kernel
      have hl : raw33691step1Labels = raw33691step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33691step0 raw33691step0Labels permutation40 permutation7
    mixedMoment B raw33691step1 raw33691step1Labels = mixedMoment B raw33691step2 raw33691step2Labels := by
      have ha : raw33691step2 = -raw33691step1 := by apply Matrix.ext; change ∀ i j, raw33691step2 i j = -(raw33691step1 i j); unfold raw33691step2 raw33691step1; decide +kernel
      have hl : raw33691step2Labels = raw33691step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33691step2 raw33691step2Labels = mixedMoment B raw33691step3 raw33691step3Labels := by
      have ha : raw33691step3 = raw33691step2 := by apply Matrix.ext; unfold raw33691step3 raw33691step2; decide +kernel
      have hl : raw33691step2Labels = labelEmbedding1 ∘ raw33691step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33691step2 raw33691step2Labels raw33691step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2748 node2748Labels := by rfl

theorem canonical33692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33692 raw33692Labels = mixedMoment B node2708 node2708Labels := by
  calc
    mixedMoment B raw33692 raw33692Labels = mixedMoment B raw33692step0 raw33692step0Labels := by
      have ha : raw33692step0 = (fun i j => raw33692 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33692step0 raw33692; decide +kernel
      have hl : raw33692step0Labels = raw33692Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33692 raw33692Labels permutation184 permutation7
    mixedMoment B raw33692step0 raw33692step0Labels = mixedMoment B raw33692step1 raw33692step1Labels := by
      have ha : raw33692step1 = -raw33692step0 := by apply Matrix.ext; change ∀ i j, raw33692step1 i j = -(raw33692step0 i j); unfold raw33692step1 raw33692step0; decide +kernel
      have hl : raw33692step1Labels = raw33692step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33692step1 raw33692step1Labels = mixedMoment B raw33692step2 raw33692step2Labels := by
      have ha : raw33692step2 = raw33692step1 := by apply Matrix.ext; unfold raw33692step2 raw33692step1; decide +kernel
      have hl : raw33692step1Labels = labelEmbedding1 ∘ raw33692step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33692step1 raw33692step1Labels raw33692step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2708 node2708Labels := by rfl

theorem canonical33693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33693 raw33693Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw33693 raw33693Labels = mixedMoment B raw33693step0 raw33693step0Labels := by
      have hz : ∀ j, raw33693 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33693step0 = (fun i j => raw33693 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33693step0 raw33693; decide +kernel
      have hl : raw33693step0Labels = raw33693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33693 raw33693Labels permutation434 hz
    mixedMoment B raw33693step0 raw33693step0Labels = mixedMoment B raw33693step1 raw33693step1Labels := by
      have hz : ∀ j, raw33693step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33693step1 = (fun i j => raw33693step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33693step1 raw33693step0; decide +kernel
      have hl : raw33693step1Labels = raw33693step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33693step0 raw33693step0Labels permutation80 hz
    mixedMoment B raw33693step1 raw33693step1Labels = mixedMoment B raw33693step2 raw33693step2Labels := by
      have ha : raw33693step2 = (fun i j => raw33693step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33693step2 raw33693step1; decide +kernel
      have hl : raw33693step2Labels = raw33693step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33693step1 raw33693step1Labels permutation10 permutation7
    mixedMoment B raw33693step2 raw33693step2Labels = mixedMoment B raw33693step3 raw33693step3Labels := by
      have ha : raw33693step3 = -raw33693step2 := by apply Matrix.ext; change ∀ i j, raw33693step3 i j = -(raw33693step2 i j); unfold raw33693step3 raw33693step2; decide +kernel
      have hl : raw33693step3Labels = raw33693step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33693step3 raw33693step3Labels = mixedMoment B raw33693step4 raw33693step4Labels := by
      have ha : raw33693step4 = raw33693step3 := by apply Matrix.ext; unfold raw33693step4 raw33693step3; decide +kernel
      have hl : raw33693step3Labels = labelEmbedding1 ∘ raw33693step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33693step3 raw33693step3Labels raw33693step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical33694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33694 raw33694Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw33694 raw33694Labels = mixedMoment B raw33694step0 raw33694step0Labels := by
      have hz : ∀ j, raw33694 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33694step0 = (fun i j => raw33694 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33694step0 raw33694; decide +kernel
      have hl : raw33694step0Labels = raw33694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33694 raw33694Labels permutation520 hz
    mixedMoment B raw33694step0 raw33694step0Labels = mixedMoment B raw33694step1 raw33694step1Labels := by
      have hz : ∀ j, raw33694step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33694step1 = (fun i j => raw33694step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33694step1 raw33694step0; decide +kernel
      have hl : raw33694step1Labels = raw33694step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33694step0 raw33694step0Labels permutation80 hz
    mixedMoment B raw33694step1 raw33694step1Labels = mixedMoment B raw33694step2 raw33694step2Labels := by
      have ha : raw33694step2 = (fun i j => raw33694step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33694step2 raw33694step1; decide +kernel
      have hl : raw33694step2Labels = raw33694step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33694step1 raw33694step1Labels permutation10 permutation7
    mixedMoment B raw33694step2 raw33694step2Labels = mixedMoment B raw33694step3 raw33694step3Labels := by
      have ha : raw33694step3 = -raw33694step2 := by apply Matrix.ext; change ∀ i j, raw33694step3 i j = -(raw33694step2 i j); unfold raw33694step3 raw33694step2; decide +kernel
      have hl : raw33694step3Labels = raw33694step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33694step3 raw33694step3Labels = mixedMoment B raw33694step4 raw33694step4Labels := by
      have ha : raw33694step4 = raw33694step3 := by apply Matrix.ext; unfold raw33694step4 raw33694step3; decide +kernel
      have hl : raw33694step3Labels = labelEmbedding1 ∘ raw33694step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33694step3 raw33694step3Labels raw33694step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical33695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33695 raw33695Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw33695 raw33695Labels = mixedMoment B raw33695step0 raw33695step0Labels := by
      have hz : ∀ j, raw33695 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33695step0 = (fun i j => raw33695 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33695step0 raw33695; decide +kernel
      have hl : raw33695step0Labels = raw33695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33695 raw33695Labels permutation346 hz
    mixedMoment B raw33695step0 raw33695step0Labels = mixedMoment B raw33695step1 raw33695step1Labels := by
      have ha : raw33695step1 = (fun i j => raw33695step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33695step1 raw33695step0; decide +kernel
      have hl : raw33695step1Labels = raw33695step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33695step0 raw33695step0Labels permutation40 permutation7
    mixedMoment B raw33695step1 raw33695step1Labels = mixedMoment B raw33695step2 raw33695step2Labels := by
      have ha : raw33695step2 = -raw33695step1 := by apply Matrix.ext; change ∀ i j, raw33695step2 i j = -(raw33695step1 i j); unfold raw33695step2 raw33695step1; decide +kernel
      have hl : raw33695step2Labels = raw33695step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33695step2 raw33695step2Labels = mixedMoment B raw33695step3 raw33695step3Labels := by
      have ha : raw33695step3 = raw33695step2 := by apply Matrix.ext; unfold raw33695step3 raw33695step2; decide +kernel
      have hl : raw33695step2Labels = labelEmbedding1 ∘ raw33695step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33695step2 raw33695step2Labels raw33695step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2751 node2751Labels := by rfl

theorem canonical33696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33696 raw33696Labels = mixedMoment B node2231 node2231Labels := by
  calc
    mixedMoment B raw33696 raw33696Labels = mixedMoment B raw33696step0 raw33696step0Labels := by
      have ha : raw33696step0 = (fun i j => raw33696 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33696step0 raw33696; decide +kernel
      have hl : raw33696step0Labels = raw33696Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33696 raw33696Labels permutation184 permutation7
    mixedMoment B raw33696step0 raw33696step0Labels = mixedMoment B raw33696step1 raw33696step1Labels := by
      have ha : raw33696step1 = -raw33696step0 := by apply Matrix.ext; change ∀ i j, raw33696step1 i j = -(raw33696step0 i j); unfold raw33696step1 raw33696step0; decide +kernel
      have hl : raw33696step1Labels = raw33696step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33696step1 raw33696step1Labels = mixedMoment B raw33696step2 raw33696step2Labels := by
      have ha : raw33696step2 = raw33696step1 := by apply Matrix.ext; unfold raw33696step2 raw33696step1; decide +kernel
      have hl : raw33696step1Labels = labelEmbedding1 ∘ raw33696step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33696step1 raw33696step1Labels raw33696step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2231 node2231Labels := by rfl

theorem canonical33697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33697 raw33697Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw33697 raw33697Labels = mixedMoment B raw33697step0 raw33697step0Labels := by
      have hz : ∀ j, raw33697 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33697step0 = (fun i j => raw33697 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33697step0 raw33697; decide +kernel
      have hl : raw33697step0Labels = raw33697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33697 raw33697Labels permutation434 hz
    mixedMoment B raw33697step0 raw33697step0Labels = mixedMoment B raw33697step1 raw33697step1Labels := by
      have ha : raw33697step1 = (fun i j => raw33697step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33697step1 raw33697step0; decide +kernel
      have hl : raw33697step1Labels = raw33697step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33697step0 raw33697step0Labels permutation40 permutation7
    mixedMoment B raw33697step1 raw33697step1Labels = mixedMoment B raw33697step2 raw33697step2Labels := by
      have ha : raw33697step2 = -raw33697step1 := by apply Matrix.ext; change ∀ i j, raw33697step2 i j = -(raw33697step1 i j); unfold raw33697step2 raw33697step1; decide +kernel
      have hl : raw33697step2Labels = raw33697step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33697step2 raw33697step2Labels = mixedMoment B raw33697step3 raw33697step3Labels := by
      have ha : raw33697step3 = raw33697step2 := by apply Matrix.ext; unfold raw33697step3 raw33697step2; decide +kernel
      have hl : raw33697step2Labels = labelEmbedding1 ∘ raw33697step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33697step2 raw33697step2Labels raw33697step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

theorem canonical33698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33698 raw33698Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw33698 raw33698Labels = mixedMoment B raw33698step0 raw33698step0Labels := by
      have hz : ∀ j, raw33698 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33698step0 = (fun i j => raw33698 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33698step0 raw33698; decide +kernel
      have hl : raw33698step0Labels = raw33698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33698 raw33698Labels permutation520 hz
    mixedMoment B raw33698step0 raw33698step0Labels = mixedMoment B raw33698step1 raw33698step1Labels := by
      have ha : raw33698step1 = (fun i j => raw33698step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33698step1 raw33698step0; decide +kernel
      have hl : raw33698step1Labels = raw33698step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33698step0 raw33698step0Labels permutation40 permutation7
    mixedMoment B raw33698step1 raw33698step1Labels = mixedMoment B raw33698step2 raw33698step2Labels := by
      have ha : raw33698step2 = -raw33698step1 := by apply Matrix.ext; change ∀ i j, raw33698step2 i j = -(raw33698step1 i j); unfold raw33698step2 raw33698step1; decide +kernel
      have hl : raw33698step2Labels = raw33698step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33698step2 raw33698step2Labels = mixedMoment B raw33698step3 raw33698step3Labels := by
      have ha : raw33698step3 = raw33698step2 := by apply Matrix.ext; unfold raw33698step3 raw33698step2; decide +kernel
      have hl : raw33698step2Labels = labelEmbedding1 ∘ raw33698step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33698step2 raw33698step2Labels raw33698step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

theorem canonical33699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33699 raw33699Labels = mixedMoment B node2232 node2232Labels := by
  calc
    mixedMoment B raw33699 raw33699Labels = mixedMoment B raw33699step0 raw33699step0Labels := by
      have ha : raw33699step0 = (fun i j => raw33699 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33699step0 raw33699; decide +kernel
      have hl : raw33699step0Labels = raw33699Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33699 raw33699Labels permutation184 permutation7
    mixedMoment B raw33699step0 raw33699step0Labels = mixedMoment B raw33699step1 raw33699step1Labels := by
      have ha : raw33699step1 = -raw33699step0 := by apply Matrix.ext; change ∀ i j, raw33699step1 i j = -(raw33699step0 i j); unfold raw33699step1 raw33699step0; decide +kernel
      have hl : raw33699step1Labels = raw33699step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33699step1 raw33699step1Labels = mixedMoment B raw33699step2 raw33699step2Labels := by
      have ha : raw33699step2 = raw33699step1 := by apply Matrix.ext; unfold raw33699step2 raw33699step1; decide +kernel
      have hl : raw33699step1Labels = labelEmbedding1 ∘ raw33699step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33699step1 raw33699step1Labels raw33699step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2232 node2232Labels := by rfl

theorem canonical33700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33700 raw33700Labels = mixedMoment B node2249 node2249Labels := by
  calc
    mixedMoment B raw33700 raw33700Labels = mixedMoment B raw33700step0 raw33700step0Labels := by
      have hz : ∀ j, raw33700 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33700step0 = (fun i j => raw33700 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33700step0 raw33700; decide +kernel
      have hl : raw33700step0Labels = raw33700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33700 raw33700Labels permutation346 hz
    mixedMoment B raw33700step0 raw33700step0Labels = mixedMoment B raw33700step1 raw33700step1Labels := by
      have ha : raw33700step1 = (fun i j => raw33700step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33700step1 raw33700step0; decide +kernel
      have hl : raw33700step1Labels = raw33700step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33700step0 raw33700step0Labels permutation46 permutation7
    mixedMoment B raw33700step1 raw33700step1Labels = mixedMoment B raw33700step2 raw33700step2Labels := by
      have ha : raw33700step2 = -raw33700step1 := by apply Matrix.ext; change ∀ i j, raw33700step2 i j = -(raw33700step1 i j); unfold raw33700step2 raw33700step1; decide +kernel
      have hl : raw33700step2Labels = raw33700step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33700step2 raw33700step2Labels = mixedMoment B raw33700step3 raw33700step3Labels := by
      have ha : raw33700step3 = raw33700step2 := by apply Matrix.ext; unfold raw33700step3 raw33700step2; decide +kernel
      have hl : raw33700step2Labels = labelEmbedding1 ∘ raw33700step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33700step2 raw33700step2Labels raw33700step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2249 node2249Labels := by rfl

theorem canonical33701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33701 raw33701Labels = mixedMoment B node2194 node2194Labels := by
  calc
    mixedMoment B raw33701 raw33701Labels = mixedMoment B raw33701step0 raw33701step0Labels := by
      have ha : raw33701step0 = (fun i j => raw33701 (permutation190 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33701step0 raw33701; decide +kernel
      have hl : raw33701step0Labels = raw33701Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33701 raw33701Labels permutation190 permutation7
    mixedMoment B raw33701step0 raw33701step0Labels = mixedMoment B raw33701step1 raw33701step1Labels := by
      have ha : raw33701step1 = -raw33701step0 := by apply Matrix.ext; change ∀ i j, raw33701step1 i j = -(raw33701step0 i j); unfold raw33701step1 raw33701step0; decide +kernel
      have hl : raw33701step1Labels = raw33701step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33701step1 raw33701step1Labels = mixedMoment B raw33701step2 raw33701step2Labels := by
      have ha : raw33701step2 = raw33701step1 := by apply Matrix.ext; unfold raw33701step2 raw33701step1; decide +kernel
      have hl : raw33701step1Labels = labelEmbedding1 ∘ raw33701step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33701step1 raw33701step1Labels raw33701step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2194 node2194Labels := by rfl

theorem canonical33702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33702 raw33702Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw33702 raw33702Labels = mixedMoment B raw33702step0 raw33702step0Labels := by
      have hz : ∀ j, raw33702 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33702step0 = (fun i j => raw33702 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33702step0 raw33702; decide +kernel
      have hl : raw33702step0Labels = raw33702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33702 raw33702Labels permutation520 hz
    mixedMoment B raw33702step0 raw33702step0Labels = mixedMoment B raw33702step1 raw33702step1Labels := by
      have hz : ∀ j, raw33702step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33702step1 = (fun i j => raw33702step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33702step1 raw33702step0; decide +kernel
      have hl : raw33702step1Labels = raw33702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33702step0 raw33702step0Labels permutation80 hz
    mixedMoment B raw33702step1 raw33702step1Labels = mixedMoment B raw33702step2 raw33702step2Labels := by
      have ha : raw33702step2 = (fun i j => raw33702step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33702step2 raw33702step1; decide +kernel
      have hl : raw33702step2Labels = raw33702step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33702step1 raw33702step1Labels permutation10 permutation7
    mixedMoment B raw33702step2 raw33702step2Labels = mixedMoment B raw33702step3 raw33702step3Labels := by
      have ha : raw33702step3 = -raw33702step2 := by apply Matrix.ext; change ∀ i j, raw33702step3 i j = -(raw33702step2 i j); unfold raw33702step3 raw33702step2; decide +kernel
      have hl : raw33702step3Labels = raw33702step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33702step3 raw33702step3Labels = mixedMoment B raw33702step4 raw33702step4Labels := by
      have ha : raw33702step4 = raw33702step3 := by apply Matrix.ext; unfold raw33702step4 raw33702step3; decide +kernel
      have hl : raw33702step3Labels = labelEmbedding1 ∘ raw33702step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33702step3 raw33702step3Labels raw33702step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2276 node2276Labels := by rfl

theorem canonical33703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33703 raw33703Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw33703 raw33703Labels = mixedMoment B raw33703step0 raw33703step0Labels := by
      have hz : ∀ j, raw33703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33703step0 = (fun i j => raw33703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33703step0 raw33703; decide +kernel
      have hl : raw33703step0Labels = raw33703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33703 raw33703Labels permutation346 hz
    mixedMoment B raw33703step0 raw33703step0Labels = mixedMoment B raw33703step1 raw33703step1Labels := by
      have ha : raw33703step1 = (fun i j => raw33703step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33703step1 raw33703step0; decide +kernel
      have hl : raw33703step1Labels = raw33703step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33703step0 raw33703step0Labels permutation46 permutation7
    mixedMoment B raw33703step1 raw33703step1Labels = mixedMoment B raw33703step2 raw33703step2Labels := by
      have ha : raw33703step2 = -raw33703step1 := by apply Matrix.ext; change ∀ i j, raw33703step2 i j = -(raw33703step1 i j); unfold raw33703step2 raw33703step1; decide +kernel
      have hl : raw33703step2Labels = raw33703step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33703step2 raw33703step2Labels = mixedMoment B raw33703step3 raw33703step3Labels := by
      have ha : raw33703step3 = raw33703step2 := by apply Matrix.ext; unfold raw33703step3 raw33703step2; decide +kernel
      have hl : raw33703step2Labels = labelEmbedding1 ∘ raw33703step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33703step2 raw33703step2Labels raw33703step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2251 node2251Labels := by rfl

theorem canonical33704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33704 raw33704Labels = mixedMoment B node2249 node2249Labels := by
  calc
    mixedMoment B raw33704 raw33704Labels = mixedMoment B raw33704step0 raw33704step0Labels := by
      have hz : ∀ j, raw33704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33704step0 = (fun i j => raw33704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33704step0 raw33704; decide +kernel
      have hl : raw33704step0Labels = raw33704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33704 raw33704Labels permutation346 hz
    mixedMoment B raw33704step0 raw33704step0Labels = mixedMoment B raw33704step1 raw33704step1Labels := by
      have ha : raw33704step1 = (fun i j => raw33704step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33704step1 raw33704step0; decide +kernel
      have hl : raw33704step1Labels = raw33704step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33704step0 raw33704step0Labels permutation40 permutation7
    mixedMoment B raw33704step1 raw33704step1Labels = mixedMoment B raw33704step2 raw33704step2Labels := by
      have ha : raw33704step2 = -raw33704step1 := by apply Matrix.ext; change ∀ i j, raw33704step2 i j = -(raw33704step1 i j); unfold raw33704step2 raw33704step1; decide +kernel
      have hl : raw33704step2Labels = raw33704step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33704step2 raw33704step2Labels = mixedMoment B raw33704step3 raw33704step3Labels := by
      have ha : raw33704step3 = raw33704step2 := by apply Matrix.ext; unfold raw33704step3 raw33704step2; decide +kernel
      have hl : raw33704step2Labels = labelEmbedding1 ∘ raw33704step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33704step2 raw33704step2Labels raw33704step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2249 node2249Labels := by rfl

theorem canonical33705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33705 raw33705Labels = mixedMoment B node2194 node2194Labels := by
  calc
    mixedMoment B raw33705 raw33705Labels = mixedMoment B raw33705step0 raw33705step0Labels := by
      have ha : raw33705step0 = (fun i j => raw33705 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33705step0 raw33705; decide +kernel
      have hl : raw33705step0Labels = raw33705Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33705 raw33705Labels permutation184 permutation7
    mixedMoment B raw33705step0 raw33705step0Labels = mixedMoment B raw33705step1 raw33705step1Labels := by
      have ha : raw33705step1 = -raw33705step0 := by apply Matrix.ext; change ∀ i j, raw33705step1 i j = -(raw33705step0 i j); unfold raw33705step1 raw33705step0; decide +kernel
      have hl : raw33705step1Labels = raw33705step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33705step1 raw33705step1Labels = mixedMoment B raw33705step2 raw33705step2Labels := by
      have ha : raw33705step2 = raw33705step1 := by apply Matrix.ext; unfold raw33705step2 raw33705step1; decide +kernel
      have hl : raw33705step1Labels = labelEmbedding1 ∘ raw33705step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33705step1 raw33705step1Labels raw33705step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2194 node2194Labels := by rfl

theorem canonical33706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33706 raw33706Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw33706 raw33706Labels = mixedMoment B raw33706step0 raw33706step0Labels := by
      have hz : ∀ j, raw33706 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33706step0 = (fun i j => raw33706 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33706step0 raw33706; decide +kernel
      have hl : raw33706step0Labels = raw33706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33706 raw33706Labels permutation434 hz
    mixedMoment B raw33706step0 raw33706step0Labels = mixedMoment B raw33706step1 raw33706step1Labels := by
      have hz : ∀ j, raw33706step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33706step1 = (fun i j => raw33706step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33706step1 raw33706step0; decide +kernel
      have hl : raw33706step1Labels = raw33706step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33706step0 raw33706step0Labels permutation80 hz
    mixedMoment B raw33706step1 raw33706step1Labels = mixedMoment B raw33706step2 raw33706step2Labels := by
      have ha : raw33706step2 = (fun i j => raw33706step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33706step2 raw33706step1; decide +kernel
      have hl : raw33706step2Labels = raw33706step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33706step1 raw33706step1Labels permutation10 permutation7
    mixedMoment B raw33706step2 raw33706step2Labels = mixedMoment B raw33706step3 raw33706step3Labels := by
      have ha : raw33706step3 = -raw33706step2 := by apply Matrix.ext; change ∀ i j, raw33706step3 i j = -(raw33706step2 i j); unfold raw33706step3 raw33706step2; decide +kernel
      have hl : raw33706step3Labels = raw33706step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33706step3 raw33706step3Labels = mixedMoment B raw33706step4 raw33706step4Labels := by
      have ha : raw33706step4 = raw33706step3 := by apply Matrix.ext; unfold raw33706step4 raw33706step3; decide +kernel
      have hl : raw33706step3Labels = labelEmbedding1 ∘ raw33706step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33706step3 raw33706step3Labels raw33706step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2276 node2276Labels := by rfl

theorem canonical33707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33707 raw33707Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw33707 raw33707Labels = mixedMoment B raw33707step0 raw33707step0Labels := by
      have hz : ∀ j, raw33707 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33707step0 = (fun i j => raw33707 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33707step0 raw33707; decide +kernel
      have hl : raw33707step0Labels = raw33707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33707 raw33707Labels permutation346 hz
    mixedMoment B raw33707step0 raw33707step0Labels = mixedMoment B raw33707step1 raw33707step1Labels := by
      have ha : raw33707step1 = (fun i j => raw33707step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33707step1 raw33707step0; decide +kernel
      have hl : raw33707step1Labels = raw33707step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33707step0 raw33707step0Labels permutation40 permutation7
    mixedMoment B raw33707step1 raw33707step1Labels = mixedMoment B raw33707step2 raw33707step2Labels := by
      have ha : raw33707step2 = -raw33707step1 := by apply Matrix.ext; change ∀ i j, raw33707step2 i j = -(raw33707step1 i j); unfold raw33707step2 raw33707step1; decide +kernel
      have hl : raw33707step2Labels = raw33707step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33707step2 raw33707step2Labels = mixedMoment B raw33707step3 raw33707step3Labels := by
      have ha : raw33707step3 = raw33707step2 := by apply Matrix.ext; unfold raw33707step3 raw33707step2; decide +kernel
      have hl : raw33707step2Labels = labelEmbedding1 ∘ raw33707step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33707step2 raw33707step2Labels raw33707step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2251 node2251Labels := by rfl

theorem canonical33708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33708 raw33708Labels = mixedMoment B node2239 node2239Labels := by
  calc
    mixedMoment B raw33708 raw33708Labels = mixedMoment B raw33708step0 raw33708step0Labels := by
      have hz : ∀ j, raw33708 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33708step0 = (fun i j => raw33708 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33708step0 raw33708; decide +kernel
      have hl : raw33708step0Labels = raw33708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33708 raw33708Labels permutation346 hz
    mixedMoment B raw33708step0 raw33708step0Labels = mixedMoment B raw33708step1 raw33708step1Labels := by
      have ha : raw33708step1 = (fun i j => raw33708step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33708step1 raw33708step0; decide +kernel
      have hl : raw33708step1Labels = raw33708step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33708step0 raw33708step0Labels permutation40 permutation7
    mixedMoment B raw33708step1 raw33708step1Labels = mixedMoment B raw33708step2 raw33708step2Labels := by
      have ha : raw33708step2 = -raw33708step1 := by apply Matrix.ext; change ∀ i j, raw33708step2 i j = -(raw33708step1 i j); unfold raw33708step2 raw33708step1; decide +kernel
      have hl : raw33708step2Labels = raw33708step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33708step2 raw33708step2Labels = mixedMoment B raw33708step3 raw33708step3Labels := by
      have ha : raw33708step3 = raw33708step2 := by apply Matrix.ext; unfold raw33708step3 raw33708step2; decide +kernel
      have hl : raw33708step2Labels = labelEmbedding1 ∘ raw33708step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33708step2 raw33708step2Labels raw33708step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2239 node2239Labels := by rfl

theorem canonical33709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33709 raw33709Labels = mixedMoment B node2189 node2189Labels := by
  calc
    mixedMoment B raw33709 raw33709Labels = mixedMoment B raw33709step0 raw33709step0Labels := by
      have ha : raw33709step0 = (fun i j => raw33709 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33709step0 raw33709; decide +kernel
      have hl : raw33709step0Labels = raw33709Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33709 raw33709Labels permutation184 permutation7
    mixedMoment B raw33709step0 raw33709step0Labels = mixedMoment B raw33709step1 raw33709step1Labels := by
      have ha : raw33709step1 = -raw33709step0 := by apply Matrix.ext; change ∀ i j, raw33709step1 i j = -(raw33709step0 i j); unfold raw33709step1 raw33709step0; decide +kernel
      have hl : raw33709step1Labels = raw33709step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33709step1 raw33709step1Labels = mixedMoment B raw33709step2 raw33709step2Labels := by
      have ha : raw33709step2 = raw33709step1 := by apply Matrix.ext; unfold raw33709step2 raw33709step1; decide +kernel
      have hl : raw33709step1Labels = labelEmbedding1 ∘ raw33709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33709step1 raw33709step1Labels raw33709step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2189 node2189Labels := by rfl

theorem canonical33710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33710 raw33710Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw33710 raw33710Labels = mixedMoment B raw33710step0 raw33710step0Labels := by
      have hz : ∀ j, raw33710 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33710step0 = (fun i j => raw33710 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33710step0 raw33710; decide +kernel
      have hl : raw33710step0Labels = raw33710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33710 raw33710Labels permutation520 hz
    mixedMoment B raw33710step0 raw33710step0Labels = mixedMoment B raw33710step1 raw33710step1Labels := by
      have hz : ∀ j, raw33710step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33710step1 = (fun i j => raw33710step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33710step1 raw33710step0; decide +kernel
      have hl : raw33710step1Labels = raw33710step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33710step0 raw33710step0Labels permutation80 hz
    mixedMoment B raw33710step1 raw33710step1Labels = mixedMoment B raw33710step2 raw33710step2Labels := by
      have ha : raw33710step2 = (fun i j => raw33710step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33710step2 raw33710step1; decide +kernel
      have hl : raw33710step2Labels = raw33710step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33710step1 raw33710step1Labels permutation10 permutation7
    mixedMoment B raw33710step2 raw33710step2Labels = mixedMoment B raw33710step3 raw33710step3Labels := by
      have ha : raw33710step3 = -raw33710step2 := by apply Matrix.ext; change ∀ i j, raw33710step3 i j = -(raw33710step2 i j); unfold raw33710step3 raw33710step2; decide +kernel
      have hl : raw33710step3Labels = raw33710step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33710step3 raw33710step3Labels = mixedMoment B raw33710step4 raw33710step4Labels := by
      have ha : raw33710step4 = raw33710step3 := by apply Matrix.ext; unfold raw33710step4 raw33710step3; decide +kernel
      have hl : raw33710step3Labels = labelEmbedding1 ∘ raw33710step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33710step3 raw33710step3Labels raw33710step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical33711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33711 raw33711Labels = mixedMoment B node3050 node3050Labels := by
  calc
    mixedMoment B raw33711 raw33711Labels = mixedMoment B raw33711step0 raw33711step0Labels := by
      have hz : ∀ j, raw33711 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33711step0 = (fun i j => raw33711 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33711step0 raw33711; decide +kernel
      have hl : raw33711step0Labels = raw33711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33711 raw33711Labels permutation346 hz
    mixedMoment B raw33711step0 raw33711step0Labels = mixedMoment B raw33711step1 raw33711step1Labels := by
      have ha : raw33711step1 = (fun i j => raw33711step0 (permutation77 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33711step1 raw33711step0; decide +kernel
      have hl : raw33711step1Labels = raw33711step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33711step0 raw33711step0Labels permutation77 permutation4
    mixedMoment B raw33711step1 raw33711step1Labels = mixedMoment B raw33711step2 raw33711step2Labels := by
      have ha : raw33711step2 = -raw33711step1 := by apply Matrix.ext; change ∀ i j, raw33711step2 i j = -(raw33711step1 i j); unfold raw33711step2 raw33711step1; decide +kernel
      have hl : raw33711step2Labels = raw33711step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3050 node3050Labels := by rfl

theorem canonical33712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33712 raw33712Labels = mixedMoment B node1821 node1821Labels := by
  calc
    _ = mixedMoment B node1821 node1821Labels := by rfl

theorem canonical33713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33713 raw33713Labels = mixedMoment B node1826 node1826Labels := by
  calc
    mixedMoment B raw33713 raw33713Labels = mixedMoment B raw33713step0 raw33713step0Labels := by
      have hz : ∀ j, raw33713 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33713step0 = (fun i j => raw33713 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33713step0 raw33713; decide +kernel
      have hl : raw33713step0Labels = raw33713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33713 raw33713Labels permutation346 hz
    mixedMoment B raw33713step0 raw33713step0Labels = mixedMoment B raw33713step1 raw33713step1Labels := by
      have ha : raw33713step1 = (fun i j => raw33713step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33713step1 raw33713step0; decide +kernel
      have hl : raw33713step1Labels = raw33713step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33713step0 raw33713step0Labels permutation34 permutation2
    _ = mixedMoment B node1826 node1826Labels := by rfl

theorem canonical33714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33714 raw33714Labels = mixedMoment B node1826 node1826Labels := by
  calc
    mixedMoment B raw33714 raw33714Labels = mixedMoment B raw33714step0 raw33714step0Labels := by
      have hz : ∀ j, raw33714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33714step0 = (fun i j => raw33714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33714step0 raw33714; decide +kernel
      have hl : raw33714step0Labels = raw33714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33714 raw33714Labels permutation346 hz
    _ = mixedMoment B node1826 node1826Labels := by rfl

theorem canonical33715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33715 raw33715Labels = mixedMoment B node1823 node1823Labels := by
  calc
    mixedMoment B raw33715 raw33715Labels = mixedMoment B raw33715step0 raw33715step0Labels := by
      have hz : ∀ j, raw33715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33715step0 = (fun i j => raw33715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33715step0 raw33715; decide +kernel
      have hl : raw33715step0Labels = raw33715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33715 raw33715Labels permutation346 hz
    _ = mixedMoment B node1823 node1823Labels := by rfl

theorem canonical33716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33716 raw33716Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw33716 raw33716Labels = mixedMoment B raw33716step0 raw33716step0Labels := by
      have hz : ∀ j, raw33716 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33716step0 = (fun i j => raw33716 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33716step0 raw33716; decide +kernel
      have hl : raw33716step0Labels = raw33716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33716 raw33716Labels permutation434 hz
    _ = mixedMoment B node2106 node2106Labels := by rfl

theorem canonical33717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33717 raw33717Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw33717 raw33717Labels = mixedMoment B raw33717step0 raw33717step0Labels := by
      have hz : ∀ j, raw33717 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33717step0 = (fun i j => raw33717 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33717step0 raw33717; decide +kernel
      have hl : raw33717step0Labels = raw33717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33717 raw33717Labels permutation520 hz
    _ = mixedMoment B node2106 node2106Labels := by rfl

theorem canonical33718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33718 raw33718Labels = mixedMoment B node2104 node2104Labels := by
  calc
    _ = mixedMoment B node2104 node2104Labels := by rfl

theorem canonical33784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33784 raw33784Labels = mixedMoment B node3446 node3446Labels := by
  calc
    mixedMoment B raw33784 raw33784Labels = mixedMoment B raw33784step0 raw33784step0Labels := by
      have ha : raw33784step0 = (fun i j => raw33784 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33784step0 raw33784; decide +kernel
      have hl : raw33784step0Labels = raw33784Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33784 raw33784Labels permutation176 permutation2
    _ = mixedMoment B node3446 node3446Labels := by rfl

theorem canonical33788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33788 raw33788Labels = mixedMoment B node1879 node1879Labels := by
  calc
    mixedMoment B raw33788 raw33788Labels = mixedMoment B raw33788step0 raw33788step0Labels := by
      have ha : raw33788step0 = (fun i j => raw33788 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33788step0 raw33788; decide +kernel
      have hl : raw33788step0Labels = raw33788Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33788 raw33788Labels permutation178 permutation2
    _ = mixedMoment B node1879 node1879Labels := by rfl

theorem canonical33789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33789 raw33789Labels = mixedMoment B node1879 node1879Labels := by
  calc
    mixedMoment B raw33789 raw33789Labels = mixedMoment B raw33789step0 raw33789step0Labels := by
      have ha : raw33789step0 = (fun i j => raw33789 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33789step0 raw33789; decide +kernel
      have hl : raw33789step0Labels = raw33789Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33789 raw33789Labels permutation176 permutation2
    _ = mixedMoment B node1879 node1879Labels := by rfl

theorem canonical33790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33790 raw33790Labels = mixedMoment B node1877 node1877Labels := by
  calc
    mixedMoment B raw33790 raw33790Labels = mixedMoment B raw33790step0 raw33790step0Labels := by
      have ha : raw33790step0 = (fun i j => raw33790 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33790step0 raw33790; decide +kernel
      have hl : raw33790step0Labels = raw33790Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33790 raw33790Labels permutation176 permutation2
    _ = mixedMoment B node1877 node1877Labels := by rfl

theorem canonical33791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33791 raw33791Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw33791 raw33791Labels = mixedMoment B raw33791step0 raw33791step0Labels := by
      have ha : raw33791step0 = (fun i j => raw33791 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33791step0 raw33791; decide +kernel
      have hl : raw33791step0Labels = raw33791Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33791 raw33791Labels permutation170 permutation7
    mixedMoment B raw33791step0 raw33791step0Labels = mixedMoment B raw33791step1 raw33791step1Labels := by
      have ha : raw33791step1 = -raw33791step0 := by apply Matrix.ext; change ∀ i j, raw33791step1 i j = -(raw33791step0 i j); unfold raw33791step1 raw33791step0; decide +kernel
      have hl : raw33791step1Labels = raw33791step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33791step1 raw33791step1Labels = mixedMoment B raw33791step2 raw33791step2Labels := by
      have ha : raw33791step2 = raw33791step1 := by apply Matrix.ext; unfold raw33791step2 raw33791step1; decide +kernel
      have hl : raw33791step1Labels = labelEmbedding10 ∘ raw33791step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33791step1 raw33791step1Labels raw33791step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

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

theorem canonical33792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33792 raw33792Labels = mixedMoment B node5263 node5263Labels := by
  calc
    mixedMoment B raw33792 raw33792Labels = mixedMoment B raw33792step0 raw33792step0Labels := by
      have ha : raw33792step0 = (fun i j => raw33792 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33792step0 raw33792; decide +kernel
      have hl : raw33792step0Labels = raw33792Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33792 raw33792Labels permutation170 permutation7
    mixedMoment B raw33792step0 raw33792step0Labels = mixedMoment B raw33792step1 raw33792step1Labels := by
      have ha : raw33792step1 = -raw33792step0 := by apply Matrix.ext; change ∀ i j, raw33792step1 i j = -(raw33792step0 i j); unfold raw33792step1 raw33792step0; decide +kernel
      have hl : raw33792step1Labels = raw33792step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33792step1 raw33792step1Labels = mixedMoment B raw33792step2 raw33792step2Labels := by
      have ha : raw33792step2 = raw33792step1 := by apply Matrix.ext; unfold raw33792step2 raw33792step1; decide +kernel
      have hl : raw33792step1Labels = labelEmbedding10 ∘ raw33792step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33792step1 raw33792step1Labels raw33792step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5263 node5263Labels := by rfl

theorem canonical33793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33793 raw33793Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw33793 raw33793Labels = mixedMoment B raw33793step0 raw33793step0Labels := by
      have ha : raw33793step0 = (fun i j => raw33793 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33793step0 raw33793; decide +kernel
      have hl : raw33793step0Labels = raw33793Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33793 raw33793Labels permutation170 permutation7
    mixedMoment B raw33793step0 raw33793step0Labels = mixedMoment B raw33793step1 raw33793step1Labels := by
      have ha : raw33793step1 = -raw33793step0 := by apply Matrix.ext; change ∀ i j, raw33793step1 i j = -(raw33793step0 i j); unfold raw33793step1 raw33793step0; decide +kernel
      have hl : raw33793step1Labels = raw33793step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33793step1 raw33793step1Labels = mixedMoment B raw33793step2 raw33793step2Labels := by
      have ha : raw33793step2 = raw33793step1 := by apply Matrix.ext; unfold raw33793step2 raw33793step1; decide +kernel
      have hl : raw33793step1Labels = labelEmbedding10 ∘ raw33793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33793step1 raw33793step1Labels raw33793step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical33794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33794 raw33794Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw33794 raw33794Labels = mixedMoment B raw33794step0 raw33794step0Labels := by
      have ha : raw33794step0 = (fun i j => raw33794 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33794step0 raw33794; decide +kernel
      have hl : raw33794step0Labels = raw33794Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33794 raw33794Labels permutation171 permutation7
    mixedMoment B raw33794step0 raw33794step0Labels = mixedMoment B raw33794step1 raw33794step1Labels := by
      have ha : raw33794step1 = -raw33794step0 := by apply Matrix.ext; change ∀ i j, raw33794step1 i j = -(raw33794step0 i j); unfold raw33794step1 raw33794step0; decide +kernel
      have hl : raw33794step1Labels = raw33794step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33794step1 raw33794step1Labels = mixedMoment B raw33794step2 raw33794step2Labels := by
      have ha : raw33794step2 = raw33794step1 := by apply Matrix.ext; unfold raw33794step2 raw33794step1; decide +kernel
      have hl : raw33794step1Labels = labelEmbedding10 ∘ raw33794step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33794step1 raw33794step1Labels raw33794step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical33795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33795 raw33795Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw33795 raw33795Labels = mixedMoment B raw33795step0 raw33795step0Labels := by
      have ha : raw33795step0 = (fun i j => raw33795 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33795step0 raw33795; decide +kernel
      have hl : raw33795step0Labels = raw33795Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33795 raw33795Labels permutation170 permutation7
    mixedMoment B raw33795step0 raw33795step0Labels = mixedMoment B raw33795step1 raw33795step1Labels := by
      have ha : raw33795step1 = -raw33795step0 := by apply Matrix.ext; change ∀ i j, raw33795step1 i j = -(raw33795step0 i j); unfold raw33795step1 raw33795step0; decide +kernel
      have hl : raw33795step1Labels = raw33795step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33795step1 raw33795step1Labels = mixedMoment B raw33795step2 raw33795step2Labels := by
      have ha : raw33795step2 = raw33795step1 := by apply Matrix.ext; unfold raw33795step2 raw33795step1; decide +kernel
      have hl : raw33795step1Labels = labelEmbedding10 ∘ raw33795step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33795step1 raw33795step1Labels raw33795step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical33796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33796 raw33796Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw33796 raw33796Labels = mixedMoment B raw33796step0 raw33796step0Labels := by
      have hz : ∀ j, raw33796 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33796step0 = (fun i j => raw33796 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33796step0 raw33796; decide +kernel
      have hl : raw33796step0Labels = raw33796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33796 raw33796Labels permutation265 hz
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical33797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33797 raw33797Labels = mixedMoment B node4685 node4685Labels := by
  calc
    _ = mixedMoment B node4685 node4685Labels := by rfl

theorem canonical33798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33798 raw33798Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw33798 raw33798Labels = mixedMoment B raw33798step0 raw33798step0Labels := by
      have ha : raw33798step0 = (fun i j => raw33798 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33798step0 raw33798; decide +kernel
      have hl : raw33798step0Labels = raw33798Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33798 raw33798Labels permutation158 permutation2
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical33799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33799 raw33799Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw33799 raw33799Labels = mixedMoment B raw33799step0 raw33799step0Labels := by
      have ha : raw33799step0 = (fun i j => raw33799 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33799step0 raw33799; decide +kernel
      have hl : raw33799step0Labels = raw33799Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33799 raw33799Labels permutation164 permutation2
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical33800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33800 raw33800Labels = mixedMoment B node4332 node4332Labels := by
  calc
    mixedMoment B raw33800 raw33800Labels = mixedMoment B raw33800step0 raw33800step0Labels := by
      have ha : raw33800step0 = (fun i j => raw33800 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33800step0 raw33800; decide +kernel
      have hl : raw33800step0Labels = raw33800Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33800 raw33800Labels permutation155 permutation2
    _ = mixedMoment B node4332 node4332Labels := by rfl

theorem canonical33801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33801 raw33801Labels = mixedMoment B node4668 node4668Labels := by
  calc
    mixedMoment B raw33801 raw33801Labels = mixedMoment B raw33801step0 raw33801step0Labels := by
      have ha : raw33801step0 = (fun i j => raw33801 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33801step0 raw33801; decide +kernel
      have hl : raw33801step0Labels = raw33801Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33801 raw33801Labels permutation155 permutation2
    _ = mixedMoment B node4668 node4668Labels := by rfl

theorem canonical33802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33802 raw33802Labels = mixedMoment B node4775 node4775Labels := by
  calc
    mixedMoment B raw33802 raw33802Labels = mixedMoment B raw33802step0 raw33802step0Labels := by
      have ha : raw33802step0 = (fun i j => raw33802 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33802step0 raw33802; decide +kernel
      have hl : raw33802step0Labels = raw33802Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33802 raw33802Labels permutation155 permutation2
    _ = mixedMoment B node4775 node4775Labels := by rfl

theorem canonical33803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33803 raw33803Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw33803 raw33803Labels = mixedMoment B raw33803step0 raw33803step0Labels := by
      have ha : raw33803step0 = (fun i j => raw33803 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33803step0 raw33803; decide +kernel
      have hl : raw33803step0Labels = raw33803Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33803 raw33803Labels permutation155 permutation2
    _ = mixedMoment B node4795 node4795Labels := by rfl

theorem canonical33804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33804 raw33804Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw33804 raw33804Labels = mixedMoment B raw33804step0 raw33804step0Labels := by
      have ha : raw33804step0 = (fun i j => raw33804 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33804step0 raw33804; decide +kernel
      have hl : raw33804step0Labels = raw33804Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33804 raw33804Labels permutation157 permutation2
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical33805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33805 raw33805Labels = mixedMoment B node4332 node4332Labels := by
  calc
    mixedMoment B raw33805 raw33805Labels = mixedMoment B raw33805step0 raw33805step0Labels := by
      have ha : raw33805step0 = (fun i j => raw33805 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33805step0 raw33805; decide +kernel
      have hl : raw33805step0Labels = raw33805Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33805 raw33805Labels permutation153 permutation2
    _ = mixedMoment B node4332 node4332Labels := by rfl

theorem canonical33806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33806 raw33806Labels = mixedMoment B node4668 node4668Labels := by
  calc
    mixedMoment B raw33806 raw33806Labels = mixedMoment B raw33806step0 raw33806step0Labels := by
      have ha : raw33806step0 = (fun i j => raw33806 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33806step0 raw33806; decide +kernel
      have hl : raw33806step0Labels = raw33806Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33806 raw33806Labels permutation153 permutation2
    _ = mixedMoment B node4668 node4668Labels := by rfl

theorem canonical33807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33807 raw33807Labels = mixedMoment B node4775 node4775Labels := by
  calc
    mixedMoment B raw33807 raw33807Labels = mixedMoment B raw33807step0 raw33807step0Labels := by
      have ha : raw33807step0 = (fun i j => raw33807 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33807step0 raw33807; decide +kernel
      have hl : raw33807step0Labels = raw33807Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33807 raw33807Labels permutation153 permutation2
    _ = mixedMoment B node4775 node4775Labels := by rfl

theorem canonical33808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33808 raw33808Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw33808 raw33808Labels = mixedMoment B raw33808step0 raw33808step0Labels := by
      have ha : raw33808step0 = (fun i j => raw33808 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33808step0 raw33808; decide +kernel
      have hl : raw33808step0Labels = raw33808Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33808 raw33808Labels permutation153 permutation2
    _ = mixedMoment B node4795 node4795Labels := by rfl

theorem canonical33809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33809 raw33809Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw33809 raw33809Labels = mixedMoment B raw33809step0 raw33809step0Labels := by
      have ha : raw33809step0 = (fun i j => raw33809 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33809step0 raw33809; decide +kernel
      have hl : raw33809step0Labels = raw33809Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33809 raw33809Labels permutation156 permutation2
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical33810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33810 raw33810Labels = mixedMoment B node4331 node4331Labels := by
  calc
    _ = mixedMoment B node4331 node4331Labels := by rfl

theorem canonical33811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33811 raw33811Labels = mixedMoment B node4667 node4667Labels := by
  calc
    _ = mixedMoment B node4667 node4667Labels := by rfl

theorem canonical33812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33812 raw33812Labels = mixedMoment B node4765 node4765Labels := by
  calc
    mixedMoment B raw33812 raw33812Labels = mixedMoment B raw33812step0 raw33812step0Labels := by
      have ha : raw33812step0 = (fun i j => raw33812 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33812step0 raw33812; decide +kernel
      have hl : raw33812step0Labels = raw33812Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33812 raw33812Labels permutation662 permutation3
    mixedMoment B raw33812step0 raw33812step0Labels = mixedMoment B raw33812step1 raw33812step1Labels := by
      have ha : raw33812step1 = -raw33812step0 := by apply Matrix.ext; change ∀ i j, raw33812step1 i j = -(raw33812step0 i j); unfold raw33812step1 raw33812step0; decide +kernel
      have hl : raw33812step1Labels = raw33812step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33812step1 raw33812step1Labels = mixedMoment B raw33812step2 raw33812step2Labels := by
      have ha : raw33812step2 = raw33812step1 := by apply Matrix.ext; unfold raw33812step2 raw33812step1; decide +kernel
      have hl : raw33812step1Labels = labelEmbedding6 ∘ raw33812step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33812step1 raw33812step1Labels raw33812step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4765 node4765Labels := by rfl

theorem canonical33813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33813 raw33813Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw33813 raw33813Labels = mixedMoment B raw33813step0 raw33813step0Labels := by
      have ha : raw33813step0 = (fun i j => raw33813 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33813step0 raw33813; decide +kernel
      have hl : raw33813step0Labels = raw33813Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33813 raw33813Labels permutation170 permutation7
    mixedMoment B raw33813step0 raw33813step0Labels = mixedMoment B raw33813step1 raw33813step1Labels := by
      have ha : raw33813step1 = -raw33813step0 := by apply Matrix.ext; change ∀ i j, raw33813step1 i j = -(raw33813step0 i j); unfold raw33813step1 raw33813step0; decide +kernel
      have hl : raw33813step1Labels = raw33813step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33813step1 raw33813step1Labels = mixedMoment B raw33813step2 raw33813step2Labels := by
      have ha : raw33813step2 = raw33813step1 := by apply Matrix.ext; unfold raw33813step2 raw33813step1; decide +kernel
      have hl : raw33813step1Labels = labelEmbedding1 ∘ raw33813step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33813step1 raw33813step1Labels raw33813step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2676 node2676Labels := by rfl

theorem canonical33814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33814 raw33814Labels = mixedMoment B node2728 node2728Labels := by
  calc
    mixedMoment B raw33814 raw33814Labels = mixedMoment B raw33814step0 raw33814step0Labels := by
      have ha : raw33814step0 = (fun i j => raw33814 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33814step0 raw33814; decide +kernel
      have hl : raw33814step0Labels = raw33814Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33814 raw33814Labels permutation170 permutation7
    mixedMoment B raw33814step0 raw33814step0Labels = mixedMoment B raw33814step1 raw33814step1Labels := by
      have ha : raw33814step1 = -raw33814step0 := by apply Matrix.ext; change ∀ i j, raw33814step1 i j = -(raw33814step0 i j); unfold raw33814step1 raw33814step0; decide +kernel
      have hl : raw33814step1Labels = raw33814step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33814step1 raw33814step1Labels = mixedMoment B raw33814step2 raw33814step2Labels := by
      have ha : raw33814step2 = raw33814step1 := by apply Matrix.ext; unfold raw33814step2 raw33814step1; decide +kernel
      have hl : raw33814step1Labels = labelEmbedding1 ∘ raw33814step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33814step1 raw33814step1Labels raw33814step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2728 node2728Labels := by rfl

theorem canonical33815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33815 raw33815Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw33815 raw33815Labels = mixedMoment B raw33815step0 raw33815step0Labels := by
      have ha : raw33815step0 = (fun i j => raw33815 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33815step0 raw33815; decide +kernel
      have hl : raw33815step0Labels = raw33815Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33815 raw33815Labels permutation170 permutation7
    mixedMoment B raw33815step0 raw33815step0Labels = mixedMoment B raw33815step1 raw33815step1Labels := by
      have ha : raw33815step1 = -raw33815step0 := by apply Matrix.ext; change ∀ i j, raw33815step1 i j = -(raw33815step0 i j); unfold raw33815step1 raw33815step0; decide +kernel
      have hl : raw33815step1Labels = raw33815step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33815step1 raw33815step1Labels = mixedMoment B raw33815step2 raw33815step2Labels := by
      have ha : raw33815step2 = raw33815step1 := by apply Matrix.ext; unfold raw33815step2 raw33815step1; decide +kernel
      have hl : raw33815step1Labels = labelEmbedding1 ∘ raw33815step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33815step1 raw33815step1Labels raw33815step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2730 node2730Labels := by rfl

theorem canonical33816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33816 raw33816Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw33816 raw33816Labels = mixedMoment B raw33816step0 raw33816step0Labels := by
      have ha : raw33816step0 = (fun i j => raw33816 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33816step0 raw33816; decide +kernel
      have hl : raw33816step0Labels = raw33816Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33816 raw33816Labels permutation171 permutation7
    mixedMoment B raw33816step0 raw33816step0Labels = mixedMoment B raw33816step1 raw33816step1Labels := by
      have ha : raw33816step1 = -raw33816step0 := by apply Matrix.ext; change ∀ i j, raw33816step1 i j = -(raw33816step0 i j); unfold raw33816step1 raw33816step0; decide +kernel
      have hl : raw33816step1Labels = raw33816step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33816step1 raw33816step1Labels = mixedMoment B raw33816step2 raw33816step2Labels := by
      have ha : raw33816step2 = raw33816step1 := by apply Matrix.ext; unfold raw33816step2 raw33816step1; decide +kernel
      have hl : raw33816step1Labels = labelEmbedding1 ∘ raw33816step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33816step1 raw33816step1Labels raw33816step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2730 node2730Labels := by rfl

theorem canonical33817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33817 raw33817Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw33817 raw33817Labels = mixedMoment B raw33817step0 raw33817step0Labels := by
      have ha : raw33817step0 = (fun i j => raw33817 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33817step0 raw33817; decide +kernel
      have hl : raw33817step0Labels = raw33817Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33817 raw33817Labels permutation170 permutation7
    mixedMoment B raw33817step0 raw33817step0Labels = mixedMoment B raw33817step1 raw33817step1Labels := by
      have ha : raw33817step1 = -raw33817step0 := by apply Matrix.ext; change ∀ i j, raw33817step1 i j = -(raw33817step0 i j); unfold raw33817step1 raw33817step0; decide +kernel
      have hl : raw33817step1Labels = raw33817step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33817step1 raw33817step1Labels = mixedMoment B raw33817step2 raw33817step2Labels := by
      have ha : raw33817step2 = raw33817step1 := by apply Matrix.ext; unfold raw33817step2 raw33817step1; decide +kernel
      have hl : raw33817step1Labels = labelEmbedding1 ∘ raw33817step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33817step1 raw33817step1Labels raw33817step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical33818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33818 raw33818Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw33818 raw33818Labels = mixedMoment B raw33818step0 raw33818step0Labels := by
      have hz : ∀ j, raw33818 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33818step0 = (fun i j => raw33818 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33818step0 raw33818; decide +kernel
      have hl : raw33818step0Labels = raw33818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33818 raw33818Labels permutation265 hz
    mixedMoment B raw33818step0 raw33818step0Labels = mixedMoment B raw33818step1 raw33818step1Labels := by
      have ha : raw33818step1 = (fun i j => raw33818step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33818step1 raw33818step0; decide +kernel
      have hl : raw33818step1Labels = raw33818step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33818step0 raw33818step0Labels permutation50 permutation7
    mixedMoment B raw33818step1 raw33818step1Labels = mixedMoment B raw33818step2 raw33818step2Labels := by
      have ha : raw33818step2 = -raw33818step1 := by apply Matrix.ext; change ∀ i j, raw33818step2 i j = -(raw33818step1 i j); unfold raw33818step2 raw33818step1; decide +kernel
      have hl : raw33818step2Labels = raw33818step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33818step2 raw33818step2Labels = mixedMoment B raw33818step3 raw33818step3Labels := by
      have ha : raw33818step3 = raw33818step2 := by apply Matrix.ext; unfold raw33818step3 raw33818step2; decide +kernel
      have hl : raw33818step2Labels = labelEmbedding1 ∘ raw33818step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33818step2 raw33818step2Labels raw33818step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

theorem canonical33819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33819 raw33819Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw33819 raw33819Labels = mixedMoment B raw33819step0 raw33819step0Labels := by
      have hz : ∀ j, raw33819 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33819step0 = (fun i j => raw33819 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33819step0 raw33819; decide +kernel
      have hl : raw33819step0Labels = raw33819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33819 raw33819Labels permutation265 hz
    mixedMoment B raw33819step0 raw33819step0Labels = mixedMoment B raw33819step1 raw33819step1Labels := by
      have ha : raw33819step1 = (fun i j => raw33819step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33819step1 raw33819step0; decide +kernel
      have hl : raw33819step1Labels = raw33819step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33819step0 raw33819step0Labels permutation50 permutation7
    mixedMoment B raw33819step1 raw33819step1Labels = mixedMoment B raw33819step2 raw33819step2Labels := by
      have ha : raw33819step2 = -raw33819step1 := by apply Matrix.ext; change ∀ i j, raw33819step2 i j = -(raw33819step1 i j); unfold raw33819step2 raw33819step1; decide +kernel
      have hl : raw33819step2Labels = raw33819step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33819step2 raw33819step2Labels = mixedMoment B raw33819step3 raw33819step3Labels := by
      have ha : raw33819step3 = raw33819step2 := by apply Matrix.ext; unfold raw33819step3 raw33819step2; decide +kernel
      have hl : raw33819step2Labels = labelEmbedding1 ∘ raw33819step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33819step2 raw33819step2Labels raw33819step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2275 node2275Labels := by rfl

theorem canonical33820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33820 raw33820Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw33820 raw33820Labels = mixedMoment B raw33820step0 raw33820step0Labels := by
      have hz : ∀ j, raw33820 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33820step0 = (fun i j => raw33820 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33820step0 raw33820; decide +kernel
      have hl : raw33820step0Labels = raw33820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33820 raw33820Labels permutation265 hz
    mixedMoment B raw33820step0 raw33820step0Labels = mixedMoment B raw33820step1 raw33820step1Labels := by
      have ha : raw33820step1 = (fun i j => raw33820step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33820step1 raw33820step0; decide +kernel
      have hl : raw33820step1Labels = raw33820step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33820step0 raw33820step0Labels permutation50 permutation7
    mixedMoment B raw33820step1 raw33820step1Labels = mixedMoment B raw33820step2 raw33820step2Labels := by
      have ha : raw33820step2 = -raw33820step1 := by apply Matrix.ext; change ∀ i j, raw33820step2 i j = -(raw33820step1 i j); unfold raw33820step2 raw33820step1; decide +kernel
      have hl : raw33820step2Labels = raw33820step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33820step2 raw33820step2Labels = mixedMoment B raw33820step3 raw33820step3Labels := by
      have ha : raw33820step3 = raw33820step2 := by apply Matrix.ext; unfold raw33820step3 raw33820step2; decide +kernel
      have hl : raw33820step2Labels = labelEmbedding1 ∘ raw33820step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33820step2 raw33820step2Labels raw33820step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

theorem canonical33821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33821 raw33821Labels = mixedMoment B node1680 node1680Labels := by
  calc
    mixedMoment B raw33821 raw33821Labels = mixedMoment B raw33821step0 raw33821step0Labels := by
      have ha : raw33821step0 = (fun i j => raw33821 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33821step0 raw33821; decide +kernel
      have hl : raw33821step0Labels = raw33821Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33821 raw33821Labels permutation170 permutation7
    mixedMoment B raw33821step0 raw33821step0Labels = mixedMoment B raw33821step1 raw33821step1Labels := by
      have ha : raw33821step1 = -raw33821step0 := by apply Matrix.ext; change ∀ i j, raw33821step1 i j = -(raw33821step0 i j); unfold raw33821step1 raw33821step0; decide +kernel
      have hl : raw33821step1Labels = raw33821step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33821step1 raw33821step1Labels = mixedMoment B raw33821step2 raw33821step2Labels := by
      have ha : raw33821step2 = raw33821step1 := by apply Matrix.ext; unfold raw33821step2 raw33821step1; decide +kernel
      have hl : raw33821step1Labels = labelEmbedding1 ∘ raw33821step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33821step1 raw33821step1Labels raw33821step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1680 node1680Labels := by rfl

theorem canonical33822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33822 raw33822Labels = mixedMoment B node2156 node2156Labels := by
  calc
    mixedMoment B raw33822 raw33822Labels = mixedMoment B raw33822step0 raw33822step0Labels := by
      have ha : raw33822step0 = (fun i j => raw33822 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33822step0 raw33822; decide +kernel
      have hl : raw33822step0Labels = raw33822Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33822 raw33822Labels permutation170 permutation7
    mixedMoment B raw33822step0 raw33822step0Labels = mixedMoment B raw33822step1 raw33822step1Labels := by
      have ha : raw33822step1 = -raw33822step0 := by apply Matrix.ext; change ∀ i j, raw33822step1 i j = -(raw33822step0 i j); unfold raw33822step1 raw33822step0; decide +kernel
      have hl : raw33822step1Labels = raw33822step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33822step1 raw33822step1Labels = mixedMoment B raw33822step2 raw33822step2Labels := by
      have ha : raw33822step2 = raw33822step1 := by apply Matrix.ext; unfold raw33822step2 raw33822step1; decide +kernel
      have hl : raw33822step1Labels = labelEmbedding1 ∘ raw33822step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33822step1 raw33822step1Labels raw33822step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2156 node2156Labels := by rfl

theorem canonical33823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33823 raw33823Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw33823 raw33823Labels = mixedMoment B raw33823step0 raw33823step0Labels := by
      have ha : raw33823step0 = (fun i j => raw33823 (permutation172 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33823step0 raw33823; decide +kernel
      have hl : raw33823step0Labels = raw33823Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33823 raw33823Labels permutation172 permutation7
    mixedMoment B raw33823step0 raw33823step0Labels = mixedMoment B raw33823step1 raw33823step1Labels := by
      have ha : raw33823step1 = -raw33823step0 := by apply Matrix.ext; change ∀ i j, raw33823step1 i j = -(raw33823step0 i j); unfold raw33823step1 raw33823step0; decide +kernel
      have hl : raw33823step1Labels = raw33823step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33823step1 raw33823step1Labels = mixedMoment B raw33823step2 raw33823step2Labels := by
      have ha : raw33823step2 = raw33823step1 := by apply Matrix.ext; unfold raw33823step2 raw33823step1; decide +kernel
      have hl : raw33823step1Labels = labelEmbedding1 ∘ raw33823step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33823step1 raw33823step1Labels raw33823step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2214 node2214Labels := by rfl

theorem canonical33824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33824 raw33824Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw33824 raw33824Labels = mixedMoment B raw33824step0 raw33824step0Labels := by
      have ha : raw33824step0 = (fun i j => raw33824 (permutation174 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33824step0 raw33824; decide +kernel
      have hl : raw33824step0Labels = raw33824Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33824 raw33824Labels permutation174 permutation7
    mixedMoment B raw33824step0 raw33824step0Labels = mixedMoment B raw33824step1 raw33824step1Labels := by
      have ha : raw33824step1 = -raw33824step0 := by apply Matrix.ext; change ∀ i j, raw33824step1 i j = -(raw33824step0 i j); unfold raw33824step1 raw33824step0; decide +kernel
      have hl : raw33824step1Labels = raw33824step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33824step1 raw33824step1Labels = mixedMoment B raw33824step2 raw33824step2Labels := by
      have ha : raw33824step2 = raw33824step1 := by apply Matrix.ext; unfold raw33824step2 raw33824step1; decide +kernel
      have hl : raw33824step1Labels = labelEmbedding1 ∘ raw33824step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33824step1 raw33824step1Labels raw33824step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2214 node2214Labels := by rfl

theorem canonical33825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33825 raw33825Labels = mixedMoment B node2204 node2204Labels := by
  calc
    mixedMoment B raw33825 raw33825Labels = mixedMoment B raw33825step0 raw33825step0Labels := by
      have ha : raw33825step0 = (fun i j => raw33825 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33825step0 raw33825; decide +kernel
      have hl : raw33825step0Labels = raw33825Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33825 raw33825Labels permutation170 permutation7
    mixedMoment B raw33825step0 raw33825step0Labels = mixedMoment B raw33825step1 raw33825step1Labels := by
      have ha : raw33825step1 = -raw33825step0 := by apply Matrix.ext; change ∀ i j, raw33825step1 i j = -(raw33825step0 i j); unfold raw33825step1 raw33825step0; decide +kernel
      have hl : raw33825step1Labels = raw33825step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33825step1 raw33825step1Labels = mixedMoment B raw33825step2 raw33825step2Labels := by
      have ha : raw33825step2 = raw33825step1 := by apply Matrix.ext; unfold raw33825step2 raw33825step1; decide +kernel
      have hl : raw33825step1Labels = labelEmbedding1 ∘ raw33825step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33825step1 raw33825step1Labels raw33825step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2204 node2204Labels := by rfl

theorem canonical33826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33826 raw33826Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw33826 raw33826Labels = mixedMoment B raw33826step0 raw33826step0Labels := by
      have ha : raw33826step0 = (fun i j => raw33826 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33826step0 raw33826; decide +kernel
      have hl : raw33826step0Labels = raw33826Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33826 raw33826Labels permutation171 permutation7
    mixedMoment B raw33826step0 raw33826step0Labels = mixedMoment B raw33826step1 raw33826step1Labels := by
      have ha : raw33826step1 = -raw33826step0 := by apply Matrix.ext; change ∀ i j, raw33826step1 i j = -(raw33826step0 i j); unfold raw33826step1 raw33826step0; decide +kernel
      have hl : raw33826step1Labels = raw33826step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33826step1 raw33826step1Labels = mixedMoment B raw33826step2 raw33826step2Labels := by
      have ha : raw33826step2 = raw33826step1 := by apply Matrix.ext; unfold raw33826step2 raw33826step1; decide +kernel
      have hl : raw33826step1Labels = labelEmbedding1 ∘ raw33826step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33826step1 raw33826step1Labels raw33826step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1678 node1678Labels := by rfl

theorem canonical33827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33827 raw33827Labels = mixedMoment B node2154 node2154Labels := by
  calc
    mixedMoment B raw33827 raw33827Labels = mixedMoment B raw33827step0 raw33827step0Labels := by
      have ha : raw33827step0 = (fun i j => raw33827 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33827step0 raw33827; decide +kernel
      have hl : raw33827step0Labels = raw33827Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33827 raw33827Labels permutation171 permutation7
    mixedMoment B raw33827step0 raw33827step0Labels = mixedMoment B raw33827step1 raw33827step1Labels := by
      have ha : raw33827step1 = -raw33827step0 := by apply Matrix.ext; change ∀ i j, raw33827step1 i j = -(raw33827step0 i j); unfold raw33827step1 raw33827step0; decide +kernel
      have hl : raw33827step1Labels = raw33827step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33827step1 raw33827step1Labels = mixedMoment B raw33827step2 raw33827step2Labels := by
      have ha : raw33827step2 = raw33827step1 := by apply Matrix.ext; unfold raw33827step2 raw33827step1; decide +kernel
      have hl : raw33827step1Labels = labelEmbedding1 ∘ raw33827step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33827step1 raw33827step1Labels raw33827step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2154 node2154Labels := by rfl

theorem canonical33828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33828 raw33828Labels = mixedMoment B node2211 node2211Labels := by
  calc
    mixedMoment B raw33828 raw33828Labels = mixedMoment B raw33828step0 raw33828step0Labels := by
      have ha : raw33828step0 = (fun i j => raw33828 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33828step0 raw33828; decide +kernel
      have hl : raw33828step0Labels = raw33828Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33828 raw33828Labels permutation171 permutation7
    mixedMoment B raw33828step0 raw33828step0Labels = mixedMoment B raw33828step1 raw33828step1Labels := by
      have ha : raw33828step1 = -raw33828step0 := by apply Matrix.ext; change ∀ i j, raw33828step1 i j = -(raw33828step0 i j); unfold raw33828step1 raw33828step0; decide +kernel
      have hl : raw33828step1Labels = raw33828step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33828step1 raw33828step1Labels = mixedMoment B raw33828step2 raw33828step2Labels := by
      have ha : raw33828step2 = raw33828step1 := by apply Matrix.ext; unfold raw33828step2 raw33828step1; decide +kernel
      have hl : raw33828step1Labels = labelEmbedding1 ∘ raw33828step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33828step1 raw33828step1Labels raw33828step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2211 node2211Labels := by rfl

theorem canonical33829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33829 raw33829Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw33829 raw33829Labels = mixedMoment B raw33829step0 raw33829step0Labels := by
      have ha : raw33829step0 = (fun i j => raw33829 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33829step0 raw33829; decide +kernel
      have hl : raw33829step0Labels = raw33829Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33829 raw33829Labels permutation171 permutation7
    mixedMoment B raw33829step0 raw33829step0Labels = mixedMoment B raw33829step1 raw33829step1Labels := by
      have ha : raw33829step1 = -raw33829step0 := by apply Matrix.ext; change ∀ i j, raw33829step1 i j = -(raw33829step0 i j); unfold raw33829step1 raw33829step0; decide +kernel
      have hl : raw33829step1Labels = raw33829step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33829step1 raw33829step1Labels = mixedMoment B raw33829step2 raw33829step2Labels := by
      have ha : raw33829step2 = raw33829step1 := by apply Matrix.ext; unfold raw33829step2 raw33829step1; decide +kernel
      have hl : raw33829step1Labels = labelEmbedding1 ∘ raw33829step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33829step1 raw33829step1Labels raw33829step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

theorem canonical33830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33830 raw33830Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw33830 raw33830Labels = mixedMoment B raw33830step0 raw33830step0Labels := by
      have ha : raw33830step0 = (fun i j => raw33830 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33830step0 raw33830; decide +kernel
      have hl : raw33830step0Labels = raw33830Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33830 raw33830Labels permutation171 permutation7
    mixedMoment B raw33830step0 raw33830step0Labels = mixedMoment B raw33830step1 raw33830step1Labels := by
      have ha : raw33830step1 = -raw33830step0 := by apply Matrix.ext; change ∀ i j, raw33830step1 i j = -(raw33830step0 i j); unfold raw33830step1 raw33830step0; decide +kernel
      have hl : raw33830step1Labels = raw33830step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33830step1 raw33830step1Labels = mixedMoment B raw33830step2 raw33830step2Labels := by
      have ha : raw33830step2 = raw33830step1 := by apply Matrix.ext; unfold raw33830step2 raw33830step1; decide +kernel
      have hl : raw33830step1Labels = labelEmbedding1 ∘ raw33830step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33830step1 raw33830step1Labels raw33830step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

theorem canonical33831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33831 raw33831Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw33831 raw33831Labels = mixedMoment B raw33831step0 raw33831step0Labels := by
      have ha : raw33831step0 = (fun i j => raw33831 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33831step0 raw33831; decide +kernel
      have hl : raw33831step0Labels = raw33831Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33831 raw33831Labels permutation170 permutation7
    mixedMoment B raw33831step0 raw33831step0Labels = mixedMoment B raw33831step1 raw33831step1Labels := by
      have ha : raw33831step1 = -raw33831step0 := by apply Matrix.ext; change ∀ i j, raw33831step1 i j = -(raw33831step0 i j); unfold raw33831step1 raw33831step0; decide +kernel
      have hl : raw33831step1Labels = raw33831step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33831step1 raw33831step1Labels = mixedMoment B raw33831step2 raw33831step2Labels := by
      have ha : raw33831step2 = raw33831step1 := by apply Matrix.ext; unfold raw33831step2 raw33831step1; decide +kernel
      have hl : raw33831step1Labels = labelEmbedding1 ∘ raw33831step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33831step1 raw33831step1Labels raw33831step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1678 node1678Labels := by rfl

theorem canonical33832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33832 raw33832Labels = mixedMoment B node2154 node2154Labels := by
  calc
    mixedMoment B raw33832 raw33832Labels = mixedMoment B raw33832step0 raw33832step0Labels := by
      have ha : raw33832step0 = (fun i j => raw33832 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33832step0 raw33832; decide +kernel
      have hl : raw33832step0Labels = raw33832Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33832 raw33832Labels permutation170 permutation7
    mixedMoment B raw33832step0 raw33832step0Labels = mixedMoment B raw33832step1 raw33832step1Labels := by
      have ha : raw33832step1 = -raw33832step0 := by apply Matrix.ext; change ∀ i j, raw33832step1 i j = -(raw33832step0 i j); unfold raw33832step1 raw33832step0; decide +kernel
      have hl : raw33832step1Labels = raw33832step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33832step1 raw33832step1Labels = mixedMoment B raw33832step2 raw33832step2Labels := by
      have ha : raw33832step2 = raw33832step1 := by apply Matrix.ext; unfold raw33832step2 raw33832step1; decide +kernel
      have hl : raw33832step1Labels = labelEmbedding1 ∘ raw33832step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33832step1 raw33832step1Labels raw33832step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2154 node2154Labels := by rfl

theorem canonical33833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33833 raw33833Labels = mixedMoment B node2211 node2211Labels := by
  calc
    mixedMoment B raw33833 raw33833Labels = mixedMoment B raw33833step0 raw33833step0Labels := by
      have ha : raw33833step0 = (fun i j => raw33833 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33833step0 raw33833; decide +kernel
      have hl : raw33833step0Labels = raw33833Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33833 raw33833Labels permutation170 permutation7
    mixedMoment B raw33833step0 raw33833step0Labels = mixedMoment B raw33833step1 raw33833step1Labels := by
      have ha : raw33833step1 = -raw33833step0 := by apply Matrix.ext; change ∀ i j, raw33833step1 i j = -(raw33833step0 i j); unfold raw33833step1 raw33833step0; decide +kernel
      have hl : raw33833step1Labels = raw33833step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33833step1 raw33833step1Labels = mixedMoment B raw33833step2 raw33833step2Labels := by
      have ha : raw33833step2 = raw33833step1 := by apply Matrix.ext; unfold raw33833step2 raw33833step1; decide +kernel
      have hl : raw33833step1Labels = labelEmbedding1 ∘ raw33833step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33833step1 raw33833step1Labels raw33833step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2211 node2211Labels := by rfl

theorem canonical33834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33834 raw33834Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw33834 raw33834Labels = mixedMoment B raw33834step0 raw33834step0Labels := by
      have ha : raw33834step0 = (fun i j => raw33834 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33834step0 raw33834; decide +kernel
      have hl : raw33834step0Labels = raw33834Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33834 raw33834Labels permutation170 permutation7
    mixedMoment B raw33834step0 raw33834step0Labels = mixedMoment B raw33834step1 raw33834step1Labels := by
      have ha : raw33834step1 = -raw33834step0 := by apply Matrix.ext; change ∀ i j, raw33834step1 i j = -(raw33834step0 i j); unfold raw33834step1 raw33834step0; decide +kernel
      have hl : raw33834step1Labels = raw33834step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33834step1 raw33834step1Labels = mixedMoment B raw33834step2 raw33834step2Labels := by
      have ha : raw33834step2 = raw33834step1 := by apply Matrix.ext; unfold raw33834step2 raw33834step1; decide +kernel
      have hl : raw33834step1Labels = labelEmbedding1 ∘ raw33834step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33834step1 raw33834step1Labels raw33834step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

theorem canonical33835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33835 raw33835Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw33835 raw33835Labels = mixedMoment B raw33835step0 raw33835step0Labels := by
      have ha : raw33835step0 = (fun i j => raw33835 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33835step0 raw33835; decide +kernel
      have hl : raw33835step0Labels = raw33835Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33835 raw33835Labels permutation170 permutation7
    mixedMoment B raw33835step0 raw33835step0Labels = mixedMoment B raw33835step1 raw33835step1Labels := by
      have ha : raw33835step1 = -raw33835step0 := by apply Matrix.ext; change ∀ i j, raw33835step1 i j = -(raw33835step0 i j); unfold raw33835step1 raw33835step0; decide +kernel
      have hl : raw33835step1Labels = raw33835step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33835step1 raw33835step1Labels = mixedMoment B raw33835step2 raw33835step2Labels := by
      have ha : raw33835step2 = raw33835step1 := by apply Matrix.ext; unfold raw33835step2 raw33835step1; decide +kernel
      have hl : raw33835step1Labels = labelEmbedding1 ∘ raw33835step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33835step1 raw33835step1Labels raw33835step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

theorem canonical33836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33836 raw33836Labels = mixedMoment B node1684 node1684Labels := by
  calc
    mixedMoment B raw33836 raw33836Labels = mixedMoment B raw33836step0 raw33836step0Labels := by
      have ha : raw33836step0 = (fun i j => raw33836 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33836step0 raw33836; decide +kernel
      have hl : raw33836step0Labels = raw33836Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33836 raw33836Labels permutation170 permutation7
    mixedMoment B raw33836step0 raw33836step0Labels = mixedMoment B raw33836step1 raw33836step1Labels := by
      have ha : raw33836step1 = -raw33836step0 := by apply Matrix.ext; change ∀ i j, raw33836step1 i j = -(raw33836step0 i j); unfold raw33836step1 raw33836step0; decide +kernel
      have hl : raw33836step1Labels = raw33836step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33836step1 raw33836step1Labels = mixedMoment B raw33836step2 raw33836step2Labels := by
      have ha : raw33836step2 = raw33836step1 := by apply Matrix.ext; unfold raw33836step2 raw33836step1; decide +kernel
      have hl : raw33836step1Labels = labelEmbedding1 ∘ raw33836step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33836step1 raw33836step1Labels raw33836step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1684 node1684Labels := by rfl

theorem canonical33837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33837 raw33837Labels = mixedMoment B node2160 node2160Labels := by
  calc
    mixedMoment B raw33837 raw33837Labels = mixedMoment B raw33837step0 raw33837step0Labels := by
      have ha : raw33837step0 = (fun i j => raw33837 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33837step0 raw33837; decide +kernel
      have hl : raw33837step0Labels = raw33837Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33837 raw33837Labels permutation170 permutation7
    mixedMoment B raw33837step0 raw33837step0Labels = mixedMoment B raw33837step1 raw33837step1Labels := by
      have ha : raw33837step1 = -raw33837step0 := by apply Matrix.ext; change ∀ i j, raw33837step1 i j = -(raw33837step0 i j); unfold raw33837step1 raw33837step0; decide +kernel
      have hl : raw33837step1Labels = raw33837step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33837step1 raw33837step1Labels = mixedMoment B raw33837step2 raw33837step2Labels := by
      have ha : raw33837step2 = raw33837step1 := by apply Matrix.ext; unfold raw33837step2 raw33837step1; decide +kernel
      have hl : raw33837step1Labels = labelEmbedding1 ∘ raw33837step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33837step1 raw33837step1Labels raw33837step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2160 node2160Labels := by rfl

theorem canonical33838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33838 raw33838Labels = mixedMoment B node2179 node2179Labels := by
  calc
    mixedMoment B raw33838 raw33838Labels = mixedMoment B raw33838step0 raw33838step0Labels := by
      have ha : raw33838step0 = (fun i j => raw33838 (permutation659 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33838step0 raw33838; decide +kernel
      have hl : raw33838step0Labels = raw33838Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33838 raw33838Labels permutation659 permutation5
    mixedMoment B raw33838step0 raw33838step0Labels = mixedMoment B raw33838step1 raw33838step1Labels := by
      have ha : raw33838step1 = raw33838step0 := by apply Matrix.ext; unfold raw33838step1 raw33838step0; decide +kernel
      have hl : raw33838step0Labels = labelEmbedding1 ∘ raw33838step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33838step0 raw33838step0Labels raw33838step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2179 node2179Labels := by rfl

theorem canonical33839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33839 raw33839Labels = mixedMoment B node3378 node3378Labels := by
  calc
    _ = mixedMoment B node3378 node3378Labels := by rfl

theorem canonical33840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33840 raw33840Labels = mixedMoment B node2023 node2023Labels := by
  calc
    _ = mixedMoment B node2023 node2023Labels := by rfl

theorem canonical33841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33841 raw33841Labels = mixedMoment B node1811 node1811Labels := by
  calc
    _ = mixedMoment B node1811 node1811Labels := by rfl

theorem canonical33842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33842 raw33842Labels = mixedMoment B node1794 node1794Labels := by
  calc
    mixedMoment B raw33842 raw33842Labels = mixedMoment B raw33842step0 raw33842step0Labels := by
      have ha : raw33842step0 = (fun i j => raw33842 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33842step0 raw33842; decide +kernel
      have hl : raw33842step0Labels = raw33842Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33842 raw33842Labels permutation155 permutation2
    _ = mixedMoment B node1794 node1794Labels := by rfl

theorem canonical33843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33843 raw33843Labels = mixedMoment B node1794 node1794Labels := by
  calc
    mixedMoment B raw33843 raw33843Labels = mixedMoment B raw33843step0 raw33843step0Labels := by
      have ha : raw33843step0 = (fun i j => raw33843 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33843step0 raw33843; decide +kernel
      have hl : raw33843step0Labels = raw33843Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33843 raw33843Labels permutation153 permutation2
    _ = mixedMoment B node1794 node1794Labels := by rfl

theorem canonical33844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33844 raw33844Labels = mixedMoment B node1793 node1793Labels := by
  calc
    _ = mixedMoment B node1793 node1793Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3754 raw3754Labels = mixedMoment B node4793 node4793Labels := by
  calc
    mixedMoment B raw3754 raw3754Labels = mixedMoment B raw3754step0 raw3754step0Labels := by
      have ha : raw3754step0 = (fun i j => raw3754 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3754step0 raw3754; decide +kernel
      have hl : raw3754step0Labels = raw3754Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3754 raw3754Labels permutation154 permutation2
    _ = mixedMoment B node4793 node4793Labels := by rfl

theorem canonical3757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3757 raw3757Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw3757 raw3757Labels = mixedMoment B raw3757step0 raw3757step0Labels := by
      have hz : ∀ j, raw3757 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3757step0 = (fun i j => raw3757 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3757step0 raw3757; decide +kernel
      have hl : raw3757step0Labels = raw3757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3757 raw3757Labels permutation265 hz
    mixedMoment B raw3757step0 raw3757step0Labels = mixedMoment B raw3757step1 raw3757step1Labels := by
      have ha : raw3757step1 = (fun i j => raw3757step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3757step1 raw3757step0; decide +kernel
      have hl : raw3757step1Labels = raw3757step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3757step0 raw3757step0Labels permutation34 permutation2
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical3759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3759 raw3759Labels = mixedMoment B node4793 node4793Labels := by
  calc
    _ = mixedMoment B node4793 node4793Labels := by rfl

theorem canonical3762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3762 raw3762Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw3762 raw3762Labels = mixedMoment B raw3762step0 raw3762step0Labels := by
      have hz : ∀ j, raw3762 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3762step0 = (fun i j => raw3762 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3762step0 raw3762; decide +kernel
      have hl : raw3762step0Labels = raw3762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3762 raw3762Labels permutation265 hz
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical3814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3814 raw3814Labels = mixedMoment B node2219 node2219Labels := by
  calc
    mixedMoment B raw3814 raw3814Labels = mixedMoment B raw3814step0 raw3814step0Labels := by
      have ha : raw3814step0 = (fun i j => raw3814 (permutation649 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3814step0 raw3814; decide +kernel
      have hl : raw3814step0Labels = raw3814Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3814 raw3814Labels permutation649 permutation5
    mixedMoment B raw3814step0 raw3814step0Labels = mixedMoment B raw3814step1 raw3814step1Labels := by
      have ha : raw3814step1 = raw3814step0 := by apply Matrix.ext; unfold raw3814step1 raw3814step0; decide +kernel
      have hl : raw3814step0Labels = labelEmbedding1 ∘ raw3814step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3814step0 raw3814step0Labels raw3814step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2219 node2219Labels := by rfl

theorem canonical3817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3817 raw3817Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw3817 raw3817Labels = mixedMoment B raw3817step0 raw3817step0Labels := by
      have hz : ∀ j, raw3817 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3817step0 = (fun i j => raw3817 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3817step0 raw3817; decide +kernel
      have hl : raw3817step0Labels = raw3817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3817 raw3817Labels permutation265 hz
    mixedMoment B raw3817step0 raw3817step0Labels = mixedMoment B raw3817step1 raw3817step1Labels := by
      have ha : raw3817step1 = (fun i j => raw3817step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3817step1 raw3817step0; decide +kernel
      have hl : raw3817step1Labels = raw3817step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3817step0 raw3817step0Labels permutation51 permutation7
    mixedMoment B raw3817step1 raw3817step1Labels = mixedMoment B raw3817step2 raw3817step2Labels := by
      have ha : raw3817step2 = -raw3817step1 := by apply Matrix.ext; change ∀ i j, raw3817step2 i j = -(raw3817step1 i j); unfold raw3817step2 raw3817step1; decide +kernel
      have hl : raw3817step2Labels = raw3817step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3817step2 raw3817step2Labels = mixedMoment B raw3817step3 raw3817step3Labels := by
      have ha : raw3817step3 = raw3817step2 := by apply Matrix.ext; unfold raw3817step3 raw3817step2; decide +kernel
      have hl : raw3817step2Labels = labelEmbedding1 ∘ raw3817step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3817step2 raw3817step2Labels raw3817step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

theorem canonical3819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3819 raw3819Labels = mixedMoment B node2219 node2219Labels := by
  calc
    mixedMoment B raw3819 raw3819Labels = mixedMoment B raw3819step0 raw3819step0Labels := by
      have ha : raw3819step0 = (fun i j => raw3819 (permutation668 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3819step0 raw3819; decide +kernel
      have hl : raw3819step0Labels = raw3819Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3819 raw3819Labels permutation668 permutation5
    mixedMoment B raw3819step0 raw3819step0Labels = mixedMoment B raw3819step1 raw3819step1Labels := by
      have ha : raw3819step1 = raw3819step0 := by apply Matrix.ext; unfold raw3819step1 raw3819step0; decide +kernel
      have hl : raw3819step0Labels = labelEmbedding1 ∘ raw3819step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3819step0 raw3819step0Labels raw3819step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2219 node2219Labels := by rfl

theorem canonical3822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3822 raw3822Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw3822 raw3822Labels = mixedMoment B raw3822step0 raw3822step0Labels := by
      have hz : ∀ j, raw3822 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3822step0 = (fun i j => raw3822 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3822step0 raw3822; decide +kernel
      have hl : raw3822step0Labels = raw3822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3822 raw3822Labels permutation265 hz
    mixedMoment B raw3822step0 raw3822step0Labels = mixedMoment B raw3822step1 raw3822step1Labels := by
      have ha : raw3822step1 = (fun i j => raw3822step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3822step1 raw3822step0; decide +kernel
      have hl : raw3822step1Labels = raw3822step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3822step0 raw3822step0Labels permutation50 permutation7
    mixedMoment B raw3822step1 raw3822step1Labels = mixedMoment B raw3822step2 raw3822step2Labels := by
      have ha : raw3822step2 = -raw3822step1 := by apply Matrix.ext; change ∀ i j, raw3822step2 i j = -(raw3822step1 i j); unfold raw3822step2 raw3822step1; decide +kernel
      have hl : raw3822step2Labels = raw3822step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3822step2 raw3822step2Labels = mixedMoment B raw3822step3 raw3822step3Labels := by
      have ha : raw3822step3 = raw3822step2 := by apply Matrix.ext; unfold raw3822step3 raw3822step2; decide +kernel
      have hl : raw3822step2Labels = labelEmbedding1 ∘ raw3822step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3822step2 raw3822step2Labels raw3822step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

theorem canonical3834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3834 raw3834Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw3834 raw3834Labels = mixedMoment B raw3834step0 raw3834step0Labels := by
      have hz : ∀ j, raw3834 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3834step0 = (fun i j => raw3834 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3834step0 raw3834; decide +kernel
      have hl : raw3834step0Labels = raw3834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3834 raw3834Labels permutation590 hz
    mixedMoment B raw3834step0 raw3834step0Labels = mixedMoment B raw3834step1 raw3834step1Labels := by
      have hz : ∀ j, raw3834step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3834step1 = (fun i j => raw3834step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3834step1 raw3834step0; decide +kernel
      have hl : raw3834step1Labels = raw3834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3834step0 raw3834step0Labels permutation56 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1140 raw1140Labels = mixedMoment B node4351 node4351Labels := by
  calc
    mixedMoment B raw1140 raw1140Labels = mixedMoment B raw1140step0 raw1140step0Labels := by
      have ha : raw1140step0 = (fun i j => raw1140 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1140step0 raw1140; decide +kernel
      have hl : raw1140step0Labels = raw1140Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1140 raw1140Labels permutation152 permutation4
    mixedMoment B raw1140step0 raw1140step0Labels = mixedMoment B raw1140step1 raw1140step1Labels := by
      have ha : raw1140step1 = raw1140step0 := by apply Matrix.ext; unfold raw1140step1 raw1140step0; decide +kernel
      have hl : raw1140step0Labels = labelEmbedding7 ∘ raw1140step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1140step0 raw1140step0Labels raw1140step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4351 node4351Labels := by rfl

theorem canonical1141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1141 raw1141Labels = mixedMoment B node929 node929Labels := by
  calc
    mixedMoment B raw1141 raw1141Labels = mixedMoment B raw1141step0 raw1141step0Labels := by
      have ha : raw1141step0 = (fun i j => raw1141 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1141step0 raw1141; decide +kernel
      have hl : raw1141step0Labels = raw1141Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1141 raw1141Labels permutation152 permutation4
    _ = mixedMoment B node929 node929Labels := by rfl

theorem canonical1142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1142 raw1142Labels = mixedMoment B node1680 node1680Labels := by
  calc
    mixedMoment B raw1142 raw1142Labels = mixedMoment B raw1142step0 raw1142step0Labels := by
      have ha : raw1142step0 = (fun i j => raw1142 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1142step0 raw1142; decide +kernel
      have hl : raw1142step0Labels = raw1142Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1142 raw1142Labels permutation170 permutation6
    mixedMoment B raw1142step0 raw1142step0Labels = mixedMoment B raw1142step1 raw1142step1Labels := by
      have ha : raw1142step1 = -raw1142step0 := by apply Matrix.ext; change ∀ i j, raw1142step1 i j = -(raw1142step0 i j); unfold raw1142step1 raw1142step0; decide +kernel
      have hl : raw1142step1Labels = raw1142step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1142step1 raw1142step1Labels = mixedMoment B raw1142step2 raw1142step2Labels := by
      have ha : raw1142step2 = raw1142step1 := by apply Matrix.ext; unfold raw1142step2 raw1142step1; decide +kernel
      have hl : raw1142step1Labels = labelEmbedding1 ∘ raw1142step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1142step1 raw1142step1Labels raw1142step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1680 node1680Labels := by rfl

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

theorem canonical1266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1266 raw1266Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw1266 raw1266Labels = mixedMoment B raw1266step0 raw1266step0Labels := by
      have ha : raw1266step0 = (fun i j => raw1266 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1266step0 raw1266; decide +kernel
      have hl : raw1266step0Labels = raw1266Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1266 raw1266Labels permutation32 permutation4
    mixedMoment B raw1266step0 raw1266step0Labels = mixedMoment B raw1266step1 raw1266step1Labels := by
      have ha : raw1266step1 = raw1266step0 := by apply Matrix.ext; unfold raw1266step1 raw1266step0; decide +kernel
      have hl : raw1266step0Labels = labelEmbedding7 ∘ raw1266step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1266step0 raw1266step0Labels raw1266step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

theorem canonical1267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1267 raw1267Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw1267 raw1267Labels = mixedMoment B raw1267step0 raw1267step0Labels := by
      have ha : raw1267step0 = (fun i j => raw1267 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1267step0 raw1267; decide +kernel
      have hl : raw1267step0Labels = raw1267Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1267 raw1267Labels permutation32 permutation4
    _ = mixedMoment B node1044 node1044Labels := by rfl

theorem canonical1268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1268 raw1268Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw1268 raw1268Labels = mixedMoment B raw1268step0 raw1268step0Labels := by
      have ha : raw1268step0 = (fun i j => raw1268 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1268step0 raw1268; decide +kernel
      have hl : raw1268step0Labels = raw1268Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1268 raw1268Labels permutation50 permutation6
    mixedMoment B raw1268step0 raw1268step0Labels = mixedMoment B raw1268step1 raw1268step1Labels := by
      have ha : raw1268step1 = -raw1268step0 := by apply Matrix.ext; change ∀ i j, raw1268step1 i j = -(raw1268step0 i j); unfold raw1268step1 raw1268step0; decide +kernel
      have hl : raw1268step1Labels = raw1268step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1268step1 raw1268step1Labels = mixedMoment B raw1268step2 raw1268step2Labels := by
      have ha : raw1268step2 = raw1268step1 := by apply Matrix.ext; unfold raw1268step2 raw1268step1; decide +kernel
      have hl : raw1268step1Labels = labelEmbedding1 ∘ raw1268step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1268step1 raw1268step1Labels raw1268step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

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

theorem sum_fin_six {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
  ac_rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4351 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4351 node4351Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node929 node929Labels + mixedMoment B node1680 node1680Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1140 singletonSmall4351
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4351) = raw1140Labels := by decide +kernel
  rw [hl, canonical1140 B hB] at h
  have hc0 : mixedMoment B raw1140 (Fin.cases (0 : Fin 2) singletonSmall4351) =
      mixedMoment B node929 node929Labels := by
    have ha : raw1140 = raw1141 := by apply Matrix.ext; unfold raw1140 raw1141; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4351 = raw1141Labels := by decide +kernel
    rw [ha, hj, canonical1141 B hB]
  have hc1 : mixedMoment B raw1140 (Fin.cases (1 : Fin 2) singletonSmall4351) =
      mixedMoment B node1680 node1680Labels := by
    have ha : raw1140 = raw1142 := by apply Matrix.ext; unfold raw1140 raw1142; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4351 = raw1142Labels := by decide +kernel
    rw [ha, hj, canonical1142 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4461 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4461 node4461Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1044 node1044Labels + mixedMoment B node1737 node1737Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1266 singletonSmall4461
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4461) = raw1266Labels := by decide +kernel
  rw [hl, canonical1266 B hB] at h
  have hc0 : mixedMoment B raw1266 (Fin.cases (0 : Fin 2) singletonSmall4461) =
      mixedMoment B node1044 node1044Labels := by
    have ha : raw1266 = raw1267 := by apply Matrix.ext; unfold raw1266 raw1267; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4461 = raw1267Labels := by decide +kernel
    rw [ha, hj, canonical1267 B hB]
  have hc1 : mixedMoment B raw1266 (Fin.cases (1 : Fin 2) singletonSmall4461) =
      mixedMoment B node1737 node1737Labels := by
    have ha : raw1266 = raw1268 := by apply Matrix.ext; unfold raw1266 raw1268; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4461 = raw1268Labels := by decide +kernel
    rw [ha, hj, canonical1268 B hB]
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

theorem singleton4802 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4802 node4802Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2020 node2020Labels + mixedMoment B node2202 node2202Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1734 singletonSmall4802
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4802) = raw1734Labels := by decide +kernel
  rw [hl, canonical1734 B hB] at h
  have hc0 : mixedMoment B raw1734 (Fin.cases (0 : Fin 2) singletonSmall4802) =
      mixedMoment B node2020 node2020Labels := by
    have ha : raw1734 = raw1735 := by apply Matrix.ext; unfold raw1734 raw1735; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4802 = raw1735Labels := by decide +kernel
    rw [ha, hj, canonical1735 B hB]
  have hc1 : mixedMoment B raw1734 (Fin.cases (1 : Fin 2) singletonSmall4802) =
      mixedMoment B node2202 node2202Labels := by
    have ha : raw1734 = raw1736 := by apply Matrix.ext; unfold raw1734 raw1736; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4802 = raw1736Labels := by decide +kernel
    rw [ha, hj, canonical1736 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node929 node929Labels = Sparse.eval nodeValue929 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 929) = mixedMoment B node929 node929Labels := rfl
  simpa [nodeValue929, Sparse.eval] using hc.symm

theorem sound941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node941 node941Labels = Sparse.eval nodeValue941 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 941) = mixedMoment B node941 node941Labels := rfl
  simpa [nodeValue941, Sparse.eval] using hc.symm

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

theorem sound1044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1044 node1044Labels = Sparse.eval nodeValue1044 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1044) = mixedMoment B node1044 node1044Labels := rfl
  simpa [nodeValue1044, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1678 node1678Labels = Sparse.eval nodeValue1678 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1678) = mixedMoment B node1678 node1678Labels := rfl
  simpa [nodeValue1678, Sparse.eval] using hc.symm

theorem sound1680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1680 node1680Labels = Sparse.eval nodeValue1680 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1680) = mixedMoment B node1680 node1680Labels := rfl
  simpa [nodeValue1680, Sparse.eval] using hc.symm

theorem sound1684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1684 node1684Labels = Sparse.eval nodeValue1684 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1684) = mixedMoment B node1684 node1684Labels := rfl
  simpa [nodeValue1684, Sparse.eval] using hc.symm

theorem sound1697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1697 node1697Labels = Sparse.eval nodeValue1697 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1697) = mixedMoment B node1697 node1697Labels := rfl
  simpa [nodeValue1697, Sparse.eval] using hc.symm

theorem sound1704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1704 node1704Labels = Sparse.eval nodeValue1704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1704) = mixedMoment B node1704 node1704Labels := rfl
  simpa [nodeValue1704, Sparse.eval] using hc.symm

theorem sound1707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1707 node1707Labels = Sparse.eval nodeValue1707 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1707) = mixedMoment B node1707 node1707Labels := rfl
  simpa [nodeValue1707, Sparse.eval] using hc.symm

theorem sound1712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1712 node1712Labels = Sparse.eval nodeValue1712 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1712) = mixedMoment B node1712 node1712Labels := rfl
  simpa [nodeValue1712, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1737 node1737Labels = Sparse.eval nodeValue1737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1737) = mixedMoment B node1737 node1737Labels := rfl
  simpa [nodeValue1737, Sparse.eval] using hc.symm

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

theorem sound1793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1793 node1793Labels = Sparse.eval nodeValue1793 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1793) = mixedMoment B node1793 node1793Labels := rfl
  simpa [nodeValue1793, Sparse.eval] using hc.symm

theorem sound1794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1794 node1794Labels = Sparse.eval nodeValue1794 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1794) = mixedMoment B node1794 node1794Labels := rfl
  simpa [nodeValue1794, Sparse.eval] using hc.symm

theorem sound1811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1811 node1811Labels = Sparse.eval nodeValue1811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1811) = mixedMoment B node1811 node1811Labels := rfl
  simpa [nodeValue1811, Sparse.eval] using hc.symm

theorem sound1821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1821 node1821Labels = Sparse.eval nodeValue1821 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1821) = mixedMoment B node1821 node1821Labels := rfl
  simpa [nodeValue1821, Sparse.eval] using hc.symm

theorem sound1823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1823 node1823Labels = Sparse.eval nodeValue1823 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1823) = mixedMoment B node1823 node1823Labels := rfl
  simpa [nodeValue1823, Sparse.eval] using hc.symm

theorem sound1826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1826 node1826Labels = Sparse.eval nodeValue1826 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1826) = mixedMoment B node1826 node1826Labels := rfl
  simpa [nodeValue1826, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1912 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1912 node1912Labels = 0 := by
  exact mixedMoment_order_one B hB node1912 node1912Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1877 node1877Labels = Sparse.eval nodeValue1877 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1877) = mixedMoment B node1877 node1877Labels := rfl
  simpa [nodeValue1877, Sparse.eval] using hc.symm

theorem sound1879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1879 node1879Labels = Sparse.eval nodeValue1879 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1879) = mixedMoment B node1879 node1879Labels := rfl
  simpa [nodeValue1879, Sparse.eval] using hc.symm

theorem sound1912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1912 node1912Labels = Sparse.eval nodeValue1912 (mixedVector B) := by
  simpa only [nodeValue1912, Sparse.eval_nil] using zero1912 B _hB _hF

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

theorem sound2020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2020 node2020Labels = Sparse.eval nodeValue2020 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2020) = mixedMoment B node2020 node2020Labels := rfl
  simpa [nodeValue2020, Sparse.eval] using hc.symm

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

theorem sound2077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2077 node2077Labels = Sparse.eval nodeValue2077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2077) = mixedMoment B node2077 node2077Labels := rfl
  simpa [nodeValue2077, Sparse.eval] using hc.symm

theorem sound2104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2104 node2104Labels = Sparse.eval nodeValue2104 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2104) = mixedMoment B node2104 node2104Labels := rfl
  simpa [nodeValue2104, Sparse.eval] using hc.symm

theorem sound2106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2106 node2106Labels = Sparse.eval nodeValue2106 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2106) = mixedMoment B node2106 node2106Labels := rfl
  simpa [nodeValue2106, Sparse.eval] using hc.symm

theorem sound2110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2110 node2110Labels = Sparse.eval nodeValue2110 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2110) = mixedMoment B node2110 node2110Labels := rfl
  simpa [nodeValue2110, Sparse.eval] using hc.symm

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

theorem sound2154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2154 node2154Labels = Sparse.eval nodeValue2154 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2154) = mixedMoment B node2154 node2154Labels := rfl
  simpa [nodeValue2154, Sparse.eval] using hc.symm

theorem sound2156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2156 node2156Labels = Sparse.eval nodeValue2156 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2156) = mixedMoment B node2156 node2156Labels := rfl
  simpa [nodeValue2156, Sparse.eval] using hc.symm

theorem sound2160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2160 node2160Labels = Sparse.eval nodeValue2160 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2160) = mixedMoment B node2160 node2160Labels := rfl
  simpa [nodeValue2160, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2204 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2204 node2204Labels = 0 := by
  exact mixedMoment_order_one B hB node2204 node2204Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2179 node2179Labels = Sparse.eval nodeValue2179 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2179) = mixedMoment B node2179 node2179Labels := rfl
  simpa [nodeValue2179, Sparse.eval] using hc.symm

theorem sound2189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2189 node2189Labels = Sparse.eval nodeValue2189 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2189) = mixedMoment B node2189 node2189Labels := rfl
  simpa [nodeValue2189, Sparse.eval] using hc.symm

theorem sound2190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2190 node2190Labels = Sparse.eval nodeValue2190 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2190) = mixedMoment B node2190 node2190Labels := rfl
  simpa [nodeValue2190, Sparse.eval] using hc.symm

theorem sound2194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2194 node2194Labels = Sparse.eval nodeValue2194 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2194) = mixedMoment B node2194 node2194Labels := rfl
  simpa [nodeValue2194, Sparse.eval] using hc.symm

theorem sound2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2202 node2202Labels = Sparse.eval nodeValue2202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2202) = mixedMoment B node2202 node2202Labels := rfl
  simpa [nodeValue2202, Sparse.eval] using hc.symm

theorem sound2204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2204 node2204Labels = Sparse.eval nodeValue2204 (mixedVector B) := by
  simpa only [nodeValue2204, Sparse.eval_nil] using zero2204 B _hB _hF

theorem sound2211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2211 node2211Labels = Sparse.eval nodeValue2211 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2211) = mixedMoment B node2211 node2211Labels := rfl
  simpa [nodeValue2211, Sparse.eval] using hc.symm

theorem sound2213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2213 node2213Labels = Sparse.eval nodeValue2213 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2213) = mixedMoment B node2213 node2213Labels := rfl
  simpa [nodeValue2213, Sparse.eval] using hc.symm

theorem sound2214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2214 node2214Labels = Sparse.eval nodeValue2214 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2214) = mixedMoment B node2214 node2214Labels := rfl
  simpa [nodeValue2214, Sparse.eval] using hc.symm

theorem sound2219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2219 node2219Labels = Sparse.eval nodeValue2219 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2219) = mixedMoment B node2219 node2219Labels := rfl
  simpa [nodeValue2219, Sparse.eval] using hc.symm

theorem sound2231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2231 node2231Labels = Sparse.eval nodeValue2231 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2231) = mixedMoment B node2231 node2231Labels := rfl
  simpa [nodeValue2231, Sparse.eval] using hc.symm

theorem sound2232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2232 node2232Labels = Sparse.eval nodeValue2232 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2232) = mixedMoment B node2232 node2232Labels := rfl
  simpa [nodeValue2232, Sparse.eval] using hc.symm

theorem sound2239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2239 node2239Labels = Sparse.eval nodeValue2239 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2239) = mixedMoment B node2239 node2239Labels := rfl
  simpa [nodeValue2239, Sparse.eval] using hc.symm

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

theorem zero2263 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2263 node2263Labels = 0 := by
  exact mixedMoment_order_one B hB node2263 node2263Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = 0 := by
  exact mixedMoment_order_one B hB node2264 node2264Labels 1
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

theorem sound2242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2242 node2242Labels = Sparse.eval nodeValue2242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2242) = mixedMoment B node2242 node2242Labels := rfl
  simpa [nodeValue2242, Sparse.eval] using hc.symm

theorem sound2244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2244 node2244Labels = Sparse.eval nodeValue2244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2244) = mixedMoment B node2244 node2244Labels := rfl
  simpa [nodeValue2244, Sparse.eval] using hc.symm

theorem sound2245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2245 node2245Labels = Sparse.eval nodeValue2245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2245) = mixedMoment B node2245 node2245Labels := rfl
  simpa [nodeValue2245, Sparse.eval] using hc.symm

theorem sound2249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2249 node2249Labels = Sparse.eval nodeValue2249 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2249) = mixedMoment B node2249 node2249Labels := rfl
  simpa [nodeValue2249, Sparse.eval] using hc.symm

theorem sound2251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2251 node2251Labels = Sparse.eval nodeValue2251 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2251) = mixedMoment B node2251 node2251Labels := rfl
  simpa [nodeValue2251, Sparse.eval] using hc.symm

theorem sound2261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2261 node2261Labels = Sparse.eval nodeValue2261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2261) = mixedMoment B node2261 node2261Labels := rfl
  simpa [nodeValue2261, Sparse.eval] using hc.symm

theorem sound2263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2263 node2263Labels = Sparse.eval nodeValue2263 (mixedVector B) := by
  simpa only [nodeValue2263, Sparse.eval_nil] using zero2263 B _hB _hF

theorem sound2264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = Sparse.eval nodeValue2264 (mixedVector B) := by
  simpa only [nodeValue2264, Sparse.eval_nil] using zero2264 B _hB _hF

theorem sound2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2275 node2275Labels = Sparse.eval nodeValue2275 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2275) = mixedMoment B node2275 node2275Labels := rfl
  simpa [nodeValue2275, Sparse.eval] using hc.symm

theorem sound2276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2276 node2276Labels = Sparse.eval nodeValue2276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2276) = mixedMoment B node2276 node2276Labels := rfl
  simpa [nodeValue2276, Sparse.eval] using hc.symm

theorem sound2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2277 node2277Labels = Sparse.eval nodeValue2277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2277) = mixedMoment B node2277 node2277Labels := rfl
  simpa [nodeValue2277, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2676 node2676Labels = Sparse.eval nodeValue2676 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2676) = mixedMoment B node2676 node2676Labels := rfl
  simpa [nodeValue2676, Sparse.eval] using hc.symm

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

theorem sound2708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2708 node2708Labels = Sparse.eval nodeValue2708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2708) = mixedMoment B node2708 node2708Labels := rfl
  simpa [nodeValue2708, Sparse.eval] using hc.symm

theorem sound2721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2721 node2721Labels = Sparse.eval nodeValue2721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2721) = mixedMoment B node2721 node2721Labels := rfl
  simpa [nodeValue2721, Sparse.eval] using hc.symm

theorem sound2728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2728 node2728Labels = Sparse.eval nodeValue2728 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2728) = mixedMoment B node2728 node2728Labels := rfl
  simpa [nodeValue2728, Sparse.eval] using hc.symm

theorem sound2730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2730 node2730Labels = Sparse.eval nodeValue2730 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2730) = mixedMoment B node2730 node2730Labels := rfl
  simpa [nodeValue2730, Sparse.eval] using hc.symm

theorem sound2748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2748 node2748Labels = Sparse.eval nodeValue2748 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2748) = mixedMoment B node2748 node2748Labels := rfl
  simpa [nodeValue2748, Sparse.eval] using hc.symm

theorem sound2751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2751 node2751Labels = Sparse.eval nodeValue2751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2751) = mixedMoment B node2751 node2751Labels := rfl
  simpa [nodeValue2751, Sparse.eval] using hc.symm

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

theorem sound2765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2765 node2765Labels = Sparse.eval nodeValue2765 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2765) = mixedMoment B node2765 node2765Labels := rfl
  simpa [nodeValue2765, Sparse.eval] using hc.symm

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

theorem sound3050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3050 node3050Labels = Sparse.eval nodeValue3050 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3050) = mixedMoment B node3050 node3050Labels := rfl
  simpa [nodeValue3050, Sparse.eval] using hc.symm

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

theorem sound3378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3378 node3378Labels = Sparse.eval nodeValue3378 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3378) = mixedMoment B node3378 node3378Labels := rfl
  simpa [nodeValue3378, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3446 node3446Labels = Sparse.eval nodeValue3446 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3446) = mixedMoment B node3446 node3446Labels := rfl
  simpa [nodeValue3446, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4079 node4079Labels = Sparse.eval nodeValue4079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4079) = mixedMoment B node4079 node4079Labels := rfl
  simpa [nodeValue4079, Sparse.eval] using hc.symm

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4331 node4331Labels = Sparse.eval nodeValue4331 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4331) = mixedMoment B node4331 node4331Labels := rfl
  simpa [nodeValue4331, Sparse.eval] using hc.symm

theorem sound4332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4332 node4332Labels = Sparse.eval nodeValue4332 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4332) = mixedMoment B node4332 node4332Labels := rfl
  simpa [nodeValue4332, Sparse.eval] using hc.symm

theorem sound4351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4351 node4351Labels = Sparse.eval nodeValue4351 (mixedVector B) := by
  have h := singleton4351 B _hB
  rw [sound929 B _hB _hF, sound1680 B _hB _hF] at h
  norm_num [nodeValue4351, nodeValue929, nodeValue1680, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4461 node4461Labels = Sparse.eval nodeValue4461 (mixedVector B) := by
  have h := singleton4461 B _hB
  rw [sound1044 B _hB _hF, sound1737 B _hB _hF] at h
  norm_num [nodeValue4461, nodeValue1044, nodeValue1737, Sparse.eval] at h ⊢
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

theorem sound4667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4667 node4667Labels = Sparse.eval nodeValue4667 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4667) = mixedMoment B node4667 node4667Labels := rfl
  simpa [nodeValue4667, Sparse.eval] using hc.symm

theorem sound4668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4668 node4668Labels = Sparse.eval nodeValue4668 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4668) = mixedMoment B node4668 node4668Labels := rfl
  simpa [nodeValue4668, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4765 node4765Labels = Sparse.eval nodeValue4765 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4765) = mixedMoment B node4765 node4765Labels := rfl
  simpa [nodeValue4765, Sparse.eval] using hc.symm

theorem sound4775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4775 node4775Labels = Sparse.eval nodeValue4775 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4775) = mixedMoment B node4775 node4775Labels := rfl
  simpa [nodeValue4775, Sparse.eval] using hc.symm

theorem sound4793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4793 node4793Labels = Sparse.eval nodeValue4793 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4793) = mixedMoment B node4793 node4793Labels := rfl
  simpa [nodeValue4793, Sparse.eval] using hc.symm

theorem sound4795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4795 node4795Labels = Sparse.eval nodeValue4795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4795) = mixedMoment B node4795 node4795Labels := rfl
  simpa [nodeValue4795, Sparse.eval] using hc.symm

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

theorem zero4833 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4833 node4833Labels = 0 := by
  exact mixedMoment_order_one B hB node4833 node4833Labels 1
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

theorem sound4802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4802 node4802Labels = Sparse.eval nodeValue4802 (mixedVector B) := by
  have h := singleton4802 B _hB
  rw [sound2020 B _hB _hF, sound2202 B _hB _hF] at h
  norm_num [nodeValue4802, nodeValue2020, nodeValue2202, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4805 node4805Labels = Sparse.eval nodeValue4805 (mixedVector B) := by
  have h := singleton4805 B _hB
  rw [sound2023 B _hB _hF, sound2214 B _hB _hF] at h
  norm_num [nodeValue4805, nodeValue2023, nodeValue2214, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4833 node4833Labels = Sparse.eval nodeValue4833 (mixedVector B) := by
  simpa only [nodeValue4833, Sparse.eval_nil] using zero4833 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4893 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4893 node4893Labels = 0 := by
  exact mixedMoment_order_one B hB node4893 node4893Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4869 node4869Labels = Sparse.eval nodeValue4869 (mixedVector B) := by
  have h := singleton4869 B _hB
  rw [sound2110 B _hB _hF, sound2275 B _hB _hF] at h
  norm_num [nodeValue4869, nodeValue2110, nodeValue2275, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4889 node4889Labels = Sparse.eval nodeValue4889 (mixedVector B) := by
  have h := singleton4889 B _hB
  rw [sound2245 B _hB _hF, sound2277 B _hB _hF] at h
  norm_num [nodeValue4889, nodeValue2245, nodeValue2277, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4893 node4893Labels = Sparse.eval nodeValue4893 (mixedVector B) := by
  simpa only [nodeValue4893, Sparse.eval_nil] using zero4893 B _hB _hF

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

theorem sound5231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5231 node5231Labels = Sparse.eval nodeValue5231 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5231) = mixedMoment B node5231 node5231Labels := rfl
  simpa [nodeValue5231, Sparse.eval] using hc.symm

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

theorem sound5263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5263 node5263Labels = Sparse.eval nodeValue5263 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5263) = mixedMoment B node5263 node5263Labels := rfl
  simpa [nodeValue5263, Sparse.eval] using hc.symm

theorem sound5265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5265 node5265Labels = Sparse.eval nodeValue5265 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5265) = mixedMoment B node5265 node5265Labels := rfl
  simpa [nodeValue5265, Sparse.eval] using hc.symm

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

theorem sourceEq2453 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2453 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2453 + difference 0 1) (sourceB2453 + difference 1 0) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2748) := by
    have ha : (tripleCharges (sourceA2453 + difference 0 1) (sourceB2453 + difference 1 0) sourceC2453) = raw33691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33691; decide +kernel
    rw [ha]
    exact (canonical33691 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2453 + difference 0 2) (sourceB2453 + difference 2 0) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2708) := by
    have ha : (tripleCharges (sourceA2453 + difference 0 2) (sourceB2453 + difference 2 0) sourceC2453) = raw33692 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33692; decide +kernel
    rw [ha]
    exact (canonical33692 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2453 + difference 0 3) (sourceB2453 + difference 3 0) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA2453 + difference 0 3) (sourceB2453 + difference 3 0) sourceC2453) = raw33693 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33693; decide +kernel
    rw [ha]
    exact (canonical33693 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2453 + difference 0 4) (sourceB2453 + difference 4 0) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA2453 + difference 0 4) (sourceB2453 + difference 4 0) sourceC2453) = raw33694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33694; decide +kernel
    rw [ha]
    exact (canonical33694 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2453 + difference 0 5) (sourceB2453 + difference 5 0) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA2453 + difference 0 5) (sourceB2453 + difference 5 0) sourceC2453) = raw33695 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33695; decide +kernel
    rw [ha]
    exact (canonical33695 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2453 + difference 1 0) (sourceB2453 + difference 0 1) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA2453 + difference 1 0) (sourceB2453 + difference 0 1) sourceC2453) = raw21444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw21444; decide +kernel
    rw [ha]
    exact (canonical21444 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2453 + difference 1 2) (sourceB2453 + difference 2 1) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA2453 + difference 1 2) (sourceB2453 + difference 2 1) sourceC2453) = raw25392 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw25392; decide +kernel
    rw [ha]
    exact (canonical25392 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2453 + difference 1 3) (sourceB2453 + difference 3 1) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA2453 + difference 1 3) (sourceB2453 + difference 3 1) sourceC2453) = raw21429 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw21429; decide +kernel
    rw [ha]
    exact (canonical21429 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2453 + difference 1 4) (sourceB2453 + difference 4 1) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA2453 + difference 1 4) (sourceB2453 + difference 4 1) sourceC2453) = raw25393 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw25393; decide +kernel
    rw [ha]
    exact (canonical25393 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2453 + difference 1 5) (sourceB2453 + difference 5 1) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA2453 + difference 1 5) (sourceB2453 + difference 5 1) sourceC2453) = raw25394 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw25394; decide +kernel
    rw [ha]
    exact (canonical25394 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2453 + difference 2 0) (sourceB2453 + difference 0 2) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1697) := by
    have ha : (tripleCharges (sourceA2453 + difference 2 0) (sourceB2453 + difference 0 2) sourceC2453) = raw25400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw25400; decide +kernel
    rw [ha]
    exact (canonical25400 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2453 + difference 2 1) (sourceB2453 + difference 1 2) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2231) := by
    have ha : (tripleCharges (sourceA2453 + difference 2 1) (sourceB2453 + difference 1 2) sourceC2453) = raw33696 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33696; decide +kernel
    rw [ha]
    exact (canonical33696 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2453 + difference 2 3) (sourceB2453 + difference 3 2) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA2453 + difference 2 3) (sourceB2453 + difference 3 2) sourceC2453) = raw33697 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33697; decide +kernel
    rw [ha]
    exact (canonical33697 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2453 + difference 2 4) (sourceB2453 + difference 4 2) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA2453 + difference 2 4) (sourceB2453 + difference 4 2) sourceC2453) = raw33698 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33698; decide +kernel
    rw [ha]
    exact (canonical33698 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2453 + difference 2 5) (sourceB2453 + difference 5 2) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2232) := by
    have ha : (tripleCharges (sourceA2453 + difference 2 5) (sourceB2453 + difference 5 2) sourceC2453) = raw33699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33699; decide +kernel
    rw [ha]
    exact (canonical33699 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2453 + difference 3 0) (sourceB2453 + difference 0 3) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1712) := by
    have ha : (tripleCharges (sourceA2453 + difference 3 0) (sourceB2453 + difference 0 3) sourceC2453) = raw25404 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw25404; decide +kernel
    rw [ha]
    exact (canonical25404 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2453 + difference 3 1) (sourceB2453 + difference 1 3) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2249) := by
    have ha : (tripleCharges (sourceA2453 + difference 3 1) (sourceB2453 + difference 1 3) sourceC2453) = raw33700 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33700; decide +kernel
    rw [ha]
    exact (canonical33700 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2453 + difference 3 2) (sourceB2453 + difference 2 3) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2194) := by
    have ha : (tripleCharges (sourceA2453 + difference 3 2) (sourceB2453 + difference 2 3) sourceC2453) = raw33701 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33701; decide +kernel
    rw [ha]
    exact (canonical33701 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2453 + difference 3 4) (sourceB2453 + difference 4 3) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA2453 + difference 3 4) (sourceB2453 + difference 4 3) sourceC2453) = raw33702 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33702; decide +kernel
    rw [ha]
    exact (canonical33702 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2453 + difference 3 5) (sourceB2453 + difference 5 3) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA2453 + difference 3 5) (sourceB2453 + difference 5 3) sourceC2453) = raw33703 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33703; decide +kernel
    rw [ha]
    exact (canonical33703 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2453 + difference 4 0) (sourceB2453 + difference 0 4) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1712) := by
    have ha : (tripleCharges (sourceA2453 + difference 4 0) (sourceB2453 + difference 0 4) sourceC2453) = raw25409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw25409; decide +kernel
    rw [ha]
    exact (canonical25409 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2453 + difference 4 1) (sourceB2453 + difference 1 4) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2249) := by
    have ha : (tripleCharges (sourceA2453 + difference 4 1) (sourceB2453 + difference 1 4) sourceC2453) = raw33704 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33704; decide +kernel
    rw [ha]
    exact (canonical33704 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2453 + difference 4 2) (sourceB2453 + difference 2 4) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2194) := by
    have ha : (tripleCharges (sourceA2453 + difference 4 2) (sourceB2453 + difference 2 4) sourceC2453) = raw33705 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33705; decide +kernel
    rw [ha]
    exact (canonical33705 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2453 + difference 4 3) (sourceB2453 + difference 3 4) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA2453 + difference 4 3) (sourceB2453 + difference 3 4) sourceC2453) = raw33706 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33706; decide +kernel
    rw [ha]
    exact (canonical33706 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2453 + difference 4 5) (sourceB2453 + difference 5 4) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA2453 + difference 4 5) (sourceB2453 + difference 5 4) sourceC2453) = raw33707 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33707; decide +kernel
    rw [ha]
    exact (canonical33707 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2453 + difference 5 0) (sourceB2453 + difference 0 5) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1704) := by
    have ha : (tripleCharges (sourceA2453 + difference 5 0) (sourceB2453 + difference 0 5) sourceC2453) = raw21441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw21441; decide +kernel
    rw [ha]
    exact (canonical21441 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2453 + difference 5 1) (sourceB2453 + difference 1 5) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2239) := by
    have ha : (tripleCharges (sourceA2453 + difference 5 1) (sourceB2453 + difference 1 5) sourceC2453) = raw33708 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33708; decide +kernel
    rw [ha]
    exact (canonical33708 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2453 + difference 5 2) (sourceB2453 + difference 2 5) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2189) := by
    have ha : (tripleCharges (sourceA2453 + difference 5 2) (sourceB2453 + difference 2 5) sourceC2453) = raw33709 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33709; decide +kernel
    rw [ha]
    exact (canonical33709 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2453 + difference 5 3) (sourceB2453 + difference 3 5) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA2453 + difference 5 3) (sourceB2453 + difference 3 5) sourceC2453) = raw21425 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw21425; decide +kernel
    rw [ha]
    exact (canonical21425 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2453 + difference 5 4) (sourceB2453 + difference 4 5) sourceC2453) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA2453 + difference 5 4) (sourceB2453 + difference 4 5) sourceC2453) = raw33710 := by
      apply Matrix.ext; unfold tripleCharges sourceA2453 sourceB2453 sourceC2453 difference raw33710; decide +kernel
    rw [ha]
    exact (canonical33710 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2453 sourceB2453 sourceC2453
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2453, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2454 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2454 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2454 + difference 0 1) (sourceB2454 + difference 1 0) sourceC2454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3050) := by
    have ha : (tripleCharges (sourceA2454 + difference 0 1) (sourceB2454 + difference 1 0) sourceC2454) = raw33711 := by
      apply Matrix.ext; unfold tripleCharges sourceA2454 sourceB2454 sourceC2454 difference raw33711; decide +kernel
    rw [ha]
    exact (canonical33711 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2454 + difference 1 1) (sourceB2454 + difference 1 1) sourceC2454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA2454 + difference 1 1) (sourceB2454 + difference 1 1) sourceC2454) = raw25421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2454 sourceB2454 sourceC2454 difference raw25421; decide +kernel
    rw [ha]
    exact (canonical25421 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2454 + difference 2 1) (sourceB2454 + difference 1 2) sourceC2454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1821) := by
    have ha : (tripleCharges (sourceA2454 + difference 2 1) (sourceB2454 + difference 1 2) sourceC2454) = raw33712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2454 sourceB2454 sourceC2454 difference raw33712; decide +kernel
    rw [ha]
    exact (canonical33712 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2454 + difference 3 1) (sourceB2454 + difference 1 3) sourceC2454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1826) := by
    have ha : (tripleCharges (sourceA2454 + difference 3 1) (sourceB2454 + difference 1 3) sourceC2454) = raw33713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2454 sourceB2454 sourceC2454 difference raw33713; decide +kernel
    rw [ha]
    exact (canonical33713 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2454 + difference 4 1) (sourceB2454 + difference 1 4) sourceC2454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1826) := by
    have ha : (tripleCharges (sourceA2454 + difference 4 1) (sourceB2454 + difference 1 4) sourceC2454) = raw33714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2454 sourceB2454 sourceC2454 difference raw33714; decide +kernel
    rw [ha]
    exact (canonical33714 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2454 + difference 5 1) (sourceB2454 + difference 1 5) sourceC2454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1823) := by
    have ha : (tripleCharges (sourceA2454 + difference 5 1) (sourceB2454 + difference 1 5) sourceC2454) = raw33715 := by
      apply Matrix.ext; unfold tripleCharges sourceA2454 sourceB2454 sourceC2454 difference raw33715; decide +kernel
    rw [ha]
    exact (canonical33715 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2454 + sourceB2454) sourceC2454) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2454 + sourceB2454) sourceC2454) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA2454 sourceB2454 sourceC2454 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2454 sourceB2454 sourceC2454
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2454, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2455 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2455 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2455 + difference 2 0) (sourceB2455 + difference 0 2) sourceC2455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 941) := by
    have ha : (tripleCharges (sourceA2455 + difference 2 0) (sourceB2455 + difference 0 2) sourceC2455) = raw25422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2455 sourceB2455 sourceC2455 difference raw25422; decide +kernel
    rw [ha]
    exact (canonical25422 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2455 + difference 2 1) (sourceB2455 + difference 1 2) sourceC2455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1821) := by
    have ha : (tripleCharges (sourceA2455 + difference 2 1) (sourceB2455 + difference 1 2) sourceC2455) = raw33712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2455 sourceB2455 sourceC2455 difference raw33712; decide +kernel
    rw [ha]
    exact (canonical33712 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2455 + difference 2 2) (sourceB2455 + difference 2 2) sourceC2455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA2455 + difference 2 2) (sourceB2455 + difference 2 2) sourceC2455) = raw25421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2455 sourceB2455 sourceC2455 difference raw25421; decide +kernel
    rw [ha]
    exact (canonical25421 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2455 + difference 2 3) (sourceB2455 + difference 3 2) sourceC2455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA2455 + difference 2 3) (sourceB2455 + difference 3 2) sourceC2455) = raw33716 := by
      apply Matrix.ext; unfold tripleCharges sourceA2455 sourceB2455 sourceC2455 difference raw33716; decide +kernel
    rw [ha]
    exact (canonical33716 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2455 + difference 2 4) (sourceB2455 + difference 4 2) sourceC2455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA2455 + difference 2 4) (sourceB2455 + difference 4 2) sourceC2455) = raw33717 := by
      apply Matrix.ext; unfold tripleCharges sourceA2455 sourceB2455 sourceC2455 difference raw33717; decide +kernel
    rw [ha]
    exact (canonical33717 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2455 + difference 2 5) (sourceB2455 + difference 5 2) sourceC2455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2104) := by
    have ha : (tripleCharges (sourceA2455 + difference 2 5) (sourceB2455 + difference 5 2) sourceC2455) = raw33718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2455 sourceB2455 sourceC2455 difference raw33718; decide +kernel
    rw [ha]
    exact (canonical33718 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2455 + sourceB2455) sourceC2455) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2455 + sourceB2455) sourceC2455) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA2455 sourceB2455 sourceC2455 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2455 sourceB2455 sourceC2455
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2455, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2460 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2460 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2460 + difference 0 2) (sourceB2460 + difference 2 0) sourceC2460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3446) := by
    have ha : (tripleCharges (sourceA2460 + difference 0 2) (sourceB2460 + difference 2 0) sourceC2460) = raw33784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2460 sourceB2460 sourceC2460 difference raw33784; decide +kernel
    rw [ha]
    exact (canonical33784 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2460 + difference 1 2) (sourceB2460 + difference 2 1) sourceC2460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1912) := by
    have ha : (tripleCharges (sourceA2460 + difference 1 2) (sourceB2460 + difference 2 1) sourceC2460) = raw25525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2460 sourceB2460 sourceC2460 difference raw25525; decide +kernel
    rw [ha]
    exact (canonical25525 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2460 + difference 2 2) (sourceB2460 + difference 2 2) sourceC2460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2077) := by
    have ha : (tripleCharges (sourceA2460 + difference 2 2) (sourceB2460 + difference 2 2) sourceC2460) = raw25524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2460 sourceB2460 sourceC2460 difference raw25524; decide +kernel
    rw [ha]
    exact (canonical25524 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2460 + difference 3 2) (sourceB2460 + difference 2 3) sourceC2460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1879) := by
    have ha : (tripleCharges (sourceA2460 + difference 3 2) (sourceB2460 + difference 2 3) sourceC2460) = raw33788 := by
      apply Matrix.ext; unfold tripleCharges sourceA2460 sourceB2460 sourceC2460 difference raw33788; decide +kernel
    rw [ha]
    exact (canonical33788 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2460 + difference 4 2) (sourceB2460 + difference 2 4) sourceC2460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1879) := by
    have ha : (tripleCharges (sourceA2460 + difference 4 2) (sourceB2460 + difference 2 4) sourceC2460) = raw33789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2460 sourceB2460 sourceC2460 difference raw33789; decide +kernel
    rw [ha]
    exact (canonical33789 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2460 + difference 5 2) (sourceB2460 + difference 2 5) sourceC2460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1877) := by
    have ha : (tripleCharges (sourceA2460 + difference 5 2) (sourceB2460 + difference 2 5) sourceC2460) = raw33790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2460 sourceB2460 sourceC2460 difference raw33790; decide +kernel
    rw [ha]
    exact (canonical33790 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2460 + sourceB2460) sourceC2460) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA2460 + sourceB2460) sourceC2460) = raw25529 := by
      apply Matrix.ext; unfold doubleCharges sourceA2460 sourceB2460 sourceC2460 raw25529; decide +kernel
    rw [ha]
    exact (canonical25529 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2460 sourceB2460 sourceC2460
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2460, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2461 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2461 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2461 + difference 0 1) (sourceB2461 + difference 1 0) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA2461 + difference 0 1) (sourceB2461 + difference 1 0) sourceC2461) = raw33791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33791; decide +kernel
    rw [ha]
    exact (canonical33791 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2461 + difference 0 2) (sourceB2461 + difference 2 0) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5263) := by
    have ha : (tripleCharges (sourceA2461 + difference 0 2) (sourceB2461 + difference 2 0) sourceC2461) = raw33792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33792; decide +kernel
    rw [ha]
    exact (canonical33792 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2461 + difference 0 3) (sourceB2461 + difference 3 0) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA2461 + difference 0 3) (sourceB2461 + difference 3 0) sourceC2461) = raw33793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33793; decide +kernel
    rw [ha]
    exact (canonical33793 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2461 + difference 0 4) (sourceB2461 + difference 4 0) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA2461 + difference 0 4) (sourceB2461 + difference 4 0) sourceC2461) = raw33794 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33794; decide +kernel
    rw [ha]
    exact (canonical33794 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2461 + difference 0 5) (sourceB2461 + difference 5 0) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA2461 + difference 0 5) (sourceB2461 + difference 5 0) sourceC2461) = raw33795 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33795; decide +kernel
    rw [ha]
    exact (canonical33795 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2461 + difference 1 0) (sourceB2461 + difference 0 1) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA2461 + difference 1 0) (sourceB2461 + difference 0 1) sourceC2461) = raw27198 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw27198; decide +kernel
    rw [ha]
    exact (canonical27198 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2461 + difference 1 2) (sourceB2461 + difference 2 1) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA2461 + difference 1 2) (sourceB2461 + difference 2 1) sourceC2461) = raw33796 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33796; decide +kernel
    rw [ha]
    exact (canonical33796 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2461 + difference 1 3) (sourceB2461 + difference 3 1) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA2461 + difference 1 3) (sourceB2461 + difference 3 1) sourceC2461) = raw3762 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw3762; decide +kernel
    rw [ha]
    exact (canonical3762 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2461 + difference 1 4) (sourceB2461 + difference 4 1) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA2461 + difference 1 4) (sourceB2461 + difference 4 1) sourceC2461) = raw3757 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw3757; decide +kernel
    rw [ha]
    exact (canonical3757 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2461 + difference 1 5) (sourceB2461 + difference 5 1) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA2461 + difference 1 5) (sourceB2461 + difference 5 1) sourceC2461) = raw27172 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw27172; decide +kernel
    rw [ha]
    exact (canonical27172 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2461 + difference 2 0) (sourceB2461 + difference 0 2) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4351) := by
    have ha : (tripleCharges (sourceA2461 + difference 2 0) (sourceB2461 + difference 0 2) sourceC2461) = raw27197 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw27197; decide +kernel
    rw [ha]
    exact (canonical27197 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2461 + difference 2 1) (sourceB2461 + difference 1 2) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4685) := by
    have ha : (tripleCharges (sourceA2461 + difference 2 1) (sourceB2461 + difference 1 2) sourceC2461) = raw33797 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33797; decide +kernel
    rw [ha]
    exact (canonical33797 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2461 + difference 2 3) (sourceB2461 + difference 3 2) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2461 + difference 2 3) (sourceB2461 + difference 3 2) sourceC2461) = raw33798 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33798; decide +kernel
    rw [ha]
    exact (canonical33798 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2461 + difference 2 4) (sourceB2461 + difference 4 2) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2461 + difference 2 4) (sourceB2461 + difference 4 2) sourceC2461) = raw33799 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33799; decide +kernel
    rw [ha]
    exact (canonical33799 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2461 + difference 2 5) (sourceB2461 + difference 5 2) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA2461 + difference 2 5) (sourceB2461 + difference 5 2) sourceC2461) = raw27171 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw27171; decide +kernel
    rw [ha]
    exact (canonical27171 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2461 + difference 3 0) (sourceB2461 + difference 0 3) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4332) := by
    have ha : (tripleCharges (sourceA2461 + difference 3 0) (sourceB2461 + difference 0 3) sourceC2461) = raw33800 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33800; decide +kernel
    rw [ha]
    exact (canonical33800 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2461 + difference 3 1) (sourceB2461 + difference 1 3) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4668) := by
    have ha : (tripleCharges (sourceA2461 + difference 3 1) (sourceB2461 + difference 1 3) sourceC2461) = raw33801 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33801; decide +kernel
    rw [ha]
    exact (canonical33801 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2461 + difference 3 2) (sourceB2461 + difference 2 3) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4775) := by
    have ha : (tripleCharges (sourceA2461 + difference 3 2) (sourceB2461 + difference 2 3) sourceC2461) = raw33802 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33802; decide +kernel
    rw [ha]
    exact (canonical33802 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2461 + difference 3 4) (sourceB2461 + difference 4 3) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA2461 + difference 3 4) (sourceB2461 + difference 4 3) sourceC2461) = raw33803 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33803; decide +kernel
    rw [ha]
    exact (canonical33803 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2461 + difference 3 5) (sourceB2461 + difference 5 3) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2461 + difference 3 5) (sourceB2461 + difference 5 3) sourceC2461) = raw33804 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33804; decide +kernel
    rw [ha]
    exact (canonical33804 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2461 + difference 4 0) (sourceB2461 + difference 0 4) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4332) := by
    have ha : (tripleCharges (sourceA2461 + difference 4 0) (sourceB2461 + difference 0 4) sourceC2461) = raw33805 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33805; decide +kernel
    rw [ha]
    exact (canonical33805 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2461 + difference 4 1) (sourceB2461 + difference 1 4) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4668) := by
    have ha : (tripleCharges (sourceA2461 + difference 4 1) (sourceB2461 + difference 1 4) sourceC2461) = raw33806 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33806; decide +kernel
    rw [ha]
    exact (canonical33806 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2461 + difference 4 2) (sourceB2461 + difference 2 4) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4775) := by
    have ha : (tripleCharges (sourceA2461 + difference 4 2) (sourceB2461 + difference 2 4) sourceC2461) = raw33807 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33807; decide +kernel
    rw [ha]
    exact (canonical33807 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2461 + difference 4 3) (sourceB2461 + difference 3 4) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA2461 + difference 4 3) (sourceB2461 + difference 3 4) sourceC2461) = raw33808 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33808; decide +kernel
    rw [ha]
    exact (canonical33808 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2461 + difference 4 5) (sourceB2461 + difference 5 4) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2461 + difference 4 5) (sourceB2461 + difference 5 4) sourceC2461) = raw33809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33809; decide +kernel
    rw [ha]
    exact (canonical33809 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2461 + difference 5 0) (sourceB2461 + difference 0 5) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4331) := by
    have ha : (tripleCharges (sourceA2461 + difference 5 0) (sourceB2461 + difference 0 5) sourceC2461) = raw33810 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33810; decide +kernel
    rw [ha]
    exact (canonical33810 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2461 + difference 5 1) (sourceB2461 + difference 1 5) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4667) := by
    have ha : (tripleCharges (sourceA2461 + difference 5 1) (sourceB2461 + difference 1 5) sourceC2461) = raw33811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33811; decide +kernel
    rw [ha]
    exact (canonical33811 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2461 + difference 5 2) (sourceB2461 + difference 2 5) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4765) := by
    have ha : (tripleCharges (sourceA2461 + difference 5 2) (sourceB2461 + difference 2 5) sourceC2461) = raw33812 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw33812; decide +kernel
    rw [ha]
    exact (canonical33812 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2461 + difference 5 3) (sourceB2461 + difference 3 5) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4793) := by
    have ha : (tripleCharges (sourceA2461 + difference 5 3) (sourceB2461 + difference 3 5) sourceC2461) = raw3759 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw3759; decide +kernel
    rw [ha]
    exact (canonical3759 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2461 + difference 5 4) (sourceB2461 + difference 4 5) sourceC2461) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4793) := by
    have ha : (tripleCharges (sourceA2461 + difference 5 4) (sourceB2461 + difference 4 5) sourceC2461) = raw3754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2461 sourceB2461 sourceC2461 difference raw3754; decide +kernel
    rw [ha]
    exact (canonical3754 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2461 sourceB2461 sourceC2461
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2461, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2462 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2462 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2462 + difference 0 1) (sourceB2462 + difference 1 0) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2676) := by
    have ha : (tripleCharges (sourceA2462 + difference 0 1) (sourceB2462 + difference 1 0) sourceC2462) = raw33813 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33813; decide +kernel
    rw [ha]
    exact (canonical33813 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2462 + difference 0 2) (sourceB2462 + difference 2 0) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2728) := by
    have ha : (tripleCharges (sourceA2462 + difference 0 2) (sourceB2462 + difference 2 0) sourceC2462) = raw33814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33814; decide +kernel
    rw [ha]
    exact (canonical33814 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2462 + difference 0 3) (sourceB2462 + difference 3 0) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA2462 + difference 0 3) (sourceB2462 + difference 3 0) sourceC2462) = raw33815 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33815; decide +kernel
    rw [ha]
    exact (canonical33815 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2462 + difference 0 4) (sourceB2462 + difference 4 0) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA2462 + difference 0 4) (sourceB2462 + difference 4 0) sourceC2462) = raw33816 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33816; decide +kernel
    rw [ha]
    exact (canonical33816 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2462 + difference 0 5) (sourceB2462 + difference 5 0) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA2462 + difference 0 5) (sourceB2462 + difference 5 0) sourceC2462) = raw33817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33817; decide +kernel
    rw [ha]
    exact (canonical33817 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2462 + difference 1 0) (sourceB2462 + difference 0 1) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA2462 + difference 1 0) (sourceB2462 + difference 0 1) sourceC2462) = raw33818 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33818; decide +kernel
    rw [ha]
    exact (canonical33818 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2462 + difference 1 2) (sourceB2462 + difference 2 1) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA2462 + difference 1 2) (sourceB2462 + difference 2 1) sourceC2462) = raw33819 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33819; decide +kernel
    rw [ha]
    exact (canonical33819 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2462 + difference 1 3) (sourceB2462 + difference 3 1) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA2462 + difference 1 3) (sourceB2462 + difference 3 1) sourceC2462) = raw3822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw3822; decide +kernel
    rw [ha]
    exact (canonical3822 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2462 + difference 1 4) (sourceB2462 + difference 4 1) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA2462 + difference 1 4) (sourceB2462 + difference 4 1) sourceC2462) = raw3817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw3817; decide +kernel
    rw [ha]
    exact (canonical3817 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2462 + difference 1 5) (sourceB2462 + difference 5 1) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA2462 + difference 1 5) (sourceB2462 + difference 5 1) sourceC2462) = raw33820 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33820; decide +kernel
    rw [ha]
    exact (canonical33820 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2462 + difference 2 0) (sourceB2462 + difference 0 2) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1680) := by
    have ha : (tripleCharges (sourceA2462 + difference 2 0) (sourceB2462 + difference 0 2) sourceC2462) = raw33821 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33821; decide +kernel
    rw [ha]
    exact (canonical33821 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2462 + difference 2 1) (sourceB2462 + difference 1 2) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2156) := by
    have ha : (tripleCharges (sourceA2462 + difference 2 1) (sourceB2462 + difference 1 2) sourceC2462) = raw33822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33822; decide +kernel
    rw [ha]
    exact (canonical33822 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2462 + difference 2 3) (sourceB2462 + difference 3 2) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA2462 + difference 2 3) (sourceB2462 + difference 3 2) sourceC2462) = raw33823 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33823; decide +kernel
    rw [ha]
    exact (canonical33823 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2462 + difference 2 4) (sourceB2462 + difference 4 2) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA2462 + difference 2 4) (sourceB2462 + difference 4 2) sourceC2462) = raw33824 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33824; decide +kernel
    rw [ha]
    exact (canonical33824 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2462 + difference 2 5) (sourceB2462 + difference 5 2) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2204) := by
    have ha : (tripleCharges (sourceA2462 + difference 2 5) (sourceB2462 + difference 5 2) sourceC2462) = raw33825 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33825; decide +kernel
    rw [ha]
    exact (canonical33825 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2462 + difference 3 0) (sourceB2462 + difference 0 3) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1678) := by
    have ha : (tripleCharges (sourceA2462 + difference 3 0) (sourceB2462 + difference 0 3) sourceC2462) = raw33826 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33826; decide +kernel
    rw [ha]
    exact (canonical33826 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2462 + difference 3 1) (sourceB2462 + difference 1 3) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2154) := by
    have ha : (tripleCharges (sourceA2462 + difference 3 1) (sourceB2462 + difference 1 3) sourceC2462) = raw33827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33827; decide +kernel
    rw [ha]
    exact (canonical33827 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2462 + difference 3 2) (sourceB2462 + difference 2 3) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2211) := by
    have ha : (tripleCharges (sourceA2462 + difference 3 2) (sourceB2462 + difference 2 3) sourceC2462) = raw33828 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33828; decide +kernel
    rw [ha]
    exact (canonical33828 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2462 + difference 3 4) (sourceB2462 + difference 4 3) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA2462 + difference 3 4) (sourceB2462 + difference 4 3) sourceC2462) = raw33829 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33829; decide +kernel
    rw [ha]
    exact (canonical33829 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2462 + difference 3 5) (sourceB2462 + difference 5 3) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA2462 + difference 3 5) (sourceB2462 + difference 5 3) sourceC2462) = raw33830 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33830; decide +kernel
    rw [ha]
    exact (canonical33830 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2462 + difference 4 0) (sourceB2462 + difference 0 4) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1678) := by
    have ha : (tripleCharges (sourceA2462 + difference 4 0) (sourceB2462 + difference 0 4) sourceC2462) = raw33831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33831; decide +kernel
    rw [ha]
    exact (canonical33831 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2462 + difference 4 1) (sourceB2462 + difference 1 4) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2154) := by
    have ha : (tripleCharges (sourceA2462 + difference 4 1) (sourceB2462 + difference 1 4) sourceC2462) = raw33832 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33832; decide +kernel
    rw [ha]
    exact (canonical33832 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2462 + difference 4 2) (sourceB2462 + difference 2 4) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2211) := by
    have ha : (tripleCharges (sourceA2462 + difference 4 2) (sourceB2462 + difference 2 4) sourceC2462) = raw33833 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33833; decide +kernel
    rw [ha]
    exact (canonical33833 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2462 + difference 4 3) (sourceB2462 + difference 3 4) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA2462 + difference 4 3) (sourceB2462 + difference 3 4) sourceC2462) = raw33834 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33834; decide +kernel
    rw [ha]
    exact (canonical33834 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2462 + difference 4 5) (sourceB2462 + difference 5 4) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA2462 + difference 4 5) (sourceB2462 + difference 5 4) sourceC2462) = raw33835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33835; decide +kernel
    rw [ha]
    exact (canonical33835 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2462 + difference 5 0) (sourceB2462 + difference 0 5) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1684) := by
    have ha : (tripleCharges (sourceA2462 + difference 5 0) (sourceB2462 + difference 0 5) sourceC2462) = raw33836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33836; decide +kernel
    rw [ha]
    exact (canonical33836 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2462 + difference 5 1) (sourceB2462 + difference 1 5) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2160) := by
    have ha : (tripleCharges (sourceA2462 + difference 5 1) (sourceB2462 + difference 1 5) sourceC2462) = raw33837 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33837; decide +kernel
    rw [ha]
    exact (canonical33837 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2462 + difference 5 2) (sourceB2462 + difference 2 5) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2179) := by
    have ha : (tripleCharges (sourceA2462 + difference 5 2) (sourceB2462 + difference 2 5) sourceC2462) = raw33838 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw33838; decide +kernel
    rw [ha]
    exact (canonical33838 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2462 + difference 5 3) (sourceB2462 + difference 3 5) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2219) := by
    have ha : (tripleCharges (sourceA2462 + difference 5 3) (sourceB2462 + difference 3 5) sourceC2462) = raw3819 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw3819; decide +kernel
    rw [ha]
    exact (canonical3819 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2462 + difference 5 4) (sourceB2462 + difference 4 5) sourceC2462) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2219) := by
    have ha : (tripleCharges (sourceA2462 + difference 5 4) (sourceB2462 + difference 4 5) sourceC2462) = raw3814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2462 sourceB2462 sourceC2462 difference raw3814; decide +kernel
    rw [ha]
    exact (canonical3814 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2462 sourceB2462 sourceC2462
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2462, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2463 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2463 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2463 + difference 0 1) (sourceB2463 + difference 1 0) sourceC2463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3378) := by
    have ha : (tripleCharges (sourceA2463 + difference 0 1) (sourceB2463 + difference 1 0) sourceC2463) = raw33839 := by
      apply Matrix.ext; unfold tripleCharges sourceA2463 sourceB2463 sourceC2463 difference raw33839; decide +kernel
    rw [ha]
    exact (canonical33839 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2463 + difference 1 1) (sourceB2463 + difference 1 1) sourceC2463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2023) := by
    have ha : (tripleCharges (sourceA2463 + difference 1 1) (sourceB2463 + difference 1 1) sourceC2463) = raw33840 := by
      apply Matrix.ext; unfold tripleCharges sourceA2463 sourceB2463 sourceC2463 difference raw33840; decide +kernel
    rw [ha]
    exact (canonical33840 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2463 + difference 2 1) (sourceB2463 + difference 1 2) sourceC2463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1811) := by
    have ha : (tripleCharges (sourceA2463 + difference 2 1) (sourceB2463 + difference 1 2) sourceC2463) = raw33841 := by
      apply Matrix.ext; unfold tripleCharges sourceA2463 sourceB2463 sourceC2463 difference raw33841; decide +kernel
    rw [ha]
    exact (canonical33841 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2463 + difference 3 1) (sourceB2463 + difference 1 3) sourceC2463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1794) := by
    have ha : (tripleCharges (sourceA2463 + difference 3 1) (sourceB2463 + difference 1 3) sourceC2463) = raw33842 := by
      apply Matrix.ext; unfold tripleCharges sourceA2463 sourceB2463 sourceC2463 difference raw33842; decide +kernel
    rw [ha]
    exact (canonical33842 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2463 + difference 4 1) (sourceB2463 + difference 1 4) sourceC2463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1794) := by
    have ha : (tripleCharges (sourceA2463 + difference 4 1) (sourceB2463 + difference 1 4) sourceC2463) = raw33843 := by
      apply Matrix.ext; unfold tripleCharges sourceA2463 sourceB2463 sourceC2463 difference raw33843; decide +kernel
    rw [ha]
    exact (canonical33843 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2463 + difference 5 1) (sourceB2463 + difference 1 5) sourceC2463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1793) := by
    have ha : (tripleCharges (sourceA2463 + difference 5 1) (sourceB2463 + difference 1 5) sourceC2463) = raw33844 := by
      apply Matrix.ext; unfold tripleCharges sourceA2463 sourceB2463 sourceC2463 difference raw33844; decide +kernel
    rw [ha]
    exact (canonical33844 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2463 + sourceB2463) sourceC2463) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2463 + sourceB2463) sourceC2463) = raw3834 := by
      apply Matrix.ext; unfold doubleCharges sourceA2463 sourceB2463 sourceC2463 raw3834; decide +kernel
    rw [ha]
    exact (canonical3834 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2463 sourceB2463 sourceC2463
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2463, Integer.Sparse.eval]
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

theorem reindexCheck1973 : Integer.Sparse.reindex keyMap MixedData.row1973 = numericRow1973 := by decide +kernel

theorem numericCheck1973 (x : Master → ℝ) : Integer.Sparse.eval numericRow1973 x =
    (1 : ℝ) * reducedSource1973 x := by
  norm_num [numericRow1973, reducedSource1973, Integer.Sparse.eval, Sparse.eval, nodeValue1697, nodeValue1704, nodeValue1707, nodeValue1712, nodeValue2189, nodeValue2190, nodeValue2194, nodeValue2231, nodeValue2232, nodeValue2239, nodeValue2242, nodeValue2244, nodeValue2249, nodeValue2251, nodeValue2261, nodeValue2264, nodeValue2276, nodeValue2708, nodeValue2748, nodeValue2751, nodeValue2765]

theorem reindexCheck1974 : Integer.Sparse.reindex keyMap MixedData.row1974 = numericRow1974 := by decide +kernel

theorem numericCheck1974 (x : Master → ℝ) : Integer.Sparse.eval numericRow1974 x =
    (1 : ℝ) * reducedSource1974 x := by
  norm_num [numericRow1974, reducedSource1974, Integer.Sparse.eval, Sparse.eval, nodeValue1821, nodeValue1823, nodeValue1826, nodeValue2106, nodeValue3050, nodeValue4084]

theorem reindexCheck1975 : Integer.Sparse.reindex keyMap MixedData.row1975 = numericRow1975 := by decide +kernel

theorem numericCheck1975 (x : Master → ℝ) : Integer.Sparse.eval numericRow1975 x =
    (1 : ℝ) * reducedSource1975 x := by
  norm_num [numericRow1975, reducedSource1975, Integer.Sparse.eval, Sparse.eval, nodeValue941, nodeValue1821, nodeValue2104, nodeValue2106, nodeValue4084]

theorem reindexCheck1979 : Integer.Sparse.reindex keyMap MixedData.row1979 = numericRow1979 := by decide +kernel

theorem numericCheck1979 (x : Master → ℝ) : Integer.Sparse.eval numericRow1979 x =
    (1 : ℝ) * reducedSource1979 x := by
  norm_num [numericRow1979, reducedSource1979, Integer.Sparse.eval, Sparse.eval, nodeValue1877, nodeValue1879, nodeValue1912, nodeValue2077, nodeValue3446, nodeValue4079]

theorem reindexCheck1980 : Integer.Sparse.reindex keyMap MixedData.row1980 = numericRow1980 := by decide +kernel

theorem numericCheck1980 (x : Master → ℝ) : Integer.Sparse.eval numericRow1980 x =
    (4 : ℝ) * reducedSource1980 x := by
  norm_num [numericRow1980, reducedSource1980, Integer.Sparse.eval, Sparse.eval, nodeValue4331, nodeValue4332, nodeValue4351, nodeValue4461, nodeValue4667, nodeValue4668, nodeValue4685, nodeValue4765, nodeValue4775, nodeValue4793, nodeValue4795, nodeValue4802, nodeValue4805, nodeValue4833, nodeValue4869, nodeValue4889, nodeValue4893, nodeValue5231, nodeValue5257, nodeValue5263, nodeValue5265]
  ring

theorem reindexCheck1981 : Integer.Sparse.reindex keyMap MixedData.row1981 = numericRow1981 := by decide +kernel

theorem numericCheck1981 (x : Master → ℝ) : Integer.Sparse.eval numericRow1981 x =
    (1 : ℝ) * reducedSource1981 x := by
  norm_num [numericRow1981, reducedSource1981, Integer.Sparse.eval, Sparse.eval, nodeValue1678, nodeValue1680, nodeValue1684, nodeValue1737, nodeValue2154, nodeValue2156, nodeValue2160, nodeValue2179, nodeValue2202, nodeValue2204, nodeValue2211, nodeValue2213, nodeValue2214, nodeValue2219, nodeValue2263, nodeValue2275, nodeValue2277, nodeValue2676, nodeValue2721, nodeValue2728, nodeValue2730]

theorem reindexCheck1982 : Integer.Sparse.reindex keyMap MixedData.row1982 = numericRow1982 := by decide +kernel

theorem numericCheck1982 (x : Master → ℝ) : Integer.Sparse.eval numericRow1982 x =
    (1 : ℝ) * reducedSource1982 x := by
  norm_num [numericRow1982, reducedSource1982, Integer.Sparse.eval, Sparse.eval, nodeValue1793, nodeValue1794, nodeValue1811, nodeValue2023, nodeValue3378, nodeValue4083]

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

theorem reducedZero1973 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1973 (mixedVector B) = 0 := by
  have h1697 : mixedVector B (Sum.inr 1697) = Sparse.eval nodeValue1697 (mixedVector B) := by
    change mixedMoment B node1697 node1697Labels = _
    exact sound1697 B hB hF
  have h1704 : mixedVector B (Sum.inr 1704) = Sparse.eval nodeValue1704 (mixedVector B) := by
    change mixedMoment B node1704 node1704Labels = _
    exact sound1704 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h1712 : mixedVector B (Sum.inr 1712) = Sparse.eval nodeValue1712 (mixedVector B) := by
    change mixedMoment B node1712 node1712Labels = _
    exact sound1712 B hB hF
  have h2189 : mixedVector B (Sum.inr 2189) = Sparse.eval nodeValue2189 (mixedVector B) := by
    change mixedMoment B node2189 node2189Labels = _
    exact sound2189 B hB hF
  have h2190 : mixedVector B (Sum.inr 2190) = Sparse.eval nodeValue2190 (mixedVector B) := by
    change mixedMoment B node2190 node2190Labels = _
    exact sound2190 B hB hF
  have h2194 : mixedVector B (Sum.inr 2194) = Sparse.eval nodeValue2194 (mixedVector B) := by
    change mixedMoment B node2194 node2194Labels = _
    exact sound2194 B hB hF
  have h2231 : mixedVector B (Sum.inr 2231) = Sparse.eval nodeValue2231 (mixedVector B) := by
    change mixedMoment B node2231 node2231Labels = _
    exact sound2231 B hB hF
  have h2232 : mixedVector B (Sum.inr 2232) = Sparse.eval nodeValue2232 (mixedVector B) := by
    change mixedMoment B node2232 node2232Labels = _
    exact sound2232 B hB hF
  have h2239 : mixedVector B (Sum.inr 2239) = Sparse.eval nodeValue2239 (mixedVector B) := by
    change mixedMoment B node2239 node2239Labels = _
    exact sound2239 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
  have h2244 : mixedVector B (Sum.inr 2244) = Sparse.eval nodeValue2244 (mixedVector B) := by
    change mixedMoment B node2244 node2244Labels = _
    exact sound2244 B hB hF
  have h2249 : mixedVector B (Sum.inr 2249) = Sparse.eval nodeValue2249 (mixedVector B) := by
    change mixedMoment B node2249 node2249Labels = _
    exact sound2249 B hB hF
  have h2251 : mixedVector B (Sum.inr 2251) = Sparse.eval nodeValue2251 (mixedVector B) := by
    change mixedMoment B node2251 node2251Labels = _
    exact sound2251 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h2708 : mixedVector B (Sum.inr 2708) = Sparse.eval nodeValue2708 (mixedVector B) := by
    change mixedMoment B node2708 node2708Labels = _
    exact sound2708 B hB hF
  have h2748 : mixedVector B (Sum.inr 2748) = Sparse.eval nodeValue2748 (mixedVector B) := by
    change mixedMoment B node2748 node2748Labels = _
    exact sound2748 B hB hF
  have h2751 : mixedVector B (Sum.inr 2751) = Sparse.eval nodeValue2751 (mixedVector B) := by
    change mixedMoment B node2751 node2751Labels = _
    exact sound2751 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  simpa only [sourceForm2453, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1697, h1704, h1707, h1712, h2189, h2190, h2194, h2231, h2232, h2239, h2242, h2244, h2249, h2251, h2261, h2264, h2276, h2708, h2748, h2751, h2765, reducedSource1973] using sourceEq2453 B hB

theorem rowSound1973 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1973 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1973, numericCheck1973, reducedZero1973 B hB hF, mul_zero]

theorem reducedZero1974 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1974 (mixedVector B) = 0 := by
  have h1821 : mixedVector B (Sum.inr 1821) = Sparse.eval nodeValue1821 (mixedVector B) := by
    change mixedMoment B node1821 node1821Labels = _
    exact sound1821 B hB hF
  have h1823 : mixedVector B (Sum.inr 1823) = Sparse.eval nodeValue1823 (mixedVector B) := by
    change mixedMoment B node1823 node1823Labels = _
    exact sound1823 B hB hF
  have h1826 : mixedVector B (Sum.inr 1826) = Sparse.eval nodeValue1826 (mixedVector B) := by
    change mixedMoment B node1826 node1826Labels = _
    exact sound1826 B hB hF
  have h2106 : mixedVector B (Sum.inr 2106) = Sparse.eval nodeValue2106 (mixedVector B) := by
    change mixedMoment B node2106 node2106Labels = _
    exact sound2106 B hB hF
  have h3050 : mixedVector B (Sum.inr 3050) = Sparse.eval nodeValue3050 (mixedVector B) := by
    change mixedMoment B node3050 node3050Labels = _
    exact sound3050 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2454, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1821, h1823, h1826, h2106, h3050, h4084, reducedSource1974] using sourceEq2454 B hB

theorem rowSound1974 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1974 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1974, numericCheck1974, reducedZero1974 B hB hF, mul_zero]

theorem reducedZero1975 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1975 (mixedVector B) = 0 := by
  have h941 : mixedVector B (Sum.inr 941) = Sparse.eval nodeValue941 (mixedVector B) := by
    change mixedMoment B node941 node941Labels = _
    exact sound941 B hB hF
  have h1821 : mixedVector B (Sum.inr 1821) = Sparse.eval nodeValue1821 (mixedVector B) := by
    change mixedMoment B node1821 node1821Labels = _
    exact sound1821 B hB hF
  have h2104 : mixedVector B (Sum.inr 2104) = Sparse.eval nodeValue2104 (mixedVector B) := by
    change mixedMoment B node2104 node2104Labels = _
    exact sound2104 B hB hF
  have h2106 : mixedVector B (Sum.inr 2106) = Sparse.eval nodeValue2106 (mixedVector B) := by
    change mixedMoment B node2106 node2106Labels = _
    exact sound2106 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2455, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h941, h1821, h2104, h2106, h4084, reducedSource1975] using sourceEq2455 B hB

theorem rowSound1975 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1975 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1975, numericCheck1975, reducedZero1975 B hB hF, mul_zero]

theorem reducedZero1979 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1979 (mixedVector B) = 0 := by
  have h1877 : mixedVector B (Sum.inr 1877) = Sparse.eval nodeValue1877 (mixedVector B) := by
    change mixedMoment B node1877 node1877Labels = _
    exact sound1877 B hB hF
  have h1879 : mixedVector B (Sum.inr 1879) = Sparse.eval nodeValue1879 (mixedVector B) := by
    change mixedMoment B node1879 node1879Labels = _
    exact sound1879 B hB hF
  have h1912 : mixedVector B (Sum.inr 1912) = Sparse.eval nodeValue1912 (mixedVector B) := by
    change mixedMoment B node1912 node1912Labels = _
    exact sound1912 B hB hF
  have h2077 : mixedVector B (Sum.inr 2077) = Sparse.eval nodeValue2077 (mixedVector B) := by
    change mixedMoment B node2077 node2077Labels = _
    exact sound2077 B hB hF
  have h3446 : mixedVector B (Sum.inr 3446) = Sparse.eval nodeValue3446 (mixedVector B) := by
    change mixedMoment B node3446 node3446Labels = _
    exact sound3446 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm2460, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1877, h1879, h1912, h2077, h3446, h4079, reducedSource1979] using sourceEq2460 B hB

theorem rowSound1979 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1979 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1979, numericCheck1979, reducedZero1979 B hB hF, mul_zero]

theorem reducedZero1980 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1980 (mixedVector B) = 0 := by
  have h4331 : mixedVector B (Sum.inr 4331) = Sparse.eval nodeValue4331 (mixedVector B) := by
    change mixedMoment B node4331 node4331Labels = _
    exact sound4331 B hB hF
  have h4332 : mixedVector B (Sum.inr 4332) = Sparse.eval nodeValue4332 (mixedVector B) := by
    change mixedMoment B node4332 node4332Labels = _
    exact sound4332 B hB hF
  have h4351 : mixedVector B (Sum.inr 4351) = Sparse.eval nodeValue4351 (mixedVector B) := by
    change mixedMoment B node4351 node4351Labels = _
    exact sound4351 B hB hF
  have h4461 : mixedVector B (Sum.inr 4461) = Sparse.eval nodeValue4461 (mixedVector B) := by
    change mixedMoment B node4461 node4461Labels = _
    exact sound4461 B hB hF
  have h4667 : mixedVector B (Sum.inr 4667) = Sparse.eval nodeValue4667 (mixedVector B) := by
    change mixedMoment B node4667 node4667Labels = _
    exact sound4667 B hB hF
  have h4668 : mixedVector B (Sum.inr 4668) = Sparse.eval nodeValue4668 (mixedVector B) := by
    change mixedMoment B node4668 node4668Labels = _
    exact sound4668 B hB hF
  have h4685 : mixedVector B (Sum.inr 4685) = Sparse.eval nodeValue4685 (mixedVector B) := by
    change mixedMoment B node4685 node4685Labels = _
    exact sound4685 B hB hF
  have h4765 : mixedVector B (Sum.inr 4765) = Sparse.eval nodeValue4765 (mixedVector B) := by
    change mixedMoment B node4765 node4765Labels = _
    exact sound4765 B hB hF
  have h4775 : mixedVector B (Sum.inr 4775) = Sparse.eval nodeValue4775 (mixedVector B) := by
    change mixedMoment B node4775 node4775Labels = _
    exact sound4775 B hB hF
  have h4793 : mixedVector B (Sum.inr 4793) = Sparse.eval nodeValue4793 (mixedVector B) := by
    change mixedMoment B node4793 node4793Labels = _
    exact sound4793 B hB hF
  have h4795 : mixedVector B (Sum.inr 4795) = Sparse.eval nodeValue4795 (mixedVector B) := by
    change mixedMoment B node4795 node4795Labels = _
    exact sound4795 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4833 : mixedVector B (Sum.inr 4833) = Sparse.eval nodeValue4833 (mixedVector B) := by
    change mixedMoment B node4833 node4833Labels = _
    exact sound4833 B hB hF
  have h4869 : mixedVector B (Sum.inr 4869) = Sparse.eval nodeValue4869 (mixedVector B) := by
    change mixedMoment B node4869 node4869Labels = _
    exact sound4869 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h4893 : mixedVector B (Sum.inr 4893) = Sparse.eval nodeValue4893 (mixedVector B) := by
    change mixedMoment B node4893 node4893Labels = _
    exact sound4893 B hB hF
  have h5231 : mixedVector B (Sum.inr 5231) = Sparse.eval nodeValue5231 (mixedVector B) := by
    change mixedMoment B node5231 node5231Labels = _
    exact sound5231 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5263 : mixedVector B (Sum.inr 5263) = Sparse.eval nodeValue5263 (mixedVector B) := by
    change mixedMoment B node5263 node5263Labels = _
    exact sound5263 B hB hF
  have h5265 : mixedVector B (Sum.inr 5265) = Sparse.eval nodeValue5265 (mixedVector B) := by
    change mixedMoment B node5265 node5265Labels = _
    exact sound5265 B hB hF
  simpa only [sourceForm2461, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4331, h4332, h4351, h4461, h4667, h4668, h4685, h4765, h4775, h4793, h4795, h4802, h4805, h4833, h4869, h4889, h4893, h5231, h5257, h5263, h5265, reducedSource1980] using sourceEq2461 B hB

theorem rowSound1980 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1980 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1980, numericCheck1980, reducedZero1980 B hB hF, mul_zero]

theorem reducedZero1981 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1981 (mixedVector B) = 0 := by
  have h1678 : mixedVector B (Sum.inr 1678) = Sparse.eval nodeValue1678 (mixedVector B) := by
    change mixedMoment B node1678 node1678Labels = _
    exact sound1678 B hB hF
  have h1680 : mixedVector B (Sum.inr 1680) = Sparse.eval nodeValue1680 (mixedVector B) := by
    change mixedMoment B node1680 node1680Labels = _
    exact sound1680 B hB hF
  have h1684 : mixedVector B (Sum.inr 1684) = Sparse.eval nodeValue1684 (mixedVector B) := by
    change mixedMoment B node1684 node1684Labels = _
    exact sound1684 B hB hF
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h2154 : mixedVector B (Sum.inr 2154) = Sparse.eval nodeValue2154 (mixedVector B) := by
    change mixedMoment B node2154 node2154Labels = _
    exact sound2154 B hB hF
  have h2156 : mixedVector B (Sum.inr 2156) = Sparse.eval nodeValue2156 (mixedVector B) := by
    change mixedMoment B node2156 node2156Labels = _
    exact sound2156 B hB hF
  have h2160 : mixedVector B (Sum.inr 2160) = Sparse.eval nodeValue2160 (mixedVector B) := by
    change mixedMoment B node2160 node2160Labels = _
    exact sound2160 B hB hF
  have h2179 : mixedVector B (Sum.inr 2179) = Sparse.eval nodeValue2179 (mixedVector B) := by
    change mixedMoment B node2179 node2179Labels = _
    exact sound2179 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h2204 : mixedVector B (Sum.inr 2204) = Sparse.eval nodeValue2204 (mixedVector B) := by
    change mixedMoment B node2204 node2204Labels = _
    exact sound2204 B hB hF
  have h2211 : mixedVector B (Sum.inr 2211) = Sparse.eval nodeValue2211 (mixedVector B) := by
    change mixedMoment B node2211 node2211Labels = _
    exact sound2211 B hB hF
  have h2213 : mixedVector B (Sum.inr 2213) = Sparse.eval nodeValue2213 (mixedVector B) := by
    change mixedMoment B node2213 node2213Labels = _
    exact sound2213 B hB hF
  have h2214 : mixedVector B (Sum.inr 2214) = Sparse.eval nodeValue2214 (mixedVector B) := by
    change mixedMoment B node2214 node2214Labels = _
    exact sound2214 B hB hF
  have h2219 : mixedVector B (Sum.inr 2219) = Sparse.eval nodeValue2219 (mixedVector B) := by
    change mixedMoment B node2219 node2219Labels = _
    exact sound2219 B hB hF
  have h2263 : mixedVector B (Sum.inr 2263) = Sparse.eval nodeValue2263 (mixedVector B) := by
    change mixedMoment B node2263 node2263Labels = _
    exact sound2263 B hB hF
  have h2275 : mixedVector B (Sum.inr 2275) = Sparse.eval nodeValue2275 (mixedVector B) := by
    change mixedMoment B node2275 node2275Labels = _
    exact sound2275 B hB hF
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  have h2676 : mixedVector B (Sum.inr 2676) = Sparse.eval nodeValue2676 (mixedVector B) := by
    change mixedMoment B node2676 node2676Labels = _
    exact sound2676 B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h2728 : mixedVector B (Sum.inr 2728) = Sparse.eval nodeValue2728 (mixedVector B) := by
    change mixedMoment B node2728 node2728Labels = _
    exact sound2728 B hB hF
  have h2730 : mixedVector B (Sum.inr 2730) = Sparse.eval nodeValue2730 (mixedVector B) := by
    change mixedMoment B node2730 node2730Labels = _
    exact sound2730 B hB hF
  simpa only [sourceForm2462, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1678, h1680, h1684, h1737, h2154, h2156, h2160, h2179, h2202, h2204, h2211, h2213, h2214, h2219, h2263, h2275, h2277, h2676, h2721, h2728, h2730, reducedSource1981] using sourceEq2462 B hB

theorem rowSound1981 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1981 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1981, numericCheck1981, reducedZero1981 B hB hF, mul_zero]

theorem reducedZero1982 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1982 (mixedVector B) = 0 := by
  have h1793 : mixedVector B (Sum.inr 1793) = Sparse.eval nodeValue1793 (mixedVector B) := by
    change mixedMoment B node1793 node1793Labels = _
    exact sound1793 B hB hF
  have h1794 : mixedVector B (Sum.inr 1794) = Sparse.eval nodeValue1794 (mixedVector B) := by
    change mixedMoment B node1794 node1794Labels = _
    exact sound1794 B hB hF
  have h1811 : mixedVector B (Sum.inr 1811) = Sparse.eval nodeValue1811 (mixedVector B) := by
    change mixedMoment B node1811 node1811Labels = _
    exact sound1811 B hB hF
  have h2023 : mixedVector B (Sum.inr 2023) = Sparse.eval nodeValue2023 (mixedVector B) := by
    change mixedMoment B node2023 node2023Labels = _
    exact sound2023 B hB hF
  have h3378 : mixedVector B (Sum.inr 3378) = Sparse.eval nodeValue3378 (mixedVector B) := by
    change mixedMoment B node3378 node3378Labels = _
    exact sound3378 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2463, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1793, h1794, h1811, h2023, h3378, h4083, reducedSource1982] using sourceEq2463 B hB

theorem rowSound1982 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1982 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1982, numericCheck1982, reducedZero1982 B hB hF, mul_zero]

theorem sourceRowsAt1968 : MixedData.sourceRows (1968 : Fin 2425) =
    MixedData.row1968 := by decide +kernel

theorem sourceRowsAt1969 : MixedData.sourceRows (1969 : Fin 2425) =
    MixedData.row1969 := by decide +kernel

theorem sourceRowsAt1970 : MixedData.sourceRows (1970 : Fin 2425) =
    MixedData.row1970 := by decide +kernel

theorem sourceRowsAt1971 : MixedData.sourceRows (1971 : Fin 2425) =
    MixedData.row1971 := by decide +kernel

theorem sourceRowsAt1972 : MixedData.sourceRows (1972 : Fin 2425) =
    MixedData.row1972 := by decide +kernel

theorem sourceRowsAt1973 : MixedData.sourceRows (1973 : Fin 2425) =
    MixedData.row1973 := by decide +kernel

theorem sourceRowsAt1974 : MixedData.sourceRows (1974 : Fin 2425) =
    MixedData.row1974 := by decide +kernel

theorem sourceRowsAt1975 : MixedData.sourceRows (1975 : Fin 2425) =
    MixedData.row1975 := by decide +kernel

theorem sourceRowsAt1976 : MixedData.sourceRows (1976 : Fin 2425) =
    MixedData.row1976 := by decide +kernel

theorem sourceRowsAt1977 : MixedData.sourceRows (1977 : Fin 2425) =
    MixedData.row1977 := by decide +kernel

theorem sourceRowsAt1978 : MixedData.sourceRows (1978 : Fin 2425) =
    MixedData.row1978 := by decide +kernel

theorem sourceRowsAt1979 : MixedData.sourceRows (1979 : Fin 2425) =
    MixedData.row1979 := by decide +kernel

theorem sourceRowsAt1980 : MixedData.sourceRows (1980 : Fin 2425) =
    MixedData.row1980 := by decide +kernel

theorem sourceRowsAt1981 : MixedData.sourceRows (1981 : Fin 2425) =
    MixedData.row1981 := by decide +kernel

theorem sourceRowsAt1982 : MixedData.sourceRows (1982 : Fin 2425) =
    MixedData.row1982 := by decide +kernel

theorem sourceRowsAt1983 : MixedData.sourceRows (1983 : Fin 2425) =
    MixedData.row1983 := by decide +kernel

theorem chunkSound123_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 123) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1968 ∨ k.val = 1969 ∨ k.val = 1970 ∨ k.val = 1971 ∨ k.val = 1972 ∨ k.val = 1973 ∨ k.val = 1974 ∨ k.val = 1975 ∨ k.val = 1976 ∨ k.val = 1977 ∨ k.val = 1978 ∨ k.val = 1979 ∨ k.val = 1980 ∨ k.val = 1981 ∨ k.val = 1982 ∨ k.val = 1983 := by omega
  rcases heq with h1968 | h1969 | h1970 | h1971 | h1972 | h1973 | h1974 | h1975 | h1976 | h1977 | h1978 | h1979 | h1980 | h1981 | h1982 | h1983
  · have he : k = (1968 : Fin 2425) := Fin.ext h1968
    subst k
    rw [sourceRowsAt1968]
    exact rowSound1968_e B hB hF
  · have he : k = (1969 : Fin 2425) := Fin.ext h1969
    subst k
    rw [sourceRowsAt1969]
    exact rowSound1969_e B hB hF
  · have he : k = (1970 : Fin 2425) := Fin.ext h1970
    subst k
    rw [sourceRowsAt1970]
    exact rowSound1970_e B hB hF
  · have he : k = (1971 : Fin 2425) := Fin.ext h1971
    subst k
    rw [sourceRowsAt1971]
    exact rowSound1971_e B hB hF
  · have he : k = (1972 : Fin 2425) := Fin.ext h1972
    subst k
    rw [sourceRowsAt1972]
    exact rowSound1972_e B hB hF
  · have he : k = (1973 : Fin 2425) := Fin.ext h1973
    subst k
    rw [sourceRowsAt1973]
    exact rowSound1973 B hB hF
  · have he : k = (1974 : Fin 2425) := Fin.ext h1974
    subst k
    rw [sourceRowsAt1974]
    exact rowSound1974 B hB hF
  · have he : k = (1975 : Fin 2425) := Fin.ext h1975
    subst k
    rw [sourceRowsAt1975]
    exact rowSound1975 B hB hF
  · have he : k = (1976 : Fin 2425) := Fin.ext h1976
    subst k
    rw [sourceRowsAt1976]
    exact rowSound1976_e B hB hF
  · have he : k = (1977 : Fin 2425) := Fin.ext h1977
    subst k
    rw [sourceRowsAt1977]
    exact rowSound1977_e B hB hF
  · have he : k = (1978 : Fin 2425) := Fin.ext h1978
    subst k
    rw [sourceRowsAt1978]
    exact rowSound1978_e B hB hF
  · have he : k = (1979 : Fin 2425) := Fin.ext h1979
    subst k
    rw [sourceRowsAt1979]
    exact rowSound1979 B hB hF
  · have he : k = (1980 : Fin 2425) := Fin.ext h1980
    subst k
    rw [sourceRowsAt1980]
    exact rowSound1980 B hB hF
  · have he : k = (1981 : Fin 2425) := Fin.ext h1981
    subst k
    rw [sourceRowsAt1981]
    exact rowSound1981 B hB hF
  · have he : k = (1982 : Fin 2425) := Fin.ext h1982
    subst k
    rw [sourceRowsAt1982]
    exact rowSound1982 B hB hF
  · have he : k = (1983 : Fin 2425) := Fin.ext h1983
    subst k
    rw [sourceRowsAt1983]
    exact rowSound1983_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123_e_oai
