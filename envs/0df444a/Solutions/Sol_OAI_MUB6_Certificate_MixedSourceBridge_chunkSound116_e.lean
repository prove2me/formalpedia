-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:40:11.620254+00:00
-- url     : https://prove2.me/submissions/4a1f8724-17dd-4bbe-bf08-e0a336c10de6

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1856_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1858_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1859_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1864_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1866_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1871_e

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

theorem canonical1701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1701 raw1701Labels = mixedMoment B node4767 node4767Labels := by
  calc
    mixedMoment B raw1701 raw1701Labels = mixedMoment B raw1701step0 raw1701step0Labels := by
      have ha : raw1701step0 = (fun i j => raw1701 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1701step0 raw1701; decide +kernel
      have hl : raw1701step0Labels = raw1701Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1701 raw1701Labels permutation152 permutation4
    mixedMoment B raw1701step0 raw1701step0Labels = mixedMoment B raw1701step1 raw1701step1Labels := by
      have ha : raw1701step1 = raw1701step0 := by apply Matrix.ext; unfold raw1701step1 raw1701step0; decide +kernel
      have hl : raw1701step0Labels = labelEmbedding7 ∘ raw1701step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1701step0 raw1701step0Labels raw1701step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4767 node4767Labels := by rfl

theorem canonical1702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1702 raw1702Labels = mixedMoment B node1967 node1967Labels := by
  calc
    mixedMoment B raw1702 raw1702Labels = mixedMoment B raw1702step0 raw1702step0Labels := by
      have ha : raw1702step0 = (fun i j => raw1702 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1702step0 raw1702; decide +kernel
      have hl : raw1702step0Labels = raw1702Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1702 raw1702Labels permutation152 permutation4
    _ = mixedMoment B node1967 node1967Labels := by rfl

theorem canonical1703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1703 raw1703Labels = mixedMoment B node2183 node2183Labels := by
  calc
    mixedMoment B raw1703 raw1703Labels = mixedMoment B raw1703step0 raw1703step0Labels := by
      have ha : raw1703step0 = (fun i j => raw1703 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1703step0 raw1703; decide +kernel
      have hl : raw1703step0Labels = raw1703Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1703 raw1703Labels permutation152 permutation6
    mixedMoment B raw1703step0 raw1703step0Labels = mixedMoment B raw1703step1 raw1703step1Labels := by
      have ha : raw1703step1 = -raw1703step0 := by apply Matrix.ext; change ∀ i j, raw1703step1 i j = -(raw1703step0 i j); unfold raw1703step1 raw1703step0; decide +kernel
      have hl : raw1703step1Labels = raw1703step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1703step1 raw1703step1Labels = mixedMoment B raw1703step2 raw1703step2Labels := by
      have ha : raw1703step2 = raw1703step1 := by apply Matrix.ext; unfold raw1703step2 raw1703step1; decide +kernel
      have hl : raw1703step1Labels = labelEmbedding1 ∘ raw1703step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1703step1 raw1703step1Labels raw1703step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2183 node2183Labels := by rfl

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

theorem canonical1743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1743 raw1743Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw1743 raw1743Labels = mixedMoment B raw1743step0 raw1743step0Labels := by
      have ha : raw1743step0 = (fun i j => raw1743 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1743step0 raw1743; decide +kernel
      have hl : raw1743step0Labels = raw1743Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1743 raw1743Labels permutation32 permutation4
    mixedMoment B raw1743step0 raw1743step0Labels = mixedMoment B raw1743step1 raw1743step1Labels := by
      have ha : raw1743step1 = raw1743step0 := by apply Matrix.ext; unfold raw1743step1 raw1743step0; decide +kernel
      have hl : raw1743step0Labels = labelEmbedding7 ∘ raw1743step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1743step0 raw1743step0Labels raw1743step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical1744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1744 raw1744Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw1744 raw1744Labels = mixedMoment B raw1744step0 raw1744step0Labels := by
      have ha : raw1744step0 = (fun i j => raw1744 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1744step0 raw1744; decide +kernel
      have hl : raw1744step0Labels = raw1744Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1744 raw1744Labels permutation32 permutation4
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical1745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1745 raw1745Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw1745 raw1745Labels = mixedMoment B raw1745step0 raw1745step0Labels := by
      have ha : raw1745step0 = (fun i j => raw1745 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1745step0 raw1745; decide +kernel
      have hl : raw1745step0Labels = raw1745Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1745 raw1745Labels permutation32 permutation6
    mixedMoment B raw1745step0 raw1745step0Labels = mixedMoment B raw1745step1 raw1745step1Labels := by
      have ha : raw1745step1 = -raw1745step0 := by apply Matrix.ext; change ∀ i j, raw1745step1 i j = -(raw1745step0 i j); unfold raw1745step1 raw1745step0; decide +kernel
      have hl : raw1745step1Labels = raw1745step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1745step1 raw1745step1Labels = mixedMoment B raw1745step2 raw1745step2Labels := by
      have ha : raw1745step2 = raw1745step1 := by apply Matrix.ext; unfold raw1745step2 raw1745step1; decide +kernel
      have hl : raw1745step1Labels = labelEmbedding1 ∘ raw1745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1745step1 raw1745step1Labels raw1745step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21586 raw21586Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw21586 raw21586Labels = mixedMoment B raw21586step0 raw21586step0Labels := by
      have hz : ∀ j, raw21586 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21586step0 = (fun i j => raw21586 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21586step0 raw21586; decide +kernel
      have hl : raw21586step0Labels = raw21586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21586 raw21586Labels permutation346 hz
    mixedMoment B raw21586step0 raw21586step0Labels = mixedMoment B raw21586step1 raw21586step1Labels := by
      have ha : raw21586step1 = (fun i j => raw21586step0 (permutation39 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21586step1 raw21586step0; decide +kernel
      have hl : raw21586step1Labels = raw21586step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21586step0 raw21586step0Labels permutation39 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

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

theorem canonical2280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2280 raw2280Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw2280 raw2280Labels = mixedMoment B raw2280step0 raw2280step0Labels := by
      have ha : raw2280step0 = (fun i j => raw2280 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2280step0 raw2280; decide +kernel
      have hl : raw2280step0Labels = raw2280Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2280 raw2280Labels permutation32 permutation4
    mixedMoment B raw2280step0 raw2280step0Labels = mixedMoment B raw2280step1 raw2280step1Labels := by
      have ha : raw2280step1 = raw2280step0 := by apply Matrix.ext; unfold raw2280step1 raw2280step0; decide +kernel
      have hl : raw2280step0Labels = labelEmbedding7 ∘ raw2280step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2280step0 raw2280step0Labels raw2280step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical2281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2281 raw2281Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw2281 raw2281Labels = mixedMoment B raw2281step0 raw2281step0Labels := by
      have ha : raw2281step0 = (fun i j => raw2281 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2281step0 raw2281; decide +kernel
      have hl : raw2281step0Labels = raw2281Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2281 raw2281Labels permutation32 permutation4
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical2282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2282 raw2282Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw2282 raw2282Labels = mixedMoment B raw2282step0 raw2282step0Labels := by
      have ha : raw2282step0 = (fun i j => raw2282 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2282step0 raw2282; decide +kernel
      have hl : raw2282step0Labels = raw2282Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2282 raw2282Labels permutation32 permutation6
    mixedMoment B raw2282step0 raw2282step0Labels = mixedMoment B raw2282step1 raw2282step1Labels := by
      have ha : raw2282step1 = -raw2282step0 := by apply Matrix.ext; change ∀ i j, raw2282step1 i j = -(raw2282step0 i j); unfold raw2282step1 raw2282step0; decide +kernel
      have hl : raw2282step1Labels = raw2282step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2282step1 raw2282step1Labels = mixedMoment B raw2282step2 raw2282step2Labels := by
      have ha : raw2282step2 = raw2282step1 := by apply Matrix.ext; unfold raw2282step2 raw2282step1; decide +kernel
      have hl : raw2282step1Labels = labelEmbedding1 ∘ raw2282step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2282step1 raw2282step1Labels raw2282step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical182
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23315 raw23315Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw23315 raw23315Labels = mixedMoment B raw23315step0 raw23315step0Labels := by
      have hz : ∀ j, raw23315 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23315step0 = (fun i j => raw23315 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23315step0 raw23315; decide +kernel
      have hl : raw23315step0Labels = raw23315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23315 raw23315Labels permutation346 hz
    mixedMoment B raw23315step0 raw23315step0Labels = mixedMoment B raw23315step1 raw23315step1Labels := by
      have ha : raw23315step1 = (fun i j => raw23315step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23315step1 raw23315step0; decide +kernel
      have hl : raw23315step1Labels = raw23315step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23315step0 raw23315step0Labels permutation33 permutation2
    _ = mixedMoment B node2082 node2082Labels := by rfl

theorem canonical23317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23317 raw23317Labels = mixedMoment B node1918 node1918Labels := by
  calc
    mixedMoment B raw23317 raw23317Labels = mixedMoment B raw23317step0 raw23317step0Labels := by
      have hz : ∀ j, raw23317 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23317step0 = (fun i j => raw23317 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23317step0 raw23317; decide +kernel
      have hl : raw23317step0Labels = raw23317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23317 raw23317Labels permutation346 hz
    mixedMoment B raw23317step0 raw23317step0Labels = mixedMoment B raw23317step1 raw23317step1Labels := by
      have ha : raw23317step1 = (fun i j => raw23317step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23317step1 raw23317step0; decide +kernel
      have hl : raw23317step1Labels = raw23317step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23317step0 raw23317step0Labels permutation39 permutation2
    _ = mixedMoment B node1918 node1918Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical186
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23810 raw23810Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw23810 raw23810Labels = mixedMoment B raw23810step0 raw23810step0Labels := by
      have hz : ∀ j, raw23810 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw23810step0 = (fun i j => raw23810 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw23810step0 raw23810; decide +kernel
      have hl : raw23810step0Labels = raw23810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23810 raw23810Labels permutation590 hz
    mixedMoment B raw23810step0 raw23810step0Labels = mixedMoment B raw23810step1 raw23810step1Labels := by
      have hz : ∀ j, raw23810step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw23810step1 = (fun i j => raw23810step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw23810step1 raw23810step0; decide +kernel
      have hl : raw23810step1Labels = raw23810step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23810step0 raw23810step0Labels permutation104 hz
    mixedMoment B raw23810step1 raw23810step1Labels = mixedMoment B raw23810step2 raw23810step2Labels := by
      have hz : ∀ j, raw23810step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23810step2 = (fun i j => raw23810step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23810step2 raw23810step1; decide +kernel
      have hl : raw23810step2Labels = raw23810step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23810step1 raw23810step1Labels permutation14 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical244
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical31267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31267 raw31267Labels = mixedMoment B node3448 node3448Labels := by
  calc
    mixedMoment B raw31267 raw31267Labels = mixedMoment B raw31267step0 raw31267step0Labels := by
      have hz : ∀ j, raw31267 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31267step0 = (fun i j => raw31267 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31267step0 raw31267; decide +kernel
      have hl : raw31267step0Labels = raw31267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31267 raw31267Labels permutation346 hz
    mixedMoment B raw31267step0 raw31267step0Labels = mixedMoment B raw31267step1 raw31267step1Labels := by
      have ha : raw31267step1 = (fun i j => raw31267step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31267step1 raw31267step0; decide +kernel
      have hl : raw31267step1Labels = raw31267step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31267step0 raw31267step0Labels permutation39 permutation2
    _ = mixedMoment B node3448 node3448Labels := by rfl

theorem canonical31270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31270 raw31270Labels = mixedMoment B node1876 node1876Labels := by
  calc
    mixedMoment B raw31270 raw31270Labels = mixedMoment B raw31270step0 raw31270step0Labels := by
      have ha : raw31270step0 = (fun i j => raw31270 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31270step0 raw31270; decide +kernel
      have hl : raw31270step0Labels = raw31270Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31270 raw31270Labels permutation201 permutation2
    _ = mixedMoment B node1876 node1876Labels := by rfl

theorem canonical31271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31271 raw31271Labels = mixedMoment B node1880 node1880Labels := by
  calc
    mixedMoment B raw31271 raw31271Labels = mixedMoment B raw31271step0 raw31271step0Labels := by
      have hz : ∀ j, raw31271 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31271step0 = (fun i j => raw31271 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31271step0 raw31271; decide +kernel
      have hl : raw31271step0Labels = raw31271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31271 raw31271Labels permutation346 hz
    mixedMoment B raw31271step0 raw31271step0Labels = mixedMoment B raw31271step1 raw31271step1Labels := by
      have ha : raw31271step1 = (fun i j => raw31271step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31271step1 raw31271step0; decide +kernel
      have hl : raw31271step1Labels = raw31271step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31271step0 raw31271step0Labels permutation39 permutation2
    _ = mixedMoment B node1880 node1880Labels := by rfl

theorem canonical31272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31272 raw31272Labels = mixedMoment B node1881 node1881Labels := by
  calc
    mixedMoment B raw31272 raw31272Labels = mixedMoment B raw31272step0 raw31272step0Labels := by
      have hz : ∀ j, raw31272 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31272step0 = (fun i j => raw31272 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31272step0 raw31272; decide +kernel
      have hl : raw31272step0Labels = raw31272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31272 raw31272Labels permutation346 hz
    mixedMoment B raw31272step0 raw31272step0Labels = mixedMoment B raw31272step1 raw31272step1Labels := by
      have ha : raw31272step1 = (fun i j => raw31272step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31272step1 raw31272step0; decide +kernel
      have hl : raw31272step1Labels = raw31272step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31272step0 raw31272step0Labels permutation38 permutation2
    _ = mixedMoment B node1881 node1881Labels := by rfl

theorem canonical31336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31336 raw31336Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw31336 raw31336Labels = mixedMoment B raw31336step0 raw31336step0Labels := by
      have hz : ∀ j, raw31336 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31336step0 = (fun i j => raw31336 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31336step0 raw31336; decide +kernel
      have hl : raw31336step0Labels = raw31336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31336 raw31336Labels permutation434 hz
    mixedMoment B raw31336step0 raw31336step0Labels = mixedMoment B raw31336step1 raw31336step1Labels := by
      have ha : raw31336step1 = (fun i j => raw31336step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31336step1 raw31336step0; decide +kernel
      have hl : raw31336step1Labels = raw31336step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31336step0 raw31336step0Labels permutation36 permutation7
    mixedMoment B raw31336step1 raw31336step1Labels = mixedMoment B raw31336step2 raw31336step2Labels := by
      have ha : raw31336step2 = -raw31336step1 := by apply Matrix.ext; change ∀ i j, raw31336step2 i j = -(raw31336step1 i j); unfold raw31336step2 raw31336step1; decide +kernel
      have hl : raw31336step2Labels = raw31336step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31336step2 raw31336step2Labels = mixedMoment B raw31336step3 raw31336step3Labels := by
      have ha : raw31336step3 = raw31336step2 := by apply Matrix.ext; unfold raw31336step3 raw31336step2; decide +kernel
      have hl : raw31336step2Labels = labelEmbedding1 ∘ raw31336step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31336step2 raw31336step2Labels raw31336step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2677 node2677Labels := by rfl

theorem canonical31337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31337 raw31337Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw31337 raw31337Labels = mixedMoment B raw31337step0 raw31337step0Labels := by
      have hz : ∀ j, raw31337 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31337step0 = (fun i j => raw31337 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31337step0 raw31337; decide +kernel
      have hl : raw31337step0Labels = raw31337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31337 raw31337Labels permutation434 hz
    mixedMoment B raw31337step0 raw31337step0Labels = mixedMoment B raw31337step1 raw31337step1Labels := by
      have ha : raw31337step1 = (fun i j => raw31337step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31337step1 raw31337step0; decide +kernel
      have hl : raw31337step1Labels = raw31337step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31337step0 raw31337step0Labels permutation36 permutation7
    mixedMoment B raw31337step1 raw31337step1Labels = mixedMoment B raw31337step2 raw31337step2Labels := by
      have ha : raw31337step2 = -raw31337step1 := by apply Matrix.ext; change ∀ i j, raw31337step2 i j = -(raw31337step1 i j); unfold raw31337step2 raw31337step1; decide +kernel
      have hl : raw31337step2Labels = raw31337step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31337step2 raw31337step2Labels = mixedMoment B raw31337step3 raw31337step3Labels := by
      have ha : raw31337step3 = raw31337step2 := by apply Matrix.ext; unfold raw31337step3 raw31337step2; decide +kernel
      have hl : raw31337step2Labels = labelEmbedding1 ∘ raw31337step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31337step2 raw31337step2Labels raw31337step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2729 node2729Labels := by rfl

theorem canonical31338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31338 raw31338Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw31338 raw31338Labels = mixedMoment B raw31338step0 raw31338step0Labels := by
      have ha : raw31338step0 = (fun i j => raw31338 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31338step0 raw31338; decide +kernel
      have hl : raw31338step0Labels = raw31338Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31338 raw31338Labels permutation162 permutation7
    mixedMoment B raw31338step0 raw31338step0Labels = mixedMoment B raw31338step1 raw31338step1Labels := by
      have ha : raw31338step1 = -raw31338step0 := by apply Matrix.ext; change ∀ i j, raw31338step1 i j = -(raw31338step0 i j); unfold raw31338step1 raw31338step0; decide +kernel
      have hl : raw31338step1Labels = raw31338step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31338step1 raw31338step1Labels = mixedMoment B raw31338step2 raw31338step2Labels := by
      have ha : raw31338step2 = raw31338step1 := by apply Matrix.ext; unfold raw31338step2 raw31338step1; decide +kernel
      have hl : raw31338step1Labels = labelEmbedding1 ∘ raw31338step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31338step1 raw31338step1Labels raw31338step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2697 node2697Labels := by rfl

theorem canonical31339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31339 raw31339Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw31339 raw31339Labels = mixedMoment B raw31339step0 raw31339step0Labels := by
      have hz : ∀ j, raw31339 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31339step0 = (fun i j => raw31339 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31339step0 raw31339; decide +kernel
      have hl : raw31339step0Labels = raw31339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31339 raw31339Labels permutation434 hz
    mixedMoment B raw31339step0 raw31339step0Labels = mixedMoment B raw31339step1 raw31339step1Labels := by
      have ha : raw31339step1 = (fun i j => raw31339step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31339step1 raw31339step0; decide +kernel
      have hl : raw31339step1Labels = raw31339step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31339step0 raw31339step0Labels permutation36 permutation7
    mixedMoment B raw31339step1 raw31339step1Labels = mixedMoment B raw31339step2 raw31339step2Labels := by
      have ha : raw31339step2 = -raw31339step1 := by apply Matrix.ext; change ∀ i j, raw31339step2 i j = -(raw31339step1 i j); unfold raw31339step2 raw31339step1; decide +kernel
      have hl : raw31339step2Labels = raw31339step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31339step2 raw31339step2Labels = mixedMoment B raw31339step3 raw31339step3Labels := by
      have ha : raw31339step3 = raw31339step2 := by apply Matrix.ext; unfold raw31339step3 raw31339step2; decide +kernel
      have hl : raw31339step2Labels = labelEmbedding1 ∘ raw31339step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31339step2 raw31339step2Labels raw31339step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2731 node2731Labels := by rfl

theorem canonical31340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31340 raw31340Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw31340 raw31340Labels = mixedMoment B raw31340step0 raw31340step0Labels := by
      have hz : ∀ j, raw31340 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31340step0 = (fun i j => raw31340 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31340step0 raw31340; decide +kernel
      have hl : raw31340step0Labels = raw31340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31340 raw31340Labels permutation434 hz
    mixedMoment B raw31340step0 raw31340step0Labels = mixedMoment B raw31340step1 raw31340step1Labels := by
      have ha : raw31340step1 = (fun i j => raw31340step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31340step1 raw31340step0; decide +kernel
      have hl : raw31340step1Labels = raw31340step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31340step0 raw31340step0Labels permutation36 permutation7
    mixedMoment B raw31340step1 raw31340step1Labels = mixedMoment B raw31340step2 raw31340step2Labels := by
      have ha : raw31340step2 = -raw31340step1 := by apply Matrix.ext; change ∀ i j, raw31340step2 i j = -(raw31340step1 i j); unfold raw31340step2 raw31340step1; decide +kernel
      have hl : raw31340step2Labels = raw31340step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31340step2 raw31340step2Labels = mixedMoment B raw31340step3 raw31340step3Labels := by
      have ha : raw31340step3 = raw31340step2 := by apply Matrix.ext; unfold raw31340step3 raw31340step2; decide +kernel
      have hl : raw31340step2Labels = labelEmbedding1 ∘ raw31340step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31340step2 raw31340step2Labels raw31340step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical31341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31341 raw31341Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw31341 raw31341Labels = mixedMoment B raw31341step0 raw31341step0Labels := by
      have hz : ∀ j, raw31341 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31341step0 = (fun i j => raw31341 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31341step0 raw31341; decide +kernel
      have hl : raw31341step0Labels = raw31341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31341 raw31341Labels permutation434 hz
    mixedMoment B raw31341step0 raw31341step0Labels = mixedMoment B raw31341step1 raw31341step1Labels := by
      have hz : ∀ j, raw31341step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31341step1 = (fun i j => raw31341step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31341step1 raw31341step0; decide +kernel
      have hl : raw31341step1Labels = raw31341step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31341step0 raw31341step0Labels permutation56 hz
    mixedMoment B raw31341step1 raw31341step1Labels = mixedMoment B raw31341step2 raw31341step2Labels := by
      have ha : raw31341step2 = (fun i j => raw31341step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31341step2 raw31341step1; decide +kernel
      have hl : raw31341step2Labels = raw31341step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31341step1 raw31341step1Labels permutation12 permutation7
    mixedMoment B raw31341step2 raw31341step2Labels = mixedMoment B raw31341step3 raw31341step3Labels := by
      have ha : raw31341step3 = -raw31341step2 := by apply Matrix.ext; change ∀ i j, raw31341step3 i j = -(raw31341step2 i j); unfold raw31341step3 raw31341step2; decide +kernel
      have hl : raw31341step3Labels = raw31341step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31341step3 raw31341step3Labels = mixedMoment B raw31341step4 raw31341step4Labels := by
      have ha : raw31341step4 = raw31341step3 := by apply Matrix.ext; unfold raw31341step4 raw31341step3; decide +kernel
      have hl : raw31341step3Labels = labelEmbedding1 ∘ raw31341step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31341step3 raw31341step3Labels raw31341step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1738 node1738Labels := by rfl

theorem canonical31342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31342 raw31342Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw31342 raw31342Labels = mixedMoment B raw31342step0 raw31342step0Labels := by
      have hz : ∀ j, raw31342 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31342step0 = (fun i j => raw31342 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31342step0 raw31342; decide +kernel
      have hl : raw31342step0Labels = raw31342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31342 raw31342Labels permutation434 hz
    mixedMoment B raw31342step0 raw31342step0Labels = mixedMoment B raw31342step1 raw31342step1Labels := by
      have hz : ∀ j, raw31342step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31342step1 = (fun i j => raw31342step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31342step1 raw31342step0; decide +kernel
      have hl : raw31342step1Labels = raw31342step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31342step0 raw31342step0Labels permutation56 hz
    mixedMoment B raw31342step1 raw31342step1Labels = mixedMoment B raw31342step2 raw31342step2Labels := by
      have ha : raw31342step2 = (fun i j => raw31342step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31342step2 raw31342step1; decide +kernel
      have hl : raw31342step2Labels = raw31342step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31342step1 raw31342step1Labels permutation12 permutation7
    mixedMoment B raw31342step2 raw31342step2Labels = mixedMoment B raw31342step3 raw31342step3Labels := by
      have ha : raw31342step3 = -raw31342step2 := by apply Matrix.ext; change ∀ i j, raw31342step3 i j = -(raw31342step2 i j); unfold raw31342step3 raw31342step2; decide +kernel
      have hl : raw31342step3Labels = raw31342step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31342step3 raw31342step3Labels = mixedMoment B raw31342step4 raw31342step4Labels := by
      have ha : raw31342step4 = raw31342step3 := by apply Matrix.ext; unfold raw31342step4 raw31342step3; decide +kernel
      have hl : raw31342step3Labels = labelEmbedding1 ∘ raw31342step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31342step3 raw31342step3Labels raw31342step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2276 node2276Labels := by rfl

theorem canonical31343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31343 raw31343Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw31343 raw31343Labels = mixedMoment B raw31343step0 raw31343step0Labels := by
      have hz : ∀ j, raw31343 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw31343step0 = (fun i j => raw31343 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw31343step0 raw31343; decide +kernel
      have hl : raw31343step0Labels = raw31343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31343 raw31343Labels permutation265 hz
    mixedMoment B raw31343step0 raw31343step0Labels = mixedMoment B raw31343step1 raw31343step1Labels := by
      have ha : raw31343step1 = (fun i j => raw31343step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31343step1 raw31343step0; decide +kernel
      have hl : raw31343step1Labels = raw31343step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31343step0 raw31343step0Labels permutation42 permutation7
    mixedMoment B raw31343step1 raw31343step1Labels = mixedMoment B raw31343step2 raw31343step2Labels := by
      have ha : raw31343step2 = -raw31343step1 := by apply Matrix.ext; change ∀ i j, raw31343step2 i j = -(raw31343step1 i j); unfold raw31343step2 raw31343step1; decide +kernel
      have hl : raw31343step2Labels = raw31343step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31343step2 raw31343step2Labels = mixedMoment B raw31343step3 raw31343step3Labels := by
      have ha : raw31343step3 = raw31343step2 := by apply Matrix.ext; unfold raw31343step3 raw31343step2; decide +kernel
      have hl : raw31343step2Labels = labelEmbedding1 ∘ raw31343step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31343step2 raw31343step2Labels raw31343step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical31344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31344 raw31344Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw31344 raw31344Labels = mixedMoment B raw31344step0 raw31344step0Labels := by
      have hz : ∀ j, raw31344 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31344step0 = (fun i j => raw31344 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31344step0 raw31344; decide +kernel
      have hl : raw31344step0Labels = raw31344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31344 raw31344Labels permutation434 hz
    mixedMoment B raw31344step0 raw31344step0Labels = mixedMoment B raw31344step1 raw31344step1Labels := by
      have hz : ∀ j, raw31344step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31344step1 = (fun i j => raw31344step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31344step1 raw31344step0; decide +kernel
      have hl : raw31344step1Labels = raw31344step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31344step0 raw31344step0Labels permutation56 hz
    mixedMoment B raw31344step1 raw31344step1Labels = mixedMoment B raw31344step2 raw31344step2Labels := by
      have ha : raw31344step2 = (fun i j => raw31344step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31344step2 raw31344step1; decide +kernel
      have hl : raw31344step2Labels = raw31344step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31344step1 raw31344step1Labels permutation12 permutation7
    mixedMoment B raw31344step2 raw31344step2Labels = mixedMoment B raw31344step3 raw31344step3Labels := by
      have ha : raw31344step3 = -raw31344step2 := by apply Matrix.ext; change ∀ i j, raw31344step3 i j = -(raw31344step2 i j); unfold raw31344step3 raw31344step2; decide +kernel
      have hl : raw31344step3Labels = raw31344step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31344step3 raw31344step3Labels = mixedMoment B raw31344step4 raw31344step4Labels := by
      have ha : raw31344step4 = raw31344step3 := by apply Matrix.ext; unfold raw31344step4 raw31344step3; decide +kernel
      have hl : raw31344step3Labels = labelEmbedding1 ∘ raw31344step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31344step3 raw31344step3Labels raw31344step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2278 node2278Labels := by rfl

theorem canonical31345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31345 raw31345Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw31345 raw31345Labels = mixedMoment B raw31345step0 raw31345step0Labels := by
      have hz : ∀ j, raw31345 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31345step0 = (fun i j => raw31345 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31345step0 raw31345; decide +kernel
      have hl : raw31345step0Labels = raw31345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31345 raw31345Labels permutation434 hz
    mixedMoment B raw31345step0 raw31345step0Labels = mixedMoment B raw31345step1 raw31345step1Labels := by
      have hz : ∀ j, raw31345step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31345step1 = (fun i j => raw31345step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31345step1 raw31345step0; decide +kernel
      have hl : raw31345step1Labels = raw31345step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31345step0 raw31345step0Labels permutation56 hz
    mixedMoment B raw31345step1 raw31345step1Labels = mixedMoment B raw31345step2 raw31345step2Labels := by
      have ha : raw31345step2 = (fun i j => raw31345step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31345step2 raw31345step1; decide +kernel
      have hl : raw31345step2Labels = raw31345step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31345step1 raw31345step1Labels permutation12 permutation7
    mixedMoment B raw31345step2 raw31345step2Labels = mixedMoment B raw31345step3 raw31345step3Labels := by
      have ha : raw31345step3 = -raw31345step2 := by apply Matrix.ext; change ∀ i j, raw31345step3 i j = -(raw31345step2 i j); unfold raw31345step3 raw31345step2; decide +kernel
      have hl : raw31345step3Labels = raw31345step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31345step3 raw31345step3Labels = mixedMoment B raw31345step4 raw31345step4Labels := by
      have ha : raw31345step4 = raw31345step3 := by apply Matrix.ext; unfold raw31345step4 raw31345step3; decide +kernel
      have hl : raw31345step3Labels = labelEmbedding1 ∘ raw31345step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31345step3 raw31345step3Labels raw31345step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

theorem canonical31346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31346 raw31346Labels = mixedMoment B node1681 node1681Labels := by
  calc
    mixedMoment B raw31346 raw31346Labels = mixedMoment B raw31346step0 raw31346step0Labels := by
      have hz : ∀ j, raw31346 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31346step0 = (fun i j => raw31346 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31346step0 raw31346; decide +kernel
      have hl : raw31346step0Labels = raw31346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31346 raw31346Labels permutation434 hz
    mixedMoment B raw31346step0 raw31346step0Labels = mixedMoment B raw31346step1 raw31346step1Labels := by
      have ha : raw31346step1 = (fun i j => raw31346step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31346step1 raw31346step0; decide +kernel
      have hl : raw31346step1Labels = raw31346step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31346step0 raw31346step0Labels permutation36 permutation7
    mixedMoment B raw31346step1 raw31346step1Labels = mixedMoment B raw31346step2 raw31346step2Labels := by
      have ha : raw31346step2 = -raw31346step1 := by apply Matrix.ext; change ∀ i j, raw31346step2 i j = -(raw31346step1 i j); unfold raw31346step2 raw31346step1; decide +kernel
      have hl : raw31346step2Labels = raw31346step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31346step2 raw31346step2Labels = mixedMoment B raw31346step3 raw31346step3Labels := by
      have ha : raw31346step3 = raw31346step2 := by apply Matrix.ext; unfold raw31346step3 raw31346step2; decide +kernel
      have hl : raw31346step2Labels = labelEmbedding1 ∘ raw31346step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31346step2 raw31346step2Labels raw31346step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1681 node1681Labels := by rfl

theorem canonical31347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31347 raw31347Labels = mixedMoment B node2157 node2157Labels := by
  calc
    mixedMoment B raw31347 raw31347Labels = mixedMoment B raw31347step0 raw31347step0Labels := by
      have hz : ∀ j, raw31347 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31347step0 = (fun i j => raw31347 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31347step0 raw31347; decide +kernel
      have hl : raw31347step0Labels = raw31347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31347 raw31347Labels permutation434 hz
    mixedMoment B raw31347step0 raw31347step0Labels = mixedMoment B raw31347step1 raw31347step1Labels := by
      have ha : raw31347step1 = (fun i j => raw31347step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31347step1 raw31347step0; decide +kernel
      have hl : raw31347step1Labels = raw31347step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31347step0 raw31347step0Labels permutation36 permutation7
    mixedMoment B raw31347step1 raw31347step1Labels = mixedMoment B raw31347step2 raw31347step2Labels := by
      have ha : raw31347step2 = -raw31347step1 := by apply Matrix.ext; change ∀ i j, raw31347step2 i j = -(raw31347step1 i j); unfold raw31347step2 raw31347step1; decide +kernel
      have hl : raw31347step2Labels = raw31347step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31347step2 raw31347step2Labels = mixedMoment B raw31347step3 raw31347step3Labels := by
      have ha : raw31347step3 = raw31347step2 := by apply Matrix.ext; unfold raw31347step3 raw31347step2; decide +kernel
      have hl : raw31347step2Labels = labelEmbedding1 ∘ raw31347step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31347step2 raw31347step2Labels raw31347step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2157 node2157Labels := by rfl

theorem canonical31348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31348 raw31348Labels = mixedMoment B node2177 node2177Labels := by
  calc
    mixedMoment B raw31348 raw31348Labels = mixedMoment B raw31348step0 raw31348step0Labels := by
      have ha : raw31348step0 = (fun i j => raw31348 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31348step0 raw31348; decide +kernel
      have hl : raw31348step0Labels = raw31348Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31348 raw31348Labels permutation162 permutation7
    mixedMoment B raw31348step0 raw31348step0Labels = mixedMoment B raw31348step1 raw31348step1Labels := by
      have ha : raw31348step1 = -raw31348step0 := by apply Matrix.ext; change ∀ i j, raw31348step1 i j = -(raw31348step0 i j); unfold raw31348step1 raw31348step0; decide +kernel
      have hl : raw31348step1Labels = raw31348step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31348step1 raw31348step1Labels = mixedMoment B raw31348step2 raw31348step2Labels := by
      have ha : raw31348step2 = raw31348step1 := by apply Matrix.ext; unfold raw31348step2 raw31348step1; decide +kernel
      have hl : raw31348step1Labels = labelEmbedding1 ∘ raw31348step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31348step1 raw31348step1Labels raw31348step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2177 node2177Labels := by rfl

theorem canonical31349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31349 raw31349Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw31349 raw31349Labels = mixedMoment B raw31349step0 raw31349step0Labels := by
      have hz : ∀ j, raw31349 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31349step0 = (fun i j => raw31349 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31349step0 raw31349; decide +kernel
      have hl : raw31349step0Labels = raw31349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31349 raw31349Labels permutation434 hz
    mixedMoment B raw31349step0 raw31349step0Labels = mixedMoment B raw31349step1 raw31349step1Labels := by
      have ha : raw31349step1 = (fun i j => raw31349step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31349step1 raw31349step0; decide +kernel
      have hl : raw31349step1Labels = raw31349step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31349step0 raw31349step0Labels permutation36 permutation7
    mixedMoment B raw31349step1 raw31349step1Labels = mixedMoment B raw31349step2 raw31349step2Labels := by
      have ha : raw31349step2 = -raw31349step1 := by apply Matrix.ext; change ∀ i j, raw31349step2 i j = -(raw31349step1 i j); unfold raw31349step2 raw31349step1; decide +kernel
      have hl : raw31349step2Labels = raw31349step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31349step2 raw31349step2Labels = mixedMoment B raw31349step3 raw31349step3Labels := by
      have ha : raw31349step3 = raw31349step2 := by apply Matrix.ext; unfold raw31349step3 raw31349step2; decide +kernel
      have hl : raw31349step2Labels = labelEmbedding1 ∘ raw31349step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31349step2 raw31349step2Labels raw31349step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

theorem canonical31350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31350 raw31350Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw31350 raw31350Labels = mixedMoment B raw31350step0 raw31350step0Labels := by
      have hz : ∀ j, raw31350 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31350step0 = (fun i j => raw31350 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31350step0 raw31350; decide +kernel
      have hl : raw31350step0Labels = raw31350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31350 raw31350Labels permutation434 hz
    mixedMoment B raw31350step0 raw31350step0Labels = mixedMoment B raw31350step1 raw31350step1Labels := by
      have ha : raw31350step1 = (fun i j => raw31350step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31350step1 raw31350step0; decide +kernel
      have hl : raw31350step1Labels = raw31350step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31350step0 raw31350step0Labels permutation36 permutation7
    mixedMoment B raw31350step1 raw31350step1Labels = mixedMoment B raw31350step2 raw31350step2Labels := by
      have ha : raw31350step2 = -raw31350step1 := by apply Matrix.ext; change ∀ i j, raw31350step2 i j = -(raw31350step1 i j); unfold raw31350step2 raw31350step1; decide +kernel
      have hl : raw31350step2Labels = raw31350step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31350step2 raw31350step2Labels = mixedMoment B raw31350step3 raw31350step3Labels := by
      have ha : raw31350step3 = raw31350step2 := by apply Matrix.ext; unfold raw31350step3 raw31350step2; decide +kernel
      have hl : raw31350step2Labels = labelEmbedding1 ∘ raw31350step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31350step2 raw31350step2Labels raw31350step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

theorem canonical31351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31351 raw31351Labels = mixedMoment B node1667 node1667Labels := by
  calc
    mixedMoment B raw31351 raw31351Labels = mixedMoment B raw31351step0 raw31351step0Labels := by
      have ha : raw31351step0 = (fun i j => raw31351 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31351step0 raw31351; decide +kernel
      have hl : raw31351step0Labels = raw31351Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31351 raw31351Labels permutation162 permutation7
    mixedMoment B raw31351step0 raw31351step0Labels = mixedMoment B raw31351step1 raw31351step1Labels := by
      have ha : raw31351step1 = -raw31351step0 := by apply Matrix.ext; change ∀ i j, raw31351step1 i j = -(raw31351step0 i j); unfold raw31351step1 raw31351step0; decide +kernel
      have hl : raw31351step1Labels = raw31351step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31351step1 raw31351step1Labels = mixedMoment B raw31351step2 raw31351step2Labels := by
      have ha : raw31351step2 = raw31351step1 := by apply Matrix.ext; unfold raw31351step2 raw31351step1; decide +kernel
      have hl : raw31351step1Labels = labelEmbedding1 ∘ raw31351step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31351step1 raw31351step1Labels raw31351step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1667 node1667Labels := by rfl

theorem canonical31352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31352 raw31352Labels = mixedMoment B node2144 node2144Labels := by
  calc
    mixedMoment B raw31352 raw31352Labels = mixedMoment B raw31352step0 raw31352step0Labels := by
      have ha : raw31352step0 = (fun i j => raw31352 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31352step0 raw31352; decide +kernel
      have hl : raw31352step0Labels = raw31352Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31352 raw31352Labels permutation162 permutation7
    mixedMoment B raw31352step0 raw31352step0Labels = mixedMoment B raw31352step1 raw31352step1Labels := by
      have ha : raw31352step1 = -raw31352step0 := by apply Matrix.ext; change ∀ i j, raw31352step1 i j = -(raw31352step0 i j); unfold raw31352step1 raw31352step0; decide +kernel
      have hl : raw31352step1Labels = raw31352step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31352step1 raw31352step1Labels = mixedMoment B raw31352step2 raw31352step2Labels := by
      have ha : raw31352step2 = raw31352step1 := by apply Matrix.ext; unfold raw31352step2 raw31352step1; decide +kernel
      have hl : raw31352step1Labels = labelEmbedding1 ∘ raw31352step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31352step1 raw31352step1Labels raw31352step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2144 node2144Labels := by rfl

theorem canonical31353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31353 raw31353Labels = mixedMoment B node2194 node2194Labels := by
  calc
    mixedMoment B raw31353 raw31353Labels = mixedMoment B raw31353step0 raw31353step0Labels := by
      have ha : raw31353step0 = (fun i j => raw31353 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31353step0 raw31353; decide +kernel
      have hl : raw31353step0Labels = raw31353Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31353 raw31353Labels permutation162 permutation7
    mixedMoment B raw31353step0 raw31353step0Labels = mixedMoment B raw31353step1 raw31353step1Labels := by
      have ha : raw31353step1 = -raw31353step0 := by apply Matrix.ext; change ∀ i j, raw31353step1 i j = -(raw31353step0 i j); unfold raw31353step1 raw31353step0; decide +kernel
      have hl : raw31353step1Labels = raw31353step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31353step1 raw31353step1Labels = mixedMoment B raw31353step2 raw31353step2Labels := by
      have ha : raw31353step2 = raw31353step1 := by apply Matrix.ext; unfold raw31353step2 raw31353step1; decide +kernel
      have hl : raw31353step1Labels = labelEmbedding1 ∘ raw31353step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31353step1 raw31353step1Labels raw31353step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2194 node2194Labels := by rfl

theorem canonical31354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31354 raw31354Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw31354 raw31354Labels = mixedMoment B raw31354step0 raw31354step0Labels := by
      have ha : raw31354step0 = (fun i j => raw31354 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31354step0 raw31354; decide +kernel
      have hl : raw31354step0Labels = raw31354Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31354 raw31354Labels permutation162 permutation7
    mixedMoment B raw31354step0 raw31354step0Labels = mixedMoment B raw31354step1 raw31354step1Labels := by
      have ha : raw31354step1 = -raw31354step0 := by apply Matrix.ext; change ∀ i j, raw31354step1 i j = -(raw31354step0 i j); unfold raw31354step1 raw31354step0; decide +kernel
      have hl : raw31354step1Labels = raw31354step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31354step1 raw31354step1Labels = mixedMoment B raw31354step2 raw31354step2Labels := by
      have ha : raw31354step2 = raw31354step1 := by apply Matrix.ext; unfold raw31354step2 raw31354step1; decide +kernel
      have hl : raw31354step1Labels = labelEmbedding1 ∘ raw31354step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31354step1 raw31354step1Labels raw31354step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

theorem canonical31355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31355 raw31355Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw31355 raw31355Labels = mixedMoment B raw31355step0 raw31355step0Labels := by
      have ha : raw31355step0 = (fun i j => raw31355 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31355step0 raw31355; decide +kernel
      have hl : raw31355step0Labels = raw31355Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31355 raw31355Labels permutation162 permutation7
    mixedMoment B raw31355step0 raw31355step0Labels = mixedMoment B raw31355step1 raw31355step1Labels := by
      have ha : raw31355step1 = -raw31355step0 := by apply Matrix.ext; change ∀ i j, raw31355step1 i j = -(raw31355step0 i j); unfold raw31355step1 raw31355step0; decide +kernel
      have hl : raw31355step1Labels = raw31355step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31355step1 raw31355step1Labels = mixedMoment B raw31355step2 raw31355step2Labels := by
      have ha : raw31355step2 = raw31355step1 := by apply Matrix.ext; unfold raw31355step2 raw31355step1; decide +kernel
      have hl : raw31355step1Labels = labelEmbedding1 ∘ raw31355step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31355step1 raw31355step1Labels raw31355step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2190 node2190Labels := by rfl

theorem canonical31356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31356 raw31356Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw31356 raw31356Labels = mixedMoment B raw31356step0 raw31356step0Labels := by
      have hz : ∀ j, raw31356 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31356step0 = (fun i j => raw31356 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31356step0 raw31356; decide +kernel
      have hl : raw31356step0Labels = raw31356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31356 raw31356Labels permutation434 hz
    mixedMoment B raw31356step0 raw31356step0Labels = mixedMoment B raw31356step1 raw31356step1Labels := by
      have ha : raw31356step1 = (fun i j => raw31356step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31356step1 raw31356step0; decide +kernel
      have hl : raw31356step1Labels = raw31356step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31356step0 raw31356step0Labels permutation36 permutation7
    mixedMoment B raw31356step1 raw31356step1Labels = mixedMoment B raw31356step2 raw31356step2Labels := by
      have ha : raw31356step2 = -raw31356step1 := by apply Matrix.ext; change ∀ i j, raw31356step2 i j = -(raw31356step1 i j); unfold raw31356step2 raw31356step1; decide +kernel
      have hl : raw31356step2Labels = raw31356step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31356step2 raw31356step2Labels = mixedMoment B raw31356step3 raw31356step3Labels := by
      have ha : raw31356step3 = raw31356step2 := by apply Matrix.ext; unfold raw31356step3 raw31356step2; decide +kernel
      have hl : raw31356step2Labels = labelEmbedding1 ∘ raw31356step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31356step2 raw31356step2Labels raw31356step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1679 node1679Labels := by rfl

theorem canonical31357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31357 raw31357Labels = mixedMoment B node2155 node2155Labels := by
  calc
    mixedMoment B raw31357 raw31357Labels = mixedMoment B raw31357step0 raw31357step0Labels := by
      have hz : ∀ j, raw31357 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31357step0 = (fun i j => raw31357 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31357step0 raw31357; decide +kernel
      have hl : raw31357step0Labels = raw31357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31357 raw31357Labels permutation434 hz
    mixedMoment B raw31357step0 raw31357step0Labels = mixedMoment B raw31357step1 raw31357step1Labels := by
      have ha : raw31357step1 = (fun i j => raw31357step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31357step1 raw31357step0; decide +kernel
      have hl : raw31357step1Labels = raw31357step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31357step0 raw31357step0Labels permutation36 permutation7
    mixedMoment B raw31357step1 raw31357step1Labels = mixedMoment B raw31357step2 raw31357step2Labels := by
      have ha : raw31357step2 = -raw31357step1 := by apply Matrix.ext; change ∀ i j, raw31357step2 i j = -(raw31357step1 i j); unfold raw31357step2 raw31357step1; decide +kernel
      have hl : raw31357step2Labels = raw31357step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31357step2 raw31357step2Labels = mixedMoment B raw31357step3 raw31357step3Labels := by
      have ha : raw31357step3 = raw31357step2 := by apply Matrix.ext; unfold raw31357step3 raw31357step2; decide +kernel
      have hl : raw31357step2Labels = labelEmbedding1 ∘ raw31357step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31357step2 raw31357step2Labels raw31357step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2155 node2155Labels := by rfl

theorem canonical31358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31358 raw31358Labels = mixedMoment B node2212 node2212Labels := by
  calc
    mixedMoment B raw31358 raw31358Labels = mixedMoment B raw31358step0 raw31358step0Labels := by
      have hz : ∀ j, raw31358 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31358step0 = (fun i j => raw31358 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31358step0 raw31358; decide +kernel
      have hl : raw31358step0Labels = raw31358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31358 raw31358Labels permutation434 hz
    mixedMoment B raw31358step0 raw31358step0Labels = mixedMoment B raw31358step1 raw31358step1Labels := by
      have ha : raw31358step1 = (fun i j => raw31358step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31358step1 raw31358step0; decide +kernel
      have hl : raw31358step1Labels = raw31358step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31358step0 raw31358step0Labels permutation36 permutation7
    mixedMoment B raw31358step1 raw31358step1Labels = mixedMoment B raw31358step2 raw31358step2Labels := by
      have ha : raw31358step2 = -raw31358step1 := by apply Matrix.ext; change ∀ i j, raw31358step2 i j = -(raw31358step1 i j); unfold raw31358step2 raw31358step1; decide +kernel
      have hl : raw31358step2Labels = raw31358step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31358step2 raw31358step2Labels = mixedMoment B raw31358step3 raw31358step3Labels := by
      have ha : raw31358step3 = raw31358step2 := by apply Matrix.ext; unfold raw31358step3 raw31358step2; decide +kernel
      have hl : raw31358step2Labels = labelEmbedding1 ∘ raw31358step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31358step2 raw31358step2Labels raw31358step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2212 node2212Labels := by rfl

theorem canonical31359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31359 raw31359Labels = mixedMoment B node2176 node2176Labels := by
  calc
    mixedMoment B raw31359 raw31359Labels = mixedMoment B raw31359step0 raw31359step0Labels := by
      have ha : raw31359step0 = (fun i j => raw31359 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31359step0 raw31359; decide +kernel
      have hl : raw31359step0Labels = raw31359Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31359 raw31359Labels permutation162 permutation7
    mixedMoment B raw31359step0 raw31359step0Labels = mixedMoment B raw31359step1 raw31359step1Labels := by
      have ha : raw31359step1 = -raw31359step0 := by apply Matrix.ext; change ∀ i j, raw31359step1 i j = -(raw31359step0 i j); unfold raw31359step1 raw31359step0; decide +kernel
      have hl : raw31359step1Labels = raw31359step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31359step1 raw31359step1Labels = mixedMoment B raw31359step2 raw31359step2Labels := by
      have ha : raw31359step2 = raw31359step1 := by apply Matrix.ext; unfold raw31359step2 raw31359step1; decide +kernel
      have hl : raw31359step1Labels = labelEmbedding1 ∘ raw31359step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31359step1 raw31359step1Labels raw31359step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2176 node2176Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical245
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical31360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31360 raw31360Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw31360 raw31360Labels = mixedMoment B raw31360step0 raw31360step0Labels := by
      have hz : ∀ j, raw31360 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31360step0 = (fun i j => raw31360 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31360step0 raw31360; decide +kernel
      have hl : raw31360step0Labels = raw31360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31360 raw31360Labels permutation434 hz
    mixedMoment B raw31360step0 raw31360step0Labels = mixedMoment B raw31360step1 raw31360step1Labels := by
      have ha : raw31360step1 = (fun i j => raw31360step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31360step1 raw31360step0; decide +kernel
      have hl : raw31360step1Labels = raw31360step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31360step0 raw31360step0Labels permutation36 permutation7
    mixedMoment B raw31360step1 raw31360step1Labels = mixedMoment B raw31360step2 raw31360step2Labels := by
      have ha : raw31360step2 = -raw31360step1 := by apply Matrix.ext; change ∀ i j, raw31360step2 i j = -(raw31360step1 i j); unfold raw31360step2 raw31360step1; decide +kernel
      have hl : raw31360step2Labels = raw31360step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31360step2 raw31360step2Labels = mixedMoment B raw31360step3 raw31360step3Labels := by
      have ha : raw31360step3 = raw31360step2 := by apply Matrix.ext; unfold raw31360step3 raw31360step2; decide +kernel
      have hl : raw31360step2Labels = labelEmbedding1 ∘ raw31360step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31360step2 raw31360step2Labels raw31360step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical31361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31361 raw31361Labels = mixedMoment B node1685 node1685Labels := by
  calc
    mixedMoment B raw31361 raw31361Labels = mixedMoment B raw31361step0 raw31361step0Labels := by
      have hz : ∀ j, raw31361 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31361step0 = (fun i j => raw31361 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31361step0 raw31361; decide +kernel
      have hl : raw31361step0Labels = raw31361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31361 raw31361Labels permutation434 hz
    mixedMoment B raw31361step0 raw31361step0Labels = mixedMoment B raw31361step1 raw31361step1Labels := by
      have ha : raw31361step1 = (fun i j => raw31361step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31361step1 raw31361step0; decide +kernel
      have hl : raw31361step1Labels = raw31361step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31361step0 raw31361step0Labels permutation36 permutation7
    mixedMoment B raw31361step1 raw31361step1Labels = mixedMoment B raw31361step2 raw31361step2Labels := by
      have ha : raw31361step2 = -raw31361step1 := by apply Matrix.ext; change ∀ i j, raw31361step2 i j = -(raw31361step1 i j); unfold raw31361step2 raw31361step1; decide +kernel
      have hl : raw31361step2Labels = raw31361step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31361step2 raw31361step2Labels = mixedMoment B raw31361step3 raw31361step3Labels := by
      have ha : raw31361step3 = raw31361step2 := by apply Matrix.ext; unfold raw31361step3 raw31361step2; decide +kernel
      have hl : raw31361step2Labels = labelEmbedding1 ∘ raw31361step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31361step2 raw31361step2Labels raw31361step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1685 node1685Labels := by rfl

theorem canonical31362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31362 raw31362Labels = mixedMoment B node2161 node2161Labels := by
  calc
    mixedMoment B raw31362 raw31362Labels = mixedMoment B raw31362step0 raw31362step0Labels := by
      have hz : ∀ j, raw31362 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31362step0 = (fun i j => raw31362 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31362step0 raw31362; decide +kernel
      have hl : raw31362step0Labels = raw31362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31362 raw31362Labels permutation434 hz
    mixedMoment B raw31362step0 raw31362step0Labels = mixedMoment B raw31362step1 raw31362step1Labels := by
      have ha : raw31362step1 = (fun i j => raw31362step0 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31362step1 raw31362step0; decide +kernel
      have hl : raw31362step1Labels = raw31362step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31362step0 raw31362step0Labels permutation147 permutation5
    mixedMoment B raw31362step1 raw31362step1Labels = mixedMoment B raw31362step2 raw31362step2Labels := by
      have ha : raw31362step2 = raw31362step1 := by apply Matrix.ext; unfold raw31362step2 raw31362step1; decide +kernel
      have hl : raw31362step1Labels = labelEmbedding1 ∘ raw31362step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31362step1 raw31362step1Labels raw31362step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2161 node2161Labels := by rfl

theorem canonical31363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31363 raw31363Labels = mixedMoment B node2162 node2162Labels := by
  calc
    mixedMoment B raw31363 raw31363Labels = mixedMoment B raw31363step0 raw31363step0Labels := by
      have hz : ∀ j, raw31363 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31363step0 = (fun i j => raw31363 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31363step0 raw31363; decide +kernel
      have hl : raw31363step0Labels = raw31363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31363 raw31363Labels permutation434 hz
    mixedMoment B raw31363step0 raw31363step0Labels = mixedMoment B raw31363step1 raw31363step1Labels := by
      have ha : raw31363step1 = (fun i j => raw31363step0 (permutation146 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31363step1 raw31363step0; decide +kernel
      have hl : raw31363step1Labels = raw31363step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31363step0 raw31363step0Labels permutation146 permutation5
    mixedMoment B raw31363step1 raw31363step1Labels = mixedMoment B raw31363step2 raw31363step2Labels := by
      have ha : raw31363step2 = raw31363step1 := by apply Matrix.ext; unfold raw31363step2 raw31363step1; decide +kernel
      have hl : raw31363step1Labels = labelEmbedding1 ∘ raw31363step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31363step1 raw31363step1Labels raw31363step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2162 node2162Labels := by rfl

theorem canonical31364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31364 raw31364Labels = mixedMoment B node2160 node2160Labels := by
  calc
    mixedMoment B raw31364 raw31364Labels = mixedMoment B raw31364step0 raw31364step0Labels := by
      have ha : raw31364step0 = (fun i j => raw31364 (permutation667 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31364step0 raw31364; decide +kernel
      have hl : raw31364step0Labels = raw31364Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31364 raw31364Labels permutation667 permutation5
    mixedMoment B raw31364step0 raw31364step0Labels = mixedMoment B raw31364step1 raw31364step1Labels := by
      have ha : raw31364step1 = raw31364step0 := by apply Matrix.ext; unfold raw31364step1 raw31364step0; decide +kernel
      have hl : raw31364step0Labels = labelEmbedding1 ∘ raw31364step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31364step0 raw31364step0Labels raw31364step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2160 node2160Labels := by rfl

theorem canonical31365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31365 raw31365Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw31365 raw31365Labels = mixedMoment B raw31365step0 raw31365step0Labels := by
      have hz : ∀ j, raw31365 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31365step0 = (fun i j => raw31365 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31365step0 raw31365; decide +kernel
      have hl : raw31365step0Labels = raw31365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31365 raw31365Labels permutation434 hz
    mixedMoment B raw31365step0 raw31365step0Labels = mixedMoment B raw31365step1 raw31365step1Labels := by
      have ha : raw31365step1 = (fun i j => raw31365step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31365step1 raw31365step0; decide +kernel
      have hl : raw31365step1Labels = raw31365step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31365step0 raw31365step0Labels permutation36 permutation7
    mixedMoment B raw31365step1 raw31365step1Labels = mixedMoment B raw31365step2 raw31365step2Labels := by
      have ha : raw31365step2 = -raw31365step1 := by apply Matrix.ext; change ∀ i j, raw31365step2 i j = -(raw31365step1 i j); unfold raw31365step2 raw31365step1; decide +kernel
      have hl : raw31365step2Labels = raw31365step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31365step2 raw31365step2Labels = mixedMoment B raw31365step3 raw31365step3Labels := by
      have ha : raw31365step3 = raw31365step2 := by apply Matrix.ext; unfold raw31365step3 raw31365step2; decide +kernel
      have hl : raw31365step2Labels = labelEmbedding1 ∘ raw31365step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31365step2 raw31365step2Labels raw31365step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

theorem canonical31366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31366 raw31366Labels = mixedMoment B node3379 node3379Labels := by
  calc
    mixedMoment B raw31366 raw31366Labels = mixedMoment B raw31366step0 raw31366step0Labels := by
      have hz : ∀ j, raw31366 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31366step0 = (fun i j => raw31366 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31366step0 raw31366; decide +kernel
      have hl : raw31366step0Labels = raw31366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31366 raw31366Labels permutation434 hz
    mixedMoment B raw31366step0 raw31366step0Labels = mixedMoment B raw31366step1 raw31366step1Labels := by
      have ha : raw31366step1 = (fun i j => raw31366step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31366step1 raw31366step0; decide +kernel
      have hl : raw31366step1Labels = raw31366step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31366step0 raw31366step0Labels permutation33 permutation2
    _ = mixedMoment B node3379 node3379Labels := by rfl

theorem canonical31367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31367 raw31367Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw31367 raw31367Labels = mixedMoment B raw31367step0 raw31367step0Labels := by
      have hz : ∀ j, raw31367 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31367step0 = (fun i j => raw31367 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31367step0 raw31367; decide +kernel
      have hl : raw31367step0Labels = raw31367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31367 raw31367Labels permutation434 hz
    mixedMoment B raw31367step0 raw31367step0Labels = mixedMoment B raw31367step1 raw31367step1Labels := by
      have ha : raw31367step1 = (fun i j => raw31367step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31367step1 raw31367step0; decide +kernel
      have hl : raw31367step1Labels = raw31367step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31367step0 raw31367step0Labels permutation33 permutation2
    _ = mixedMoment B node2028 node2028Labels := by rfl

theorem canonical31368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31368 raw31368Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw31368 raw31368Labels = mixedMoment B raw31368step0 raw31368step0Labels := by
      have hz : ∀ j, raw31368 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31368step0 = (fun i j => raw31368 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31368step0 raw31368; decide +kernel
      have hl : raw31368step0Labels = raw31368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31368 raw31368Labels permutation434 hz
    mixedMoment B raw31368step0 raw31368step0Labels = mixedMoment B raw31368step1 raw31368step1Labels := by
      have ha : raw31368step1 = (fun i j => raw31368step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31368step1 raw31368step0; decide +kernel
      have hl : raw31368step1Labels = raw31368step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31368step0 raw31368step0Labels permutation33 permutation2
    _ = mixedMoment B node1814 node1814Labels := by rfl

theorem canonical31369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31369 raw31369Labels = mixedMoment B node1791 node1791Labels := by
  calc
    mixedMoment B raw31369 raw31369Labels = mixedMoment B raw31369step0 raw31369step0Labels := by
      have ha : raw31369step0 = (fun i j => raw31369 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31369step0 raw31369; decide +kernel
      have hl : raw31369step0Labels = raw31369Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31369 raw31369Labels permutation153 permutation2
    _ = mixedMoment B node1791 node1791Labels := by rfl

theorem canonical31370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31370 raw31370Labels = mixedMoment B node1795 node1795Labels := by
  calc
    mixedMoment B raw31370 raw31370Labels = mixedMoment B raw31370step0 raw31370step0Labels := by
      have hz : ∀ j, raw31370 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31370step0 = (fun i j => raw31370 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31370step0 raw31370; decide +kernel
      have hl : raw31370step0Labels = raw31370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31370 raw31370Labels permutation434 hz
    mixedMoment B raw31370step0 raw31370step0Labels = mixedMoment B raw31370step1 raw31370step1Labels := by
      have ha : raw31370step1 = (fun i j => raw31370step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31370step1 raw31370step0; decide +kernel
      have hl : raw31370step1Labels = raw31370step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31370step0 raw31370step0Labels permutation33 permutation2
    _ = mixedMoment B node1795 node1795Labels := by rfl

theorem canonical31371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31371 raw31371Labels = mixedMoment B node1797 node1797Labels := by
  calc
    mixedMoment B raw31371 raw31371Labels = mixedMoment B raw31371step0 raw31371step0Labels := by
      have hz : ∀ j, raw31371 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31371step0 = (fun i j => raw31371 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31371step0 raw31371; decide +kernel
      have hl : raw31371step0Labels = raw31371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31371 raw31371Labels permutation434 hz
    _ = mixedMoment B node1797 node1797Labels := by rfl

theorem canonical31372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31372 raw31372Labels = mixedMoment B node932 node932Labels := by
  calc
    mixedMoment B raw31372 raw31372Labels = mixedMoment B raw31372step0 raw31372step0Labels := by
      have hz : ∀ j, raw31372 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31372step0 = (fun i j => raw31372 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31372step0 raw31372; decide +kernel
      have hl : raw31372step0Labels = raw31372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31372 raw31372Labels permutation434 hz
    mixedMoment B raw31372step0 raw31372step0Labels = mixedMoment B raw31372step1 raw31372step1Labels := by
      have ha : raw31372step1 = (fun i j => raw31372step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31372step1 raw31372step0; decide +kernel
      have hl : raw31372step1Labels = raw31372step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31372step0 raw31372step0Labels permutation33 permutation2
    _ = mixedMoment B node932 node932Labels := by rfl

theorem canonical31373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31373 raw31373Labels = mixedMoment B node1966 node1966Labels := by
  calc
    mixedMoment B raw31373 raw31373Labels = mixedMoment B raw31373step0 raw31373step0Labels := by
      have ha : raw31373step0 = (fun i j => raw31373 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31373step0 raw31373; decide +kernel
      have hl : raw31373step0Labels = raw31373Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31373 raw31373Labels permutation159 permutation2
    _ = mixedMoment B node1966 node1966Labels := by rfl

theorem canonical31374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31374 raw31374Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw31374 raw31374Labels = mixedMoment B raw31374step0 raw31374step0Labels := by
      have hz : ∀ j, raw31374 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31374step0 = (fun i j => raw31374 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31374step0 raw31374; decide +kernel
      have hl : raw31374step0Labels = raw31374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31374 raw31374Labels permutation434 hz
    _ = mixedMoment B node2058 node2058Labels := by rfl

theorem canonical31375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31375 raw31375Labels = mixedMoment B node2053 node2053Labels := by
  calc
    mixedMoment B raw31375 raw31375Labels = mixedMoment B raw31375step0 raw31375step0Labels := by
      have hz : ∀ j, raw31375 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31375step0 = (fun i j => raw31375 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31375step0 raw31375; decide +kernel
      have hl : raw31375step0Labels = raw31375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31375 raw31375Labels permutation434 hz
    mixedMoment B raw31375step0 raw31375step0Labels = mixedMoment B raw31375step1 raw31375step1Labels := by
      have ha : raw31375step1 = (fun i j => raw31375step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31375step1 raw31375step0; decide +kernel
      have hl : raw31375step1Labels = raw31375step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31375step0 raw31375step0Labels permutation36 permutation2
    _ = mixedMoment B node2053 node2053Labels := by rfl

theorem canonical31376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31376 raw31376Labels = mixedMoment B node906 node906Labels := by
  calc
    mixedMoment B raw31376 raw31376Labels = mixedMoment B raw31376step0 raw31376step0Labels := by
      have ha : raw31376step0 = (fun i j => raw31376 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31376step0 raw31376; decide +kernel
      have hl : raw31376step0Labels = raw31376Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31376 raw31376Labels permutation153 permutation2
    _ = mixedMoment B node906 node906Labels := by rfl

theorem canonical31377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31377 raw31377Labels = mixedMoment B node1974 node1974Labels := by
  calc
    mixedMoment B raw31377 raw31377Labels = mixedMoment B raw31377step0 raw31377step0Labels := by
      have ha : raw31377step0 = (fun i j => raw31377 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31377step0 raw31377; decide +kernel
      have hl : raw31377step0Labels = raw31377Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31377 raw31377Labels permutation153 permutation2
    _ = mixedMoment B node1974 node1974Labels := by rfl

theorem canonical31378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31378 raw31378Labels = mixedMoment B node2021 node2021Labels := by
  calc
    _ = mixedMoment B node2021 node2021Labels := by rfl

theorem canonical31379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31379 raw31379Labels = mixedMoment B node2019 node2019Labels := by
  calc
    mixedMoment B raw31379 raw31379Labels = mixedMoment B raw31379step0 raw31379step0Labels := by
      have ha : raw31379step0 = (fun i j => raw31379 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31379step0 raw31379; decide +kernel
      have hl : raw31379step0Labels = raw31379Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31379 raw31379Labels permutation153 permutation2
    _ = mixedMoment B node2019 node2019Labels := by rfl

theorem canonical31457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31457 raw31457Labels = mixedMoment B node5236 node5236Labels := by
  calc
    mixedMoment B raw31457 raw31457Labels = mixedMoment B raw31457step0 raw31457step0Labels := by
      have hz : ∀ j, raw31457 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31457step0 = (fun i j => raw31457 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31457step0 raw31457; decide +kernel
      have hl : raw31457step0Labels = raw31457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31457 raw31457Labels permutation434 hz
    mixedMoment B raw31457step0 raw31457step0Labels = mixedMoment B raw31457step1 raw31457step1Labels := by
      have ha : raw31457step1 = (fun i j => raw31457step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31457step1 raw31457step0; decide +kernel
      have hl : raw31457step1Labels = raw31457step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31457step0 raw31457step0Labels permutation32 permutation7
    mixedMoment B raw31457step1 raw31457step1Labels = mixedMoment B raw31457step2 raw31457step2Labels := by
      have ha : raw31457step2 = -raw31457step1 := by apply Matrix.ext; change ∀ i j, raw31457step2 i j = -(raw31457step1 i j); unfold raw31457step2 raw31457step1; decide +kernel
      have hl : raw31457step2Labels = raw31457step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31457step2 raw31457step2Labels = mixedMoment B raw31457step3 raw31457step3Labels := by
      have ha : raw31457step3 = raw31457step2 := by apply Matrix.ext; unfold raw31457step3 raw31457step2; decide +kernel
      have hl : raw31457step2Labels = labelEmbedding10 ∘ raw31457step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31457step2 raw31457step2Labels raw31457step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5236 node5236Labels := by rfl

theorem canonical31458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31458 raw31458Labels = mixedMoment B node5269 node5269Labels := by
  calc
    mixedMoment B raw31458 raw31458Labels = mixedMoment B raw31458step0 raw31458step0Labels := by
      have hz : ∀ j, raw31458 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31458step0 = (fun i j => raw31458 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31458step0 raw31458; decide +kernel
      have hl : raw31458step0Labels = raw31458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31458 raw31458Labels permutation434 hz
    mixedMoment B raw31458step0 raw31458step0Labels = mixedMoment B raw31458step1 raw31458step1Labels := by
      have ha : raw31458step1 = (fun i j => raw31458step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31458step1 raw31458step0; decide +kernel
      have hl : raw31458step1Labels = raw31458step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31458step0 raw31458step0Labels permutation32 permutation7
    mixedMoment B raw31458step1 raw31458step1Labels = mixedMoment B raw31458step2 raw31458step2Labels := by
      have ha : raw31458step2 = -raw31458step1 := by apply Matrix.ext; change ∀ i j, raw31458step2 i j = -(raw31458step1 i j); unfold raw31458step2 raw31458step1; decide +kernel
      have hl : raw31458step2Labels = raw31458step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31458step2 raw31458step2Labels = mixedMoment B raw31458step3 raw31458step3Labels := by
      have ha : raw31458step3 = raw31458step2 := by apply Matrix.ext; unfold raw31458step3 raw31458step2; decide +kernel
      have hl : raw31458step2Labels = labelEmbedding10 ∘ raw31458step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31458step2 raw31458step2Labels raw31458step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5269 node5269Labels := by rfl

theorem canonical31459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31459 raw31459Labels = mixedMoment B node5246 node5246Labels := by
  calc
    mixedMoment B raw31459 raw31459Labels = mixedMoment B raw31459step0 raw31459step0Labels := by
      have ha : raw31459step0 = (fun i j => raw31459 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31459step0 raw31459; decide +kernel
      have hl : raw31459step0Labels = raw31459Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31459 raw31459Labels permutation158 permutation7
    mixedMoment B raw31459step0 raw31459step0Labels = mixedMoment B raw31459step1 raw31459step1Labels := by
      have ha : raw31459step1 = -raw31459step0 := by apply Matrix.ext; change ∀ i j, raw31459step1 i j = -(raw31459step0 i j); unfold raw31459step1 raw31459step0; decide +kernel
      have hl : raw31459step1Labels = raw31459step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31459step1 raw31459step1Labels = mixedMoment B raw31459step2 raw31459step2Labels := by
      have ha : raw31459step2 = raw31459step1 := by apply Matrix.ext; unfold raw31459step2 raw31459step1; decide +kernel
      have hl : raw31459step1Labels = labelEmbedding10 ∘ raw31459step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31459step1 raw31459step1Labels raw31459step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5246 node5246Labels := by rfl

theorem canonical31460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31460 raw31460Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw31460 raw31460Labels = mixedMoment B raw31460step0 raw31460step0Labels := by
      have hz : ∀ j, raw31460 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31460step0 = (fun i j => raw31460 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31460step0 raw31460; decide +kernel
      have hl : raw31460step0Labels = raw31460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31460 raw31460Labels permutation434 hz
    mixedMoment B raw31460step0 raw31460step0Labels = mixedMoment B raw31460step1 raw31460step1Labels := by
      have ha : raw31460step1 = (fun i j => raw31460step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31460step1 raw31460step0; decide +kernel
      have hl : raw31460step1Labels = raw31460step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31460step0 raw31460step0Labels permutation32 permutation7
    mixedMoment B raw31460step1 raw31460step1Labels = mixedMoment B raw31460step2 raw31460step2Labels := by
      have ha : raw31460step2 = -raw31460step1 := by apply Matrix.ext; change ∀ i j, raw31460step2 i j = -(raw31460step1 i j); unfold raw31460step2 raw31460step1; decide +kernel
      have hl : raw31460step2Labels = raw31460step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31460step2 raw31460step2Labels = mixedMoment B raw31460step3 raw31460step3Labels := by
      have ha : raw31460step3 = raw31460step2 := by apply Matrix.ext; unfold raw31460step3 raw31460step2; decide +kernel
      have hl : raw31460step2Labels = labelEmbedding10 ∘ raw31460step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31460step2 raw31460step2Labels raw31460step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical31461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31461 raw31461Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw31461 raw31461Labels = mixedMoment B raw31461step0 raw31461step0Labels := by
      have hz : ∀ j, raw31461 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31461step0 = (fun i j => raw31461 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31461step0 raw31461; decide +kernel
      have hl : raw31461step0Labels = raw31461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31461 raw31461Labels permutation434 hz
    mixedMoment B raw31461step0 raw31461step0Labels = mixedMoment B raw31461step1 raw31461step1Labels := by
      have ha : raw31461step1 = (fun i j => raw31461step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31461step1 raw31461step0; decide +kernel
      have hl : raw31461step1Labels = raw31461step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31461step0 raw31461step0Labels permutation33 permutation7
    mixedMoment B raw31461step1 raw31461step1Labels = mixedMoment B raw31461step2 raw31461step2Labels := by
      have ha : raw31461step2 = -raw31461step1 := by apply Matrix.ext; change ∀ i j, raw31461step2 i j = -(raw31461step1 i j); unfold raw31461step2 raw31461step1; decide +kernel
      have hl : raw31461step2Labels = raw31461step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31461step2 raw31461step2Labels = mixedMoment B raw31461step3 raw31461step3Labels := by
      have ha : raw31461step3 = raw31461step2 := by apply Matrix.ext; unfold raw31461step3 raw31461step2; decide +kernel
      have hl : raw31461step2Labels = labelEmbedding10 ∘ raw31461step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31461step2 raw31461step2Labels raw31461step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical31462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31462 raw31462Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw31462 raw31462Labels = mixedMoment B raw31462step0 raw31462step0Labels := by
      have hz : ∀ j, raw31462 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31462step0 = (fun i j => raw31462 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31462step0 raw31462; decide +kernel
      have hl : raw31462step0Labels = raw31462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31462 raw31462Labels permutation434 hz
    mixedMoment B raw31462step0 raw31462step0Labels = mixedMoment B raw31462step1 raw31462step1Labels := by
      have hz : ∀ j, raw31462step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31462step1 = (fun i j => raw31462step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31462step1 raw31462step0; decide +kernel
      have hl : raw31462step1Labels = raw31462step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31462step0 raw31462step0Labels permutation56 hz
    _ = mixedMoment B node4467 node4467Labels := by rfl

theorem canonical31463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31463 raw31463Labels = mixedMoment B node4875 node4875Labels := by
  calc
    mixedMoment B raw31463 raw31463Labels = mixedMoment B raw31463step0 raw31463step0Labels := by
      have hz : ∀ j, raw31463 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31463step0 = (fun i j => raw31463 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31463step0 raw31463; decide +kernel
      have hl : raw31463step0Labels = raw31463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31463 raw31463Labels permutation434 hz
    mixedMoment B raw31463step0 raw31463step0Labels = mixedMoment B raw31463step1 raw31463step1Labels := by
      have hz : ∀ j, raw31463step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31463step1 = (fun i j => raw31463step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31463step1 raw31463step0; decide +kernel
      have hl : raw31463step1Labels = raw31463step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31463step0 raw31463step0Labels permutation56 hz
    _ = mixedMoment B node4875 node4875Labels := by rfl

theorem canonical31464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31464 raw31464Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw31464 raw31464Labels = mixedMoment B raw31464step0 raw31464step0Labels := by
      have hz : ∀ j, raw31464 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw31464step0 = (fun i j => raw31464 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw31464step0 raw31464; decide +kernel
      have hl : raw31464step0Labels = raw31464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31464 raw31464Labels permutation265 hz
    mixedMoment B raw31464step0 raw31464step0Labels = mixedMoment B raw31464step1 raw31464step1Labels := by
      have ha : raw31464step1 = (fun i j => raw31464step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31464step1 raw31464step0; decide +kernel
      have hl : raw31464step1Labels = raw31464step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31464step0 raw31464step0Labels permutation38 permutation2
    _ = mixedMoment B node4811 node4811Labels := by rfl

theorem canonical31465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31465 raw31465Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw31465 raw31465Labels = mixedMoment B raw31465step0 raw31465step0Labels := by
      have hz : ∀ j, raw31465 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31465step0 = (fun i j => raw31465 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31465step0 raw31465; decide +kernel
      have hl : raw31465step0Labels = raw31465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31465 raw31465Labels permutation434 hz
    mixedMoment B raw31465step0 raw31465step0Labels = mixedMoment B raw31465step1 raw31465step1Labels := by
      have hz : ∀ j, raw31465step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31465step1 = (fun i j => raw31465step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31465step1 raw31465step0; decide +kernel
      have hl : raw31465step1Labels = raw31465step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31465step0 raw31465step0Labels permutation56 hz
    _ = mixedMoment B node4895 node4895Labels := by rfl

theorem canonical31466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31466 raw31466Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw31466 raw31466Labels = mixedMoment B raw31466step0 raw31466step0Labels := by
      have hz : ∀ j, raw31466 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31466step0 = (fun i j => raw31466 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31466step0 raw31466; decide +kernel
      have hl : raw31466step0Labels = raw31466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31466 raw31466Labels permutation434 hz
    mixedMoment B raw31466step0 raw31466step0Labels = mixedMoment B raw31466step1 raw31466step1Labels := by
      have hz : ∀ j, raw31466step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31466step1 = (fun i j => raw31466step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31466step1 raw31466step0; decide +kernel
      have hl : raw31466step1Labels = raw31466step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31466step0 raw31466step0Labels permutation56 hz
    mixedMoment B raw31466step1 raw31466step1Labels = mixedMoment B raw31466step2 raw31466step2Labels := by
      have ha : raw31466step2 = (fun i j => raw31466step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31466step2 raw31466step1; decide +kernel
      have hl : raw31466step2Labels = raw31466step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31466step1 raw31466step1Labels permutation9 permutation2
    _ = mixedMoment B node4895 node4895Labels := by rfl

theorem canonical31467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31467 raw31467Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw31467 raw31467Labels = mixedMoment B raw31467step0 raw31467step0Labels := by
      have hz : ∀ j, raw31467 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31467step0 = (fun i j => raw31467 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31467step0 raw31467; decide +kernel
      have hl : raw31467step0Labels = raw31467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31467 raw31467Labels permutation434 hz
    _ = mixedMoment B node4355 node4355Labels := by rfl

theorem canonical31468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31468 raw31468Labels = mixedMoment B node4689 node4689Labels := by
  calc
    mixedMoment B raw31468 raw31468Labels = mixedMoment B raw31468step0 raw31468step0Labels := by
      have hz : ∀ j, raw31468 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31468step0 = (fun i j => raw31468 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31468step0 raw31468; decide +kernel
      have hl : raw31468step0Labels = raw31468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31468 raw31468Labels permutation434 hz
    _ = mixedMoment B node4689 node4689Labels := by rfl

theorem canonical31469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31469 raw31469Labels = mixedMoment B node4767 node4767Labels := by
  calc
    mixedMoment B raw31469 raw31469Labels = mixedMoment B raw31469step0 raw31469step0Labels := by
      have ha : raw31469step0 = (fun i j => raw31469 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31469step0 raw31469; decide +kernel
      have hl : raw31469step0Labels = raw31469Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31469 raw31469Labels permutation158 permutation2
    _ = mixedMoment B node4767 node4767Labels := by rfl

theorem canonical31470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31470 raw31470Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw31470 raw31470Labels = mixedMoment B raw31470step0 raw31470step0Labels := by
      have hz : ∀ j, raw31470 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31470step0 = (fun i j => raw31470 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31470step0 raw31470; decide +kernel
      have hl : raw31470step0Labels = raw31470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31470 raw31470Labels permutation434 hz
    _ = mixedMoment B node4838 node4838Labels := by rfl

theorem canonical31471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31471 raw31471Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw31471 raw31471Labels = mixedMoment B raw31471step0 raw31471step0Labels := by
      have hz : ∀ j, raw31471 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31471step0 = (fun i j => raw31471 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31471step0 raw31471; decide +kernel
      have hl : raw31471step0Labels = raw31471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31471 raw31471Labels permutation434 hz
    mixedMoment B raw31471step0 raw31471step0Labels = mixedMoment B raw31471step1 raw31471step1Labels := by
      have ha : raw31471step1 = (fun i j => raw31471step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31471step1 raw31471step0; decide +kernel
      have hl : raw31471step1Labels = raw31471step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31471step0 raw31471step0Labels permutation33 permutation2
    _ = mixedMoment B node4838 node4838Labels := by rfl

theorem canonical31472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31472 raw31472Labels = mixedMoment B node4329 node4329Labels := by
  calc
    _ = mixedMoment B node4329 node4329Labels := by rfl

theorem canonical31473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31473 raw31473Labels = mixedMoment B node4666 node4666Labels := by
  calc
    _ = mixedMoment B node4666 node4666Labels := by rfl

theorem canonical31474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31474 raw31474Labels = mixedMoment B node4774 node4774Labels := by
  calc
    _ = mixedMoment B node4774 node4774Labels := by rfl

theorem canonical31475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31475 raw31475Labels = mixedMoment B node4802 node4802Labels := by
  calc
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical31476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31476 raw31476Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw31476 raw31476Labels = mixedMoment B raw31476step0 raw31476step0Labels := by
      have ha : raw31476step0 = (fun i j => raw31476 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31476step0 raw31476; decide +kernel
      have hl : raw31476step0Labels = raw31476Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31476 raw31476Labels permutation153 permutation2
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical31477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31477 raw31477Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw31477 raw31477Labels = mixedMoment B raw31477step0 raw31477step0Labels := by
      have hz : ∀ j, raw31477 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31477step0 = (fun i j => raw31477 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31477step0 raw31477; decide +kernel
      have hl : raw31477step0Labels = raw31477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31477 raw31477Labels permutation434 hz
    mixedMoment B raw31477step0 raw31477step0Labels = mixedMoment B raw31477step1 raw31477step1Labels := by
      have ha : raw31477step1 = (fun i j => raw31477step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31477step1 raw31477step0; decide +kernel
      have hl : raw31477step1Labels = raw31477step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31477step0 raw31477step0Labels permutation33 permutation2
    _ = mixedMoment B node4335 node4335Labels := by rfl

theorem canonical31478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31478 raw31478Labels = mixedMoment B node4670 node4670Labels := by
  calc
    mixedMoment B raw31478 raw31478Labels = mixedMoment B raw31478step0 raw31478step0Labels := by
      have hz : ∀ j, raw31478 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31478step0 = (fun i j => raw31478 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31478step0 raw31478; decide +kernel
      have hl : raw31478step0Labels = raw31478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31478 raw31478Labels permutation434 hz
    mixedMoment B raw31478step0 raw31478step0Labels = mixedMoment B raw31478step1 raw31478step1Labels := by
      have ha : raw31478step1 = (fun i j => raw31478step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31478step1 raw31478step0; decide +kernel
      have hl : raw31478step1Labels = raw31478step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31478step0 raw31478step0Labels permutation33 permutation2
    _ = mixedMoment B node4670 node4670Labels := by rfl

theorem canonical31479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31479 raw31479Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw31479 raw31479Labels = mixedMoment B raw31479step0 raw31479step0Labels := by
      have hz : ∀ j, raw31479 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31479step0 = (fun i j => raw31479 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31479step0 raw31479; decide +kernel
      have hl : raw31479step0Labels = raw31479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31479 raw31479Labels permutation434 hz
    mixedMoment B raw31479step0 raw31479step0Labels = mixedMoment B raw31479step1 raw31479step1Labels := by
      have ha : raw31479step1 = (fun i j => raw31479step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31479step1 raw31479step0; decide +kernel
      have hl : raw31479step1Labels = raw31479step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31479step0 raw31479step0Labels permutation33 permutation2
    _ = mixedMoment B node4777 node4777Labels := by rfl

theorem canonical31480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31480 raw31480Labels = mixedMoment B node4757 node4757Labels := by
  calc
    mixedMoment B raw31480 raw31480Labels = mixedMoment B raw31480step0 raw31480step0Labels := by
      have ha : raw31480step0 = (fun i j => raw31480 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31480step0 raw31480; decide +kernel
      have hl : raw31480step0Labels = raw31480Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31480 raw31480Labels permutation159 permutation2
    _ = mixedMoment B node4757 node4757Labels := by rfl

theorem canonical31481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31481 raw31481Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw31481 raw31481Labels = mixedMoment B raw31481step0 raw31481step0Labels := by
      have hz : ∀ j, raw31481 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31481step0 = (fun i j => raw31481 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31481step0 raw31481; decide +kernel
      have hl : raw31481step0Labels = raw31481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31481 raw31481Labels permutation434 hz
    mixedMoment B raw31481step0 raw31481step0Labels = mixedMoment B raw31481step1 raw31481step1Labels := by
      have ha : raw31481step1 = (fun i j => raw31481step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31481step1 raw31481step0; decide +kernel
      have hl : raw31481step1Labels = raw31481step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31481step0 raw31481step0Labels permutation33 permutation2
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical31482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31482 raw31482Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw31482 raw31482Labels = mixedMoment B raw31482step0 raw31482step0Labels := by
      have hz : ∀ j, raw31482 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31482step0 = (fun i j => raw31482 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31482step0 raw31482; decide +kernel
      have hl : raw31482step0Labels = raw31482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31482 raw31482Labels permutation434 hz
    _ = mixedMoment B node4335 node4335Labels := by rfl

theorem canonical31483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31483 raw31483Labels = mixedMoment B node4670 node4670Labels := by
  calc
    mixedMoment B raw31483 raw31483Labels = mixedMoment B raw31483step0 raw31483step0Labels := by
      have hz : ∀ j, raw31483 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31483step0 = (fun i j => raw31483 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31483step0 raw31483; decide +kernel
      have hl : raw31483step0Labels = raw31483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31483 raw31483Labels permutation434 hz
    _ = mixedMoment B node4670 node4670Labels := by rfl

theorem canonical31484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31484 raw31484Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw31484 raw31484Labels = mixedMoment B raw31484step0 raw31484step0Labels := by
      have hz : ∀ j, raw31484 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31484step0 = (fun i j => raw31484 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31484step0 raw31484; decide +kernel
      have hl : raw31484step0Labels = raw31484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31484 raw31484Labels permutation434 hz
    _ = mixedMoment B node4777 node4777Labels := by rfl

theorem canonical31485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31485 raw31485Labels = mixedMoment B node4757 node4757Labels := by
  calc
    mixedMoment B raw31485 raw31485Labels = mixedMoment B raw31485step0 raw31485step0Labels := by
      have ha : raw31485step0 = (fun i j => raw31485 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31485step0 raw31485; decide +kernel
      have hl : raw31485step0Labels = raw31485Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31485 raw31485Labels permutation158 permutation2
    _ = mixedMoment B node4757 node4757Labels := by rfl

theorem canonical31486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31486 raw31486Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw31486 raw31486Labels = mixedMoment B raw31486step0 raw31486step0Labels := by
      have hz : ∀ j, raw31486 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31486step0 = (fun i j => raw31486 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31486step0 raw31486; decide +kernel
      have hl : raw31486step0Labels = raw31486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31486 raw31486Labels permutation434 hz
    _ = mixedMoment B node4807 node4807Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical246
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical31517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31517 raw31517Labels = mixedMoment B node2682 node2682Labels := by
  calc
    mixedMoment B raw31517 raw31517Labels = mixedMoment B raw31517step0 raw31517step0Labels := by
      have hz : ∀ j, raw31517 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31517step0 = (fun i j => raw31517 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31517step0 raw31517; decide +kernel
      have hl : raw31517step0Labels = raw31517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31517 raw31517Labels permutation434 hz
    mixedMoment B raw31517step0 raw31517step0Labels = mixedMoment B raw31517step1 raw31517step1Labels := by
      have ha : raw31517step1 = (fun i j => raw31517step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31517step1 raw31517step0; decide +kernel
      have hl : raw31517step1Labels = raw31517step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31517step0 raw31517step0Labels permutation32 permutation7
    mixedMoment B raw31517step1 raw31517step1Labels = mixedMoment B raw31517step2 raw31517step2Labels := by
      have ha : raw31517step2 = -raw31517step1 := by apply Matrix.ext; change ∀ i j, raw31517step2 i j = -(raw31517step1 i j); unfold raw31517step2 raw31517step1; decide +kernel
      have hl : raw31517step2Labels = raw31517step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31517step2 raw31517step2Labels = mixedMoment B raw31517step3 raw31517step3Labels := by
      have ha : raw31517step3 = raw31517step2 := by apply Matrix.ext; unfold raw31517step3 raw31517step2; decide +kernel
      have hl : raw31517step2Labels = labelEmbedding1 ∘ raw31517step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31517step2 raw31517step2Labels raw31517step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2682 node2682Labels := by rfl

theorem canonical31518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31518 raw31518Labels = mixedMoment B node2736 node2736Labels := by
  calc
    mixedMoment B raw31518 raw31518Labels = mixedMoment B raw31518step0 raw31518step0Labels := by
      have hz : ∀ j, raw31518 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31518step0 = (fun i j => raw31518 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31518step0 raw31518; decide +kernel
      have hl : raw31518step0Labels = raw31518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31518 raw31518Labels permutation434 hz
    mixedMoment B raw31518step0 raw31518step0Labels = mixedMoment B raw31518step1 raw31518step1Labels := by
      have ha : raw31518step1 = (fun i j => raw31518step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31518step1 raw31518step0; decide +kernel
      have hl : raw31518step1Labels = raw31518step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31518step0 raw31518step0Labels permutation32 permutation7
    mixedMoment B raw31518step1 raw31518step1Labels = mixedMoment B raw31518step2 raw31518step2Labels := by
      have ha : raw31518step2 = -raw31518step1 := by apply Matrix.ext; change ∀ i j, raw31518step2 i j = -(raw31518step1 i j); unfold raw31518step2 raw31518step1; decide +kernel
      have hl : raw31518step2Labels = raw31518step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31518step2 raw31518step2Labels = mixedMoment B raw31518step3 raw31518step3Labels := by
      have ha : raw31518step3 = raw31518step2 := by apply Matrix.ext; unfold raw31518step3 raw31518step2; decide +kernel
      have hl : raw31518step2Labels = labelEmbedding1 ∘ raw31518step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31518step2 raw31518step2Labels raw31518step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2736 node2736Labels := by rfl

theorem canonical31519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31519 raw31519Labels = mixedMoment B node2701 node2701Labels := by
  calc
    mixedMoment B raw31519 raw31519Labels = mixedMoment B raw31519step0 raw31519step0Labels := by
      have ha : raw31519step0 = (fun i j => raw31519 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31519step0 raw31519; decide +kernel
      have hl : raw31519step0Labels = raw31519Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31519 raw31519Labels permutation158 permutation7
    mixedMoment B raw31519step0 raw31519step0Labels = mixedMoment B raw31519step1 raw31519step1Labels := by
      have ha : raw31519step1 = -raw31519step0 := by apply Matrix.ext; change ∀ i j, raw31519step1 i j = -(raw31519step0 i j); unfold raw31519step1 raw31519step0; decide +kernel
      have hl : raw31519step1Labels = raw31519step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31519step1 raw31519step1Labels = mixedMoment B raw31519step2 raw31519step2Labels := by
      have ha : raw31519step2 = raw31519step1 := by apply Matrix.ext; unfold raw31519step2 raw31519step1; decide +kernel
      have hl : raw31519step1Labels = labelEmbedding1 ∘ raw31519step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31519step1 raw31519step1Labels raw31519step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2701 node2701Labels := by rfl

theorem canonical31520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31520 raw31520Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw31520 raw31520Labels = mixedMoment B raw31520step0 raw31520step0Labels := by
      have hz : ∀ j, raw31520 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31520step0 = (fun i j => raw31520 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31520step0 raw31520; decide +kernel
      have hl : raw31520step0Labels = raw31520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31520 raw31520Labels permutation434 hz
    mixedMoment B raw31520step0 raw31520step0Labels = mixedMoment B raw31520step1 raw31520step1Labels := by
      have ha : raw31520step1 = (fun i j => raw31520step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31520step1 raw31520step0; decide +kernel
      have hl : raw31520step1Labels = raw31520step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31520step0 raw31520step0Labels permutation32 permutation7
    mixedMoment B raw31520step1 raw31520step1Labels = mixedMoment B raw31520step2 raw31520step2Labels := by
      have ha : raw31520step2 = -raw31520step1 := by apply Matrix.ext; change ∀ i j, raw31520step2 i j = -(raw31520step1 i j); unfold raw31520step2 raw31520step1; decide +kernel
      have hl : raw31520step2Labels = raw31520step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31520step2 raw31520step2Labels = mixedMoment B raw31520step3 raw31520step3Labels := by
      have ha : raw31520step3 = raw31520step2 := by apply Matrix.ext; unfold raw31520step3 raw31520step2; decide +kernel
      have hl : raw31520step2Labels = labelEmbedding1 ∘ raw31520step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31520step2 raw31520step2Labels raw31520step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical31521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31521 raw31521Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw31521 raw31521Labels = mixedMoment B raw31521step0 raw31521step0Labels := by
      have hz : ∀ j, raw31521 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31521step0 = (fun i j => raw31521 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31521step0 raw31521; decide +kernel
      have hl : raw31521step0Labels = raw31521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31521 raw31521Labels permutation434 hz
    mixedMoment B raw31521step0 raw31521step0Labels = mixedMoment B raw31521step1 raw31521step1Labels := by
      have ha : raw31521step1 = (fun i j => raw31521step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31521step1 raw31521step0; decide +kernel
      have hl : raw31521step1Labels = raw31521step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31521step0 raw31521step0Labels permutation33 permutation7
    mixedMoment B raw31521step1 raw31521step1Labels = mixedMoment B raw31521step2 raw31521step2Labels := by
      have ha : raw31521step2 = -raw31521step1 := by apply Matrix.ext; change ∀ i j, raw31521step2 i j = -(raw31521step1 i j); unfold raw31521step2 raw31521step1; decide +kernel
      have hl : raw31521step2Labels = raw31521step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31521step2 raw31521step2Labels = mixedMoment B raw31521step3 raw31521step3Labels := by
      have ha : raw31521step3 = raw31521step2 := by apply Matrix.ext; unfold raw31521step3 raw31521step2; decide +kernel
      have hl : raw31521step2Labels = labelEmbedding1 ∘ raw31521step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31521step2 raw31521step2Labels raw31521step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical31522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31522 raw31522Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw31522 raw31522Labels = mixedMoment B raw31522step0 raw31522step0Labels := by
      have hz : ∀ j, raw31522 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31522step0 = (fun i j => raw31522 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31522step0 raw31522; decide +kernel
      have hl : raw31522step0Labels = raw31522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31522 raw31522Labels permutation434 hz
    mixedMoment B raw31522step0 raw31522step0Labels = mixedMoment B raw31522step1 raw31522step1Labels := by
      have hz : ∀ j, raw31522step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31522step1 = (fun i j => raw31522step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31522step1 raw31522step0; decide +kernel
      have hl : raw31522step1Labels = raw31522step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31522step0 raw31522step0Labels permutation56 hz
    mixedMoment B raw31522step1 raw31522step1Labels = mixedMoment B raw31522step2 raw31522step2Labels := by
      have ha : raw31522step2 = (fun i j => raw31522step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31522step2 raw31522step1; decide +kernel
      have hl : raw31522step2Labels = raw31522step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31522step1 raw31522step1Labels permutation8 permutation7
    mixedMoment B raw31522step2 raw31522step2Labels = mixedMoment B raw31522step3 raw31522step3Labels := by
      have ha : raw31522step3 = -raw31522step2 := by apply Matrix.ext; change ∀ i j, raw31522step3 i j = -(raw31522step2 i j); unfold raw31522step3 raw31522step2; decide +kernel
      have hl : raw31522step3Labels = raw31522step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31522step3 raw31522step3Labels = mixedMoment B raw31522step4 raw31522step4Labels := by
      have ha : raw31522step4 = raw31522step3 := by apply Matrix.ext; unfold raw31522step4 raw31522step3; decide +kernel
      have hl : raw31522step3Labels = labelEmbedding1 ∘ raw31522step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31522step3 raw31522step3Labels raw31522step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1751 node1751Labels := by rfl

theorem canonical31523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31523 raw31523Labels = mixedMoment B node2288 node2288Labels := by
  calc
    mixedMoment B raw31523 raw31523Labels = mixedMoment B raw31523step0 raw31523step0Labels := by
      have hz : ∀ j, raw31523 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31523step0 = (fun i j => raw31523 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31523step0 raw31523; decide +kernel
      have hl : raw31523step0Labels = raw31523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31523 raw31523Labels permutation434 hz
    mixedMoment B raw31523step0 raw31523step0Labels = mixedMoment B raw31523step1 raw31523step1Labels := by
      have hz : ∀ j, raw31523step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31523step1 = (fun i j => raw31523step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31523step1 raw31523step0; decide +kernel
      have hl : raw31523step1Labels = raw31523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31523step0 raw31523step0Labels permutation56 hz
    mixedMoment B raw31523step1 raw31523step1Labels = mixedMoment B raw31523step2 raw31523step2Labels := by
      have ha : raw31523step2 = (fun i j => raw31523step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31523step2 raw31523step1; decide +kernel
      have hl : raw31523step2Labels = raw31523step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31523step1 raw31523step1Labels permutation8 permutation7
    mixedMoment B raw31523step2 raw31523step2Labels = mixedMoment B raw31523step3 raw31523step3Labels := by
      have ha : raw31523step3 = -raw31523step2 := by apply Matrix.ext; change ∀ i j, raw31523step3 i j = -(raw31523step2 i j); unfold raw31523step3 raw31523step2; decide +kernel
      have hl : raw31523step3Labels = raw31523step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31523step3 raw31523step3Labels = mixedMoment B raw31523step4 raw31523step4Labels := by
      have ha : raw31523step4 = raw31523step3 := by apply Matrix.ext; unfold raw31523step4 raw31523step3; decide +kernel
      have hl : raw31523step3Labels = labelEmbedding1 ∘ raw31523step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31523step3 raw31523step3Labels raw31523step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2288 node2288Labels := by rfl

theorem canonical31524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31524 raw31524Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw31524 raw31524Labels = mixedMoment B raw31524step0 raw31524step0Labels := by
      have hz : ∀ j, raw31524 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw31524step0 = (fun i j => raw31524 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw31524step0 raw31524; decide +kernel
      have hl : raw31524step0Labels = raw31524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31524 raw31524Labels permutation265 hz
    mixedMoment B raw31524step0 raw31524step0Labels = mixedMoment B raw31524step1 raw31524step1Labels := by
      have ha : raw31524step1 = (fun i j => raw31524step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31524step1 raw31524step0; decide +kernel
      have hl : raw31524step1Labels = raw31524step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31524step0 raw31524step0Labels permutation38 permutation7
    mixedMoment B raw31524step1 raw31524step1Labels = mixedMoment B raw31524step2 raw31524step2Labels := by
      have ha : raw31524step2 = -raw31524step1 := by apply Matrix.ext; change ∀ i j, raw31524step2 i j = -(raw31524step1 i j); unfold raw31524step2 raw31524step1; decide +kernel
      have hl : raw31524step2Labels = raw31524step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31524step2 raw31524step2Labels = mixedMoment B raw31524step3 raw31524step3Labels := by
      have ha : raw31524step3 = raw31524step2 := by apply Matrix.ext; unfold raw31524step3 raw31524step2; decide +kernel
      have hl : raw31524step2Labels = labelEmbedding1 ∘ raw31524step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31524step2 raw31524step2Labels raw31524step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2225 node2225Labels := by rfl

theorem canonical31525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31525 raw31525Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw31525 raw31525Labels = mixedMoment B raw31525step0 raw31525step0Labels := by
      have hz : ∀ j, raw31525 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31525step0 = (fun i j => raw31525 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31525step0 raw31525; decide +kernel
      have hl : raw31525step0Labels = raw31525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31525 raw31525Labels permutation434 hz
    mixedMoment B raw31525step0 raw31525step0Labels = mixedMoment B raw31525step1 raw31525step1Labels := by
      have hz : ∀ j, raw31525step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31525step1 = (fun i j => raw31525step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31525step1 raw31525step0; decide +kernel
      have hl : raw31525step1Labels = raw31525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31525step0 raw31525step0Labels permutation56 hz
    mixedMoment B raw31525step1 raw31525step1Labels = mixedMoment B raw31525step2 raw31525step2Labels := by
      have ha : raw31525step2 = (fun i j => raw31525step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31525step2 raw31525step1; decide +kernel
      have hl : raw31525step2Labels = raw31525step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31525step1 raw31525step1Labels permutation8 permutation7
    mixedMoment B raw31525step2 raw31525step2Labels = mixedMoment B raw31525step3 raw31525step3Labels := by
      have ha : raw31525step3 = -raw31525step2 := by apply Matrix.ext; change ∀ i j, raw31525step3 i j = -(raw31525step2 i j); unfold raw31525step3 raw31525step2; decide +kernel
      have hl : raw31525step3Labels = raw31525step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31525step3 raw31525step3Labels = mixedMoment B raw31525step4 raw31525step4Labels := by
      have ha : raw31525step4 = raw31525step3 := by apply Matrix.ext; unfold raw31525step4 raw31525step3; decide +kernel
      have hl : raw31525step3Labels = labelEmbedding1 ∘ raw31525step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31525step3 raw31525step3Labels raw31525step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

theorem canonical31526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31526 raw31526Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw31526 raw31526Labels = mixedMoment B raw31526step0 raw31526step0Labels := by
      have hz : ∀ j, raw31526 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31526step0 = (fun i j => raw31526 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31526step0 raw31526; decide +kernel
      have hl : raw31526step0Labels = raw31526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31526 raw31526Labels permutation434 hz
    mixedMoment B raw31526step0 raw31526step0Labels = mixedMoment B raw31526step1 raw31526step1Labels := by
      have hz : ∀ j, raw31526step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31526step1 = (fun i j => raw31526step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31526step1 raw31526step0; decide +kernel
      have hl : raw31526step1Labels = raw31526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31526step0 raw31526step0Labels permutation56 hz
    mixedMoment B raw31526step1 raw31526step1Labels = mixedMoment B raw31526step2 raw31526step2Labels := by
      have ha : raw31526step2 = (fun i j => raw31526step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31526step2 raw31526step1; decide +kernel
      have hl : raw31526step2Labels = raw31526step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31526step1 raw31526step1Labels permutation9 permutation7
    mixedMoment B raw31526step2 raw31526step2Labels = mixedMoment B raw31526step3 raw31526step3Labels := by
      have ha : raw31526step3 = -raw31526step2 := by apply Matrix.ext; change ∀ i j, raw31526step3 i j = -(raw31526step2 i j); unfold raw31526step3 raw31526step2; decide +kernel
      have hl : raw31526step3Labels = raw31526step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31526step3 raw31526step3Labels = mixedMoment B raw31526step4 raw31526step4Labels := by
      have ha : raw31526step4 = raw31526step3 := by apply Matrix.ext; unfold raw31526step4 raw31526step3; decide +kernel
      have hl : raw31526step3Labels = labelEmbedding1 ∘ raw31526step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31526step3 raw31526step3Labels raw31526step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

theorem canonical31527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31527 raw31527Labels = mixedMoment B node1691 node1691Labels := by
  calc
    mixedMoment B raw31527 raw31527Labels = mixedMoment B raw31527step0 raw31527step0Labels := by
      have hz : ∀ j, raw31527 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31527step0 = (fun i j => raw31527 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31527step0 raw31527; decide +kernel
      have hl : raw31527step0Labels = raw31527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31527 raw31527Labels permutation434 hz
    mixedMoment B raw31527step0 raw31527step0Labels = mixedMoment B raw31527step1 raw31527step1Labels := by
      have ha : raw31527step1 = (fun i j => raw31527step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31527step1 raw31527step0; decide +kernel
      have hl : raw31527step1Labels = raw31527step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31527step0 raw31527step0Labels permutation32 permutation7
    mixedMoment B raw31527step1 raw31527step1Labels = mixedMoment B raw31527step2 raw31527step2Labels := by
      have ha : raw31527step2 = -raw31527step1 := by apply Matrix.ext; change ∀ i j, raw31527step2 i j = -(raw31527step1 i j); unfold raw31527step2 raw31527step1; decide +kernel
      have hl : raw31527step2Labels = raw31527step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31527step2 raw31527step2Labels = mixedMoment B raw31527step3 raw31527step3Labels := by
      have ha : raw31527step3 = raw31527step2 := by apply Matrix.ext; unfold raw31527step3 raw31527step2; decide +kernel
      have hl : raw31527step2Labels = labelEmbedding1 ∘ raw31527step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31527step2 raw31527step2Labels raw31527step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1691 node1691Labels := by rfl

theorem canonical31528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31528 raw31528Labels = mixedMoment B node2166 node2166Labels := by
  calc
    mixedMoment B raw31528 raw31528Labels = mixedMoment B raw31528step0 raw31528step0Labels := by
      have hz : ∀ j, raw31528 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31528step0 = (fun i j => raw31528 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31528step0 raw31528; decide +kernel
      have hl : raw31528step0Labels = raw31528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31528 raw31528Labels permutation434 hz
    mixedMoment B raw31528step0 raw31528step0Labels = mixedMoment B raw31528step1 raw31528step1Labels := by
      have ha : raw31528step1 = (fun i j => raw31528step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31528step1 raw31528step0; decide +kernel
      have hl : raw31528step1Labels = raw31528step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31528step0 raw31528step0Labels permutation32 permutation7
    mixedMoment B raw31528step1 raw31528step1Labels = mixedMoment B raw31528step2 raw31528step2Labels := by
      have ha : raw31528step2 = -raw31528step1 := by apply Matrix.ext; change ∀ i j, raw31528step2 i j = -(raw31528step1 i j); unfold raw31528step2 raw31528step1; decide +kernel
      have hl : raw31528step2Labels = raw31528step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31528step2 raw31528step2Labels = mixedMoment B raw31528step3 raw31528step3Labels := by
      have ha : raw31528step3 = raw31528step2 := by apply Matrix.ext; unfold raw31528step3 raw31528step2; decide +kernel
      have hl : raw31528step2Labels = labelEmbedding1 ∘ raw31528step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31528step2 raw31528step2Labels raw31528step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2166 node2166Labels := by rfl

theorem canonical31529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31529 raw31529Labels = mixedMoment B node2183 node2183Labels := by
  calc
    mixedMoment B raw31529 raw31529Labels = mixedMoment B raw31529step0 raw31529step0Labels := by
      have ha : raw31529step0 = (fun i j => raw31529 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31529step0 raw31529; decide +kernel
      have hl : raw31529step0Labels = raw31529Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31529 raw31529Labels permutation158 permutation7
    mixedMoment B raw31529step0 raw31529step0Labels = mixedMoment B raw31529step1 raw31529step1Labels := by
      have ha : raw31529step1 = -raw31529step0 := by apply Matrix.ext; change ∀ i j, raw31529step1 i j = -(raw31529step0 i j); unfold raw31529step1 raw31529step0; decide +kernel
      have hl : raw31529step1Labels = raw31529step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31529step1 raw31529step1Labels = mixedMoment B raw31529step2 raw31529step2Labels := by
      have ha : raw31529step2 = raw31529step1 := by apply Matrix.ext; unfold raw31529step2 raw31529step1; decide +kernel
      have hl : raw31529step1Labels = labelEmbedding1 ∘ raw31529step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31529step1 raw31529step1Labels raw31529step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2183 node2183Labels := by rfl

theorem canonical31530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31530 raw31530Labels = mixedMoment B node2227 node2227Labels := by
  calc
    mixedMoment B raw31530 raw31530Labels = mixedMoment B raw31530step0 raw31530step0Labels := by
      have hz : ∀ j, raw31530 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31530step0 = (fun i j => raw31530 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31530step0 raw31530; decide +kernel
      have hl : raw31530step0Labels = raw31530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31530 raw31530Labels permutation434 hz
    mixedMoment B raw31530step0 raw31530step0Labels = mixedMoment B raw31530step1 raw31530step1Labels := by
      have ha : raw31530step1 = (fun i j => raw31530step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31530step1 raw31530step0; decide +kernel
      have hl : raw31530step1Labels = raw31530step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31530step0 raw31530step0Labels permutation32 permutation7
    mixedMoment B raw31530step1 raw31530step1Labels = mixedMoment B raw31530step2 raw31530step2Labels := by
      have ha : raw31530step2 = -raw31530step1 := by apply Matrix.ext; change ∀ i j, raw31530step2 i j = -(raw31530step1 i j); unfold raw31530step2 raw31530step1; decide +kernel
      have hl : raw31530step2Labels = raw31530step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31530step2 raw31530step2Labels = mixedMoment B raw31530step3 raw31530step3Labels := by
      have ha : raw31530step3 = raw31530step2 := by apply Matrix.ext; unfold raw31530step3 raw31530step2; decide +kernel
      have hl : raw31530step2Labels = labelEmbedding1 ∘ raw31530step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31530step2 raw31530step2Labels raw31530step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2227 node2227Labels := by rfl

theorem canonical31531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31531 raw31531Labels = mixedMoment B node2227 node2227Labels := by
  calc
    mixedMoment B raw31531 raw31531Labels = mixedMoment B raw31531step0 raw31531step0Labels := by
      have hz : ∀ j, raw31531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31531step0 = (fun i j => raw31531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31531step0 raw31531; decide +kernel
      have hl : raw31531step0Labels = raw31531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31531 raw31531Labels permutation434 hz
    mixedMoment B raw31531step0 raw31531step0Labels = mixedMoment B raw31531step1 raw31531step1Labels := by
      have ha : raw31531step1 = (fun i j => raw31531step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31531step1 raw31531step0; decide +kernel
      have hl : raw31531step1Labels = raw31531step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31531step0 raw31531step0Labels permutation33 permutation7
    mixedMoment B raw31531step1 raw31531step1Labels = mixedMoment B raw31531step2 raw31531step2Labels := by
      have ha : raw31531step2 = -raw31531step1 := by apply Matrix.ext; change ∀ i j, raw31531step2 i j = -(raw31531step1 i j); unfold raw31531step2 raw31531step1; decide +kernel
      have hl : raw31531step2Labels = raw31531step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31531step2 raw31531step2Labels = mixedMoment B raw31531step3 raw31531step3Labels := by
      have ha : raw31531step3 = raw31531step2 := by apply Matrix.ext; unfold raw31531step3 raw31531step2; decide +kernel
      have hl : raw31531step2Labels = labelEmbedding1 ∘ raw31531step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31531step2 raw31531step2Labels raw31531step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2227 node2227Labels := by rfl

theorem canonical31532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31532 raw31532Labels = mixedMoment B node1671 node1671Labels := by
  calc
    mixedMoment B raw31532 raw31532Labels = mixedMoment B raw31532step0 raw31532step0Labels := by
      have ha : raw31532step0 = (fun i j => raw31532 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31532step0 raw31532; decide +kernel
      have hl : raw31532step0Labels = raw31532Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31532 raw31532Labels permutation158 permutation7
    mixedMoment B raw31532step0 raw31532step0Labels = mixedMoment B raw31532step1 raw31532step1Labels := by
      have ha : raw31532step1 = -raw31532step0 := by apply Matrix.ext; change ∀ i j, raw31532step1 i j = -(raw31532step0 i j); unfold raw31532step1 raw31532step0; decide +kernel
      have hl : raw31532step1Labels = raw31532step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31532step1 raw31532step1Labels = mixedMoment B raw31532step2 raw31532step2Labels := by
      have ha : raw31532step2 = raw31532step1 := by apply Matrix.ext; unfold raw31532step2 raw31532step1; decide +kernel
      have hl : raw31532step1Labels = labelEmbedding1 ∘ raw31532step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31532step1 raw31532step1Labels raw31532step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1671 node1671Labels := by rfl

theorem canonical31533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31533 raw31533Labels = mixedMoment B node2148 node2148Labels := by
  calc
    mixedMoment B raw31533 raw31533Labels = mixedMoment B raw31533step0 raw31533step0Labels := by
      have ha : raw31533step0 = (fun i j => raw31533 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31533step0 raw31533; decide +kernel
      have hl : raw31533step0Labels = raw31533Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31533 raw31533Labels permutation158 permutation7
    mixedMoment B raw31533step0 raw31533step0Labels = mixedMoment B raw31533step1 raw31533step1Labels := by
      have ha : raw31533step1 = -raw31533step0 := by apply Matrix.ext; change ∀ i j, raw31533step1 i j = -(raw31533step0 i j); unfold raw31533step1 raw31533step0; decide +kernel
      have hl : raw31533step1Labels = raw31533step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31533step1 raw31533step1Labels = mixedMoment B raw31533step2 raw31533step2Labels := by
      have ha : raw31533step2 = raw31533step1 := by apply Matrix.ext; unfold raw31533step2 raw31533step1; decide +kernel
      have hl : raw31533step1Labels = labelEmbedding1 ∘ raw31533step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31533step1 raw31533step1Labels raw31533step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2148 node2148Labels := by rfl

theorem canonical31534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31534 raw31534Labels = mixedMoment B node2199 node2199Labels := by
  calc
    mixedMoment B raw31534 raw31534Labels = mixedMoment B raw31534step0 raw31534step0Labels := by
      have ha : raw31534step0 = (fun i j => raw31534 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31534step0 raw31534; decide +kernel
      have hl : raw31534step0Labels = raw31534Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31534 raw31534Labels permutation158 permutation7
    mixedMoment B raw31534step0 raw31534step0Labels = mixedMoment B raw31534step1 raw31534step1Labels := by
      have ha : raw31534step1 = -raw31534step0 := by apply Matrix.ext; change ∀ i j, raw31534step1 i j = -(raw31534step0 i j); unfold raw31534step1 raw31534step0; decide +kernel
      have hl : raw31534step1Labels = raw31534step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31534step1 raw31534step1Labels = mixedMoment B raw31534step2 raw31534step2Labels := by
      have ha : raw31534step2 = raw31534step1 := by apply Matrix.ext; unfold raw31534step2 raw31534step1; decide +kernel
      have hl : raw31534step1Labels = labelEmbedding1 ∘ raw31534step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31534step1 raw31534step1Labels raw31534step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2199 node2199Labels := by rfl

theorem canonical31535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31535 raw31535Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw31535 raw31535Labels = mixedMoment B raw31535step0 raw31535step0Labels := by
      have ha : raw31535step0 = (fun i j => raw31535 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31535step0 raw31535; decide +kernel
      have hl : raw31535step0Labels = raw31535Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31535 raw31535Labels permutation158 permutation7
    mixedMoment B raw31535step0 raw31535step0Labels = mixedMoment B raw31535step1 raw31535step1Labels := by
      have ha : raw31535step1 = -raw31535step0 := by apply Matrix.ext; change ∀ i j, raw31535step1 i j = -(raw31535step0 i j); unfold raw31535step1 raw31535step0; decide +kernel
      have hl : raw31535step1Labels = raw31535step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31535step1 raw31535step1Labels = mixedMoment B raw31535step2 raw31535step2Labels := by
      have ha : raw31535step2 = raw31535step1 := by apply Matrix.ext; unfold raw31535step2 raw31535step1; decide +kernel
      have hl : raw31535step1Labels = labelEmbedding1 ∘ raw31535step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31535step1 raw31535step1Labels raw31535step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

theorem canonical31536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31536 raw31536Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw31536 raw31536Labels = mixedMoment B raw31536step0 raw31536step0Labels := by
      have ha : raw31536step0 = (fun i j => raw31536 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31536step0 raw31536; decide +kernel
      have hl : raw31536step0Labels = raw31536Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31536 raw31536Labels permutation159 permutation7
    mixedMoment B raw31536step0 raw31536step0Labels = mixedMoment B raw31536step1 raw31536step1Labels := by
      have ha : raw31536step1 = -raw31536step0 := by apply Matrix.ext; change ∀ i j, raw31536step1 i j = -(raw31536step0 i j); unfold raw31536step1 raw31536step0; decide +kernel
      have hl : raw31536step1Labels = raw31536step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31536step1 raw31536step1Labels = mixedMoment B raw31536step2 raw31536step2Labels := by
      have ha : raw31536step2 = raw31536step1 := by apply Matrix.ext; unfold raw31536step2 raw31536step1; decide +kernel
      have hl : raw31536step1Labels = labelEmbedding1 ∘ raw31536step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31536step1 raw31536step1Labels raw31536step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

theorem canonical31537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31537 raw31537Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw31537 raw31537Labels = mixedMoment B raw31537step0 raw31537step0Labels := by
      have hz : ∀ j, raw31537 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31537step0 = (fun i j => raw31537 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31537step0 raw31537; decide +kernel
      have hl : raw31537step0Labels = raw31537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31537 raw31537Labels permutation434 hz
    mixedMoment B raw31537step0 raw31537step0Labels = mixedMoment B raw31537step1 raw31537step1Labels := by
      have ha : raw31537step1 = (fun i j => raw31537step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31537step1 raw31537step0; decide +kernel
      have hl : raw31537step1Labels = raw31537step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31537step0 raw31537step0Labels permutation33 permutation7
    mixedMoment B raw31537step1 raw31537step1Labels = mixedMoment B raw31537step2 raw31537step2Labels := by
      have ha : raw31537step2 = -raw31537step1 := by apply Matrix.ext; change ∀ i j, raw31537step2 i j = -(raw31537step1 i j); unfold raw31537step2 raw31537step1; decide +kernel
      have hl : raw31537step2Labels = raw31537step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31537step2 raw31537step2Labels = mixedMoment B raw31537step3 raw31537step3Labels := by
      have ha : raw31537step3 = raw31537step2 := by apply Matrix.ext; unfold raw31537step3 raw31537step2; decide +kernel
      have hl : raw31537step2Labels = labelEmbedding1 ∘ raw31537step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31537step2 raw31537step2Labels raw31537step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

theorem canonical31538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31538 raw31538Labels = mixedMoment B node2164 node2164Labels := by
  calc
    mixedMoment B raw31538 raw31538Labels = mixedMoment B raw31538step0 raw31538step0Labels := by
      have hz : ∀ j, raw31538 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31538step0 = (fun i j => raw31538 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31538step0 raw31538; decide +kernel
      have hl : raw31538step0Labels = raw31538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31538 raw31538Labels permutation434 hz
    mixedMoment B raw31538step0 raw31538step0Labels = mixedMoment B raw31538step1 raw31538step1Labels := by
      have ha : raw31538step1 = (fun i j => raw31538step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31538step1 raw31538step0; decide +kernel
      have hl : raw31538step1Labels = raw31538step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31538step0 raw31538step0Labels permutation33 permutation7
    mixedMoment B raw31538step1 raw31538step1Labels = mixedMoment B raw31538step2 raw31538step2Labels := by
      have ha : raw31538step2 = -raw31538step1 := by apply Matrix.ext; change ∀ i j, raw31538step2 i j = -(raw31538step1 i j); unfold raw31538step2 raw31538step1; decide +kernel
      have hl : raw31538step2Labels = raw31538step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31538step2 raw31538step2Labels = mixedMoment B raw31538step3 raw31538step3Labels := by
      have ha : raw31538step3 = raw31538step2 := by apply Matrix.ext; unfold raw31538step3 raw31538step2; decide +kernel
      have hl : raw31538step2Labels = labelEmbedding1 ∘ raw31538step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31538step2 raw31538step2Labels raw31538step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2164 node2164Labels := by rfl

theorem canonical31539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31539 raw31539Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw31539 raw31539Labels = mixedMoment B raw31539step0 raw31539step0Labels := by
      have hz : ∀ j, raw31539 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31539step0 = (fun i j => raw31539 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31539step0 raw31539; decide +kernel
      have hl : raw31539step0Labels = raw31539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31539 raw31539Labels permutation434 hz
    mixedMoment B raw31539step0 raw31539step0Labels = mixedMoment B raw31539step1 raw31539step1Labels := by
      have ha : raw31539step1 = (fun i j => raw31539step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31539step1 raw31539step0; decide +kernel
      have hl : raw31539step1Labels = raw31539step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31539step0 raw31539step0Labels permutation33 permutation7
    mixedMoment B raw31539step1 raw31539step1Labels = mixedMoment B raw31539step2 raw31539step2Labels := by
      have ha : raw31539step2 = -raw31539step1 := by apply Matrix.ext; change ∀ i j, raw31539step2 i j = -(raw31539step1 i j); unfold raw31539step2 raw31539step1; decide +kernel
      have hl : raw31539step2Labels = raw31539step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31539step2 raw31539step2Labels = mixedMoment B raw31539step3 raw31539step3Labels := by
      have ha : raw31539step3 = raw31539step2 := by apply Matrix.ext; unfold raw31539step3 raw31539step2; decide +kernel
      have hl : raw31539step2Labels = labelEmbedding1 ∘ raw31539step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31539step2 raw31539step2Labels raw31539step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

theorem canonical31540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31540 raw31540Labels = mixedMoment B node2181 node2181Labels := by
  calc
    mixedMoment B raw31540 raw31540Labels = mixedMoment B raw31540step0 raw31540step0Labels := by
      have ha : raw31540step0 = (fun i j => raw31540 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31540step0 raw31540; decide +kernel
      have hl : raw31540step0Labels = raw31540Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31540 raw31540Labels permutation159 permutation7
    mixedMoment B raw31540step0 raw31540step0Labels = mixedMoment B raw31540step1 raw31540step1Labels := by
      have ha : raw31540step1 = -raw31540step0 := by apply Matrix.ext; change ∀ i j, raw31540step1 i j = -(raw31540step0 i j); unfold raw31540step1 raw31540step0; decide +kernel
      have hl : raw31540step1Labels = raw31540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31540step1 raw31540step1Labels = mixedMoment B raw31540step2 raw31540step2Labels := by
      have ha : raw31540step2 = raw31540step1 := by apply Matrix.ext; unfold raw31540step2 raw31540step1; decide +kernel
      have hl : raw31540step1Labels = labelEmbedding1 ∘ raw31540step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31540step1 raw31540step1Labels raw31540step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2181 node2181Labels := by rfl

theorem canonical31541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31541 raw31541Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw31541 raw31541Labels = mixedMoment B raw31541step0 raw31541step0Labels := by
      have hz : ∀ j, raw31541 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31541step0 = (fun i j => raw31541 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31541step0 raw31541; decide +kernel
      have hl : raw31541step0Labels = raw31541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31541 raw31541Labels permutation434 hz
    mixedMoment B raw31541step0 raw31541step0Labels = mixedMoment B raw31541step1 raw31541step1Labels := by
      have ha : raw31541step1 = (fun i j => raw31541step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31541step1 raw31541step0; decide +kernel
      have hl : raw31541step1Labels = raw31541step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31541step0 raw31541step0Labels permutation33 permutation7
    mixedMoment B raw31541step1 raw31541step1Labels = mixedMoment B raw31541step2 raw31541step2Labels := by
      have ha : raw31541step2 = -raw31541step1 := by apply Matrix.ext; change ∀ i j, raw31541step2 i j = -(raw31541step1 i j); unfold raw31541step2 raw31541step1; decide +kernel
      have hl : raw31541step2Labels = raw31541step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31541step2 raw31541step2Labels = mixedMoment B raw31541step3 raw31541step3Labels := by
      have ha : raw31541step3 = raw31541step2 := by apply Matrix.ext; unfold raw31541step3 raw31541step2; decide +kernel
      have hl : raw31541step2Labels = labelEmbedding1 ∘ raw31541step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31541step2 raw31541step2Labels raw31541step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical31542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31542 raw31542Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw31542 raw31542Labels = mixedMoment B raw31542step0 raw31542step0Labels := by
      have hz : ∀ j, raw31542 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31542step0 = (fun i j => raw31542 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31542step0 raw31542; decide +kernel
      have hl : raw31542step0Labels = raw31542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31542 raw31542Labels permutation434 hz
    mixedMoment B raw31542step0 raw31542step0Labels = mixedMoment B raw31542step1 raw31542step1Labels := by
      have ha : raw31542step1 = (fun i j => raw31542step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31542step1 raw31542step0; decide +kernel
      have hl : raw31542step1Labels = raw31542step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31542step0 raw31542step0Labels permutation32 permutation7
    mixedMoment B raw31542step1 raw31542step1Labels = mixedMoment B raw31542step2 raw31542step2Labels := by
      have ha : raw31542step2 = -raw31542step1 := by apply Matrix.ext; change ∀ i j, raw31542step2 i j = -(raw31542step1 i j); unfold raw31542step2 raw31542step1; decide +kernel
      have hl : raw31542step2Labels = raw31542step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31542step2 raw31542step2Labels = mixedMoment B raw31542step3 raw31542step3Labels := by
      have ha : raw31542step3 = raw31542step2 := by apply Matrix.ext; unfold raw31542step3 raw31542step2; decide +kernel
      have hl : raw31542step2Labels = labelEmbedding1 ∘ raw31542step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31542step2 raw31542step2Labels raw31542step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

theorem canonical31543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31543 raw31543Labels = mixedMoment B node2164 node2164Labels := by
  calc
    mixedMoment B raw31543 raw31543Labels = mixedMoment B raw31543step0 raw31543step0Labels := by
      have hz : ∀ j, raw31543 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31543step0 = (fun i j => raw31543 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31543step0 raw31543; decide +kernel
      have hl : raw31543step0Labels = raw31543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31543 raw31543Labels permutation434 hz
    mixedMoment B raw31543step0 raw31543step0Labels = mixedMoment B raw31543step1 raw31543step1Labels := by
      have ha : raw31543step1 = (fun i j => raw31543step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31543step1 raw31543step0; decide +kernel
      have hl : raw31543step1Labels = raw31543step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31543step0 raw31543step0Labels permutation32 permutation7
    mixedMoment B raw31543step1 raw31543step1Labels = mixedMoment B raw31543step2 raw31543step2Labels := by
      have ha : raw31543step2 = -raw31543step1 := by apply Matrix.ext; change ∀ i j, raw31543step2 i j = -(raw31543step1 i j); unfold raw31543step2 raw31543step1; decide +kernel
      have hl : raw31543step2Labels = raw31543step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31543step2 raw31543step2Labels = mixedMoment B raw31543step3 raw31543step3Labels := by
      have ha : raw31543step3 = raw31543step2 := by apply Matrix.ext; unfold raw31543step3 raw31543step2; decide +kernel
      have hl : raw31543step2Labels = labelEmbedding1 ∘ raw31543step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31543step2 raw31543step2Labels raw31543step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2164 node2164Labels := by rfl

theorem canonical31544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31544 raw31544Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw31544 raw31544Labels = mixedMoment B raw31544step0 raw31544step0Labels := by
      have hz : ∀ j, raw31544 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31544step0 = (fun i j => raw31544 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31544step0 raw31544; decide +kernel
      have hl : raw31544step0Labels = raw31544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31544 raw31544Labels permutation434 hz
    mixedMoment B raw31544step0 raw31544step0Labels = mixedMoment B raw31544step1 raw31544step1Labels := by
      have ha : raw31544step1 = (fun i j => raw31544step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31544step1 raw31544step0; decide +kernel
      have hl : raw31544step1Labels = raw31544step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31544step0 raw31544step0Labels permutation32 permutation7
    mixedMoment B raw31544step1 raw31544step1Labels = mixedMoment B raw31544step2 raw31544step2Labels := by
      have ha : raw31544step2 = -raw31544step1 := by apply Matrix.ext; change ∀ i j, raw31544step2 i j = -(raw31544step1 i j); unfold raw31544step2 raw31544step1; decide +kernel
      have hl : raw31544step2Labels = raw31544step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31544step2 raw31544step2Labels = mixedMoment B raw31544step3 raw31544step3Labels := by
      have ha : raw31544step3 = raw31544step2 := by apply Matrix.ext; unfold raw31544step3 raw31544step2; decide +kernel
      have hl : raw31544step2Labels = labelEmbedding1 ∘ raw31544step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31544step2 raw31544step2Labels raw31544step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

theorem canonical31545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31545 raw31545Labels = mixedMoment B node2181 node2181Labels := by
  calc
    mixedMoment B raw31545 raw31545Labels = mixedMoment B raw31545step0 raw31545step0Labels := by
      have ha : raw31545step0 = (fun i j => raw31545 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31545step0 raw31545; decide +kernel
      have hl : raw31545step0Labels = raw31545Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31545 raw31545Labels permutation158 permutation7
    mixedMoment B raw31545step0 raw31545step0Labels = mixedMoment B raw31545step1 raw31545step1Labels := by
      have ha : raw31545step1 = -raw31545step0 := by apply Matrix.ext; change ∀ i j, raw31545step1 i j = -(raw31545step0 i j); unfold raw31545step1 raw31545step0; decide +kernel
      have hl : raw31545step1Labels = raw31545step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31545step1 raw31545step1Labels = mixedMoment B raw31545step2 raw31545step2Labels := by
      have ha : raw31545step2 = raw31545step1 := by apply Matrix.ext; unfold raw31545step2 raw31545step1; decide +kernel
      have hl : raw31545step1Labels = labelEmbedding1 ∘ raw31545step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31545step1 raw31545step1Labels raw31545step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2181 node2181Labels := by rfl

theorem canonical31546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31546 raw31546Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw31546 raw31546Labels = mixedMoment B raw31546step0 raw31546step0Labels := by
      have hz : ∀ j, raw31546 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31546step0 = (fun i j => raw31546 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31546step0 raw31546; decide +kernel
      have hl : raw31546step0Labels = raw31546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31546 raw31546Labels permutation434 hz
    mixedMoment B raw31546step0 raw31546step0Labels = mixedMoment B raw31546step1 raw31546step1Labels := by
      have ha : raw31546step1 = (fun i j => raw31546step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31546step1 raw31546step0; decide +kernel
      have hl : raw31546step1Labels = raw31546step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31546step0 raw31546step0Labels permutation32 permutation7
    mixedMoment B raw31546step1 raw31546step1Labels = mixedMoment B raw31546step2 raw31546step2Labels := by
      have ha : raw31546step2 = -raw31546step1 := by apply Matrix.ext; change ∀ i j, raw31546step2 i j = -(raw31546step1 i j); unfold raw31546step2 raw31546step1; decide +kernel
      have hl : raw31546step2Labels = raw31546step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31546step2 raw31546step2Labels = mixedMoment B raw31546step3 raw31546step3Labels := by
      have ha : raw31546step3 = raw31546step2 := by apply Matrix.ext; unfold raw31546step3 raw31546step2; decide +kernel
      have hl : raw31546step2Labels = labelEmbedding1 ∘ raw31546step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31546step2 raw31546step2Labels raw31546step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical31547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31547 raw31547Labels = mixedMoment B node3380 node3380Labels := by
  calc
    mixedMoment B raw31547 raw31547Labels = mixedMoment B raw31547step0 raw31547step0Labels := by
      have hz : ∀ j, raw31547 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31547step0 = (fun i j => raw31547 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31547step0 raw31547; decide +kernel
      have hl : raw31547step0Labels = raw31547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31547 raw31547Labels permutation434 hz
    _ = mixedMoment B node3380 node3380Labels := by rfl

theorem canonical31548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31548 raw31548Labels = mixedMoment B node2029 node2029Labels := by
  calc
    mixedMoment B raw31548 raw31548Labels = mixedMoment B raw31548step0 raw31548step0Labels := by
      have hz : ∀ j, raw31548 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31548step0 = (fun i j => raw31548 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31548step0 raw31548; decide +kernel
      have hl : raw31548step0Labels = raw31548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31548 raw31548Labels permutation434 hz
    _ = mixedMoment B node2029 node2029Labels := by rfl

theorem canonical31549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31549 raw31549Labels = mixedMoment B node1815 node1815Labels := by
  calc
    mixedMoment B raw31549 raw31549Labels = mixedMoment B raw31549step0 raw31549step0Labels := by
      have hz : ∀ j, raw31549 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31549step0 = (fun i j => raw31549 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31549step0 raw31549; decide +kernel
      have hl : raw31549step0Labels = raw31549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31549 raw31549Labels permutation434 hz
    _ = mixedMoment B node1815 node1815Labels := by rfl

theorem canonical31550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31550 raw31550Labels = mixedMoment B node1792 node1792Labels := by
  calc
    _ = mixedMoment B node1792 node1792Labels := by rfl

theorem canonical31551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31551 raw31551Labels = mixedMoment B node1796 node1796Labels := by
  calc
    mixedMoment B raw31551 raw31551Labels = mixedMoment B raw31551step0 raw31551step0Labels := by
      have hz : ∀ j, raw31551 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31551step0 = (fun i j => raw31551 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31551step0 raw31551; decide +kernel
      have hl : raw31551step0Labels = raw31551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31551 raw31551Labels permutation434 hz
    mixedMoment B raw31551step0 raw31551step0Labels = mixedMoment B raw31551step1 raw31551step1Labels := by
      have ha : raw31551step1 = (fun i j => raw31551step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31551step1 raw31551step0; decide +kernel
      have hl : raw31551step1Labels = raw31551step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31551step0 raw31551step0Labels permutation33 permutation2
    _ = mixedMoment B node1796 node1796Labels := by rfl

theorem canonical31552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31552 raw31552Labels = mixedMoment B node1796 node1796Labels := by
  calc
    mixedMoment B raw31552 raw31552Labels = mixedMoment B raw31552step0 raw31552step0Labels := by
      have hz : ∀ j, raw31552 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31552step0 = (fun i j => raw31552 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31552step0 raw31552; decide +kernel
      have hl : raw31552step0Labels = raw31552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31552 raw31552Labels permutation434 hz
    _ = mixedMoment B node1796 node1796Labels := by rfl

theorem canonical31553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31553 raw31553Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw31553 raw31553Labels = mixedMoment B raw31553step0 raw31553step0Labels := by
      have hz : ∀ j, raw31553 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31553step0 = (fun i j => raw31553 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31553step0 raw31553; decide +kernel
      have hl : raw31553step0Labels = raw31553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31553 raw31553Labels permutation434 hz
    mixedMoment B raw31553step0 raw31553step0Labels = mixedMoment B raw31553step1 raw31553step1Labels := by
      have hz : ∀ j, raw31553step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31553step1 = (fun i j => raw31553step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31553step1 raw31553step0; decide +kernel
      have hl : raw31553step1Labels = raw31553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31553step0 raw31553step0Labels permutation56 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical31554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31554 raw31554Labels = mixedMoment B node933 node933Labels := by
  calc
    mixedMoment B raw31554 raw31554Labels = mixedMoment B raw31554step0 raw31554step0Labels := by
      have hz : ∀ j, raw31554 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31554step0 = (fun i j => raw31554 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31554step0 raw31554; decide +kernel
      have hl : raw31554step0Labels = raw31554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31554 raw31554Labels permutation434 hz
    _ = mixedMoment B node933 node933Labels := by rfl

theorem canonical31555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31555 raw31555Labels = mixedMoment B node1967 node1967Labels := by
  calc
    mixedMoment B raw31555 raw31555Labels = mixedMoment B raw31555step0 raw31555step0Labels := by
      have ha : raw31555step0 = (fun i j => raw31555 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31555step0 raw31555; decide +kernel
      have hl : raw31555step0Labels = raw31555Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31555 raw31555Labels permutation158 permutation2
    _ = mixedMoment B node1967 node1967Labels := by rfl

theorem canonical31556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31556 raw31556Labels = mixedMoment B node2057 node2057Labels := by
  calc
    mixedMoment B raw31556 raw31556Labels = mixedMoment B raw31556step0 raw31556step0Labels := by
      have hz : ∀ j, raw31556 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31556step0 = (fun i j => raw31556 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31556step0 raw31556; decide +kernel
      have hl : raw31556step0Labels = raw31556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31556 raw31556Labels permutation434 hz
    _ = mixedMoment B node2057 node2057Labels := by rfl

theorem canonical31557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31557 raw31557Labels = mixedMoment B node2057 node2057Labels := by
  calc
    mixedMoment B raw31557 raw31557Labels = mixedMoment B raw31557step0 raw31557step0Labels := by
      have hz : ∀ j, raw31557 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31557step0 = (fun i j => raw31557 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31557step0 raw31557; decide +kernel
      have hl : raw31557step0Labels = raw31557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31557 raw31557Labels permutation434 hz
    mixedMoment B raw31557step0 raw31557step0Labels = mixedMoment B raw31557step1 raw31557step1Labels := by
      have ha : raw31557step1 = (fun i j => raw31557step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31557step1 raw31557step0; decide +kernel
      have hl : raw31557step1Labels = raw31557step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31557step0 raw31557step0Labels permutation33 permutation2
    _ = mixedMoment B node2057 node2057Labels := by rfl

theorem canonical31558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31558 raw31558Labels = mixedMoment B node907 node907Labels := by
  calc
    _ = mixedMoment B node907 node907Labels := by rfl

theorem canonical31559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31559 raw31559Labels = mixedMoment B node1975 node1975Labels := by
  calc
    _ = mixedMoment B node1975 node1975Labels := by rfl

theorem canonical31560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31560 raw31560Labels = mixedMoment B node2020 node2020Labels := by
  calc
    _ = mixedMoment B node2020 node2020Labels := by rfl

theorem canonical31561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31561 raw31561Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw31561 raw31561Labels = mixedMoment B raw31561step0 raw31561step0Labels := by
      have ha : raw31561step0 = (fun i j => raw31561 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31561step0 raw31561; decide +kernel
      have hl : raw31561step0Labels = raw31561Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31561 raw31561Labels permutation153 permutation2
    _ = mixedMoment B node2020 node2020Labels := by rfl

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

theorem canonical1149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1149 raw1149Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw1149 raw1149Labels = mixedMoment B raw1149step0 raw1149step0Labels := by
      have ha : raw1149step0 = (fun i j => raw1149 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1149step0 raw1149; decide +kernel
      have hl : raw1149step0Labels = raw1149Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1149 raw1149Labels permutation32 permutation4
    mixedMoment B raw1149step0 raw1149step0Labels = mixedMoment B raw1149step1 raw1149step1Labels := by
      have ha : raw1149step1 = raw1149step0 := by apply Matrix.ext; unfold raw1149step1 raw1149step0; decide +kernel
      have hl : raw1149step0Labels = labelEmbedding7 ∘ raw1149step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1149step0 raw1149step0Labels raw1149step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4355 node4355Labels := by rfl

theorem canonical1150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1150 raw1150Labels = mixedMoment B node933 node933Labels := by
  calc
    mixedMoment B raw1150 raw1150Labels = mixedMoment B raw1150step0 raw1150step0Labels := by
      have ha : raw1150step0 = (fun i j => raw1150 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1150step0 raw1150; decide +kernel
      have hl : raw1150step0Labels = raw1150Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1150 raw1150Labels permutation32 permutation4
    _ = mixedMoment B node933 node933Labels := by rfl

theorem canonical1151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1151 raw1151Labels = mixedMoment B node1691 node1691Labels := by
  calc
    mixedMoment B raw1151 raw1151Labels = mixedMoment B raw1151step0 raw1151step0Labels := by
      have ha : raw1151step0 = (fun i j => raw1151 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1151step0 raw1151; decide +kernel
      have hl : raw1151step0Labels = raw1151Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1151 raw1151Labels permutation32 permutation6
    mixedMoment B raw1151step0 raw1151step0Labels = mixedMoment B raw1151step1 raw1151step1Labels := by
      have ha : raw1151step1 = -raw1151step0 := by apply Matrix.ext; change ∀ i j, raw1151step1 i j = -(raw1151step0 i j); unfold raw1151step1 raw1151step0; decide +kernel
      have hl : raw1151step1Labels = raw1151step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1151step1 raw1151step1Labels = mixedMoment B raw1151step2 raw1151step2Labels := by
      have ha : raw1151step2 = raw1151step1 := by apply Matrix.ext; unfold raw1151step2 raw1151step1; decide +kernel
      have hl : raw1151step1Labels = labelEmbedding1 ∘ raw1151step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1151step1 raw1151step1Labels raw1151step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1691 node1691Labels := by rfl

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

theorem canonical1275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1275 raw1275Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw1275 raw1275Labels = mixedMoment B raw1275step0 raw1275step0Labels := by
      have ha : raw1275step0 = (fun i j => raw1275 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1275step0 raw1275; decide +kernel
      have hl : raw1275step0Labels = raw1275Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1275 raw1275Labels permutation8 permutation4
    mixedMoment B raw1275step0 raw1275step0Labels = mixedMoment B raw1275step1 raw1275step1Labels := by
      have ha : raw1275step1 = raw1275step0 := by apply Matrix.ext; unfold raw1275step1 raw1275step0; decide +kernel
      have hl : raw1275step0Labels = labelEmbedding7 ∘ raw1275step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1275step0 raw1275step0Labels raw1275step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

theorem canonical1276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1276 raw1276Labels = mixedMoment B node1050 node1050Labels := by
  calc
    mixedMoment B raw1276 raw1276Labels = mixedMoment B raw1276step0 raw1276step0Labels := by
      have ha : raw1276step0 = (fun i j => raw1276 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1276step0 raw1276; decide +kernel
      have hl : raw1276step0Labels = raw1276Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1276 raw1276Labels permutation8 permutation4
    _ = mixedMoment B node1050 node1050Labels := by rfl

theorem canonical1277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1277 raw1277Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw1277 raw1277Labels = mixedMoment B raw1277step0 raw1277step0Labels := by
      have ha : raw1277step0 = (fun i j => raw1277 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1277step0 raw1277; decide +kernel
      have hl : raw1277step0Labels = raw1277Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1277 raw1277Labels permutation8 permutation6
    mixedMoment B raw1277step0 raw1277step0Labels = mixedMoment B raw1277step1 raw1277step1Labels := by
      have ha : raw1277step1 = -raw1277step0 := by apply Matrix.ext; change ∀ i j, raw1277step1 i j = -(raw1277step0 i j); unfold raw1277step1 raw1277step0; decide +kernel
      have hl : raw1277step1Labels = raw1277step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1277step1 raw1277step1Labels = mixedMoment B raw1277step2 raw1277step2Labels := by
      have ha : raw1277step2 = raw1277step1 := by apply Matrix.ext; unfold raw1277step2 raw1277step1; decide +kernel
      have hl : raw1277step1Labels = labelEmbedding1 ∘ raw1277step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1277step1 raw1277step1Labels raw1277step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1751 node1751Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4355 node4355Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node933 node933Labels + mixedMoment B node1691 node1691Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1149 singletonSmall4355
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4355) = raw1149Labels := by decide +kernel
  rw [hl, canonical1149 B hB] at h
  have hc0 : mixedMoment B raw1149 (Fin.cases (0 : Fin 2) singletonSmall4355) =
      mixedMoment B node933 node933Labels := by
    have ha : raw1149 = raw1150 := by apply Matrix.ext; unfold raw1149 raw1150; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4355 = raw1150Labels := by decide +kernel
    rw [ha, hj, canonical1150 B hB]
  have hc1 : mixedMoment B raw1149 (Fin.cases (1 : Fin 2) singletonSmall4355) =
      mixedMoment B node1691 node1691Labels := by
    have ha : raw1149 = raw1151 := by apply Matrix.ext; unfold raw1149 raw1151; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4355 = raw1151Labels := by decide +kernel
    rw [ha, hj, canonical1151 B hB]
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

theorem singleton4467 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4467 node4467Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1050 node1050Labels + mixedMoment B node1751 node1751Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1275 singletonSmall4467
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4467) = raw1275Labels := by decide +kernel
  rw [hl, canonical1275 B hB] at h
  have hc0 : mixedMoment B raw1275 (Fin.cases (0 : Fin 2) singletonSmall4467) =
      mixedMoment B node1050 node1050Labels := by
    have ha : raw1275 = raw1276 := by apply Matrix.ext; unfold raw1275 raw1276; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4467 = raw1276Labels := by decide +kernel
    rw [ha, hj, canonical1276 B hB]
  have hc1 : mixedMoment B raw1275 (Fin.cases (1 : Fin 2) singletonSmall4467) =
      mixedMoment B node1751 node1751Labels := by
    have ha : raw1275 = raw1277 := by apply Matrix.ext; unfold raw1275 raw1277; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4467 = raw1277Labels := by decide +kernel
    rw [ha, hj, canonical1277 B hB]
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

theorem singleton4767 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4767 node4767Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1967 node1967Labels + mixedMoment B node2183 node2183Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1701 singletonSmall4767
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4767) = raw1701Labels := by decide +kernel
  rw [hl, canonical1701 B hB] at h
  have hc0 : mixedMoment B raw1701 (Fin.cases (0 : Fin 2) singletonSmall4767) =
      mixedMoment B node1967 node1967Labels := by
    have ha : raw1701 = raw1702 := by apply Matrix.ext; unfold raw1701 raw1702; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4767 = raw1702Labels := by decide +kernel
    rw [ha, hj, canonical1702 B hB]
  have hc1 : mixedMoment B raw1701 (Fin.cases (1 : Fin 2) singletonSmall4767) =
      mixedMoment B node2183 node2183Labels := by
    have ha : raw1701 = raw1703 := by apply Matrix.ext; unfold raw1701 raw1703; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4767 = raw1703Labels := by decide +kernel
    rw [ha, hj, canonical1703 B hB]
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

theorem singleton4807 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4807 node4807Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2025 node2025Labels + mixedMoment B node2224 node2224Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1743 singletonSmall4807
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4807) = raw1743Labels := by decide +kernel
  rw [hl, canonical1743 B hB] at h
  have hc0 : mixedMoment B raw1743 (Fin.cases (0 : Fin 2) singletonSmall4807) =
      mixedMoment B node2025 node2025Labels := by
    have ha : raw1743 = raw1744 := by apply Matrix.ext; unfold raw1743 raw1744; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4807 = raw1744Labels := by decide +kernel
    rw [ha, hj, canonical1744 B hB]
  have hc1 : mixedMoment B raw1743 (Fin.cases (1 : Fin 2) singletonSmall4807) =
      mixedMoment B node2224 node2224Labels := by
    have ha : raw1743 = raw1745 := by apply Matrix.ext; unfold raw1743 raw1745; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4807 = raw1745Labels := by decide +kernel
    rw [ha, hj, canonical1745 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5271 node5271Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2739 node2739Labels + mixedMoment B node3534 node3534Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2280 singletonSmall5271
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5271) = raw2280Labels := by decide +kernel
  rw [hl, canonical2280 B hB] at h
  have hc0 : mixedMoment B raw2280 (Fin.cases (0 : Fin 2) singletonSmall5271) =
      mixedMoment B node2739 node2739Labels := by
    have ha : raw2280 = raw2281 := by apply Matrix.ext; unfold raw2280 raw2281; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5271 = raw2281Labels := by decide +kernel
    rw [ha, hj, canonical2281 B hB]
  have hc1 : mixedMoment B raw2280 (Fin.cases (1 : Fin 2) singletonSmall5271) =
      mixedMoment B node3534 node3534Labels := by
    have ha : raw2280 = raw2282 := by apply Matrix.ext; unfold raw2280 raw2282; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5271 = raw2282Labels := by decide +kernel
    rw [ha, hj, canonical2282 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node907 node907Labels = 0 := by
  exact mixedMoment_alpha B hF node907 node907Labels 1 permutation152
    (by decide +kernel)

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

theorem sound906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node906 node906Labels = Sparse.eval nodeValue906 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 906) = mixedMoment B node906 node906Labels := rfl
  simpa [nodeValue906, Sparse.eval] using hc.symm

theorem sound907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node907 node907Labels = Sparse.eval nodeValue907 (mixedVector B) := by
  simpa only [nodeValue907, Sparse.eval_nil] using zero907 B _hB _hF

theorem sound932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node932 node932Labels = Sparse.eval nodeValue932 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 932) = mixedMoment B node932 node932Labels := rfl
  simpa [nodeValue932, Sparse.eval] using hc.symm

theorem sound933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node933 node933Labels = Sparse.eval nodeValue933 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 933) = mixedMoment B node933 node933Labels := rfl
  simpa [nodeValue933, Sparse.eval] using hc.symm

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

theorem sound1050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1050 node1050Labels = Sparse.eval nodeValue1050 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1050) = mixedMoment B node1050 node1050Labels := rfl
  simpa [nodeValue1050, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1671 node1671Labels = 0 := by
  exact mixedMoment_alpha B hF node1671 node1671Labels 1 permutation487
    (by decide +kernel)

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

theorem sound1667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1667 node1667Labels = Sparse.eval nodeValue1667 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1667) = mixedMoment B node1667 node1667Labels := rfl
  simpa [nodeValue1667, Sparse.eval] using hc.symm

theorem sound1671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1671 node1671Labels = Sparse.eval nodeValue1671 (mixedVector B) := by
  simpa only [nodeValue1671, Sparse.eval_nil] using zero1671 B _hB _hF

theorem sound1679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1679 node1679Labels = Sparse.eval nodeValue1679 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1679) = mixedMoment B node1679 node1679Labels := rfl
  simpa [nodeValue1679, Sparse.eval] using hc.symm

theorem sound1681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1681 node1681Labels = Sparse.eval nodeValue1681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1681) = mixedMoment B node1681 node1681Labels := rfl
  simpa [nodeValue1681, Sparse.eval] using hc.symm

theorem sound1685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1685 node1685Labels = Sparse.eval nodeValue1685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1685) = mixedMoment B node1685 node1685Labels := rfl
  simpa [nodeValue1685, Sparse.eval] using hc.symm

theorem sound1689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1689 node1689Labels = Sparse.eval nodeValue1689 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1689) = mixedMoment B node1689 node1689Labels := rfl
  simpa [nodeValue1689, Sparse.eval] using hc.symm

theorem sound1691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1691 node1691Labels = Sparse.eval nodeValue1691 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1691) = mixedMoment B node1691 node1691Labels := rfl
  simpa [nodeValue1691, Sparse.eval] using hc.symm

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

theorem sound1738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1738 node1738Labels = Sparse.eval nodeValue1738 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1738) = mixedMoment B node1738 node1738Labels := rfl
  simpa [nodeValue1738, Sparse.eval] using hc.symm

theorem sound1751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1751 node1751Labels = Sparse.eval nodeValue1751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1751) = mixedMoment B node1751 node1751Labels := rfl
  simpa [nodeValue1751, Sparse.eval] using hc.symm

theorem sound1791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1791 node1791Labels = Sparse.eval nodeValue1791 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1791) = mixedMoment B node1791 node1791Labels := rfl
  simpa [nodeValue1791, Sparse.eval] using hc.symm

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

theorem sound1792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1792 node1792Labels = Sparse.eval nodeValue1792 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1792) = mixedMoment B node1792 node1792Labels := rfl
  simpa [nodeValue1792, Sparse.eval] using hc.symm

theorem sound1795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1795 node1795Labels = Sparse.eval nodeValue1795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1795) = mixedMoment B node1795 node1795Labels := rfl
  simpa [nodeValue1795, Sparse.eval] using hc.symm

theorem sound1796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1796 node1796Labels = Sparse.eval nodeValue1796 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1796) = mixedMoment B node1796 node1796Labels := rfl
  simpa [nodeValue1796, Sparse.eval] using hc.symm

theorem sound1797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1797 node1797Labels = Sparse.eval nodeValue1797 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1797) = mixedMoment B node1797 node1797Labels := rfl
  simpa [nodeValue1797, Sparse.eval] using hc.symm

theorem sound1814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1814 node1814Labels = Sparse.eval nodeValue1814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1814) = mixedMoment B node1814 node1814Labels := rfl
  simpa [nodeValue1814, Sparse.eval] using hc.symm

theorem sound1815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1815 node1815Labels = Sparse.eval nodeValue1815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1815) = mixedMoment B node1815 node1815Labels := rfl
  simpa [nodeValue1815, Sparse.eval] using hc.symm

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

theorem zero1918 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1918 node1918Labels = 0 := by
  exact mixedMoment_order_one B hB node1918 node1918Labels 1
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

theorem sound1876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1876 node1876Labels = Sparse.eval nodeValue1876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1876) = mixedMoment B node1876 node1876Labels := rfl
  simpa [nodeValue1876, Sparse.eval] using hc.symm

theorem sound1880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1880 node1880Labels = Sparse.eval nodeValue1880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1880) = mixedMoment B node1880 node1880Labels := rfl
  simpa [nodeValue1880, Sparse.eval] using hc.symm

theorem sound1881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1881 node1881Labels = Sparse.eval nodeValue1881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1881) = mixedMoment B node1881 node1881Labels := rfl
  simpa [nodeValue1881, Sparse.eval] using hc.symm

theorem sound1918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1918 node1918Labels = Sparse.eval nodeValue1918 (mixedVector B) := by
  simpa only [nodeValue1918, Sparse.eval_nil] using zero1918 B _hB _hF

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

theorem sound1966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1966 node1966Labels = Sparse.eval nodeValue1966 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1966) = mixedMoment B node1966 node1966Labels := rfl
  simpa [nodeValue1966, Sparse.eval] using hc.symm

theorem sound1967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1967 node1967Labels = Sparse.eval nodeValue1967 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1967) = mixedMoment B node1967 node1967Labels := rfl
  simpa [nodeValue1967, Sparse.eval] using hc.symm

theorem sound1974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1974 node1974Labels = Sparse.eval nodeValue1974 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1974) = mixedMoment B node1974 node1974Labels := rfl
  simpa [nodeValue1974, Sparse.eval] using hc.symm

theorem sound1975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1975 node1975Labels = Sparse.eval nodeValue1975 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1975) = mixedMoment B node1975 node1975Labels := rfl
  simpa [nodeValue1975, Sparse.eval] using hc.symm

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

theorem sound2019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2019 node2019Labels = Sparse.eval nodeValue2019 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2019) = mixedMoment B node2019 node2019Labels := rfl
  simpa [nodeValue2019, Sparse.eval] using hc.symm

theorem sound2020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2020 node2020Labels = Sparse.eval nodeValue2020 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2020) = mixedMoment B node2020 node2020Labels := rfl
  simpa [nodeValue2020, Sparse.eval] using hc.symm

theorem sound2021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2021 node2021Labels = Sparse.eval nodeValue2021 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2021) = mixedMoment B node2021 node2021Labels := rfl
  simpa [nodeValue2021, Sparse.eval] using hc.symm

theorem sound2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2025 node2025Labels = Sparse.eval nodeValue2025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2025) = mixedMoment B node2025 node2025Labels := rfl
  simpa [nodeValue2025, Sparse.eval] using hc.symm

theorem sound2028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2028 node2028Labels = Sparse.eval nodeValue2028 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2028) = mixedMoment B node2028 node2028Labels := rfl
  simpa [nodeValue2028, Sparse.eval] using hc.symm

theorem sound2029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2029 node2029Labels = Sparse.eval nodeValue2029 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2029) = mixedMoment B node2029 node2029Labels := rfl
  simpa [nodeValue2029, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2053 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2053 node2053Labels = 0 := by
  exact mixedMoment_order_one B hB node2053 node2053Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2057 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2057 node2057Labels = 0 := by
  exact mixedMoment_order_one B hB node2057 node2057Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2053 node2053Labels = Sparse.eval nodeValue2053 (mixedVector B) := by
  simpa only [nodeValue2053, Sparse.eval_nil] using zero2053 B _hB _hF

theorem sound2057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2057 node2057Labels = Sparse.eval nodeValue2057 (mixedVector B) := by
  simpa only [nodeValue2057, Sparse.eval_nil] using zero2057 B _hB _hF

theorem sound2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2058 node2058Labels = Sparse.eval nodeValue2058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2058) = mixedMoment B node2058 node2058Labels := rfl
  simpa [nodeValue2058, Sparse.eval] using hc.symm

theorem sound2082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2082 node2082Labels = Sparse.eval nodeValue2082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2082) = mixedMoment B node2082 node2082Labels := rfl
  simpa [nodeValue2082, Sparse.eval] using hc.symm

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

theorem sound2144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2144 node2144Labels = Sparse.eval nodeValue2144 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2144) = mixedMoment B node2144 node2144Labels := rfl
  simpa [nodeValue2144, Sparse.eval] using hc.symm

theorem sound2148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2148 node2148Labels = Sparse.eval nodeValue2148 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2148) = mixedMoment B node2148 node2148Labels := rfl
  simpa [nodeValue2148, Sparse.eval] using hc.symm

theorem sound2155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2155 node2155Labels = Sparse.eval nodeValue2155 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2155) = mixedMoment B node2155 node2155Labels := rfl
  simpa [nodeValue2155, Sparse.eval] using hc.symm

theorem sound2157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2157 node2157Labels = Sparse.eval nodeValue2157 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2157) = mixedMoment B node2157 node2157Labels := rfl
  simpa [nodeValue2157, Sparse.eval] using hc.symm

theorem sound2160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2160 node2160Labels = Sparse.eval nodeValue2160 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2160) = mixedMoment B node2160 node2160Labels := rfl
  simpa [nodeValue2160, Sparse.eval] using hc.symm

theorem sound2161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2161 node2161Labels = Sparse.eval nodeValue2161 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2161) = mixedMoment B node2161 node2161Labels := rfl
  simpa [nodeValue2161, Sparse.eval] using hc.symm

theorem sound2162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2162 node2162Labels = Sparse.eval nodeValue2162 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2162) = mixedMoment B node2162 node2162Labels := rfl
  simpa [nodeValue2162, Sparse.eval] using hc.symm

theorem sound2164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2164 node2164Labels = Sparse.eval nodeValue2164 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2164) = mixedMoment B node2164 node2164Labels := rfl
  simpa [nodeValue2164, Sparse.eval] using hc.symm

theorem sound2166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2166 node2166Labels = Sparse.eval nodeValue2166 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2166) = mixedMoment B node2166 node2166Labels := rfl
  simpa [nodeValue2166, Sparse.eval] using hc.symm

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

theorem zero2205 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2205 node2205Labels = 0 := by
  exact mixedMoment_order_one B hB node2205 node2205Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2227 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2227 node2227Labels = 0 := by
  exact mixedMoment_order_one B hB node2227 node2227Labels 1
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

theorem sound2176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2176 node2176Labels = Sparse.eval nodeValue2176 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2176) = mixedMoment B node2176 node2176Labels := rfl
  simpa [nodeValue2176, Sparse.eval] using hc.symm

theorem sound2177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2177 node2177Labels = Sparse.eval nodeValue2177 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2177) = mixedMoment B node2177 node2177Labels := rfl
  simpa [nodeValue2177, Sparse.eval] using hc.symm

theorem sound2181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2181 node2181Labels = Sparse.eval nodeValue2181 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2181) = mixedMoment B node2181 node2181Labels := rfl
  simpa [nodeValue2181, Sparse.eval] using hc.symm

theorem sound2183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2183 node2183Labels = Sparse.eval nodeValue2183 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2183) = mixedMoment B node2183 node2183Labels := rfl
  simpa [nodeValue2183, Sparse.eval] using hc.symm

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

theorem sound2195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2195 node2195Labels = Sparse.eval nodeValue2195 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2195) = mixedMoment B node2195 node2195Labels := rfl
  simpa [nodeValue2195, Sparse.eval] using hc.symm

theorem sound2199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2199 node2199Labels = Sparse.eval nodeValue2199 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2199) = mixedMoment B node2199 node2199Labels := rfl
  simpa [nodeValue2199, Sparse.eval] using hc.symm

theorem sound2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2202 node2202Labels = Sparse.eval nodeValue2202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2202) = mixedMoment B node2202 node2202Labels := rfl
  simpa [nodeValue2202, Sparse.eval] using hc.symm

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

theorem sound2205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2205 node2205Labels = Sparse.eval nodeValue2205 (mixedVector B) := by
  simpa only [nodeValue2205, Sparse.eval_nil] using zero2205 B _hB _hF

theorem sound2212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2212 node2212Labels = Sparse.eval nodeValue2212 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2212) = mixedMoment B node2212 node2212Labels := rfl
  simpa [nodeValue2212, Sparse.eval] using hc.symm

theorem sound2215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2215 node2215Labels = Sparse.eval nodeValue2215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2215) = mixedMoment B node2215 node2215Labels := rfl
  simpa [nodeValue2215, Sparse.eval] using hc.symm

theorem sound2216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2216 node2216Labels = Sparse.eval nodeValue2216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2216) = mixedMoment B node2216 node2216Labels := rfl
  simpa [nodeValue2216, Sparse.eval] using hc.symm

theorem sound2220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2220 node2220Labels = Sparse.eval nodeValue2220 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2220) = mixedMoment B node2220 node2220Labels := rfl
  simpa [nodeValue2220, Sparse.eval] using hc.symm

theorem sound2223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2223 node2223Labels = Sparse.eval nodeValue2223 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2223) = mixedMoment B node2223 node2223Labels := rfl
  simpa [nodeValue2223, Sparse.eval] using hc.symm

theorem sound2224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2224 node2224Labels = Sparse.eval nodeValue2224 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2224) = mixedMoment B node2224 node2224Labels := rfl
  simpa [nodeValue2224, Sparse.eval] using hc.symm

theorem sound2225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2225 node2225Labels = Sparse.eval nodeValue2225 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2225) = mixedMoment B node2225 node2225Labels := rfl
  simpa [nodeValue2225, Sparse.eval] using hc.symm

theorem sound2227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2227 node2227Labels = Sparse.eval nodeValue2227 (mixedVector B) := by
  simpa only [nodeValue2227, Sparse.eval_nil] using zero2227 B _hB _hF

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

theorem zero2264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = 0 := by
  exact mixedMoment_order_one B hB node2264 node2264Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = 0 := by
  exact mixedMoment_order_one B hB node2291 node2291Labels 1
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

theorem sound2264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = Sparse.eval nodeValue2264 (mixedVector B) := by
  simpa only [nodeValue2264, Sparse.eval_nil] using zero2264 B _hB _hF

theorem sound2276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2276 node2276Labels = Sparse.eval nodeValue2276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2276) = mixedMoment B node2276 node2276Labels := rfl
  simpa [nodeValue2276, Sparse.eval] using hc.symm

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

theorem sound2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = Sparse.eval nodeValue2291 (mixedVector B) := by
  simpa only [nodeValue2291, Sparse.eval_nil] using zero2291 B _hB _hF

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

theorem sound2677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2677 node2677Labels = Sparse.eval nodeValue2677 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2677) = mixedMoment B node2677 node2677Labels := rfl
  simpa [nodeValue2677, Sparse.eval] using hc.symm

theorem sound2682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2682 node2682Labels = Sparse.eval nodeValue2682 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2682) = mixedMoment B node2682 node2682Labels := rfl
  simpa [nodeValue2682, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2701 node2701Labels = 0 := by
  exact mixedMoment_alpha B hF node2701 node2701Labels 1 permutation216
    (by decide +kernel)

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

theorem sound2697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2697 node2697Labels = Sparse.eval nodeValue2697 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2697) = mixedMoment B node2697 node2697Labels := rfl
  simpa [nodeValue2697, Sparse.eval] using hc.symm

theorem sound2701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2701 node2701Labels = Sparse.eval nodeValue2701 (mixedVector B) := by
  simpa only [nodeValue2701, Sparse.eval_nil] using zero2701 B _hB _hF

theorem sound2722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2722 node2722Labels = Sparse.eval nodeValue2722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2722) = mixedMoment B node2722 node2722Labels := rfl
  simpa [nodeValue2722, Sparse.eval] using hc.symm

theorem sound2729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2729 node2729Labels = Sparse.eval nodeValue2729 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2729) = mixedMoment B node2729 node2729Labels := rfl
  simpa [nodeValue2729, Sparse.eval] using hc.symm

theorem sound2731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2731 node2731Labels = Sparse.eval nodeValue2731 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2731) = mixedMoment B node2731 node2731Labels := rfl
  simpa [nodeValue2731, Sparse.eval] using hc.symm

theorem sound2736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2736 node2736Labels = Sparse.eval nodeValue2736 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2736) = mixedMoment B node2736 node2736Labels := rfl
  simpa [nodeValue2736, Sparse.eval] using hc.symm

theorem sound2739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2739 node2739Labels = Sparse.eval nodeValue2739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2739) = mixedMoment B node2739 node2739Labels := rfl
  simpa [nodeValue2739, Sparse.eval] using hc.symm

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

theorem sound3379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3379 node3379Labels = Sparse.eval nodeValue3379 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3379) = mixedMoment B node3379 node3379Labels := rfl
  simpa [nodeValue3379, Sparse.eval] using hc.symm

theorem sound3380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3380 node3380Labels = Sparse.eval nodeValue3380 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3380) = mixedMoment B node3380 node3380Labels := rfl
  simpa [nodeValue3380, Sparse.eval] using hc.symm

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

theorem sound3448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3448 node3448Labels = Sparse.eval nodeValue3448 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3448) = mixedMoment B node3448 node3448Labels := rfl
  simpa [nodeValue3448, Sparse.eval] using hc.symm

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

theorem sound3534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3534 node3534Labels = Sparse.eval nodeValue3534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3534) = mixedMoment B node3534 node3534Labels := rfl
  simpa [nodeValue3534, Sparse.eval] using hc.symm

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

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4329 node4329Labels = 0 := by
  exact mixedMoment_alpha B hF node4329 node4329Labels 1 permutation152
    (by decide +kernel)

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

theorem sound4329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4329 node4329Labels = Sparse.eval nodeValue4329 (mixedVector B) := by
  simpa only [nodeValue4329, Sparse.eval_nil] using zero4329 B _hB _hF

theorem sound4335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4335 node4335Labels = Sparse.eval nodeValue4335 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4335) = mixedMoment B node4335 node4335Labels := rfl
  simpa [nodeValue4335, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4355 node4355Labels = Sparse.eval nodeValue4355 (mixedVector B) := by
  have h := singleton4355 B _hB
  rw [sound933 B _hB _hF, sound1691 B _hB _hF] at h
  norm_num [nodeValue4355, nodeValue933, nodeValue1691, Sparse.eval] at h ⊢
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

theorem sound4467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4467 node4467Labels = Sparse.eval nodeValue4467 (mixedVector B) := by
  have h := singleton4467 B _hB
  rw [sound1050 B _hB _hF, sound1751 B _hB _hF] at h
  norm_num [nodeValue4467, nodeValue1050, nodeValue1751, Sparse.eval] at h ⊢
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

theorem sound4666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4666 node4666Labels = Sparse.eval nodeValue4666 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4666) = mixedMoment B node4666 node4666Labels := rfl
  simpa [nodeValue4666, Sparse.eval] using hc.symm

theorem sound4670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4670 node4670Labels = Sparse.eval nodeValue4670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4670) = mixedMoment B node4670 node4670Labels := rfl
  simpa [nodeValue4670, Sparse.eval] using hc.symm

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

theorem sound4689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4689 node4689Labels = Sparse.eval nodeValue4689 (mixedVector B) := by
  have h := singleton4689 B _hB
  rw [sound1815 B _hB _hF, sound2166 B _hB _hF] at h
  norm_num [nodeValue4689, nodeValue1815, nodeValue2166, Sparse.eval] at h ⊢
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

theorem sound4757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4757 node4757Labels = Sparse.eval nodeValue4757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4757) = mixedMoment B node4757 node4757Labels := rfl
  simpa [nodeValue4757, Sparse.eval] using hc.symm

theorem sound4767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4767 node4767Labels = Sparse.eval nodeValue4767 (mixedVector B) := by
  have h := singleton4767 B _hB
  rw [sound1967 B _hB _hF, sound2183 B _hB _hF] at h
  norm_num [nodeValue4767, nodeValue1967, nodeValue2183, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4774 node4774Labels = Sparse.eval nodeValue4774 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4774) = mixedMoment B node4774 node4774Labels := rfl
  simpa [nodeValue4774, Sparse.eval] using hc.symm

theorem sound4777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4777 node4777Labels = Sparse.eval nodeValue4777 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4777) = mixedMoment B node4777 node4777Labels := rfl
  simpa [nodeValue4777, Sparse.eval] using hc.symm

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

theorem zero4838 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4838 node4838Labels = 0 := by
  exact mixedMoment_order_one B hB node4838 node4838Labels 1
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

theorem sound4807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4807 node4807Labels = Sparse.eval nodeValue4807 (mixedVector B) := by
  have h := singleton4807 B _hB
  rw [sound2025 B _hB _hF, sound2224 B _hB _hF] at h
  norm_num [nodeValue4807, nodeValue2025, nodeValue2224, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4811 node4811Labels = Sparse.eval nodeValue4811 (mixedVector B) := by
  have h := singleton4811 B _hB
  rw [sound2029 B _hB _hF, sound2225 B _hB _hF] at h
  norm_num [nodeValue4811, nodeValue2029, nodeValue2225, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4838 node4838Labels = Sparse.eval nodeValue4838 (mixedVector B) := by
  simpa only [nodeValue4838, Sparse.eval_nil] using zero4838 B _hB _hF

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

theorem zero4895 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4895 node4895Labels = 0 := by
  exact mixedMoment_order_one B hB node4895 node4895Labels 1
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

theorem sound4875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4875 node4875Labels = Sparse.eval nodeValue4875 (mixedVector B) := by
  have h := singleton4875 B _hB
  rw [sound2116 B _hB _hF, sound2288 B _hB _hF] at h
  norm_num [nodeValue4875, nodeValue2116, nodeValue2288, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4895 node4895Labels = Sparse.eval nodeValue4895 (mixedVector B) := by
  simpa only [nodeValue4895, Sparse.eval_nil] using zero4895 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5246 node5246Labels = 0 := by
  exact mixedMoment_alpha B hF node5246 node5246Labels 1 permutation216
    (by decide +kernel)

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

theorem sound5236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5236 node5236Labels = Sparse.eval nodeValue5236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5236) = mixedMoment B node5236 node5236Labels := rfl
  simpa [nodeValue5236, Sparse.eval] using hc.symm

theorem sound5246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5246 node5246Labels = Sparse.eval nodeValue5246 (mixedVector B) := by
  simpa only [nodeValue5246, Sparse.eval_nil] using zero5246 B _hB _hF

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

theorem sound5269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5269 node5269Labels = Sparse.eval nodeValue5269 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5269) = mixedMoment B node5269 node5269Labels := rfl
  simpa [nodeValue5269, Sparse.eval] using hc.symm

theorem sound5271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5271 node5271Labels = Sparse.eval nodeValue5271 (mixedVector B) := by
  have h := singleton5271 B _hB
  rw [sound2739 B _hB _hF, sound3534 B _hB _hF] at h
  norm_num [nodeValue5271, nodeValue2739, nodeValue3534, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources70
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2271 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2271 + difference 0 3) (sourceB2271 + difference 3 0) sourceC2271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3448) := by
    have ha : (tripleCharges (sourceA2271 + difference 0 3) (sourceB2271 + difference 3 0) sourceC2271) = raw31267 := by
      apply Matrix.ext; unfold tripleCharges sourceA2271 sourceB2271 sourceC2271 difference raw31267; decide +kernel
    rw [ha]
    exact (canonical31267 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2271 + difference 1 3) (sourceB2271 + difference 3 1) sourceC2271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1918) := by
    have ha : (tripleCharges (sourceA2271 + difference 1 3) (sourceB2271 + difference 3 1) sourceC2271) = raw23317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2271 sourceB2271 sourceC2271 difference raw23317; decide +kernel
    rw [ha]
    exact (canonical23317 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2271 + difference 2 3) (sourceB2271 + difference 3 2) sourceC2271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1876) := by
    have ha : (tripleCharges (sourceA2271 + difference 2 3) (sourceB2271 + difference 3 2) sourceC2271) = raw31270 := by
      apply Matrix.ext; unfold tripleCharges sourceA2271 sourceB2271 sourceC2271 difference raw31270; decide +kernel
    rw [ha]
    exact (canonical31270 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2271 + difference 3 3) (sourceB2271 + difference 3 3) sourceC2271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2082) := by
    have ha : (tripleCharges (sourceA2271 + difference 3 3) (sourceB2271 + difference 3 3) sourceC2271) = raw23315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2271 sourceB2271 sourceC2271 difference raw23315; decide +kernel
    rw [ha]
    exact (canonical23315 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2271 + difference 4 3) (sourceB2271 + difference 3 4) sourceC2271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1880) := by
    have ha : (tripleCharges (sourceA2271 + difference 4 3) (sourceB2271 + difference 3 4) sourceC2271) = raw31271 := by
      apply Matrix.ext; unfold tripleCharges sourceA2271 sourceB2271 sourceC2271 difference raw31271; decide +kernel
    rw [ha]
    exact (canonical31271 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2271 + difference 5 3) (sourceB2271 + difference 3 5) sourceC2271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1881) := by
    have ha : (tripleCharges (sourceA2271 + difference 5 3) (sourceB2271 + difference 3 5) sourceC2271) = raw31272 := by
      apply Matrix.ext; unfold tripleCharges sourceA2271 sourceB2271 sourceC2271 difference raw31272; decide +kernel
    rw [ha]
    exact (canonical31272 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2271 + sourceB2271) sourceC2271) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2271 + sourceB2271) sourceC2271) = raw21586 := by
      apply Matrix.ext; unfold doubleCharges sourceA2271 sourceB2271 sourceC2271 raw21586; decide +kernel
    rw [ha]
    exact (canonical21586 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2271 sourceB2271 sourceC2271
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2271, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources71
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2275 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2275 + difference 0 1) (sourceB2275 + difference 1 0) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2677) := by
    have ha : (tripleCharges (sourceA2275 + difference 0 1) (sourceB2275 + difference 1 0) sourceC2275) = raw31336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31336; decide +kernel
    rw [ha]
    exact (canonical31336 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2275 + difference 0 2) (sourceB2275 + difference 2 0) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA2275 + difference 0 2) (sourceB2275 + difference 2 0) sourceC2275) = raw31337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31337; decide +kernel
    rw [ha]
    exact (canonical31337 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2275 + difference 0 3) (sourceB2275 + difference 3 0) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2697) := by
    have ha : (tripleCharges (sourceA2275 + difference 0 3) (sourceB2275 + difference 3 0) sourceC2275) = raw31338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31338; decide +kernel
    rw [ha]
    exact (canonical31338 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2275 + difference 0 4) (sourceB2275 + difference 4 0) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA2275 + difference 0 4) (sourceB2275 + difference 4 0) sourceC2275) = raw31339 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31339; decide +kernel
    rw [ha]
    exact (canonical31339 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2275 + difference 0 5) (sourceB2275 + difference 5 0) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA2275 + difference 0 5) (sourceB2275 + difference 5 0) sourceC2275) = raw31340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31340; decide +kernel
    rw [ha]
    exact (canonical31340 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2275 + difference 1 0) (sourceB2275 + difference 0 1) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA2275 + difference 1 0) (sourceB2275 + difference 0 1) sourceC2275) = raw31341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31341; decide +kernel
    rw [ha]
    exact (canonical31341 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2275 + difference 1 2) (sourceB2275 + difference 2 1) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA2275 + difference 1 2) (sourceB2275 + difference 2 1) sourceC2275) = raw31342 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31342; decide +kernel
    rw [ha]
    exact (canonical31342 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2275 + difference 1 3) (sourceB2275 + difference 3 1) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2275 + difference 1 3) (sourceB2275 + difference 3 1) sourceC2275) = raw31343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31343; decide +kernel
    rw [ha]
    exact (canonical31343 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2275 + difference 1 4) (sourceB2275 + difference 4 1) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA2275 + difference 1 4) (sourceB2275 + difference 4 1) sourceC2275) = raw31344 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31344; decide +kernel
    rw [ha]
    exact (canonical31344 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2275 + difference 1 5) (sourceB2275 + difference 5 1) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA2275 + difference 1 5) (sourceB2275 + difference 5 1) sourceC2275) = raw31345 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31345; decide +kernel
    rw [ha]
    exact (canonical31345 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2275 + difference 2 0) (sourceB2275 + difference 0 2) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1681) := by
    have ha : (tripleCharges (sourceA2275 + difference 2 0) (sourceB2275 + difference 0 2) sourceC2275) = raw31346 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31346; decide +kernel
    rw [ha]
    exact (canonical31346 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2275 + difference 2 1) (sourceB2275 + difference 1 2) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2157) := by
    have ha : (tripleCharges (sourceA2275 + difference 2 1) (sourceB2275 + difference 1 2) sourceC2275) = raw31347 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31347; decide +kernel
    rw [ha]
    exact (canonical31347 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2275 + difference 2 3) (sourceB2275 + difference 3 2) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2177) := by
    have ha : (tripleCharges (sourceA2275 + difference 2 3) (sourceB2275 + difference 3 2) sourceC2275) = raw31348 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31348; decide +kernel
    rw [ha]
    exact (canonical31348 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2275 + difference 2 4) (sourceB2275 + difference 4 2) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA2275 + difference 2 4) (sourceB2275 + difference 4 2) sourceC2275) = raw31349 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31349; decide +kernel
    rw [ha]
    exact (canonical31349 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2275 + difference 2 5) (sourceB2275 + difference 5 2) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2275 + difference 2 5) (sourceB2275 + difference 5 2) sourceC2275) = raw31350 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31350; decide +kernel
    rw [ha]
    exact (canonical31350 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2275 + difference 3 0) (sourceB2275 + difference 0 3) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1667) := by
    have ha : (tripleCharges (sourceA2275 + difference 3 0) (sourceB2275 + difference 0 3) sourceC2275) = raw31351 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31351; decide +kernel
    rw [ha]
    exact (canonical31351 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2275 + difference 3 1) (sourceB2275 + difference 1 3) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2144) := by
    have ha : (tripleCharges (sourceA2275 + difference 3 1) (sourceB2275 + difference 1 3) sourceC2275) = raw31352 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31352; decide +kernel
    rw [ha]
    exact (canonical31352 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2275 + difference 3 2) (sourceB2275 + difference 2 3) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2194) := by
    have ha : (tripleCharges (sourceA2275 + difference 3 2) (sourceB2275 + difference 2 3) sourceC2275) = raw31353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31353; decide +kernel
    rw [ha]
    exact (canonical31353 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2275 + difference 3 4) (sourceB2275 + difference 4 3) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA2275 + difference 3 4) (sourceB2275 + difference 4 3) sourceC2275) = raw31354 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31354; decide +kernel
    rw [ha]
    exact (canonical31354 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2275 + difference 3 5) (sourceB2275 + difference 5 3) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA2275 + difference 3 5) (sourceB2275 + difference 5 3) sourceC2275) = raw31355 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31355; decide +kernel
    rw [ha]
    exact (canonical31355 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2275 + difference 4 0) (sourceB2275 + difference 0 4) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1679) := by
    have ha : (tripleCharges (sourceA2275 + difference 4 0) (sourceB2275 + difference 0 4) sourceC2275) = raw31356 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31356; decide +kernel
    rw [ha]
    exact (canonical31356 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2275 + difference 4 1) (sourceB2275 + difference 1 4) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2155) := by
    have ha : (tripleCharges (sourceA2275 + difference 4 1) (sourceB2275 + difference 1 4) sourceC2275) = raw31357 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31357; decide +kernel
    rw [ha]
    exact (canonical31357 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2275 + difference 4 2) (sourceB2275 + difference 2 4) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2212) := by
    have ha : (tripleCharges (sourceA2275 + difference 4 2) (sourceB2275 + difference 2 4) sourceC2275) = raw31358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31358; decide +kernel
    rw [ha]
    exact (canonical31358 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2275 + difference 4 3) (sourceB2275 + difference 3 4) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2176) := by
    have ha : (tripleCharges (sourceA2275 + difference 4 3) (sourceB2275 + difference 3 4) sourceC2275) = raw31359 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31359; decide +kernel
    rw [ha]
    exact (canonical31359 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2275 + difference 4 5) (sourceB2275 + difference 5 4) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA2275 + difference 4 5) (sourceB2275 + difference 5 4) sourceC2275) = raw31360 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31360; decide +kernel
    rw [ha]
    exact (canonical31360 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2275 + difference 5 0) (sourceB2275 + difference 0 5) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1685) := by
    have ha : (tripleCharges (sourceA2275 + difference 5 0) (sourceB2275 + difference 0 5) sourceC2275) = raw31361 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31361; decide +kernel
    rw [ha]
    exact (canonical31361 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2275 + difference 5 1) (sourceB2275 + difference 1 5) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2161) := by
    have ha : (tripleCharges (sourceA2275 + difference 5 1) (sourceB2275 + difference 1 5) sourceC2275) = raw31362 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31362; decide +kernel
    rw [ha]
    exact (canonical31362 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2275 + difference 5 2) (sourceB2275 + difference 2 5) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2162) := by
    have ha : (tripleCharges (sourceA2275 + difference 5 2) (sourceB2275 + difference 2 5) sourceC2275) = raw31363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31363; decide +kernel
    rw [ha]
    exact (canonical31363 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2275 + difference 5 3) (sourceB2275 + difference 3 5) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2160) := by
    have ha : (tripleCharges (sourceA2275 + difference 5 3) (sourceB2275 + difference 3 5) sourceC2275) = raw31364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31364; decide +kernel
    rw [ha]
    exact (canonical31364 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2275 + difference 5 4) (sourceB2275 + difference 4 5) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA2275 + difference 5 4) (sourceB2275 + difference 4 5) sourceC2275) = raw31365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31365; decide +kernel
    rw [ha]
    exact (canonical31365 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2275 sourceB2275 sourceC2275
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2275, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2276 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2276 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2276 + difference 0 1) (sourceB2276 + difference 1 0) sourceC2276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3379) := by
    have ha : (tripleCharges (sourceA2276 + difference 0 1) (sourceB2276 + difference 1 0) sourceC2276) = raw31366 := by
      apply Matrix.ext; unfold tripleCharges sourceA2276 sourceB2276 sourceC2276 difference raw31366; decide +kernel
    rw [ha]
    exact (canonical31366 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2276 + difference 1 1) (sourceB2276 + difference 1 1) sourceC2276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA2276 + difference 1 1) (sourceB2276 + difference 1 1) sourceC2276) = raw31367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2276 sourceB2276 sourceC2276 difference raw31367; decide +kernel
    rw [ha]
    exact (canonical31367 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2276 + difference 2 1) (sourceB2276 + difference 1 2) sourceC2276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1814) := by
    have ha : (tripleCharges (sourceA2276 + difference 2 1) (sourceB2276 + difference 1 2) sourceC2276) = raw31368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2276 sourceB2276 sourceC2276 difference raw31368; decide +kernel
    rw [ha]
    exact (canonical31368 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2276 + difference 3 1) (sourceB2276 + difference 1 3) sourceC2276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1791) := by
    have ha : (tripleCharges (sourceA2276 + difference 3 1) (sourceB2276 + difference 1 3) sourceC2276) = raw31369 := by
      apply Matrix.ext; unfold tripleCharges sourceA2276 sourceB2276 sourceC2276 difference raw31369; decide +kernel
    rw [ha]
    exact (canonical31369 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2276 + difference 4 1) (sourceB2276 + difference 1 4) sourceC2276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1795) := by
    have ha : (tripleCharges (sourceA2276 + difference 4 1) (sourceB2276 + difference 1 4) sourceC2276) = raw31370 := by
      apply Matrix.ext; unfold tripleCharges sourceA2276 sourceB2276 sourceC2276 difference raw31370; decide +kernel
    rw [ha]
    exact (canonical31370 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2276 + difference 5 1) (sourceB2276 + difference 1 5) sourceC2276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1797) := by
    have ha : (tripleCharges (sourceA2276 + difference 5 1) (sourceB2276 + difference 1 5) sourceC2276) = raw31371 := by
      apply Matrix.ext; unfold tripleCharges sourceA2276 sourceB2276 sourceC2276 difference raw31371; decide +kernel
    rw [ha]
    exact (canonical31371 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2276 + sourceB2276) sourceC2276) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2276 + sourceB2276) sourceC2276) = raw23810 := by
      apply Matrix.ext; unfold doubleCharges sourceA2276 sourceB2276 sourceC2276 raw23810; decide +kernel
    rw [ha]
    exact (canonical23810 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2276 sourceB2276 sourceC2276
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2276, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2277 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2277 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2277 + difference 2 0) (sourceB2277 + difference 0 2) sourceC2277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 932) := by
    have ha : (tripleCharges (sourceA2277 + difference 2 0) (sourceB2277 + difference 0 2) sourceC2277) = raw31372 := by
      apply Matrix.ext; unfold tripleCharges sourceA2277 sourceB2277 sourceC2277 difference raw31372; decide +kernel
    rw [ha]
    exact (canonical31372 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2277 + difference 2 1) (sourceB2277 + difference 1 2) sourceC2277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1814) := by
    have ha : (tripleCharges (sourceA2277 + difference 2 1) (sourceB2277 + difference 1 2) sourceC2277) = raw31368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2277 sourceB2277 sourceC2277 difference raw31368; decide +kernel
    rw [ha]
    exact (canonical31368 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2277 + difference 2 2) (sourceB2277 + difference 2 2) sourceC2277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA2277 + difference 2 2) (sourceB2277 + difference 2 2) sourceC2277) = raw31367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2277 sourceB2277 sourceC2277 difference raw31367; decide +kernel
    rw [ha]
    exact (canonical31367 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2277 + difference 2 3) (sourceB2277 + difference 3 2) sourceC2277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1966) := by
    have ha : (tripleCharges (sourceA2277 + difference 2 3) (sourceB2277 + difference 3 2) sourceC2277) = raw31373 := by
      apply Matrix.ext; unfold tripleCharges sourceA2277 sourceB2277 sourceC2277 difference raw31373; decide +kernel
    rw [ha]
    exact (canonical31373 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2277 + difference 2 4) (sourceB2277 + difference 4 2) sourceC2277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA2277 + difference 2 4) (sourceB2277 + difference 4 2) sourceC2277) = raw31374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2277 sourceB2277 sourceC2277 difference raw31374; decide +kernel
    rw [ha]
    exact (canonical31374 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2277 + difference 2 5) (sourceB2277 + difference 5 2) sourceC2277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2053) := by
    have ha : (tripleCharges (sourceA2277 + difference 2 5) (sourceB2277 + difference 5 2) sourceC2277) = raw31375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2277 sourceB2277 sourceC2277 difference raw31375; decide +kernel
    rw [ha]
    exact (canonical31375 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2277 + sourceB2277) sourceC2277) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2277 + sourceB2277) sourceC2277) = raw23810 := by
      apply Matrix.ext; unfold doubleCharges sourceA2277 sourceB2277 sourceC2277 raw23810; decide +kernel
    rw [ha]
    exact (canonical23810 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2277 sourceB2277 sourceC2277
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2277, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2278 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2278 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2278 + difference 3 0) (sourceB2278 + difference 0 3) sourceC2278) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 906) := by
    have ha : (tripleCharges (sourceA2278 + difference 3 0) (sourceB2278 + difference 0 3) sourceC2278) = raw31376 := by
      apply Matrix.ext; unfold tripleCharges sourceA2278 sourceB2278 sourceC2278 difference raw31376; decide +kernel
    rw [ha]
    exact (canonical31376 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2278 + difference 3 1) (sourceB2278 + difference 1 3) sourceC2278) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1791) := by
    have ha : (tripleCharges (sourceA2278 + difference 3 1) (sourceB2278 + difference 1 3) sourceC2278) = raw31369 := by
      apply Matrix.ext; unfold tripleCharges sourceA2278 sourceB2278 sourceC2278 difference raw31369; decide +kernel
    rw [ha]
    exact (canonical31369 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2278 + difference 3 2) (sourceB2278 + difference 2 3) sourceC2278) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1974) := by
    have ha : (tripleCharges (sourceA2278 + difference 3 2) (sourceB2278 + difference 2 3) sourceC2278) = raw31377 := by
      apply Matrix.ext; unfold tripleCharges sourceA2278 sourceB2278 sourceC2278 difference raw31377; decide +kernel
    rw [ha]
    exact (canonical31377 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2278 + difference 3 3) (sourceB2278 + difference 3 3) sourceC2278) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA2278 + difference 3 3) (sourceB2278 + difference 3 3) sourceC2278) = raw31367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2278 sourceB2278 sourceC2278 difference raw31367; decide +kernel
    rw [ha]
    exact (canonical31367 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2278 + difference 3 4) (sourceB2278 + difference 4 3) sourceC2278) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA2278 + difference 3 4) (sourceB2278 + difference 4 3) sourceC2278) = raw31378 := by
      apply Matrix.ext; unfold tripleCharges sourceA2278 sourceB2278 sourceC2278 difference raw31378; decide +kernel
    rw [ha]
    exact (canonical31378 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2278 + difference 3 5) (sourceB2278 + difference 5 3) sourceC2278) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2019) := by
    have ha : (tripleCharges (sourceA2278 + difference 3 5) (sourceB2278 + difference 5 3) sourceC2278) = raw31379 := by
      apply Matrix.ext; unfold tripleCharges sourceA2278 sourceB2278 sourceC2278 difference raw31379; decide +kernel
    rw [ha]
    exact (canonical31379 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2278 + sourceB2278) sourceC2278) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2278 + sourceB2278) sourceC2278) = raw23810 := by
      apply Matrix.ext; unfold doubleCharges sourceA2278 sourceB2278 sourceC2278 raw23810; decide +kernel
    rw [ha]
    exact (canonical23810 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2278 sourceB2278 sourceC2278
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2278, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2283 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2283 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2283 + difference 0 1) (sourceB2283 + difference 1 0) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5236) := by
    have ha : (tripleCharges (sourceA2283 + difference 0 1) (sourceB2283 + difference 1 0) sourceC2283) = raw31457 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31457; decide +kernel
    rw [ha]
    exact (canonical31457 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2283 + difference 0 2) (sourceB2283 + difference 2 0) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5269) := by
    have ha : (tripleCharges (sourceA2283 + difference 0 2) (sourceB2283 + difference 2 0) sourceC2283) = raw31458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31458; decide +kernel
    rw [ha]
    exact (canonical31458 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2283 + difference 0 3) (sourceB2283 + difference 3 0) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5246) := by
    have ha : (tripleCharges (sourceA2283 + difference 0 3) (sourceB2283 + difference 3 0) sourceC2283) = raw31459 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31459; decide +kernel
    rw [ha]
    exact (canonical31459 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2283 + difference 0 4) (sourceB2283 + difference 4 0) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA2283 + difference 0 4) (sourceB2283 + difference 4 0) sourceC2283) = raw31460 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31460; decide +kernel
    rw [ha]
    exact (canonical31460 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2283 + difference 0 5) (sourceB2283 + difference 5 0) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA2283 + difference 0 5) (sourceB2283 + difference 5 0) sourceC2283) = raw31461 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31461; decide +kernel
    rw [ha]
    exact (canonical31461 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2283 + difference 1 0) (sourceB2283 + difference 0 1) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA2283 + difference 1 0) (sourceB2283 + difference 0 1) sourceC2283) = raw31462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31462; decide +kernel
    rw [ha]
    exact (canonical31462 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2283 + difference 1 2) (sourceB2283 + difference 2 1) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4875) := by
    have ha : (tripleCharges (sourceA2283 + difference 1 2) (sourceB2283 + difference 2 1) sourceC2283) = raw31463 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31463; decide +kernel
    rw [ha]
    exact (canonical31463 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2283 + difference 1 3) (sourceB2283 + difference 3 1) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2283 + difference 1 3) (sourceB2283 + difference 3 1) sourceC2283) = raw31464 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31464; decide +kernel
    rw [ha]
    exact (canonical31464 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2283 + difference 1 4) (sourceB2283 + difference 4 1) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA2283 + difference 1 4) (sourceB2283 + difference 4 1) sourceC2283) = raw31465 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31465; decide +kernel
    rw [ha]
    exact (canonical31465 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2283 + difference 1 5) (sourceB2283 + difference 5 1) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA2283 + difference 1 5) (sourceB2283 + difference 5 1) sourceC2283) = raw31466 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31466; decide +kernel
    rw [ha]
    exact (canonical31466 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2283 + difference 2 0) (sourceB2283 + difference 0 2) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA2283 + difference 2 0) (sourceB2283 + difference 0 2) sourceC2283) = raw31467 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31467; decide +kernel
    rw [ha]
    exact (canonical31467 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2283 + difference 2 1) (sourceB2283 + difference 1 2) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4689) := by
    have ha : (tripleCharges (sourceA2283 + difference 2 1) (sourceB2283 + difference 1 2) sourceC2283) = raw31468 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31468; decide +kernel
    rw [ha]
    exact (canonical31468 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2283 + difference 2 3) (sourceB2283 + difference 3 2) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4767) := by
    have ha : (tripleCharges (sourceA2283 + difference 2 3) (sourceB2283 + difference 3 2) sourceC2283) = raw31469 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31469; decide +kernel
    rw [ha]
    exact (canonical31469 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2283 + difference 2 4) (sourceB2283 + difference 4 2) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2283 + difference 2 4) (sourceB2283 + difference 4 2) sourceC2283) = raw31470 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31470; decide +kernel
    rw [ha]
    exact (canonical31470 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2283 + difference 2 5) (sourceB2283 + difference 5 2) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2283 + difference 2 5) (sourceB2283 + difference 5 2) sourceC2283) = raw31471 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31471; decide +kernel
    rw [ha]
    exact (canonical31471 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2283 + difference 3 0) (sourceB2283 + difference 0 3) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4329) := by
    have ha : (tripleCharges (sourceA2283 + difference 3 0) (sourceB2283 + difference 0 3) sourceC2283) = raw31472 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31472; decide +kernel
    rw [ha]
    exact (canonical31472 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2283 + difference 3 1) (sourceB2283 + difference 1 3) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4666) := by
    have ha : (tripleCharges (sourceA2283 + difference 3 1) (sourceB2283 + difference 1 3) sourceC2283) = raw31473 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31473; decide +kernel
    rw [ha]
    exact (canonical31473 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2283 + difference 3 2) (sourceB2283 + difference 2 3) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4774) := by
    have ha : (tripleCharges (sourceA2283 + difference 3 2) (sourceB2283 + difference 2 3) sourceC2283) = raw31474 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31474; decide +kernel
    rw [ha]
    exact (canonical31474 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2283 + difference 3 4) (sourceB2283 + difference 4 3) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2283 + difference 3 4) (sourceB2283 + difference 4 3) sourceC2283) = raw31475 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31475; decide +kernel
    rw [ha]
    exact (canonical31475 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2283 + difference 3 5) (sourceB2283 + difference 5 3) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2283 + difference 3 5) (sourceB2283 + difference 5 3) sourceC2283) = raw31476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31476; decide +kernel
    rw [ha]
    exact (canonical31476 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2283 + difference 4 0) (sourceB2283 + difference 0 4) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA2283 + difference 4 0) (sourceB2283 + difference 0 4) sourceC2283) = raw31477 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31477; decide +kernel
    rw [ha]
    exact (canonical31477 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2283 + difference 4 1) (sourceB2283 + difference 1 4) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4670) := by
    have ha : (tripleCharges (sourceA2283 + difference 4 1) (sourceB2283 + difference 1 4) sourceC2283) = raw31478 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31478; decide +kernel
    rw [ha]
    exact (canonical31478 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2283 + difference 4 2) (sourceB2283 + difference 2 4) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4777) := by
    have ha : (tripleCharges (sourceA2283 + difference 4 2) (sourceB2283 + difference 2 4) sourceC2283) = raw31479 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31479; decide +kernel
    rw [ha]
    exact (canonical31479 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2283 + difference 4 3) (sourceB2283 + difference 3 4) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4757) := by
    have ha : (tripleCharges (sourceA2283 + difference 4 3) (sourceB2283 + difference 3 4) sourceC2283) = raw31480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31480; decide +kernel
    rw [ha]
    exact (canonical31480 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2283 + difference 4 5) (sourceB2283 + difference 5 4) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2283 + difference 4 5) (sourceB2283 + difference 5 4) sourceC2283) = raw31481 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31481; decide +kernel
    rw [ha]
    exact (canonical31481 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2283 + difference 5 0) (sourceB2283 + difference 0 5) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA2283 + difference 5 0) (sourceB2283 + difference 0 5) sourceC2283) = raw31482 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31482; decide +kernel
    rw [ha]
    exact (canonical31482 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2283 + difference 5 1) (sourceB2283 + difference 1 5) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4670) := by
    have ha : (tripleCharges (sourceA2283 + difference 5 1) (sourceB2283 + difference 1 5) sourceC2283) = raw31483 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31483; decide +kernel
    rw [ha]
    exact (canonical31483 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2283 + difference 5 2) (sourceB2283 + difference 2 5) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4777) := by
    have ha : (tripleCharges (sourceA2283 + difference 5 2) (sourceB2283 + difference 2 5) sourceC2283) = raw31484 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31484; decide +kernel
    rw [ha]
    exact (canonical31484 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2283 + difference 5 3) (sourceB2283 + difference 3 5) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4757) := by
    have ha : (tripleCharges (sourceA2283 + difference 5 3) (sourceB2283 + difference 3 5) sourceC2283) = raw31485 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31485; decide +kernel
    rw [ha]
    exact (canonical31485 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2283 + difference 5 4) (sourceB2283 + difference 4 5) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2283 + difference 5 4) (sourceB2283 + difference 4 5) sourceC2283) = raw31486 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31486; decide +kernel
    rw [ha]
    exact (canonical31486 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2283 sourceB2283 sourceC2283
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2283, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2285 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2285 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2285 + difference 0 1) (sourceB2285 + difference 1 0) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2682) := by
    have ha : (tripleCharges (sourceA2285 + difference 0 1) (sourceB2285 + difference 1 0) sourceC2285) = raw31517 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31517; decide +kernel
    rw [ha]
    exact (canonical31517 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2285 + difference 0 2) (sourceB2285 + difference 2 0) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2736) := by
    have ha : (tripleCharges (sourceA2285 + difference 0 2) (sourceB2285 + difference 2 0) sourceC2285) = raw31518 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31518; decide +kernel
    rw [ha]
    exact (canonical31518 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2285 + difference 0 3) (sourceB2285 + difference 3 0) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2701) := by
    have ha : (tripleCharges (sourceA2285 + difference 0 3) (sourceB2285 + difference 3 0) sourceC2285) = raw31519 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31519; decide +kernel
    rw [ha]
    exact (canonical31519 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2285 + difference 0 4) (sourceB2285 + difference 4 0) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA2285 + difference 0 4) (sourceB2285 + difference 4 0) sourceC2285) = raw31520 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31520; decide +kernel
    rw [ha]
    exact (canonical31520 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2285 + difference 0 5) (sourceB2285 + difference 5 0) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA2285 + difference 0 5) (sourceB2285 + difference 5 0) sourceC2285) = raw31521 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31521; decide +kernel
    rw [ha]
    exact (canonical31521 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2285 + difference 1 0) (sourceB2285 + difference 0 1) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA2285 + difference 1 0) (sourceB2285 + difference 0 1) sourceC2285) = raw31522 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31522; decide +kernel
    rw [ha]
    exact (canonical31522 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2285 + difference 1 2) (sourceB2285 + difference 2 1) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2288) := by
    have ha : (tripleCharges (sourceA2285 + difference 1 2) (sourceB2285 + difference 2 1) sourceC2285) = raw31523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31523; decide +kernel
    rw [ha]
    exact (canonical31523 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2285 + difference 1 3) (sourceB2285 + difference 3 1) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA2285 + difference 1 3) (sourceB2285 + difference 3 1) sourceC2285) = raw31524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31524; decide +kernel
    rw [ha]
    exact (canonical31524 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2285 + difference 1 4) (sourceB2285 + difference 4 1) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA2285 + difference 1 4) (sourceB2285 + difference 4 1) sourceC2285) = raw31525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31525; decide +kernel
    rw [ha]
    exact (canonical31525 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2285 + difference 1 5) (sourceB2285 + difference 5 1) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA2285 + difference 1 5) (sourceB2285 + difference 5 1) sourceC2285) = raw31526 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31526; decide +kernel
    rw [ha]
    exact (canonical31526 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2285 + difference 2 0) (sourceB2285 + difference 0 2) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1691) := by
    have ha : (tripleCharges (sourceA2285 + difference 2 0) (sourceB2285 + difference 0 2) sourceC2285) = raw31527 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31527; decide +kernel
    rw [ha]
    exact (canonical31527 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2285 + difference 2 1) (sourceB2285 + difference 1 2) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2166) := by
    have ha : (tripleCharges (sourceA2285 + difference 2 1) (sourceB2285 + difference 1 2) sourceC2285) = raw31528 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31528; decide +kernel
    rw [ha]
    exact (canonical31528 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2285 + difference 2 3) (sourceB2285 + difference 3 2) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2183) := by
    have ha : (tripleCharges (sourceA2285 + difference 2 3) (sourceB2285 + difference 3 2) sourceC2285) = raw31529 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31529; decide +kernel
    rw [ha]
    exact (canonical31529 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2285 + difference 2 4) (sourceB2285 + difference 4 2) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2227) := by
    have ha : (tripleCharges (sourceA2285 + difference 2 4) (sourceB2285 + difference 4 2) sourceC2285) = raw31530 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31530; decide +kernel
    rw [ha]
    exact (canonical31530 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2285 + difference 2 5) (sourceB2285 + difference 5 2) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2227) := by
    have ha : (tripleCharges (sourceA2285 + difference 2 5) (sourceB2285 + difference 5 2) sourceC2285) = raw31531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31531; decide +kernel
    rw [ha]
    exact (canonical31531 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2285 + difference 3 0) (sourceB2285 + difference 0 3) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1671) := by
    have ha : (tripleCharges (sourceA2285 + difference 3 0) (sourceB2285 + difference 0 3) sourceC2285) = raw31532 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31532; decide +kernel
    rw [ha]
    exact (canonical31532 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2285 + difference 3 1) (sourceB2285 + difference 1 3) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2148) := by
    have ha : (tripleCharges (sourceA2285 + difference 3 1) (sourceB2285 + difference 1 3) sourceC2285) = raw31533 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31533; decide +kernel
    rw [ha]
    exact (canonical31533 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2285 + difference 3 2) (sourceB2285 + difference 2 3) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2199) := by
    have ha : (tripleCharges (sourceA2285 + difference 3 2) (sourceB2285 + difference 2 3) sourceC2285) = raw31534 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31534; decide +kernel
    rw [ha]
    exact (canonical31534 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2285 + difference 3 4) (sourceB2285 + difference 4 3) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA2285 + difference 3 4) (sourceB2285 + difference 4 3) sourceC2285) = raw31535 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31535; decide +kernel
    rw [ha]
    exact (canonical31535 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2285 + difference 3 5) (sourceB2285 + difference 5 3) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA2285 + difference 3 5) (sourceB2285 + difference 5 3) sourceC2285) = raw31536 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31536; decide +kernel
    rw [ha]
    exact (canonical31536 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2285 + difference 4 0) (sourceB2285 + difference 0 4) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA2285 + difference 4 0) (sourceB2285 + difference 0 4) sourceC2285) = raw31537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31537; decide +kernel
    rw [ha]
    exact (canonical31537 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2285 + difference 4 1) (sourceB2285 + difference 1 4) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2164) := by
    have ha : (tripleCharges (sourceA2285 + difference 4 1) (sourceB2285 + difference 1 4) sourceC2285) = raw31538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31538; decide +kernel
    rw [ha]
    exact (canonical31538 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2285 + difference 4 2) (sourceB2285 + difference 2 4) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA2285 + difference 4 2) (sourceB2285 + difference 2 4) sourceC2285) = raw31539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31539; decide +kernel
    rw [ha]
    exact (canonical31539 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2285 + difference 4 3) (sourceB2285 + difference 3 4) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2181) := by
    have ha : (tripleCharges (sourceA2285 + difference 4 3) (sourceB2285 + difference 3 4) sourceC2285) = raw31540 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31540; decide +kernel
    rw [ha]
    exact (canonical31540 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2285 + difference 4 5) (sourceB2285 + difference 5 4) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA2285 + difference 4 5) (sourceB2285 + difference 5 4) sourceC2285) = raw31541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31541; decide +kernel
    rw [ha]
    exact (canonical31541 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2285 + difference 5 0) (sourceB2285 + difference 0 5) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA2285 + difference 5 0) (sourceB2285 + difference 0 5) sourceC2285) = raw31542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31542; decide +kernel
    rw [ha]
    exact (canonical31542 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2285 + difference 5 1) (sourceB2285 + difference 1 5) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2164) := by
    have ha : (tripleCharges (sourceA2285 + difference 5 1) (sourceB2285 + difference 1 5) sourceC2285) = raw31543 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31543; decide +kernel
    rw [ha]
    exact (canonical31543 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2285 + difference 5 2) (sourceB2285 + difference 2 5) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA2285 + difference 5 2) (sourceB2285 + difference 2 5) sourceC2285) = raw31544 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31544; decide +kernel
    rw [ha]
    exact (canonical31544 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2285 + difference 5 3) (sourceB2285 + difference 3 5) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2181) := by
    have ha : (tripleCharges (sourceA2285 + difference 5 3) (sourceB2285 + difference 3 5) sourceC2285) = raw31545 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31545; decide +kernel
    rw [ha]
    exact (canonical31545 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2285 + difference 5 4) (sourceB2285 + difference 4 5) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA2285 + difference 5 4) (sourceB2285 + difference 4 5) sourceC2285) = raw31546 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31546; decide +kernel
    rw [ha]
    exact (canonical31546 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2285 sourceB2285 sourceC2285
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2285, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2286 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2286 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2286 + difference 0 1) (sourceB2286 + difference 1 0) sourceC2286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3380) := by
    have ha : (tripleCharges (sourceA2286 + difference 0 1) (sourceB2286 + difference 1 0) sourceC2286) = raw31547 := by
      apply Matrix.ext; unfold tripleCharges sourceA2286 sourceB2286 sourceC2286 difference raw31547; decide +kernel
    rw [ha]
    exact (canonical31547 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2286 + difference 1 1) (sourceB2286 + difference 1 1) sourceC2286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2029) := by
    have ha : (tripleCharges (sourceA2286 + difference 1 1) (sourceB2286 + difference 1 1) sourceC2286) = raw31548 := by
      apply Matrix.ext; unfold tripleCharges sourceA2286 sourceB2286 sourceC2286 difference raw31548; decide +kernel
    rw [ha]
    exact (canonical31548 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2286 + difference 2 1) (sourceB2286 + difference 1 2) sourceC2286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1815) := by
    have ha : (tripleCharges (sourceA2286 + difference 2 1) (sourceB2286 + difference 1 2) sourceC2286) = raw31549 := by
      apply Matrix.ext; unfold tripleCharges sourceA2286 sourceB2286 sourceC2286 difference raw31549; decide +kernel
    rw [ha]
    exact (canonical31549 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2286 + difference 3 1) (sourceB2286 + difference 1 3) sourceC2286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1792) := by
    have ha : (tripleCharges (sourceA2286 + difference 3 1) (sourceB2286 + difference 1 3) sourceC2286) = raw31550 := by
      apply Matrix.ext; unfold tripleCharges sourceA2286 sourceB2286 sourceC2286 difference raw31550; decide +kernel
    rw [ha]
    exact (canonical31550 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2286 + difference 4 1) (sourceB2286 + difference 1 4) sourceC2286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1796) := by
    have ha : (tripleCharges (sourceA2286 + difference 4 1) (sourceB2286 + difference 1 4) sourceC2286) = raw31551 := by
      apply Matrix.ext; unfold tripleCharges sourceA2286 sourceB2286 sourceC2286 difference raw31551; decide +kernel
    rw [ha]
    exact (canonical31551 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2286 + difference 5 1) (sourceB2286 + difference 1 5) sourceC2286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1796) := by
    have ha : (tripleCharges (sourceA2286 + difference 5 1) (sourceB2286 + difference 1 5) sourceC2286) = raw31552 := by
      apply Matrix.ext; unfold tripleCharges sourceA2286 sourceB2286 sourceC2286 difference raw31552; decide +kernel
    rw [ha]
    exact (canonical31552 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2286 + sourceB2286) sourceC2286) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2286 + sourceB2286) sourceC2286) = raw31553 := by
      apply Matrix.ext; unfold doubleCharges sourceA2286 sourceB2286 sourceC2286 raw31553; decide +kernel
    rw [ha]
    exact (canonical31553 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2286 sourceB2286 sourceC2286
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2286, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2287 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2287 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2287 + difference 2 0) (sourceB2287 + difference 0 2) sourceC2287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 933) := by
    have ha : (tripleCharges (sourceA2287 + difference 2 0) (sourceB2287 + difference 0 2) sourceC2287) = raw31554 := by
      apply Matrix.ext; unfold tripleCharges sourceA2287 sourceB2287 sourceC2287 difference raw31554; decide +kernel
    rw [ha]
    exact (canonical31554 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2287 + difference 2 1) (sourceB2287 + difference 1 2) sourceC2287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1815) := by
    have ha : (tripleCharges (sourceA2287 + difference 2 1) (sourceB2287 + difference 1 2) sourceC2287) = raw31549 := by
      apply Matrix.ext; unfold tripleCharges sourceA2287 sourceB2287 sourceC2287 difference raw31549; decide +kernel
    rw [ha]
    exact (canonical31549 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2287 + difference 2 2) (sourceB2287 + difference 2 2) sourceC2287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2029) := by
    have ha : (tripleCharges (sourceA2287 + difference 2 2) (sourceB2287 + difference 2 2) sourceC2287) = raw31548 := by
      apply Matrix.ext; unfold tripleCharges sourceA2287 sourceB2287 sourceC2287 difference raw31548; decide +kernel
    rw [ha]
    exact (canonical31548 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2287 + difference 2 3) (sourceB2287 + difference 3 2) sourceC2287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1967) := by
    have ha : (tripleCharges (sourceA2287 + difference 2 3) (sourceB2287 + difference 3 2) sourceC2287) = raw31555 := by
      apply Matrix.ext; unfold tripleCharges sourceA2287 sourceB2287 sourceC2287 difference raw31555; decide +kernel
    rw [ha]
    exact (canonical31555 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2287 + difference 2 4) (sourceB2287 + difference 4 2) sourceC2287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2057) := by
    have ha : (tripleCharges (sourceA2287 + difference 2 4) (sourceB2287 + difference 4 2) sourceC2287) = raw31556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2287 sourceB2287 sourceC2287 difference raw31556; decide +kernel
    rw [ha]
    exact (canonical31556 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2287 + difference 2 5) (sourceB2287 + difference 5 2) sourceC2287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2057) := by
    have ha : (tripleCharges (sourceA2287 + difference 2 5) (sourceB2287 + difference 5 2) sourceC2287) = raw31557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2287 sourceB2287 sourceC2287 difference raw31557; decide +kernel
    rw [ha]
    exact (canonical31557 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2287 + sourceB2287) sourceC2287) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2287 + sourceB2287) sourceC2287) = raw31553 := by
      apply Matrix.ext; unfold doubleCharges sourceA2287 sourceB2287 sourceC2287 raw31553; decide +kernel
    rw [ha]
    exact (canonical31553 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2287 sourceB2287 sourceC2287
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2287, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2288 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2288 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2288 + difference 3 0) (sourceB2288 + difference 0 3) sourceC2288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 907) := by
    have ha : (tripleCharges (sourceA2288 + difference 3 0) (sourceB2288 + difference 0 3) sourceC2288) = raw31558 := by
      apply Matrix.ext; unfold tripleCharges sourceA2288 sourceB2288 sourceC2288 difference raw31558; decide +kernel
    rw [ha]
    exact (canonical31558 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2288 + difference 3 1) (sourceB2288 + difference 1 3) sourceC2288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1792) := by
    have ha : (tripleCharges (sourceA2288 + difference 3 1) (sourceB2288 + difference 1 3) sourceC2288) = raw31550 := by
      apply Matrix.ext; unfold tripleCharges sourceA2288 sourceB2288 sourceC2288 difference raw31550; decide +kernel
    rw [ha]
    exact (canonical31550 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2288 + difference 3 2) (sourceB2288 + difference 2 3) sourceC2288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1975) := by
    have ha : (tripleCharges (sourceA2288 + difference 3 2) (sourceB2288 + difference 2 3) sourceC2288) = raw31559 := by
      apply Matrix.ext; unfold tripleCharges sourceA2288 sourceB2288 sourceC2288 difference raw31559; decide +kernel
    rw [ha]
    exact (canonical31559 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2288 + difference 3 3) (sourceB2288 + difference 3 3) sourceC2288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2029) := by
    have ha : (tripleCharges (sourceA2288 + difference 3 3) (sourceB2288 + difference 3 3) sourceC2288) = raw31548 := by
      apply Matrix.ext; unfold tripleCharges sourceA2288 sourceB2288 sourceC2288 difference raw31548; decide +kernel
    rw [ha]
    exact (canonical31548 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2288 + difference 3 4) (sourceB2288 + difference 4 3) sourceC2288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2020) := by
    have ha : (tripleCharges (sourceA2288 + difference 3 4) (sourceB2288 + difference 4 3) sourceC2288) = raw31560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2288 sourceB2288 sourceC2288 difference raw31560; decide +kernel
    rw [ha]
    exact (canonical31560 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2288 + difference 3 5) (sourceB2288 + difference 5 3) sourceC2288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2020) := by
    have ha : (tripleCharges (sourceA2288 + difference 3 5) (sourceB2288 + difference 5 3) sourceC2288) = raw31561 := by
      apply Matrix.ext; unfold tripleCharges sourceA2288 sourceB2288 sourceC2288 difference raw31561; decide +kernel
    rw [ha]
    exact (canonical31561 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2288 + sourceB2288) sourceC2288) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2288 + sourceB2288) sourceC2288) = raw31553 := by
      apply Matrix.ext; unfold doubleCharges sourceA2288 sourceB2288 sourceC2288 raw31553; decide +kernel
    rw [ha]
    exact (canonical31553 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2288 sourceB2288 sourceC2288
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2288, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1857 : Integer.Sparse.reindex keyMap MixedData.row1857 = numericRow1857 := by decide +kernel

theorem numericCheck1857 (x : Master → ℝ) : Integer.Sparse.eval numericRow1857 x =
    (1 : ℝ) * reducedSource1857 x := by
  norm_num [numericRow1857, reducedSource1857, Integer.Sparse.eval, Sparse.eval, nodeValue1876, nodeValue1880, nodeValue1881, nodeValue1918, nodeValue2082, nodeValue3448, nodeValue4080]

theorem reindexCheck1860 : Integer.Sparse.reindex keyMap MixedData.row1860 = numericRow1860 := by decide +kernel

theorem numericCheck1860 (x : Master → ℝ) : Integer.Sparse.eval numericRow1860 x =
    (1 : ℝ) * reducedSource1860 x := by
  norm_num [numericRow1860, reducedSource1860, Integer.Sparse.eval, Sparse.eval, nodeValue1667, nodeValue1679, nodeValue1681, nodeValue1685, nodeValue1738, nodeValue2144, nodeValue2155, nodeValue2157, nodeValue2160, nodeValue2161, nodeValue2162, nodeValue2176, nodeValue2177, nodeValue2190, nodeValue2194, nodeValue2195, nodeValue2203, nodeValue2205, nodeValue2212, nodeValue2215, nodeValue2216, nodeValue2220, nodeValue2264, nodeValue2276, nodeValue2278, nodeValue2677, nodeValue2697, nodeValue2722, nodeValue2729, nodeValue2731]

theorem reindexCheck1861 : Integer.Sparse.reindex keyMap MixedData.row1861 = numericRow1861 := by decide +kernel

theorem numericCheck1861 (x : Master → ℝ) : Integer.Sparse.eval numericRow1861 x =
    (1 : ℝ) * reducedSource1861 x := by
  norm_num [numericRow1861, reducedSource1861, Integer.Sparse.eval, Sparse.eval, nodeValue1791, nodeValue1795, nodeValue1797, nodeValue1814, nodeValue2028, nodeValue3379, nodeValue4084]

theorem reindexCheck1862 : Integer.Sparse.reindex keyMap MixedData.row1862 = numericRow1862 := by decide +kernel

theorem numericCheck1862 (x : Master → ℝ) : Integer.Sparse.eval numericRow1862 x =
    (1 : ℝ) * reducedSource1862 x := by
  norm_num [numericRow1862, reducedSource1862, Integer.Sparse.eval, Sparse.eval, nodeValue932, nodeValue1814, nodeValue1966, nodeValue2028, nodeValue2053, nodeValue2058, nodeValue4084]

theorem reindexCheck1863 : Integer.Sparse.reindex keyMap MixedData.row1863 = numericRow1863 := by decide +kernel

theorem numericCheck1863 (x : Master → ℝ) : Integer.Sparse.eval numericRow1863 x =
    (1 : ℝ) * reducedSource1863 x := by
  norm_num [numericRow1863, reducedSource1863, Integer.Sparse.eval, Sparse.eval, nodeValue906, nodeValue1791, nodeValue1974, nodeValue2019, nodeValue2021, nodeValue2028, nodeValue4084]

theorem reindexCheck1865 : Integer.Sparse.reindex keyMap MixedData.row1865 = numericRow1865 := by decide +kernel

theorem numericCheck1865 (x : Master → ℝ) : Integer.Sparse.eval numericRow1865 x =
    (4 : ℝ) * reducedSource1865 x := by
  norm_num [numericRow1865, reducedSource1865, Integer.Sparse.eval, Sparse.eval, nodeValue4329, nodeValue4335, nodeValue4355, nodeValue4467, nodeValue4666, nodeValue4670, nodeValue4689, nodeValue4757, nodeValue4767, nodeValue4774, nodeValue4777, nodeValue4802, nodeValue4807, nodeValue4811, nodeValue4838, nodeValue4875, nodeValue4895, nodeValue5236, nodeValue5246, nodeValue5269, nodeValue5271]
  ring

theorem reindexCheck1867 : Integer.Sparse.reindex keyMap MixedData.row1867 = numericRow1867 := by decide +kernel

theorem numericCheck1867 (x : Master → ℝ) : Integer.Sparse.eval numericRow1867 x =
    (1 : ℝ) * reducedSource1867 x := by
  norm_num [numericRow1867, reducedSource1867, Integer.Sparse.eval, Sparse.eval, nodeValue1671, nodeValue1689, nodeValue1691, nodeValue1751, nodeValue2148, nodeValue2164, nodeValue2166, nodeValue2181, nodeValue2183, nodeValue2199, nodeValue2202, nodeValue2223, nodeValue2224, nodeValue2225, nodeValue2227, nodeValue2288, nodeValue2291, nodeValue2682, nodeValue2701, nodeValue2736, nodeValue2739]

theorem reindexCheck1868 : Integer.Sparse.reindex keyMap MixedData.row1868 = numericRow1868 := by decide +kernel

theorem numericCheck1868 (x : Master → ℝ) : Integer.Sparse.eval numericRow1868 x =
    (1 : ℝ) * reducedSource1868 x := by
  norm_num [numericRow1868, reducedSource1868, Integer.Sparse.eval, Sparse.eval, nodeValue1792, nodeValue1796, nodeValue1815, nodeValue2029, nodeValue3380, nodeValue4083]

theorem reindexCheck1869 : Integer.Sparse.reindex keyMap MixedData.row1869 = numericRow1869 := by decide +kernel

theorem numericCheck1869 (x : Master → ℝ) : Integer.Sparse.eval numericRow1869 x =
    (1 : ℝ) * reducedSource1869 x := by
  norm_num [numericRow1869, reducedSource1869, Integer.Sparse.eval, Sparse.eval, nodeValue933, nodeValue1815, nodeValue1967, nodeValue2029, nodeValue2057, nodeValue4083]

theorem reindexCheck1870 : Integer.Sparse.reindex keyMap MixedData.row1870 = numericRow1870 := by decide +kernel

theorem numericCheck1870 (x : Master → ℝ) : Integer.Sparse.eval numericRow1870 x =
    (1 : ℝ) * reducedSource1870 x := by
  norm_num [numericRow1870, reducedSource1870, Integer.Sparse.eval, Sparse.eval, nodeValue907, nodeValue1792, nodeValue1975, nodeValue2020, nodeValue2029, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1857 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1857 (mixedVector B) = 0 := by
  have h1876 : mixedVector B (Sum.inr 1876) = Sparse.eval nodeValue1876 (mixedVector B) := by
    change mixedMoment B node1876 node1876Labels = _
    exact sound1876 B hB hF
  have h1880 : mixedVector B (Sum.inr 1880) = Sparse.eval nodeValue1880 (mixedVector B) := by
    change mixedMoment B node1880 node1880Labels = _
    exact sound1880 B hB hF
  have h1881 : mixedVector B (Sum.inr 1881) = Sparse.eval nodeValue1881 (mixedVector B) := by
    change mixedMoment B node1881 node1881Labels = _
    exact sound1881 B hB hF
  have h1918 : mixedVector B (Sum.inr 1918) = Sparse.eval nodeValue1918 (mixedVector B) := by
    change mixedMoment B node1918 node1918Labels = _
    exact sound1918 B hB hF
  have h2082 : mixedVector B (Sum.inr 2082) = Sparse.eval nodeValue2082 (mixedVector B) := by
    change mixedMoment B node2082 node2082Labels = _
    exact sound2082 B hB hF
  have h3448 : mixedVector B (Sum.inr 3448) = Sparse.eval nodeValue3448 (mixedVector B) := by
    change mixedMoment B node3448 node3448Labels = _
    exact sound3448 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm2271, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1876, h1880, h1881, h1918, h2082, h3448, h4080, reducedSource1857] using sourceEq2271 B hB

theorem rowSound1857 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1857 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1857, numericCheck1857, reducedZero1857 B hB hF, mul_zero]

theorem reducedZero1860 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1860 (mixedVector B) = 0 := by
  have h1667 : mixedVector B (Sum.inr 1667) = Sparse.eval nodeValue1667 (mixedVector B) := by
    change mixedMoment B node1667 node1667Labels = _
    exact sound1667 B hB hF
  have h1679 : mixedVector B (Sum.inr 1679) = Sparse.eval nodeValue1679 (mixedVector B) := by
    change mixedMoment B node1679 node1679Labels = _
    exact sound1679 B hB hF
  have h1681 : mixedVector B (Sum.inr 1681) = Sparse.eval nodeValue1681 (mixedVector B) := by
    change mixedMoment B node1681 node1681Labels = _
    exact sound1681 B hB hF
  have h1685 : mixedVector B (Sum.inr 1685) = Sparse.eval nodeValue1685 (mixedVector B) := by
    change mixedMoment B node1685 node1685Labels = _
    exact sound1685 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h2144 : mixedVector B (Sum.inr 2144) = Sparse.eval nodeValue2144 (mixedVector B) := by
    change mixedMoment B node2144 node2144Labels = _
    exact sound2144 B hB hF
  have h2155 : mixedVector B (Sum.inr 2155) = Sparse.eval nodeValue2155 (mixedVector B) := by
    change mixedMoment B node2155 node2155Labels = _
    exact sound2155 B hB hF
  have h2157 : mixedVector B (Sum.inr 2157) = Sparse.eval nodeValue2157 (mixedVector B) := by
    change mixedMoment B node2157 node2157Labels = _
    exact sound2157 B hB hF
  have h2160 : mixedVector B (Sum.inr 2160) = Sparse.eval nodeValue2160 (mixedVector B) := by
    change mixedMoment B node2160 node2160Labels = _
    exact sound2160 B hB hF
  have h2161 : mixedVector B (Sum.inr 2161) = Sparse.eval nodeValue2161 (mixedVector B) := by
    change mixedMoment B node2161 node2161Labels = _
    exact sound2161 B hB hF
  have h2162 : mixedVector B (Sum.inr 2162) = Sparse.eval nodeValue2162 (mixedVector B) := by
    change mixedMoment B node2162 node2162Labels = _
    exact sound2162 B hB hF
  have h2176 : mixedVector B (Sum.inr 2176) = Sparse.eval nodeValue2176 (mixedVector B) := by
    change mixedMoment B node2176 node2176Labels = _
    exact sound2176 B hB hF
  have h2177 : mixedVector B (Sum.inr 2177) = Sparse.eval nodeValue2177 (mixedVector B) := by
    change mixedMoment B node2177 node2177Labels = _
    exact sound2177 B hB hF
  have h2190 : mixedVector B (Sum.inr 2190) = Sparse.eval nodeValue2190 (mixedVector B) := by
    change mixedMoment B node2190 node2190Labels = _
    exact sound2190 B hB hF
  have h2194 : mixedVector B (Sum.inr 2194) = Sparse.eval nodeValue2194 (mixedVector B) := by
    change mixedMoment B node2194 node2194Labels = _
    exact sound2194 B hB hF
  have h2195 : mixedVector B (Sum.inr 2195) = Sparse.eval nodeValue2195 (mixedVector B) := by
    change mixedMoment B node2195 node2195Labels = _
    exact sound2195 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h2212 : mixedVector B (Sum.inr 2212) = Sparse.eval nodeValue2212 (mixedVector B) := by
    change mixedMoment B node2212 node2212Labels = _
    exact sound2212 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h2220 : mixedVector B (Sum.inr 2220) = Sparse.eval nodeValue2220 (mixedVector B) := by
    change mixedMoment B node2220 node2220Labels = _
    exact sound2220 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  have h2276 : mixedVector B (Sum.inr 2276) = Sparse.eval nodeValue2276 (mixedVector B) := by
    change mixedMoment B node2276 node2276Labels = _
    exact sound2276 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h2677 : mixedVector B (Sum.inr 2677) = Sparse.eval nodeValue2677 (mixedVector B) := by
    change mixedMoment B node2677 node2677Labels = _
    exact sound2677 B hB hF
  have h2697 : mixedVector B (Sum.inr 2697) = Sparse.eval nodeValue2697 (mixedVector B) := by
    change mixedMoment B node2697 node2697Labels = _
    exact sound2697 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2729 : mixedVector B (Sum.inr 2729) = Sparse.eval nodeValue2729 (mixedVector B) := by
    change mixedMoment B node2729 node2729Labels = _
    exact sound2729 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  simpa only [sourceForm2275, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1667, h1679, h1681, h1685, h1738, h2144, h2155, h2157, h2160, h2161, h2162, h2176, h2177, h2190, h2194, h2195, h2203, h2205, h2212, h2215, h2216, h2220, h2264, h2276, h2278, h2677, h2697, h2722, h2729, h2731, reducedSource1860] using sourceEq2275 B hB

theorem rowSound1860 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1860 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1860, numericCheck1860, reducedZero1860 B hB hF, mul_zero]

theorem reducedZero1861 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1861 (mixedVector B) = 0 := by
  have h1791 : mixedVector B (Sum.inr 1791) = Sparse.eval nodeValue1791 (mixedVector B) := by
    change mixedMoment B node1791 node1791Labels = _
    exact sound1791 B hB hF
  have h1795 : mixedVector B (Sum.inr 1795) = Sparse.eval nodeValue1795 (mixedVector B) := by
    change mixedMoment B node1795 node1795Labels = _
    exact sound1795 B hB hF
  have h1797 : mixedVector B (Sum.inr 1797) = Sparse.eval nodeValue1797 (mixedVector B) := by
    change mixedMoment B node1797 node1797Labels = _
    exact sound1797 B hB hF
  have h1814 : mixedVector B (Sum.inr 1814) = Sparse.eval nodeValue1814 (mixedVector B) := by
    change mixedMoment B node1814 node1814Labels = _
    exact sound1814 B hB hF
  have h2028 : mixedVector B (Sum.inr 2028) = Sparse.eval nodeValue2028 (mixedVector B) := by
    change mixedMoment B node2028 node2028Labels = _
    exact sound2028 B hB hF
  have h3379 : mixedVector B (Sum.inr 3379) = Sparse.eval nodeValue3379 (mixedVector B) := by
    change mixedMoment B node3379 node3379Labels = _
    exact sound3379 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2276, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1791, h1795, h1797, h1814, h2028, h3379, h4084, reducedSource1861] using sourceEq2276 B hB

theorem rowSound1861 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1861 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1861, numericCheck1861, reducedZero1861 B hB hF, mul_zero]

theorem reducedZero1862 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1862 (mixedVector B) = 0 := by
  have h932 : mixedVector B (Sum.inr 932) = Sparse.eval nodeValue932 (mixedVector B) := by
    change mixedMoment B node932 node932Labels = _
    exact sound932 B hB hF
  have h1814 : mixedVector B (Sum.inr 1814) = Sparse.eval nodeValue1814 (mixedVector B) := by
    change mixedMoment B node1814 node1814Labels = _
    exact sound1814 B hB hF
  have h1966 : mixedVector B (Sum.inr 1966) = Sparse.eval nodeValue1966 (mixedVector B) := by
    change mixedMoment B node1966 node1966Labels = _
    exact sound1966 B hB hF
  have h2028 : mixedVector B (Sum.inr 2028) = Sparse.eval nodeValue2028 (mixedVector B) := by
    change mixedMoment B node2028 node2028Labels = _
    exact sound2028 B hB hF
  have h2053 : mixedVector B (Sum.inr 2053) = Sparse.eval nodeValue2053 (mixedVector B) := by
    change mixedMoment B node2053 node2053Labels = _
    exact sound2053 B hB hF
  have h2058 : mixedVector B (Sum.inr 2058) = Sparse.eval nodeValue2058 (mixedVector B) := by
    change mixedMoment B node2058 node2058Labels = _
    exact sound2058 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2277, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h932, h1814, h1966, h2028, h2053, h2058, h4084, reducedSource1862] using sourceEq2277 B hB

theorem rowSound1862 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1862 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1862, numericCheck1862, reducedZero1862 B hB hF, mul_zero]

theorem reducedZero1863 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1863 (mixedVector B) = 0 := by
  have h906 : mixedVector B (Sum.inr 906) = Sparse.eval nodeValue906 (mixedVector B) := by
    change mixedMoment B node906 node906Labels = _
    exact sound906 B hB hF
  have h1791 : mixedVector B (Sum.inr 1791) = Sparse.eval nodeValue1791 (mixedVector B) := by
    change mixedMoment B node1791 node1791Labels = _
    exact sound1791 B hB hF
  have h1974 : mixedVector B (Sum.inr 1974) = Sparse.eval nodeValue1974 (mixedVector B) := by
    change mixedMoment B node1974 node1974Labels = _
    exact sound1974 B hB hF
  have h2019 : mixedVector B (Sum.inr 2019) = Sparse.eval nodeValue2019 (mixedVector B) := by
    change mixedMoment B node2019 node2019Labels = _
    exact sound2019 B hB hF
  have h2021 : mixedVector B (Sum.inr 2021) = Sparse.eval nodeValue2021 (mixedVector B) := by
    change mixedMoment B node2021 node2021Labels = _
    exact sound2021 B hB hF
  have h2028 : mixedVector B (Sum.inr 2028) = Sparse.eval nodeValue2028 (mixedVector B) := by
    change mixedMoment B node2028 node2028Labels = _
    exact sound2028 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2278, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h906, h1791, h1974, h2019, h2021, h2028, h4084, reducedSource1863] using sourceEq2278 B hB

theorem rowSound1863 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1863 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1863, numericCheck1863, reducedZero1863 B hB hF, mul_zero]

theorem reducedZero1865 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1865 (mixedVector B) = 0 := by
  have h4329 : mixedVector B (Sum.inr 4329) = Sparse.eval nodeValue4329 (mixedVector B) := by
    change mixedMoment B node4329 node4329Labels = _
    exact sound4329 B hB hF
  have h4335 : mixedVector B (Sum.inr 4335) = Sparse.eval nodeValue4335 (mixedVector B) := by
    change mixedMoment B node4335 node4335Labels = _
    exact sound4335 B hB hF
  have h4355 : mixedVector B (Sum.inr 4355) = Sparse.eval nodeValue4355 (mixedVector B) := by
    change mixedMoment B node4355 node4355Labels = _
    exact sound4355 B hB hF
  have h4467 : mixedVector B (Sum.inr 4467) = Sparse.eval nodeValue4467 (mixedVector B) := by
    change mixedMoment B node4467 node4467Labels = _
    exact sound4467 B hB hF
  have h4666 : mixedVector B (Sum.inr 4666) = Sparse.eval nodeValue4666 (mixedVector B) := by
    change mixedMoment B node4666 node4666Labels = _
    exact sound4666 B hB hF
  have h4670 : mixedVector B (Sum.inr 4670) = Sparse.eval nodeValue4670 (mixedVector B) := by
    change mixedMoment B node4670 node4670Labels = _
    exact sound4670 B hB hF
  have h4689 : mixedVector B (Sum.inr 4689) = Sparse.eval nodeValue4689 (mixedVector B) := by
    change mixedMoment B node4689 node4689Labels = _
    exact sound4689 B hB hF
  have h4757 : mixedVector B (Sum.inr 4757) = Sparse.eval nodeValue4757 (mixedVector B) := by
    change mixedMoment B node4757 node4757Labels = _
    exact sound4757 B hB hF
  have h4767 : mixedVector B (Sum.inr 4767) = Sparse.eval nodeValue4767 (mixedVector B) := by
    change mixedMoment B node4767 node4767Labels = _
    exact sound4767 B hB hF
  have h4774 : mixedVector B (Sum.inr 4774) = Sparse.eval nodeValue4774 (mixedVector B) := by
    change mixedMoment B node4774 node4774Labels = _
    exact sound4774 B hB hF
  have h4777 : mixedVector B (Sum.inr 4777) = Sparse.eval nodeValue4777 (mixedVector B) := by
    change mixedMoment B node4777 node4777Labels = _
    exact sound4777 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4838 : mixedVector B (Sum.inr 4838) = Sparse.eval nodeValue4838 (mixedVector B) := by
    change mixedMoment B node4838 node4838Labels = _
    exact sound4838 B hB hF
  have h4875 : mixedVector B (Sum.inr 4875) = Sparse.eval nodeValue4875 (mixedVector B) := by
    change mixedMoment B node4875 node4875Labels = _
    exact sound4875 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  have h5236 : mixedVector B (Sum.inr 5236) = Sparse.eval nodeValue5236 (mixedVector B) := by
    change mixedMoment B node5236 node5236Labels = _
    exact sound5236 B hB hF
  have h5246 : mixedVector B (Sum.inr 5246) = Sparse.eval nodeValue5246 (mixedVector B) := by
    change mixedMoment B node5246 node5246Labels = _
    exact sound5246 B hB hF
  have h5269 : mixedVector B (Sum.inr 5269) = Sparse.eval nodeValue5269 (mixedVector B) := by
    change mixedMoment B node5269 node5269Labels = _
    exact sound5269 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  simpa only [sourceForm2283, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4329, h4335, h4355, h4467, h4666, h4670, h4689, h4757, h4767, h4774, h4777, h4802, h4807, h4811, h4838, h4875, h4895, h5236, h5246, h5269, h5271, reducedSource1865] using sourceEq2283 B hB

theorem rowSound1865 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1865 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1865, numericCheck1865, reducedZero1865 B hB hF, mul_zero]

theorem reducedZero1867 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1867 (mixedVector B) = 0 := by
  have h1671 : mixedVector B (Sum.inr 1671) = Sparse.eval nodeValue1671 (mixedVector B) := by
    change mixedMoment B node1671 node1671Labels = _
    exact sound1671 B hB hF
  have h1689 : mixedVector B (Sum.inr 1689) = Sparse.eval nodeValue1689 (mixedVector B) := by
    change mixedMoment B node1689 node1689Labels = _
    exact sound1689 B hB hF
  have h1691 : mixedVector B (Sum.inr 1691) = Sparse.eval nodeValue1691 (mixedVector B) := by
    change mixedMoment B node1691 node1691Labels = _
    exact sound1691 B hB hF
  have h1751 : mixedVector B (Sum.inr 1751) = Sparse.eval nodeValue1751 (mixedVector B) := by
    change mixedMoment B node1751 node1751Labels = _
    exact sound1751 B hB hF
  have h2148 : mixedVector B (Sum.inr 2148) = Sparse.eval nodeValue2148 (mixedVector B) := by
    change mixedMoment B node2148 node2148Labels = _
    exact sound2148 B hB hF
  have h2164 : mixedVector B (Sum.inr 2164) = Sparse.eval nodeValue2164 (mixedVector B) := by
    change mixedMoment B node2164 node2164Labels = _
    exact sound2164 B hB hF
  have h2166 : mixedVector B (Sum.inr 2166) = Sparse.eval nodeValue2166 (mixedVector B) := by
    change mixedMoment B node2166 node2166Labels = _
    exact sound2166 B hB hF
  have h2181 : mixedVector B (Sum.inr 2181) = Sparse.eval nodeValue2181 (mixedVector B) := by
    change mixedMoment B node2181 node2181Labels = _
    exact sound2181 B hB hF
  have h2183 : mixedVector B (Sum.inr 2183) = Sparse.eval nodeValue2183 (mixedVector B) := by
    change mixedMoment B node2183 node2183Labels = _
    exact sound2183 B hB hF
  have h2199 : mixedVector B (Sum.inr 2199) = Sparse.eval nodeValue2199 (mixedVector B) := by
    change mixedMoment B node2199 node2199Labels = _
    exact sound2199 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h2223 : mixedVector B (Sum.inr 2223) = Sparse.eval nodeValue2223 (mixedVector B) := by
    change mixedMoment B node2223 node2223Labels = _
    exact sound2223 B hB hF
  have h2224 : mixedVector B (Sum.inr 2224) = Sparse.eval nodeValue2224 (mixedVector B) := by
    change mixedMoment B node2224 node2224Labels = _
    exact sound2224 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h2227 : mixedVector B (Sum.inr 2227) = Sparse.eval nodeValue2227 (mixedVector B) := by
    change mixedMoment B node2227 node2227Labels = _
    exact sound2227 B hB hF
  have h2288 : mixedVector B (Sum.inr 2288) = Sparse.eval nodeValue2288 (mixedVector B) := by
    change mixedMoment B node2288 node2288Labels = _
    exact sound2288 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  have h2682 : mixedVector B (Sum.inr 2682) = Sparse.eval nodeValue2682 (mixedVector B) := by
    change mixedMoment B node2682 node2682Labels = _
    exact sound2682 B hB hF
  have h2701 : mixedVector B (Sum.inr 2701) = Sparse.eval nodeValue2701 (mixedVector B) := by
    change mixedMoment B node2701 node2701Labels = _
    exact sound2701 B hB hF
  have h2736 : mixedVector B (Sum.inr 2736) = Sparse.eval nodeValue2736 (mixedVector B) := by
    change mixedMoment B node2736 node2736Labels = _
    exact sound2736 B hB hF
  have h2739 : mixedVector B (Sum.inr 2739) = Sparse.eval nodeValue2739 (mixedVector B) := by
    change mixedMoment B node2739 node2739Labels = _
    exact sound2739 B hB hF
  simpa only [sourceForm2285, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1671, h1689, h1691, h1751, h2148, h2164, h2166, h2181, h2183, h2199, h2202, h2223, h2224, h2225, h2227, h2288, h2291, h2682, h2701, h2736, h2739, reducedSource1867] using sourceEq2285 B hB

theorem rowSound1867 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1867 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1867, numericCheck1867, reducedZero1867 B hB hF, mul_zero]

theorem reducedZero1868 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1868 (mixedVector B) = 0 := by
  have h1792 : mixedVector B (Sum.inr 1792) = Sparse.eval nodeValue1792 (mixedVector B) := by
    change mixedMoment B node1792 node1792Labels = _
    exact sound1792 B hB hF
  have h1796 : mixedVector B (Sum.inr 1796) = Sparse.eval nodeValue1796 (mixedVector B) := by
    change mixedMoment B node1796 node1796Labels = _
    exact sound1796 B hB hF
  have h1815 : mixedVector B (Sum.inr 1815) = Sparse.eval nodeValue1815 (mixedVector B) := by
    change mixedMoment B node1815 node1815Labels = _
    exact sound1815 B hB hF
  have h2029 : mixedVector B (Sum.inr 2029) = Sparse.eval nodeValue2029 (mixedVector B) := by
    change mixedMoment B node2029 node2029Labels = _
    exact sound2029 B hB hF
  have h3380 : mixedVector B (Sum.inr 3380) = Sparse.eval nodeValue3380 (mixedVector B) := by
    change mixedMoment B node3380 node3380Labels = _
    exact sound3380 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2286, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1792, h1796, h1815, h2029, h3380, h4083, reducedSource1868] using sourceEq2286 B hB

theorem rowSound1868 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1868 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1868, numericCheck1868, reducedZero1868 B hB hF, mul_zero]

theorem reducedZero1869 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1869 (mixedVector B) = 0 := by
  have h933 : mixedVector B (Sum.inr 933) = Sparse.eval nodeValue933 (mixedVector B) := by
    change mixedMoment B node933 node933Labels = _
    exact sound933 B hB hF
  have h1815 : mixedVector B (Sum.inr 1815) = Sparse.eval nodeValue1815 (mixedVector B) := by
    change mixedMoment B node1815 node1815Labels = _
    exact sound1815 B hB hF
  have h1967 : mixedVector B (Sum.inr 1967) = Sparse.eval nodeValue1967 (mixedVector B) := by
    change mixedMoment B node1967 node1967Labels = _
    exact sound1967 B hB hF
  have h2029 : mixedVector B (Sum.inr 2029) = Sparse.eval nodeValue2029 (mixedVector B) := by
    change mixedMoment B node2029 node2029Labels = _
    exact sound2029 B hB hF
  have h2057 : mixedVector B (Sum.inr 2057) = Sparse.eval nodeValue2057 (mixedVector B) := by
    change mixedMoment B node2057 node2057Labels = _
    exact sound2057 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2287, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h933, h1815, h1967, h2029, h2057, h4083, reducedSource1869] using sourceEq2287 B hB

theorem rowSound1869 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1869 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1869, numericCheck1869, reducedZero1869 B hB hF, mul_zero]

theorem reducedZero1870 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1870 (mixedVector B) = 0 := by
  have h907 : mixedVector B (Sum.inr 907) = Sparse.eval nodeValue907 (mixedVector B) := by
    change mixedMoment B node907 node907Labels = _
    exact sound907 B hB hF
  have h1792 : mixedVector B (Sum.inr 1792) = Sparse.eval nodeValue1792 (mixedVector B) := by
    change mixedMoment B node1792 node1792Labels = _
    exact sound1792 B hB hF
  have h1975 : mixedVector B (Sum.inr 1975) = Sparse.eval nodeValue1975 (mixedVector B) := by
    change mixedMoment B node1975 node1975Labels = _
    exact sound1975 B hB hF
  have h2020 : mixedVector B (Sum.inr 2020) = Sparse.eval nodeValue2020 (mixedVector B) := by
    change mixedMoment B node2020 node2020Labels = _
    exact sound2020 B hB hF
  have h2029 : mixedVector B (Sum.inr 2029) = Sparse.eval nodeValue2029 (mixedVector B) := by
    change mixedMoment B node2029 node2029Labels = _
    exact sound2029 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2288, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h907, h1792, h1975, h2020, h2029, h4083, reducedSource1870] using sourceEq2288 B hB

theorem rowSound1870 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1870 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1870, numericCheck1870, reducedZero1870 B hB hF, mul_zero]

theorem sourceRowsAt1856 : MixedData.sourceRows (1856 : Fin 2425) =
    MixedData.row1856 := by decide +kernel

theorem sourceRowsAt1857 : MixedData.sourceRows (1857 : Fin 2425) =
    MixedData.row1857 := by decide +kernel

theorem sourceRowsAt1858 : MixedData.sourceRows (1858 : Fin 2425) =
    MixedData.row1858 := by decide +kernel

theorem sourceRowsAt1859 : MixedData.sourceRows (1859 : Fin 2425) =
    MixedData.row1859 := by decide +kernel

theorem sourceRowsAt1860 : MixedData.sourceRows (1860 : Fin 2425) =
    MixedData.row1860 := by decide +kernel

theorem sourceRowsAt1861 : MixedData.sourceRows (1861 : Fin 2425) =
    MixedData.row1861 := by decide +kernel

theorem sourceRowsAt1862 : MixedData.sourceRows (1862 : Fin 2425) =
    MixedData.row1862 := by decide +kernel

theorem sourceRowsAt1863 : MixedData.sourceRows (1863 : Fin 2425) =
    MixedData.row1863 := by decide +kernel

theorem sourceRowsAt1864 : MixedData.sourceRows (1864 : Fin 2425) =
    MixedData.row1864 := by decide +kernel

theorem sourceRowsAt1865 : MixedData.sourceRows (1865 : Fin 2425) =
    MixedData.row1865 := by decide +kernel

theorem sourceRowsAt1866 : MixedData.sourceRows (1866 : Fin 2425) =
    MixedData.row1866 := by decide +kernel

theorem sourceRowsAt1867 : MixedData.sourceRows (1867 : Fin 2425) =
    MixedData.row1867 := by decide +kernel

theorem sourceRowsAt1868 : MixedData.sourceRows (1868 : Fin 2425) =
    MixedData.row1868 := by decide +kernel

theorem sourceRowsAt1869 : MixedData.sourceRows (1869 : Fin 2425) =
    MixedData.row1869 := by decide +kernel

theorem sourceRowsAt1870 : MixedData.sourceRows (1870 : Fin 2425) =
    MixedData.row1870 := by decide +kernel

theorem sourceRowsAt1871 : MixedData.sourceRows (1871 : Fin 2425) =
    MixedData.row1871 := by decide +kernel

theorem chunkSound116_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 116) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1856 ∨ k.val = 1857 ∨ k.val = 1858 ∨ k.val = 1859 ∨ k.val = 1860 ∨ k.val = 1861 ∨ k.val = 1862 ∨ k.val = 1863 ∨ k.val = 1864 ∨ k.val = 1865 ∨ k.val = 1866 ∨ k.val = 1867 ∨ k.val = 1868 ∨ k.val = 1869 ∨ k.val = 1870 ∨ k.val = 1871 := by omega
  rcases heq with h1856 | h1857 | h1858 | h1859 | h1860 | h1861 | h1862 | h1863 | h1864 | h1865 | h1866 | h1867 | h1868 | h1869 | h1870 | h1871
  · have he : k = (1856 : Fin 2425) := Fin.ext h1856
    subst k
    rw [sourceRowsAt1856]
    exact rowSound1856_e B hB hF
  · have he : k = (1857 : Fin 2425) := Fin.ext h1857
    subst k
    rw [sourceRowsAt1857]
    exact rowSound1857 B hB hF
  · have he : k = (1858 : Fin 2425) := Fin.ext h1858
    subst k
    rw [sourceRowsAt1858]
    exact rowSound1858_e B hB hF
  · have he : k = (1859 : Fin 2425) := Fin.ext h1859
    subst k
    rw [sourceRowsAt1859]
    exact rowSound1859_e B hB hF
  · have he : k = (1860 : Fin 2425) := Fin.ext h1860
    subst k
    rw [sourceRowsAt1860]
    exact rowSound1860 B hB hF
  · have he : k = (1861 : Fin 2425) := Fin.ext h1861
    subst k
    rw [sourceRowsAt1861]
    exact rowSound1861 B hB hF
  · have he : k = (1862 : Fin 2425) := Fin.ext h1862
    subst k
    rw [sourceRowsAt1862]
    exact rowSound1862 B hB hF
  · have he : k = (1863 : Fin 2425) := Fin.ext h1863
    subst k
    rw [sourceRowsAt1863]
    exact rowSound1863 B hB hF
  · have he : k = (1864 : Fin 2425) := Fin.ext h1864
    subst k
    rw [sourceRowsAt1864]
    exact rowSound1864_e B hB hF
  · have he : k = (1865 : Fin 2425) := Fin.ext h1865
    subst k
    rw [sourceRowsAt1865]
    exact rowSound1865 B hB hF
  · have he : k = (1866 : Fin 2425) := Fin.ext h1866
    subst k
    rw [sourceRowsAt1866]
    exact rowSound1866_e B hB hF
  · have he : k = (1867 : Fin 2425) := Fin.ext h1867
    subst k
    rw [sourceRowsAt1867]
    exact rowSound1867 B hB hF
  · have he : k = (1868 : Fin 2425) := Fin.ext h1868
    subst k
    rw [sourceRowsAt1868]
    exact rowSound1868 B hB hF
  · have he : k = (1869 : Fin 2425) := Fin.ext h1869
    subst k
    rw [sourceRowsAt1869]
    exact rowSound1869 B hB hF
  · have he : k = (1870 : Fin 2425) := Fin.ext h1870
    subst k
    rw [sourceRowsAt1870]
    exact rowSound1870 B hB hF
  · have he : k = (1871 : Fin 2425) := Fin.ext h1871
    subst k
    rw [sourceRowsAt1871]
    exact rowSound1871_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116_e_oai
