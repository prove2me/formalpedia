-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:39:43.147627+00:00
-- url     : https://prove2.me/submissions/00ec9b57-bb6e-475d-8fc2-569beab99ed7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1840_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1844_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1845_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1846_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1847_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1849_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1853_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1854_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1855_e

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

theorem canonical1803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1803 raw1803Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw1803 raw1803Labels = mixedMoment B raw1803step0 raw1803step0Labels := by
      have ha : raw1803step0 = (fun i j => raw1803 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1803step0 raw1803; decide +kernel
      have hl : raw1803step0Labels = raw1803Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1803 raw1803Labels permutation8 permutation4
    mixedMoment B raw1803step0 raw1803step0Labels = mixedMoment B raw1803step1 raw1803step1Labels := by
      have ha : raw1803step1 = raw1803step0 := by apply Matrix.ext; unfold raw1803step1 raw1803step0; decide +kernel
      have hl : raw1803step0Labels = labelEmbedding7 ∘ raw1803step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1803step0 raw1803step0Labels raw1803step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

theorem canonical1804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1804 raw1804Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw1804 raw1804Labels = mixedMoment B raw1804step0 raw1804step0Labels := by
      have ha : raw1804step0 = (fun i j => raw1804 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1804step0 raw1804; decide +kernel
      have hl : raw1804step0Labels = raw1804Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1804 raw1804Labels permutation8 permutation4
    _ = mixedMoment B node2112 node2112Labels := by rfl

theorem canonical1805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1805 raw1805Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw1805 raw1805Labels = mixedMoment B raw1805step0 raw1805step0Labels := by
      have ha : raw1805step0 = (fun i j => raw1805 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1805step0 raw1805; decide +kernel
      have hl : raw1805step0Labels = raw1805Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1805 raw1805Labels permutation8 permutation6
    mixedMoment B raw1805step0 raw1805step0Labels = mixedMoment B raw1805step1 raw1805step1Labels := by
      have ha : raw1805step1 = -raw1805step0 := by apply Matrix.ext; change ∀ i j, raw1805step1 i j = -(raw1805step0 i j); unfold raw1805step1 raw1805step0; decide +kernel
      have hl : raw1805step1Labels = raw1805step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1805step1 raw1805step1Labels = mixedMoment B raw1805step2 raw1805step2Labels := by
      have ha : raw1805step2 = raw1805step1 := by apply Matrix.ext; unfold raw1805step2 raw1805step1; decide +kernel
      have hl : raw1805step1Labels = labelEmbedding1 ∘ raw1805step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1805step1 raw1805step1Labels raw1805step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2287 node2287Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical165
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21144 raw21144Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw21144 raw21144Labels = mixedMoment B raw21144step0 raw21144step0Labels := by
      have hz : ∀ j, raw21144 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21144step0 = (fun i j => raw21144 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21144step0 raw21144; decide +kernel
      have hl : raw21144step0Labels = raw21144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21144 raw21144Labels permutation434 hz
    mixedMoment B raw21144step0 raw21144step0Labels = mixedMoment B raw21144step1 raw21144step1Labels := by
      have hz : ∀ j, raw21144step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21144step1 = (fun i j => raw21144step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21144step1 raw21144step0; decide +kernel
      have hl : raw21144step1Labels = raw21144step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21144step0 raw21144step0Labels permutation80 hz
    _ = mixedMoment B node4895 node4895Labels := by rfl

theorem canonical21158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21158 raw21158Labels = mixedMoment B node4374 node4374Labels := by
  calc
    mixedMoment B raw21158 raw21158Labels = mixedMoment B raw21158step0 raw21158step0Labels := by
      have hz : ∀ j, raw21158 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21158step0 = (fun i j => raw21158 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21158step0 raw21158; decide +kernel
      have hl : raw21158step0Labels = raw21158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21158 raw21158Labels permutation434 hz
    mixedMoment B raw21158step0 raw21158step0Labels = mixedMoment B raw21158step1 raw21158step1Labels := by
      have hz : ∀ j, raw21158step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21158step1 = (fun i j => raw21158step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21158step1 raw21158step0; decide +kernel
      have hl : raw21158step1Labels = raw21158step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21158step0 raw21158step0Labels permutation80 hz
    _ = mixedMoment B node4374 node4374Labels := by rfl

theorem canonical21196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21196 raw21196Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw21196 raw21196Labels = mixedMoment B raw21196step0 raw21196step0Labels := by
      have hz : ∀ j, raw21196 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21196step0 = (fun i j => raw21196 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21196step0 raw21196; decide +kernel
      have hl : raw21196step0Labels = raw21196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21196 raw21196Labels permutation434 hz
    mixedMoment B raw21196step0 raw21196step0Labels = mixedMoment B raw21196step1 raw21196step1Labels := by
      have hz : ∀ j, raw21196step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21196step1 = (fun i j => raw21196step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21196step1 raw21196step0; decide +kernel
      have hl : raw21196step1Labels = raw21196step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21196step0 raw21196step0Labels permutation80 hz
    mixedMoment B raw21196step1 raw21196step1Labels = mixedMoment B raw21196step2 raw21196step2Labels := by
      have ha : raw21196step2 = (fun i j => raw21196step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21196step2 raw21196step1; decide +kernel
      have hl : raw21196step2Labels = raw21196step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21196step1 raw21196step1Labels permutation8 permutation7
    mixedMoment B raw21196step2 raw21196step2Labels = mixedMoment B raw21196step3 raw21196step3Labels := by
      have ha : raw21196step3 = -raw21196step2 := by apply Matrix.ext; change ∀ i j, raw21196step3 i j = -(raw21196step2 i j); unfold raw21196step3 raw21196step2; decide +kernel
      have hl : raw21196step3Labels = raw21196step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21196step3 raw21196step3Labels = mixedMoment B raw21196step4 raw21196step4Labels := by
      have ha : raw21196step4 = raw21196step3 := by apply Matrix.ext; unfold raw21196step4 raw21196step3; decide +kernel
      have hl : raw21196step3Labels = labelEmbedding1 ∘ raw21196step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21196step3 raw21196step3Labels raw21196step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

theorem canonical21210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21210 raw21210Labels = mixedMoment B node1748 node1748Labels := by
  calc
    mixedMoment B raw21210 raw21210Labels = mixedMoment B raw21210step0 raw21210step0Labels := by
      have hz : ∀ j, raw21210 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21210step0 = (fun i j => raw21210 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21210step0 raw21210; decide +kernel
      have hl : raw21210step0Labels = raw21210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21210 raw21210Labels permutation434 hz
    mixedMoment B raw21210step0 raw21210step0Labels = mixedMoment B raw21210step1 raw21210step1Labels := by
      have hz : ∀ j, raw21210step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21210step1 = (fun i j => raw21210step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21210step1 raw21210step0; decide +kernel
      have hl : raw21210step1Labels = raw21210step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21210step0 raw21210step0Labels permutation80 hz
    mixedMoment B raw21210step1 raw21210step1Labels = mixedMoment B raw21210step2 raw21210step2Labels := by
      have ha : raw21210step2 = (fun i j => raw21210step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21210step2 raw21210step1; decide +kernel
      have hl : raw21210step2Labels = raw21210step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21210step1 raw21210step1Labels permutation8 permutation7
    mixedMoment B raw21210step2 raw21210step2Labels = mixedMoment B raw21210step3 raw21210step3Labels := by
      have ha : raw21210step3 = -raw21210step2 := by apply Matrix.ext; change ∀ i j, raw21210step3 i j = -(raw21210step2 i j); unfold raw21210step3 raw21210step2; decide +kernel
      have hl : raw21210step3Labels = raw21210step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21210step3 raw21210step3Labels = mixedMoment B raw21210step4 raw21210step4Labels := by
      have ha : raw21210step4 = raw21210step3 := by apply Matrix.ext; unfold raw21210step4 raw21210step3; decide +kernel
      have hl : raw21210step3Labels = labelEmbedding1 ∘ raw21210step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21210step3 raw21210step3Labels raw21210step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1748 node1748Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical179
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22988 raw22988Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw22988 raw22988Labels = mixedMoment B raw22988step0 raw22988step0Labels := by
      have hz : ∀ j, raw22988 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22988step0 = (fun i j => raw22988 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22988step0 raw22988; decide +kernel
      have hl : raw22988step0Labels = raw22988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22988 raw22988Labels permutation434 hz
    mixedMoment B raw22988step0 raw22988step0Labels = mixedMoment B raw22988step1 raw22988step1Labels := by
      have ha : raw22988step1 = (fun i j => raw22988step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22988step1 raw22988step0; decide +kernel
      have hl : raw22988step1Labels = raw22988step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22988step0 raw22988step0Labels permutation42 permutation7
    mixedMoment B raw22988step1 raw22988step1Labels = mixedMoment B raw22988step2 raw22988step2Labels := by
      have ha : raw22988step2 = -raw22988step1 := by apply Matrix.ext; change ∀ i j, raw22988step2 i j = -(raw22988step1 i j); unfold raw22988step2 raw22988step1; decide +kernel
      have hl : raw22988step2Labels = raw22988step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22988step2 raw22988step2Labels = mixedMoment B raw22988step3 raw22988step3Labels := by
      have ha : raw22988step3 = raw22988step2 := by apply Matrix.ext; unfold raw22988step3 raw22988step2; decide +kernel
      have hl : raw22988step2Labels = labelEmbedding1 ∘ raw22988step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22988step2 raw22988step2Labels raw22988step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical22989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22989 raw22989Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw22989 raw22989Labels = mixedMoment B raw22989step0 raw22989step0Labels := by
      have hz : ∀ j, raw22989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22989step0 = (fun i j => raw22989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22989step0 raw22989; decide +kernel
      have hl : raw22989step0Labels = raw22989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22989 raw22989Labels permutation346 hz
    mixedMoment B raw22989step0 raw22989step0Labels = mixedMoment B raw22989step1 raw22989step1Labels := by
      have ha : raw22989step1 = (fun i j => raw22989step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22989step1 raw22989step0; decide +kernel
      have hl : raw22989step1Labels = raw22989step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22989step0 raw22989step0Labels permutation42 permutation7
    mixedMoment B raw22989step1 raw22989step1Labels = mixedMoment B raw22989step2 raw22989step2Labels := by
      have ha : raw22989step2 = -raw22989step1 := by apply Matrix.ext; change ∀ i j, raw22989step2 i j = -(raw22989step1 i j); unfold raw22989step2 raw22989step1; decide +kernel
      have hl : raw22989step2Labels = raw22989step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22989step2 raw22989step2Labels = mixedMoment B raw22989step3 raw22989step3Labels := by
      have ha : raw22989step3 = raw22989step2 := by apply Matrix.ext; unfold raw22989step3 raw22989step2; decide +kernel
      have hl : raw22989step2Labels = labelEmbedding1 ∘ raw22989step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22989step2 raw22989step2Labels raw22989step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical22990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22990 raw22990Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw22990 raw22990Labels = mixedMoment B raw22990step0 raw22990step0Labels := by
      have hz : ∀ j, raw22990 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22990step0 = (fun i j => raw22990 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22990step0 raw22990; decide +kernel
      have hl : raw22990step0Labels = raw22990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22990 raw22990Labels permutation434 hz
    mixedMoment B raw22990step0 raw22990step0Labels = mixedMoment B raw22990step1 raw22990step1Labels := by
      have hz : ∀ j, raw22990step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22990step1 = (fun i j => raw22990step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22990step1 raw22990step0; decide +kernel
      have hl : raw22990step1Labels = raw22990step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22990step0 raw22990step0Labels permutation80 hz
    mixedMoment B raw22990step1 raw22990step1Labels = mixedMoment B raw22990step2 raw22990step2Labels := by
      have ha : raw22990step2 = (fun i j => raw22990step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22990step2 raw22990step1; decide +kernel
      have hl : raw22990step2Labels = raw22990step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22990step1 raw22990step1Labels permutation12 permutation7
    mixedMoment B raw22990step2 raw22990step2Labels = mixedMoment B raw22990step3 raw22990step3Labels := by
      have ha : raw22990step3 = -raw22990step2 := by apply Matrix.ext; change ∀ i j, raw22990step3 i j = -(raw22990step2 i j); unfold raw22990step3 raw22990step2; decide +kernel
      have hl : raw22990step3Labels = raw22990step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22990step3 raw22990step3Labels = mixedMoment B raw22990step4 raw22990step4Labels := by
      have ha : raw22990step4 = raw22990step3 := by apply Matrix.ext; unfold raw22990step4 raw22990step3; decide +kernel
      have hl : raw22990step3Labels = labelEmbedding1 ∘ raw22990step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22990step3 raw22990step3Labels raw22990step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2278 node2278Labels := by rfl

theorem canonical22991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22991 raw22991Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw22991 raw22991Labels = mixedMoment B raw22991step0 raw22991step0Labels := by
      have hz : ∀ j, raw22991 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22991step0 = (fun i j => raw22991 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22991step0 raw22991; decide +kernel
      have hl : raw22991step0Labels = raw22991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22991 raw22991Labels permutation434 hz
    mixedMoment B raw22991step0 raw22991step0Labels = mixedMoment B raw22991step1 raw22991step1Labels := by
      have hz : ∀ j, raw22991step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22991step1 = (fun i j => raw22991step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22991step1 raw22991step0; decide +kernel
      have hl : raw22991step1Labels = raw22991step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22991step0 raw22991step0Labels permutation80 hz
    mixedMoment B raw22991step1 raw22991step1Labels = mixedMoment B raw22991step2 raw22991step2Labels := by
      have ha : raw22991step2 = (fun i j => raw22991step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22991step2 raw22991step1; decide +kernel
      have hl : raw22991step2Labels = raw22991step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22991step1 raw22991step1Labels permutation12 permutation7
    mixedMoment B raw22991step2 raw22991step2Labels = mixedMoment B raw22991step3 raw22991step3Labels := by
      have ha : raw22991step3 = -raw22991step2 := by apply Matrix.ext; change ∀ i j, raw22991step3 i j = -(raw22991step2 i j); unfold raw22991step3 raw22991step2; decide +kernel
      have hl : raw22991step3Labels = raw22991step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22991step3 raw22991step3Labels = mixedMoment B raw22991step4 raw22991step4Labels := by
      have ha : raw22991step4 = raw22991step3 := by apply Matrix.ext; unfold raw22991step4 raw22991step3; decide +kernel
      have hl : raw22991step3Labels = labelEmbedding1 ∘ raw22991step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22991step3 raw22991step3Labels raw22991step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

theorem canonical22998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22998 raw22998Labels = mixedMoment B node1712 node1712Labels := by
  calc
    mixedMoment B raw22998 raw22998Labels = mixedMoment B raw22998step0 raw22998step0Labels := by
      have hz : ∀ j, raw22998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22998step0 = (fun i j => raw22998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22998step0 raw22998; decide +kernel
      have hl : raw22998step0Labels = raw22998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22998 raw22998Labels permutation434 hz
    mixedMoment B raw22998step0 raw22998step0Labels = mixedMoment B raw22998step1 raw22998step1Labels := by
      have ha : raw22998step1 = (fun i j => raw22998step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22998step1 raw22998step0; decide +kernel
      have hl : raw22998step1Labels = raw22998step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22998step0 raw22998step0Labels permutation42 permutation7
    mixedMoment B raw22998step1 raw22998step1Labels = mixedMoment B raw22998step2 raw22998step2Labels := by
      have ha : raw22998step2 = -raw22998step1 := by apply Matrix.ext; change ∀ i j, raw22998step2 i j = -(raw22998step1 i j); unfold raw22998step2 raw22998step1; decide +kernel
      have hl : raw22998step2Labels = raw22998step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22998step2 raw22998step2Labels = mixedMoment B raw22998step3 raw22998step3Labels := by
      have ha : raw22998step3 = raw22998step2 := by apply Matrix.ext; unfold raw22998step3 raw22998step2; decide +kernel
      have hl : raw22998step2Labels = labelEmbedding1 ∘ raw22998step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22998step2 raw22998step2Labels raw22998step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1712 node1712Labels := by rfl

theorem canonical23003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23003 raw23003Labels = mixedMoment B node1712 node1712Labels := by
  calc
    mixedMoment B raw23003 raw23003Labels = mixedMoment B raw23003step0 raw23003step0Labels := by
      have hz : ∀ j, raw23003 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23003step0 = (fun i j => raw23003 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23003step0 raw23003; decide +kernel
      have hl : raw23003step0Labels = raw23003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23003 raw23003Labels permutation346 hz
    mixedMoment B raw23003step0 raw23003step0Labels = mixedMoment B raw23003step1 raw23003step1Labels := by
      have ha : raw23003step1 = (fun i j => raw23003step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23003step1 raw23003step0; decide +kernel
      have hl : raw23003step1Labels = raw23003step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23003step0 raw23003step0Labels permutation42 permutation7
    mixedMoment B raw23003step1 raw23003step1Labels = mixedMoment B raw23003step2 raw23003step2Labels := by
      have ha : raw23003step2 = -raw23003step1 := by apply Matrix.ext; change ∀ i j, raw23003step2 i j = -(raw23003step1 i j); unfold raw23003step2 raw23003step1; decide +kernel
      have hl : raw23003step2Labels = raw23003step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23003step2 raw23003step2Labels = mixedMoment B raw23003step3 raw23003step3Labels := by
      have ha : raw23003step3 = raw23003step2 := by apply Matrix.ext; unfold raw23003step3 raw23003step2; decide +kernel
      have hl : raw23003step2Labels = labelEmbedding1 ∘ raw23003step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23003step2 raw23003step2Labels raw23003step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1712 node1712Labels := by rfl

theorem canonical23008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23008 raw23008Labels = mixedMoment B node1735 node1735Labels := by
  calc
    mixedMoment B raw23008 raw23008Labels = mixedMoment B raw23008step0 raw23008step0Labels := by
      have hz : ∀ j, raw23008 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23008step0 = (fun i j => raw23008 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23008step0 raw23008; decide +kernel
      have hl : raw23008step0Labels = raw23008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23008 raw23008Labels permutation434 hz
    mixedMoment B raw23008step0 raw23008step0Labels = mixedMoment B raw23008step1 raw23008step1Labels := by
      have hz : ∀ j, raw23008step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23008step1 = (fun i j => raw23008step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23008step1 raw23008step0; decide +kernel
      have hl : raw23008step1Labels = raw23008step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23008step0 raw23008step0Labels permutation80 hz
    mixedMoment B raw23008step1 raw23008step1Labels = mixedMoment B raw23008step2 raw23008step2Labels := by
      have ha : raw23008step2 = (fun i j => raw23008step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23008step2 raw23008step1; decide +kernel
      have hl : raw23008step2Labels = raw23008step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23008step1 raw23008step1Labels permutation12 permutation7
    mixedMoment B raw23008step2 raw23008step2Labels = mixedMoment B raw23008step3 raw23008step3Labels := by
      have ha : raw23008step3 = -raw23008step2 := by apply Matrix.ext; change ∀ i j, raw23008step3 i j = -(raw23008step2 i j); unfold raw23008step3 raw23008step2; decide +kernel
      have hl : raw23008step3Labels = raw23008step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23008step3 raw23008step3Labels = mixedMoment B raw23008step4 raw23008step4Labels := by
      have ha : raw23008step4 = raw23008step3 := by apply Matrix.ext; unfold raw23008step4 raw23008step3; decide +kernel
      have hl : raw23008step3Labels = labelEmbedding1 ∘ raw23008step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23008step3 raw23008step3Labels raw23008step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1735 node1735Labels := by rfl

theorem canonical23013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23013 raw23013Labels = mixedMoment B node1743 node1743Labels := by
  calc
    mixedMoment B raw23013 raw23013Labels = mixedMoment B raw23013step0 raw23013step0Labels := by
      have hz : ∀ j, raw23013 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23013step0 = (fun i j => raw23013 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23013step0 raw23013; decide +kernel
      have hl : raw23013step0Labels = raw23013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23013 raw23013Labels permutation434 hz
    mixedMoment B raw23013step0 raw23013step0Labels = mixedMoment B raw23013step1 raw23013step1Labels := by
      have hz : ∀ j, raw23013step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23013step1 = (fun i j => raw23013step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23013step1 raw23013step0; decide +kernel
      have hl : raw23013step1Labels = raw23013step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23013step0 raw23013step0Labels permutation80 hz
    mixedMoment B raw23013step1 raw23013step1Labels = mixedMoment B raw23013step2 raw23013step2Labels := by
      have ha : raw23013step2 = (fun i j => raw23013step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23013step2 raw23013step1; decide +kernel
      have hl : raw23013step2Labels = raw23013step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23013step1 raw23013step1Labels permutation12 permutation7
    mixedMoment B raw23013step2 raw23013step2Labels = mixedMoment B raw23013step3 raw23013step3Labels := by
      have ha : raw23013step3 = -raw23013step2 := by apply Matrix.ext; change ∀ i j, raw23013step3 i j = -(raw23013step2 i j); unfold raw23013step3 raw23013step2; decide +kernel
      have hl : raw23013step3Labels = raw23013step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23013step3 raw23013step3Labels = mixedMoment B raw23013step4 raw23013step4Labels := by
      have ha : raw23013step4 = raw23013step3 := by apply Matrix.ext; unfold raw23013step4 raw23013step3; decide +kernel
      have hl : raw23013step3Labels = labelEmbedding1 ∘ raw23013step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23013step3 raw23013step3Labels raw23013step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1743 node1743Labels := by rfl

theorem canonical23023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23023 raw23023Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw23023 raw23023Labels = mixedMoment B raw23023step0 raw23023step0Labels := by
      have hz : ∀ j, raw23023 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw23023step0 = (fun i j => raw23023 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw23023step0 raw23023; decide +kernel
      have hl : raw23023step0Labels = raw23023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23023 raw23023Labels permutation590 hz
    mixedMoment B raw23023step0 raw23023step0Labels = mixedMoment B raw23023step1 raw23023step1Labels := by
      have hz : ∀ j, raw23023step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw23023step1 = (fun i j => raw23023step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw23023step1 raw23023step0; decide +kernel
      have hl : raw23023step1Labels = raw23023step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23023step0 raw23023step0Labels permutation104 hz
    mixedMoment B raw23023step1 raw23023step1Labels = mixedMoment B raw23023step2 raw23023step2Labels := by
      have hz : ∀ j, raw23023step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw23023step2 = (fun i j => raw23023step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw23023step2 raw23023step1; decide +kernel
      have hl : raw23023step2Labels = raw23023step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23023step1 raw23023step1Labels permutation20 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical23028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23028 raw23028Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw23028 raw23028Labels = mixedMoment B raw23028step0 raw23028step0Labels := by
      have hz : ∀ j, raw23028 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23028step0 = (fun i j => raw23028 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23028step0 raw23028; decide +kernel
      have hl : raw23028step0Labels = raw23028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23028 raw23028Labels permutation434 hz
    mixedMoment B raw23028step0 raw23028step0Labels = mixedMoment B raw23028step1 raw23028step1Labels := by
      have hz : ∀ j, raw23028step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23028step1 = (fun i j => raw23028step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23028step1 raw23028step0; decide +kernel
      have hl : raw23028step1Labels = raw23028step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23028step0 raw23028step0Labels permutation80 hz
    mixedMoment B raw23028step1 raw23028step1Labels = mixedMoment B raw23028step2 raw23028step2Labels := by
      have ha : raw23028step2 = (fun i j => raw23028step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23028step2 raw23028step1; decide +kernel
      have hl : raw23028step2Labels = raw23028step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23028step1 raw23028step1Labels permutation9 permutation2
    _ = mixedMoment B node2115 node2115Labels := by rfl

theorem canonical23029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23029 raw23029Labels = mixedMoment B node946 node946Labels := by
  calc
    mixedMoment B raw23029 raw23029Labels = mixedMoment B raw23029step0 raw23029step0Labels := by
      have hz : ∀ j, raw23029 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23029step0 = (fun i j => raw23029 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23029step0 raw23029; decide +kernel
      have hl : raw23029step0Labels = raw23029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23029 raw23029Labels permutation434 hz
    mixedMoment B raw23029step0 raw23029step0Labels = mixedMoment B raw23029step1 raw23029step1Labels := by
      have ha : raw23029step1 = (fun i j => raw23029step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23029step1 raw23029step0; decide +kernel
      have hl : raw23029step1Labels = raw23029step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23029step0 raw23029step0Labels permutation33 permutation2
    _ = mixedMoment B node946 node946Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2316 raw2316Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw2316 raw2316Labels = mixedMoment B raw2316step0 raw2316step0Labels := by
      have ha : raw2316step0 = (fun i j => raw2316 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2316step0 raw2316; decide +kernel
      have hl : raw2316step0Labels = raw2316Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2316 raw2316Labels permutation8 permutation4
    mixedMoment B raw2316step0 raw2316step0Labels = mixedMoment B raw2316step1 raw2316step1Labels := by
      have ha : raw2316step1 = raw2316step0 := by apply Matrix.ext; unfold raw2316step1 raw2316step0; decide +kernel
      have hl : raw2316step0Labels = labelEmbedding7 ∘ raw2316step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2316step0 raw2316step0Labels raw2316step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

theorem canonical2317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2317 raw2317Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw2317 raw2317Labels = mixedMoment B raw2317step0 raw2317step0Labels := by
      have ha : raw2317step0 = (fun i j => raw2317 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2317step0 raw2317; decide +kernel
      have hl : raw2317step0Labels = raw2317Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2317 raw2317Labels permutation8 permutation4
    _ = mixedMoment B node2782 node2782Labels := by rfl

theorem canonical2318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2318 raw2318Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw2318 raw2318Labels = mixedMoment B raw2318step0 raw2318step0Labels := by
      have ha : raw2318step0 = (fun i j => raw2318 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2318step0 raw2318; decide +kernel
      have hl : raw2318step0Labels = raw2318Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2318 raw2318Labels permutation8 permutation6
    mixedMoment B raw2318step0 raw2318step0Labels = mixedMoment B raw2318step1 raw2318step1Labels := by
      have ha : raw2318step1 = -raw2318step0 := by apply Matrix.ext; change ∀ i j, raw2318step1 i j = -(raw2318step0 i j); unfold raw2318step1 raw2318step0; decide +kernel
      have hl : raw2318step1Labels = raw2318step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2318step1 raw2318step1Labels = mixedMoment B raw2318step2 raw2318step2Labels := by
      have ha : raw2318step2 = raw2318step1 := by apply Matrix.ext; unfold raw2318step2 raw2318step1; decide +kernel
      have hl : raw2318step1Labels = labelEmbedding1 ∘ raw2318step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2318step1 raw2318step1Labels raw2318step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3583 node3583Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical180
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23154 raw23154Labels = mixedMoment B node4369 node4369Labels := by
  calc
    mixedMoment B raw23154 raw23154Labels = mixedMoment B raw23154step0 raw23154step0Labels := by
      have hz : ∀ j, raw23154 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23154step0 = (fun i j => raw23154 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23154step0 raw23154; decide +kernel
      have hl : raw23154step0Labels = raw23154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23154 raw23154Labels permutation434 hz
    _ = mixedMoment B node4369 node4369Labels := by rfl

theorem canonical23158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23158 raw23158Labels = mixedMoment B node4369 node4369Labels := by
  calc
    mixedMoment B raw23158 raw23158Labels = mixedMoment B raw23158step0 raw23158step0Labels := by
      have hz : ∀ j, raw23158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23158step0 = (fun i j => raw23158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23158step0 raw23158; decide +kernel
      have hl : raw23158step0Labels = raw23158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23158 raw23158Labels permutation346 hz
    _ = mixedMoment B node4369 node4369Labels := by rfl

theorem canonical23162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23162 raw23162Labels = mixedMoment B node4374 node4374Labels := by
  calc
    mixedMoment B raw23162 raw23162Labels = mixedMoment B raw23162step0 raw23162step0Labels := by
      have hz : ∀ j, raw23162 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23162step0 = (fun i j => raw23162 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23162step0 raw23162; decide +kernel
      have hl : raw23162step0Labels = raw23162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23162 raw23162Labels permutation434 hz
    mixedMoment B raw23162step0 raw23162step0Labels = mixedMoment B raw23162step1 raw23162step1Labels := by
      have hz : ∀ j, raw23162step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23162step1 = (fun i j => raw23162step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23162step1 raw23162step0; decide +kernel
      have hl : raw23162step1Labels = raw23162step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23162step0 raw23162step0Labels permutation80 hz
    mixedMoment B raw23162step1 raw23162step1Labels = mixedMoment B raw23162step2 raw23162step2Labels := by
      have ha : raw23162step2 = (fun i j => raw23162step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23162step2 raw23162step1; decide +kernel
      have hl : raw23162step2Labels = raw23162step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23162step1 raw23162step1Labels permutation9 permutation2
    _ = mixedMoment B node4374 node4374Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical181
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23193 raw23193Labels = mixedMoment B node1721 node1721Labels := by
  calc
    mixedMoment B raw23193 raw23193Labels = mixedMoment B raw23193step0 raw23193step0Labels := by
      have hz : ∀ j, raw23193 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23193step0 = (fun i j => raw23193 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23193step0 raw23193; decide +kernel
      have hl : raw23193step0Labels = raw23193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23193 raw23193Labels permutation434 hz
    mixedMoment B raw23193step0 raw23193step0Labels = mixedMoment B raw23193step1 raw23193step1Labels := by
      have ha : raw23193step1 = (fun i j => raw23193step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23193step1 raw23193step0; decide +kernel
      have hl : raw23193step1Labels = raw23193step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23193step0 raw23193step0Labels permutation38 permutation7
    mixedMoment B raw23193step1 raw23193step1Labels = mixedMoment B raw23193step2 raw23193step2Labels := by
      have ha : raw23193step2 = -raw23193step1 := by apply Matrix.ext; change ∀ i j, raw23193step2 i j = -(raw23193step1 i j); unfold raw23193step2 raw23193step1; decide +kernel
      have hl : raw23193step2Labels = raw23193step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23193step2 raw23193step2Labels = mixedMoment B raw23193step3 raw23193step3Labels := by
      have ha : raw23193step3 = raw23193step2 := by apply Matrix.ext; unfold raw23193step3 raw23193step2; decide +kernel
      have hl : raw23193step2Labels = labelEmbedding1 ∘ raw23193step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23193step2 raw23193step2Labels raw23193step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1721 node1721Labels := by rfl

theorem canonical23197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23197 raw23197Labels = mixedMoment B node1721 node1721Labels := by
  calc
    mixedMoment B raw23197 raw23197Labels = mixedMoment B raw23197step0 raw23197step0Labels := by
      have hz : ∀ j, raw23197 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23197step0 = (fun i j => raw23197 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23197step0 raw23197; decide +kernel
      have hl : raw23197step0Labels = raw23197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23197 raw23197Labels permutation346 hz
    mixedMoment B raw23197step0 raw23197step0Labels = mixedMoment B raw23197step1 raw23197step1Labels := by
      have ha : raw23197step1 = (fun i j => raw23197step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23197step1 raw23197step0; decide +kernel
      have hl : raw23197step1Labels = raw23197step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23197step0 raw23197step0Labels permutation38 permutation7
    mixedMoment B raw23197step1 raw23197step1Labels = mixedMoment B raw23197step2 raw23197step2Labels := by
      have ha : raw23197step2 = -raw23197step1 := by apply Matrix.ext; change ∀ i j, raw23197step2 i j = -(raw23197step1 i j); unfold raw23197step2 raw23197step1; decide +kernel
      have hl : raw23197step2Labels = raw23197step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23197step2 raw23197step2Labels = mixedMoment B raw23197step3 raw23197step3Labels := by
      have ha : raw23197step3 = raw23197step2 := by apply Matrix.ext; unfold raw23197step3 raw23197step2; decide +kernel
      have hl : raw23197step2Labels = labelEmbedding1 ∘ raw23197step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23197step2 raw23197step2Labels raw23197step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1721 node1721Labels := by rfl

theorem canonical23201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23201 raw23201Labels = mixedMoment B node1748 node1748Labels := by
  calc
    mixedMoment B raw23201 raw23201Labels = mixedMoment B raw23201step0 raw23201step0Labels := by
      have hz : ∀ j, raw23201 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23201step0 = (fun i j => raw23201 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23201step0 raw23201; decide +kernel
      have hl : raw23201step0Labels = raw23201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23201 raw23201Labels permutation434 hz
    mixedMoment B raw23201step0 raw23201step0Labels = mixedMoment B raw23201step1 raw23201step1Labels := by
      have hz : ∀ j, raw23201step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23201step1 = (fun i j => raw23201step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23201step1 raw23201step0; decide +kernel
      have hl : raw23201step1Labels = raw23201step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23201step0 raw23201step0Labels permutation80 hz
    mixedMoment B raw23201step1 raw23201step1Labels = mixedMoment B raw23201step2 raw23201step2Labels := by
      have ha : raw23201step2 = (fun i j => raw23201step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23201step2 raw23201step1; decide +kernel
      have hl : raw23201step2Labels = raw23201step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23201step1 raw23201step1Labels permutation9 permutation7
    mixedMoment B raw23201step2 raw23201step2Labels = mixedMoment B raw23201step3 raw23201step3Labels := by
      have ha : raw23201step3 = -raw23201step2 := by apply Matrix.ext; change ∀ i j, raw23201step3 i j = -(raw23201step2 i j); unfold raw23201step3 raw23201step2; decide +kernel
      have hl : raw23201step3Labels = raw23201step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23201step3 raw23201step3Labels = mixedMoment B raw23201step4 raw23201step4Labels := by
      have ha : raw23201step4 = raw23201step3 := by apply Matrix.ext; unfold raw23201step4 raw23201step3; decide +kernel
      have hl : raw23201step3Labels = labelEmbedding1 ∘ raw23201step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23201step3 raw23201step3Labels raw23201step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1748 node1748Labels := by rfl

theorem canonical23213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23213 raw23213Labels = mixedMoment B node947 node947Labels := by
  calc
    mixedMoment B raw23213 raw23213Labels = mixedMoment B raw23213step0 raw23213step0Labels := by
      have hz : ∀ j, raw23213 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23213step0 = (fun i j => raw23213 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23213step0 raw23213; decide +kernel
      have hl : raw23213step0Labels = raw23213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23213 raw23213Labels permutation434 hz
    _ = mixedMoment B node947 node947Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical214
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27395 raw27395Labels = mixedMoment B node1832 node1832Labels := by
  calc
    mixedMoment B raw27395 raw27395Labels = mixedMoment B raw27395step0 raw27395step0Labels := by
      have hz : ∀ j, raw27395 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27395step0 = (fun i j => raw27395 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27395step0 raw27395; decide +kernel
      have hl : raw27395step0Labels = raw27395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27395 raw27395Labels permutation434 hz
    mixedMoment B raw27395step0 raw27395step0Labels = mixedMoment B raw27395step1 raw27395step1Labels := by
      have hz : ∀ j, raw27395step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27395step1 = (fun i j => raw27395step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27395step1 raw27395step0; decide +kernel
      have hl : raw27395step1Labels = raw27395step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27395step0 raw27395step0Labels permutation80 hz
    _ = mixedMoment B node1832 node1832Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical242
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30980 raw30980Labels = mixedMoment B node2771 node2771Labels := by
  calc
    mixedMoment B raw30980 raw30980Labels = mixedMoment B raw30980step0 raw30980step0Labels := by
      have hz : ∀ j, raw30980 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30980step0 = (fun i j => raw30980 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30980step0 raw30980; decide +kernel
      have hl : raw30980step0Labels = raw30980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30980 raw30980Labels permutation434 hz
    mixedMoment B raw30980step0 raw30980step0Labels = mixedMoment B raw30980step1 raw30980step1Labels := by
      have hz : ∀ j, raw30980step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30980step1 = (fun i j => raw30980step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30980step1 raw30980step0; decide +kernel
      have hl : raw30980step1Labels = raw30980step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30980step0 raw30980step0Labels permutation80 hz
    mixedMoment B raw30980step1 raw30980step1Labels = mixedMoment B raw30980step2 raw30980step2Labels := by
      have ha : raw30980step2 = (fun i j => raw30980step1 (permutation16 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30980step2 raw30980step1; decide +kernel
      have hl : raw30980step2Labels = raw30980step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30980step1 raw30980step1Labels permutation16 permutation5
    mixedMoment B raw30980step2 raw30980step2Labels = mixedMoment B raw30980step3 raw30980step3Labels := by
      have ha : raw30980step3 = -raw30980step2 := by apply Matrix.ext; change ∀ i j, raw30980step3 i j = -(raw30980step2 i j); unfold raw30980step3 raw30980step2; decide +kernel
      have hl : raw30980step3Labels = raw30980step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30980step3 raw30980step3Labels = mixedMoment B raw30980step4 raw30980step4Labels := by
      have ha : raw30980step4 = raw30980step3 := by apply Matrix.ext; unfold raw30980step4 raw30980step3; decide +kernel
      have hl : raw30980step3Labels = labelEmbedding1 ∘ raw30980step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30980step3 raw30980step3Labels raw30980step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2771 node2771Labels := by rfl

theorem canonical30981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30981 raw30981Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw30981 raw30981Labels = mixedMoment B raw30981step0 raw30981step0Labels := by
      have hz : ∀ j, raw30981 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30981step0 = (fun i j => raw30981 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30981step0 raw30981; decide +kernel
      have hl : raw30981step0Labels = raw30981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30981 raw30981Labels permutation434 hz
    mixedMoment B raw30981step0 raw30981step0Labels = mixedMoment B raw30981step1 raw30981step1Labels := by
      have ha : raw30981step1 = (fun i j => raw30981step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30981step1 raw30981step0; decide +kernel
      have hl : raw30981step1Labels = raw30981step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30981step0 raw30981step0Labels permutation42 permutation7
    mixedMoment B raw30981step1 raw30981step1Labels = mixedMoment B raw30981step2 raw30981step2Labels := by
      have ha : raw30981step2 = -raw30981step1 := by apply Matrix.ext; change ∀ i j, raw30981step2 i j = -(raw30981step1 i j); unfold raw30981step2 raw30981step1; decide +kernel
      have hl : raw30981step2Labels = raw30981step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30981step2 raw30981step2Labels = mixedMoment B raw30981step3 raw30981step3Labels := by
      have ha : raw30981step3 = raw30981step2 := by apply Matrix.ext; unfold raw30981step3 raw30981step2; decide +kernel
      have hl : raw30981step2Labels = labelEmbedding1 ∘ raw30981step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30981step2 raw30981step2Labels raw30981step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2729 node2729Labels := by rfl

theorem canonical30982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30982 raw30982Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw30982 raw30982Labels = mixedMoment B raw30982step0 raw30982step0Labels := by
      have hz : ∀ j, raw30982 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30982step0 = (fun i j => raw30982 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30982step0 raw30982; decide +kernel
      have hl : raw30982step0Labels = raw30982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30982 raw30982Labels permutation346 hz
    mixedMoment B raw30982step0 raw30982step0Labels = mixedMoment B raw30982step1 raw30982step1Labels := by
      have ha : raw30982step1 = (fun i j => raw30982step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30982step1 raw30982step0; decide +kernel
      have hl : raw30982step1Labels = raw30982step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30982step0 raw30982step0Labels permutation42 permutation7
    mixedMoment B raw30982step1 raw30982step1Labels = mixedMoment B raw30982step2 raw30982step2Labels := by
      have ha : raw30982step2 = -raw30982step1 := by apply Matrix.ext; change ∀ i j, raw30982step2 i j = -(raw30982step1 i j); unfold raw30982step2 raw30982step1; decide +kernel
      have hl : raw30982step2Labels = raw30982step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30982step2 raw30982step2Labels = mixedMoment B raw30982step3 raw30982step3Labels := by
      have ha : raw30982step3 = raw30982step2 := by apply Matrix.ext; unfold raw30982step3 raw30982step2; decide +kernel
      have hl : raw30982step2Labels = labelEmbedding1 ∘ raw30982step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30982step2 raw30982step2Labels raw30982step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2729 node2729Labels := by rfl

theorem canonical30983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30983 raw30983Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw30983 raw30983Labels = mixedMoment B raw30983step0 raw30983step0Labels := by
      have hz : ∀ j, raw30983 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30983step0 = (fun i j => raw30983 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30983step0 raw30983; decide +kernel
      have hl : raw30983step0Labels = raw30983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30983 raw30983Labels permutation434 hz
    mixedMoment B raw30983step0 raw30983step0Labels = mixedMoment B raw30983step1 raw30983step1Labels := by
      have hz : ∀ j, raw30983step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30983step1 = (fun i j => raw30983step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30983step1 raw30983step0; decide +kernel
      have hl : raw30983step1Labels = raw30983step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30983step0 raw30983step0Labels permutation80 hz
    mixedMoment B raw30983step1 raw30983step1Labels = mixedMoment B raw30983step2 raw30983step2Labels := by
      have ha : raw30983step2 = (fun i j => raw30983step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30983step2 raw30983step1; decide +kernel
      have hl : raw30983step2Labels = raw30983step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30983step1 raw30983step1Labels permutation12 permutation7
    mixedMoment B raw30983step2 raw30983step2Labels = mixedMoment B raw30983step3 raw30983step3Labels := by
      have ha : raw30983step3 = -raw30983step2 := by apply Matrix.ext; change ∀ i j, raw30983step3 i j = -(raw30983step2 i j); unfold raw30983step3 raw30983step2; decide +kernel
      have hl : raw30983step3Labels = raw30983step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30983step3 raw30983step3Labels = mixedMoment B raw30983step4 raw30983step4Labels := by
      have ha : raw30983step4 = raw30983step3 := by apply Matrix.ext; unfold raw30983step4 raw30983step3; decide +kernel
      have hl : raw30983step3Labels = labelEmbedding1 ∘ raw30983step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30983step3 raw30983step3Labels raw30983step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2774 node2774Labels := by rfl

theorem canonical30984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30984 raw30984Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw30984 raw30984Labels = mixedMoment B raw30984step0 raw30984step0Labels := by
      have hz : ∀ j, raw30984 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30984step0 = (fun i j => raw30984 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30984step0 raw30984; decide +kernel
      have hl : raw30984step0Labels = raw30984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30984 raw30984Labels permutation434 hz
    mixedMoment B raw30984step0 raw30984step0Labels = mixedMoment B raw30984step1 raw30984step1Labels := by
      have hz : ∀ j, raw30984step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30984step1 = (fun i j => raw30984step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30984step1 raw30984step0; decide +kernel
      have hl : raw30984step1Labels = raw30984step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30984step0 raw30984step0Labels permutation80 hz
    mixedMoment B raw30984step1 raw30984step1Labels = mixedMoment B raw30984step2 raw30984step2Labels := by
      have ha : raw30984step2 = (fun i j => raw30984step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30984step2 raw30984step1; decide +kernel
      have hl : raw30984step2Labels = raw30984step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30984step1 raw30984step1Labels permutation12 permutation7
    mixedMoment B raw30984step2 raw30984step2Labels = mixedMoment B raw30984step3 raw30984step3Labels := by
      have ha : raw30984step3 = -raw30984step2 := by apply Matrix.ext; change ∀ i j, raw30984step3 i j = -(raw30984step2 i j); unfold raw30984step3 raw30984step2; decide +kernel
      have hl : raw30984step3Labels = raw30984step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30984step3 raw30984step3Labels = mixedMoment B raw30984step4 raw30984step4Labels := by
      have ha : raw30984step4 = raw30984step3 := by apply Matrix.ext; unfold raw30984step4 raw30984step3; decide +kernel
      have hl : raw30984step3Labels = labelEmbedding1 ∘ raw30984step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30984step3 raw30984step3Labels raw30984step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical30985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30985 raw30985Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw30985 raw30985Labels = mixedMoment B raw30985step0 raw30985step0Labels := by
      have hz : ∀ j, raw30985 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30985step0 = (fun i j => raw30985 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30985step0 raw30985; decide +kernel
      have hl : raw30985step0Labels = raw30985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30985 raw30985Labels permutation434 hz
    mixedMoment B raw30985step0 raw30985step0Labels = mixedMoment B raw30985step1 raw30985step1Labels := by
      have hz : ∀ j, raw30985step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30985step1 = (fun i j => raw30985step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30985step1 raw30985step0; decide +kernel
      have hl : raw30985step1Labels = raw30985step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30985step0 raw30985step0Labels permutation80 hz
    mixedMoment B raw30985step1 raw30985step1Labels = mixedMoment B raw30985step2 raw30985step2Labels := by
      have ha : raw30985step2 = (fun i j => raw30985step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30985step2 raw30985step1; decide +kernel
      have hl : raw30985step2Labels = raw30985step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30985step1 raw30985step1Labels permutation12 permutation7
    mixedMoment B raw30985step2 raw30985step2Labels = mixedMoment B raw30985step3 raw30985step3Labels := by
      have ha : raw30985step3 = -raw30985step2 := by apply Matrix.ext; change ∀ i j, raw30985step3 i j = -(raw30985step2 i j); unfold raw30985step3 raw30985step2; decide +kernel
      have hl : raw30985step3Labels = raw30985step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30985step3 raw30985step3Labels = mixedMoment B raw30985step4 raw30985step4Labels := by
      have ha : raw30985step4 = raw30985step3 := by apply Matrix.ext; unfold raw30985step4 raw30985step3; decide +kernel
      have hl : raw30985step3Labels = labelEmbedding1 ∘ raw30985step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30985step3 raw30985step3Labels raw30985step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1738 node1738Labels := by rfl

theorem canonical30986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30986 raw30986Labels = mixedMoment B node2249 node2249Labels := by
  calc
    mixedMoment B raw30986 raw30986Labels = mixedMoment B raw30986step0 raw30986step0Labels := by
      have hz : ∀ j, raw30986 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30986step0 = (fun i j => raw30986 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30986step0 raw30986; decide +kernel
      have hl : raw30986step0Labels = raw30986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30986 raw30986Labels permutation434 hz
    mixedMoment B raw30986step0 raw30986step0Labels = mixedMoment B raw30986step1 raw30986step1Labels := by
      have ha : raw30986step1 = (fun i j => raw30986step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30986step1 raw30986step0; decide +kernel
      have hl : raw30986step1Labels = raw30986step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30986step0 raw30986step0Labels permutation42 permutation7
    mixedMoment B raw30986step1 raw30986step1Labels = mixedMoment B raw30986step2 raw30986step2Labels := by
      have ha : raw30986step2 = -raw30986step1 := by apply Matrix.ext; change ∀ i j, raw30986step2 i j = -(raw30986step1 i j); unfold raw30986step2 raw30986step1; decide +kernel
      have hl : raw30986step2Labels = raw30986step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30986step2 raw30986step2Labels = mixedMoment B raw30986step3 raw30986step3Labels := by
      have ha : raw30986step3 = raw30986step2 := by apply Matrix.ext; unfold raw30986step3 raw30986step2; decide +kernel
      have hl : raw30986step2Labels = labelEmbedding1 ∘ raw30986step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30986step2 raw30986step2Labels raw30986step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2249 node2249Labels := by rfl

theorem canonical30987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30987 raw30987Labels = mixedMoment B node2194 node2194Labels := by
  calc
    mixedMoment B raw30987 raw30987Labels = mixedMoment B raw30987step0 raw30987step0Labels := by
      have ha : raw30987step0 = (fun i j => raw30987 (permutation210 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30987step0 raw30987; decide +kernel
      have hl : raw30987step0Labels = raw30987Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30987 raw30987Labels permutation210 permutation7
    mixedMoment B raw30987step0 raw30987step0Labels = mixedMoment B raw30987step1 raw30987step1Labels := by
      have ha : raw30987step1 = -raw30987step0 := by apply Matrix.ext; change ∀ i j, raw30987step1 i j = -(raw30987step0 i j); unfold raw30987step1 raw30987step0; decide +kernel
      have hl : raw30987step1Labels = raw30987step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30987step1 raw30987step1Labels = mixedMoment B raw30987step2 raw30987step2Labels := by
      have ha : raw30987step2 = raw30987step1 := by apply Matrix.ext; unfold raw30987step2 raw30987step1; decide +kernel
      have hl : raw30987step1Labels = labelEmbedding1 ∘ raw30987step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30987step1 raw30987step1Labels raw30987step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2194 node2194Labels := by rfl

theorem canonical30988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30988 raw30988Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw30988 raw30988Labels = mixedMoment B raw30988step0 raw30988step0Labels := by
      have hz : ∀ j, raw30988 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30988step0 = (fun i j => raw30988 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30988step0 raw30988; decide +kernel
      have hl : raw30988step0Labels = raw30988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30988 raw30988Labels permutation434 hz
    mixedMoment B raw30988step0 raw30988step0Labels = mixedMoment B raw30988step1 raw30988step1Labels := by
      have ha : raw30988step1 = (fun i j => raw30988step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30988step1 raw30988step0; decide +kernel
      have hl : raw30988step1Labels = raw30988step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30988step0 raw30988step0Labels permutation42 permutation7
    mixedMoment B raw30988step1 raw30988step1Labels = mixedMoment B raw30988step2 raw30988step2Labels := by
      have ha : raw30988step2 = -raw30988step1 := by apply Matrix.ext; change ∀ i j, raw30988step2 i j = -(raw30988step1 i j); unfold raw30988step2 raw30988step1; decide +kernel
      have hl : raw30988step2Labels = raw30988step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30988step2 raw30988step2Labels = mixedMoment B raw30988step3 raw30988step3Labels := by
      have ha : raw30988step3 = raw30988step2 := by apply Matrix.ext; unfold raw30988step3 raw30988step2; decide +kernel
      have hl : raw30988step2Labels = labelEmbedding1 ∘ raw30988step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30988step2 raw30988step2Labels raw30988step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2251 node2251Labels := by rfl

theorem canonical30989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30989 raw30989Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw30989 raw30989Labels = mixedMoment B raw30989step0 raw30989step0Labels := by
      have hz : ∀ j, raw30989 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30989step0 = (fun i j => raw30989 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30989step0 raw30989; decide +kernel
      have hl : raw30989step0Labels = raw30989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30989 raw30989Labels permutation434 hz
    mixedMoment B raw30989step0 raw30989step0Labels = mixedMoment B raw30989step1 raw30989step1Labels := by
      have ha : raw30989step1 = (fun i j => raw30989step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30989step1 raw30989step0; decide +kernel
      have hl : raw30989step1Labels = raw30989step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30989step0 raw30989step0Labels permutation42 permutation7
    mixedMoment B raw30989step1 raw30989step1Labels = mixedMoment B raw30989step2 raw30989step2Labels := by
      have ha : raw30989step2 = -raw30989step1 := by apply Matrix.ext; change ∀ i j, raw30989step2 i j = -(raw30989step1 i j); unfold raw30989step2 raw30989step1; decide +kernel
      have hl : raw30989step2Labels = raw30989step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30989step2 raw30989step2Labels = mixedMoment B raw30989step3 raw30989step3Labels := by
      have ha : raw30989step3 = raw30989step2 := by apply Matrix.ext; unfold raw30989step3 raw30989step2; decide +kernel
      have hl : raw30989step2Labels = labelEmbedding1 ∘ raw30989step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30989step2 raw30989step2Labels raw30989step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

theorem canonical30990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30990 raw30990Labels = mixedMoment B node2249 node2249Labels := by
  calc
    mixedMoment B raw30990 raw30990Labels = mixedMoment B raw30990step0 raw30990step0Labels := by
      have hz : ∀ j, raw30990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30990step0 = (fun i j => raw30990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30990step0 raw30990; decide +kernel
      have hl : raw30990step0Labels = raw30990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30990 raw30990Labels permutation346 hz
    mixedMoment B raw30990step0 raw30990step0Labels = mixedMoment B raw30990step1 raw30990step1Labels := by
      have ha : raw30990step1 = (fun i j => raw30990step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30990step1 raw30990step0; decide +kernel
      have hl : raw30990step1Labels = raw30990step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30990step0 raw30990step0Labels permutation42 permutation7
    mixedMoment B raw30990step1 raw30990step1Labels = mixedMoment B raw30990step2 raw30990step2Labels := by
      have ha : raw30990step2 = -raw30990step1 := by apply Matrix.ext; change ∀ i j, raw30990step2 i j = -(raw30990step1 i j); unfold raw30990step2 raw30990step1; decide +kernel
      have hl : raw30990step2Labels = raw30990step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30990step2 raw30990step2Labels = mixedMoment B raw30990step3 raw30990step3Labels := by
      have ha : raw30990step3 = raw30990step2 := by apply Matrix.ext; unfold raw30990step3 raw30990step2; decide +kernel
      have hl : raw30990step2Labels = labelEmbedding1 ∘ raw30990step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30990step2 raw30990step2Labels raw30990step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2249 node2249Labels := by rfl

theorem canonical30991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30991 raw30991Labels = mixedMoment B node2194 node2194Labels := by
  calc
    mixedMoment B raw30991 raw30991Labels = mixedMoment B raw30991step0 raw30991step0Labels := by
      have ha : raw30991step0 = (fun i j => raw30991 (permutation186 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30991step0 raw30991; decide +kernel
      have hl : raw30991step0Labels = raw30991Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30991 raw30991Labels permutation186 permutation7
    mixedMoment B raw30991step0 raw30991step0Labels = mixedMoment B raw30991step1 raw30991step1Labels := by
      have ha : raw30991step1 = -raw30991step0 := by apply Matrix.ext; change ∀ i j, raw30991step1 i j = -(raw30991step0 i j); unfold raw30991step1 raw30991step0; decide +kernel
      have hl : raw30991step1Labels = raw30991step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30991step1 raw30991step1Labels = mixedMoment B raw30991step2 raw30991step2Labels := by
      have ha : raw30991step2 = raw30991step1 := by apply Matrix.ext; unfold raw30991step2 raw30991step1; decide +kernel
      have hl : raw30991step1Labels = labelEmbedding1 ∘ raw30991step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30991step1 raw30991step1Labels raw30991step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2194 node2194Labels := by rfl

theorem canonical30992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30992 raw30992Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw30992 raw30992Labels = mixedMoment B raw30992step0 raw30992step0Labels := by
      have hz : ∀ j, raw30992 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30992step0 = (fun i j => raw30992 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30992step0 raw30992; decide +kernel
      have hl : raw30992step0Labels = raw30992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30992 raw30992Labels permutation346 hz
    mixedMoment B raw30992step0 raw30992step0Labels = mixedMoment B raw30992step1 raw30992step1Labels := by
      have ha : raw30992step1 = (fun i j => raw30992step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30992step1 raw30992step0; decide +kernel
      have hl : raw30992step1Labels = raw30992step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30992step0 raw30992step0Labels permutation42 permutation7
    mixedMoment B raw30992step1 raw30992step1Labels = mixedMoment B raw30992step2 raw30992step2Labels := by
      have ha : raw30992step2 = -raw30992step1 := by apply Matrix.ext; change ∀ i j, raw30992step2 i j = -(raw30992step1 i j); unfold raw30992step2 raw30992step1; decide +kernel
      have hl : raw30992step2Labels = raw30992step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30992step2 raw30992step2Labels = mixedMoment B raw30992step3 raw30992step3Labels := by
      have ha : raw30992step3 = raw30992step2 := by apply Matrix.ext; unfold raw30992step3 raw30992step2; decide +kernel
      have hl : raw30992step2Labels = labelEmbedding1 ∘ raw30992step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30992step2 raw30992step2Labels raw30992step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2251 node2251Labels := by rfl

theorem canonical30993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30993 raw30993Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw30993 raw30993Labels = mixedMoment B raw30993step0 raw30993step0Labels := by
      have hz : ∀ j, raw30993 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30993step0 = (fun i j => raw30993 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30993step0 raw30993; decide +kernel
      have hl : raw30993step0Labels = raw30993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30993 raw30993Labels permutation346 hz
    mixedMoment B raw30993step0 raw30993step0Labels = mixedMoment B raw30993step1 raw30993step1Labels := by
      have ha : raw30993step1 = (fun i j => raw30993step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30993step1 raw30993step0; decide +kernel
      have hl : raw30993step1Labels = raw30993step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30993step0 raw30993step0Labels permutation42 permutation7
    mixedMoment B raw30993step1 raw30993step1Labels = mixedMoment B raw30993step2 raw30993step2Labels := by
      have ha : raw30993step2 = -raw30993step1 := by apply Matrix.ext; change ∀ i j, raw30993step2 i j = -(raw30993step1 i j); unfold raw30993step2 raw30993step1; decide +kernel
      have hl : raw30993step2Labels = raw30993step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30993step2 raw30993step2Labels = mixedMoment B raw30993step3 raw30993step3Labels := by
      have ha : raw30993step3 = raw30993step2 := by apply Matrix.ext; unfold raw30993step3 raw30993step2; decide +kernel
      have hl : raw30993step2Labels = labelEmbedding1 ∘ raw30993step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30993step2 raw30993step2Labels raw30993step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

theorem canonical30994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30994 raw30994Labels = mixedMoment B node2273 node2273Labels := by
  calc
    mixedMoment B raw30994 raw30994Labels = mixedMoment B raw30994step0 raw30994step0Labels := by
      have hz : ∀ j, raw30994 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30994step0 = (fun i j => raw30994 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30994step0 raw30994; decide +kernel
      have hl : raw30994step0Labels = raw30994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30994 raw30994Labels permutation434 hz
    mixedMoment B raw30994step0 raw30994step0Labels = mixedMoment B raw30994step1 raw30994step1Labels := by
      have hz : ∀ j, raw30994step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30994step1 = (fun i j => raw30994step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30994step1 raw30994step0; decide +kernel
      have hl : raw30994step1Labels = raw30994step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30994step0 raw30994step0Labels permutation80 hz
    mixedMoment B raw30994step1 raw30994step1Labels = mixedMoment B raw30994step2 raw30994step2Labels := by
      have ha : raw30994step2 = (fun i j => raw30994step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30994step2 raw30994step1; decide +kernel
      have hl : raw30994step2Labels = raw30994step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30994step1 raw30994step1Labels permutation12 permutation7
    mixedMoment B raw30994step2 raw30994step2Labels = mixedMoment B raw30994step3 raw30994step3Labels := by
      have ha : raw30994step3 = -raw30994step2 := by apply Matrix.ext; change ∀ i j, raw30994step3 i j = -(raw30994step2 i j); unfold raw30994step3 raw30994step2; decide +kernel
      have hl : raw30994step3Labels = raw30994step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30994step3 raw30994step3Labels = mixedMoment B raw30994step4 raw30994step4Labels := by
      have ha : raw30994step4 = raw30994step3 := by apply Matrix.ext; unfold raw30994step4 raw30994step3; decide +kernel
      have hl : raw30994step3Labels = labelEmbedding1 ∘ raw30994step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30994step3 raw30994step3Labels raw30994step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2273 node2273Labels := by rfl

theorem canonical30995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30995 raw30995Labels = mixedMoment B node2212 node2212Labels := by
  calc
    mixedMoment B raw30995 raw30995Labels = mixedMoment B raw30995step0 raw30995step0Labels := by
      have hz : ∀ j, raw30995 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30995step0 = (fun i j => raw30995 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30995step0 raw30995; decide +kernel
      have hl : raw30995step0Labels = raw30995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30995 raw30995Labels permutation434 hz
    mixedMoment B raw30995step0 raw30995step0Labels = mixedMoment B raw30995step1 raw30995step1Labels := by
      have ha : raw30995step1 = (fun i j => raw30995step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30995step1 raw30995step0; decide +kernel
      have hl : raw30995step1Labels = raw30995step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30995step0 raw30995step0Labels permutation42 permutation7
    mixedMoment B raw30995step1 raw30995step1Labels = mixedMoment B raw30995step2 raw30995step2Labels := by
      have ha : raw30995step2 = -raw30995step1 := by apply Matrix.ext; change ∀ i j, raw30995step2 i j = -(raw30995step1 i j); unfold raw30995step2 raw30995step1; decide +kernel
      have hl : raw30995step2Labels = raw30995step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30995step2 raw30995step2Labels = mixedMoment B raw30995step3 raw30995step3Labels := by
      have ha : raw30995step3 = raw30995step2 := by apply Matrix.ext; unfold raw30995step3 raw30995step2; decide +kernel
      have hl : raw30995step2Labels = labelEmbedding1 ∘ raw30995step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30995step2 raw30995step2Labels raw30995step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2212 node2212Labels := by rfl

theorem canonical30996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30996 raw30996Labels = mixedMoment B node2212 node2212Labels := by
  calc
    mixedMoment B raw30996 raw30996Labels = mixedMoment B raw30996step0 raw30996step0Labels := by
      have hz : ∀ j, raw30996 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30996step0 = (fun i j => raw30996 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30996step0 raw30996; decide +kernel
      have hl : raw30996step0Labels = raw30996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30996 raw30996Labels permutation346 hz
    mixedMoment B raw30996step0 raw30996step0Labels = mixedMoment B raw30996step1 raw30996step1Labels := by
      have ha : raw30996step1 = (fun i j => raw30996step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30996step1 raw30996step0; decide +kernel
      have hl : raw30996step1Labels = raw30996step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30996step0 raw30996step0Labels permutation42 permutation7
    mixedMoment B raw30996step1 raw30996step1Labels = mixedMoment B raw30996step2 raw30996step2Labels := by
      have ha : raw30996step2 = -raw30996step1 := by apply Matrix.ext; change ∀ i j, raw30996step2 i j = -(raw30996step1 i j); unfold raw30996step2 raw30996step1; decide +kernel
      have hl : raw30996step2Labels = raw30996step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30996step2 raw30996step2Labels = mixedMoment B raw30996step3 raw30996step3Labels := by
      have ha : raw30996step3 = raw30996step2 := by apply Matrix.ext; unfold raw30996step3 raw30996step2; decide +kernel
      have hl : raw30996step2Labels = labelEmbedding1 ∘ raw30996step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30996step2 raw30996step2Labels raw30996step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2212 node2212Labels := by rfl

theorem canonical30997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30997 raw30997Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw30997 raw30997Labels = mixedMoment B raw30997step0 raw30997step0Labels := by
      have hz : ∀ j, raw30997 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30997step0 = (fun i j => raw30997 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30997step0 raw30997; decide +kernel
      have hl : raw30997step0Labels = raw30997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30997 raw30997Labels permutation434 hz
    mixedMoment B raw30997step0 raw30997step0Labels = mixedMoment B raw30997step1 raw30997step1Labels := by
      have hz : ∀ j, raw30997step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30997step1 = (fun i j => raw30997step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30997step1 raw30997step0; decide +kernel
      have hl : raw30997step1Labels = raw30997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30997step0 raw30997step0Labels permutation80 hz
    mixedMoment B raw30997step1 raw30997step1Labels = mixedMoment B raw30997step2 raw30997step2Labels := by
      have ha : raw30997step2 = (fun i j => raw30997step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30997step2 raw30997step1; decide +kernel
      have hl : raw30997step2Labels = raw30997step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30997step1 raw30997step1Labels permutation12 permutation7
    mixedMoment B raw30997step2 raw30997step2Labels = mixedMoment B raw30997step3 raw30997step3Labels := by
      have ha : raw30997step3 = -raw30997step2 := by apply Matrix.ext; change ∀ i j, raw30997step3 i j = -(raw30997step2 i j); unfold raw30997step3 raw30997step2; decide +kernel
      have hl : raw30997step3Labels = raw30997step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30997step3 raw30997step3Labels = mixedMoment B raw30997step4 raw30997step4Labels := by
      have ha : raw30997step4 = raw30997step3 := by apply Matrix.ext; unfold raw30997step4 raw30997step3; decide +kernel
      have hl : raw30997step3Labels = labelEmbedding1 ∘ raw30997step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30997step3 raw30997step3Labels raw30997step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical30998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30998 raw30998Labels = mixedMoment B node2163 node2163Labels := by
  calc
    mixedMoment B raw30998 raw30998Labels = mixedMoment B raw30998step0 raw30998step0Labels := by
      have hz : ∀ j, raw30998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30998step0 = (fun i j => raw30998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30998step0 raw30998; decide +kernel
      have hl : raw30998step0Labels = raw30998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30998 raw30998Labels permutation434 hz
    mixedMoment B raw30998step0 raw30998step0Labels = mixedMoment B raw30998step1 raw30998step1Labels := by
      have hz : ∀ j, raw30998step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30998step1 = (fun i j => raw30998step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30998step1 raw30998step0; decide +kernel
      have hl : raw30998step1Labels = raw30998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30998step0 raw30998step0Labels permutation80 hz
    mixedMoment B raw30998step1 raw30998step1Labels = mixedMoment B raw30998step2 raw30998step2Labels := by
      have ha : raw30998step2 = (fun i j => raw30998step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30998step2 raw30998step1; decide +kernel
      have hl : raw30998step2Labels = raw30998step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30998step1 raw30998step1Labels permutation30 permutation5
    mixedMoment B raw30998step2 raw30998step2Labels = mixedMoment B raw30998step3 raw30998step3Labels := by
      have ha : raw30998step3 = raw30998step2 := by apply Matrix.ext; unfold raw30998step3 raw30998step2; decide +kernel
      have hl : raw30998step2Labels = labelEmbedding1 ∘ raw30998step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30998step2 raw30998step2Labels raw30998step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2163 node2163Labels := by rfl

theorem canonical30999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30999 raw30999Labels = mixedMoment B node2162 node2162Labels := by
  calc
    mixedMoment B raw30999 raw30999Labels = mixedMoment B raw30999step0 raw30999step0Labels := by
      have hz : ∀ j, raw30999 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30999step0 = (fun i j => raw30999 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30999step0 raw30999; decide +kernel
      have hl : raw30999step0Labels = raw30999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30999 raw30999Labels permutation434 hz
    mixedMoment B raw30999step0 raw30999step0Labels = mixedMoment B raw30999step1 raw30999step1Labels := by
      have ha : raw30999step1 = (fun i j => raw30999step0 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30999step1 raw30999step0; decide +kernel
      have hl : raw30999step1Labels = raw30999step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30999step0 raw30999step0Labels permutation147 permutation5
    mixedMoment B raw30999step1 raw30999step1Labels = mixedMoment B raw30999step2 raw30999step2Labels := by
      have ha : raw30999step2 = raw30999step1 := by apply Matrix.ext; unfold raw30999step2 raw30999step1; decide +kernel
      have hl : raw30999step1Labels = labelEmbedding1 ∘ raw30999step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30999step1 raw30999step1Labels raw30999step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2162 node2162Labels := by rfl

theorem canonical31000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31000 raw31000Labels = mixedMoment B node2162 node2162Labels := by
  calc
    mixedMoment B raw31000 raw31000Labels = mixedMoment B raw31000step0 raw31000step0Labels := by
      have hz : ∀ j, raw31000 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31000step0 = (fun i j => raw31000 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31000step0 raw31000; decide +kernel
      have hl : raw31000step0Labels = raw31000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31000 raw31000Labels permutation346 hz
    mixedMoment B raw31000step0 raw31000step0Labels = mixedMoment B raw31000step1 raw31000step1Labels := by
      have ha : raw31000step1 = (fun i j => raw31000step0 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31000step1 raw31000step0; decide +kernel
      have hl : raw31000step1Labels = raw31000step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31000step0 raw31000step0Labels permutation147 permutation5
    mixedMoment B raw31000step1 raw31000step1Labels = mixedMoment B raw31000step2 raw31000step2Labels := by
      have ha : raw31000step2 = raw31000step1 := by apply Matrix.ext; unfold raw31000step2 raw31000step1; decide +kernel
      have hl : raw31000step1Labels = labelEmbedding1 ∘ raw31000step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31000step1 raw31000step1Labels raw31000step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2162 node2162Labels := by rfl

theorem canonical31001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31001 raw31001Labels = mixedMoment B node2282 node2282Labels := by
  calc
    mixedMoment B raw31001 raw31001Labels = mixedMoment B raw31001step0 raw31001step0Labels := by
      have hz : ∀ j, raw31001 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31001step0 = (fun i j => raw31001 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31001step0 raw31001; decide +kernel
      have hl : raw31001step0Labels = raw31001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31001 raw31001Labels permutation434 hz
    mixedMoment B raw31001step0 raw31001step0Labels = mixedMoment B raw31001step1 raw31001step1Labels := by
      have hz : ∀ j, raw31001step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31001step1 = (fun i j => raw31001step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31001step1 raw31001step0; decide +kernel
      have hl : raw31001step1Labels = raw31001step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31001step0 raw31001step0Labels permutation80 hz
    mixedMoment B raw31001step1 raw31001step1Labels = mixedMoment B raw31001step2 raw31001step2Labels := by
      have ha : raw31001step2 = (fun i j => raw31001step1 (permutation27 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31001step2 raw31001step1; decide +kernel
      have hl : raw31001step2Labels = raw31001step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31001step1 raw31001step1Labels permutation27 permutation5
    mixedMoment B raw31001step2 raw31001step2Labels = mixedMoment B raw31001step3 raw31001step3Labels := by
      have ha : raw31001step3 = raw31001step2 := by apply Matrix.ext; unfold raw31001step3 raw31001step2; decide +kernel
      have hl : raw31001step2Labels = labelEmbedding1 ∘ raw31001step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31001step2 raw31001step2Labels raw31001step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2282 node2282Labels := by rfl

theorem canonical31002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31002 raw31002Labels = mixedMoment B node3056 node3056Labels := by
  calc
    mixedMoment B raw31002 raw31002Labels = mixedMoment B raw31002step0 raw31002step0Labels := by
      have hz : ∀ j, raw31002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31002step0 = (fun i j => raw31002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31002step0 raw31002; decide +kernel
      have hl : raw31002step0Labels = raw31002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31002 raw31002Labels permutation434 hz
    mixedMoment B raw31002step0 raw31002step0Labels = mixedMoment B raw31002step1 raw31002step1Labels := by
      have hz : ∀ j, raw31002step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31002step1 = (fun i j => raw31002step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31002step1 raw31002step0; decide +kernel
      have hl : raw31002step1Labels = raw31002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31002step0 raw31002step0Labels permutation80 hz
    mixedMoment B raw31002step1 raw31002step1Labels = mixedMoment B raw31002step2 raw31002step2Labels := by
      have ha : raw31002step2 = (fun i j => raw31002step1 (permutation16 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31002step2 raw31002step1; decide +kernel
      have hl : raw31002step2Labels = raw31002step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31002step1 raw31002step1Labels permutation16 permutation4
    mixedMoment B raw31002step2 raw31002step2Labels = mixedMoment B raw31002step3 raw31002step3Labels := by
      have ha : raw31002step3 = -raw31002step2 := by apply Matrix.ext; change ∀ i j, raw31002step3 i j = -(raw31002step2 i j); unfold raw31002step3 raw31002step2; decide +kernel
      have hl : raw31002step3Labels = raw31002step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3056 node3056Labels := by rfl

theorem canonical31003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31003 raw31003Labels = mixedMoment B node1826 node1826Labels := by
  calc
    mixedMoment B raw31003 raw31003Labels = mixedMoment B raw31003step0 raw31003step0Labels := by
      have hz : ∀ j, raw31003 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31003step0 = (fun i j => raw31003 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31003step0 raw31003; decide +kernel
      have hl : raw31003step0Labels = raw31003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31003 raw31003Labels permutation434 hz
    mixedMoment B raw31003step0 raw31003step0Labels = mixedMoment B raw31003step1 raw31003step1Labels := by
      have ha : raw31003step1 = (fun i j => raw31003step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31003step1 raw31003step0; decide +kernel
      have hl : raw31003step1Labels = raw31003step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31003step0 raw31003step0Labels permutation33 permutation2
    _ = mixedMoment B node1826 node1826Labels := by rfl

theorem canonical31004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31004 raw31004Labels = mixedMoment B node1826 node1826Labels := by
  calc
    mixedMoment B raw31004 raw31004Labels = mixedMoment B raw31004step0 raw31004step0Labels := by
      have hz : ∀ j, raw31004 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31004step0 = (fun i j => raw31004 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31004step0 raw31004; decide +kernel
      have hl : raw31004step0Labels = raw31004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31004 raw31004Labels permutation346 hz
    mixedMoment B raw31004step0 raw31004step0Labels = mixedMoment B raw31004step1 raw31004step1Labels := by
      have ha : raw31004step1 = (fun i j => raw31004step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31004step1 raw31004step0; decide +kernel
      have hl : raw31004step1Labels = raw31004step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31004step0 raw31004step0Labels permutation33 permutation2
    _ = mixedMoment B node1826 node1826Labels := by rfl

theorem canonical31005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31005 raw31005Labels = mixedMoment B node1830 node1830Labels := by
  calc
    mixedMoment B raw31005 raw31005Labels = mixedMoment B raw31005step0 raw31005step0Labels := by
      have hz : ∀ j, raw31005 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31005step0 = (fun i j => raw31005 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31005step0 raw31005; decide +kernel
      have hl : raw31005step0Labels = raw31005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31005 raw31005Labels permutation434 hz
    mixedMoment B raw31005step0 raw31005step0Labels = mixedMoment B raw31005step1 raw31005step1Labels := by
      have hz : ∀ j, raw31005step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31005step1 = (fun i j => raw31005step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31005step1 raw31005step0; decide +kernel
      have hl : raw31005step1Labels = raw31005step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31005step0 raw31005step0Labels permutation80 hz
    mixedMoment B raw31005step1 raw31005step1Labels = mixedMoment B raw31005step2 raw31005step2Labels := by
      have ha : raw31005step2 = (fun i j => raw31005step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31005step2 raw31005step1; decide +kernel
      have hl : raw31005step2Labels = raw31005step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31005step1 raw31005step1Labels permutation9 permutation2
    _ = mixedMoment B node1830 node1830Labels := by rfl

theorem canonical31006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31006 raw31006Labels = mixedMoment B node1974 node1974Labels := by
  calc
    mixedMoment B raw31006 raw31006Labels = mixedMoment B raw31006step0 raw31006step0Labels := by
      have ha : raw31006step0 = (fun i j => raw31006 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31006step0 raw31006; decide +kernel
      have hl : raw31006step0Labels = raw31006Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31006 raw31006Labels permutation201 permutation2
    _ = mixedMoment B node1974 node1974Labels := by rfl

theorem canonical31007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31007 raw31007Labels = mixedMoment B node2108 node2108Labels := by
  calc
    mixedMoment B raw31007 raw31007Labels = mixedMoment B raw31007step0 raw31007step0Labels := by
      have hz : ∀ j, raw31007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31007step0 = (fun i j => raw31007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31007step0 raw31007; decide +kernel
      have hl : raw31007step0Labels = raw31007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31007 raw31007Labels permutation434 hz
    _ = mixedMoment B node2108 node2108Labels := by rfl

theorem canonical31008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31008 raw31008Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw31008 raw31008Labels = mixedMoment B raw31008step0 raw31008step0Labels := by
      have hz : ∀ j, raw31008 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31008step0 = (fun i j => raw31008 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31008step0 raw31008; decide +kernel
      have hl : raw31008step0Labels = raw31008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31008 raw31008Labels permutation434 hz
    mixedMoment B raw31008step0 raw31008step0Labels = mixedMoment B raw31008step1 raw31008step1Labels := by
      have ha : raw31008step1 = (fun i j => raw31008step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31008step1 raw31008step0; decide +kernel
      have hl : raw31008step1Labels = raw31008step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31008step0 raw31008step0Labels permutation33 permutation2
    _ = mixedMoment B node2106 node2106Labels := by rfl

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

theorem canonical31139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31139 raw31139Labels = mixedMoment B node5303 node5303Labels := by
  calc
    mixedMoment B raw31139 raw31139Labels = mixedMoment B raw31139step0 raw31139step0Labels := by
      have hz : ∀ j, raw31139 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31139step0 = (fun i j => raw31139 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31139step0 raw31139; decide +kernel
      have hl : raw31139step0Labels = raw31139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31139 raw31139Labels permutation434 hz
    mixedMoment B raw31139step0 raw31139step0Labels = mixedMoment B raw31139step1 raw31139step1Labels := by
      have hz : ∀ j, raw31139step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31139step1 = (fun i j => raw31139step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31139step1 raw31139step0; decide +kernel
      have hl : raw31139step1Labels = raw31139step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31139step0 raw31139step0Labels permutation80 hz
    mixedMoment B raw31139step1 raw31139step1Labels = mixedMoment B raw31139step2 raw31139step2Labels := by
      have ha : raw31139step2 = (fun i j => raw31139step1 (permutation14 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31139step2 raw31139step1; decide +kernel
      have hl : raw31139step2Labels = raw31139step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31139step1 raw31139step1Labels permutation14 permutation5
    mixedMoment B raw31139step2 raw31139step2Labels = mixedMoment B raw31139step3 raw31139step3Labels := by
      have ha : raw31139step3 = -raw31139step2 := by apply Matrix.ext; change ∀ i j, raw31139step3 i j = -(raw31139step2 i j); unfold raw31139step3 raw31139step2; decide +kernel
      have hl : raw31139step3Labels = raw31139step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31139step3 raw31139step3Labels = mixedMoment B raw31139step4 raw31139step4Labels := by
      have ha : raw31139step4 = raw31139step3 := by apply Matrix.ext; unfold raw31139step4 raw31139step3; decide +kernel
      have hl : raw31139step3Labels = labelEmbedding8 ∘ raw31139step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31139step3 raw31139step3Labels raw31139step4Labels labelEmbedding8 hl
    _ = mixedMoment B node5303 node5303Labels := by rfl

theorem canonical31140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31140 raw31140Labels = mixedMoment B node5269 node5269Labels := by
  calc
    mixedMoment B raw31140 raw31140Labels = mixedMoment B raw31140step0 raw31140step0Labels := by
      have hz : ∀ j, raw31140 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31140step0 = (fun i j => raw31140 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31140step0 raw31140; decide +kernel
      have hl : raw31140step0Labels = raw31140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31140 raw31140Labels permutation434 hz
    mixedMoment B raw31140step0 raw31140step0Labels = mixedMoment B raw31140step1 raw31140step1Labels := by
      have ha : raw31140step1 = (fun i j => raw31140step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31140step1 raw31140step0; decide +kernel
      have hl : raw31140step1Labels = raw31140step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31140step0 raw31140step0Labels permutation38 permutation7
    mixedMoment B raw31140step1 raw31140step1Labels = mixedMoment B raw31140step2 raw31140step2Labels := by
      have ha : raw31140step2 = -raw31140step1 := by apply Matrix.ext; change ∀ i j, raw31140step2 i j = -(raw31140step1 i j); unfold raw31140step2 raw31140step1; decide +kernel
      have hl : raw31140step2Labels = raw31140step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31140step2 raw31140step2Labels = mixedMoment B raw31140step3 raw31140step3Labels := by
      have ha : raw31140step3 = raw31140step2 := by apply Matrix.ext; unfold raw31140step3 raw31140step2; decide +kernel
      have hl : raw31140step2Labels = labelEmbedding10 ∘ raw31140step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31140step2 raw31140step2Labels raw31140step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5269 node5269Labels := by rfl

theorem canonical31141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31141 raw31141Labels = mixedMoment B node5269 node5269Labels := by
  calc
    mixedMoment B raw31141 raw31141Labels = mixedMoment B raw31141step0 raw31141step0Labels := by
      have hz : ∀ j, raw31141 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31141step0 = (fun i j => raw31141 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31141step0 raw31141; decide +kernel
      have hl : raw31141step0Labels = raw31141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31141 raw31141Labels permutation346 hz
    mixedMoment B raw31141step0 raw31141step0Labels = mixedMoment B raw31141step1 raw31141step1Labels := by
      have ha : raw31141step1 = (fun i j => raw31141step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31141step1 raw31141step0; decide +kernel
      have hl : raw31141step1Labels = raw31141step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31141step0 raw31141step0Labels permutation38 permutation7
    mixedMoment B raw31141step1 raw31141step1Labels = mixedMoment B raw31141step2 raw31141step2Labels := by
      have ha : raw31141step2 = -raw31141step1 := by apply Matrix.ext; change ∀ i j, raw31141step2 i j = -(raw31141step1 i j); unfold raw31141step2 raw31141step1; decide +kernel
      have hl : raw31141step2Labels = raw31141step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31141step2 raw31141step2Labels = mixedMoment B raw31141step3 raw31141step3Labels := by
      have ha : raw31141step3 = raw31141step2 := by apply Matrix.ext; unfold raw31141step3 raw31141step2; decide +kernel
      have hl : raw31141step2Labels = labelEmbedding10 ∘ raw31141step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31141step2 raw31141step2Labels raw31141step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5269 node5269Labels := by rfl

theorem canonical31142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31142 raw31142Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw31142 raw31142Labels = mixedMoment B raw31142step0 raw31142step0Labels := by
      have hz : ∀ j, raw31142 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31142step0 = (fun i j => raw31142 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31142step0 raw31142; decide +kernel
      have hl : raw31142step0Labels = raw31142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31142 raw31142Labels permutation434 hz
    mixedMoment B raw31142step0 raw31142step0Labels = mixedMoment B raw31142step1 raw31142step1Labels := by
      have hz : ∀ j, raw31142step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31142step1 = (fun i j => raw31142step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31142step1 raw31142step0; decide +kernel
      have hl : raw31142step1Labels = raw31142step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31142step0 raw31142step0Labels permutation80 hz
    mixedMoment B raw31142step1 raw31142step1Labels = mixedMoment B raw31142step2 raw31142step2Labels := by
      have ha : raw31142step2 = (fun i j => raw31142step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31142step2 raw31142step1; decide +kernel
      have hl : raw31142step2Labels = raw31142step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31142step1 raw31142step1Labels permutation9 permutation7
    mixedMoment B raw31142step2 raw31142step2Labels = mixedMoment B raw31142step3 raw31142step3Labels := by
      have ha : raw31142step3 = -raw31142step2 := by apply Matrix.ext; change ∀ i j, raw31142step3 i j = -(raw31142step2 i j); unfold raw31142step3 raw31142step2; decide +kernel
      have hl : raw31142step3Labels = raw31142step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31142step3 raw31142step3Labels = mixedMoment B raw31142step4 raw31142step4Labels := by
      have ha : raw31142step4 = raw31142step3 := by apply Matrix.ext; unfold raw31142step4 raw31142step3; decide +kernel
      have hl : raw31142step3Labels = labelEmbedding10 ∘ raw31142step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31142step3 raw31142step3Labels raw31142step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

theorem canonical31143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31143 raw31143Labels = mixedMoment B node4701 node4701Labels := by
  calc
    mixedMoment B raw31143 raw31143Labels = mixedMoment B raw31143step0 raw31143step0Labels := by
      have hz : ∀ j, raw31143 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31143step0 = (fun i j => raw31143 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31143step0 raw31143; decide +kernel
      have hl : raw31143step0Labels = raw31143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31143 raw31143Labels permutation434 hz
    _ = mixedMoment B node4701 node4701Labels := by rfl

theorem canonical31144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31144 raw31144Labels = mixedMoment B node4774 node4774Labels := by
  calc
    mixedMoment B raw31144 raw31144Labels = mixedMoment B raw31144step0 raw31144step0Labels := by
      have ha : raw31144step0 = (fun i j => raw31144 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31144step0 raw31144; decide +kernel
      have hl : raw31144step0Labels = raw31144Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31144 raw31144Labels permutation200 permutation2
    _ = mixedMoment B node4774 node4774Labels := by rfl

theorem canonical31145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31145 raw31145Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw31145 raw31145Labels = mixedMoment B raw31145step0 raw31145step0Labels := by
      have hz : ∀ j, raw31145 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31145step0 = (fun i j => raw31145 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31145step0 raw31145; decide +kernel
      have hl : raw31145step0Labels = raw31145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31145 raw31145Labels permutation434 hz
    mixedMoment B raw31145step0 raw31145step0Labels = mixedMoment B raw31145step1 raw31145step1Labels := by
      have ha : raw31145step1 = (fun i j => raw31145step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31145step1 raw31145step0; decide +kernel
      have hl : raw31145step1Labels = raw31145step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31145step0 raw31145step0Labels permutation33 permutation2
    _ = mixedMoment B node4866 node4866Labels := by rfl

theorem canonical31146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31146 raw31146Labels = mixedMoment B node4701 node4701Labels := by
  calc
    mixedMoment B raw31146 raw31146Labels = mixedMoment B raw31146step0 raw31146step0Labels := by
      have hz : ∀ j, raw31146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31146step0 = (fun i j => raw31146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31146step0 raw31146; decide +kernel
      have hl : raw31146step0Labels = raw31146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31146 raw31146Labels permutation346 hz
    _ = mixedMoment B node4701 node4701Labels := by rfl

theorem canonical31147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31147 raw31147Labels = mixedMoment B node4774 node4774Labels := by
  calc
    mixedMoment B raw31147 raw31147Labels = mixedMoment B raw31147step0 raw31147step0Labels := by
      have ha : raw31147step0 = (fun i j => raw31147 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31147step0 raw31147; decide +kernel
      have hl : raw31147step0Labels = raw31147Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31147 raw31147Labels permutation176 permutation2
    _ = mixedMoment B node4774 node4774Labels := by rfl

theorem canonical31148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31148 raw31148Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw31148 raw31148Labels = mixedMoment B raw31148step0 raw31148step0Labels := by
      have hz : ∀ j, raw31148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31148step0 = (fun i j => raw31148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31148step0 raw31148; decide +kernel
      have hl : raw31148step0Labels = raw31148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31148 raw31148Labels permutation346 hz
    mixedMoment B raw31148step0 raw31148step0Labels = mixedMoment B raw31148step1 raw31148step1Labels := by
      have ha : raw31148step1 = (fun i j => raw31148step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31148step1 raw31148step0; decide +kernel
      have hl : raw31148step1Labels = raw31148step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31148step0 raw31148step0Labels permutation33 permutation2
    _ = mixedMoment B node4866 node4866Labels := by rfl

theorem canonical31149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31149 raw31149Labels = mixedMoment B node4705 node4705Labels := by
  calc
    mixedMoment B raw31149 raw31149Labels = mixedMoment B raw31149step0 raw31149step0Labels := by
      have hz : ∀ j, raw31149 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31149step0 = (fun i j => raw31149 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31149step0 raw31149; decide +kernel
      have hl : raw31149step0Labels = raw31149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31149 raw31149Labels permutation434 hz
    mixedMoment B raw31149step0 raw31149step0Labels = mixedMoment B raw31149step1 raw31149step1Labels := by
      have hz : ∀ j, raw31149step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31149step1 = (fun i j => raw31149step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31149step1 raw31149step0; decide +kernel
      have hl : raw31149step1Labels = raw31149step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31149step0 raw31149step0Labels permutation80 hz
    mixedMoment B raw31149step1 raw31149step1Labels = mixedMoment B raw31149step2 raw31149step2Labels := by
      have ha : raw31149step2 = (fun i j => raw31149step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31149step2 raw31149step1; decide +kernel
      have hl : raw31149step2Labels = raw31149step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31149step1 raw31149step1Labels permutation9 permutation2
    _ = mixedMoment B node4705 node4705Labels := by rfl

theorem canonical31150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31150 raw31150Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw31150 raw31150Labels = mixedMoment B raw31150step0 raw31150step0Labels := by
      have hz : ∀ j, raw31150 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31150step0 = (fun i j => raw31150 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31150step0 raw31150; decide +kernel
      have hl : raw31150step0Labels = raw31150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31150 raw31150Labels permutation434 hz
    mixedMoment B raw31150step0 raw31150step0Labels = mixedMoment B raw31150step1 raw31150step1Labels := by
      have ha : raw31150step1 = (fun i j => raw31150step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31150step1 raw31150step0; decide +kernel
      have hl : raw31150step1Labels = raw31150step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31150step0 raw31150step0Labels permutation39 permutation2
    _ = mixedMoment B node4777 node4777Labels := by rfl

theorem canonical31151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31151 raw31151Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw31151 raw31151Labels = mixedMoment B raw31151step0 raw31151step0Labels := by
      have hz : ∀ j, raw31151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31151step0 = (fun i j => raw31151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31151step0 raw31151; decide +kernel
      have hl : raw31151step0Labels = raw31151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31151 raw31151Labels permutation346 hz
    mixedMoment B raw31151step0 raw31151step0Labels = mixedMoment B raw31151step1 raw31151step1Labels := by
      have ha : raw31151step1 = (fun i j => raw31151step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31151step1 raw31151step0; decide +kernel
      have hl : raw31151step1Labels = raw31151step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31151step0 raw31151step0Labels permutation39 permutation2
    _ = mixedMoment B node4777 node4777Labels := by rfl

theorem canonical31152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31152 raw31152Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw31152 raw31152Labels = mixedMoment B raw31152step0 raw31152step0Labels := by
      have hz : ∀ j, raw31152 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31152step0 = (fun i j => raw31152 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31152step0 raw31152; decide +kernel
      have hl : raw31152step0Labels = raw31152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31152 raw31152Labels permutation434 hz
    mixedMoment B raw31152step0 raw31152step0Labels = mixedMoment B raw31152step1 raw31152step1Labels := by
      have hz : ∀ j, raw31152step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31152step1 = (fun i j => raw31152step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31152step1 raw31152step0; decide +kernel
      have hl : raw31152step1Labels = raw31152step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31152step0 raw31152step0Labels permutation80 hz
    mixedMoment B raw31152step1 raw31152step1Labels = mixedMoment B raw31152step2 raw31152step2Labels := by
      have ha : raw31152step2 = (fun i j => raw31152step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31152step2 raw31152step1; decide +kernel
      have hl : raw31152step2Labels = raw31152step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31152step1 raw31152step1Labels permutation9 permutation2
    _ = mixedMoment B node4871 node4871Labels := by rfl

theorem canonical31153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31153 raw31153Labels = mixedMoment B node4705 node4705Labels := by
  calc
    mixedMoment B raw31153 raw31153Labels = mixedMoment B raw31153step0 raw31153step0Labels := by
      have hz : ∀ j, raw31153 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31153step0 = (fun i j => raw31153 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31153step0 raw31153; decide +kernel
      have hl : raw31153step0Labels = raw31153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31153 raw31153Labels permutation434 hz
    mixedMoment B raw31153step0 raw31153step0Labels = mixedMoment B raw31153step1 raw31153step1Labels := by
      have hz : ∀ j, raw31153step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31153step1 = (fun i j => raw31153step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31153step1 raw31153step0; decide +kernel
      have hl : raw31153step1Labels = raw31153step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31153step0 raw31153step0Labels permutation80 hz
    _ = mixedMoment B node4705 node4705Labels := by rfl

theorem canonical31154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31154 raw31154Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw31154 raw31154Labels = mixedMoment B raw31154step0 raw31154step0Labels := by
      have hz : ∀ j, raw31154 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31154step0 = (fun i j => raw31154 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31154step0 raw31154; decide +kernel
      have hl : raw31154step0Labels = raw31154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31154 raw31154Labels permutation434 hz
    mixedMoment B raw31154step0 raw31154step0Labels = mixedMoment B raw31154step1 raw31154step1Labels := by
      have ha : raw31154step1 = (fun i j => raw31154step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31154step1 raw31154step0; decide +kernel
      have hl : raw31154step1Labels = raw31154step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31154step0 raw31154step0Labels permutation38 permutation2
    _ = mixedMoment B node4777 node4777Labels := by rfl

theorem canonical31155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31155 raw31155Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw31155 raw31155Labels = mixedMoment B raw31155step0 raw31155step0Labels := by
      have hz : ∀ j, raw31155 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31155step0 = (fun i j => raw31155 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31155step0 raw31155; decide +kernel
      have hl : raw31155step0Labels = raw31155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31155 raw31155Labels permutation346 hz
    mixedMoment B raw31155step0 raw31155step0Labels = mixedMoment B raw31155step1 raw31155step1Labels := by
      have ha : raw31155step1 = (fun i j => raw31155step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31155step1 raw31155step0; decide +kernel
      have hl : raw31155step1Labels = raw31155step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31155step0 raw31155step0Labels permutation38 permutation2
    _ = mixedMoment B node4777 node4777Labels := by rfl

theorem canonical31176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31176 raw31176Labels = mixedMoment B node2779 node2779Labels := by
  calc
    mixedMoment B raw31176 raw31176Labels = mixedMoment B raw31176step0 raw31176step0Labels := by
      have hz : ∀ j, raw31176 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31176step0 = (fun i j => raw31176 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31176step0 raw31176; decide +kernel
      have hl : raw31176step0Labels = raw31176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31176 raw31176Labels permutation434 hz
    mixedMoment B raw31176step0 raw31176step0Labels = mixedMoment B raw31176step1 raw31176step1Labels := by
      have hz : ∀ j, raw31176step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31176step1 = (fun i j => raw31176step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31176step1 raw31176step0; decide +kernel
      have hl : raw31176step1Labels = raw31176step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31176step0 raw31176step0Labels permutation80 hz
    mixedMoment B raw31176step1 raw31176step1Labels = mixedMoment B raw31176step2 raw31176step2Labels := by
      have ha : raw31176step2 = (fun i j => raw31176step1 (permutation14 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31176step2 raw31176step1; decide +kernel
      have hl : raw31176step2Labels = raw31176step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31176step1 raw31176step1Labels permutation14 permutation5
    mixedMoment B raw31176step2 raw31176step2Labels = mixedMoment B raw31176step3 raw31176step3Labels := by
      have ha : raw31176step3 = -raw31176step2 := by apply Matrix.ext; change ∀ i j, raw31176step3 i j = -(raw31176step2 i j); unfold raw31176step3 raw31176step2; decide +kernel
      have hl : raw31176step3Labels = raw31176step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31176step3 raw31176step3Labels = mixedMoment B raw31176step4 raw31176step4Labels := by
      have ha : raw31176step4 = raw31176step3 := by apply Matrix.ext; unfold raw31176step4 raw31176step3; decide +kernel
      have hl : raw31176step3Labels = labelEmbedding1 ∘ raw31176step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31176step3 raw31176step3Labels raw31176step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2779 node2779Labels := by rfl

theorem canonical31177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31177 raw31177Labels = mixedMoment B node2736 node2736Labels := by
  calc
    mixedMoment B raw31177 raw31177Labels = mixedMoment B raw31177step0 raw31177step0Labels := by
      have hz : ∀ j, raw31177 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31177step0 = (fun i j => raw31177 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31177step0 raw31177; decide +kernel
      have hl : raw31177step0Labels = raw31177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31177 raw31177Labels permutation434 hz
    mixedMoment B raw31177step0 raw31177step0Labels = mixedMoment B raw31177step1 raw31177step1Labels := by
      have ha : raw31177step1 = (fun i j => raw31177step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31177step1 raw31177step0; decide +kernel
      have hl : raw31177step1Labels = raw31177step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31177step0 raw31177step0Labels permutation38 permutation7
    mixedMoment B raw31177step1 raw31177step1Labels = mixedMoment B raw31177step2 raw31177step2Labels := by
      have ha : raw31177step2 = -raw31177step1 := by apply Matrix.ext; change ∀ i j, raw31177step2 i j = -(raw31177step1 i j); unfold raw31177step2 raw31177step1; decide +kernel
      have hl : raw31177step2Labels = raw31177step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31177step2 raw31177step2Labels = mixedMoment B raw31177step3 raw31177step3Labels := by
      have ha : raw31177step3 = raw31177step2 := by apply Matrix.ext; unfold raw31177step3 raw31177step2; decide +kernel
      have hl : raw31177step2Labels = labelEmbedding1 ∘ raw31177step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31177step2 raw31177step2Labels raw31177step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2736 node2736Labels := by rfl

theorem canonical31178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31178 raw31178Labels = mixedMoment B node2736 node2736Labels := by
  calc
    mixedMoment B raw31178 raw31178Labels = mixedMoment B raw31178step0 raw31178step0Labels := by
      have hz : ∀ j, raw31178 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31178step0 = (fun i j => raw31178 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31178step0 raw31178; decide +kernel
      have hl : raw31178step0Labels = raw31178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31178 raw31178Labels permutation346 hz
    mixedMoment B raw31178step0 raw31178step0Labels = mixedMoment B raw31178step1 raw31178step1Labels := by
      have ha : raw31178step1 = (fun i j => raw31178step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31178step1 raw31178step0; decide +kernel
      have hl : raw31178step1Labels = raw31178step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31178step0 raw31178step0Labels permutation38 permutation7
    mixedMoment B raw31178step1 raw31178step1Labels = mixedMoment B raw31178step2 raw31178step2Labels := by
      have ha : raw31178step2 = -raw31178step1 := by apply Matrix.ext; change ∀ i j, raw31178step2 i j = -(raw31178step1 i j); unfold raw31178step2 raw31178step1; decide +kernel
      have hl : raw31178step2Labels = raw31178step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31178step2 raw31178step2Labels = mixedMoment B raw31178step3 raw31178step3Labels := by
      have ha : raw31178step3 = raw31178step2 := by apply Matrix.ext; unfold raw31178step3 raw31178step2; decide +kernel
      have hl : raw31178step2Labels = labelEmbedding1 ∘ raw31178step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31178step2 raw31178step2Labels raw31178step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2736 node2736Labels := by rfl

theorem canonical31179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31179 raw31179Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw31179 raw31179Labels = mixedMoment B raw31179step0 raw31179step0Labels := by
      have hz : ∀ j, raw31179 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31179step0 = (fun i j => raw31179 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31179step0 raw31179; decide +kernel
      have hl : raw31179step0Labels = raw31179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31179 raw31179Labels permutation434 hz
    mixedMoment B raw31179step0 raw31179step0Labels = mixedMoment B raw31179step1 raw31179step1Labels := by
      have hz : ∀ j, raw31179step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31179step1 = (fun i j => raw31179step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31179step1 raw31179step0; decide +kernel
      have hl : raw31179step1Labels = raw31179step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31179step0 raw31179step0Labels permutation80 hz
    mixedMoment B raw31179step1 raw31179step1Labels = mixedMoment B raw31179step2 raw31179step2Labels := by
      have ha : raw31179step2 = (fun i j => raw31179step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31179step2 raw31179step1; decide +kernel
      have hl : raw31179step2Labels = raw31179step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31179step1 raw31179step1Labels permutation9 permutation7
    mixedMoment B raw31179step2 raw31179step2Labels = mixedMoment B raw31179step3 raw31179step3Labels := by
      have ha : raw31179step3 = -raw31179step2 := by apply Matrix.ext; change ∀ i j, raw31179step3 i j = -(raw31179step2 i j); unfold raw31179step3 raw31179step2; decide +kernel
      have hl : raw31179step3Labels = raw31179step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31179step3 raw31179step3Labels = mixedMoment B raw31179step4 raw31179step4Labels := by
      have ha : raw31179step4 = raw31179step3 := by apply Matrix.ext; unfold raw31179step4 raw31179step3; decide +kernel
      have hl : raw31179step3Labels = labelEmbedding1 ∘ raw31179step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31179step3 raw31179step3Labels raw31179step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2782 node2782Labels := by rfl

theorem canonical31180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31180 raw31180Labels = mixedMoment B node2257 node2257Labels := by
  calc
    mixedMoment B raw31180 raw31180Labels = mixedMoment B raw31180step0 raw31180step0Labels := by
      have hz : ∀ j, raw31180 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31180step0 = (fun i j => raw31180 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31180step0 raw31180; decide +kernel
      have hl : raw31180step0Labels = raw31180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31180 raw31180Labels permutation434 hz
    mixedMoment B raw31180step0 raw31180step0Labels = mixedMoment B raw31180step1 raw31180step1Labels := by
      have ha : raw31180step1 = (fun i j => raw31180step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31180step1 raw31180step0; decide +kernel
      have hl : raw31180step1Labels = raw31180step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31180step0 raw31180step0Labels permutation38 permutation7
    mixedMoment B raw31180step1 raw31180step1Labels = mixedMoment B raw31180step2 raw31180step2Labels := by
      have ha : raw31180step2 = -raw31180step1 := by apply Matrix.ext; change ∀ i j, raw31180step2 i j = -(raw31180step1 i j); unfold raw31180step2 raw31180step1; decide +kernel
      have hl : raw31180step2Labels = raw31180step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31180step2 raw31180step2Labels = mixedMoment B raw31180step3 raw31180step3Labels := by
      have ha : raw31180step3 = raw31180step2 := by apply Matrix.ext; unfold raw31180step3 raw31180step2; decide +kernel
      have hl : raw31180step2Labels = labelEmbedding1 ∘ raw31180step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31180step2 raw31180step2Labels raw31180step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2257 node2257Labels := by rfl

theorem canonical31181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31181 raw31181Labels = mixedMoment B node2199 node2199Labels := by
  calc
    mixedMoment B raw31181 raw31181Labels = mixedMoment B raw31181step0 raw31181step0Labels := by
      have ha : raw31181step0 = (fun i j => raw31181 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31181step0 raw31181; decide +kernel
      have hl : raw31181step0Labels = raw31181Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31181 raw31181Labels permutation206 permutation7
    mixedMoment B raw31181step0 raw31181step0Labels = mixedMoment B raw31181step1 raw31181step1Labels := by
      have ha : raw31181step1 = -raw31181step0 := by apply Matrix.ext; change ∀ i j, raw31181step1 i j = -(raw31181step0 i j); unfold raw31181step1 raw31181step0; decide +kernel
      have hl : raw31181step1Labels = raw31181step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31181step1 raw31181step1Labels = mixedMoment B raw31181step2 raw31181step2Labels := by
      have ha : raw31181step2 = raw31181step1 := by apply Matrix.ext; unfold raw31181step2 raw31181step1; decide +kernel
      have hl : raw31181step1Labels = labelEmbedding1 ∘ raw31181step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31181step1 raw31181step1Labels raw31181step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2199 node2199Labels := by rfl

theorem canonical31182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31182 raw31182Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw31182 raw31182Labels = mixedMoment B raw31182step0 raw31182step0Labels := by
      have hz : ∀ j, raw31182 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31182step0 = (fun i j => raw31182 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31182step0 raw31182; decide +kernel
      have hl : raw31182step0Labels = raw31182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31182 raw31182Labels permutation434 hz
    mixedMoment B raw31182step0 raw31182step0Labels = mixedMoment B raw31182step1 raw31182step1Labels := by
      have ha : raw31182step1 = (fun i j => raw31182step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31182step1 raw31182step0; decide +kernel
      have hl : raw31182step1Labels = raw31182step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31182step0 raw31182step0Labels permutation39 permutation7
    mixedMoment B raw31182step1 raw31182step1Labels = mixedMoment B raw31182step2 raw31182step2Labels := by
      have ha : raw31182step2 = -raw31182step1 := by apply Matrix.ext; change ∀ i j, raw31182step2 i j = -(raw31182step1 i j); unfold raw31182step2 raw31182step1; decide +kernel
      have hl : raw31182step2Labels = raw31182step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31182step2 raw31182step2Labels = mixedMoment B raw31182step3 raw31182step3Labels := by
      have ha : raw31182step3 = raw31182step2 := by apply Matrix.ext; unfold raw31182step3 raw31182step2; decide +kernel
      have hl : raw31182step2Labels = labelEmbedding1 ∘ raw31182step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31182step2 raw31182step2Labels raw31182step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical31183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31183 raw31183Labels = mixedMoment B node2257 node2257Labels := by
  calc
    mixedMoment B raw31183 raw31183Labels = mixedMoment B raw31183step0 raw31183step0Labels := by
      have hz : ∀ j, raw31183 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31183step0 = (fun i j => raw31183 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31183step0 raw31183; decide +kernel
      have hl : raw31183step0Labels = raw31183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31183 raw31183Labels permutation346 hz
    mixedMoment B raw31183step0 raw31183step0Labels = mixedMoment B raw31183step1 raw31183step1Labels := by
      have ha : raw31183step1 = (fun i j => raw31183step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31183step1 raw31183step0; decide +kernel
      have hl : raw31183step1Labels = raw31183step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31183step0 raw31183step0Labels permutation38 permutation7
    mixedMoment B raw31183step1 raw31183step1Labels = mixedMoment B raw31183step2 raw31183step2Labels := by
      have ha : raw31183step2 = -raw31183step1 := by apply Matrix.ext; change ∀ i j, raw31183step2 i j = -(raw31183step1 i j); unfold raw31183step2 raw31183step1; decide +kernel
      have hl : raw31183step2Labels = raw31183step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31183step2 raw31183step2Labels = mixedMoment B raw31183step3 raw31183step3Labels := by
      have ha : raw31183step3 = raw31183step2 := by apply Matrix.ext; unfold raw31183step3 raw31183step2; decide +kernel
      have hl : raw31183step2Labels = labelEmbedding1 ∘ raw31183step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31183step2 raw31183step2Labels raw31183step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2257 node2257Labels := by rfl

theorem canonical31184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31184 raw31184Labels = mixedMoment B node2199 node2199Labels := by
  calc
    mixedMoment B raw31184 raw31184Labels = mixedMoment B raw31184step0 raw31184step0Labels := by
      have ha : raw31184step0 = (fun i j => raw31184 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31184step0 raw31184; decide +kernel
      have hl : raw31184step0Labels = raw31184Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31184 raw31184Labels permutation182 permutation7
    mixedMoment B raw31184step0 raw31184step0Labels = mixedMoment B raw31184step1 raw31184step1Labels := by
      have ha : raw31184step1 = -raw31184step0 := by apply Matrix.ext; change ∀ i j, raw31184step1 i j = -(raw31184step0 i j); unfold raw31184step1 raw31184step0; decide +kernel
      have hl : raw31184step1Labels = raw31184step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31184step1 raw31184step1Labels = mixedMoment B raw31184step2 raw31184step2Labels := by
      have ha : raw31184step2 = raw31184step1 := by apply Matrix.ext; unfold raw31184step2 raw31184step1; decide +kernel
      have hl : raw31184step1Labels = labelEmbedding1 ∘ raw31184step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31184step1 raw31184step1Labels raw31184step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2199 node2199Labels := by rfl

theorem canonical31185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31185 raw31185Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw31185 raw31185Labels = mixedMoment B raw31185step0 raw31185step0Labels := by
      have hz : ∀ j, raw31185 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31185step0 = (fun i j => raw31185 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31185step0 raw31185; decide +kernel
      have hl : raw31185step0Labels = raw31185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31185 raw31185Labels permutation346 hz
    mixedMoment B raw31185step0 raw31185step0Labels = mixedMoment B raw31185step1 raw31185step1Labels := by
      have ha : raw31185step1 = (fun i j => raw31185step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31185step1 raw31185step0; decide +kernel
      have hl : raw31185step1Labels = raw31185step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31185step0 raw31185step0Labels permutation39 permutation7
    mixedMoment B raw31185step1 raw31185step1Labels = mixedMoment B raw31185step2 raw31185step2Labels := by
      have ha : raw31185step2 = -raw31185step1 := by apply Matrix.ext; change ∀ i j, raw31185step2 i j = -(raw31185step1 i j); unfold raw31185step2 raw31185step1; decide +kernel
      have hl : raw31185step2Labels = raw31185step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31185step2 raw31185step2Labels = mixedMoment B raw31185step3 raw31185step3Labels := by
      have ha : raw31185step3 = raw31185step2 := by apply Matrix.ext; unfold raw31185step3 raw31185step2; decide +kernel
      have hl : raw31185step2Labels = labelEmbedding1 ∘ raw31185step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31185step2 raw31185step2Labels raw31185step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical31186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31186 raw31186Labels = mixedMoment B node2286 node2286Labels := by
  calc
    mixedMoment B raw31186 raw31186Labels = mixedMoment B raw31186step0 raw31186step0Labels := by
      have hz : ∀ j, raw31186 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31186step0 = (fun i j => raw31186 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31186step0 raw31186; decide +kernel
      have hl : raw31186step0Labels = raw31186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31186 raw31186Labels permutation434 hz
    mixedMoment B raw31186step0 raw31186step0Labels = mixedMoment B raw31186step1 raw31186step1Labels := by
      have hz : ∀ j, raw31186step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31186step1 = (fun i j => raw31186step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31186step1 raw31186step0; decide +kernel
      have hl : raw31186step1Labels = raw31186step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31186step0 raw31186step0Labels permutation80 hz
    mixedMoment B raw31186step1 raw31186step1Labels = mixedMoment B raw31186step2 raw31186step2Labels := by
      have ha : raw31186step2 = (fun i j => raw31186step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31186step2 raw31186step1; decide +kernel
      have hl : raw31186step2Labels = raw31186step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31186step1 raw31186step1Labels permutation9 permutation7
    mixedMoment B raw31186step2 raw31186step2Labels = mixedMoment B raw31186step3 raw31186step3Labels := by
      have ha : raw31186step3 = -raw31186step2 := by apply Matrix.ext; change ∀ i j, raw31186step3 i j = -(raw31186step2 i j); unfold raw31186step3 raw31186step2; decide +kernel
      have hl : raw31186step3Labels = raw31186step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31186step3 raw31186step3Labels = mixedMoment B raw31186step4 raw31186step4Labels := by
      have ha : raw31186step4 = raw31186step3 := by apply Matrix.ext; unfold raw31186step4 raw31186step3; decide +kernel
      have hl : raw31186step3Labels = labelEmbedding1 ∘ raw31186step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31186step3 raw31186step3Labels raw31186step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2286 node2286Labels := by rfl

theorem canonical31187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31187 raw31187Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw31187 raw31187Labels = mixedMoment B raw31187step0 raw31187step0Labels := by
      have hz : ∀ j, raw31187 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31187step0 = (fun i j => raw31187 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31187step0 raw31187; decide +kernel
      have hl : raw31187step0Labels = raw31187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31187 raw31187Labels permutation434 hz
    mixedMoment B raw31187step0 raw31187step0Labels = mixedMoment B raw31187step1 raw31187step1Labels := by
      have ha : raw31187step1 = (fun i j => raw31187step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31187step1 raw31187step0; decide +kernel
      have hl : raw31187step1Labels = raw31187step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31187step0 raw31187step0Labels permutation39 permutation7
    mixedMoment B raw31187step1 raw31187step1Labels = mixedMoment B raw31187step2 raw31187step2Labels := by
      have ha : raw31187step2 = -raw31187step1 := by apply Matrix.ext; change ∀ i j, raw31187step2 i j = -(raw31187step1 i j); unfold raw31187step2 raw31187step1; decide +kernel
      have hl : raw31187step2Labels = raw31187step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31187step2 raw31187step2Labels = mixedMoment B raw31187step3 raw31187step3Labels := by
      have ha : raw31187step3 = raw31187step2 := by apply Matrix.ext; unfold raw31187step3 raw31187step2; decide +kernel
      have hl : raw31187step2Labels = labelEmbedding1 ∘ raw31187step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31187step2 raw31187step2Labels raw31187step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

theorem canonical31188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31188 raw31188Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw31188 raw31188Labels = mixedMoment B raw31188step0 raw31188step0Labels := by
      have hz : ∀ j, raw31188 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31188step0 = (fun i j => raw31188 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31188step0 raw31188; decide +kernel
      have hl : raw31188step0Labels = raw31188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31188 raw31188Labels permutation346 hz
    mixedMoment B raw31188step0 raw31188step0Labels = mixedMoment B raw31188step1 raw31188step1Labels := by
      have ha : raw31188step1 = (fun i j => raw31188step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31188step1 raw31188step0; decide +kernel
      have hl : raw31188step1Labels = raw31188step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31188step0 raw31188step0Labels permutation39 permutation7
    mixedMoment B raw31188step1 raw31188step1Labels = mixedMoment B raw31188step2 raw31188step2Labels := by
      have ha : raw31188step2 = -raw31188step1 := by apply Matrix.ext; change ∀ i j, raw31188step2 i j = -(raw31188step1 i j); unfold raw31188step2 raw31188step1; decide +kernel
      have hl : raw31188step2Labels = raw31188step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31188step2 raw31188step2Labels = mixedMoment B raw31188step3 raw31188step3Labels := by
      have ha : raw31188step3 = raw31188step2 := by apply Matrix.ext; unfold raw31188step3 raw31188step2; decide +kernel
      have hl : raw31188step2Labels = labelEmbedding1 ∘ raw31188step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31188step2 raw31188step2Labels raw31188step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

theorem canonical31189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31189 raw31189Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw31189 raw31189Labels = mixedMoment B raw31189step0 raw31189step0Labels := by
      have hz : ∀ j, raw31189 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31189step0 = (fun i j => raw31189 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31189step0 raw31189; decide +kernel
      have hl : raw31189step0Labels = raw31189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31189 raw31189Labels permutation434 hz
    mixedMoment B raw31189step0 raw31189step0Labels = mixedMoment B raw31189step1 raw31189step1Labels := by
      have hz : ∀ j, raw31189step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31189step1 = (fun i j => raw31189step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31189step1 raw31189step0; decide +kernel
      have hl : raw31189step1Labels = raw31189step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31189step0 raw31189step0Labels permutation80 hz
    mixedMoment B raw31189step1 raw31189step1Labels = mixedMoment B raw31189step2 raw31189step2Labels := by
      have ha : raw31189step2 = (fun i j => raw31189step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31189step2 raw31189step1; decide +kernel
      have hl : raw31189step2Labels = raw31189step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31189step1 raw31189step1Labels permutation9 permutation7
    mixedMoment B raw31189step2 raw31189step2Labels = mixedMoment B raw31189step3 raw31189step3Labels := by
      have ha : raw31189step3 = -raw31189step2 := by apply Matrix.ext; change ∀ i j, raw31189step3 i j = -(raw31189step2 i j); unfold raw31189step3 raw31189step2; decide +kernel
      have hl : raw31189step3Labels = raw31189step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31189step3 raw31189step3Labels = mixedMoment B raw31189step4 raw31189step4Labels := by
      have ha : raw31189step4 = raw31189step3 := by apply Matrix.ext; unfold raw31189step4 raw31189step3; decide +kernel
      have hl : raw31189step3Labels = labelEmbedding1 ∘ raw31189step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31189step3 raw31189step3Labels raw31189step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2287 node2287Labels := by rfl

theorem canonical31190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31190 raw31190Labels = mixedMoment B node2286 node2286Labels := by
  calc
    mixedMoment B raw31190 raw31190Labels = mixedMoment B raw31190step0 raw31190step0Labels := by
      have hz : ∀ j, raw31190 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31190step0 = (fun i j => raw31190 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31190step0 raw31190; decide +kernel
      have hl : raw31190step0Labels = raw31190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31190 raw31190Labels permutation434 hz
    mixedMoment B raw31190step0 raw31190step0Labels = mixedMoment B raw31190step1 raw31190step1Labels := by
      have hz : ∀ j, raw31190step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31190step1 = (fun i j => raw31190step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31190step1 raw31190step0; decide +kernel
      have hl : raw31190step1Labels = raw31190step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31190step0 raw31190step0Labels permutation80 hz
    mixedMoment B raw31190step1 raw31190step1Labels = mixedMoment B raw31190step2 raw31190step2Labels := by
      have ha : raw31190step2 = (fun i j => raw31190step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31190step2 raw31190step1; decide +kernel
      have hl : raw31190step2Labels = raw31190step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31190step1 raw31190step1Labels permutation8 permutation7
    mixedMoment B raw31190step2 raw31190step2Labels = mixedMoment B raw31190step3 raw31190step3Labels := by
      have ha : raw31190step3 = -raw31190step2 := by apply Matrix.ext; change ∀ i j, raw31190step3 i j = -(raw31190step2 i j); unfold raw31190step3 raw31190step2; decide +kernel
      have hl : raw31190step3Labels = raw31190step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31190step3 raw31190step3Labels = mixedMoment B raw31190step4 raw31190step4Labels := by
      have ha : raw31190step4 = raw31190step3 := by apply Matrix.ext; unfold raw31190step4 raw31190step3; decide +kernel
      have hl : raw31190step3Labels = labelEmbedding1 ∘ raw31190step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31190step3 raw31190step3Labels raw31190step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2286 node2286Labels := by rfl

theorem canonical31191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31191 raw31191Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw31191 raw31191Labels = mixedMoment B raw31191step0 raw31191step0Labels := by
      have hz : ∀ j, raw31191 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31191step0 = (fun i j => raw31191 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31191step0 raw31191; decide +kernel
      have hl : raw31191step0Labels = raw31191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31191 raw31191Labels permutation434 hz
    mixedMoment B raw31191step0 raw31191step0Labels = mixedMoment B raw31191step1 raw31191step1Labels := by
      have ha : raw31191step1 = (fun i j => raw31191step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31191step1 raw31191step0; decide +kernel
      have hl : raw31191step1Labels = raw31191step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31191step0 raw31191step0Labels permutation38 permutation7
    mixedMoment B raw31191step1 raw31191step1Labels = mixedMoment B raw31191step2 raw31191step2Labels := by
      have ha : raw31191step2 = -raw31191step1 := by apply Matrix.ext; change ∀ i j, raw31191step2 i j = -(raw31191step1 i j); unfold raw31191step2 raw31191step1; decide +kernel
      have hl : raw31191step2Labels = raw31191step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31191step2 raw31191step2Labels = mixedMoment B raw31191step3 raw31191step3Labels := by
      have ha : raw31191step3 = raw31191step2 := by apply Matrix.ext; unfold raw31191step3 raw31191step2; decide +kernel
      have hl : raw31191step2Labels = labelEmbedding1 ∘ raw31191step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31191step2 raw31191step2Labels raw31191step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

theorem canonical31192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31192 raw31192Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw31192 raw31192Labels = mixedMoment B raw31192step0 raw31192step0Labels := by
      have hz : ∀ j, raw31192 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31192step0 = (fun i j => raw31192 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31192step0 raw31192; decide +kernel
      have hl : raw31192step0Labels = raw31192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31192 raw31192Labels permutation346 hz
    mixedMoment B raw31192step0 raw31192step0Labels = mixedMoment B raw31192step1 raw31192step1Labels := by
      have ha : raw31192step1 = (fun i j => raw31192step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31192step1 raw31192step0; decide +kernel
      have hl : raw31192step1Labels = raw31192step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31192step0 raw31192step0Labels permutation38 permutation7
    mixedMoment B raw31192step1 raw31192step1Labels = mixedMoment B raw31192step2 raw31192step2Labels := by
      have ha : raw31192step2 = -raw31192step1 := by apply Matrix.ext; change ∀ i j, raw31192step2 i j = -(raw31192step1 i j); unfold raw31192step2 raw31192step1; decide +kernel
      have hl : raw31192step2Labels = raw31192step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31192step2 raw31192step2Labels = mixedMoment B raw31192step3 raw31192step3Labels := by
      have ha : raw31192step3 = raw31192step2 := by apply Matrix.ext; unfold raw31192step3 raw31192step2; decide +kernel
      have hl : raw31192step2Labels = labelEmbedding1 ∘ raw31192step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31192step2 raw31192step2Labels raw31192step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

theorem canonical31193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31193 raw31193Labels = mixedMoment B node3118 node3118Labels := by
  calc
    mixedMoment B raw31193 raw31193Labels = mixedMoment B raw31193step0 raw31193step0Labels := by
      have hz : ∀ j, raw31193 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31193step0 = (fun i j => raw31193 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31193step0 raw31193; decide +kernel
      have hl : raw31193step0Labels = raw31193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31193 raw31193Labels permutation434 hz
    mixedMoment B raw31193step0 raw31193step0Labels = mixedMoment B raw31193step1 raw31193step1Labels := by
      have hz : ∀ j, raw31193step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31193step1 = (fun i j => raw31193step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31193step1 raw31193step0; decide +kernel
      have hl : raw31193step1Labels = raw31193step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31193step0 raw31193step0Labels permutation80 hz
    mixedMoment B raw31193step1 raw31193step1Labels = mixedMoment B raw31193step2 raw31193step2Labels := by
      have ha : raw31193step2 = (fun i j => raw31193step1 (permutation17 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31193step2 raw31193step1; decide +kernel
      have hl : raw31193step2Labels = raw31193step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31193step1 raw31193step1Labels permutation17 permutation4
    mixedMoment B raw31193step2 raw31193step2Labels = mixedMoment B raw31193step3 raw31193step3Labels := by
      have ha : raw31193step3 = -raw31193step2 := by apply Matrix.ext; change ∀ i j, raw31193step3 i j = -(raw31193step2 i j); unfold raw31193step3 raw31193step2; decide +kernel
      have hl : raw31193step3Labels = raw31193step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3118 node3118Labels := by rfl

theorem canonical31194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31194 raw31194Labels = mixedMoment B node1827 node1827Labels := by
  calc
    mixedMoment B raw31194 raw31194Labels = mixedMoment B raw31194step0 raw31194step0Labels := by
      have hz : ∀ j, raw31194 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31194step0 = (fun i j => raw31194 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31194step0 raw31194; decide +kernel
      have hl : raw31194step0Labels = raw31194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31194 raw31194Labels permutation434 hz
    _ = mixedMoment B node1827 node1827Labels := by rfl

theorem canonical31195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31195 raw31195Labels = mixedMoment B node1827 node1827Labels := by
  calc
    mixedMoment B raw31195 raw31195Labels = mixedMoment B raw31195step0 raw31195step0Labels := by
      have hz : ∀ j, raw31195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31195step0 = (fun i j => raw31195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31195step0 raw31195; decide +kernel
      have hl : raw31195step0Labels = raw31195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31195 raw31195Labels permutation346 hz
    _ = mixedMoment B node1827 node1827Labels := by rfl

theorem canonical31196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31196 raw31196Labels = mixedMoment B node1831 node1831Labels := by
  calc
    mixedMoment B raw31196 raw31196Labels = mixedMoment B raw31196step0 raw31196step0Labels := by
      have hz : ∀ j, raw31196 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31196step0 = (fun i j => raw31196 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31196step0 raw31196; decide +kernel
      have hl : raw31196step0Labels = raw31196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31196 raw31196Labels permutation434 hz
    mixedMoment B raw31196step0 raw31196step0Labels = mixedMoment B raw31196step1 raw31196step1Labels := by
      have hz : ∀ j, raw31196step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31196step1 = (fun i j => raw31196step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31196step1 raw31196step0; decide +kernel
      have hl : raw31196step1Labels = raw31196step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31196step0 raw31196step0Labels permutation80 hz
    mixedMoment B raw31196step1 raw31196step1Labels = mixedMoment B raw31196step2 raw31196step2Labels := by
      have ha : raw31196step2 = (fun i j => raw31196step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31196step2 raw31196step1; decide +kernel
      have hl : raw31196step2Labels = raw31196step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31196step1 raw31196step1Labels permutation9 permutation2
    _ = mixedMoment B node1831 node1831Labels := by rfl

theorem canonical31197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31197 raw31197Labels = mixedMoment B node1831 node1831Labels := by
  calc
    mixedMoment B raw31197 raw31197Labels = mixedMoment B raw31197step0 raw31197step0Labels := by
      have hz : ∀ j, raw31197 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31197step0 = (fun i j => raw31197 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31197step0 raw31197; decide +kernel
      have hl : raw31197step0Labels = raw31197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31197 raw31197Labels permutation434 hz
    mixedMoment B raw31197step0 raw31197step0Labels = mixedMoment B raw31197step1 raw31197step1Labels := by
      have hz : ∀ j, raw31197step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31197step1 = (fun i j => raw31197step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31197step1 raw31197step0; decide +kernel
      have hl : raw31197step1Labels = raw31197step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31197step0 raw31197step0Labels permutation80 hz
    _ = mixedMoment B node1831 node1831Labels := by rfl

theorem canonical31198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31198 raw31198Labels = mixedMoment B node1975 node1975Labels := by
  calc
    mixedMoment B raw31198 raw31198Labels = mixedMoment B raw31198step0 raw31198step0Labels := by
      have ha : raw31198step0 = (fun i j => raw31198 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31198step0 raw31198; decide +kernel
      have hl : raw31198step0Labels = raw31198Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31198 raw31198Labels permutation200 permutation2
    _ = mixedMoment B node1975 node1975Labels := by rfl

theorem canonical31199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31199 raw31199Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw31199 raw31199Labels = mixedMoment B raw31199step0 raw31199step0Labels := by
      have hz : ∀ j, raw31199 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31199step0 = (fun i j => raw31199 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31199step0 raw31199; decide +kernel
      have hl : raw31199step0Labels = raw31199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31199 raw31199Labels permutation434 hz
    mixedMoment B raw31199step0 raw31199step0Labels = mixedMoment B raw31199step1 raw31199step1Labels := by
      have ha : raw31199step1 = (fun i j => raw31199step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31199step1 raw31199step0; decide +kernel
      have hl : raw31199step1Labels = raw31199step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31199step0 raw31199step0Labels permutation33 permutation2
    _ = mixedMoment B node2107 node2107Labels := by rfl

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

theorem canonical11398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11398 raw11398Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw11398 raw11398Labels = mixedMoment B raw11398step0 raw11398step0Labels := by
      have hz : ∀ j, raw11398 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11398step0 = (fun i j => raw11398 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11398step0 raw11398; decide +kernel
      have hl : raw11398step0Labels = raw11398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11398 raw11398Labels permutation434 hz
    mixedMoment B raw11398step0 raw11398step0Labels = mixedMoment B raw11398step1 raw11398step1Labels := by
      have hz : ∀ j, raw11398step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11398step1 = (fun i j => raw11398step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11398step1 raw11398step0; decide +kernel
      have hl : raw11398step1Labels = raw11398step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11398step0 raw11398step0Labels permutation80 hz
    mixedMoment B raw11398step1 raw11398step1Labels = mixedMoment B raw11398step2 raw11398step2Labels := by
      have ha : raw11398step2 = (fun i j => raw11398step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11398step2 raw11398step1; decide +kernel
      have hl : raw11398step2Labels = raw11398step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11398step1 raw11398step1Labels permutation8 permutation7
    mixedMoment B raw11398step2 raw11398step2Labels = mixedMoment B raw11398step3 raw11398step3Labels := by
      have ha : raw11398step3 = -raw11398step2 := by apply Matrix.ext; change ∀ i j, raw11398step3 i j = -(raw11398step2 i j); unfold raw11398step3 raw11398step2; decide +kernel
      have hl : raw11398step3Labels = raw11398step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11398step3 raw11398step3Labels = mixedMoment B raw11398step4 raw11398step4Labels := by
      have ha : raw11398step4 = raw11398step3 := by apply Matrix.ext; unfold raw11398step4 raw11398step3; decide +kernel
      have hl : raw11398step3Labels = labelEmbedding10 ∘ raw11398step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11398step3 raw11398step3Labels raw11398step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

theorem canonical11409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11409 raw11409Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw11409 raw11409Labels = mixedMoment B raw11409step0 raw11409step0Labels := by
      have hz : ∀ j, raw11409 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11409step0 = (fun i j => raw11409 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11409step0 raw11409; decide +kernel
      have hl : raw11409step0Labels = raw11409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11409 raw11409Labels permutation434 hz
    _ = mixedMoment B node4866 node4866Labels := by rfl

theorem canonical11414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11414 raw11414Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw11414 raw11414Labels = mixedMoment B raw11414step0 raw11414step0Labels := by
      have hz : ∀ j, raw11414 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11414step0 = (fun i j => raw11414 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11414step0 raw11414; decide +kernel
      have hl : raw11414step0Labels = raw11414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11414 raw11414Labels permutation346 hz
    _ = mixedMoment B node4866 node4866Labels := by rfl

theorem canonical11418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11418 raw11418Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw11418 raw11418Labels = mixedMoment B raw11418step0 raw11418step0Labels := by
      have hz : ∀ j, raw11418 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11418step0 = (fun i j => raw11418 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11418step0 raw11418; decide +kernel
      have hl : raw11418step0Labels = raw11418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11418 raw11418Labels permutation434 hz
    mixedMoment B raw11418step0 raw11418step0Labels = mixedMoment B raw11418step1 raw11418step1Labels := by
      have hz : ∀ j, raw11418step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11418step1 = (fun i j => raw11418step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11418step1 raw11418step0; decide +kernel
      have hl : raw11418step1Labels = raw11418step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11418step0 raw11418step0Labels permutation80 hz
    _ = mixedMoment B node4467 node4467Labels := by rfl

theorem canonical11420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11420 raw11420Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw11420 raw11420Labels = mixedMoment B raw11420step0 raw11420step0Labels := by
      have hz : ∀ j, raw11420 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11420step0 = (fun i j => raw11420 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11420step0 raw11420; decide +kernel
      have hl : raw11420step0Labels = raw11420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11420 raw11420Labels permutation434 hz
    mixedMoment B raw11420step0 raw11420step0Labels = mixedMoment B raw11420step1 raw11420step1Labels := by
      have ha : raw11420step1 = (fun i j => raw11420step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11420step1 raw11420step0; decide +kernel
      have hl : raw11420step1Labels = raw11420step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11420step0 raw11420step0Labels permutation38 permutation2
    _ = mixedMoment B node4811 node4811Labels := by rfl

theorem canonical11421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11421 raw11421Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw11421 raw11421Labels = mixedMoment B raw11421step0 raw11421step0Labels := by
      have hz : ∀ j, raw11421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11421step0 = (fun i j => raw11421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11421step0 raw11421; decide +kernel
      have hl : raw11421step0Labels = raw11421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11421 raw11421Labels permutation346 hz
    mixedMoment B raw11421step0 raw11421step0Labels = mixedMoment B raw11421step1 raw11421step1Labels := by
      have ha : raw11421step1 = (fun i j => raw11421step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11421step1 raw11421step0; decide +kernel
      have hl : raw11421step1Labels = raw11421step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11421step0 raw11421step0Labels permutation38 permutation2
    _ = mixedMoment B node4811 node4811Labels := by rfl

theorem canonical11422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11422 raw11422Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw11422 raw11422Labels = mixedMoment B raw11422step0 raw11422step0Labels := by
      have hz : ∀ j, raw11422 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11422step0 = (fun i j => raw11422 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11422step0 raw11422; decide +kernel
      have hl : raw11422step0Labels = raw11422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11422 raw11422Labels permutation434 hz
    mixedMoment B raw11422step0 raw11422step0Labels = mixedMoment B raw11422step1 raw11422step1Labels := by
      have hz : ∀ j, raw11422step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11422step1 = (fun i j => raw11422step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11422step1 raw11422step0; decide +kernel
      have hl : raw11422step1Labels = raw11422step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11422step0 raw11422step0Labels permutation80 hz
    mixedMoment B raw11422step1 raw11422step1Labels = mixedMoment B raw11422step2 raw11422step2Labels := by
      have ha : raw11422step2 = (fun i j => raw11422step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11422step2 raw11422step1; decide +kernel
      have hl : raw11422step2Labels = raw11422step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11422step1 raw11422step1Labels permutation9 permutation2
    _ = mixedMoment B node4895 node4895Labels := by rfl

theorem canonical11424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11424 raw11424Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw11424 raw11424Labels = mixedMoment B raw11424step0 raw11424step0Labels := by
      have hz : ∀ j, raw11424 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11424step0 = (fun i j => raw11424 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11424step0 raw11424; decide +kernel
      have hl : raw11424step0Labels = raw11424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11424 raw11424Labels permutation434 hz
    mixedMoment B raw11424step0 raw11424step0Labels = mixedMoment B raw11424step1 raw11424step1Labels := by
      have hz : ∀ j, raw11424step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11424step1 = (fun i j => raw11424step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11424step1 raw11424step0; decide +kernel
      have hl : raw11424step1Labels = raw11424step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11424step0 raw11424step0Labels permutation80 hz
    _ = mixedMoment B node4871 node4871Labels := by rfl

theorem canonical11428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11428 raw11428Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw11428 raw11428Labels = mixedMoment B raw11428step0 raw11428step0Labels := by
      have hz : ∀ j, raw11428 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11428step0 = (fun i j => raw11428 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11428step0 raw11428; decide +kernel
      have hl : raw11428step0Labels = raw11428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11428 raw11428Labels permutation434 hz
    mixedMoment B raw11428step0 raw11428step0Labels = mixedMoment B raw11428step1 raw11428step1Labels := by
      have hz : ∀ j, raw11428step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11428step1 = (fun i j => raw11428step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11428step1 raw11428step0; decide +kernel
      have hl : raw11428step1Labels = raw11428step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11428step0 raw11428step0Labels permutation80 hz
    mixedMoment B raw11428step1 raw11428step1Labels = mixedMoment B raw11428step2 raw11428step2Labels := by
      have ha : raw11428step2 = (fun i j => raw11428step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11428step2 raw11428step1; decide +kernel
      have hl : raw11428step2Labels = raw11428step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11428step1 raw11428step1Labels permutation8 permutation7
    mixedMoment B raw11428step2 raw11428step2Labels = mixedMoment B raw11428step3 raw11428step3Labels := by
      have ha : raw11428step3 = -raw11428step2 := by apply Matrix.ext; change ∀ i j, raw11428step3 i j = -(raw11428step2 i j); unfold raw11428step3 raw11428step2; decide +kernel
      have hl : raw11428step3Labels = raw11428step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11428step3 raw11428step3Labels = mixedMoment B raw11428step4 raw11428step4Labels := by
      have ha : raw11428step4 = raw11428step3 := by apply Matrix.ext; unfold raw11428step4 raw11428step3; decide +kernel
      have hl : raw11428step3Labels = labelEmbedding1 ∘ raw11428step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11428step3 raw11428step3Labels raw11428step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2782 node2782Labels := by rfl

theorem canonical11439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11439 raw11439Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw11439 raw11439Labels = mixedMoment B raw11439step0 raw11439step0Labels := by
      have hz : ∀ j, raw11439 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11439step0 = (fun i j => raw11439 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11439step0 raw11439; decide +kernel
      have hl : raw11439step0Labels = raw11439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11439 raw11439Labels permutation434 hz
    mixedMoment B raw11439step0 raw11439step0Labels = mixedMoment B raw11439step1 raw11439step1Labels := by
      have ha : raw11439step1 = (fun i j => raw11439step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11439step1 raw11439step0; decide +kernel
      have hl : raw11439step1Labels = raw11439step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11439step0 raw11439step0Labels permutation38 permutation7
    mixedMoment B raw11439step1 raw11439step1Labels = mixedMoment B raw11439step2 raw11439step2Labels := by
      have ha : raw11439step2 = -raw11439step1 := by apply Matrix.ext; change ∀ i j, raw11439step2 i j = -(raw11439step1 i j); unfold raw11439step2 raw11439step1; decide +kernel
      have hl : raw11439step2Labels = raw11439step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11439step2 raw11439step2Labels = mixedMoment B raw11439step3 raw11439step3Labels := by
      have ha : raw11439step3 = raw11439step2 := by apply Matrix.ext; unfold raw11439step3 raw11439step2; decide +kernel
      have hl : raw11439step2Labels = labelEmbedding1 ∘ raw11439step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11439step2 raw11439step2Labels raw11439step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical11444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11444 raw11444Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw11444 raw11444Labels = mixedMoment B raw11444step0 raw11444step0Labels := by
      have hz : ∀ j, raw11444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11444step0 = (fun i j => raw11444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11444step0 raw11444; decide +kernel
      have hl : raw11444step0Labels = raw11444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11444 raw11444Labels permutation346 hz
    mixedMoment B raw11444step0 raw11444step0Labels = mixedMoment B raw11444step1 raw11444step1Labels := by
      have ha : raw11444step1 = (fun i j => raw11444step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11444step1 raw11444step0; decide +kernel
      have hl : raw11444step1Labels = raw11444step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11444step0 raw11444step0Labels permutation38 permutation7
    mixedMoment B raw11444step1 raw11444step1Labels = mixedMoment B raw11444step2 raw11444step2Labels := by
      have ha : raw11444step2 = -raw11444step1 := by apply Matrix.ext; change ∀ i j, raw11444step2 i j = -(raw11444step1 i j); unfold raw11444step2 raw11444step1; decide +kernel
      have hl : raw11444step2Labels = raw11444step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11444step2 raw11444step2Labels = mixedMoment B raw11444step3 raw11444step3Labels := by
      have ha : raw11444step3 = raw11444step2 := by apply Matrix.ext; unfold raw11444step3 raw11444step2; decide +kernel
      have hl : raw11444step2Labels = labelEmbedding1 ∘ raw11444step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11444step2 raw11444step2Labels raw11444step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

theorem canonical11448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11448 raw11448Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw11448 raw11448Labels = mixedMoment B raw11448step0 raw11448step0Labels := by
      have hz : ∀ j, raw11448 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11448step0 = (fun i j => raw11448 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11448step0 raw11448; decide +kernel
      have hl : raw11448step0Labels = raw11448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11448 raw11448Labels permutation434 hz
    mixedMoment B raw11448step0 raw11448step0Labels = mixedMoment B raw11448step1 raw11448step1Labels := by
      have hz : ∀ j, raw11448step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11448step1 = (fun i j => raw11448step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11448step1 raw11448step0; decide +kernel
      have hl : raw11448step1Labels = raw11448step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11448step0 raw11448step0Labels permutation80 hz
    mixedMoment B raw11448step1 raw11448step1Labels = mixedMoment B raw11448step2 raw11448step2Labels := by
      have ha : raw11448step2 = (fun i j => raw11448step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11448step2 raw11448step1; decide +kernel
      have hl : raw11448step2Labels = raw11448step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11448step1 raw11448step1Labels permutation8 permutation7
    mixedMoment B raw11448step2 raw11448step2Labels = mixedMoment B raw11448step3 raw11448step3Labels := by
      have ha : raw11448step3 = -raw11448step2 := by apply Matrix.ext; change ∀ i j, raw11448step3 i j = -(raw11448step2 i j); unfold raw11448step3 raw11448step2; decide +kernel
      have hl : raw11448step3Labels = raw11448step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11448step3 raw11448step3Labels = mixedMoment B raw11448step4 raw11448step4Labels := by
      have ha : raw11448step4 = raw11448step3 := by apply Matrix.ext; unfold raw11448step4 raw11448step3; decide +kernel
      have hl : raw11448step3Labels = labelEmbedding1 ∘ raw11448step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11448step3 raw11448step3Labels raw11448step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1751 node1751Labels := by rfl

theorem canonical11450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11450 raw11450Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw11450 raw11450Labels = mixedMoment B raw11450step0 raw11450step0Labels := by
      have hz : ∀ j, raw11450 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11450step0 = (fun i j => raw11450 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11450step0 raw11450; decide +kernel
      have hl : raw11450step0Labels = raw11450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11450 raw11450Labels permutation434 hz
    mixedMoment B raw11450step0 raw11450step0Labels = mixedMoment B raw11450step1 raw11450step1Labels := by
      have ha : raw11450step1 = (fun i j => raw11450step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11450step1 raw11450step0; decide +kernel
      have hl : raw11450step1Labels = raw11450step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11450step0 raw11450step0Labels permutation38 permutation7
    mixedMoment B raw11450step1 raw11450step1Labels = mixedMoment B raw11450step2 raw11450step2Labels := by
      have ha : raw11450step2 = -raw11450step1 := by apply Matrix.ext; change ∀ i j, raw11450step2 i j = -(raw11450step1 i j); unfold raw11450step2 raw11450step1; decide +kernel
      have hl : raw11450step2Labels = raw11450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11450step2 raw11450step2Labels = mixedMoment B raw11450step3 raw11450step3Labels := by
      have ha : raw11450step3 = raw11450step2 := by apply Matrix.ext; unfold raw11450step3 raw11450step2; decide +kernel
      have hl : raw11450step2Labels = labelEmbedding1 ∘ raw11450step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11450step2 raw11450step2Labels raw11450step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2225 node2225Labels := by rfl

theorem canonical11451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11451 raw11451Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw11451 raw11451Labels = mixedMoment B raw11451step0 raw11451step0Labels := by
      have hz : ∀ j, raw11451 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11451step0 = (fun i j => raw11451 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11451step0 raw11451; decide +kernel
      have hl : raw11451step0Labels = raw11451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11451 raw11451Labels permutation346 hz
    mixedMoment B raw11451step0 raw11451step0Labels = mixedMoment B raw11451step1 raw11451step1Labels := by
      have ha : raw11451step1 = (fun i j => raw11451step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11451step1 raw11451step0; decide +kernel
      have hl : raw11451step1Labels = raw11451step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11451step0 raw11451step0Labels permutation38 permutation7
    mixedMoment B raw11451step1 raw11451step1Labels = mixedMoment B raw11451step2 raw11451step2Labels := by
      have ha : raw11451step2 = -raw11451step1 := by apply Matrix.ext; change ∀ i j, raw11451step2 i j = -(raw11451step1 i j); unfold raw11451step2 raw11451step1; decide +kernel
      have hl : raw11451step2Labels = raw11451step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11451step2 raw11451step2Labels = mixedMoment B raw11451step3 raw11451step3Labels := by
      have ha : raw11451step3 = raw11451step2 := by apply Matrix.ext; unfold raw11451step3 raw11451step2; decide +kernel
      have hl : raw11451step2Labels = labelEmbedding1 ∘ raw11451step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11451step2 raw11451step2Labels raw11451step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2225 node2225Labels := by rfl

theorem canonical11452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11452 raw11452Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw11452 raw11452Labels = mixedMoment B raw11452step0 raw11452step0Labels := by
      have hz : ∀ j, raw11452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11452step0 = (fun i j => raw11452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11452step0 raw11452; decide +kernel
      have hl : raw11452step0Labels = raw11452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11452 raw11452Labels permutation434 hz
    mixedMoment B raw11452step0 raw11452step0Labels = mixedMoment B raw11452step1 raw11452step1Labels := by
      have hz : ∀ j, raw11452step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11452step1 = (fun i j => raw11452step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11452step1 raw11452step0; decide +kernel
      have hl : raw11452step1Labels = raw11452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11452step0 raw11452step0Labels permutation80 hz
    mixedMoment B raw11452step1 raw11452step1Labels = mixedMoment B raw11452step2 raw11452step2Labels := by
      have ha : raw11452step2 = (fun i j => raw11452step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11452step2 raw11452step1; decide +kernel
      have hl : raw11452step2Labels = raw11452step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11452step1 raw11452step1Labels permutation9 permutation7
    mixedMoment B raw11452step2 raw11452step2Labels = mixedMoment B raw11452step3 raw11452step3Labels := by
      have ha : raw11452step3 = -raw11452step2 := by apply Matrix.ext; change ∀ i j, raw11452step3 i j = -(raw11452step2 i j); unfold raw11452step3 raw11452step2; decide +kernel
      have hl : raw11452step3Labels = raw11452step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11452step3 raw11452step3Labels = mixedMoment B raw11452step4 raw11452step4Labels := by
      have ha : raw11452step4 = raw11452step3 := by apply Matrix.ext; unfold raw11452step4 raw11452step3; decide +kernel
      have hl : raw11452step3Labels = labelEmbedding1 ∘ raw11452step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11452step3 raw11452step3Labels raw11452step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

theorem canonical11454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11454 raw11454Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw11454 raw11454Labels = mixedMoment B raw11454step0 raw11454step0Labels := by
      have hz : ∀ j, raw11454 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11454step0 = (fun i j => raw11454 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11454step0 raw11454; decide +kernel
      have hl : raw11454step0Labels = raw11454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11454 raw11454Labels permutation434 hz
    mixedMoment B raw11454step0 raw11454step0Labels = mixedMoment B raw11454step1 raw11454step1Labels := by
      have hz : ∀ j, raw11454step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11454step1 = (fun i j => raw11454step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11454step1 raw11454step0; decide +kernel
      have hl : raw11454step1Labels = raw11454step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11454step0 raw11454step0Labels permutation80 hz
    mixedMoment B raw11454step1 raw11454step1Labels = mixedMoment B raw11454step2 raw11454step2Labels := by
      have ha : raw11454step2 = (fun i j => raw11454step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11454step2 raw11454step1; decide +kernel
      have hl : raw11454step2Labels = raw11454step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11454step1 raw11454step1Labels permutation8 permutation7
    mixedMoment B raw11454step2 raw11454step2Labels = mixedMoment B raw11454step3 raw11454step3Labels := by
      have ha : raw11454step3 = -raw11454step2 := by apply Matrix.ext; change ∀ i j, raw11454step3 i j = -(raw11454step2 i j); unfold raw11454step3 raw11454step2; decide +kernel
      have hl : raw11454step3Labels = raw11454step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11454step3 raw11454step3Labels = mixedMoment B raw11454step4 raw11454step4Labels := by
      have ha : raw11454step4 = raw11454step3 := by apply Matrix.ext; unfold raw11454step4 raw11454step3; decide +kernel
      have hl : raw11454step3Labels = labelEmbedding1 ∘ raw11454step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11454step3 raw11454step3Labels raw11454step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2287 node2287Labels := by rfl

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

theorem singleton4871 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4871 node4871Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2112 node2112Labels + mixedMoment B node2287 node2287Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1803 singletonSmall4871
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4871) = raw1803Labels := by decide +kernel
  rw [hl, canonical1803 B hB] at h
  have hc0 : mixedMoment B raw1803 (Fin.cases (0 : Fin 2) singletonSmall4871) =
      mixedMoment B node2112 node2112Labels := by
    have ha : raw1803 = raw1804 := by apply Matrix.ext; unfold raw1803 raw1804; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4871 = raw1804Labels := by decide +kernel
    rw [ha, hj, canonical1804 B hB]
  have hc1 : mixedMoment B raw1803 (Fin.cases (1 : Fin 2) singletonSmall4871) =
      mixedMoment B node2287 node2287Labels := by
    have ha : raw1803 = raw1805 := by apply Matrix.ext; unfold raw1803 raw1805; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4871 = raw1805Labels := by decide +kernel
    rw [ha, hj, canonical1805 B hB]
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

theorem singleton5304 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5304 node5304Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2782 node2782Labels + mixedMoment B node3583 node3583Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2316 singletonSmall5304
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5304) = raw2316Labels := by decide +kernel
  rw [hl, canonical2316 B hB] at h
  have hc0 : mixedMoment B raw2316 (Fin.cases (0 : Fin 2) singletonSmall5304) =
      mixedMoment B node2782 node2782Labels := by
    have ha : raw2316 = raw2317 := by apply Matrix.ext; unfold raw2316 raw2317; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5304 = raw2317Labels := by decide +kernel
    rw [ha, hj, canonical2317 B hB]
  have hc1 : mixedMoment B raw2316 (Fin.cases (1 : Fin 2) singletonSmall5304) =
      mixedMoment B node3583 node3583Labels := by
    have ha : raw2316 = raw2318 := by apply Matrix.ext; unfold raw2316 raw2318; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5304 = raw2318Labels := by decide +kernel
    rw [ha, hj, canonical2318 B hB]
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

theorem sound946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node946 node946Labels = Sparse.eval nodeValue946 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 946) = mixedMoment B node946 node946Labels := rfl
  simpa [nodeValue946, Sparse.eval] using hc.symm

theorem sound947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node947 node947Labels = Sparse.eval nodeValue947 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 947) = mixedMoment B node947 node947Labels := rfl
  simpa [nodeValue947, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1712 node1712Labels = Sparse.eval nodeValue1712 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1712) = mixedMoment B node1712 node1712Labels := rfl
  simpa [nodeValue1712, Sparse.eval] using hc.symm

theorem sound1721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1721 node1721Labels = Sparse.eval nodeValue1721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1721) = mixedMoment B node1721 node1721Labels := rfl
  simpa [nodeValue1721, Sparse.eval] using hc.symm

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

theorem sound1735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1735 node1735Labels = Sparse.eval nodeValue1735 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1735) = mixedMoment B node1735 node1735Labels := rfl
  simpa [nodeValue1735, Sparse.eval] using hc.symm

theorem sound1738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1738 node1738Labels = Sparse.eval nodeValue1738 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1738) = mixedMoment B node1738 node1738Labels := rfl
  simpa [nodeValue1738, Sparse.eval] using hc.symm

theorem sound1743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1743 node1743Labels = Sparse.eval nodeValue1743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1743) = mixedMoment B node1743 node1743Labels := rfl
  simpa [nodeValue1743, Sparse.eval] using hc.symm

theorem sound1748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1748 node1748Labels = Sparse.eval nodeValue1748 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1748) = mixedMoment B node1748 node1748Labels := rfl
  simpa [nodeValue1748, Sparse.eval] using hc.symm

theorem sound1751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1751 node1751Labels = Sparse.eval nodeValue1751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1751) = mixedMoment B node1751 node1751Labels := rfl
  simpa [nodeValue1751, Sparse.eval] using hc.symm

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

theorem sound1826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1826 node1826Labels = Sparse.eval nodeValue1826 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1826) = mixedMoment B node1826 node1826Labels := rfl
  simpa [nodeValue1826, Sparse.eval] using hc.symm

theorem sound1827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1827 node1827Labels = Sparse.eval nodeValue1827 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1827) = mixedMoment B node1827 node1827Labels := rfl
  simpa [nodeValue1827, Sparse.eval] using hc.symm

theorem sound1830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1830 node1830Labels = Sparse.eval nodeValue1830 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1830) = mixedMoment B node1830 node1830Labels := rfl
  simpa [nodeValue1830, Sparse.eval] using hc.symm

theorem sound1831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1831 node1831Labels = Sparse.eval nodeValue1831 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1831) = mixedMoment B node1831 node1831Labels := rfl
  simpa [nodeValue1831, Sparse.eval] using hc.symm

theorem sound1832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1832 node1832Labels = Sparse.eval nodeValue1832 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1832) = mixedMoment B node1832 node1832Labels := rfl
  simpa [nodeValue1832, Sparse.eval] using hc.symm

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

theorem sound2029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2029 node2029Labels = Sparse.eval nodeValue2029 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2029) = mixedMoment B node2029 node2029Labels := rfl
  simpa [nodeValue2029, Sparse.eval] using hc.symm

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

theorem sound2108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2108 node2108Labels = Sparse.eval nodeValue2108 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2108) = mixedMoment B node2108 node2108Labels := rfl
  simpa [nodeValue2108, Sparse.eval] using hc.symm

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

theorem sound2115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2115 node2115Labels = Sparse.eval nodeValue2115 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2115) = mixedMoment B node2115 node2115Labels := rfl
  simpa [nodeValue2115, Sparse.eval] using hc.symm

theorem sound2116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2116 node2116Labels = Sparse.eval nodeValue2116 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2116) = mixedMoment B node2116 node2116Labels := rfl
  simpa [nodeValue2116, Sparse.eval] using hc.symm

theorem sound2162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2162 node2162Labels = Sparse.eval nodeValue2162 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2162) = mixedMoment B node2162 node2162Labels := rfl
  simpa [nodeValue2162, Sparse.eval] using hc.symm

theorem sound2163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2163 node2163Labels = Sparse.eval nodeValue2163 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2163) = mixedMoment B node2163 node2163Labels := rfl
  simpa [nodeValue2163, Sparse.eval] using hc.symm

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

theorem sound2194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2194 node2194Labels = Sparse.eval nodeValue2194 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2194) = mixedMoment B node2194 node2194Labels := rfl
  simpa [nodeValue2194, Sparse.eval] using hc.symm

theorem sound2199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2199 node2199Labels = Sparse.eval nodeValue2199 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2199) = mixedMoment B node2199 node2199Labels := rfl
  simpa [nodeValue2199, Sparse.eval] using hc.symm

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

theorem sound2223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2223 node2223Labels = Sparse.eval nodeValue2223 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2223) = mixedMoment B node2223 node2223Labels := rfl
  simpa [nodeValue2223, Sparse.eval] using hc.symm

theorem sound2225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2225 node2225Labels = Sparse.eval nodeValue2225 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2225) = mixedMoment B node2225 node2225Labels := rfl
  simpa [nodeValue2225, Sparse.eval] using hc.symm

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

theorem sound2242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2242 node2242Labels = Sparse.eval nodeValue2242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2242) = mixedMoment B node2242 node2242Labels := rfl
  simpa [nodeValue2242, Sparse.eval] using hc.symm

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

theorem sound2257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2257 node2257Labels = Sparse.eval nodeValue2257 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2257) = mixedMoment B node2257 node2257Labels := rfl
  simpa [nodeValue2257, Sparse.eval] using hc.symm

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

theorem sound2264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = Sparse.eval nodeValue2264 (mixedVector B) := by
  simpa only [nodeValue2264, Sparse.eval_nil] using zero2264 B _hB _hF

theorem sound2273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2273 node2273Labels = Sparse.eval nodeValue2273 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2273) = mixedMoment B node2273 node2273Labels := rfl
  simpa [nodeValue2273, Sparse.eval] using hc.symm

theorem sound2278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2278 node2278Labels = Sparse.eval nodeValue2278 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2278) = mixedMoment B node2278 node2278Labels := rfl
  simpa [nodeValue2278, Sparse.eval] using hc.symm

theorem sound2282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2282 node2282Labels = Sparse.eval nodeValue2282 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2282) = mixedMoment B node2282 node2282Labels := rfl
  simpa [nodeValue2282, Sparse.eval] using hc.symm

theorem sound2286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2286 node2286Labels = Sparse.eval nodeValue2286 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2286) = mixedMoment B node2286 node2286Labels := rfl
  simpa [nodeValue2286, Sparse.eval] using hc.symm

theorem sound2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2287 node2287Labels = Sparse.eval nodeValue2287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2287) = mixedMoment B node2287 node2287Labels := rfl
  simpa [nodeValue2287, Sparse.eval] using hc.symm

theorem sound2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = Sparse.eval nodeValue2291 (mixedVector B) := by
  simpa only [nodeValue2291, Sparse.eval_nil] using zero2291 B _hB _hF

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

theorem sound2729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2729 node2729Labels = Sparse.eval nodeValue2729 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2729) = mixedMoment B node2729 node2729Labels := rfl
  simpa [nodeValue2729, Sparse.eval] using hc.symm

theorem sound2736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2736 node2736Labels = Sparse.eval nodeValue2736 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2736) = mixedMoment B node2736 node2736Labels := rfl
  simpa [nodeValue2736, Sparse.eval] using hc.symm

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

theorem sound2771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2771 node2771Labels = Sparse.eval nodeValue2771 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2771) = mixedMoment B node2771 node2771Labels := rfl
  simpa [nodeValue2771, Sparse.eval] using hc.symm

theorem sound2774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2774 node2774Labels = Sparse.eval nodeValue2774 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2774) = mixedMoment B node2774 node2774Labels := rfl
  simpa [nodeValue2774, Sparse.eval] using hc.symm

theorem sound2779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2779 node2779Labels = Sparse.eval nodeValue2779 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2779) = mixedMoment B node2779 node2779Labels := rfl
  simpa [nodeValue2779, Sparse.eval] using hc.symm

theorem sound2782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2782 node2782Labels = Sparse.eval nodeValue2782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2782) = mixedMoment B node2782 node2782Labels := rfl
  simpa [nodeValue2782, Sparse.eval] using hc.symm

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

theorem sound3056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3056 node3056Labels = Sparse.eval nodeValue3056 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3056) = mixedMoment B node3056 node3056Labels := rfl
  simpa [nodeValue3056, Sparse.eval] using hc.symm

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

theorem sound3118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3118 node3118Labels = Sparse.eval nodeValue3118 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3118) = mixedMoment B node3118 node3118Labels := rfl
  simpa [nodeValue3118, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4369 node4369Labels = Sparse.eval nodeValue4369 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4369) = mixedMoment B node4369 node4369Labels := rfl
  simpa [nodeValue4369, Sparse.eval] using hc.symm

theorem sound4374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4374 node4374Labels = Sparse.eval nodeValue4374 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4374) = mixedMoment B node4374 node4374Labels := rfl
  simpa [nodeValue4374, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4701 node4701Labels = Sparse.eval nodeValue4701 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4701) = mixedMoment B node4701 node4701Labels := rfl
  simpa [nodeValue4701, Sparse.eval] using hc.symm

theorem sound4705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4705 node4705Labels = Sparse.eval nodeValue4705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4705) = mixedMoment B node4705 node4705Labels := rfl
  simpa [nodeValue4705, Sparse.eval] using hc.symm

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

theorem sound4866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4866 node4866Labels = Sparse.eval nodeValue4866 (mixedVector B) := by
  have h := singleton4866 B _hB
  rw [sound2107 B _hB _hF, sound2260 B _hB _hF] at h
  norm_num [nodeValue4866, nodeValue2107, nodeValue2260, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4871 node4871Labels = Sparse.eval nodeValue4871 (mixedVector B) := by
  have h := singleton4871 B _hB
  rw [sound2112 B _hB _hF, sound2287 B _hB _hF] at h
  norm_num [nodeValue4871, nodeValue2112, nodeValue2287, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4895 node4895Labels = Sparse.eval nodeValue4895 (mixedVector B) := by
  simpa only [nodeValue4895, Sparse.eval_nil] using zero4895 B _hB _hF

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

theorem sound5303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5303 node5303Labels = Sparse.eval nodeValue5303 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5303) = mixedMoment B node5303 node5303Labels := rfl
  simpa [nodeValue5303, Sparse.eval] using hc.symm

theorem sound5304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5304 node5304Labels = Sparse.eval nodeValue5304 (mixedVector B) := by
  have h := singleton5304 B _hB
  rw [sound2782 B _hB _hF, sound3583 B _hB _hF] at h
  norm_num [nodeValue5304, nodeValue2782, nodeValue3583, Sparse.eval] at h ⊢
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

theorem sourceEq2253 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2253 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2253 + difference 0 1) (sourceB2253 + difference 1 0) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2771) := by
    have ha : (tripleCharges (sourceA2253 + difference 0 1) (sourceB2253 + difference 1 0) sourceC2253) = raw30980 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30980; decide +kernel
    rw [ha]
    exact (canonical30980 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2253 + difference 0 2) (sourceB2253 + difference 2 0) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA2253 + difference 0 2) (sourceB2253 + difference 2 0) sourceC2253) = raw30981 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30981; decide +kernel
    rw [ha]
    exact (canonical30981 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2253 + difference 0 3) (sourceB2253 + difference 3 0) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA2253 + difference 0 3) (sourceB2253 + difference 3 0) sourceC2253) = raw30982 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30982; decide +kernel
    rw [ha]
    exact (canonical30982 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2253 + difference 0 4) (sourceB2253 + difference 4 0) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA2253 + difference 0 4) (sourceB2253 + difference 4 0) sourceC2253) = raw30983 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30983; decide +kernel
    rw [ha]
    exact (canonical30983 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2253 + difference 0 5) (sourceB2253 + difference 5 0) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA2253 + difference 0 5) (sourceB2253 + difference 5 0) sourceC2253) = raw30984 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30984; decide +kernel
    rw [ha]
    exact (canonical30984 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2253 + difference 1 0) (sourceB2253 + difference 0 1) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA2253 + difference 1 0) (sourceB2253 + difference 0 1) sourceC2253) = raw30985 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30985; decide +kernel
    rw [ha]
    exact (canonical30985 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2253 + difference 1 2) (sourceB2253 + difference 2 1) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2253 + difference 1 2) (sourceB2253 + difference 2 1) sourceC2253) = raw22988 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw22988; decide +kernel
    rw [ha]
    exact (canonical22988 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2253 + difference 1 3) (sourceB2253 + difference 3 1) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2253 + difference 1 3) (sourceB2253 + difference 3 1) sourceC2253) = raw22989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw22989; decide +kernel
    rw [ha]
    exact (canonical22989 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2253 + difference 1 4) (sourceB2253 + difference 4 1) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA2253 + difference 1 4) (sourceB2253 + difference 4 1) sourceC2253) = raw22990 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw22990; decide +kernel
    rw [ha]
    exact (canonical22990 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2253 + difference 1 5) (sourceB2253 + difference 5 1) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA2253 + difference 1 5) (sourceB2253 + difference 5 1) sourceC2253) = raw22991 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw22991; decide +kernel
    rw [ha]
    exact (canonical22991 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2253 + difference 2 0) (sourceB2253 + difference 0 2) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1712) := by
    have ha : (tripleCharges (sourceA2253 + difference 2 0) (sourceB2253 + difference 0 2) sourceC2253) = raw22998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw22998; decide +kernel
    rw [ha]
    exact (canonical22998 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2253 + difference 2 1) (sourceB2253 + difference 1 2) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2249) := by
    have ha : (tripleCharges (sourceA2253 + difference 2 1) (sourceB2253 + difference 1 2) sourceC2253) = raw30986 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30986; decide +kernel
    rw [ha]
    exact (canonical30986 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2253 + difference 2 3) (sourceB2253 + difference 3 2) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2194) := by
    have ha : (tripleCharges (sourceA2253 + difference 2 3) (sourceB2253 + difference 3 2) sourceC2253) = raw30987 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30987; decide +kernel
    rw [ha]
    exact (canonical30987 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2253 + difference 2 4) (sourceB2253 + difference 4 2) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA2253 + difference 2 4) (sourceB2253 + difference 4 2) sourceC2253) = raw30988 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30988; decide +kernel
    rw [ha]
    exact (canonical30988 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2253 + difference 2 5) (sourceB2253 + difference 5 2) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA2253 + difference 2 5) (sourceB2253 + difference 5 2) sourceC2253) = raw30989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30989; decide +kernel
    rw [ha]
    exact (canonical30989 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2253 + difference 3 0) (sourceB2253 + difference 0 3) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1712) := by
    have ha : (tripleCharges (sourceA2253 + difference 3 0) (sourceB2253 + difference 0 3) sourceC2253) = raw23003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw23003; decide +kernel
    rw [ha]
    exact (canonical23003 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2253 + difference 3 1) (sourceB2253 + difference 1 3) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2249) := by
    have ha : (tripleCharges (sourceA2253 + difference 3 1) (sourceB2253 + difference 1 3) sourceC2253) = raw30990 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30990; decide +kernel
    rw [ha]
    exact (canonical30990 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2253 + difference 3 2) (sourceB2253 + difference 2 3) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2194) := by
    have ha : (tripleCharges (sourceA2253 + difference 3 2) (sourceB2253 + difference 2 3) sourceC2253) = raw30991 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30991; decide +kernel
    rw [ha]
    exact (canonical30991 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2253 + difference 3 4) (sourceB2253 + difference 4 3) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA2253 + difference 3 4) (sourceB2253 + difference 4 3) sourceC2253) = raw30992 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30992; decide +kernel
    rw [ha]
    exact (canonical30992 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2253 + difference 3 5) (sourceB2253 + difference 5 3) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA2253 + difference 3 5) (sourceB2253 + difference 5 3) sourceC2253) = raw30993 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30993; decide +kernel
    rw [ha]
    exact (canonical30993 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2253 + difference 4 0) (sourceB2253 + difference 0 4) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1735) := by
    have ha : (tripleCharges (sourceA2253 + difference 4 0) (sourceB2253 + difference 0 4) sourceC2253) = raw23008 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw23008; decide +kernel
    rw [ha]
    exact (canonical23008 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2253 + difference 4 1) (sourceB2253 + difference 1 4) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2273) := by
    have ha : (tripleCharges (sourceA2253 + difference 4 1) (sourceB2253 + difference 1 4) sourceC2253) = raw30994 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30994; decide +kernel
    rw [ha]
    exact (canonical30994 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2253 + difference 4 2) (sourceB2253 + difference 2 4) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2212) := by
    have ha : (tripleCharges (sourceA2253 + difference 4 2) (sourceB2253 + difference 2 4) sourceC2253) = raw30995 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30995; decide +kernel
    rw [ha]
    exact (canonical30995 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2253 + difference 4 3) (sourceB2253 + difference 3 4) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2212) := by
    have ha : (tripleCharges (sourceA2253 + difference 4 3) (sourceB2253 + difference 3 4) sourceC2253) = raw30996 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30996; decide +kernel
    rw [ha]
    exact (canonical30996 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2253 + difference 4 5) (sourceB2253 + difference 5 4) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA2253 + difference 4 5) (sourceB2253 + difference 5 4) sourceC2253) = raw30997 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30997; decide +kernel
    rw [ha]
    exact (canonical30997 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2253 + difference 5 0) (sourceB2253 + difference 0 5) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1743) := by
    have ha : (tripleCharges (sourceA2253 + difference 5 0) (sourceB2253 + difference 0 5) sourceC2253) = raw23013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw23013; decide +kernel
    rw [ha]
    exact (canonical23013 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2253 + difference 5 1) (sourceB2253 + difference 1 5) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2163) := by
    have ha : (tripleCharges (sourceA2253 + difference 5 1) (sourceB2253 + difference 1 5) sourceC2253) = raw30998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30998; decide +kernel
    rw [ha]
    exact (canonical30998 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2253 + difference 5 2) (sourceB2253 + difference 2 5) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2162) := by
    have ha : (tripleCharges (sourceA2253 + difference 5 2) (sourceB2253 + difference 2 5) sourceC2253) = raw30999 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30999; decide +kernel
    rw [ha]
    exact (canonical30999 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2253 + difference 5 3) (sourceB2253 + difference 3 5) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2162) := by
    have ha : (tripleCharges (sourceA2253 + difference 5 3) (sourceB2253 + difference 3 5) sourceC2253) = raw31000 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw31000; decide +kernel
    rw [ha]
    exact (canonical31000 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2253 + difference 5 4) (sourceB2253 + difference 4 5) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2282) := by
    have ha : (tripleCharges (sourceA2253 + difference 5 4) (sourceB2253 + difference 4 5) sourceC2253) = raw31001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw31001; decide +kernel
    rw [ha]
    exact (canonical31001 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2253 sourceB2253 sourceC2253
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2253, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2254 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2254 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2254 + difference 0 1) (sourceB2254 + difference 1 0) sourceC2254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3056) := by
    have ha : (tripleCharges (sourceA2254 + difference 0 1) (sourceB2254 + difference 1 0) sourceC2254) = raw31002 := by
      apply Matrix.ext; unfold tripleCharges sourceA2254 sourceB2254 sourceC2254 difference raw31002; decide +kernel
    rw [ha]
    exact (canonical31002 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2254 + difference 1 1) (sourceB2254 + difference 1 1) sourceC2254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA2254 + difference 1 1) (sourceB2254 + difference 1 1) sourceC2254) = raw23028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2254 sourceB2254 sourceC2254 difference raw23028; decide +kernel
    rw [ha]
    exact (canonical23028 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2254 + difference 2 1) (sourceB2254 + difference 1 2) sourceC2254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1826) := by
    have ha : (tripleCharges (sourceA2254 + difference 2 1) (sourceB2254 + difference 1 2) sourceC2254) = raw31003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2254 sourceB2254 sourceC2254 difference raw31003; decide +kernel
    rw [ha]
    exact (canonical31003 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2254 + difference 3 1) (sourceB2254 + difference 1 3) sourceC2254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1826) := by
    have ha : (tripleCharges (sourceA2254 + difference 3 1) (sourceB2254 + difference 1 3) sourceC2254) = raw31004 := by
      apply Matrix.ext; unfold tripleCharges sourceA2254 sourceB2254 sourceC2254 difference raw31004; decide +kernel
    rw [ha]
    exact (canonical31004 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2254 + difference 4 1) (sourceB2254 + difference 1 4) sourceC2254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1830) := by
    have ha : (tripleCharges (sourceA2254 + difference 4 1) (sourceB2254 + difference 1 4) sourceC2254) = raw31005 := by
      apply Matrix.ext; unfold tripleCharges sourceA2254 sourceB2254 sourceC2254 difference raw31005; decide +kernel
    rw [ha]
    exact (canonical31005 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2254 + difference 5 1) (sourceB2254 + difference 1 5) sourceC2254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1832) := by
    have ha : (tripleCharges (sourceA2254 + difference 5 1) (sourceB2254 + difference 1 5) sourceC2254) = raw27395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2254 sourceB2254 sourceC2254 difference raw27395; decide +kernel
    rw [ha]
    exact (canonical27395 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2254 + sourceB2254) sourceC2254) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2254 + sourceB2254) sourceC2254) = raw23023 := by
      apply Matrix.ext; unfold doubleCharges sourceA2254 sourceB2254 sourceC2254 raw23023; decide +kernel
    rw [ha]
    exact (canonical23023 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2254 sourceB2254 sourceC2254
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2254, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2255 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2255 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2255 + difference 2 0) (sourceB2255 + difference 0 2) sourceC2255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 946) := by
    have ha : (tripleCharges (sourceA2255 + difference 2 0) (sourceB2255 + difference 0 2) sourceC2255) = raw23029 := by
      apply Matrix.ext; unfold tripleCharges sourceA2255 sourceB2255 sourceC2255 difference raw23029; decide +kernel
    rw [ha]
    exact (canonical23029 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2255 + difference 2 1) (sourceB2255 + difference 1 2) sourceC2255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1826) := by
    have ha : (tripleCharges (sourceA2255 + difference 2 1) (sourceB2255 + difference 1 2) sourceC2255) = raw31003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2255 sourceB2255 sourceC2255 difference raw31003; decide +kernel
    rw [ha]
    exact (canonical31003 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2255 + difference 2 2) (sourceB2255 + difference 2 2) sourceC2255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA2255 + difference 2 2) (sourceB2255 + difference 2 2) sourceC2255) = raw23028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2255 sourceB2255 sourceC2255 difference raw23028; decide +kernel
    rw [ha]
    exact (canonical23028 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2255 + difference 2 3) (sourceB2255 + difference 3 2) sourceC2255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1974) := by
    have ha : (tripleCharges (sourceA2255 + difference 2 3) (sourceB2255 + difference 3 2) sourceC2255) = raw31006 := by
      apply Matrix.ext; unfold tripleCharges sourceA2255 sourceB2255 sourceC2255 difference raw31006; decide +kernel
    rw [ha]
    exact (canonical31006 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2255 + difference 2 4) (sourceB2255 + difference 4 2) sourceC2255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2108) := by
    have ha : (tripleCharges (sourceA2255 + difference 2 4) (sourceB2255 + difference 4 2) sourceC2255) = raw31007 := by
      apply Matrix.ext; unfold tripleCharges sourceA2255 sourceB2255 sourceC2255 difference raw31007; decide +kernel
    rw [ha]
    exact (canonical31007 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2255 + difference 2 5) (sourceB2255 + difference 5 2) sourceC2255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA2255 + difference 2 5) (sourceB2255 + difference 5 2) sourceC2255) = raw31008 := by
      apply Matrix.ext; unfold tripleCharges sourceA2255 sourceB2255 sourceC2255 difference raw31008; decide +kernel
    rw [ha]
    exact (canonical31008 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2255 + sourceB2255) sourceC2255) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2255 + sourceB2255) sourceC2255) = raw23023 := by
      apply Matrix.ext; unfold doubleCharges sourceA2255 sourceB2255 sourceC2255 raw23023; decide +kernel
    rw [ha]
    exact (canonical23023 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2255 sourceB2255 sourceC2255
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2255, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2261 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2261 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2261 + difference 0 1) (sourceB2261 + difference 1 0) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5303) := by
    have ha : (tripleCharges (sourceA2261 + difference 0 1) (sourceB2261 + difference 1 0) sourceC2261) = raw31139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31139; decide +kernel
    rw [ha]
    exact (canonical31139 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2261 + difference 0 2) (sourceB2261 + difference 2 0) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5269) := by
    have ha : (tripleCharges (sourceA2261 + difference 0 2) (sourceB2261 + difference 2 0) sourceC2261) = raw31140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31140; decide +kernel
    rw [ha]
    exact (canonical31140 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2261 + difference 0 3) (sourceB2261 + difference 3 0) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5269) := by
    have ha : (tripleCharges (sourceA2261 + difference 0 3) (sourceB2261 + difference 3 0) sourceC2261) = raw31141 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31141; decide +kernel
    rw [ha]
    exact (canonical31141 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2261 + difference 0 4) (sourceB2261 + difference 4 0) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA2261 + difference 0 4) (sourceB2261 + difference 4 0) sourceC2261) = raw11398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw11398; decide +kernel
    rw [ha]
    exact (canonical11398 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2261 + difference 0 5) (sourceB2261 + difference 5 0) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA2261 + difference 0 5) (sourceB2261 + difference 5 0) sourceC2261) = raw31142 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31142; decide +kernel
    rw [ha]
    exact (canonical31142 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2261 + difference 1 0) (sourceB2261 + difference 0 1) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA2261 + difference 1 0) (sourceB2261 + difference 0 1) sourceC2261) = raw11418 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw11418; decide +kernel
    rw [ha]
    exact (canonical11418 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2261 + difference 1 2) (sourceB2261 + difference 2 1) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2261 + difference 1 2) (sourceB2261 + difference 2 1) sourceC2261) = raw11420 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw11420; decide +kernel
    rw [ha]
    exact (canonical11420 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2261 + difference 1 3) (sourceB2261 + difference 3 1) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2261 + difference 1 3) (sourceB2261 + difference 3 1) sourceC2261) = raw11421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw11421; decide +kernel
    rw [ha]
    exact (canonical11421 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2261 + difference 1 4) (sourceB2261 + difference 4 1) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA2261 + difference 1 4) (sourceB2261 + difference 4 1) sourceC2261) = raw21144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw21144; decide +kernel
    rw [ha]
    exact (canonical21144 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2261 + difference 1 5) (sourceB2261 + difference 5 1) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA2261 + difference 1 5) (sourceB2261 + difference 5 1) sourceC2261) = raw11422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw11422; decide +kernel
    rw [ha]
    exact (canonical11422 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2261 + difference 2 0) (sourceB2261 + difference 0 2) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4369) := by
    have ha : (tripleCharges (sourceA2261 + difference 2 0) (sourceB2261 + difference 0 2) sourceC2261) = raw23154 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw23154; decide +kernel
    rw [ha]
    exact (canonical23154 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2261 + difference 2 1) (sourceB2261 + difference 1 2) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4701) := by
    have ha : (tripleCharges (sourceA2261 + difference 2 1) (sourceB2261 + difference 1 2) sourceC2261) = raw31143 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31143; decide +kernel
    rw [ha]
    exact (canonical31143 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2261 + difference 2 3) (sourceB2261 + difference 3 2) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4774) := by
    have ha : (tripleCharges (sourceA2261 + difference 2 3) (sourceB2261 + difference 3 2) sourceC2261) = raw31144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31144; decide +kernel
    rw [ha]
    exact (canonical31144 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2261 + difference 2 4) (sourceB2261 + difference 4 2) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2261 + difference 2 4) (sourceB2261 + difference 4 2) sourceC2261) = raw11409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw11409; decide +kernel
    rw [ha]
    exact (canonical11409 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2261 + difference 2 5) (sourceB2261 + difference 5 2) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2261 + difference 2 5) (sourceB2261 + difference 5 2) sourceC2261) = raw31145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31145; decide +kernel
    rw [ha]
    exact (canonical31145 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2261 + difference 3 0) (sourceB2261 + difference 0 3) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4369) := by
    have ha : (tripleCharges (sourceA2261 + difference 3 0) (sourceB2261 + difference 0 3) sourceC2261) = raw23158 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw23158; decide +kernel
    rw [ha]
    exact (canonical23158 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2261 + difference 3 1) (sourceB2261 + difference 1 3) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4701) := by
    have ha : (tripleCharges (sourceA2261 + difference 3 1) (sourceB2261 + difference 1 3) sourceC2261) = raw31146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31146; decide +kernel
    rw [ha]
    exact (canonical31146 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2261 + difference 3 2) (sourceB2261 + difference 2 3) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4774) := by
    have ha : (tripleCharges (sourceA2261 + difference 3 2) (sourceB2261 + difference 2 3) sourceC2261) = raw31147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31147; decide +kernel
    rw [ha]
    exact (canonical31147 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2261 + difference 3 4) (sourceB2261 + difference 4 3) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2261 + difference 3 4) (sourceB2261 + difference 4 3) sourceC2261) = raw11414 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw11414; decide +kernel
    rw [ha]
    exact (canonical11414 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2261 + difference 3 5) (sourceB2261 + difference 5 3) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2261 + difference 3 5) (sourceB2261 + difference 5 3) sourceC2261) = raw31148 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31148; decide +kernel
    rw [ha]
    exact (canonical31148 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2261 + difference 4 0) (sourceB2261 + difference 0 4) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4374) := by
    have ha : (tripleCharges (sourceA2261 + difference 4 0) (sourceB2261 + difference 0 4) sourceC2261) = raw23162 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw23162; decide +kernel
    rw [ha]
    exact (canonical23162 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2261 + difference 4 1) (sourceB2261 + difference 1 4) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4705) := by
    have ha : (tripleCharges (sourceA2261 + difference 4 1) (sourceB2261 + difference 1 4) sourceC2261) = raw31149 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31149; decide +kernel
    rw [ha]
    exact (canonical31149 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2261 + difference 4 2) (sourceB2261 + difference 2 4) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4777) := by
    have ha : (tripleCharges (sourceA2261 + difference 4 2) (sourceB2261 + difference 2 4) sourceC2261) = raw31150 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31150; decide +kernel
    rw [ha]
    exact (canonical31150 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2261 + difference 4 3) (sourceB2261 + difference 3 4) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4777) := by
    have ha : (tripleCharges (sourceA2261 + difference 4 3) (sourceB2261 + difference 3 4) sourceC2261) = raw31151 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31151; decide +kernel
    rw [ha]
    exact (canonical31151 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2261 + difference 4 5) (sourceB2261 + difference 5 4) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA2261 + difference 4 5) (sourceB2261 + difference 5 4) sourceC2261) = raw31152 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31152; decide +kernel
    rw [ha]
    exact (canonical31152 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2261 + difference 5 0) (sourceB2261 + difference 0 5) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4374) := by
    have ha : (tripleCharges (sourceA2261 + difference 5 0) (sourceB2261 + difference 0 5) sourceC2261) = raw21158 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw21158; decide +kernel
    rw [ha]
    exact (canonical21158 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2261 + difference 5 1) (sourceB2261 + difference 1 5) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4705) := by
    have ha : (tripleCharges (sourceA2261 + difference 5 1) (sourceB2261 + difference 1 5) sourceC2261) = raw31153 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31153; decide +kernel
    rw [ha]
    exact (canonical31153 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2261 + difference 5 2) (sourceB2261 + difference 2 5) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4777) := by
    have ha : (tripleCharges (sourceA2261 + difference 5 2) (sourceB2261 + difference 2 5) sourceC2261) = raw31154 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31154; decide +kernel
    rw [ha]
    exact (canonical31154 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2261 + difference 5 3) (sourceB2261 + difference 3 5) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4777) := by
    have ha : (tripleCharges (sourceA2261 + difference 5 3) (sourceB2261 + difference 3 5) sourceC2261) = raw31155 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31155; decide +kernel
    rw [ha]
    exact (canonical31155 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2261 + difference 5 4) (sourceB2261 + difference 4 5) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA2261 + difference 5 4) (sourceB2261 + difference 4 5) sourceC2261) = raw11424 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw11424; decide +kernel
    rw [ha]
    exact (canonical11424 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2261 sourceB2261 sourceC2261
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2261, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2263 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2263 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2263 + difference 0 1) (sourceB2263 + difference 1 0) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2779) := by
    have ha : (tripleCharges (sourceA2263 + difference 0 1) (sourceB2263 + difference 1 0) sourceC2263) = raw31176 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31176; decide +kernel
    rw [ha]
    exact (canonical31176 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2263 + difference 0 2) (sourceB2263 + difference 2 0) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2736) := by
    have ha : (tripleCharges (sourceA2263 + difference 0 2) (sourceB2263 + difference 2 0) sourceC2263) = raw31177 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31177; decide +kernel
    rw [ha]
    exact (canonical31177 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2263 + difference 0 3) (sourceB2263 + difference 3 0) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2736) := by
    have ha : (tripleCharges (sourceA2263 + difference 0 3) (sourceB2263 + difference 3 0) sourceC2263) = raw31178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31178; decide +kernel
    rw [ha]
    exact (canonical31178 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2263 + difference 0 4) (sourceB2263 + difference 4 0) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA2263 + difference 0 4) (sourceB2263 + difference 4 0) sourceC2263) = raw11428 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw11428; decide +kernel
    rw [ha]
    exact (canonical11428 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2263 + difference 0 5) (sourceB2263 + difference 5 0) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA2263 + difference 0 5) (sourceB2263 + difference 5 0) sourceC2263) = raw31179 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31179; decide +kernel
    rw [ha]
    exact (canonical31179 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2263 + difference 1 0) (sourceB2263 + difference 0 1) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA2263 + difference 1 0) (sourceB2263 + difference 0 1) sourceC2263) = raw11448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw11448; decide +kernel
    rw [ha]
    exact (canonical11448 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2263 + difference 1 2) (sourceB2263 + difference 2 1) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA2263 + difference 1 2) (sourceB2263 + difference 2 1) sourceC2263) = raw11450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw11450; decide +kernel
    rw [ha]
    exact (canonical11450 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2263 + difference 1 3) (sourceB2263 + difference 3 1) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA2263 + difference 1 3) (sourceB2263 + difference 3 1) sourceC2263) = raw11451 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw11451; decide +kernel
    rw [ha]
    exact (canonical11451 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2263 + difference 1 4) (sourceB2263 + difference 4 1) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA2263 + difference 1 4) (sourceB2263 + difference 4 1) sourceC2263) = raw21196 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw21196; decide +kernel
    rw [ha]
    exact (canonical21196 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2263 + difference 1 5) (sourceB2263 + difference 5 1) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA2263 + difference 1 5) (sourceB2263 + difference 5 1) sourceC2263) = raw11452 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw11452; decide +kernel
    rw [ha]
    exact (canonical11452 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2263 + difference 2 0) (sourceB2263 + difference 0 2) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1721) := by
    have ha : (tripleCharges (sourceA2263 + difference 2 0) (sourceB2263 + difference 0 2) sourceC2263) = raw23193 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw23193; decide +kernel
    rw [ha]
    exact (canonical23193 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2263 + difference 2 1) (sourceB2263 + difference 1 2) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2257) := by
    have ha : (tripleCharges (sourceA2263 + difference 2 1) (sourceB2263 + difference 1 2) sourceC2263) = raw31180 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31180; decide +kernel
    rw [ha]
    exact (canonical31180 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2263 + difference 2 3) (sourceB2263 + difference 3 2) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2199) := by
    have ha : (tripleCharges (sourceA2263 + difference 2 3) (sourceB2263 + difference 3 2) sourceC2263) = raw31181 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31181; decide +kernel
    rw [ha]
    exact (canonical31181 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2263 + difference 2 4) (sourceB2263 + difference 4 2) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2263 + difference 2 4) (sourceB2263 + difference 4 2) sourceC2263) = raw11439 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw11439; decide +kernel
    rw [ha]
    exact (canonical11439 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2263 + difference 2 5) (sourceB2263 + difference 5 2) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2263 + difference 2 5) (sourceB2263 + difference 5 2) sourceC2263) = raw31182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31182; decide +kernel
    rw [ha]
    exact (canonical31182 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2263 + difference 3 0) (sourceB2263 + difference 0 3) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1721) := by
    have ha : (tripleCharges (sourceA2263 + difference 3 0) (sourceB2263 + difference 0 3) sourceC2263) = raw23197 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw23197; decide +kernel
    rw [ha]
    exact (canonical23197 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2263 + difference 3 1) (sourceB2263 + difference 1 3) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2257) := by
    have ha : (tripleCharges (sourceA2263 + difference 3 1) (sourceB2263 + difference 1 3) sourceC2263) = raw31183 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31183; decide +kernel
    rw [ha]
    exact (canonical31183 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2263 + difference 3 2) (sourceB2263 + difference 2 3) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2199) := by
    have ha : (tripleCharges (sourceA2263 + difference 3 2) (sourceB2263 + difference 2 3) sourceC2263) = raw31184 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31184; decide +kernel
    rw [ha]
    exact (canonical31184 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2263 + difference 3 4) (sourceB2263 + difference 4 3) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2263 + difference 3 4) (sourceB2263 + difference 4 3) sourceC2263) = raw11444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw11444; decide +kernel
    rw [ha]
    exact (canonical11444 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2263 + difference 3 5) (sourceB2263 + difference 5 3) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2263 + difference 3 5) (sourceB2263 + difference 5 3) sourceC2263) = raw31185 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31185; decide +kernel
    rw [ha]
    exact (canonical31185 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2263 + difference 4 0) (sourceB2263 + difference 0 4) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1748) := by
    have ha : (tripleCharges (sourceA2263 + difference 4 0) (sourceB2263 + difference 0 4) sourceC2263) = raw23201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw23201; decide +kernel
    rw [ha]
    exact (canonical23201 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2263 + difference 4 1) (sourceB2263 + difference 1 4) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2286) := by
    have ha : (tripleCharges (sourceA2263 + difference 4 1) (sourceB2263 + difference 1 4) sourceC2263) = raw31186 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31186; decide +kernel
    rw [ha]
    exact (canonical31186 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2263 + difference 4 2) (sourceB2263 + difference 2 4) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA2263 + difference 4 2) (sourceB2263 + difference 2 4) sourceC2263) = raw31187 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31187; decide +kernel
    rw [ha]
    exact (canonical31187 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2263 + difference 4 3) (sourceB2263 + difference 3 4) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA2263 + difference 4 3) (sourceB2263 + difference 3 4) sourceC2263) = raw31188 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31188; decide +kernel
    rw [ha]
    exact (canonical31188 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2263 + difference 4 5) (sourceB2263 + difference 5 4) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA2263 + difference 4 5) (sourceB2263 + difference 5 4) sourceC2263) = raw31189 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31189; decide +kernel
    rw [ha]
    exact (canonical31189 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2263 + difference 5 0) (sourceB2263 + difference 0 5) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1748) := by
    have ha : (tripleCharges (sourceA2263 + difference 5 0) (sourceB2263 + difference 0 5) sourceC2263) = raw21210 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw21210; decide +kernel
    rw [ha]
    exact (canonical21210 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2263 + difference 5 1) (sourceB2263 + difference 1 5) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2286) := by
    have ha : (tripleCharges (sourceA2263 + difference 5 1) (sourceB2263 + difference 1 5) sourceC2263) = raw31190 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31190; decide +kernel
    rw [ha]
    exact (canonical31190 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2263 + difference 5 2) (sourceB2263 + difference 2 5) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA2263 + difference 5 2) (sourceB2263 + difference 2 5) sourceC2263) = raw31191 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31191; decide +kernel
    rw [ha]
    exact (canonical31191 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2263 + difference 5 3) (sourceB2263 + difference 3 5) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA2263 + difference 5 3) (sourceB2263 + difference 3 5) sourceC2263) = raw31192 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31192; decide +kernel
    rw [ha]
    exact (canonical31192 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2263 + difference 5 4) (sourceB2263 + difference 4 5) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA2263 + difference 5 4) (sourceB2263 + difference 4 5) sourceC2263) = raw11454 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw11454; decide +kernel
    rw [ha]
    exact (canonical11454 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2263 sourceB2263 sourceC2263
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2263, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2264 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2264 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2264 + difference 0 1) (sourceB2264 + difference 1 0) sourceC2264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3118) := by
    have ha : (tripleCharges (sourceA2264 + difference 0 1) (sourceB2264 + difference 1 0) sourceC2264) = raw31193 := by
      apply Matrix.ext; unfold tripleCharges sourceA2264 sourceB2264 sourceC2264 difference raw31193; decide +kernel
    rw [ha]
    exact (canonical31193 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2264 + difference 1 1) (sourceB2264 + difference 1 1) sourceC2264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2116) := by
    have ha : (tripleCharges (sourceA2264 + difference 1 1) (sourceB2264 + difference 1 1) sourceC2264) = raw11462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2264 sourceB2264 sourceC2264 difference raw11462; decide +kernel
    rw [ha]
    exact (canonical11462 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2264 + difference 2 1) (sourceB2264 + difference 1 2) sourceC2264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1827) := by
    have ha : (tripleCharges (sourceA2264 + difference 2 1) (sourceB2264 + difference 1 2) sourceC2264) = raw31194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2264 sourceB2264 sourceC2264 difference raw31194; decide +kernel
    rw [ha]
    exact (canonical31194 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2264 + difference 3 1) (sourceB2264 + difference 1 3) sourceC2264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1827) := by
    have ha : (tripleCharges (sourceA2264 + difference 3 1) (sourceB2264 + difference 1 3) sourceC2264) = raw31195 := by
      apply Matrix.ext; unfold tripleCharges sourceA2264 sourceB2264 sourceC2264 difference raw31195; decide +kernel
    rw [ha]
    exact (canonical31195 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2264 + difference 4 1) (sourceB2264 + difference 1 4) sourceC2264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1831) := by
    have ha : (tripleCharges (sourceA2264 + difference 4 1) (sourceB2264 + difference 1 4) sourceC2264) = raw31196 := by
      apply Matrix.ext; unfold tripleCharges sourceA2264 sourceB2264 sourceC2264 difference raw31196; decide +kernel
    rw [ha]
    exact (canonical31196 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2264 + difference 5 1) (sourceB2264 + difference 1 5) sourceC2264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1831) := by
    have ha : (tripleCharges (sourceA2264 + difference 5 1) (sourceB2264 + difference 1 5) sourceC2264) = raw31197 := by
      apply Matrix.ext; unfold tripleCharges sourceA2264 sourceB2264 sourceC2264 difference raw31197; decide +kernel
    rw [ha]
    exact (canonical31197 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2264 + sourceB2264) sourceC2264) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2264 + sourceB2264) sourceC2264) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA2264 sourceB2264 sourceC2264 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2264 sourceB2264 sourceC2264
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2264, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2265 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2265 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2265 + difference 2 0) (sourceB2265 + difference 0 2) sourceC2265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 947) := by
    have ha : (tripleCharges (sourceA2265 + difference 2 0) (sourceB2265 + difference 0 2) sourceC2265) = raw23213 := by
      apply Matrix.ext; unfold tripleCharges sourceA2265 sourceB2265 sourceC2265 difference raw23213; decide +kernel
    rw [ha]
    exact (canonical23213 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2265 + difference 2 1) (sourceB2265 + difference 1 2) sourceC2265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1827) := by
    have ha : (tripleCharges (sourceA2265 + difference 2 1) (sourceB2265 + difference 1 2) sourceC2265) = raw31194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2265 sourceB2265 sourceC2265 difference raw31194; decide +kernel
    rw [ha]
    exact (canonical31194 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2265 + difference 2 2) (sourceB2265 + difference 2 2) sourceC2265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2116) := by
    have ha : (tripleCharges (sourceA2265 + difference 2 2) (sourceB2265 + difference 2 2) sourceC2265) = raw11462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2265 sourceB2265 sourceC2265 difference raw11462; decide +kernel
    rw [ha]
    exact (canonical11462 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2265 + difference 2 3) (sourceB2265 + difference 3 2) sourceC2265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1975) := by
    have ha : (tripleCharges (sourceA2265 + difference 2 3) (sourceB2265 + difference 3 2) sourceC2265) = raw31198 := by
      apply Matrix.ext; unfold tripleCharges sourceA2265 sourceB2265 sourceC2265 difference raw31198; decide +kernel
    rw [ha]
    exact (canonical31198 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2265 + difference 2 4) (sourceB2265 + difference 4 2) sourceC2265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2265 + difference 2 4) (sourceB2265 + difference 4 2) sourceC2265) = raw11460 := by
      apply Matrix.ext; unfold tripleCharges sourceA2265 sourceB2265 sourceC2265 difference raw11460; decide +kernel
    rw [ha]
    exact (canonical11460 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2265 + difference 2 5) (sourceB2265 + difference 5 2) sourceC2265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2265 + difference 2 5) (sourceB2265 + difference 5 2) sourceC2265) = raw31199 := by
      apply Matrix.ext; unfold tripleCharges sourceA2265 sourceB2265 sourceC2265 difference raw31199; decide +kernel
    rw [ha]
    exact (canonical31199 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2265 + sourceB2265) sourceC2265) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2265 + sourceB2265) sourceC2265) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA2265 sourceB2265 sourceC2265 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2265 sourceB2265 sourceC2265
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2265, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1841 : Integer.Sparse.reindex keyMap MixedData.row1841 = numericRow1841 := by decide +kernel

theorem numericCheck1841 (x : Master → ℝ) : Integer.Sparse.eval numericRow1841 x =
    (1 : ℝ) * reducedSource1841 x := by
  norm_num [numericRow1841, reducedSource1841, Integer.Sparse.eval, Sparse.eval, nodeValue1712, nodeValue1735, nodeValue1738, nodeValue1743, nodeValue2162, nodeValue2163, nodeValue2194, nodeValue2212, nodeValue2215, nodeValue2242, nodeValue2249, nodeValue2251, nodeValue2261, nodeValue2264, nodeValue2273, nodeValue2278, nodeValue2282, nodeValue2729, nodeValue2765, nodeValue2771, nodeValue2774]

theorem reindexCheck1842 : Integer.Sparse.reindex keyMap MixedData.row1842 = numericRow1842 := by decide +kernel

theorem numericCheck1842 (x : Master → ℝ) : Integer.Sparse.eval numericRow1842 x =
    (1 : ℝ) * reducedSource1842 x := by
  norm_num [numericRow1842, reducedSource1842, Integer.Sparse.eval, Sparse.eval, nodeValue1826, nodeValue1830, nodeValue1832, nodeValue2115, nodeValue3056, nodeValue4084]

theorem reindexCheck1843 : Integer.Sparse.reindex keyMap MixedData.row1843 = numericRow1843 := by decide +kernel

theorem numericCheck1843 (x : Master → ℝ) : Integer.Sparse.eval numericRow1843 x =
    (1 : ℝ) * reducedSource1843 x := by
  norm_num [numericRow1843, reducedSource1843, Integer.Sparse.eval, Sparse.eval, nodeValue946, nodeValue1826, nodeValue1974, nodeValue2106, nodeValue2108, nodeValue2115, nodeValue4084]

theorem reindexCheck1848 : Integer.Sparse.reindex keyMap MixedData.row1848 = numericRow1848 := by decide +kernel

theorem numericCheck1848 (x : Master → ℝ) : Integer.Sparse.eval numericRow1848 x =
    (4 : ℝ) * reducedSource1848 x := by
  norm_num [numericRow1848, reducedSource1848, Integer.Sparse.eval, Sparse.eval, nodeValue4369, nodeValue4374, nodeValue4467, nodeValue4701, nodeValue4705, nodeValue4774, nodeValue4777, nodeValue4811, nodeValue4866, nodeValue4871, nodeValue4895, nodeValue5269, nodeValue5303, nodeValue5304]
  ring

theorem reindexCheck1850 : Integer.Sparse.reindex keyMap MixedData.row1850 = numericRow1850 := by decide +kernel

theorem numericCheck1850 (x : Master → ℝ) : Integer.Sparse.eval numericRow1850 x =
    (1 : ℝ) * reducedSource1850 x := by
  norm_num [numericRow1850, reducedSource1850, Integer.Sparse.eval, Sparse.eval, nodeValue1721, nodeValue1748, nodeValue1751, nodeValue2199, nodeValue2223, nodeValue2225, nodeValue2257, nodeValue2260, nodeValue2286, nodeValue2287, nodeValue2291, nodeValue2736, nodeValue2779, nodeValue2782]

theorem reindexCheck1851 : Integer.Sparse.reindex keyMap MixedData.row1851 = numericRow1851 := by decide +kernel

theorem numericCheck1851 (x : Master → ℝ) : Integer.Sparse.eval numericRow1851 x =
    (1 : ℝ) * reducedSource1851 x := by
  norm_num [numericRow1851, reducedSource1851, Integer.Sparse.eval, Sparse.eval, nodeValue1827, nodeValue1831, nodeValue2116, nodeValue3118, nodeValue4083]

theorem reindexCheck1852 : Integer.Sparse.reindex keyMap MixedData.row1852 = numericRow1852 := by decide +kernel

theorem numericCheck1852 (x : Master → ℝ) : Integer.Sparse.eval numericRow1852 x =
    (1 : ℝ) * reducedSource1852 x := by
  norm_num [numericRow1852, reducedSource1852, Integer.Sparse.eval, Sparse.eval, nodeValue947, nodeValue1827, nodeValue1975, nodeValue2107, nodeValue2116, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1841 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1841 (mixedVector B) = 0 := by
  have h1712 : mixedVector B (Sum.inr 1712) = Sparse.eval nodeValue1712 (mixedVector B) := by
    change mixedMoment B node1712 node1712Labels = _
    exact sound1712 B hB hF
  have h1735 : mixedVector B (Sum.inr 1735) = Sparse.eval nodeValue1735 (mixedVector B) := by
    change mixedMoment B node1735 node1735Labels = _
    exact sound1735 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h1743 : mixedVector B (Sum.inr 1743) = Sparse.eval nodeValue1743 (mixedVector B) := by
    change mixedMoment B node1743 node1743Labels = _
    exact sound1743 B hB hF
  have h2162 : mixedVector B (Sum.inr 2162) = Sparse.eval nodeValue2162 (mixedVector B) := by
    change mixedMoment B node2162 node2162Labels = _
    exact sound2162 B hB hF
  have h2163 : mixedVector B (Sum.inr 2163) = Sparse.eval nodeValue2163 (mixedVector B) := by
    change mixedMoment B node2163 node2163Labels = _
    exact sound2163 B hB hF
  have h2194 : mixedVector B (Sum.inr 2194) = Sparse.eval nodeValue2194 (mixedVector B) := by
    change mixedMoment B node2194 node2194Labels = _
    exact sound2194 B hB hF
  have h2212 : mixedVector B (Sum.inr 2212) = Sparse.eval nodeValue2212 (mixedVector B) := by
    change mixedMoment B node2212 node2212Labels = _
    exact sound2212 B hB hF
  have h2215 : mixedVector B (Sum.inr 2215) = Sparse.eval nodeValue2215 (mixedVector B) := by
    change mixedMoment B node2215 node2215Labels = _
    exact sound2215 B hB hF
  have h2242 : mixedVector B (Sum.inr 2242) = Sparse.eval nodeValue2242 (mixedVector B) := by
    change mixedMoment B node2242 node2242Labels = _
    exact sound2242 B hB hF
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
  have h2273 : mixedVector B (Sum.inr 2273) = Sparse.eval nodeValue2273 (mixedVector B) := by
    change mixedMoment B node2273 node2273Labels = _
    exact sound2273 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h2282 : mixedVector B (Sum.inr 2282) = Sparse.eval nodeValue2282 (mixedVector B) := by
    change mixedMoment B node2282 node2282Labels = _
    exact sound2282 B hB hF
  have h2729 : mixedVector B (Sum.inr 2729) = Sparse.eval nodeValue2729 (mixedVector B) := by
    change mixedMoment B node2729 node2729Labels = _
    exact sound2729 B hB hF
  have h2765 : mixedVector B (Sum.inr 2765) = Sparse.eval nodeValue2765 (mixedVector B) := by
    change mixedMoment B node2765 node2765Labels = _
    exact sound2765 B hB hF
  have h2771 : mixedVector B (Sum.inr 2771) = Sparse.eval nodeValue2771 (mixedVector B) := by
    change mixedMoment B node2771 node2771Labels = _
    exact sound2771 B hB hF
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  simpa only [sourceForm2253, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1712, h1735, h1738, h1743, h2162, h2163, h2194, h2212, h2215, h2242, h2249, h2251, h2261, h2264, h2273, h2278, h2282, h2729, h2765, h2771, h2774, reducedSource1841] using sourceEq2253 B hB

theorem rowSound1841 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1841 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1841, numericCheck1841, reducedZero1841 B hB hF, mul_zero]

theorem reducedZero1842 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1842 (mixedVector B) = 0 := by
  have h1826 : mixedVector B (Sum.inr 1826) = Sparse.eval nodeValue1826 (mixedVector B) := by
    change mixedMoment B node1826 node1826Labels = _
    exact sound1826 B hB hF
  have h1830 : mixedVector B (Sum.inr 1830) = Sparse.eval nodeValue1830 (mixedVector B) := by
    change mixedMoment B node1830 node1830Labels = _
    exact sound1830 B hB hF
  have h1832 : mixedVector B (Sum.inr 1832) = Sparse.eval nodeValue1832 (mixedVector B) := by
    change mixedMoment B node1832 node1832Labels = _
    exact sound1832 B hB hF
  have h2115 : mixedVector B (Sum.inr 2115) = Sparse.eval nodeValue2115 (mixedVector B) := by
    change mixedMoment B node2115 node2115Labels = _
    exact sound2115 B hB hF
  have h3056 : mixedVector B (Sum.inr 3056) = Sparse.eval nodeValue3056 (mixedVector B) := by
    change mixedMoment B node3056 node3056Labels = _
    exact sound3056 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2254, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1826, h1830, h1832, h2115, h3056, h4084, reducedSource1842] using sourceEq2254 B hB

theorem rowSound1842 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1842 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1842, numericCheck1842, reducedZero1842 B hB hF, mul_zero]

theorem reducedZero1843 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1843 (mixedVector B) = 0 := by
  have h946 : mixedVector B (Sum.inr 946) = Sparse.eval nodeValue946 (mixedVector B) := by
    change mixedMoment B node946 node946Labels = _
    exact sound946 B hB hF
  have h1826 : mixedVector B (Sum.inr 1826) = Sparse.eval nodeValue1826 (mixedVector B) := by
    change mixedMoment B node1826 node1826Labels = _
    exact sound1826 B hB hF
  have h1974 : mixedVector B (Sum.inr 1974) = Sparse.eval nodeValue1974 (mixedVector B) := by
    change mixedMoment B node1974 node1974Labels = _
    exact sound1974 B hB hF
  have h2106 : mixedVector B (Sum.inr 2106) = Sparse.eval nodeValue2106 (mixedVector B) := by
    change mixedMoment B node2106 node2106Labels = _
    exact sound2106 B hB hF
  have h2108 : mixedVector B (Sum.inr 2108) = Sparse.eval nodeValue2108 (mixedVector B) := by
    change mixedMoment B node2108 node2108Labels = _
    exact sound2108 B hB hF
  have h2115 : mixedVector B (Sum.inr 2115) = Sparse.eval nodeValue2115 (mixedVector B) := by
    change mixedMoment B node2115 node2115Labels = _
    exact sound2115 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2255, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h946, h1826, h1974, h2106, h2108, h2115, h4084, reducedSource1843] using sourceEq2255 B hB

theorem rowSound1843 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1843 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1843, numericCheck1843, reducedZero1843 B hB hF, mul_zero]

theorem reducedZero1848 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1848 (mixedVector B) = 0 := by
  have h4369 : mixedVector B (Sum.inr 4369) = Sparse.eval nodeValue4369 (mixedVector B) := by
    change mixedMoment B node4369 node4369Labels = _
    exact sound4369 B hB hF
  have h4374 : mixedVector B (Sum.inr 4374) = Sparse.eval nodeValue4374 (mixedVector B) := by
    change mixedMoment B node4374 node4374Labels = _
    exact sound4374 B hB hF
  have h4467 : mixedVector B (Sum.inr 4467) = Sparse.eval nodeValue4467 (mixedVector B) := by
    change mixedMoment B node4467 node4467Labels = _
    exact sound4467 B hB hF
  have h4701 : mixedVector B (Sum.inr 4701) = Sparse.eval nodeValue4701 (mixedVector B) := by
    change mixedMoment B node4701 node4701Labels = _
    exact sound4701 B hB hF
  have h4705 : mixedVector B (Sum.inr 4705) = Sparse.eval nodeValue4705 (mixedVector B) := by
    change mixedMoment B node4705 node4705Labels = _
    exact sound4705 B hB hF
  have h4774 : mixedVector B (Sum.inr 4774) = Sparse.eval nodeValue4774 (mixedVector B) := by
    change mixedMoment B node4774 node4774Labels = _
    exact sound4774 B hB hF
  have h4777 : mixedVector B (Sum.inr 4777) = Sparse.eval nodeValue4777 (mixedVector B) := by
    change mixedMoment B node4777 node4777Labels = _
    exact sound4777 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4866 : mixedVector B (Sum.inr 4866) = Sparse.eval nodeValue4866 (mixedVector B) := by
    change mixedMoment B node4866 node4866Labels = _
    exact sound4866 B hB hF
  have h4871 : mixedVector B (Sum.inr 4871) = Sparse.eval nodeValue4871 (mixedVector B) := by
    change mixedMoment B node4871 node4871Labels = _
    exact sound4871 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  have h5269 : mixedVector B (Sum.inr 5269) = Sparse.eval nodeValue5269 (mixedVector B) := by
    change mixedMoment B node5269 node5269Labels = _
    exact sound5269 B hB hF
  have h5303 : mixedVector B (Sum.inr 5303) = Sparse.eval nodeValue5303 (mixedVector B) := by
    change mixedMoment B node5303 node5303Labels = _
    exact sound5303 B hB hF
  have h5304 : mixedVector B (Sum.inr 5304) = Sparse.eval nodeValue5304 (mixedVector B) := by
    change mixedMoment B node5304 node5304Labels = _
    exact sound5304 B hB hF
  simpa only [sourceForm2261, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4369, h4374, h4467, h4701, h4705, h4774, h4777, h4811, h4866, h4871, h4895, h5269, h5303, h5304, reducedSource1848] using sourceEq2261 B hB

theorem rowSound1848 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1848 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1848, numericCheck1848, reducedZero1848 B hB hF, mul_zero]

theorem reducedZero1850 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1850 (mixedVector B) = 0 := by
  have h1721 : mixedVector B (Sum.inr 1721) = Sparse.eval nodeValue1721 (mixedVector B) := by
    change mixedMoment B node1721 node1721Labels = _
    exact sound1721 B hB hF
  have h1748 : mixedVector B (Sum.inr 1748) = Sparse.eval nodeValue1748 (mixedVector B) := by
    change mixedMoment B node1748 node1748Labels = _
    exact sound1748 B hB hF
  have h1751 : mixedVector B (Sum.inr 1751) = Sparse.eval nodeValue1751 (mixedVector B) := by
    change mixedMoment B node1751 node1751Labels = _
    exact sound1751 B hB hF
  have h2199 : mixedVector B (Sum.inr 2199) = Sparse.eval nodeValue2199 (mixedVector B) := by
    change mixedMoment B node2199 node2199Labels = _
    exact sound2199 B hB hF
  have h2223 : mixedVector B (Sum.inr 2223) = Sparse.eval nodeValue2223 (mixedVector B) := by
    change mixedMoment B node2223 node2223Labels = _
    exact sound2223 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h2257 : mixedVector B (Sum.inr 2257) = Sparse.eval nodeValue2257 (mixedVector B) := by
    change mixedMoment B node2257 node2257Labels = _
    exact sound2257 B hB hF
  have h2260 : mixedVector B (Sum.inr 2260) = Sparse.eval nodeValue2260 (mixedVector B) := by
    change mixedMoment B node2260 node2260Labels = _
    exact sound2260 B hB hF
  have h2286 : mixedVector B (Sum.inr 2286) = Sparse.eval nodeValue2286 (mixedVector B) := by
    change mixedMoment B node2286 node2286Labels = _
    exact sound2286 B hB hF
  have h2287 : mixedVector B (Sum.inr 2287) = Sparse.eval nodeValue2287 (mixedVector B) := by
    change mixedMoment B node2287 node2287Labels = _
    exact sound2287 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  have h2736 : mixedVector B (Sum.inr 2736) = Sparse.eval nodeValue2736 (mixedVector B) := by
    change mixedMoment B node2736 node2736Labels = _
    exact sound2736 B hB hF
  have h2779 : mixedVector B (Sum.inr 2779) = Sparse.eval nodeValue2779 (mixedVector B) := by
    change mixedMoment B node2779 node2779Labels = _
    exact sound2779 B hB hF
  have h2782 : mixedVector B (Sum.inr 2782) = Sparse.eval nodeValue2782 (mixedVector B) := by
    change mixedMoment B node2782 node2782Labels = _
    exact sound2782 B hB hF
  simpa only [sourceForm2263, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1721, h1748, h1751, h2199, h2223, h2225, h2257, h2260, h2286, h2287, h2291, h2736, h2779, h2782, reducedSource1850] using sourceEq2263 B hB

theorem rowSound1850 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1850 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1850, numericCheck1850, reducedZero1850 B hB hF, mul_zero]

theorem reducedZero1851 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1851 (mixedVector B) = 0 := by
  have h1827 : mixedVector B (Sum.inr 1827) = Sparse.eval nodeValue1827 (mixedVector B) := by
    change mixedMoment B node1827 node1827Labels = _
    exact sound1827 B hB hF
  have h1831 : mixedVector B (Sum.inr 1831) = Sparse.eval nodeValue1831 (mixedVector B) := by
    change mixedMoment B node1831 node1831Labels = _
    exact sound1831 B hB hF
  have h2116 : mixedVector B (Sum.inr 2116) = Sparse.eval nodeValue2116 (mixedVector B) := by
    change mixedMoment B node2116 node2116Labels = _
    exact sound2116 B hB hF
  have h3118 : mixedVector B (Sum.inr 3118) = Sparse.eval nodeValue3118 (mixedVector B) := by
    change mixedMoment B node3118 node3118Labels = _
    exact sound3118 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2264, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1827, h1831, h2116, h3118, h4083, reducedSource1851] using sourceEq2264 B hB

theorem rowSound1851 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1851 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1851, numericCheck1851, reducedZero1851 B hB hF, mul_zero]

theorem reducedZero1852 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1852 (mixedVector B) = 0 := by
  have h947 : mixedVector B (Sum.inr 947) = Sparse.eval nodeValue947 (mixedVector B) := by
    change mixedMoment B node947 node947Labels = _
    exact sound947 B hB hF
  have h1827 : mixedVector B (Sum.inr 1827) = Sparse.eval nodeValue1827 (mixedVector B) := by
    change mixedMoment B node1827 node1827Labels = _
    exact sound1827 B hB hF
  have h1975 : mixedVector B (Sum.inr 1975) = Sparse.eval nodeValue1975 (mixedVector B) := by
    change mixedMoment B node1975 node1975Labels = _
    exact sound1975 B hB hF
  have h2107 : mixedVector B (Sum.inr 2107) = Sparse.eval nodeValue2107 (mixedVector B) := by
    change mixedMoment B node2107 node2107Labels = _
    exact sound2107 B hB hF
  have h2116 : mixedVector B (Sum.inr 2116) = Sparse.eval nodeValue2116 (mixedVector B) := by
    change mixedMoment B node2116 node2116Labels = _
    exact sound2116 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2265, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h947, h1827, h1975, h2107, h2116, h4083, reducedSource1852] using sourceEq2265 B hB

theorem rowSound1852 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1852 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1852, numericCheck1852, reducedZero1852 B hB hF, mul_zero]

theorem sourceRowsAt1840 : MixedData.sourceRows (1840 : Fin 2425) =
    MixedData.row1840 := by decide +kernel

theorem sourceRowsAt1841 : MixedData.sourceRows (1841 : Fin 2425) =
    MixedData.row1841 := by decide +kernel

theorem sourceRowsAt1842 : MixedData.sourceRows (1842 : Fin 2425) =
    MixedData.row1842 := by decide +kernel

theorem sourceRowsAt1843 : MixedData.sourceRows (1843 : Fin 2425) =
    MixedData.row1843 := by decide +kernel

theorem sourceRowsAt1844 : MixedData.sourceRows (1844 : Fin 2425) =
    MixedData.row1844 := by decide +kernel

theorem sourceRowsAt1845 : MixedData.sourceRows (1845 : Fin 2425) =
    MixedData.row1845 := by decide +kernel

theorem sourceRowsAt1846 : MixedData.sourceRows (1846 : Fin 2425) =
    MixedData.row1846 := by decide +kernel

theorem sourceRowsAt1847 : MixedData.sourceRows (1847 : Fin 2425) =
    MixedData.row1847 := by decide +kernel

theorem sourceRowsAt1848 : MixedData.sourceRows (1848 : Fin 2425) =
    MixedData.row1848 := by decide +kernel

theorem sourceRowsAt1849 : MixedData.sourceRows (1849 : Fin 2425) =
    MixedData.row1849 := by decide +kernel

theorem sourceRowsAt1850 : MixedData.sourceRows (1850 : Fin 2425) =
    MixedData.row1850 := by decide +kernel

theorem sourceRowsAt1851 : MixedData.sourceRows (1851 : Fin 2425) =
    MixedData.row1851 := by decide +kernel

theorem sourceRowsAt1852 : MixedData.sourceRows (1852 : Fin 2425) =
    MixedData.row1852 := by decide +kernel

theorem sourceRowsAt1853 : MixedData.sourceRows (1853 : Fin 2425) =
    MixedData.row1853 := by decide +kernel

theorem sourceRowsAt1854 : MixedData.sourceRows (1854 : Fin 2425) =
    MixedData.row1854 := by decide +kernel

theorem sourceRowsAt1855 : MixedData.sourceRows (1855 : Fin 2425) =
    MixedData.row1855 := by decide +kernel

theorem chunkSound115_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 115) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1840 ∨ k.val = 1841 ∨ k.val = 1842 ∨ k.val = 1843 ∨ k.val = 1844 ∨ k.val = 1845 ∨ k.val = 1846 ∨ k.val = 1847 ∨ k.val = 1848 ∨ k.val = 1849 ∨ k.val = 1850 ∨ k.val = 1851 ∨ k.val = 1852 ∨ k.val = 1853 ∨ k.val = 1854 ∨ k.val = 1855 := by omega
  rcases heq with h1840 | h1841 | h1842 | h1843 | h1844 | h1845 | h1846 | h1847 | h1848 | h1849 | h1850 | h1851 | h1852 | h1853 | h1854 | h1855
  · have he : k = (1840 : Fin 2425) := Fin.ext h1840
    subst k
    rw [sourceRowsAt1840]
    exact rowSound1840_e B hB hF
  · have he : k = (1841 : Fin 2425) := Fin.ext h1841
    subst k
    rw [sourceRowsAt1841]
    exact rowSound1841 B hB hF
  · have he : k = (1842 : Fin 2425) := Fin.ext h1842
    subst k
    rw [sourceRowsAt1842]
    exact rowSound1842 B hB hF
  · have he : k = (1843 : Fin 2425) := Fin.ext h1843
    subst k
    rw [sourceRowsAt1843]
    exact rowSound1843 B hB hF
  · have he : k = (1844 : Fin 2425) := Fin.ext h1844
    subst k
    rw [sourceRowsAt1844]
    exact rowSound1844_e B hB hF
  · have he : k = (1845 : Fin 2425) := Fin.ext h1845
    subst k
    rw [sourceRowsAt1845]
    exact rowSound1845_e B hB hF
  · have he : k = (1846 : Fin 2425) := Fin.ext h1846
    subst k
    rw [sourceRowsAt1846]
    exact rowSound1846_e B hB hF
  · have he : k = (1847 : Fin 2425) := Fin.ext h1847
    subst k
    rw [sourceRowsAt1847]
    exact rowSound1847_e B hB hF
  · have he : k = (1848 : Fin 2425) := Fin.ext h1848
    subst k
    rw [sourceRowsAt1848]
    exact rowSound1848 B hB hF
  · have he : k = (1849 : Fin 2425) := Fin.ext h1849
    subst k
    rw [sourceRowsAt1849]
    exact rowSound1849_e B hB hF
  · have he : k = (1850 : Fin 2425) := Fin.ext h1850
    subst k
    rw [sourceRowsAt1850]
    exact rowSound1850 B hB hF
  · have he : k = (1851 : Fin 2425) := Fin.ext h1851
    subst k
    rw [sourceRowsAt1851]
    exact rowSound1851 B hB hF
  · have he : k = (1852 : Fin 2425) := Fin.ext h1852
    subst k
    rw [sourceRowsAt1852]
    exact rowSound1852 B hB hF
  · have he : k = (1853 : Fin 2425) := Fin.ext h1853
    subst k
    rw [sourceRowsAt1853]
    exact rowSound1853_e B hB hF
  · have he : k = (1854 : Fin 2425) := Fin.ext h1854
    subst k
    rw [sourceRowsAt1854]
    exact rowSound1854_e B hB hF
  · have he : k = (1855 : Fin 2425) := Fin.ext h1855
    subst k
    rw [sourceRowsAt1855]
    exact rowSound1855_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115_e_oai
