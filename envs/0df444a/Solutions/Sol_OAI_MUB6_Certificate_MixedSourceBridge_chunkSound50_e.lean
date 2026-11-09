-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound50_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:21:14.930481+00:00
-- url     : https://prove2.me/submissions/b4e295bb-4aca-43e3-a64b-b8537c62c790

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5435_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound800_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound801_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound802_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound804_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound805_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound813_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound815_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15255 raw15255Labels = mixedMoment B node3733 node3733Labels := by
  calc
    mixedMoment B raw15255 raw15255Labels = mixedMoment B raw15255step0 raw15255step0Labels := by
      have hz : ∀ j, raw15255 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15255step0 = (fun i j => raw15255 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15255step0 raw15255; decide +kernel
      have hl : raw15255step0Labels = raw15255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15255 raw15255Labels permutation346 hz
    mixedMoment B raw15255step0 raw15255step0Labels = mixedMoment B raw15255step1 raw15255step1Labels := by
      have ha : raw15255step1 = (fun i j => raw15255step0 (permutation90 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15255step1 raw15255step0; decide +kernel
      have hl : raw15255step1Labels = raw15255step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15255step0 raw15255step0Labels permutation90 permutation4
    mixedMoment B raw15255step1 raw15255step1Labels = mixedMoment B raw15255step2 raw15255step2Labels := by
      have ha : raw15255step2 = -raw15255step1 := by apply Matrix.ext; change ∀ i j, raw15255step2 i j = -(raw15255step1 i j); unfold raw15255step2 raw15255step1; decide +kernel
      have hl : raw15255step2Labels = raw15255step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3733 node3733Labels := by rfl

theorem canonical15256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15256 raw15256Labels = mixedMoment B node3819 node3819Labels := by
  calc
    mixedMoment B raw15256 raw15256Labels = mixedMoment B raw15256step0 raw15256step0Labels := by
      have ha : raw15256step0 = (fun i j => raw15256 (permutation458 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15256step0 raw15256; decide +kernel
      have hl : raw15256step0Labels = raw15256Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15256 raw15256Labels permutation458 permutation4
    mixedMoment B raw15256step0 raw15256step0Labels = mixedMoment B raw15256step1 raw15256step1Labels := by
      have ha : raw15256step1 = -raw15256step0 := by apply Matrix.ext; change ∀ i j, raw15256step1 i j = -(raw15256step0 i j); unfold raw15256step1 raw15256step0; decide +kernel
      have hl : raw15256step1Labels = raw15256step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3819 node3819Labels := by rfl

theorem canonical15257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15257 raw15257Labels = mixedMoment B node2591 node2591Labels := by
  calc
    mixedMoment B raw15257 raw15257Labels = mixedMoment B raw15257step0 raw15257step0Labels := by
      have hz : ∀ j, raw15257 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15257step0 = (fun i j => raw15257 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15257step0 raw15257; decide +kernel
      have hl : raw15257step0Labels = raw15257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15257 raw15257Labels permutation346 hz
    mixedMoment B raw15257step0 raw15257step0Labels = mixedMoment B raw15257step1 raw15257step1Labels := by
      have ha : raw15257step1 = (fun i j => raw15257step0 (permutation90 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15257step1 raw15257step0; decide +kernel
      have hl : raw15257step1Labels = raw15257step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15257step0 raw15257step0Labels permutation90 permutation4
    mixedMoment B raw15257step1 raw15257step1Labels = mixedMoment B raw15257step2 raw15257step2Labels := by
      have ha : raw15257step2 = -raw15257step1 := by apply Matrix.ext; change ∀ i j, raw15257step2 i j = -(raw15257step1 i j); unfold raw15257step2 raw15257step1; decide +kernel
      have hl : raw15257step2Labels = raw15257step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2591 node2591Labels := by rfl

theorem canonical15258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15258 raw15258Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw15258 raw15258Labels = mixedMoment B raw15258step0 raw15258step0Labels := by
      have hz : ∀ j, raw15258 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15258step0 = (fun i j => raw15258 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15258step0 raw15258; decide +kernel
      have hl : raw15258step0Labels = raw15258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15258 raw15258Labels permutation346 hz
    mixedMoment B raw15258step0 raw15258step0Labels = mixedMoment B raw15258step1 raw15258step1Labels := by
      have ha : raw15258step1 = (fun i j => raw15258step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15258step1 raw15258step0; decide +kernel
      have hl : raw15258step1Labels = raw15258step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15258step0 raw15258step0Labels permutation91 permutation4
    mixedMoment B raw15258step1 raw15258step1Labels = mixedMoment B raw15258step2 raw15258step2Labels := by
      have ha : raw15258step2 = -raw15258step1 := by apply Matrix.ext; change ∀ i j, raw15258step2 i j = -(raw15258step1 i j); unfold raw15258step2 raw15258step1; decide +kernel
      have hl : raw15258step2Labels = raw15258step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical15259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15259 raw15259Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw15259 raw15259Labels = mixedMoment B raw15259step0 raw15259step0Labels := by
      have hz : ∀ j, raw15259 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15259step0 = (fun i j => raw15259 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15259step0 raw15259; decide +kernel
      have hl : raw15259step0Labels = raw15259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15259 raw15259Labels permutation346 hz
    mixedMoment B raw15259step0 raw15259step0Labels = mixedMoment B raw15259step1 raw15259step1Labels := by
      have ha : raw15259step1 = (fun i j => raw15259step0 (permutation90 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15259step1 raw15259step0; decide +kernel
      have hl : raw15259step1Labels = raw15259step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15259step0 raw15259step0Labels permutation90 permutation4
    mixedMoment B raw15259step1 raw15259step1Labels = mixedMoment B raw15259step2 raw15259step2Labels := by
      have ha : raw15259step2 = -raw15259step1 := by apply Matrix.ext; change ∀ i j, raw15259step2 i j = -(raw15259step1 i j); unfold raw15259step2 raw15259step1; decide +kernel
      have hl : raw15259step2Labels = raw15259step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3845 node3845Labels := by rfl

theorem canonical15354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15354 raw15354Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw15354 raw15354Labels = mixedMoment B raw15354step0 raw15354step0Labels := by
      have hz : ∀ j, raw15354 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15354step0 = (fun i j => raw15354 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15354step0 raw15354; decide +kernel
      have hl : raw15354step0Labels = raw15354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15354 raw15354Labels permutation346 hz
    mixedMoment B raw15354step0 raw15354step0Labels = mixedMoment B raw15354step1 raw15354step1Labels := by
      have ha : raw15354step1 = (fun i j => raw15354step0 (permutation101 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15354step1 raw15354step0; decide +kernel
      have hl : raw15354step1Labels = raw15354step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15354step0 raw15354step0Labels permutation101 permutation4
    _ = mixedMoment B node3877 node3877Labels := by rfl

theorem canonical15355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15355 raw15355Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw15355 raw15355Labels = mixedMoment B raw15355step0 raw15355step0Labels := by
      have hz : ∀ j, raw15355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15355step0 = (fun i j => raw15355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15355step0 raw15355; decide +kernel
      have hl : raw15355step0Labels = raw15355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15355 raw15355Labels permutation346 hz
    mixedMoment B raw15355step0 raw15355step0Labels = mixedMoment B raw15355step1 raw15355step1Labels := by
      have ha : raw15355step1 = (fun i j => raw15355step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15355step1 raw15355step0; decide +kernel
      have hl : raw15355step1Labels = raw15355step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15355step0 raw15355step0Labels permutation48 permutation4
    mixedMoment B raw15355step1 raw15355step1Labels = mixedMoment B raw15355step2 raw15355step2Labels := by
      have ha : raw15355step2 = -raw15355step1 := by apply Matrix.ext; change ∀ i j, raw15355step2 i j = -(raw15355step1 i j); unfold raw15355step2 raw15355step1; decide +kernel
      have hl : raw15355step2Labels = raw15355step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3180 node3180Labels := by rfl

theorem canonical15356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15356 raw15356Labels = mixedMoment B node3175 node3175Labels := by
  calc
    mixedMoment B raw15356 raw15356Labels = mixedMoment B raw15356step0 raw15356step0Labels := by
      have ha : raw15356step0 = (fun i j => raw15356 (permutation228 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15356step0 raw15356; decide +kernel
      have hl : raw15356step0Labels = raw15356Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15356 raw15356Labels permutation228 permutation4
    mixedMoment B raw15356step0 raw15356step0Labels = mixedMoment B raw15356step1 raw15356step1Labels := by
      have ha : raw15356step1 = -raw15356step0 := by apply Matrix.ext; change ∀ i j, raw15356step1 i j = -(raw15356step0 i j); unfold raw15356step1 raw15356step0; decide +kernel
      have hl : raw15356step1Labels = raw15356step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3175 node3175Labels := by rfl

theorem canonical15357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15357 raw15357Labels = mixedMoment B node2619 node2619Labels := by
  calc
    mixedMoment B raw15357 raw15357Labels = mixedMoment B raw15357step0 raw15357step0Labels := by
      have hz : ∀ j, raw15357 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15357step0 = (fun i j => raw15357 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15357step0 raw15357; decide +kernel
      have hl : raw15357step0Labels = raw15357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15357 raw15357Labels permutation346 hz
    mixedMoment B raw15357step0 raw15357step0Labels = mixedMoment B raw15357step1 raw15357step1Labels := by
      have ha : raw15357step1 = (fun i j => raw15357step0 (permutation101 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15357step1 raw15357step0; decide +kernel
      have hl : raw15357step1Labels = raw15357step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15357step0 raw15357step0Labels permutation101 permutation4
    _ = mixedMoment B node2619 node2619Labels := by rfl

theorem canonical15358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15358 raw15358Labels = mixedMoment B node3198 node3198Labels := by
  calc
    mixedMoment B raw15358 raw15358Labels = mixedMoment B raw15358step0 raw15358step0Labels := by
      have hz : ∀ j, raw15358 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15358step0 = (fun i j => raw15358 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15358step0 raw15358; decide +kernel
      have hl : raw15358step0Labels = raw15358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15358 raw15358Labels permutation346 hz
    mixedMoment B raw15358step0 raw15358step0Labels = mixedMoment B raw15358step1 raw15358step1Labels := by
      have ha : raw15358step1 = (fun i j => raw15358step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15358step1 raw15358step0; decide +kernel
      have hl : raw15358step1Labels = raw15358step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15358step0 raw15358step0Labels permutation33 permutation2
    _ = mixedMoment B node3198 node3198Labels := by rfl

theorem canonical15359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15359 raw15359Labels = mixedMoment B node2872 node2872Labels := by
  calc
    mixedMoment B raw15359 raw15359Labels = mixedMoment B raw15359step0 raw15359step0Labels := by
      have hz : ∀ j, raw15359 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15359step0 = (fun i j => raw15359 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15359step0 raw15359; decide +kernel
      have hl : raw15359step0Labels = raw15359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15359 raw15359Labels permutation346 hz
    mixedMoment B raw15359step0 raw15359step0Labels = mixedMoment B raw15359step1 raw15359step1Labels := by
      have ha : raw15359step1 = (fun i j => raw15359step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15359step1 raw15359step0; decide +kernel
      have hl : raw15359step1Labels = raw15359step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15359step0 raw15359step0Labels permutation151 permutation2
    mixedMoment B raw15359step1 raw15359step1Labels = mixedMoment B raw15359step2 raw15359step2Labels := by
      have ha : raw15359step2 = -raw15359step1 := by apply Matrix.ext; change ∀ i j, raw15359step2 i j = -(raw15359step1 i j); unfold raw15359step2 raw15359step1; decide +kernel
      have hl : raw15359step2Labels = raw15359step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2872 node2872Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical120
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15360 raw15360Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw15360 raw15360Labels = mixedMoment B raw15360step0 raw15360step0Labels := by
      have hz : ∀ j, raw15360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15360step0 = (fun i j => raw15360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15360step0 raw15360; decide +kernel
      have hl : raw15360step0Labels = raw15360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15360 raw15360Labels permutation346 hz
    mixedMoment B raw15360step0 raw15360step0Labels = mixedMoment B raw15360step1 raw15360step1Labels := by
      have hz : ∀ j, raw15360step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw15360step1 = (fun i j => raw15360step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw15360step1 raw15360step0; decide +kernel
      have hl : raw15360step1Labels = raw15360step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15360step0 raw15360step0Labels permutation32 hz
    mixedMoment B raw15360step1 raw15360step1Labels = mixedMoment B raw15360step2 raw15360step2Labels := by
      have ha : raw15360step2 = (fun i j => raw15360step1 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw15360step2 raw15360step1; decide +kernel
      have hl : raw15360step2Labels = raw15360step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15360step1 raw15360step1Labels permutation15 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical15361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15361 raw15361Labels = mixedMoment B node3788 node3788Labels := by
  calc
    mixedMoment B raw15361 raw15361Labels = mixedMoment B raw15361step0 raw15361step0Labels := by
      have ha : raw15361step0 = (fun i j => raw15361 (permutation465 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15361step0 raw15361; decide +kernel
      have hl : raw15361step0Labels = raw15361Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15361 raw15361Labels permutation465 permutation4
    _ = mixedMoment B node3788 node3788Labels := by rfl

theorem canonical15362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15362 raw15362Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw15362 raw15362Labels = mixedMoment B raw15362step0 raw15362step0Labels := by
      have hz : ∀ j, raw15362 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15362step0 = (fun i j => raw15362 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15362step0 raw15362; decide +kernel
      have hl : raw15362step0Labels = raw15362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15362 raw15362Labels permutation346 hz
    mixedMoment B raw15362step0 raw15362step0Labels = mixedMoment B raw15362step1 raw15362step1Labels := by
      have ha : raw15362step1 = (fun i j => raw15362step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15362step1 raw15362step0; decide +kernel
      have hl : raw15362step1Labels = raw15362step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15362step0 raw15362step0Labels permutation149 permutation2
    mixedMoment B raw15362step1 raw15362step1Labels = mixedMoment B raw15362step2 raw15362step2Labels := by
      have ha : raw15362step2 = -raw15362step1 := by apply Matrix.ext; change ∀ i j, raw15362step2 i j = -(raw15362step1 i j); unfold raw15362step2 raw15362step1; decide +kernel
      have hl : raw15362step2Labels = raw15362step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3959 node3959Labels := by rfl

theorem canonical15363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15363 raw15363Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw15363 raw15363Labels = mixedMoment B raw15363step0 raw15363step0Labels := by
      have hz : ∀ j, raw15363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15363step0 = (fun i j => raw15363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15363step0 raw15363; decide +kernel
      have hl : raw15363step0Labels = raw15363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15363 raw15363Labels permutation346 hz
    mixedMoment B raw15363step0 raw15363step0Labels = mixedMoment B raw15363step1 raw15363step1Labels := by
      have ha : raw15363step1 = (fun i j => raw15363step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15363step1 raw15363step0; decide +kernel
      have hl : raw15363step1Labels = raw15363step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15363step0 raw15363step0Labels permutation108 permutation4
    mixedMoment B raw15363step1 raw15363step1Labels = mixedMoment B raw15363step2 raw15363step2Labels := by
      have ha : raw15363step2 = -raw15363step1 := by apply Matrix.ext; change ∀ i j, raw15363step2 i j = -(raw15363step1 i j); unfold raw15363step2 raw15363step1; decide +kernel
      have hl : raw15363step2Labels = raw15363step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3732 node3732Labels := by rfl

theorem canonical15364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15364 raw15364Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw15364 raw15364Labels = mixedMoment B raw15364step0 raw15364step0Labels := by
      have hz : ∀ j, raw15364 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15364step0 = (fun i j => raw15364 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15364step0 raw15364; decide +kernel
      have hl : raw15364step0Labels = raw15364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15364 raw15364Labels permutation346 hz
    mixedMoment B raw15364step0 raw15364step0Labels = mixedMoment B raw15364step1 raw15364step1Labels := by
      have ha : raw15364step1 = (fun i j => raw15364step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15364step1 raw15364step0; decide +kernel
      have hl : raw15364step1Labels = raw15364step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15364step0 raw15364step0Labels permutation91 permutation4
    _ = mixedMoment B node3809 node3809Labels := by rfl

theorem canonical15365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15365 raw15365Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw15365 raw15365Labels = mixedMoment B raw15365step0 raw15365step0Labels := by
      have hz : ∀ j, raw15365 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15365step0 = (fun i j => raw15365 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15365step0 raw15365; decide +kernel
      have hl : raw15365step0Labels = raw15365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15365 raw15365Labels permutation346 hz
    mixedMoment B raw15365step0 raw15365step0Labels = mixedMoment B raw15365step1 raw15365step1Labels := by
      have ha : raw15365step1 = (fun i j => raw15365step0 (permutation100 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15365step1 raw15365step0; decide +kernel
      have hl : raw15365step1Labels = raw15365step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15365step0 raw15365step0Labels permutation100 permutation4
    _ = mixedMoment B node3884 node3884Labels := by rfl

theorem canonical15366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15366 raw15366Labels = mixedMoment B node3828 node3828Labels := by
  calc
    mixedMoment B raw15366 raw15366Labels = mixedMoment B raw15366step0 raw15366step0Labels := by
      have ha : raw15366step0 = (fun i j => raw15366 (permutation482 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15366step0 raw15366; decide +kernel
      have hl : raw15366step0Labels = raw15366Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15366 raw15366Labels permutation482 permutation4
    _ = mixedMoment B node3828 node3828Labels := by rfl

theorem canonical15367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15367 raw15367Labels = mixedMoment B node2634 node2634Labels := by
  calc
    mixedMoment B raw15367 raw15367Labels = mixedMoment B raw15367step0 raw15367step0Labels := by
      have hz : ∀ j, raw15367 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15367step0 = (fun i j => raw15367 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15367step0 raw15367; decide +kernel
      have hl : raw15367step0Labels = raw15367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15367 raw15367Labels permutation346 hz
    mixedMoment B raw15367step0 raw15367step0Labels = mixedMoment B raw15367step1 raw15367step1Labels := by
      have ha : raw15367step1 = (fun i j => raw15367step0 (permutation101 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15367step1 raw15367step0; decide +kernel
      have hl : raw15367step1Labels = raw15367step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15367step0 raw15367step0Labels permutation101 permutation4
    _ = mixedMoment B node2634 node2634Labels := by rfl

theorem canonical15368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15368 raw15368Labels = mixedMoment B node3699 node3699Labels := by
  calc
    mixedMoment B raw15368 raw15368Labels = mixedMoment B raw15368step0 raw15368step0Labels := by
      have hz : ∀ j, raw15368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15368step0 = (fun i j => raw15368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15368step0 raw15368; decide +kernel
      have hl : raw15368step0Labels = raw15368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15368 raw15368Labels permutation346 hz
    mixedMoment B raw15368step0 raw15368step0Labels = mixedMoment B raw15368step1 raw15368step1Labels := by
      have ha : raw15368step1 = (fun i j => raw15368step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15368step1 raw15368step0; decide +kernel
      have hl : raw15368step1Labels = raw15368step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15368step0 raw15368step0Labels permutation126 permutation2
    mixedMoment B raw15368step1 raw15368step1Labels = mixedMoment B raw15368step2 raw15368step2Labels := by
      have ha : raw15368step2 = -raw15368step1 := by apply Matrix.ext; change ∀ i j, raw15368step2 i j = -(raw15368step1 i j); unfold raw15368step2 raw15368step1; decide +kernel
      have hl : raw15368step2Labels = raw15368step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3699 node3699Labels := by rfl

theorem canonical15369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15369 raw15369Labels = mixedMoment B node2873 node2873Labels := by
  calc
    mixedMoment B raw15369 raw15369Labels = mixedMoment B raw15369step0 raw15369step0Labels := by
      have hz : ∀ j, raw15369 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15369step0 = (fun i j => raw15369 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15369step0 raw15369; decide +kernel
      have hl : raw15369step0Labels = raw15369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15369 raw15369Labels permutation346 hz
    mixedMoment B raw15369step0 raw15369step0Labels = mixedMoment B raw15369step1 raw15369step1Labels := by
      have ha : raw15369step1 = (fun i j => raw15369step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15369step1 raw15369step0; decide +kernel
      have hl : raw15369step1Labels = raw15369step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15369step0 raw15369step0Labels permutation150 permutation2
    mixedMoment B raw15369step1 raw15369step1Labels = mixedMoment B raw15369step2 raw15369step2Labels := by
      have ha : raw15369step2 = -raw15369step1 := by apply Matrix.ext; change ∀ i j, raw15369step2 i j = -(raw15369step1 i j); unfold raw15369step2 raw15369step1; decide +kernel
      have hl : raw15369step2Labels = raw15369step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2873 node2873Labels := by rfl

theorem canonical15370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15370 raw15370Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw15370 raw15370Labels = mixedMoment B raw15370step0 raw15370step0Labels := by
      have ha : raw15370step0 = (fun i j => raw15370 (permutation508 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15370step0 raw15370; decide +kernel
      have hl : raw15370step0Labels = raw15370Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15370 raw15370Labels permutation508 permutation4
    _ = mixedMoment B node3874 node3874Labels := by rfl

theorem canonical15371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15371 raw15371Labels = mixedMoment B node2616 node2616Labels := by
  calc
    mixedMoment B raw15371 raw15371Labels = mixedMoment B raw15371step0 raw15371step0Labels := by
      have ha : raw15371step0 = (fun i j => raw15371 (permutation509 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15371step0 raw15371; decide +kernel
      have hl : raw15371step0Labels = raw15371Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15371 raw15371Labels permutation509 permutation4
    _ = mixedMoment B node2616 node2616Labels := by rfl

theorem canonical15372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15372 raw15372Labels = mixedMoment B node3698 node3698Labels := by
  calc
    mixedMoment B raw15372 raw15372Labels = mixedMoment B raw15372step0 raw15372step0Labels := by
      have ha : raw15372step0 = (fun i j => raw15372 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15372step0 raw15372; decide +kernel
      have hl : raw15372step0Labels = raw15372Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15372 raw15372Labels permutation589 permutation2
    mixedMoment B raw15372step0 raw15372step0Labels = mixedMoment B raw15372step1 raw15372step1Labels := by
      have ha : raw15372step1 = -raw15372step0 := by apply Matrix.ext; change ∀ i j, raw15372step1 i j = -(raw15372step0 i j); unfold raw15372step1 raw15372step0; decide +kernel
      have hl : raw15372step1Labels = raw15372step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3698 node3698Labels := by rfl

theorem canonical15373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15373 raw15373Labels = mixedMoment B node2870 node2870Labels := by
  calc
    mixedMoment B raw15373 raw15373Labels = mixedMoment B raw15373step0 raw15373step0Labels := by
      have ha : raw15373step0 = (fun i j => raw15373 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15373step0 raw15373; decide +kernel
      have hl : raw15373step0Labels = raw15373Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15373 raw15373Labels permutation688 permutation2
    mixedMoment B raw15373step0 raw15373step0Labels = mixedMoment B raw15373step1 raw15373step1Labels := by
      have ha : raw15373step1 = -raw15373step0 := by apply Matrix.ext; change ∀ i j, raw15373step1 i j = -(raw15373step0 i j); unfold raw15373step1 raw15373step0; decide +kernel
      have hl : raw15373step1Labels = raw15373step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2870 node2870Labels := by rfl

theorem canonical15374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15374 raw15374Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw15374 raw15374Labels = mixedMoment B raw15374step0 raw15374step0Labels := by
      have hz : ∀ j, raw15374 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15374step0 = (fun i j => raw15374 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15374step0 raw15374; decide +kernel
      have hl : raw15374step0Labels = raw15374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15374 raw15374Labels permutation346 hz
    mixedMoment B raw15374step0 raw15374step0Labels = mixedMoment B raw15374step1 raw15374step1Labels := by
      have ha : raw15374step1 = (fun i j => raw15374step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15374step1 raw15374step0; decide +kernel
      have hl : raw15374step1Labels = raw15374step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15374step0 raw15374step0Labels permutation146 permutation2
    mixedMoment B raw15374step1 raw15374step1Labels = mixedMoment B raw15374step2 raw15374step2Labels := by
      have ha : raw15374step2 = -raw15374step1 := by apply Matrix.ext; change ∀ i j, raw15374step2 i j = -(raw15374step1 i j); unfold raw15374step2 raw15374step1; decide +kernel
      have hl : raw15374step2Labels = raw15374step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3961 node3961Labels := by rfl

theorem canonical15375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15375 raw15375Labels = mixedMoment B node3946 node3946Labels := by
  calc
    mixedMoment B raw15375 raw15375Labels = mixedMoment B raw15375step0 raw15375step0Labels := by
      have ha : raw15375step0 = (fun i j => raw15375 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15375step0 raw15375; decide +kernel
      have hl : raw15375step0Labels = raw15375Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15375 raw15375Labels permutation680 permutation2
    mixedMoment B raw15375step0 raw15375step0Labels = mixedMoment B raw15375step1 raw15375step1Labels := by
      have ha : raw15375step1 = -raw15375step0 := by apply Matrix.ext; change ∀ i j, raw15375step1 i j = -(raw15375step0 i j); unfold raw15375step1 raw15375step0; decide +kernel
      have hl : raw15375step1Labels = raw15375step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3946 node3946Labels := by rfl

theorem canonical15376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15376 raw15376Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw15376 raw15376Labels = mixedMoment B raw15376step0 raw15376step0Labels := by
      have hz : ∀ j, raw15376 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15376step0 = (fun i j => raw15376 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15376step0 raw15376; decide +kernel
      have hl : raw15376step0Labels = raw15376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15376 raw15376Labels permutation346 hz
    mixedMoment B raw15376step0 raw15376step0Labels = mixedMoment B raw15376step1 raw15376step1Labels := by
      have ha : raw15376step1 = (fun i j => raw15376step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15376step1 raw15376step0; decide +kernel
      have hl : raw15376step1Labels = raw15376step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15376step0 raw15376step0Labels permutation125 permutation2
    mixedMoment B raw15376step1 raw15376step1Labels = mixedMoment B raw15376step2 raw15376step2Labels := by
      have ha : raw15376step2 = -raw15376step1 := by apply Matrix.ext; change ∀ i j, raw15376step2 i j = -(raw15376step1 i j); unfold raw15376step2 raw15376step1; decide +kernel
      have hl : raw15376step2Labels = raw15376step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3706 node3706Labels := by rfl

theorem canonical15377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15377 raw15377Labels = mixedMoment B node2885 node2885Labels := by
  calc
    mixedMoment B raw15377 raw15377Labels = mixedMoment B raw15377step0 raw15377step0Labels := by
      have hz : ∀ j, raw15377 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15377step0 = (fun i j => raw15377 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15377step0 raw15377; decide +kernel
      have hl : raw15377step0Labels = raw15377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15377 raw15377Labels permutation346 hz
    mixedMoment B raw15377step0 raw15377step0Labels = mixedMoment B raw15377step1 raw15377step1Labels := by
      have ha : raw15377step1 = (fun i j => raw15377step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15377step1 raw15377step0; decide +kernel
      have hl : raw15377step1Labels = raw15377step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15377step0 raw15377step0Labels permutation149 permutation2
    mixedMoment B raw15377step1 raw15377step1Labels = mixedMoment B raw15377step2 raw15377step2Labels := by
      have ha : raw15377step2 = -raw15377step1 := by apply Matrix.ext; change ∀ i j, raw15377step2 i j = -(raw15377step1 i j); unfold raw15377step2 raw15377step1; decide +kernel
      have hl : raw15377step2Labels = raw15377step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2885 node2885Labels := by rfl

theorem canonical15378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15378 raw15378Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw15378 raw15378Labels = mixedMoment B raw15378step0 raw15378step0Labels := by
      have hz : ∀ j, raw15378 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15378step0 = (fun i j => raw15378 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15378step0 raw15378; decide +kernel
      have hl : raw15378step0Labels = raw15378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15378 raw15378Labels permutation346 hz
    mixedMoment B raw15378step0 raw15378step0Labels = mixedMoment B raw15378step1 raw15378step1Labels := by
      have ha : raw15378step1 = (fun i j => raw15378step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15378step1 raw15378step0; decide +kernel
      have hl : raw15378step1Labels = raw15378step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15378step0 raw15378step0Labels permutation127 permutation2
    mixedMoment B raw15378step1 raw15378step1Labels = mixedMoment B raw15378step2 raw15378step2Labels := by
      have ha : raw15378step2 = -raw15378step1 := by apply Matrix.ext; change ∀ i j, raw15378step2 i j = -(raw15378step1 i j); unfold raw15378step2 raw15378step1; decide +kernel
      have hl : raw15378step2Labels = raw15378step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3814 node3814Labels := by rfl

theorem canonical15379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15379 raw15379Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw15379 raw15379Labels = mixedMoment B raw15379step0 raw15379step0Labels := by
      have hz : ∀ j, raw15379 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15379step0 = (fun i j => raw15379 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15379step0 raw15379; decide +kernel
      have hl : raw15379step0Labels = raw15379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15379 raw15379Labels permutation346 hz
    mixedMoment B raw15379step0 raw15379step0Labels = mixedMoment B raw15379step1 raw15379step1Labels := by
      have ha : raw15379step1 = (fun i j => raw15379step0 (permutation105 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15379step1 raw15379step0; decide +kernel
      have hl : raw15379step1Labels = raw15379step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15379step0 raw15379step0Labels permutation105 permutation4
    mixedMoment B raw15379step1 raw15379step1Labels = mixedMoment B raw15379step2 raw15379step2Labels := by
      have ha : raw15379step2 = -raw15379step1 := by apply Matrix.ext; change ∀ i j, raw15379step2 i j = -(raw15379step1 i j); unfold raw15379step2 raw15379step1; decide +kernel
      have hl : raw15379step2Labels = raw15379step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical15380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15380 raw15380Labels = mixedMoment B node3723 node3723Labels := by
  calc
    mixedMoment B raw15380 raw15380Labels = mixedMoment B raw15380step0 raw15380step0Labels := by
      have ha : raw15380step0 = (fun i j => raw15380 (permutation524 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15380step0 raw15380; decide +kernel
      have hl : raw15380step0Labels = raw15380Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15380 raw15380Labels permutation524 permutation4
    mixedMoment B raw15380step0 raw15380step0Labels = mixedMoment B raw15380step1 raw15380step1Labels := by
      have ha : raw15380step1 = -raw15380step0 := by apply Matrix.ext; change ∀ i j, raw15380step1 i j = -(raw15380step0 i j); unfold raw15380step1 raw15380step0; decide +kernel
      have hl : raw15380step1Labels = raw15380step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3723 node3723Labels := by rfl

theorem canonical15381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15381 raw15381Labels = mixedMoment B node2620 node2620Labels := by
  calc
    mixedMoment B raw15381 raw15381Labels = mixedMoment B raw15381step0 raw15381step0Labels := by
      have hz : ∀ j, raw15381 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15381step0 = (fun i j => raw15381 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15381step0 raw15381; decide +kernel
      have hl : raw15381step0Labels = raw15381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15381 raw15381Labels permutation346 hz
    mixedMoment B raw15381step0 raw15381step0Labels = mixedMoment B raw15381step1 raw15381step1Labels := by
      have ha : raw15381step1 = (fun i j => raw15381step0 (permutation100 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15381step1 raw15381step0; decide +kernel
      have hl : raw15381step1Labels = raw15381step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15381step0 raw15381step0Labels permutation100 permutation4
    _ = mixedMoment B node2620 node2620Labels := by rfl

theorem canonical15382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15382 raw15382Labels = mixedMoment B node3045 node3045Labels := by
  calc
    mixedMoment B raw15382 raw15382Labels = mixedMoment B raw15382step0 raw15382step0Labels := by
      have hz : ∀ j, raw15382 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15382step0 = (fun i j => raw15382 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15382step0 raw15382; decide +kernel
      have hl : raw15382step0Labels = raw15382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15382 raw15382Labels permutation346 hz
    mixedMoment B raw15382step0 raw15382step0Labels = mixedMoment B raw15382step1 raw15382step1Labels := by
      have ha : raw15382step1 = (fun i j => raw15382step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15382step1 raw15382step0; decide +kernel
      have hl : raw15382step1Labels = raw15382step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15382step0 raw15382step0Labels permutation151 permutation2
    mixedMoment B raw15382step1 raw15382step1Labels = mixedMoment B raw15382step2 raw15382step2Labels := by
      have ha : raw15382step2 = -raw15382step1 := by apply Matrix.ext; change ∀ i j, raw15382step2 i j = -(raw15382step1 i j); unfold raw15382step2 raw15382step1; decide +kernel
      have hl : raw15382step2Labels = raw15382step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3045 node3045Labels := by rfl

theorem canonical15405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15405 raw15405Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw15405 raw15405Labels = mixedMoment B raw15405step0 raw15405step0Labels := by
      have hz : ∀ j, raw15405 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15405step0 = (fun i j => raw15405 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15405step0 raw15405; decide +kernel
      have hl : raw15405step0Labels = raw15405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15405 raw15405Labels permutation346 hz
    mixedMoment B raw15405step0 raw15405step0Labels = mixedMoment B raw15405step1 raw15405step1Labels := by
      have ha : raw15405step1 = (fun i j => raw15405step0 (permutation146 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15405step1 raw15405step0; decide +kernel
      have hl : raw15405step1Labels = raw15405step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15405step0 raw15405step0Labels permutation146 permutation7
    mixedMoment B raw15405step1 raw15405step1Labels = mixedMoment B raw15405step2 raw15405step2Labels := by
      have ha : raw15405step2 = raw15405step1 := by apply Matrix.ext; unfold raw15405step2 raw15405step1; decide +kernel
      have hl : raw15405step1Labels = labelEmbedding10 ∘ raw15405step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15405step1 raw15405step1Labels raw15405step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical15406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15406 raw15406Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw15406 raw15406Labels = mixedMoment B raw15406step0 raw15406step0Labels := by
      have ha : raw15406step0 = (fun i j => raw15406 (permutation667 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15406step0 raw15406; decide +kernel
      have hl : raw15406step0Labels = raw15406Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15406 raw15406Labels permutation667 permutation7
    mixedMoment B raw15406step0 raw15406step0Labels = mixedMoment B raw15406step1 raw15406step1Labels := by
      have ha : raw15406step1 = raw15406step0 := by apply Matrix.ext; unfold raw15406step1 raw15406step0; decide +kernel
      have hl : raw15406step0Labels = labelEmbedding10 ∘ raw15406step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15406step0 raw15406step0Labels raw15406step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical15407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15407 raw15407Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw15407 raw15407Labels = mixedMoment B raw15407step0 raw15407step0Labels := by
      have hz : ∀ j, raw15407 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15407step0 = (fun i j => raw15407 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15407step0 raw15407; decide +kernel
      have hl : raw15407step0Labels = raw15407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15407 raw15407Labels permutation346 hz
    mixedMoment B raw15407step0 raw15407step0Labels = mixedMoment B raw15407step1 raw15407step1Labels := by
      have ha : raw15407step1 = (fun i j => raw15407step0 (permutation146 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15407step1 raw15407step0; decide +kernel
      have hl : raw15407step1Labels = raw15407step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15407step0 raw15407step0Labels permutation146 permutation7
    mixedMoment B raw15407step1 raw15407step1Labels = mixedMoment B raw15407step2 raw15407step2Labels := by
      have ha : raw15407step2 = raw15407step1 := by apply Matrix.ext; unfold raw15407step2 raw15407step1; decide +kernel
      have hl : raw15407step1Labels = labelEmbedding10 ∘ raw15407step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15407step1 raw15407step1Labels raw15407step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

theorem canonical15408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15408 raw15408Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw15408 raw15408Labels = mixedMoment B raw15408step0 raw15408step0Labels := by
      have hz : ∀ j, raw15408 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15408step0 = (fun i j => raw15408 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15408step0 raw15408; decide +kernel
      have hl : raw15408step0Labels = raw15408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15408 raw15408Labels permutation346 hz
    mixedMoment B raw15408step0 raw15408step0Labels = mixedMoment B raw15408step1 raw15408step1Labels := by
      have ha : raw15408step1 = (fun i j => raw15408step0 (permutation86 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15408step1 raw15408step0; decide +kernel
      have hl : raw15408step1Labels = raw15408step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15408step0 raw15408step0Labels permutation86 permutation6
    mixedMoment B raw15408step1 raw15408step1Labels = mixedMoment B raw15408step2 raw15408step2Labels := by
      have ha : raw15408step2 = -raw15408step1 := by apply Matrix.ext; change ∀ i j, raw15408step2 i j = -(raw15408step1 i j); unfold raw15408step2 raw15408step1; decide +kernel
      have hl : raw15408step2Labels = raw15408step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15408step2 raw15408step2Labels = mixedMoment B raw15408step3 raw15408step3Labels := by
      have ha : raw15408step3 = raw15408step2 := by apply Matrix.ext; unfold raw15408step3 raw15408step2; decide +kernel
      have hl : raw15408step2Labels = labelEmbedding9 ∘ raw15408step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15408step2 raw15408step2Labels raw15408step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical15409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15409 raw15409Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw15409 raw15409Labels = mixedMoment B raw15409step0 raw15409step0Labels := by
      have hz : ∀ j, raw15409 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15409step0 = (fun i j => raw15409 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15409step0 raw15409; decide +kernel
      have hl : raw15409step0Labels = raw15409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15409 raw15409Labels permutation346 hz
    mixedMoment B raw15409step0 raw15409step0Labels = mixedMoment B raw15409step1 raw15409step1Labels := by
      have ha : raw15409step1 = (fun i j => raw15409step0 (permutation86 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15409step1 raw15409step0; decide +kernel
      have hl : raw15409step1Labels = raw15409step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15409step0 raw15409step0Labels permutation86 permutation6
    mixedMoment B raw15409step1 raw15409step1Labels = mixedMoment B raw15409step2 raw15409step2Labels := by
      have ha : raw15409step2 = -raw15409step1 := by apply Matrix.ext; change ∀ i j, raw15409step2 i j = -(raw15409step1 i j); unfold raw15409step2 raw15409step1; decide +kernel
      have hl : raw15409step2Labels = raw15409step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15409step2 raw15409step2Labels = mixedMoment B raw15409step3 raw15409step3Labels := by
      have ha : raw15409step3 = raw15409step2 := by apply Matrix.ext; unfold raw15409step3 raw15409step2; decide +kernel
      have hl : raw15409step2Labels = labelEmbedding9 ∘ raw15409step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15409step2 raw15409step2Labels raw15409step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical15410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15410 raw15410Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw15410 raw15410Labels = mixedMoment B raw15410step0 raw15410step0Labels := by
      have hz : ∀ j, raw15410 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15410step0 = (fun i j => raw15410 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15410step0 raw15410; decide +kernel
      have hl : raw15410step0Labels = raw15410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15410 raw15410Labels permutation346 hz
    mixedMoment B raw15410step0 raw15410step0Labels = mixedMoment B raw15410step1 raw15410step1Labels := by
      have ha : raw15410step1 = (fun i j => raw15410step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15410step1 raw15410step0; decide +kernel
      have hl : raw15410step1Labels = raw15410step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15410step0 raw15410step0Labels permutation32 permutation3
    mixedMoment B raw15410step1 raw15410step1Labels = mixedMoment B raw15410step2 raw15410step2Labels := by
      have ha : raw15410step2 = raw15410step1 := by apply Matrix.ext; unfold raw15410step2 raw15410step1; decide +kernel
      have hl : raw15410step1Labels = labelEmbedding6 ∘ raw15410step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15410step1 raw15410step1Labels raw15410step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4891 node4891Labels := by rfl

theorem canonical15411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15411 raw15411Labels = mixedMoment B node5407 node5407Labels := by
  calc
    mixedMoment B raw15411 raw15411Labels = mixedMoment B raw15411step0 raw15411step0Labels := by
      have ha : raw15411step0 = (fun i j => raw15411 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15411step0 raw15411; decide +kernel
      have hl : raw15411step0Labels = raw15411Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15411 raw15411Labels permutation676 permutation2
    mixedMoment B raw15411step0 raw15411step0Labels = mixedMoment B raw15411step1 raw15411step1Labels := by
      have ha : raw15411step1 = -raw15411step0 := by apply Matrix.ext; change ∀ i j, raw15411step1 i j = -(raw15411step0 i j); unfold raw15411step1 raw15411step0; decide +kernel
      have hl : raw15411step1Labels = raw15411step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5407 node5407Labels := by rfl

theorem canonical15412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15412 raw15412Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw15412 raw15412Labels = mixedMoment B raw15412step0 raw15412step0Labels := by
      have hz : ∀ j, raw15412 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15412step0 = (fun i j => raw15412 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15412step0 raw15412; decide +kernel
      have hl : raw15412step0Labels = raw15412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15412 raw15412Labels permutation346 hz
    mixedMoment B raw15412step0 raw15412step0Labels = mixedMoment B raw15412step1 raw15412step1Labels := by
      have ha : raw15412step1 = (fun i j => raw15412step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15412step1 raw15412step0; decide +kernel
      have hl : raw15412step1Labels = raw15412step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15412step0 raw15412step0Labels permutation149 permutation2
    mixedMoment B raw15412step1 raw15412step1Labels = mixedMoment B raw15412step2 raw15412step2Labels := by
      have ha : raw15412step2 = -raw15412step1 := by apply Matrix.ext; change ∀ i j, raw15412step2 i j = -(raw15412step1 i j); unfold raw15412step2 raw15412step1; decide +kernel
      have hl : raw15412step2Labels = raw15412step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical15413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15413 raw15413Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw15413 raw15413Labels = mixedMoment B raw15413step0 raw15413step0Labels := by
      have hz : ∀ j, raw15413 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15413step0 = (fun i j => raw15413 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15413step0 raw15413; decide +kernel
      have hl : raw15413step0Labels = raw15413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15413 raw15413Labels permutation346 hz
    mixedMoment B raw15413step0 raw15413step0Labels = mixedMoment B raw15413step1 raw15413step1Labels := by
      have ha : raw15413step1 = (fun i j => raw15413step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15413step1 raw15413step0; decide +kernel
      have hl : raw15413step1Labels = raw15413step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15413step0 raw15413step0Labels permutation91 permutation4
    mixedMoment B raw15413step1 raw15413step1Labels = mixedMoment B raw15413step2 raw15413step2Labels := by
      have ha : raw15413step2 = raw15413step1 := by apply Matrix.ext; unfold raw15413step2 raw15413step1; decide +kernel
      have hl : raw15413step1Labels = labelEmbedding7 ∘ raw15413step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15413step1 raw15413step1Labels raw15413step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

theorem canonical15414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15414 raw15414Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw15414 raw15414Labels = mixedMoment B raw15414step0 raw15414step0Labels := by
      have hz : ∀ j, raw15414 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15414step0 = (fun i j => raw15414 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15414step0 raw15414; decide +kernel
      have hl : raw15414step0Labels = raw15414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15414 raw15414Labels permutation346 hz
    mixedMoment B raw15414step0 raw15414step0Labels = mixedMoment B raw15414step1 raw15414step1Labels := by
      have ha : raw15414step1 = (fun i j => raw15414step0 (permutation89 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15414step1 raw15414step0; decide +kernel
      have hl : raw15414step1Labels = raw15414step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15414step0 raw15414step0Labels permutation89 permutation4
    mixedMoment B raw15414step1 raw15414step1Labels = mixedMoment B raw15414step2 raw15414step2Labels := by
      have ha : raw15414step2 = raw15414step1 := by apply Matrix.ext; unfold raw15414step2 raw15414step1; decide +kernel
      have hl : raw15414step1Labels = labelEmbedding7 ∘ raw15414step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15414step1 raw15414step1Labels raw15414step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical15415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15415 raw15415Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw15415 raw15415Labels = mixedMoment B raw15415step0 raw15415step0Labels := by
      have ha : raw15415step0 = (fun i j => raw15415 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15415step0 raw15415; decide +kernel
      have hl : raw15415step0Labels = raw15415Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15415 raw15415Labels permutation160 permutation3
    mixedMoment B raw15415step0 raw15415step0Labels = mixedMoment B raw15415step1 raw15415step1Labels := by
      have ha : raw15415step1 = raw15415step0 := by apply Matrix.ext; unfold raw15415step1 raw15415step0; decide +kernel
      have hl : raw15415step0Labels = labelEmbedding6 ∘ raw15415step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15415step0 raw15415step0Labels raw15415step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4816 node4816Labels := by rfl

theorem canonical15416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15416 raw15416Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw15416 raw15416Labels = mixedMoment B raw15416step0 raw15416step0Labels := by
      have ha : raw15416step0 = (fun i j => raw15416 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15416step0 raw15416; decide +kernel
      have hl : raw15416step0Labels = raw15416Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15416 raw15416Labels permutation160 permutation3
    mixedMoment B raw15416step0 raw15416step0Labels = mixedMoment B raw15416step1 raw15416step1Labels := by
      have ha : raw15416step1 = raw15416step0 := by apply Matrix.ext; unfold raw15416step1 raw15416step0; decide +kernel
      have hl : raw15416step0Labels = labelEmbedding6 ∘ raw15416step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15416step0 raw15416step0Labels raw15416step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5360 node5360Labels := by rfl

theorem canonical15417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15417 raw15417Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw15417 raw15417Labels = mixedMoment B raw15417step0 raw15417step0Labels := by
      have ha : raw15417step0 = (fun i j => raw15417 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15417step0 raw15417; decide +kernel
      have hl : raw15417step0Labels = raw15417Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15417 raw15417Labels permutation680 permutation2
    mixedMoment B raw15417step0 raw15417step0Labels = mixedMoment B raw15417step1 raw15417step1Labels := by
      have ha : raw15417step1 = -raw15417step0 := by apply Matrix.ext; change ∀ i j, raw15417step1 i j = -(raw15417step0 i j); unfold raw15417step1 raw15417step0; decide +kernel
      have hl : raw15417step1Labels = raw15417step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5397 node5397Labels := by rfl

theorem canonical15418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15418 raw15418Labels = mixedMoment B node5426 node5426Labels := by
  calc
    mixedMoment B raw15418 raw15418Labels = mixedMoment B raw15418step0 raw15418step0Labels := by
      have ha : raw15418step0 = (fun i j => raw15418 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15418step0 raw15418; decide +kernel
      have hl : raw15418step0Labels = raw15418Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15418 raw15418Labels permutation646 permutation2
    mixedMoment B raw15418step0 raw15418step0Labels = mixedMoment B raw15418step1 raw15418step1Labels := by
      have ha : raw15418step1 = -raw15418step0 := by apply Matrix.ext; change ∀ i j, raw15418step1 i j = -(raw15418step0 i j); unfold raw15418step1 raw15418step0; decide +kernel
      have hl : raw15418step1Labels = raw15418step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5426 node5426Labels := by rfl

theorem canonical15419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15419 raw15419Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw15419 raw15419Labels = mixedMoment B raw15419step0 raw15419step0Labels := by
      have ha : raw15419step0 = (fun i j => raw15419 (permutation473 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15419step0 raw15419; decide +kernel
      have hl : raw15419step0Labels = raw15419Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15419 raw15419Labels permutation473 permutation4
    mixedMoment B raw15419step0 raw15419step0Labels = mixedMoment B raw15419step1 raw15419step1Labels := by
      have ha : raw15419step1 = raw15419step0 := by apply Matrix.ext; unfold raw15419step1 raw15419step0; decide +kernel
      have hl : raw15419step0Labels = labelEmbedding7 ∘ raw15419step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15419step0 raw15419step0Labels raw15419step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical15420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15420 raw15420Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw15420 raw15420Labels = mixedMoment B raw15420step0 raw15420step0Labels := by
      have hz : ∀ j, raw15420 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15420step0 = (fun i j => raw15420 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15420step0 raw15420; decide +kernel
      have hl : raw15420step0Labels = raw15420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15420 raw15420Labels permutation346 hz
    mixedMoment B raw15420step0 raw15420step0Labels = mixedMoment B raw15420step1 raw15420step1Labels := by
      have ha : raw15420step1 = (fun i j => raw15420step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15420step1 raw15420step0; decide +kernel
      have hl : raw15420step1Labels = raw15420step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15420step0 raw15420step0Labels permutation34 permutation3
    mixedMoment B raw15420step1 raw15420step1Labels = mixedMoment B raw15420step2 raw15420step2Labels := by
      have ha : raw15420step2 = raw15420step1 := by apply Matrix.ext; unfold raw15420step2 raw15420step1; decide +kernel
      have hl : raw15420step1Labels = labelEmbedding6 ∘ raw15420step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15420step1 raw15420step1Labels raw15420step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4836 node4836Labels := by rfl

theorem canonical15421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15421 raw15421Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw15421 raw15421Labels = mixedMoment B raw15421step0 raw15421step0Labels := by
      have hz : ∀ j, raw15421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15421step0 = (fun i j => raw15421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15421step0 raw15421; decide +kernel
      have hl : raw15421step0Labels = raw15421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15421 raw15421Labels permutation346 hz
    mixedMoment B raw15421step0 raw15421step0Labels = mixedMoment B raw15421step1 raw15421step1Labels := by
      have ha : raw15421step1 = (fun i j => raw15421step0 (permutation97 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15421step1 raw15421step0; decide +kernel
      have hl : raw15421step1Labels = raw15421step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15421step0 raw15421step0Labels permutation97 permutation4
    mixedMoment B raw15421step1 raw15421step1Labels = mixedMoment B raw15421step2 raw15421step2Labels := by
      have ha : raw15421step2 = raw15421step1 := by apply Matrix.ext; unfold raw15421step2 raw15421step1; decide +kernel
      have hl : raw15421step1Labels = labelEmbedding7 ∘ raw15421step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15421step1 raw15421step1Labels raw15421step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5287 node5287Labels := by rfl

theorem canonical15422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15422 raw15422Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw15422 raw15422Labels = mixedMoment B raw15422step0 raw15422step0Labels := by
      have ha : raw15422step0 = (fun i j => raw15422 (permutation463 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15422step0 raw15422; decide +kernel
      have hl : raw15422step0Labels = raw15422Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15422 raw15422Labels permutation463 permutation4
    mixedMoment B raw15422step0 raw15422step0Labels = mixedMoment B raw15422step1 raw15422step1Labels := by
      have ha : raw15422step1 = raw15422step0 := by apply Matrix.ext; unfold raw15422step1 raw15422step0; decide +kernel
      have hl : raw15422step0Labels = labelEmbedding7 ∘ raw15422step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15422step0 raw15422step0Labels raw15422step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5254 node5254Labels := by rfl

theorem canonical15423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15423 raw15423Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw15423 raw15423Labels = mixedMoment B raw15423step0 raw15423step0Labels := by
      have hz : ∀ j, raw15423 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15423step0 = (fun i j => raw15423 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15423step0 raw15423; decide +kernel
      have hl : raw15423step0Labels = raw15423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15423 raw15423Labels permutation346 hz
    mixedMoment B raw15423step0 raw15423step0Labels = mixedMoment B raw15423step1 raw15423step1Labels := by
      have ha : raw15423step1 = (fun i j => raw15423step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15423step1 raw15423step0; decide +kernel
      have hl : raw15423step1Labels = raw15423step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15423step0 raw15423step0Labels permutation91 permutation4
    mixedMoment B raw15423step1 raw15423step1Labels = mixedMoment B raw15423step2 raw15423step2Labels := by
      have ha : raw15423step2 = raw15423step1 := by apply Matrix.ext; unfold raw15423step2 raw15423step1; decide +kernel
      have hl : raw15423step1Labels = labelEmbedding7 ∘ raw15423step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15423step1 raw15423step1Labels raw15423step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

theorem canonical15424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15424 raw15424Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw15424 raw15424Labels = mixedMoment B raw15424step0 raw15424step0Labels := by
      have hz : ∀ j, raw15424 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15424step0 = (fun i j => raw15424 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15424step0 raw15424; decide +kernel
      have hl : raw15424step0Labels = raw15424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15424 raw15424Labels permutation346 hz
    mixedMoment B raw15424step0 raw15424step0Labels = mixedMoment B raw15424step1 raw15424step1Labels := by
      have ha : raw15424step1 = (fun i j => raw15424step0 (permutation89 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15424step1 raw15424step0; decide +kernel
      have hl : raw15424step1Labels = raw15424step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15424step0 raw15424step0Labels permutation89 permutation4
    mixedMoment B raw15424step1 raw15424step1Labels = mixedMoment B raw15424step2 raw15424step2Labels := by
      have ha : raw15424step2 = raw15424step1 := by apply Matrix.ext; unfold raw15424step2 raw15424step1; decide +kernel
      have hl : raw15424step1Labels = labelEmbedding7 ∘ raw15424step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15424step1 raw15424step1Labels raw15424step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

theorem canonical15425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15425 raw15425Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw15425 raw15425Labels = mixedMoment B raw15425step0 raw15425step0Labels := by
      have hz : ∀ j, raw15425 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15425step0 = (fun i j => raw15425 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15425step0 raw15425; decide +kernel
      have hl : raw15425step0Labels = raw15425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15425 raw15425Labels permutation346 hz
    mixedMoment B raw15425step0 raw15425step0Labels = mixedMoment B raw15425step1 raw15425step1Labels := by
      have ha : raw15425step1 = (fun i j => raw15425step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15425step1 raw15425step0; decide +kernel
      have hl : raw15425step1Labels = raw15425step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15425step0 raw15425step0Labels permutation33 permutation3
    mixedMoment B raw15425step1 raw15425step1Labels = mixedMoment B raw15425step2 raw15425step2Labels := by
      have ha : raw15425step2 = raw15425step1 := by apply Matrix.ext; unfold raw15425step2 raw15425step1; decide +kernel
      have hl : raw15425step1Labels = labelEmbedding6 ∘ raw15425step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15425step1 raw15425step1Labels raw15425step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4821 node4821Labels := by rfl

theorem canonical15426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15426 raw15426Labels = mixedMoment B node5361 node5361Labels := by
  calc
    mixedMoment B raw15426 raw15426Labels = mixedMoment B raw15426step0 raw15426step0Labels := by
      have hz : ∀ j, raw15426 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15426step0 = (fun i j => raw15426 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15426step0 raw15426; decide +kernel
      have hl : raw15426step0Labels = raw15426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15426 raw15426Labels permutation346 hz
    mixedMoment B raw15426step0 raw15426step0Labels = mixedMoment B raw15426step1 raw15426step1Labels := by
      have ha : raw15426step1 = (fun i j => raw15426step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15426step1 raw15426step0; decide +kernel
      have hl : raw15426step1Labels = raw15426step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15426step0 raw15426step0Labels permutation150 permutation2
    mixedMoment B raw15426step1 raw15426step1Labels = mixedMoment B raw15426step2 raw15426step2Labels := by
      have ha : raw15426step2 = -raw15426step1 := by apply Matrix.ext; change ∀ i j, raw15426step2 i j = -(raw15426step1 i j); unfold raw15426step2 raw15426step1; decide +kernel
      have hl : raw15426step2Labels = raw15426step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5361 node5361Labels := by rfl

theorem canonical15427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15427 raw15427Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw15427 raw15427Labels = mixedMoment B raw15427step0 raw15427step0Labels := by
      have ha : raw15427step0 = (fun i j => raw15427 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15427step0 raw15427; decide +kernel
      have hl : raw15427step0Labels = raw15427Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15427 raw15427Labels permutation688 permutation2
    mixedMoment B raw15427step0 raw15427step0Labels = mixedMoment B raw15427step1 raw15427step1Labels := by
      have ha : raw15427step1 = -raw15427step0 := by apply Matrix.ext; change ∀ i j, raw15427step1 i j = -(raw15427step0 i j); unfold raw15427step1 raw15427step0; decide +kernel
      have hl : raw15427step1Labels = raw15427step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5360 node5360Labels := by rfl

theorem canonical15428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15428 raw15428Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw15428 raw15428Labels = mixedMoment B raw15428step0 raw15428step0Labels := by
      have hz : ∀ j, raw15428 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15428step0 = (fun i j => raw15428 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15428step0 raw15428; decide +kernel
      have hl : raw15428step0Labels = raw15428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15428 raw15428Labels permutation346 hz
    mixedMoment B raw15428step0 raw15428step0Labels = mixedMoment B raw15428step1 raw15428step1Labels := by
      have ha : raw15428step1 = (fun i j => raw15428step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15428step1 raw15428step0; decide +kernel
      have hl : raw15428step1Labels = raw15428step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15428step0 raw15428step0Labels permutation149 permutation2
    mixedMoment B raw15428step1 raw15428step1Labels = mixedMoment B raw15428step2 raw15428step2Labels := by
      have ha : raw15428step2 = -raw15428step1 := by apply Matrix.ext; change ∀ i j, raw15428step2 i j = -(raw15428step1 i j); unfold raw15428step2 raw15428step1; decide +kernel
      have hl : raw15428step2Labels = raw15428step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5370 node5370Labels := by rfl

theorem canonical15429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15429 raw15429Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw15429 raw15429Labels = mixedMoment B raw15429step0 raw15429step0Labels := by
      have hz : ∀ j, raw15429 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15429step0 = (fun i j => raw15429 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15429step0 raw15429; decide +kernel
      have hl : raw15429step0Labels = raw15429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15429 raw15429Labels permutation346 hz
    mixedMoment B raw15429step0 raw15429step0Labels = mixedMoment B raw15429step1 raw15429step1Labels := by
      have ha : raw15429step1 = (fun i j => raw15429step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15429step1 raw15429step0; decide +kernel
      have hl : raw15429step1Labels = raw15429step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15429step0 raw15429step0Labels permutation33 permutation3
    mixedMoment B raw15429step1 raw15429step1Labels = mixedMoment B raw15429step2 raw15429step2Labels := by
      have ha : raw15429step2 = raw15429step1 := by apply Matrix.ext; unfold raw15429step2 raw15429step1; decide +kernel
      have hl : raw15429step1Labels = labelEmbedding6 ∘ raw15429step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15429step1 raw15429step1Labels raw15429step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

theorem canonical15430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15430 raw15430Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw15430 raw15430Labels = mixedMoment B raw15430step0 raw15430step0Labels := by
      have hz : ∀ j, raw15430 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15430step0 = (fun i j => raw15430 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15430step0 raw15430; decide +kernel
      have hl : raw15430step0Labels = raw15430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15430 raw15430Labels permutation346 hz
    mixedMoment B raw15430step0 raw15430step0Labels = mixedMoment B raw15430step1 raw15430step1Labels := by
      have ha : raw15430step1 = (fun i j => raw15430step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15430step1 raw15430step0; decide +kernel
      have hl : raw15430step1Labels = raw15430step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15430step0 raw15430step0Labels permutation32 permutation3
    mixedMoment B raw15430step1 raw15430step1Labels = mixedMoment B raw15430step2 raw15430step2Labels := by
      have ha : raw15430step2 = raw15430step1 := by apply Matrix.ext; unfold raw15430step2 raw15430step1; decide +kernel
      have hl : raw15430step1Labels = labelEmbedding6 ∘ raw15430step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15430step1 raw15430step1Labels raw15430step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4817 node4817Labels := by rfl

theorem canonical15431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15431 raw15431Labels = mixedMoment B node5090 node5090Labels := by
  calc
    mixedMoment B raw15431 raw15431Labels = mixedMoment B raw15431step0 raw15431step0Labels := by
      have hz : ∀ j, raw15431 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15431step0 = (fun i j => raw15431 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15431step0 raw15431; decide +kernel
      have hl : raw15431step0Labels = raw15431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15431 raw15431Labels permutation346 hz
    mixedMoment B raw15431step0 raw15431step0Labels = mixedMoment B raw15431step1 raw15431step1Labels := by
      have ha : raw15431step1 = (fun i j => raw15431step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15431step1 raw15431step0; decide +kernel
      have hl : raw15431step1Labels = raw15431step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15431step0 raw15431step0Labels permutation150 permutation2
    mixedMoment B raw15431step1 raw15431step1Labels = mixedMoment B raw15431step2 raw15431step2Labels := by
      have ha : raw15431step2 = -raw15431step1 := by apply Matrix.ext; change ∀ i j, raw15431step2 i j = -(raw15431step1 i j); unfold raw15431step2 raw15431step1; decide +kernel
      have hl : raw15431step2Labels = raw15431step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5090 node5090Labels := by rfl

theorem canonical15432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15432 raw15432Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw15432 raw15432Labels = mixedMoment B raw15432step0 raw15432step0Labels := by
      have ha : raw15432step0 = (fun i j => raw15432 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15432step0 raw15432; decide +kernel
      have hl : raw15432step0Labels = raw15432Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15432 raw15432Labels permutation688 permutation2
    mixedMoment B raw15432step0 raw15432step0Labels = mixedMoment B raw15432step1 raw15432step1Labels := by
      have ha : raw15432step1 = -raw15432step0 := by apply Matrix.ext; change ∀ i j, raw15432step1 i j = -(raw15432step0 i j); unfold raw15432step1 raw15432step0; decide +kernel
      have hl : raw15432step1Labels = raw15432step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5086 node5086Labels := by rfl

theorem canonical15433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15433 raw15433Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw15433 raw15433Labels = mixedMoment B raw15433step0 raw15433step0Labels := by
      have hz : ∀ j, raw15433 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15433step0 = (fun i j => raw15433 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15433step0 raw15433; decide +kernel
      have hl : raw15433step0Labels = raw15433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15433 raw15433Labels permutation346 hz
    mixedMoment B raw15433step0 raw15433step0Labels = mixedMoment B raw15433step1 raw15433step1Labels := by
      have ha : raw15433step1 = (fun i j => raw15433step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15433step1 raw15433step0; decide +kernel
      have hl : raw15433step1Labels = raw15433step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15433step0 raw15433step0Labels permutation149 permutation2
    mixedMoment B raw15433step1 raw15433step1Labels = mixedMoment B raw15433step2 raw15433step2Labels := by
      have ha : raw15433step2 = -raw15433step1 := by apply Matrix.ext; change ∀ i j, raw15433step2 i j = -(raw15433step1 i j); unfold raw15433step2 raw15433step1; decide +kernel
      have hl : raw15433step2Labels = raw15433step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5105 node5105Labels := by rfl

theorem canonical15434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15434 raw15434Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw15434 raw15434Labels = mixedMoment B raw15434step0 raw15434step0Labels := by
      have hz : ∀ j, raw15434 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15434step0 = (fun i j => raw15434 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15434step0 raw15434; decide +kernel
      have hl : raw15434step0Labels = raw15434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15434 raw15434Labels permutation346 hz
    mixedMoment B raw15434step0 raw15434step0Labels = mixedMoment B raw15434step1 raw15434step1Labels := by
      have ha : raw15434step1 = (fun i j => raw15434step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15434step1 raw15434step0; decide +kernel
      have hl : raw15434step1Labels = raw15434step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15434step0 raw15434step0Labels permutation151 permutation2
    mixedMoment B raw15434step1 raw15434step1Labels = mixedMoment B raw15434step2 raw15434step2Labels := by
      have ha : raw15434step2 = -raw15434step1 := by apply Matrix.ext; change ∀ i j, raw15434step2 i j = -(raw15434step1 i j); unfold raw15434step2 raw15434step1; decide +kernel
      have hl : raw15434step2Labels = raw15434step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5267 node5267Labels := by rfl

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

theorem canonical2130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2130 raw2130Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw2130 raw2130Labels = mixedMoment B raw2130step0 raw2130step0Labels := by
      have ha : raw2130step0 = (fun i j => raw2130 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2130step0 raw2130; decide +kernel
      have hl : raw2130step0Labels = raw2130Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2130 raw2130Labels permutation32 permutation4
    mixedMoment B raw2130step0 raw2130step0Labels = mixedMoment B raw2130step1 raw2130step1Labels := by
      have ha : raw2130step1 = raw2130step0 := by apply Matrix.ext; unfold raw2130step1 raw2130step0; decide +kernel
      have hl : raw2130step0Labels = labelEmbedding7 ∘ raw2130step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2130step0 raw2130step0Labels raw2130step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

theorem canonical2131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2131 raw2131Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw2131 raw2131Labels = mixedMoment B raw2131step0 raw2131step0Labels := by
      have ha : raw2131step0 = (fun i j => raw2131 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2131step0 raw2131; decide +kernel
      have hl : raw2131step0Labels = raw2131Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2131 raw2131Labels permutation32 permutation4
    _ = mixedMoment B node2515 node2515Labels := by rfl

theorem canonical2132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2132 raw2132Labels = mixedMoment B node3479 node3479Labels := by
  calc
    mixedMoment B raw2132 raw2132Labels = mixedMoment B raw2132step0 raw2132step0Labels := by
      have ha : raw2132step0 = (fun i j => raw2132 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2132step0 raw2132; decide +kernel
      have hl : raw2132step0Labels = raw2132Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2132 raw2132Labels permutation36 permutation6
    mixedMoment B raw2132step0 raw2132step0Labels = mixedMoment B raw2132step1 raw2132step1Labels := by
      have ha : raw2132step1 = -raw2132step0 := by apply Matrix.ext; change ∀ i j, raw2132step1 i j = -(raw2132step0 i j); unfold raw2132step1 raw2132step0; decide +kernel
      have hl : raw2132step1Labels = raw2132step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2132step1 raw2132step1Labels = mixedMoment B raw2132step2 raw2132step2Labels := by
      have ha : raw2132step2 = raw2132step1 := by apply Matrix.ext; unfold raw2132step2 raw2132step1; decide +kernel
      have hl : raw2132step1Labels = labelEmbedding1 ∘ raw2132step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2132step1 raw2132step1Labels raw2132step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3479 node3479Labels := by rfl

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

theorem canonical2418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2418 raw2418Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw2418 raw2418Labels = mixedMoment B raw2418step0 raw2418step0Labels := by
      have ha : raw2418step0 = (fun i j => raw2418 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2418step0 raw2418; decide +kernel
      have hl : raw2418step0Labels = raw2418Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2418 raw2418Labels permutation32 permutation4
    mixedMoment B raw2418step0 raw2418step0Labels = mixedMoment B raw2418step1 raw2418step1Labels := by
      have ha : raw2418step1 = raw2418step0 := by apply Matrix.ext; unfold raw2418step1 raw2418step0; decide +kernel
      have hl : raw2418step0Labels = labelEmbedding7 ∘ raw2418step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2418step0 raw2418step0Labels raw2418step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

theorem canonical2419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2419 raw2419Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw2419 raw2419Labels = mixedMoment B raw2419step0 raw2419step0Labels := by
      have ha : raw2419step0 = (fun i j => raw2419 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2419step0 raw2419; decide +kernel
      have hl : raw2419step0Labels = raw2419Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2419 raw2419Labels permutation32 permutation4
    _ = mixedMoment B node3706 node3706Labels := by rfl

theorem canonical2420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2420 raw2420Labels = mixedMoment B node3771 node3771Labels := by
  calc
    mixedMoment B raw2420 raw2420Labels = mixedMoment B raw2420step0 raw2420step0Labels := by
      have ha : raw2420step0 = (fun i j => raw2420 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2420step0 raw2420; decide +kernel
      have hl : raw2420step0Labels = raw2420Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2420 raw2420Labels permutation36 permutation6
    mixedMoment B raw2420step0 raw2420step0Labels = mixedMoment B raw2420step1 raw2420step1Labels := by
      have ha : raw2420step1 = -raw2420step0 := by apply Matrix.ext; change ∀ i j, raw2420step1 i j = -(raw2420step0 i j); unfold raw2420step1 raw2420step0; decide +kernel
      have hl : raw2420step1Labels = raw2420step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2420step1 raw2420step1Labels = mixedMoment B raw2420step2 raw2420step2Labels := by
      have ha : raw2420step2 = raw2420step1 := by apply Matrix.ext; unfold raw2420step2 raw2420step1; decide +kernel
      have hl : raw2420step1Labels = labelEmbedding1 ∘ raw2420step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2420step1 raw2420step1Labels raw2420step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3771 node3771Labels := by rfl

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

theorem canonical2466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2466 raw2466Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw2466 raw2466Labels = mixedMoment B raw2466step0 raw2466step0Labels := by
      have ha : raw2466step0 = (fun i j => raw2466 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2466step0 raw2466; decide +kernel
      have hl : raw2466step0Labels = raw2466Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2466 raw2466Labels permutation152 permutation4
    mixedMoment B raw2466step0 raw2466step0Labels = mixedMoment B raw2466step1 raw2466step1Labels := by
      have ha : raw2466step1 = raw2466step0 := by apply Matrix.ext; unfold raw2466step1 raw2466step0; decide +kernel
      have hl : raw2466step0Labels = labelEmbedding7 ∘ raw2466step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2466step0 raw2466step0Labels raw2466step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

theorem canonical2467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2467 raw2467Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw2467 raw2467Labels = mixedMoment B raw2467step0 raw2467step0Labels := by
      have ha : raw2467step0 = (fun i j => raw2467 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2467step0 raw2467; decide +kernel
      have hl : raw2467step0Labels = raw2467Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2467 raw2467Labels permutation152 permutation4
    _ = mixedMoment B node3782 node3782Labels := by rfl

theorem canonical2468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2468 raw2468Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw2468 raw2468Labels = mixedMoment B raw2468step0 raw2468step0Labels := by
      have ha : raw2468step0 = (fun i j => raw2468 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2468step0 raw2468; decide +kernel
      have hl : raw2468step0Labels = raw2468Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2468 raw2468Labels permutation156 permutation6
    mixedMoment B raw2468step0 raw2468step0Labels = mixedMoment B raw2468step1 raw2468step1Labels := by
      have ha : raw2468step1 = -raw2468step0 := by apply Matrix.ext; change ∀ i j, raw2468step1 i j = -(raw2468step0 i j); unfold raw2468step1 raw2468step0; decide +kernel
      have hl : raw2468step1Labels = raw2468step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2468step1 raw2468step1Labels = mixedMoment B raw2468step2 raw2468step2Labels := by
      have ha : raw2468step2 = raw2468step1 := by apply Matrix.ext; unfold raw2468step2 raw2468step1; decide +kernel
      have hl : raw2468step1Labels = labelEmbedding1 ∘ raw2468step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2468step1 raw2468step1Labels raw2468step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3796 node3796Labels := by rfl

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

theorem canonical2490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2490 raw2490Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw2490 raw2490Labels = mixedMoment B raw2490step0 raw2490step0Labels := by
      have ha : raw2490step0 = (fun i j => raw2490 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2490step0 raw2490; decide +kernel
      have hl : raw2490step0Labels = raw2490Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2490 raw2490Labels permutation32 permutation4
    mixedMoment B raw2490step0 raw2490step0Labels = mixedMoment B raw2490step1 raw2490step1Labels := by
      have ha : raw2490step1 = raw2490step0 := by apply Matrix.ext; unfold raw2490step1 raw2490step0; decide +kernel
      have hl : raw2490step0Labels = labelEmbedding7 ∘ raw2490step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2490step0 raw2490step0Labels raw2490step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical2491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2491 raw2491Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw2491 raw2491Labels = mixedMoment B raw2491step0 raw2491step0Labels := by
      have ha : raw2491step0 = (fun i j => raw2491 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2491step0 raw2491; decide +kernel
      have hl : raw2491step0Labels = raw2491Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2491 raw2491Labels permutation32 permutation4
    _ = mixedMoment B node3809 node3809Labels := by rfl

theorem canonical2492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2492 raw2492Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw2492 raw2492Labels = mixedMoment B raw2492step0 raw2492step0Labels := by
      have ha : raw2492step0 = (fun i j => raw2492 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2492step0 raw2492; decide +kernel
      have hl : raw2492step0Labels = raw2492Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2492 raw2492Labels permutation36 permutation6
    mixedMoment B raw2492step0 raw2492step0Labels = mixedMoment B raw2492step1 raw2492step1Labels := by
      have ha : raw2492step1 = -raw2492step0 := by apply Matrix.ext; change ∀ i j, raw2492step1 i j = -(raw2492step0 i j); unfold raw2492step1 raw2492step0; decide +kernel
      have hl : raw2492step1Labels = raw2492step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2492step1 raw2492step1Labels = mixedMoment B raw2492step2 raw2492step2Labels := by
      have ha : raw2492step2 = raw2492step1 := by apply Matrix.ext; unfold raw2492step2 raw2492step1; decide +kernel
      have hl : raw2492step1Labels = labelEmbedding1 ∘ raw2492step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2492step1 raw2492step1Labels raw2492step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

theorem canonical2493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2493 raw2493Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw2493 raw2493Labels = mixedMoment B raw2493step0 raw2493step0Labels := by
      have ha : raw2493step0 = (fun i j => raw2493 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2493step0 raw2493; decide +kernel
      have hl : raw2493step0Labels = raw2493Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2493 raw2493Labels permutation32 permutation4
    mixedMoment B raw2493step0 raw2493step0Labels = mixedMoment B raw2493step1 raw2493step1Labels := by
      have ha : raw2493step1 = raw2493step0 := by apply Matrix.ext; unfold raw2493step1 raw2493step0; decide +kernel
      have hl : raw2493step0Labels = labelEmbedding7 ∘ raw2493step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2493step0 raw2493step0Labels raw2493step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

theorem canonical2494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2494 raw2494Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw2494 raw2494Labels = mixedMoment B raw2494step0 raw2494step0Labels := by
      have ha : raw2494step0 = (fun i j => raw2494 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2494step0 raw2494; decide +kernel
      have hl : raw2494step0Labels = raw2494Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2494 raw2494Labels permutation32 permutation4
    _ = mixedMoment B node3814 node3814Labels := by rfl

theorem canonical2495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2495 raw2495Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw2495 raw2495Labels = mixedMoment B raw2495step0 raw2495step0Labels := by
      have ha : raw2495step0 = (fun i j => raw2495 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2495step0 raw2495; decide +kernel
      have hl : raw2495step0Labels = raw2495Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2495 raw2495Labels permutation37 permutation6
    mixedMoment B raw2495step0 raw2495step0Labels = mixedMoment B raw2495step1 raw2495step1Labels := by
      have ha : raw2495step1 = -raw2495step0 := by apply Matrix.ext; change ∀ i j, raw2495step1 i j = -(raw2495step0 i j); unfold raw2495step1 raw2495step0; decide +kernel
      have hl : raw2495step1Labels = raw2495step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2495step1 raw2495step1Labels = mixedMoment B raw2495step2 raw2495step2Labels := by
      have ha : raw2495step2 = raw2495step1 := by apply Matrix.ext; unfold raw2495step2 raw2495step1; decide +kernel
      have hl : raw2495step1Labels = labelEmbedding1 ∘ raw2495step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2495step1 raw2495step1Labels raw2495step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3814 node3814Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical8417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8417 raw8417Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw8417 raw8417Labels = mixedMoment B raw8417step0 raw8417step0Labels := by
      have hz : ∀ j, raw8417 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8417step0 = (fun i j => raw8417 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8417step0 raw8417; decide +kernel
      have hl : raw8417step0Labels = raw8417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8417 raw8417Labels permutation346 hz
    _ = mixedMoment B node3854 node3854Labels := by rfl

theorem canonical8422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8422 raw8422Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw8422 raw8422Labels = mixedMoment B raw8422step0 raw8422step0Labels := by
      have hz : ∀ j, raw8422 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8422step0 = (fun i j => raw8422 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8422step0 raw8422; decide +kernel
      have hl : raw8422step0Labels = raw8422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8422 raw8422Labels permutation346 hz
    mixedMoment B raw8422step0 raw8422step0Labels = mixedMoment B raw8422step1 raw8422step1Labels := by
      have hz : ∀ j, raw8422step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8422step1 = (fun i j => raw8422step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8422step1 raw8422step0; decide +kernel
      have hl : raw8422step1Labels = raw8422step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8422step0 raw8422step0Labels permutation56 hz
    mixedMoment B raw8422step1 raw8422step1Labels = mixedMoment B raw8422step2 raw8422step2Labels := by
      have ha : raw8422step2 = (fun i j => raw8422step1 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw8422step2 raw8422step1; decide +kernel
      have hl : raw8422step2Labels = raw8422step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8422step1 raw8422step1Labels permutation11 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5105 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5105 node5105Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2515 node2515Labels + mixedMoment B node3479 node3479Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2130 singletonSmall5105
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5105) = raw2130Labels := by decide +kernel
  rw [hl, canonical2130 B hB] at h
  have hc0 : mixedMoment B raw2130 (Fin.cases (0 : Fin 2) singletonSmall5105) =
      mixedMoment B node2515 node2515Labels := by
    have ha : raw2130 = raw2131 := by apply Matrix.ext; unfold raw2130 raw2131; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5105 = raw2131Labels := by decide +kernel
    rw [ha, hj, canonical2131 B hB]
  have hc1 : mixedMoment B raw2130 (Fin.cases (1 : Fin 2) singletonSmall5105) =
      mixedMoment B node3479 node3479Labels := by
    have ha : raw2130 = raw2132 := by apply Matrix.ext; unfold raw2130 raw2132; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5105 = raw2132Labels := by decide +kernel
    rw [ha, hj, canonical2132 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5370 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5370 node5370Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3706 node3706Labels + mixedMoment B node3771 node3771Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2418 singletonSmall5370
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5370) = raw2418Labels := by decide +kernel
  rw [hl, canonical2418 B hB] at h
  have hc0 : mixedMoment B raw2418 (Fin.cases (0 : Fin 2) singletonSmall5370) =
      mixedMoment B node3706 node3706Labels := by
    have ha : raw2418 = raw2419 := by apply Matrix.ext; unfold raw2418 raw2419; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5370 = raw2419Labels := by decide +kernel
    rw [ha, hj, canonical2419 B hB]
  have hc1 : mixedMoment B raw2418 (Fin.cases (1 : Fin 2) singletonSmall5370) =
      mixedMoment B node3771 node3771Labels := by
    have ha : raw2418 = raw2420 := by apply Matrix.ext; unfold raw2418 raw2420; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5370 = raw2420Labels := by decide +kernel
    rw [ha, hj, canonical2420 B hB]
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

theorem singleton5397 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5397 node5397Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3782 node3782Labels + mixedMoment B node3796 node3796Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2466 singletonSmall5397
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5397) = raw2466Labels := by decide +kernel
  rw [hl, canonical2466 B hB] at h
  have hc0 : mixedMoment B raw2466 (Fin.cases (0 : Fin 2) singletonSmall5397) =
      mixedMoment B node3782 node3782Labels := by
    have ha : raw2466 = raw2467 := by apply Matrix.ext; unfold raw2466 raw2467; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5397 = raw2467Labels := by decide +kernel
    rw [ha, hj, canonical2467 B hB]
  have hc1 : mixedMoment B raw2466 (Fin.cases (1 : Fin 2) singletonSmall5397) =
      mixedMoment B node3796 node3796Labels := by
    have ha : raw2466 = raw2468 := by apply Matrix.ext; unfold raw2466 raw2468; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5397 = raw2468Labels := by decide +kernel
    rw [ha, hj, canonical2468 B hB]
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

theorem singleton5411 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5411 node5411Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3809 node3809Labels + mixedMoment B node3813 node3813Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2490 singletonSmall5411
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5411) = raw2490Labels := by decide +kernel
  rw [hl, canonical2490 B hB] at h
  have hc0 : mixedMoment B raw2490 (Fin.cases (0 : Fin 2) singletonSmall5411) =
      mixedMoment B node3809 node3809Labels := by
    have ha : raw2490 = raw2491 := by apply Matrix.ext; unfold raw2490 raw2491; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5411 = raw2491Labels := by decide +kernel
    rw [ha, hj, canonical2491 B hB]
  have hc1 : mixedMoment B raw2490 (Fin.cases (1 : Fin 2) singletonSmall5411) =
      mixedMoment B node3813 node3813Labels := by
    have ha : raw2490 = raw2492 := by apply Matrix.ext; unfold raw2490 raw2492; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5411 = raw2492Labels := by decide +kernel
    rw [ha, hj, canonical2492 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5412 node5412Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3814 node3814Labels + mixedMoment B node3814 node3814Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2493 singletonSmall5412
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5412) = raw2493Labels := by decide +kernel
  rw [hl, canonical2493 B hB] at h
  have hc0 : mixedMoment B raw2493 (Fin.cases (0 : Fin 2) singletonSmall5412) =
      mixedMoment B node3814 node3814Labels := by
    have ha : raw2493 = raw2494 := by apply Matrix.ext; unfold raw2493 raw2494; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5412 = raw2494Labels := by decide +kernel
    rw [ha, hj, canonical2494 B hB]
  have hc1 : mixedMoment B raw2493 (Fin.cases (1 : Fin 2) singletonSmall5412) =
      mixedMoment B node3814 node3814Labels := by
    have ha : raw2493 = raw2495 := by apply Matrix.ext; unfold raw2493 raw2495; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5412 = raw2495Labels := by decide +kernel
    rw [ha, hj, canonical2495 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
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

theorem sound3814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3814 node3814Labels = Sparse.eval nodeValue3814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3814) = mixedMoment B node3814 node3814Labels := rfl
  simpa [nodeValue3814, Sparse.eval] using hc.symm

theorem sound5412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5412 node5412Labels = Sparse.eval nodeValue5412 (mixedVector B) := by
  have h := singleton5412 B _hB
  rw [sound3814 B _hB _hF] at h
  norm_num [nodeValue5412, nodeValue3814, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound2515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2515 node2515Labels = Sparse.eval nodeValue2515 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2515) = mixedMoment B node2515 node2515Labels := rfl
  simpa [nodeValue2515, Sparse.eval] using hc.symm

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

theorem sound2591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2591 node2591Labels = Sparse.eval nodeValue2591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2591) = mixedMoment B node2591 node2591Labels := rfl
  simpa [nodeValue2591, Sparse.eval] using hc.symm

theorem sound2616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2616 node2616Labels = Sparse.eval nodeValue2616 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2616) = mixedMoment B node2616 node2616Labels := rfl
  simpa [nodeValue2616, Sparse.eval] using hc.symm

theorem sound2619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2619 node2619Labels = Sparse.eval nodeValue2619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2619) = mixedMoment B node2619 node2619Labels := rfl
  simpa [nodeValue2619, Sparse.eval] using hc.symm

theorem sound2620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2620 node2620Labels = Sparse.eval nodeValue2620 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2620) = mixedMoment B node2620 node2620Labels := rfl
  simpa [nodeValue2620, Sparse.eval] using hc.symm

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

theorem sound2634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2634 node2634Labels = Sparse.eval nodeValue2634 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2634) = mixedMoment B node2634 node2634Labels := rfl
  simpa [nodeValue2634, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2870 node2870Labels = Sparse.eval nodeValue2870 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2870) = mixedMoment B node2870 node2870Labels := rfl
  simpa [nodeValue2870, Sparse.eval] using hc.symm

theorem sound2872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2872 node2872Labels = Sparse.eval nodeValue2872 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2872) = mixedMoment B node2872 node2872Labels := rfl
  simpa [nodeValue2872, Sparse.eval] using hc.symm

theorem sound2873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2873 node2873Labels = Sparse.eval nodeValue2873 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2873) = mixedMoment B node2873 node2873Labels := rfl
  simpa [nodeValue2873, Sparse.eval] using hc.symm

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

theorem sound2885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2885 node2885Labels = Sparse.eval nodeValue2885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2885) = mixedMoment B node2885 node2885Labels := rfl
  simpa [nodeValue2885, Sparse.eval] using hc.symm

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

theorem sound3045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3045 node3045Labels = Sparse.eval nodeValue3045 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3045) = mixedMoment B node3045 node3045Labels := rfl
  simpa [nodeValue3045, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3175 node3175Labels = Sparse.eval nodeValue3175 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3175) = mixedMoment B node3175 node3175Labels := rfl
  simpa [nodeValue3175, Sparse.eval] using hc.symm

theorem sound3180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3180 node3180Labels = Sparse.eval nodeValue3180 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3180) = mixedMoment B node3180 node3180Labels := rfl
  simpa [nodeValue3180, Sparse.eval] using hc.symm

theorem sound3198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3198 node3198Labels = Sparse.eval nodeValue3198 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3198) = mixedMoment B node3198 node3198Labels := rfl
  simpa [nodeValue3198, Sparse.eval] using hc.symm

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

theorem sound3479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3479 node3479Labels = Sparse.eval nodeValue3479 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3479) = mixedMoment B node3479 node3479Labels := rfl
  simpa [nodeValue3479, Sparse.eval] using hc.symm

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

theorem sound3698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3698 node3698Labels = Sparse.eval nodeValue3698 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3698) = mixedMoment B node3698 node3698Labels := rfl
  simpa [nodeValue3698, Sparse.eval] using hc.symm

theorem sound3699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3699 node3699Labels = Sparse.eval nodeValue3699 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3699) = mixedMoment B node3699 node3699Labels := rfl
  simpa [nodeValue3699, Sparse.eval] using hc.symm

theorem sound3706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3706 node3706Labels = Sparse.eval nodeValue3706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3706) = mixedMoment B node3706 node3706Labels := rfl
  simpa [nodeValue3706, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3723 node3723Labels = Sparse.eval nodeValue3723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3723) = mixedMoment B node3723 node3723Labels := rfl
  simpa [nodeValue3723, Sparse.eval] using hc.symm

theorem sound3732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3732 node3732Labels = Sparse.eval nodeValue3732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3732) = mixedMoment B node3732 node3732Labels := rfl
  simpa [nodeValue3732, Sparse.eval] using hc.symm

theorem sound3733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3733 node3733Labels = Sparse.eval nodeValue3733 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3733) = mixedMoment B node3733 node3733Labels := rfl
  simpa [nodeValue3733, Sparse.eval] using hc.symm

theorem sound3771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3771 node3771Labels = Sparse.eval nodeValue3771 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3771) = mixedMoment B node3771 node3771Labels := rfl
  simpa [nodeValue3771, Sparse.eval] using hc.symm

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

theorem sound3782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3782 node3782Labels = Sparse.eval nodeValue3782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3782) = mixedMoment B node3782 node3782Labels := rfl
  simpa [nodeValue3782, Sparse.eval] using hc.symm

theorem sound3788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3788 node3788Labels = Sparse.eval nodeValue3788 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3788) = mixedMoment B node3788 node3788Labels := rfl
  simpa [nodeValue3788, Sparse.eval] using hc.symm

theorem sound3796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3796 node3796Labels = Sparse.eval nodeValue3796 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3796) = mixedMoment B node3796 node3796Labels := rfl
  simpa [nodeValue3796, Sparse.eval] using hc.symm

theorem sound3801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3801 node3801Labels = Sparse.eval nodeValue3801 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3801) = mixedMoment B node3801 node3801Labels := rfl
  simpa [nodeValue3801, Sparse.eval] using hc.symm

theorem sound3809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3809 node3809Labels = Sparse.eval nodeValue3809 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3809) = mixedMoment B node3809 node3809Labels := rfl
  simpa [nodeValue3809, Sparse.eval] using hc.symm

theorem sound3812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3812 node3812Labels = Sparse.eval nodeValue3812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3812) = mixedMoment B node3812 node3812Labels := rfl
  simpa [nodeValue3812, Sparse.eval] using hc.symm

theorem sound3813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3813 node3813Labels = Sparse.eval nodeValue3813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3813) = mixedMoment B node3813 node3813Labels := rfl
  simpa [nodeValue3813, Sparse.eval] using hc.symm

theorem sound3819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3819 node3819Labels = Sparse.eval nodeValue3819 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3819) = mixedMoment B node3819 node3819Labels := rfl
  simpa [nodeValue3819, Sparse.eval] using hc.symm

theorem sound3828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3828 node3828Labels = Sparse.eval nodeValue3828 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3828) = mixedMoment B node3828 node3828Labels := rfl
  simpa [nodeValue3828, Sparse.eval] using hc.symm

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

theorem sound3845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3845 node3845Labels = Sparse.eval nodeValue3845 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3845) = mixedMoment B node3845 node3845Labels := rfl
  simpa [nodeValue3845, Sparse.eval] using hc.symm

theorem sound3850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3850 node3850Labels = Sparse.eval nodeValue3850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3850) = mixedMoment B node3850 node3850Labels := rfl
  simpa [nodeValue3850, Sparse.eval] using hc.symm

theorem sound3854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3854 node3854Labels = Sparse.eval nodeValue3854 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3854) = mixedMoment B node3854 node3854Labels := rfl
  simpa [nodeValue3854, Sparse.eval] using hc.symm

theorem sound3857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3857 node3857Labels = Sparse.eval nodeValue3857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3857) = mixedMoment B node3857 node3857Labels := rfl
  simpa [nodeValue3857, Sparse.eval] using hc.symm

theorem sound3874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3874 node3874Labels = Sparse.eval nodeValue3874 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3874) = mixedMoment B node3874 node3874Labels := rfl
  simpa [nodeValue3874, Sparse.eval] using hc.symm

theorem sound3877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3877 node3877Labels = Sparse.eval nodeValue3877 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3877) = mixedMoment B node3877 node3877Labels := rfl
  simpa [nodeValue3877, Sparse.eval] using hc.symm

theorem sound3884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3884 node3884Labels = Sparse.eval nodeValue3884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3884) = mixedMoment B node3884 node3884Labels := rfl
  simpa [nodeValue3884, Sparse.eval] using hc.symm

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

theorem sound3946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3946 node3946Labels = Sparse.eval nodeValue3946 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3946) = mixedMoment B node3946 node3946Labels := rfl
  simpa [nodeValue3946, Sparse.eval] using hc.symm

theorem sound3959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3959 node3959Labels = Sparse.eval nodeValue3959 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3959) = mixedMoment B node3959 node3959Labels := rfl
  simpa [nodeValue3959, Sparse.eval] using hc.symm

theorem sound3961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3961 node3961Labels = Sparse.eval nodeValue3961 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3961) = mixedMoment B node3961 node3961Labels := rfl
  simpa [nodeValue3961, Sparse.eval] using hc.symm

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

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

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

theorem sound4816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4816 node4816Labels = Sparse.eval nodeValue4816 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4816) = mixedMoment B node4816 node4816Labels := rfl
  simpa [nodeValue4816, Sparse.eval] using hc.symm

theorem sound4817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4817 node4817Labels = Sparse.eval nodeValue4817 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4817) = mixedMoment B node4817 node4817Labels := rfl
  simpa [nodeValue4817, Sparse.eval] using hc.symm

theorem sound4821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4821 node4821Labels = Sparse.eval nodeValue4821 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4821) = mixedMoment B node4821 node4821Labels := rfl
  simpa [nodeValue4821, Sparse.eval] using hc.symm

theorem sound4836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4836 node4836Labels = Sparse.eval nodeValue4836 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4836) = mixedMoment B node4836 node4836Labels := rfl
  simpa [nodeValue4836, Sparse.eval] using hc.symm

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

theorem sound4891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4891 node4891Labels = Sparse.eval nodeValue4891 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4891) = mixedMoment B node4891 node4891Labels := rfl
  simpa [nodeValue4891, Sparse.eval] using hc.symm

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

theorem sound5086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5086 node5086Labels = Sparse.eval nodeValue5086 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5086) = mixedMoment B node5086 node5086Labels := rfl
  simpa [nodeValue5086, Sparse.eval] using hc.symm

theorem sound5090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5090 node5090Labels = Sparse.eval nodeValue5090 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5090) = mixedMoment B node5090 node5090Labels := rfl
  simpa [nodeValue5090, Sparse.eval] using hc.symm

theorem sound5105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5105 node5105Labels = Sparse.eval nodeValue5105 (mixedVector B) := by
  have h := singleton5105 B _hB
  rw [sound2515 B _hB _hF, sound3479 B _hB _hF] at h
  norm_num [nodeValue5105, nodeValue2515, nodeValue3479, Sparse.eval] at h ⊢
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

theorem sound5254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5254 node5254Labels = Sparse.eval nodeValue5254 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5254) = mixedMoment B node5254 node5254Labels := rfl
  simpa [nodeValue5254, Sparse.eval] using hc.symm

theorem sound5260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5260 node5260Labels = Sparse.eval nodeValue5260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5260) = mixedMoment B node5260 node5260Labels := rfl
  simpa [nodeValue5260, Sparse.eval] using hc.symm

theorem sound5267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5267 node5267Labels = Sparse.eval nodeValue5267 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5267) = mixedMoment B node5267 node5267Labels := rfl
  simpa [nodeValue5267, Sparse.eval] using hc.symm

theorem sound5287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5287 node5287Labels = Sparse.eval nodeValue5287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5287) = mixedMoment B node5287 node5287Labels := rfl
  simpa [nodeValue5287, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5360 node5360Labels = Sparse.eval nodeValue5360 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5360) = mixedMoment B node5360 node5360Labels := rfl
  simpa [nodeValue5360, Sparse.eval] using hc.symm

theorem sound5361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5361 node5361Labels = Sparse.eval nodeValue5361 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5361) = mixedMoment B node5361 node5361Labels := rfl
  simpa [nodeValue5361, Sparse.eval] using hc.symm

theorem sound5370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5370 node5370Labels = Sparse.eval nodeValue5370 (mixedVector B) := by
  have h := singleton5370 B _hB
  rw [sound3706 B _hB _hF, sound3771 B _hB _hF] at h
  norm_num [nodeValue5370, nodeValue3706, nodeValue3771, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5410 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5410 node5410Labels = 0 := by
  exact mixedMoment_order_one B hB node5410 node5410Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5397 node5397Labels = Sparse.eval nodeValue5397 (mixedVector B) := by
  have h := singleton5397 B _hB
  rw [sound3782 B _hB _hF, sound3796 B _hB _hF] at h
  norm_num [nodeValue5397, nodeValue3782, nodeValue3796, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5406 node5406Labels = Sparse.eval nodeValue5406 (mixedVector B) := by
  have h := singleton5406 B _hB
  rw [sound3801 B _hB _hF, sound3812 B _hB _hF] at h
  norm_num [nodeValue5406, nodeValue3801, nodeValue3812, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5407 node5407Labels = Sparse.eval nodeValue5407 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5407) = mixedMoment B node5407 node5407Labels := rfl
  simpa [nodeValue5407, Sparse.eval] using hc.symm

theorem sound5410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5410 node5410Labels = Sparse.eval nodeValue5410 (mixedVector B) := by
  simpa only [nodeValue5410, Sparse.eval_nil] using zero5410 B _hB _hF

theorem sound5411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5411 node5411Labels = Sparse.eval nodeValue5411 (mixedVector B) := by
  have h := singleton5411 B _hB
  rw [sound3809 B _hB _hF, sound3813 B _hB _hF] at h
  norm_num [nodeValue5411, nodeValue3809, nodeValue3813, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5425 node5425Labels = Sparse.eval nodeValue5425 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5425) = mixedMoment B node5425 node5425Labels := rfl
  simpa [nodeValue5425, Sparse.eval] using hc.symm

theorem sound5426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5426 node5426Labels = Sparse.eval nodeValue5426 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5426) = mixedMoment B node5426 node5426Labels := rfl
  simpa [nodeValue5426, Sparse.eval] using hc.symm

theorem sound5436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5436 node5436Labels = Sparse.eval nodeValue5436 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5436) = mixedMoment B node5436 node5436Labels := rfl
  simpa [nodeValue5436, Sparse.eval] using hc.symm

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

theorem sourceEq920 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm920 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA920 + difference 0 0) (sourceB920 + difference 0 0) sourceC920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA920 + difference 0 0) (sourceB920 + difference 0 0) sourceC920) = raw8417 := by
      apply Matrix.ext; unfold tripleCharges sourceA920 sourceB920 sourceC920 difference raw8417; decide +kernel
    rw [ha]
    exact (canonical8417 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA920 + difference 0 1) (sourceB920 + difference 1 0) sourceC920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3733) := by
    have ha : (tripleCharges (sourceA920 + difference 0 1) (sourceB920 + difference 1 0) sourceC920) = raw15255 := by
      apply Matrix.ext; unfold tripleCharges sourceA920 sourceB920 sourceC920 difference raw15255; decide +kernel
    rw [ha]
    exact (canonical15255 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA920 + difference 0 2) (sourceB920 + difference 2 0) sourceC920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3819) := by
    have ha : (tripleCharges (sourceA920 + difference 0 2) (sourceB920 + difference 2 0) sourceC920) = raw15256 := by
      apply Matrix.ext; unfold tripleCharges sourceA920 sourceB920 sourceC920 difference raw15256; decide +kernel
    rw [ha]
    exact (canonical15256 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA920 + difference 0 3) (sourceB920 + difference 3 0) sourceC920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2591) := by
    have ha : (tripleCharges (sourceA920 + difference 0 3) (sourceB920 + difference 3 0) sourceC920) = raw15257 := by
      apply Matrix.ext; unfold tripleCharges sourceA920 sourceB920 sourceC920 difference raw15257; decide +kernel
    rw [ha]
    exact (canonical15257 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA920 + difference 0 4) (sourceB920 + difference 4 0) sourceC920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA920 + difference 0 4) (sourceB920 + difference 4 0) sourceC920) = raw15258 := by
      apply Matrix.ext; unfold tripleCharges sourceA920 sourceB920 sourceC920 difference raw15258; decide +kernel
    rw [ha]
    exact (canonical15258 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA920 + difference 0 5) (sourceB920 + difference 5 0) sourceC920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA920 + difference 0 5) (sourceB920 + difference 5 0) sourceC920) = raw15259 := by
      apply Matrix.ext; unfold tripleCharges sourceA920 sourceB920 sourceC920 difference raw15259; decide +kernel
    rw [ha]
    exact (canonical15259 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA920 + sourceB920) sourceC920) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA920 + sourceB920) sourceC920) = raw8422 := by
      apply Matrix.ext; unfold doubleCharges sourceA920 sourceB920 sourceC920 raw8422; decide +kernel
    rw [ha]
    exact (canonical8422 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA920 sourceB920 sourceC920
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm920, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq925 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm925 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA925 + difference 0 0) (sourceB925 + difference 0 0) sourceC925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA925 + difference 0 0) (sourceB925 + difference 0 0) sourceC925) = raw15354 := by
      apply Matrix.ext; unfold tripleCharges sourceA925 sourceB925 sourceC925 difference raw15354; decide +kernel
    rw [ha]
    exact (canonical15354 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA925 + difference 1 0) (sourceB925 + difference 0 1) sourceC925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA925 + difference 1 0) (sourceB925 + difference 0 1) sourceC925) = raw15355 := by
      apply Matrix.ext; unfold tripleCharges sourceA925 sourceB925 sourceC925 difference raw15355; decide +kernel
    rw [ha]
    exact (canonical15355 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA925 + difference 2 0) (sourceB925 + difference 0 2) sourceC925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3175) := by
    have ha : (tripleCharges (sourceA925 + difference 2 0) (sourceB925 + difference 0 2) sourceC925) = raw15356 := by
      apply Matrix.ext; unfold tripleCharges sourceA925 sourceB925 sourceC925 difference raw15356; decide +kernel
    rw [ha]
    exact (canonical15356 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA925 + difference 3 0) (sourceB925 + difference 0 3) sourceC925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2619) := by
    have ha : (tripleCharges (sourceA925 + difference 3 0) (sourceB925 + difference 0 3) sourceC925) = raw15357 := by
      apply Matrix.ext; unfold tripleCharges sourceA925 sourceB925 sourceC925 difference raw15357; decide +kernel
    rw [ha]
    exact (canonical15357 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA925 + difference 4 0) (sourceB925 + difference 0 4) sourceC925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3198) := by
    have ha : (tripleCharges (sourceA925 + difference 4 0) (sourceB925 + difference 0 4) sourceC925) = raw15358 := by
      apply Matrix.ext; unfold tripleCharges sourceA925 sourceB925 sourceC925 difference raw15358; decide +kernel
    rw [ha]
    exact (canonical15358 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA925 + difference 5 0) (sourceB925 + difference 0 5) sourceC925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2872) := by
    have ha : (tripleCharges (sourceA925 + difference 5 0) (sourceB925 + difference 0 5) sourceC925) = raw15359 := by
      apply Matrix.ext; unfold tripleCharges sourceA925 sourceB925 sourceC925 difference raw15359; decide +kernel
    rw [ha]
    exact (canonical15359 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA925 + sourceB925) sourceC925) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA925 + sourceB925) sourceC925) = raw15360 := by
      apply Matrix.ext; unfold doubleCharges sourceA925 sourceB925 sourceC925 raw15360; decide +kernel
    rw [ha]
    exact (canonical15360 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA925 sourceB925 sourceC925
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm925, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq926 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm926 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA926 + difference 1 0) (sourceB926 + difference 0 1) sourceC926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA926 + difference 1 0) (sourceB926 + difference 0 1) sourceC926) = raw15355 := by
      apply Matrix.ext; unfold tripleCharges sourceA926 sourceB926 sourceC926 difference raw15355; decide +kernel
    rw [ha]
    exact (canonical15355 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA926 + difference 1 1) (sourceB926 + difference 1 1) sourceC926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA926 + difference 1 1) (sourceB926 + difference 1 1) sourceC926) = raw15354 := by
      apply Matrix.ext; unfold tripleCharges sourceA926 sourceB926 sourceC926 difference raw15354; decide +kernel
    rw [ha]
    exact (canonical15354 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA926 + difference 1 2) (sourceB926 + difference 2 1) sourceC926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3788) := by
    have ha : (tripleCharges (sourceA926 + difference 1 2) (sourceB926 + difference 2 1) sourceC926) = raw15361 := by
      apply Matrix.ext; unfold tripleCharges sourceA926 sourceB926 sourceC926 difference raw15361; decide +kernel
    rw [ha]
    exact (canonical15361 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA926 + difference 1 3) (sourceB926 + difference 3 1) sourceC926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA926 + difference 1 3) (sourceB926 + difference 3 1) sourceC926) = raw15362 := by
      apply Matrix.ext; unfold tripleCharges sourceA926 sourceB926 sourceC926 difference raw15362; decide +kernel
    rw [ha]
    exact (canonical15362 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA926 + difference 1 4) (sourceB926 + difference 4 1) sourceC926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA926 + difference 1 4) (sourceB926 + difference 4 1) sourceC926) = raw15363 := by
      apply Matrix.ext; unfold tripleCharges sourceA926 sourceB926 sourceC926 difference raw15363; decide +kernel
    rw [ha]
    exact (canonical15363 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA926 + difference 1 5) (sourceB926 + difference 5 1) sourceC926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA926 + difference 1 5) (sourceB926 + difference 5 1) sourceC926) = raw15364 := by
      apply Matrix.ext; unfold tripleCharges sourceA926 sourceB926 sourceC926 difference raw15364; decide +kernel
    rw [ha]
    exact (canonical15364 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA926 + sourceB926) sourceC926) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA926 + sourceB926) sourceC926) = raw15360 := by
      apply Matrix.ext; unfold doubleCharges sourceA926 sourceB926 sourceC926 raw15360; decide +kernel
    rw [ha]
    exact (canonical15360 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA926 sourceB926 sourceC926
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm926, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq927 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm927 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA927 + difference 0 1) (sourceB927 + difference 1 0) sourceC927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA927 + difference 0 1) (sourceB927 + difference 1 0) sourceC927) = raw15365 := by
      apply Matrix.ext; unfold tripleCharges sourceA927 sourceB927 sourceC927 difference raw15365; decide +kernel
    rw [ha]
    exact (canonical15365 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA927 + difference 1 1) (sourceB927 + difference 1 1) sourceC927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA927 + difference 1 1) (sourceB927 + difference 1 1) sourceC927) = raw15354 := by
      apply Matrix.ext; unfold tripleCharges sourceA927 sourceB927 sourceC927 difference raw15354; decide +kernel
    rw [ha]
    exact (canonical15354 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA927 + difference 2 1) (sourceB927 + difference 1 2) sourceC927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3828) := by
    have ha : (tripleCharges (sourceA927 + difference 2 1) (sourceB927 + difference 1 2) sourceC927) = raw15366 := by
      apply Matrix.ext; unfold tripleCharges sourceA927 sourceB927 sourceC927 difference raw15366; decide +kernel
    rw [ha]
    exact (canonical15366 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA927 + difference 3 1) (sourceB927 + difference 1 3) sourceC927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2634) := by
    have ha : (tripleCharges (sourceA927 + difference 3 1) (sourceB927 + difference 1 3) sourceC927) = raw15367 := by
      apply Matrix.ext; unfold tripleCharges sourceA927 sourceB927 sourceC927 difference raw15367; decide +kernel
    rw [ha]
    exact (canonical15367 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA927 + difference 4 1) (sourceB927 + difference 1 4) sourceC927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3699) := by
    have ha : (tripleCharges (sourceA927 + difference 4 1) (sourceB927 + difference 1 4) sourceC927) = raw15368 := by
      apply Matrix.ext; unfold tripleCharges sourceA927 sourceB927 sourceC927 difference raw15368; decide +kernel
    rw [ha]
    exact (canonical15368 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA927 + difference 5 1) (sourceB927 + difference 1 5) sourceC927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2873) := by
    have ha : (tripleCharges (sourceA927 + difference 5 1) (sourceB927 + difference 1 5) sourceC927) = raw15369 := by
      apply Matrix.ext; unfold tripleCharges sourceA927 sourceB927 sourceC927 difference raw15369; decide +kernel
    rw [ha]
    exact (canonical15369 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA927 + sourceB927) sourceC927) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA927 + sourceB927) sourceC927) = raw15360 := by
      apply Matrix.ext; unfold doubleCharges sourceA927 sourceB927 sourceC927 raw15360; decide +kernel
    rw [ha]
    exact (canonical15360 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA927 sourceB927 sourceC927
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm927, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources29
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq928 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm928 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA928 + difference 0 2) (sourceB928 + difference 2 0) sourceC928) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA928 + difference 0 2) (sourceB928 + difference 2 0) sourceC928) = raw15370 := by
      apply Matrix.ext; unfold tripleCharges sourceA928 sourceB928 sourceC928 difference raw15370; decide +kernel
    rw [ha]
    exact (canonical15370 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA928 + difference 1 2) (sourceB928 + difference 2 1) sourceC928) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3788) := by
    have ha : (tripleCharges (sourceA928 + difference 1 2) (sourceB928 + difference 2 1) sourceC928) = raw15361 := by
      apply Matrix.ext; unfold tripleCharges sourceA928 sourceB928 sourceC928 difference raw15361; decide +kernel
    rw [ha]
    exact (canonical15361 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA928 + difference 2 2) (sourceB928 + difference 2 2) sourceC928) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA928 + difference 2 2) (sourceB928 + difference 2 2) sourceC928) = raw15354 := by
      apply Matrix.ext; unfold tripleCharges sourceA928 sourceB928 sourceC928 difference raw15354; decide +kernel
    rw [ha]
    exact (canonical15354 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA928 + difference 3 2) (sourceB928 + difference 2 3) sourceC928) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2616) := by
    have ha : (tripleCharges (sourceA928 + difference 3 2) (sourceB928 + difference 2 3) sourceC928) = raw15371 := by
      apply Matrix.ext; unfold tripleCharges sourceA928 sourceB928 sourceC928 difference raw15371; decide +kernel
    rw [ha]
    exact (canonical15371 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA928 + difference 4 2) (sourceB928 + difference 2 4) sourceC928) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3698) := by
    have ha : (tripleCharges (sourceA928 + difference 4 2) (sourceB928 + difference 2 4) sourceC928) = raw15372 := by
      apply Matrix.ext; unfold tripleCharges sourceA928 sourceB928 sourceC928 difference raw15372; decide +kernel
    rw [ha]
    exact (canonical15372 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA928 + difference 5 2) (sourceB928 + difference 2 5) sourceC928) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2870) := by
    have ha : (tripleCharges (sourceA928 + difference 5 2) (sourceB928 + difference 2 5) sourceC928) = raw15373 := by
      apply Matrix.ext; unfold tripleCharges sourceA928 sourceB928 sourceC928 difference raw15373; decide +kernel
    rw [ha]
    exact (canonical15373 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA928 + sourceB928) sourceC928) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA928 + sourceB928) sourceC928) = raw15360 := by
      apply Matrix.ext; unfold doubleCharges sourceA928 sourceB928 sourceC928 raw15360; decide +kernel
    rw [ha]
    exact (canonical15360 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA928 sourceB928 sourceC928
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm928, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq929 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm929 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA929 + difference 0 3) (sourceB929 + difference 3 0) sourceC929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA929 + difference 0 3) (sourceB929 + difference 3 0) sourceC929) = raw15374 := by
      apply Matrix.ext; unfold tripleCharges sourceA929 sourceB929 sourceC929 difference raw15374; decide +kernel
    rw [ha]
    exact (canonical15374 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA929 + difference 1 3) (sourceB929 + difference 3 1) sourceC929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA929 + difference 1 3) (sourceB929 + difference 3 1) sourceC929) = raw15362 := by
      apply Matrix.ext; unfold tripleCharges sourceA929 sourceB929 sourceC929 difference raw15362; decide +kernel
    rw [ha]
    exact (canonical15362 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA929 + difference 2 3) (sourceB929 + difference 3 2) sourceC929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3946) := by
    have ha : (tripleCharges (sourceA929 + difference 2 3) (sourceB929 + difference 3 2) sourceC929) = raw15375 := by
      apply Matrix.ext; unfold tripleCharges sourceA929 sourceB929 sourceC929 difference raw15375; decide +kernel
    rw [ha]
    exact (canonical15375 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA929 + difference 3 3) (sourceB929 + difference 3 3) sourceC929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA929 + difference 3 3) (sourceB929 + difference 3 3) sourceC929) = raw15354 := by
      apply Matrix.ext; unfold tripleCharges sourceA929 sourceB929 sourceC929 difference raw15354; decide +kernel
    rw [ha]
    exact (canonical15354 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA929 + difference 4 3) (sourceB929 + difference 3 4) sourceC929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA929 + difference 4 3) (sourceB929 + difference 3 4) sourceC929) = raw15376 := by
      apply Matrix.ext; unfold tripleCharges sourceA929 sourceB929 sourceC929 difference raw15376; decide +kernel
    rw [ha]
    exact (canonical15376 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA929 + difference 5 3) (sourceB929 + difference 3 5) sourceC929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2885) := by
    have ha : (tripleCharges (sourceA929 + difference 5 3) (sourceB929 + difference 3 5) sourceC929) = raw15377 := by
      apply Matrix.ext; unfold tripleCharges sourceA929 sourceB929 sourceC929 difference raw15377; decide +kernel
    rw [ha]
    exact (canonical15377 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA929 + sourceB929) sourceC929) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA929 + sourceB929) sourceC929) = raw15360 := by
      apply Matrix.ext; unfold doubleCharges sourceA929 sourceB929 sourceC929 raw15360; decide +kernel
    rw [ha]
    exact (canonical15360 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA929 sourceB929 sourceC929
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm929, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq930 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm930 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA930 + difference 4 0) (sourceB930 + difference 0 4) sourceC930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3198) := by
    have ha : (tripleCharges (sourceA930 + difference 4 0) (sourceB930 + difference 0 4) sourceC930) = raw15358 := by
      apply Matrix.ext; unfold tripleCharges sourceA930 sourceB930 sourceC930 difference raw15358; decide +kernel
    rw [ha]
    exact (canonical15358 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA930 + difference 4 1) (sourceB930 + difference 1 4) sourceC930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3699) := by
    have ha : (tripleCharges (sourceA930 + difference 4 1) (sourceB930 + difference 1 4) sourceC930) = raw15368 := by
      apply Matrix.ext; unfold tripleCharges sourceA930 sourceB930 sourceC930 difference raw15368; decide +kernel
    rw [ha]
    exact (canonical15368 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA930 + difference 4 2) (sourceB930 + difference 2 4) sourceC930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3698) := by
    have ha : (tripleCharges (sourceA930 + difference 4 2) (sourceB930 + difference 2 4) sourceC930) = raw15372 := by
      apply Matrix.ext; unfold tripleCharges sourceA930 sourceB930 sourceC930 difference raw15372; decide +kernel
    rw [ha]
    exact (canonical15372 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA930 + difference 4 3) (sourceB930 + difference 3 4) sourceC930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA930 + difference 4 3) (sourceB930 + difference 3 4) sourceC930) = raw15376 := by
      apply Matrix.ext; unfold tripleCharges sourceA930 sourceB930 sourceC930 difference raw15376; decide +kernel
    rw [ha]
    exact (canonical15376 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA930 + difference 4 4) (sourceB930 + difference 4 4) sourceC930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA930 + difference 4 4) (sourceB930 + difference 4 4) sourceC930) = raw15354 := by
      apply Matrix.ext; unfold tripleCharges sourceA930 sourceB930 sourceC930 difference raw15354; decide +kernel
    rw [ha]
    exact (canonical15354 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA930 + difference 4 5) (sourceB930 + difference 5 4) sourceC930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA930 + difference 4 5) (sourceB930 + difference 5 4) sourceC930) = raw15378 := by
      apply Matrix.ext; unfold tripleCharges sourceA930 sourceB930 sourceC930 difference raw15378; decide +kernel
    rw [ha]
    exact (canonical15378 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA930 + sourceB930) sourceC930) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA930 + sourceB930) sourceC930) = raw15360 := by
      apply Matrix.ext; unfold doubleCharges sourceA930 sourceB930 sourceC930 raw15360; decide +kernel
    rw [ha]
    exact (canonical15360 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA930 sourceB930 sourceC930
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm930, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq931 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm931 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA931 + difference 0 4) (sourceB931 + difference 4 0) sourceC931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA931 + difference 0 4) (sourceB931 + difference 4 0) sourceC931) = raw15379 := by
      apply Matrix.ext; unfold tripleCharges sourceA931 sourceB931 sourceC931 difference raw15379; decide +kernel
    rw [ha]
    exact (canonical15379 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA931 + difference 1 4) (sourceB931 + difference 4 1) sourceC931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA931 + difference 1 4) (sourceB931 + difference 4 1) sourceC931) = raw15363 := by
      apply Matrix.ext; unfold tripleCharges sourceA931 sourceB931 sourceC931 difference raw15363; decide +kernel
    rw [ha]
    exact (canonical15363 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA931 + difference 2 4) (sourceB931 + difference 4 2) sourceC931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3723) := by
    have ha : (tripleCharges (sourceA931 + difference 2 4) (sourceB931 + difference 4 2) sourceC931) = raw15380 := by
      apply Matrix.ext; unfold tripleCharges sourceA931 sourceB931 sourceC931 difference raw15380; decide +kernel
    rw [ha]
    exact (canonical15380 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA931 + difference 3 4) (sourceB931 + difference 4 3) sourceC931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2620) := by
    have ha : (tripleCharges (sourceA931 + difference 3 4) (sourceB931 + difference 4 3) sourceC931) = raw15381 := by
      apply Matrix.ext; unfold tripleCharges sourceA931 sourceB931 sourceC931 difference raw15381; decide +kernel
    rw [ha]
    exact (canonical15381 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA931 + difference 4 4) (sourceB931 + difference 4 4) sourceC931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA931 + difference 4 4) (sourceB931 + difference 4 4) sourceC931) = raw15354 := by
      apply Matrix.ext; unfold tripleCharges sourceA931 sourceB931 sourceC931 difference raw15354; decide +kernel
    rw [ha]
    exact (canonical15354 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA931 + difference 5 4) (sourceB931 + difference 4 5) sourceC931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3045) := by
    have ha : (tripleCharges (sourceA931 + difference 5 4) (sourceB931 + difference 4 5) sourceC931) = raw15382 := by
      apply Matrix.ext; unfold tripleCharges sourceA931 sourceB931 sourceC931 difference raw15382; decide +kernel
    rw [ha]
    exact (canonical15382 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA931 + sourceB931) sourceC931) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA931 + sourceB931) sourceC931) = raw15360 := by
      apply Matrix.ext; unfold doubleCharges sourceA931 sourceB931 sourceC931 raw15360; decide +kernel
    rw [ha]
    exact (canonical15360 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA931 sourceB931 sourceC931
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm931, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq933 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm933 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA933 + difference 0 1) (sourceB933 + difference 1 0) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA933 + difference 0 1) (sourceB933 + difference 1 0) sourceC933) = raw15405 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15405; decide +kernel
    rw [ha]
    exact (canonical15405 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA933 + difference 0 2) (sourceB933 + difference 2 0) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA933 + difference 0 2) (sourceB933 + difference 2 0) sourceC933) = raw15406 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15406; decide +kernel
    rw [ha]
    exact (canonical15406 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA933 + difference 0 3) (sourceB933 + difference 3 0) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA933 + difference 0 3) (sourceB933 + difference 3 0) sourceC933) = raw15407 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15407; decide +kernel
    rw [ha]
    exact (canonical15407 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA933 + difference 0 4) (sourceB933 + difference 4 0) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA933 + difference 0 4) (sourceB933 + difference 4 0) sourceC933) = raw15408 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15408; decide +kernel
    rw [ha]
    exact (canonical15408 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA933 + difference 0 5) (sourceB933 + difference 5 0) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA933 + difference 0 5) (sourceB933 + difference 5 0) sourceC933) = raw15409 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15409; decide +kernel
    rw [ha]
    exact (canonical15409 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA933 + difference 1 0) (sourceB933 + difference 0 1) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA933 + difference 1 0) (sourceB933 + difference 0 1) sourceC933) = raw15410 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15410; decide +kernel
    rw [ha]
    exact (canonical15410 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA933 + difference 1 2) (sourceB933 + difference 2 1) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5407) := by
    have ha : (tripleCharges (sourceA933 + difference 1 2) (sourceB933 + difference 2 1) sourceC933) = raw15411 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15411; decide +kernel
    rw [ha]
    exact (canonical15411 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA933 + difference 1 3) (sourceB933 + difference 3 1) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA933 + difference 1 3) (sourceB933 + difference 3 1) sourceC933) = raw15412 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15412; decide +kernel
    rw [ha]
    exact (canonical15412 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA933 + difference 1 4) (sourceB933 + difference 4 1) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA933 + difference 1 4) (sourceB933 + difference 4 1) sourceC933) = raw15413 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15413; decide +kernel
    rw [ha]
    exact (canonical15413 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA933 + difference 1 5) (sourceB933 + difference 5 1) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA933 + difference 1 5) (sourceB933 + difference 5 1) sourceC933) = raw15414 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15414; decide +kernel
    rw [ha]
    exact (canonical15414 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA933 + difference 2 0) (sourceB933 + difference 0 2) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA933 + difference 2 0) (sourceB933 + difference 0 2) sourceC933) = raw15415 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15415; decide +kernel
    rw [ha]
    exact (canonical15415 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA933 + difference 2 1) (sourceB933 + difference 1 2) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA933 + difference 2 1) (sourceB933 + difference 1 2) sourceC933) = raw15416 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15416; decide +kernel
    rw [ha]
    exact (canonical15416 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA933 + difference 2 3) (sourceB933 + difference 3 2) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA933 + difference 2 3) (sourceB933 + difference 3 2) sourceC933) = raw15417 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15417; decide +kernel
    rw [ha]
    exact (canonical15417 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA933 + difference 2 4) (sourceB933 + difference 4 2) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5426) := by
    have ha : (tripleCharges (sourceA933 + difference 2 4) (sourceB933 + difference 4 2) sourceC933) = raw15418 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15418; decide +kernel
    rw [ha]
    exact (canonical15418 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA933 + difference 2 5) (sourceB933 + difference 5 2) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA933 + difference 2 5) (sourceB933 + difference 5 2) sourceC933) = raw15419 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15419; decide +kernel
    rw [ha]
    exact (canonical15419 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA933 + difference 3 0) (sourceB933 + difference 0 3) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA933 + difference 3 0) (sourceB933 + difference 0 3) sourceC933) = raw15420 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15420; decide +kernel
    rw [ha]
    exact (canonical15420 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA933 + difference 3 1) (sourceB933 + difference 1 3) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA933 + difference 3 1) (sourceB933 + difference 1 3) sourceC933) = raw15421 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15421; decide +kernel
    rw [ha]
    exact (canonical15421 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA933 + difference 3 2) (sourceB933 + difference 2 3) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA933 + difference 3 2) (sourceB933 + difference 2 3) sourceC933) = raw15422 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15422; decide +kernel
    rw [ha]
    exact (canonical15422 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA933 + difference 3 4) (sourceB933 + difference 4 3) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA933 + difference 3 4) (sourceB933 + difference 4 3) sourceC933) = raw15423 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15423; decide +kernel
    rw [ha]
    exact (canonical15423 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA933 + difference 3 5) (sourceB933 + difference 5 3) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA933 + difference 3 5) (sourceB933 + difference 5 3) sourceC933) = raw15424 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15424; decide +kernel
    rw [ha]
    exact (canonical15424 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA933 + difference 4 0) (sourceB933 + difference 0 4) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4821) := by
    have ha : (tripleCharges (sourceA933 + difference 4 0) (sourceB933 + difference 0 4) sourceC933) = raw15425 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15425; decide +kernel
    rw [ha]
    exact (canonical15425 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA933 + difference 4 1) (sourceB933 + difference 1 4) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5361) := by
    have ha : (tripleCharges (sourceA933 + difference 4 1) (sourceB933 + difference 1 4) sourceC933) = raw15426 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15426; decide +kernel
    rw [ha]
    exact (canonical15426 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA933 + difference 4 2) (sourceB933 + difference 2 4) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA933 + difference 4 2) (sourceB933 + difference 2 4) sourceC933) = raw15427 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15427; decide +kernel
    rw [ha]
    exact (canonical15427 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA933 + difference 4 3) (sourceB933 + difference 3 4) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA933 + difference 4 3) (sourceB933 + difference 3 4) sourceC933) = raw15428 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15428; decide +kernel
    rw [ha]
    exact (canonical15428 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA933 + difference 4 5) (sourceB933 + difference 5 4) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA933 + difference 4 5) (sourceB933 + difference 5 4) sourceC933) = raw15429 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15429; decide +kernel
    rw [ha]
    exact (canonical15429 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA933 + difference 5 0) (sourceB933 + difference 0 5) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA933 + difference 5 0) (sourceB933 + difference 0 5) sourceC933) = raw15430 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15430; decide +kernel
    rw [ha]
    exact (canonical15430 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA933 + difference 5 1) (sourceB933 + difference 1 5) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5090) := by
    have ha : (tripleCharges (sourceA933 + difference 5 1) (sourceB933 + difference 1 5) sourceC933) = raw15431 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15431; decide +kernel
    rw [ha]
    exact (canonical15431 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA933 + difference 5 2) (sourceB933 + difference 2 5) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA933 + difference 5 2) (sourceB933 + difference 2 5) sourceC933) = raw15432 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15432; decide +kernel
    rw [ha]
    exact (canonical15432 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA933 + difference 5 3) (sourceB933 + difference 3 5) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA933 + difference 5 3) (sourceB933 + difference 3 5) sourceC933) = raw15433 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15433; decide +kernel
    rw [ha]
    exact (canonical15433 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA933 + difference 5 4) (sourceB933 + difference 4 5) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA933 + difference 5 4) (sourceB933 + difference 4 5) sourceC933) = raw15434 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15434; decide +kernel
    rw [ha]
    exact (canonical15434 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA933 sourceB933 sourceC933
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm933, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck803 : Integer.Sparse.reindex keyMap MixedData.row803 = numericRow803 := by decide +kernel

theorem numericCheck803 (x : Master → ℝ) : Integer.Sparse.eval numericRow803 x =
    (1 : ℝ) * reducedSource803 x := by
  norm_num [numericRow803, reducedSource803, Integer.Sparse.eval, Sparse.eval, nodeValue2591, nodeValue3733, nodeValue3819, nodeValue3845, nodeValue3854, nodeValue3857, nodeValue4092]

theorem reindexCheck806 : Integer.Sparse.reindex keyMap MixedData.row806 = numericRow806 := by decide +kernel

theorem numericCheck806 (x : Master → ℝ) : Integer.Sparse.eval numericRow806 x =
    (1 : ℝ) * reducedSource806 x := by
  norm_num [numericRow806, reducedSource806, Integer.Sparse.eval, Sparse.eval, nodeValue2619, nodeValue2872, nodeValue3175, nodeValue3180, nodeValue3198, nodeValue3877, nodeValue4092]

theorem reindexCheck807 : Integer.Sparse.reindex keyMap MixedData.row807 = numericRow807 := by decide +kernel

theorem numericCheck807 (x : Master → ℝ) : Integer.Sparse.eval numericRow807 x =
    (1 : ℝ) * reducedSource807 x := by
  norm_num [numericRow807, reducedSource807, Integer.Sparse.eval, Sparse.eval, nodeValue3180, nodeValue3732, nodeValue3788, nodeValue3809, nodeValue3877, nodeValue3959, nodeValue4092]

theorem reindexCheck808 : Integer.Sparse.reindex keyMap MixedData.row808 = numericRow808 := by decide +kernel

theorem numericCheck808 (x : Master → ℝ) : Integer.Sparse.eval numericRow808 x =
    (1 : ℝ) * reducedSource808 x := by
  norm_num [numericRow808, reducedSource808, Integer.Sparse.eval, Sparse.eval, nodeValue2634, nodeValue2873, nodeValue3699, nodeValue3828, nodeValue3877, nodeValue3884, nodeValue4092]

theorem reindexCheck809 : Integer.Sparse.reindex keyMap MixedData.row809 = numericRow809 := by decide +kernel

theorem numericCheck809 (x : Master → ℝ) : Integer.Sparse.eval numericRow809 x =
    (1 : ℝ) * reducedSource809 x := by
  norm_num [numericRow809, reducedSource809, Integer.Sparse.eval, Sparse.eval, nodeValue2616, nodeValue2870, nodeValue3698, nodeValue3788, nodeValue3874, nodeValue3877, nodeValue4092]

theorem reindexCheck810 : Integer.Sparse.reindex keyMap MixedData.row810 = numericRow810 := by decide +kernel

theorem numericCheck810 (x : Master → ℝ) : Integer.Sparse.eval numericRow810 x =
    (1 : ℝ) * reducedSource810 x := by
  norm_num [numericRow810, reducedSource810, Integer.Sparse.eval, Sparse.eval, nodeValue2885, nodeValue3706, nodeValue3877, nodeValue3946, nodeValue3959, nodeValue3961, nodeValue4092]

theorem reindexCheck811 : Integer.Sparse.reindex keyMap MixedData.row811 = numericRow811 := by decide +kernel

theorem numericCheck811 (x : Master → ℝ) : Integer.Sparse.eval numericRow811 x =
    (1 : ℝ) * reducedSource811 x := by
  norm_num [numericRow811, reducedSource811, Integer.Sparse.eval, Sparse.eval, nodeValue3198, nodeValue3698, nodeValue3699, nodeValue3706, nodeValue3814, nodeValue3877, nodeValue4092]

theorem reindexCheck812 : Integer.Sparse.reindex keyMap MixedData.row812 = numericRow812 := by decide +kernel

theorem numericCheck812 (x : Master → ℝ) : Integer.Sparse.eval numericRow812 x =
    (1 : ℝ) * reducedSource812 x := by
  norm_num [numericRow812, reducedSource812, Integer.Sparse.eval, Sparse.eval, nodeValue2620, nodeValue3045, nodeValue3723, nodeValue3732, nodeValue3850, nodeValue3877, nodeValue4092]

theorem reindexCheck814 : Integer.Sparse.reindex keyMap MixedData.row814 = numericRow814 := by decide +kernel

theorem numericCheck814 (x : Master → ℝ) : Integer.Sparse.eval numericRow814 x =
    (17280 : ℝ) * reducedSource814 x := by
  norm_num [numericRow814, reducedSource814, Integer.Sparse.eval, Sparse.eval, nodeValue4816, nodeValue4817, nodeValue4821, nodeValue4836, nodeValue4891, nodeValue5086, nodeValue5090, nodeValue5105, nodeValue5254, nodeValue5260, nodeValue5267, nodeValue5287, nodeValue5360, nodeValue5361, nodeValue5370, nodeValue5397, nodeValue5406, nodeValue5407, nodeValue5410, nodeValue5411, nodeValue5412, nodeValue5425, nodeValue5426, nodeValue5434, nodeValue5435, nodeValue5436] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero803 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource803 (mixedVector B) = 0 := by
  have h2591 : mixedVector B (Sum.inr 2591) = Sparse.eval nodeValue2591 (mixedVector B) := by
    change mixedMoment B node2591 node2591Labels = _
    exact sound2591 B hB hF
  have h3733 : mixedVector B (Sum.inr 3733) = Sparse.eval nodeValue3733 (mixedVector B) := by
    change mixedMoment B node3733 node3733Labels = _
    exact sound3733 B hB hF
  have h3819 : mixedVector B (Sum.inr 3819) = Sparse.eval nodeValue3819 (mixedVector B) := by
    change mixedMoment B node3819 node3819Labels = _
    exact sound3819 B hB hF
  have h3845 : mixedVector B (Sum.inr 3845) = Sparse.eval nodeValue3845 (mixedVector B) := by
    change mixedMoment B node3845 node3845Labels = _
    exact sound3845 B hB hF
  have h3854 : mixedVector B (Sum.inr 3854) = Sparse.eval nodeValue3854 (mixedVector B) := by
    change mixedMoment B node3854 node3854Labels = _
    exact sound3854 B hB hF
  have h3857 : mixedVector B (Sum.inr 3857) = Sparse.eval nodeValue3857 (mixedVector B) := by
    change mixedMoment B node3857 node3857Labels = _
    exact sound3857 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm920, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2591, h3733, h3819, h3845, h3854, h3857, h4092, reducedSource803] using sourceEq920 B hB

theorem rowSound803 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row803 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck803, numericCheck803, reducedZero803 B hB hF, mul_zero]

theorem reducedZero806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource806 (mixedVector B) = 0 := by
  have h2619 : mixedVector B (Sum.inr 2619) = Sparse.eval nodeValue2619 (mixedVector B) := by
    change mixedMoment B node2619 node2619Labels = _
    exact sound2619 B hB hF
  have h2872 : mixedVector B (Sum.inr 2872) = Sparse.eval nodeValue2872 (mixedVector B) := by
    change mixedMoment B node2872 node2872Labels = _
    exact sound2872 B hB hF
  have h3175 : mixedVector B (Sum.inr 3175) = Sparse.eval nodeValue3175 (mixedVector B) := by
    change mixedMoment B node3175 node3175Labels = _
    exact sound3175 B hB hF
  have h3180 : mixedVector B (Sum.inr 3180) = Sparse.eval nodeValue3180 (mixedVector B) := by
    change mixedMoment B node3180 node3180Labels = _
    exact sound3180 B hB hF
  have h3198 : mixedVector B (Sum.inr 3198) = Sparse.eval nodeValue3198 (mixedVector B) := by
    change mixedMoment B node3198 node3198Labels = _
    exact sound3198 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm925, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2619, h2872, h3175, h3180, h3198, h3877, h4092, reducedSource806] using sourceEq925 B hB

theorem rowSound806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row806 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck806, numericCheck806, reducedZero806 B hB hF, mul_zero]

theorem reducedZero807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource807 (mixedVector B) = 0 := by
  have h3180 : mixedVector B (Sum.inr 3180) = Sparse.eval nodeValue3180 (mixedVector B) := by
    change mixedMoment B node3180 node3180Labels = _
    exact sound3180 B hB hF
  have h3732 : mixedVector B (Sum.inr 3732) = Sparse.eval nodeValue3732 (mixedVector B) := by
    change mixedMoment B node3732 node3732Labels = _
    exact sound3732 B hB hF
  have h3788 : mixedVector B (Sum.inr 3788) = Sparse.eval nodeValue3788 (mixedVector B) := by
    change mixedMoment B node3788 node3788Labels = _
    exact sound3788 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3959 : mixedVector B (Sum.inr 3959) = Sparse.eval nodeValue3959 (mixedVector B) := by
    change mixedMoment B node3959 node3959Labels = _
    exact sound3959 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm926, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3180, h3732, h3788, h3809, h3877, h3959, h4092, reducedSource807] using sourceEq926 B hB

theorem rowSound807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row807 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck807, numericCheck807, reducedZero807 B hB hF, mul_zero]

theorem reducedZero808 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource808 (mixedVector B) = 0 := by
  have h2634 : mixedVector B (Sum.inr 2634) = Sparse.eval nodeValue2634 (mixedVector B) := by
    change mixedMoment B node2634 node2634Labels = _
    exact sound2634 B hB hF
  have h2873 : mixedVector B (Sum.inr 2873) = Sparse.eval nodeValue2873 (mixedVector B) := by
    change mixedMoment B node2873 node2873Labels = _
    exact sound2873 B hB hF
  have h3699 : mixedVector B (Sum.inr 3699) = Sparse.eval nodeValue3699 (mixedVector B) := by
    change mixedMoment B node3699 node3699Labels = _
    exact sound3699 B hB hF
  have h3828 : mixedVector B (Sum.inr 3828) = Sparse.eval nodeValue3828 (mixedVector B) := by
    change mixedMoment B node3828 node3828Labels = _
    exact sound3828 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm927, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2634, h2873, h3699, h3828, h3877, h3884, h4092, reducedSource808] using sourceEq927 B hB

theorem rowSound808 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row808 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck808, numericCheck808, reducedZero808 B hB hF, mul_zero]

theorem reducedZero809 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource809 (mixedVector B) = 0 := by
  have h2616 : mixedVector B (Sum.inr 2616) = Sparse.eval nodeValue2616 (mixedVector B) := by
    change mixedMoment B node2616 node2616Labels = _
    exact sound2616 B hB hF
  have h2870 : mixedVector B (Sum.inr 2870) = Sparse.eval nodeValue2870 (mixedVector B) := by
    change mixedMoment B node2870 node2870Labels = _
    exact sound2870 B hB hF
  have h3698 : mixedVector B (Sum.inr 3698) = Sparse.eval nodeValue3698 (mixedVector B) := by
    change mixedMoment B node3698 node3698Labels = _
    exact sound3698 B hB hF
  have h3788 : mixedVector B (Sum.inr 3788) = Sparse.eval nodeValue3788 (mixedVector B) := by
    change mixedMoment B node3788 node3788Labels = _
    exact sound3788 B hB hF
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm928, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2616, h2870, h3698, h3788, h3874, h3877, h4092, reducedSource809] using sourceEq928 B hB

theorem rowSound809 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row809 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck809, numericCheck809, reducedZero809 B hB hF, mul_zero]

theorem reducedZero810 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource810 (mixedVector B) = 0 := by
  have h2885 : mixedVector B (Sum.inr 2885) = Sparse.eval nodeValue2885 (mixedVector B) := by
    change mixedMoment B node2885 node2885Labels = _
    exact sound2885 B hB hF
  have h3706 : mixedVector B (Sum.inr 3706) = Sparse.eval nodeValue3706 (mixedVector B) := by
    change mixedMoment B node3706 node3706Labels = _
    exact sound3706 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3946 : mixedVector B (Sum.inr 3946) = Sparse.eval nodeValue3946 (mixedVector B) := by
    change mixedMoment B node3946 node3946Labels = _
    exact sound3946 B hB hF
  have h3959 : mixedVector B (Sum.inr 3959) = Sparse.eval nodeValue3959 (mixedVector B) := by
    change mixedMoment B node3959 node3959Labels = _
    exact sound3959 B hB hF
  have h3961 : mixedVector B (Sum.inr 3961) = Sparse.eval nodeValue3961 (mixedVector B) := by
    change mixedMoment B node3961 node3961Labels = _
    exact sound3961 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm929, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2885, h3706, h3877, h3946, h3959, h3961, h4092, reducedSource810] using sourceEq929 B hB

theorem rowSound810 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row810 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck810, numericCheck810, reducedZero810 B hB hF, mul_zero]

theorem reducedZero811 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource811 (mixedVector B) = 0 := by
  have h3198 : mixedVector B (Sum.inr 3198) = Sparse.eval nodeValue3198 (mixedVector B) := by
    change mixedMoment B node3198 node3198Labels = _
    exact sound3198 B hB hF
  have h3698 : mixedVector B (Sum.inr 3698) = Sparse.eval nodeValue3698 (mixedVector B) := by
    change mixedMoment B node3698 node3698Labels = _
    exact sound3698 B hB hF
  have h3699 : mixedVector B (Sum.inr 3699) = Sparse.eval nodeValue3699 (mixedVector B) := by
    change mixedMoment B node3699 node3699Labels = _
    exact sound3699 B hB hF
  have h3706 : mixedVector B (Sum.inr 3706) = Sparse.eval nodeValue3706 (mixedVector B) := by
    change mixedMoment B node3706 node3706Labels = _
    exact sound3706 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm930, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3198, h3698, h3699, h3706, h3814, h3877, h4092, reducedSource811] using sourceEq930 B hB

theorem rowSound811 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row811 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck811, numericCheck811, reducedZero811 B hB hF, mul_zero]

theorem reducedZero812 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource812 (mixedVector B) = 0 := by
  have h2620 : mixedVector B (Sum.inr 2620) = Sparse.eval nodeValue2620 (mixedVector B) := by
    change mixedMoment B node2620 node2620Labels = _
    exact sound2620 B hB hF
  have h3045 : mixedVector B (Sum.inr 3045) = Sparse.eval nodeValue3045 (mixedVector B) := by
    change mixedMoment B node3045 node3045Labels = _
    exact sound3045 B hB hF
  have h3723 : mixedVector B (Sum.inr 3723) = Sparse.eval nodeValue3723 (mixedVector B) := by
    change mixedMoment B node3723 node3723Labels = _
    exact sound3723 B hB hF
  have h3732 : mixedVector B (Sum.inr 3732) = Sparse.eval nodeValue3732 (mixedVector B) := by
    change mixedMoment B node3732 node3732Labels = _
    exact sound3732 B hB hF
  have h3850 : mixedVector B (Sum.inr 3850) = Sparse.eval nodeValue3850 (mixedVector B) := by
    change mixedMoment B node3850 node3850Labels = _
    exact sound3850 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm931, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2620, h3045, h3723, h3732, h3850, h3877, h4092, reducedSource812] using sourceEq931 B hB

theorem rowSound812 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row812 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck812, numericCheck812, reducedZero812 B hB hF, mul_zero]

theorem reducedZero814 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource814 (mixedVector B) = 0 := by
  have h4816 : mixedVector B (Sum.inr 4816) = Sparse.eval nodeValue4816 (mixedVector B) := by
    change mixedMoment B node4816 node4816Labels = _
    exact sound4816 B hB hF
  have h4817 : mixedVector B (Sum.inr 4817) = Sparse.eval nodeValue4817 (mixedVector B) := by
    change mixedMoment B node4817 node4817Labels = _
    exact sound4817 B hB hF
  have h4821 : mixedVector B (Sum.inr 4821) = Sparse.eval nodeValue4821 (mixedVector B) := by
    change mixedMoment B node4821 node4821Labels = _
    exact sound4821 B hB hF
  have h4836 : mixedVector B (Sum.inr 4836) = Sparse.eval nodeValue4836 (mixedVector B) := by
    change mixedMoment B node4836 node4836Labels = _
    exact sound4836 B hB hF
  have h4891 : mixedVector B (Sum.inr 4891) = Sparse.eval nodeValue4891 (mixedVector B) := by
    change mixedMoment B node4891 node4891Labels = _
    exact sound4891 B hB hF
  have h5086 : mixedVector B (Sum.inr 5086) = Sparse.eval nodeValue5086 (mixedVector B) := by
    change mixedMoment B node5086 node5086Labels = _
    exact sound5086 B hB hF
  have h5090 : mixedVector B (Sum.inr 5090) = Sparse.eval nodeValue5090 (mixedVector B) := by
    change mixedMoment B node5090 node5090Labels = _
    exact sound5090 B hB hF
  have h5105 : mixedVector B (Sum.inr 5105) = Sparse.eval nodeValue5105 (mixedVector B) := by
    change mixedMoment B node5105 node5105Labels = _
    exact sound5105 B hB hF
  have h5254 : mixedVector B (Sum.inr 5254) = Sparse.eval nodeValue5254 (mixedVector B) := by
    change mixedMoment B node5254 node5254Labels = _
    exact sound5254 B hB hF
  have h5260 : mixedVector B (Sum.inr 5260) = Sparse.eval nodeValue5260 (mixedVector B) := by
    change mixedMoment B node5260 node5260Labels = _
    exact sound5260 B hB hF
  have h5267 : mixedVector B (Sum.inr 5267) = Sparse.eval nodeValue5267 (mixedVector B) := by
    change mixedMoment B node5267 node5267Labels = _
    exact sound5267 B hB hF
  have h5287 : mixedVector B (Sum.inr 5287) = Sparse.eval nodeValue5287 (mixedVector B) := by
    change mixedMoment B node5287 node5287Labels = _
    exact sound5287 B hB hF
  have h5360 : mixedVector B (Sum.inr 5360) = Sparse.eval nodeValue5360 (mixedVector B) := by
    change mixedMoment B node5360 node5360Labels = _
    exact sound5360 B hB hF
  have h5361 : mixedVector B (Sum.inr 5361) = Sparse.eval nodeValue5361 (mixedVector B) := by
    change mixedMoment B node5361 node5361Labels = _
    exact sound5361 B hB hF
  have h5370 : mixedVector B (Sum.inr 5370) = Sparse.eval nodeValue5370 (mixedVector B) := by
    change mixedMoment B node5370 node5370Labels = _
    exact sound5370 B hB hF
  have h5397 : mixedVector B (Sum.inr 5397) = Sparse.eval nodeValue5397 (mixedVector B) := by
    change mixedMoment B node5397 node5397Labels = _
    exact sound5397 B hB hF
  have h5406 : mixedVector B (Sum.inr 5406) = Sparse.eval nodeValue5406 (mixedVector B) := by
    change mixedMoment B node5406 node5406Labels = _
    exact sound5406 B hB hF
  have h5407 : mixedVector B (Sum.inr 5407) = Sparse.eval nodeValue5407 (mixedVector B) := by
    change mixedMoment B node5407 node5407Labels = _
    exact sound5407 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5412 : mixedVector B (Sum.inr 5412) = Sparse.eval nodeValue5412 (mixedVector B) := by
    change mixedMoment B node5412 node5412Labels = _
    exact sound5412 B hB hF
  have h5425 : mixedVector B (Sum.inr 5425) = Sparse.eval nodeValue5425 (mixedVector B) := by
    change mixedMoment B node5425 node5425Labels = _
    exact sound5425 B hB hF
  have h5426 : mixedVector B (Sum.inr 5426) = Sparse.eval nodeValue5426 (mixedVector B) := by
    change mixedMoment B node5426 node5426Labels = _
    exact sound5426 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435_e B hB hF
  have h5436 : mixedVector B (Sum.inr 5436) = Sparse.eval nodeValue5436 (mixedVector B) := by
    change mixedMoment B node5436 node5436Labels = _
    exact sound5436 B hB hF
  simpa only [sourceForm933, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4816, h4817, h4821, h4836, h4891, h5086, h5090, h5105, h5254, h5260, h5267, h5287, h5360, h5361, h5370, h5397, h5406, h5407, h5410, h5411, h5412, h5425, h5426, h5434, h5435, h5436, reducedSource814] using sourceEq933 B hB

theorem rowSound814 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row814 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck814, numericCheck814, reducedZero814 B hB hF, mul_zero]

theorem sourceRowsAt800 : MixedData.sourceRows (800 : Fin 2425) =
    MixedData.row800 := by decide +kernel

theorem sourceRowsAt801 : MixedData.sourceRows (801 : Fin 2425) =
    MixedData.row801 := by decide +kernel

theorem sourceRowsAt802 : MixedData.sourceRows (802 : Fin 2425) =
    MixedData.row802 := by decide +kernel

theorem sourceRowsAt803 : MixedData.sourceRows (803 : Fin 2425) =
    MixedData.row803 := by decide +kernel

theorem sourceRowsAt804 : MixedData.sourceRows (804 : Fin 2425) =
    MixedData.row804 := by decide +kernel

theorem sourceRowsAt805 : MixedData.sourceRows (805 : Fin 2425) =
    MixedData.row805 := by decide +kernel

theorem sourceRowsAt806 : MixedData.sourceRows (806 : Fin 2425) =
    MixedData.row806 := by decide +kernel

theorem sourceRowsAt807 : MixedData.sourceRows (807 : Fin 2425) =
    MixedData.row807 := by decide +kernel

theorem sourceRowsAt808 : MixedData.sourceRows (808 : Fin 2425) =
    MixedData.row808 := by decide +kernel

theorem sourceRowsAt809 : MixedData.sourceRows (809 : Fin 2425) =
    MixedData.row809 := by decide +kernel

theorem sourceRowsAt810 : MixedData.sourceRows (810 : Fin 2425) =
    MixedData.row810 := by decide +kernel

theorem sourceRowsAt811 : MixedData.sourceRows (811 : Fin 2425) =
    MixedData.row811 := by decide +kernel

theorem sourceRowsAt812 : MixedData.sourceRows (812 : Fin 2425) =
    MixedData.row812 := by decide +kernel

theorem sourceRowsAt813 : MixedData.sourceRows (813 : Fin 2425) =
    MixedData.row813 := by decide +kernel

theorem sourceRowsAt814 : MixedData.sourceRows (814 : Fin 2425) =
    MixedData.row814 := by decide +kernel

theorem sourceRowsAt815 : MixedData.sourceRows (815 : Fin 2425) =
    MixedData.row815 := by decide +kernel

theorem chunkSound50_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 50) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 800 ∨ k.val = 801 ∨ k.val = 802 ∨ k.val = 803 ∨ k.val = 804 ∨ k.val = 805 ∨ k.val = 806 ∨ k.val = 807 ∨ k.val = 808 ∨ k.val = 809 ∨ k.val = 810 ∨ k.val = 811 ∨ k.val = 812 ∨ k.val = 813 ∨ k.val = 814 ∨ k.val = 815 := by omega
  rcases heq with h800 | h801 | h802 | h803 | h804 | h805 | h806 | h807 | h808 | h809 | h810 | h811 | h812 | h813 | h814 | h815
  · have he : k = (800 : Fin 2425) := Fin.ext h800
    subst k
    rw [sourceRowsAt800]
    exact rowSound800_e B hB hF
  · have he : k = (801 : Fin 2425) := Fin.ext h801
    subst k
    rw [sourceRowsAt801]
    exact rowSound801_e B hB hF
  · have he : k = (802 : Fin 2425) := Fin.ext h802
    subst k
    rw [sourceRowsAt802]
    exact rowSound802_e B hB hF
  · have he : k = (803 : Fin 2425) := Fin.ext h803
    subst k
    rw [sourceRowsAt803]
    exact rowSound803 B hB hF
  · have he : k = (804 : Fin 2425) := Fin.ext h804
    subst k
    rw [sourceRowsAt804]
    exact rowSound804_e B hB hF
  · have he : k = (805 : Fin 2425) := Fin.ext h805
    subst k
    rw [sourceRowsAt805]
    exact rowSound805_e B hB hF
  · have he : k = (806 : Fin 2425) := Fin.ext h806
    subst k
    rw [sourceRowsAt806]
    exact rowSound806 B hB hF
  · have he : k = (807 : Fin 2425) := Fin.ext h807
    subst k
    rw [sourceRowsAt807]
    exact rowSound807 B hB hF
  · have he : k = (808 : Fin 2425) := Fin.ext h808
    subst k
    rw [sourceRowsAt808]
    exact rowSound808 B hB hF
  · have he : k = (809 : Fin 2425) := Fin.ext h809
    subst k
    rw [sourceRowsAt809]
    exact rowSound809 B hB hF
  · have he : k = (810 : Fin 2425) := Fin.ext h810
    subst k
    rw [sourceRowsAt810]
    exact rowSound810 B hB hF
  · have he : k = (811 : Fin 2425) := Fin.ext h811
    subst k
    rw [sourceRowsAt811]
    exact rowSound811 B hB hF
  · have he : k = (812 : Fin 2425) := Fin.ext h812
    subst k
    rw [sourceRowsAt812]
    exact rowSound812 B hB hF
  · have he : k = (813 : Fin 2425) := Fin.ext h813
    subst k
    rw [sourceRowsAt813]
    exact rowSound813_e B hB hF
  · have he : k = (814 : Fin 2425) := Fin.ext h814
    subst k
    rw [sourceRowsAt814]
    exact rowSound814 B hB hF
  · have he : k = (815 : Fin 2425) := Fin.ext h815
    subst k
    rw [sourceRowsAt815]
    exact rowSound815_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound50_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound50_e_oai
