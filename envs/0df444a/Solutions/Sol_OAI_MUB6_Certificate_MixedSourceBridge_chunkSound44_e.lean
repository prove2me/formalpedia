-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:18:12.337783+00:00
-- url     : https://prove2.me/submissions/a58d0dc1-e2d2-45f6-a00f-ae7aef739723

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3100_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3226_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5292_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5452_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound707_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound710_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound711_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound712_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound717_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound718_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound719_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12887 raw12887Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw12887 raw12887Labels = mixedMoment B raw12887step0 raw12887step0Labels := by
      have ha : raw12887step0 = (fun i j => raw12887 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12887step0 raw12887; decide +kernel
      have hl : raw12887step0Labels = raw12887Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12887 raw12887Labels permutation152 permutation6
    mixedMoment B raw12887step0 raw12887step0Labels = mixedMoment B raw12887step1 raw12887step1Labels := by
      have ha : raw12887step1 = raw12887step0 := by apply Matrix.ext; unfold raw12887step1 raw12887step0; decide +kernel
      have hl : raw12887step0Labels = labelEmbedding9 ∘ raw12887step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12887step0 raw12887step0Labels raw12887step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

theorem canonical12915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12915 raw12915Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw12915 raw12915Labels = mixedMoment B raw12915step0 raw12915step0Labels := by
      have ha : raw12915step0 = (fun i j => raw12915 (permutation179 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12915step0 raw12915; decide +kernel
      have hl : raw12915step0Labels = raw12915Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12915 raw12915Labels permutation179 permutation7
    mixedMoment B raw12915step0 raw12915step0Labels = mixedMoment B raw12915step1 raw12915step1Labels := by
      have ha : raw12915step1 = raw12915step0 := by apply Matrix.ext; unfold raw12915step1 raw12915step0; decide +kernel
      have hl : raw12915step0Labels = labelEmbedding1 ∘ raw12915step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12915step0 raw12915step0Labels raw12915step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3023 node3023Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12928 raw12928Labels = mixedMoment B node3551 node3551Labels := by
  calc
    mixedMoment B raw12928 raw12928Labels = mixedMoment B raw12928step0 raw12928step0Labels := by
      have ha : raw12928step0 = (fun i j => raw12928 (permutation213 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12928step0 raw12928; decide +kernel
      have hl : raw12928step0Labels = raw12928Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12928 raw12928Labels permutation213 permutation4
    mixedMoment B raw12928step0 raw12928step0Labels = mixedMoment B raw12928step1 raw12928step1Labels := by
      have ha : raw12928step1 = -raw12928step0 := by apply Matrix.ext; change ∀ i j, raw12928step1 i j = -(raw12928step0 i j); unfold raw12928step1 raw12928step0; decide +kernel
      have hl : raw12928step1Labels = raw12928step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3551 node3551Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13071 raw13071Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw13071 raw13071Labels = mixedMoment B raw13071step0 raw13071step0Labels := by
      have ha : raw13071step0 = (fun i j => raw13071 (permutation216 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13071step0 raw13071; decide +kernel
      have hl : raw13071step0Labels = raw13071Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13071 raw13071Labels permutation216 permutation4
    mixedMoment B raw13071step0 raw13071step0Labels = mixedMoment B raw13071step1 raw13071step1Labels := by
      have ha : raw13071step1 = -raw13071step0 := by apply Matrix.ext; change ∀ i j, raw13071step1 i j = -(raw13071step0 i j); unfold raw13071step1 raw13071step0; decide +kernel
      have hl : raw13071step1Labels = raw13071step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13071step1 raw13071step1Labels = mixedMoment B raw13071step2 raw13071step2Labels := by
      have ha : raw13071step2 = raw13071step1 := by apply Matrix.ext; unfold raw13071step2 raw13071step1; decide +kernel
      have hl : raw13071step1Labels = labelEmbedding7 ∘ raw13071step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13071step1 raw13071step1Labels raw13071step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

theorem canonical13072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13072 raw13072Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw13072 raw13072Labels = mixedMoment B raw13072step0 raw13072step0Labels := by
      have ha : raw13072step0 = (fun i j => raw13072 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13072step0 raw13072; decide +kernel
      have hl : raw13072step0Labels = raw13072Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13072 raw13072Labels permutation154 permutation6
    mixedMoment B raw13072step0 raw13072step0Labels = mixedMoment B raw13072step1 raw13072step1Labels := by
      have ha : raw13072step1 = raw13072step0 := by apply Matrix.ext; unfold raw13072step1 raw13072step0; decide +kernel
      have hl : raw13072step0Labels = labelEmbedding9 ∘ raw13072step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13072step0 raw13072step0Labels raw13072step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

theorem canonical13073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13073 raw13073Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw13073 raw13073Labels = mixedMoment B raw13073step0 raw13073step0Labels := by
      have ha : raw13073step0 = (fun i j => raw13073 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13073step0 raw13073; decide +kernel
      have hl : raw13073step0Labels = raw13073Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13073 raw13073Labels permutation156 permutation6
    mixedMoment B raw13073step0 raw13073step0Labels = mixedMoment B raw13073step1 raw13073step1Labels := by
      have ha : raw13073step1 = raw13073step0 := by apply Matrix.ext; unfold raw13073step1 raw13073step0; decide +kernel
      have hl : raw13073step0Labels = labelEmbedding9 ∘ raw13073step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13073step0 raw13073step0Labels raw13073step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

theorem canonical13082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13082 raw13082Labels = mixedMoment B node2741 node2741Labels := by
  calc
    mixedMoment B raw13082 raw13082Labels = mixedMoment B raw13082step0 raw13082step0Labels := by
      have hz : ∀ j, raw13082 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13082step0 = (fun i j => raw13082 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13082step0 raw13082; decide +kernel
      have hl : raw13082step0Labels = raw13082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13082 raw13082Labels permutation265 hz
    mixedMoment B raw13082step0 raw13082step0Labels = mixedMoment B raw13082step1 raw13082step1Labels := by
      have ha : raw13082step1 = (fun i j => raw13082step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13082step1 raw13082step0; decide +kernel
      have hl : raw13082step1Labels = raw13082step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13082step0 raw13082step0Labels permutation32 permutation7
    mixedMoment B raw13082step1 raw13082step1Labels = mixedMoment B raw13082step2 raw13082step2Labels := by
      have ha : raw13082step2 = raw13082step1 := by apply Matrix.ext; unfold raw13082step2 raw13082step1; decide +kernel
      have hl : raw13082step1Labels = labelEmbedding1 ∘ raw13082step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13082step1 raw13082step1Labels raw13082step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2741 node2741Labels := by rfl

theorem canonical13085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13085 raw13085Labels = mixedMoment B node3221 node3221Labels := by
  calc
    mixedMoment B raw13085 raw13085Labels = mixedMoment B raw13085step0 raw13085step0Labels := by
      have ha : raw13085step0 = (fun i j => raw13085 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13085step0 raw13085; decide +kernel
      have hl : raw13085step0Labels = raw13085Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13085 raw13085Labels permutation176 permutation7
    mixedMoment B raw13085step0 raw13085step0Labels = mixedMoment B raw13085step1 raw13085step1Labels := by
      have ha : raw13085step1 = raw13085step0 := by apply Matrix.ext; unfold raw13085step1 raw13085step0; decide +kernel
      have hl : raw13085step0Labels = labelEmbedding1 ∘ raw13085step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13085step0 raw13085step0Labels raw13085step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3221 node3221Labels := by rfl

theorem canonical13087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13087 raw13087Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw13087 raw13087Labels = mixedMoment B raw13087step0 raw13087step0Labels := by
      have ha : raw13087step0 = (fun i j => raw13087 (permutation177 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13087step0 raw13087; decide +kernel
      have hl : raw13087step0Labels = raw13087Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13087 raw13087Labels permutation177 permutation7
    mixedMoment B raw13087step0 raw13087step0Labels = mixedMoment B raw13087step1 raw13087step1Labels := by
      have ha : raw13087step1 = raw13087step0 := by apply Matrix.ext; unfold raw13087step1 raw13087step0; decide +kernel
      have hl : raw13087step0Labels = labelEmbedding1 ∘ raw13087step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13087step0 raw13087step0Labels raw13087step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3023 node3023Labels := by rfl

theorem canonical13088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13088 raw13088Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw13088 raw13088Labels = mixedMoment B raw13088step0 raw13088step0Labels := by
      have ha : raw13088step0 = (fun i j => raw13088 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13088step0 raw13088; decide +kernel
      have hl : raw13088step0Labels = raw13088Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13088 raw13088Labels permutation176 permutation7
    mixedMoment B raw13088step0 raw13088step0Labels = mixedMoment B raw13088step1 raw13088step1Labels := by
      have ha : raw13088step1 = raw13088step0 := by apply Matrix.ext; unfold raw13088step1 raw13088step0; decide +kernel
      have hl : raw13088step0Labels = labelEmbedding1 ∘ raw13088step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13088step0 raw13088step0Labels raw13088step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3023 node3023Labels := by rfl

theorem canonical13093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13093 raw13093Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw13093 raw13093Labels = mixedMoment B raw13093step0 raw13093step0Labels := by
      have hz : ∀ j, raw13093 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13093step0 = (fun i j => raw13093 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13093step0 raw13093; decide +kernel
      have hl : raw13093step0Labels = raw13093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13093 raw13093Labels permutation265 hz
    mixedMoment B raw13093step0 raw13093step0Labels = mixedMoment B raw13093step1 raw13093step1Labels := by
      have ha : raw13093step1 = (fun i j => raw13093step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13093step1 raw13093step0; decide +kernel
      have hl : raw13093step1Labels = raw13093step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13093step0 raw13093step0Labels permutation32 permutation7
    mixedMoment B raw13093step1 raw13093step1Labels = mixedMoment B raw13093step2 raw13093step2Labels := by
      have ha : raw13093step2 = raw13093step1 := by apply Matrix.ext; unfold raw13093step2 raw13093step1; decide +kernel
      have hl : raw13093step1Labels = labelEmbedding1 ∘ raw13093step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13093step1 raw13093step1Labels raw13093step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3100 node3100Labels := by rfl

theorem canonical13097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13097 raw13097Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw13097 raw13097Labels = mixedMoment B raw13097step0 raw13097step0Labels := by
      have hz : ∀ j, raw13097 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13097step0 = (fun i j => raw13097 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13097step0 raw13097; decide +kernel
      have hl : raw13097step0Labels = raw13097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13097 raw13097Labels permutation265 hz
    mixedMoment B raw13097step0 raw13097step0Labels = mixedMoment B raw13097step1 raw13097step1Labels := by
      have ha : raw13097step1 = (fun i j => raw13097step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13097step1 raw13097step0; decide +kernel
      have hl : raw13097step1Labels = raw13097step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13097step0 raw13097step0Labels permutation34 permutation7
    mixedMoment B raw13097step1 raw13097step1Labels = mixedMoment B raw13097step2 raw13097step2Labels := by
      have ha : raw13097step2 = raw13097step1 := by apply Matrix.ext; unfold raw13097step2 raw13097step1; decide +kernel
      have hl : raw13097step1Labels = labelEmbedding1 ∘ raw13097step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13097step1 raw13097step1Labels raw13097step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3100 node3100Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13322 raw13322Labels = mixedMoment B node5247 node5247Labels := by
  calc
    mixedMoment B raw13322 raw13322Labels = mixedMoment B raw13322step0 raw13322step0Labels := by
      have ha : raw13322step0 = (fun i j => raw13322 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13322step0 raw13322; decide +kernel
      have hl : raw13322step0Labels = raw13322Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13322 raw13322Labels permutation155 permutation7
    mixedMoment B raw13322step0 raw13322step0Labels = mixedMoment B raw13322step1 raw13322step1Labels := by
      have ha : raw13322step1 = raw13322step0 := by apply Matrix.ext; unfold raw13322step1 raw13322step0; decide +kernel
      have hl : raw13322step0Labels = labelEmbedding10 ∘ raw13322step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13322step0 raw13322step0Labels raw13322step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5247 node5247Labels := by rfl

theorem canonical13327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13327 raw13327Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw13327 raw13327Labels = mixedMoment B raw13327step0 raw13327step0Labels := by
      have ha : raw13327step0 = (fun i j => raw13327 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13327step0 raw13327; decide +kernel
      have hl : raw13327step0Labels = raw13327Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13327 raw13327Labels permutation176 permutation6
    mixedMoment B raw13327step0 raw13327step0Labels = mixedMoment B raw13327step1 raw13327step1Labels := by
      have ha : raw13327step1 = raw13327step0 := by apply Matrix.ext; unfold raw13327step1 raw13327step0; decide +kernel
      have hl : raw13327step0Labels = labelEmbedding9 ∘ raw13327step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13327step0 raw13327step0Labels raw13327step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

theorem canonical13331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13331 raw13331Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw13331 raw13331Labels = mixedMoment B raw13331step0 raw13331step0Labels := by
      have ha : raw13331step0 = (fun i j => raw13331 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13331step0 raw13331; decide +kernel
      have hl : raw13331step0Labels = raw13331Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13331 raw13331Labels permutation153 permutation6
    mixedMoment B raw13331step0 raw13331step0Labels = mixedMoment B raw13331step1 raw13331step1Labels := by
      have ha : raw13331step1 = raw13331step0 := by apply Matrix.ext; unfold raw13331step1 raw13331step0; decide +kernel
      have hl : raw13331step0Labels = labelEmbedding9 ∘ raw13331step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13331step0 raw13331step0Labels raw13331step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical13352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13352 raw13352Labels = mixedMoment B node2703 node2703Labels := by
  calc
    mixedMoment B raw13352 raw13352Labels = mixedMoment B raw13352step0 raw13352step0Labels := by
      have ha : raw13352step0 = (fun i j => raw13352 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13352step0 raw13352; decide +kernel
      have hl : raw13352step0Labels = raw13352Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13352 raw13352Labels permutation155 permutation7
    mixedMoment B raw13352step0 raw13352step0Labels = mixedMoment B raw13352step1 raw13352step1Labels := by
      have ha : raw13352step1 = raw13352step0 := by apply Matrix.ext; unfold raw13352step1 raw13352step0; decide +kernel
      have hl : raw13352step0Labels = labelEmbedding1 ∘ raw13352step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13352step0 raw13352step0Labels raw13352step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2703 node2703Labels := by rfl

theorem canonical13357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13357 raw13357Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw13357 raw13357Labels = mixedMoment B raw13357step0 raw13357step0Labels := by
      have ha : raw13357step0 = (fun i j => raw13357 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13357step0 raw13357; decide +kernel
      have hl : raw13357step0Labels = raw13357Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13357 raw13357Labels permutation155 permutation7
    mixedMoment B raw13357step0 raw13357step0Labels = mixedMoment B raw13357step1 raw13357step1Labels := by
      have ha : raw13357step1 = raw13357step0 := by apply Matrix.ext; unfold raw13357step1 raw13357step0; decide +kernel
      have hl : raw13357step0Labels = labelEmbedding1 ∘ raw13357step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13357step0 raw13357step0Labels raw13357step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3023 node3023Labels := by rfl

theorem canonical13358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13358 raw13358Labels = mixedMoment B node3226 node3226Labels := by
  calc
    mixedMoment B raw13358 raw13358Labels = mixedMoment B raw13358step0 raw13358step0Labels := by
      have ha : raw13358step0 = (fun i j => raw13358 (permutation216 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13358step0 raw13358; decide +kernel
      have hl : raw13358step0Labels = raw13358Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13358 raw13358Labels permutation216 permutation5
    mixedMoment B raw13358step0 raw13358step0Labels = mixedMoment B raw13358step1 raw13358step1Labels := by
      have ha : raw13358step1 = -raw13358step0 := by apply Matrix.ext; change ∀ i j, raw13358step1 i j = -(raw13358step0 i j); unfold raw13358step1 raw13358step0; decide +kernel
      have hl : raw13358step1Labels = raw13358step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13358step1 raw13358step1Labels = mixedMoment B raw13358step2 raw13358step2Labels := by
      have ha : raw13358step2 = raw13358step1 := by apply Matrix.ext; unfold raw13358step2 raw13358step1; decide +kernel
      have hl : raw13358step1Labels = labelEmbedding1 ∘ raw13358step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13358step1 raw13358step1Labels raw13358step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3226 node3226Labels := by rfl

theorem canonical13359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13359 raw13359Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw13359 raw13359Labels = mixedMoment B raw13359step0 raw13359step0Labels := by
      have ha : raw13359step0 = (fun i j => raw13359 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13359step0 raw13359; decide +kernel
      have hl : raw13359step0Labels = raw13359Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13359 raw13359Labels permutation156 permutation7
    mixedMoment B raw13359step0 raw13359step0Labels = mixedMoment B raw13359step1 raw13359step1Labels := by
      have ha : raw13359step1 = raw13359step0 := by apply Matrix.ext; unfold raw13359step1 raw13359step0; decide +kernel
      have hl : raw13359step0Labels = labelEmbedding1 ∘ raw13359step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13359step0 raw13359step0Labels raw13359step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

theorem canonical13363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13363 raw13363Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw13363 raw13363Labels = mixedMoment B raw13363step0 raw13363step0Labels := by
      have ha : raw13363step0 = (fun i j => raw13363 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13363step0 raw13363; decide +kernel
      have hl : raw13363step0Labels = raw13363Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13363 raw13363Labels permutation155 permutation7
    mixedMoment B raw13363step0 raw13363step0Labels = mixedMoment B raw13363step1 raw13363step1Labels := by
      have ha : raw13363step1 = raw13363step0 := by apply Matrix.ext; unfold raw13363step1 raw13363step0; decide +kernel
      have hl : raw13363step0Labels = labelEmbedding1 ∘ raw13363step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13363step0 raw13363step0Labels raw13363step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

theorem canonical13366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13366 raw13366Labels = mixedMoment B node3489 node3489Labels := by
  calc
    mixedMoment B raw13366 raw13366Labels = mixedMoment B raw13366step0 raw13366step0Labels := by
      have ha : raw13366step0 = (fun i j => raw13366 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13366step0 raw13366; decide +kernel
      have hl : raw13366step0Labels = raw13366Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13366 raw13366Labels permutation156 permutation2
    mixedMoment B raw13366step0 raw13366step0Labels = mixedMoment B raw13366step1 raw13366step1Labels := by
      have ha : raw13366step1 = -raw13366step0 := by apply Matrix.ext; change ∀ i j, raw13366step1 i j = -(raw13366step0 i j); unfold raw13366step1 raw13366step0; decide +kernel
      have hl : raw13366step1Labels = raw13366step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3489 node3489Labels := by rfl

theorem canonical13369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13369 raw13369Labels = mixedMoment B node2105 node2105Labels := by
  calc
    mixedMoment B raw13369 raw13369Labels = mixedMoment B raw13369step0 raw13369step0Labels := by
      have ha : raw13369step0 = (fun i j => raw13369 (permutation200 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13369step0 raw13369; decide +kernel
      have hl : raw13369step0Labels = raw13369Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13369 raw13369Labels permutation200 permutation4
    mixedMoment B raw13369step0 raw13369step0Labels = mixedMoment B raw13369step1 raw13369step1Labels := by
      have ha : raw13369step1 = -raw13369step0 := by apply Matrix.ext; change ∀ i j, raw13369step1 i j = -(raw13369step0 i j); unfold raw13369step1 raw13369step0; decide +kernel
      have hl : raw13369step1Labels = raw13369step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2105 node2105Labels := by rfl

theorem canonical13371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13371 raw13371Labels = mixedMoment B node3073 node3073Labels := by
  calc
    mixedMoment B raw13371 raw13371Labels = mixedMoment B raw13371step0 raw13371step0Labels := by
      have ha : raw13371step0 = (fun i j => raw13371 (permutation502 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13371step0 raw13371; decide +kernel
      have hl : raw13371step0Labels = raw13371Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13371 raw13371Labels permutation502 permutation2
    _ = mixedMoment B node3073 node3073Labels := by rfl

theorem canonical13372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13372 raw13372Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw13372 raw13372Labels = mixedMoment B raw13372step0 raw13372step0Labels := by
      have hz : ∀ j, raw13372 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13372step0 = (fun i j => raw13372 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13372step0 raw13372; decide +kernel
      have hl : raw13372step0Labels = raw13372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13372 raw13372Labels permutation346 hz
    mixedMoment B raw13372step0 raw13372step0Labels = mixedMoment B raw13372step1 raw13372step1Labels := by
      have ha : raw13372step1 = (fun i j => raw13372step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13372step1 raw13372step0; decide +kernel
      have hl : raw13372step1Labels = raw13372step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13372step0 raw13372step0Labels permutation38 permutation4
    mixedMoment B raw13372step1 raw13372step1Labels = mixedMoment B raw13372step2 raw13372step2Labels := by
      have ha : raw13372step2 = -raw13372step1 := by apply Matrix.ext; change ∀ i j, raw13372step2 i j = -(raw13372step1 i j); unfold raw13372step2 raw13372step1; decide +kernel
      have hl : raw13372step2Labels = raw13372step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3581 node3581Labels := by rfl

theorem canonical13373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13373 raw13373Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw13373 raw13373Labels = mixedMoment B raw13373step0 raw13373step0Labels := by
      have ha : raw13373step0 = (fun i j => raw13373 (permutation218 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13373step0 raw13373; decide +kernel
      have hl : raw13373step0Labels = raw13373Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13373 raw13373Labels permutation218 permutation4
    mixedMoment B raw13373step0 raw13373step0Labels = mixedMoment B raw13373step1 raw13373step1Labels := by
      have ha : raw13373step1 = -raw13373step0 := by apply Matrix.ext; change ∀ i j, raw13373step1 i j = -(raw13373step0 i j); unfold raw13373step1 raw13373step0; decide +kernel
      have hl : raw13373step1Labels = raw13373step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3571 node3571Labels := by rfl

theorem canonical13374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13374 raw13374Labels = mixedMoment B node3551 node3551Labels := by
  calc
    mixedMoment B raw13374 raw13374Labels = mixedMoment B raw13374step0 raw13374step0Labels := by
      have ha : raw13374step0 = (fun i j => raw13374 (permutation215 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13374step0 raw13374; decide +kernel
      have hl : raw13374step0Labels = raw13374Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13374 raw13374Labels permutation215 permutation4
    mixedMoment B raw13374step0 raw13374step0Labels = mixedMoment B raw13374step1 raw13374step1Labels := by
      have ha : raw13374step1 = -raw13374step0 := by apply Matrix.ext; change ∀ i j, raw13374step1 i j = -(raw13374step0 i j); unfold raw13374step1 raw13374step0; decide +kernel
      have hl : raw13374step1Labels = raw13374step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3551 node3551Labels := by rfl

theorem canonical13375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13375 raw13375Labels = mixedMoment B node5447 node5447Labels := by
  calc
    _ = mixedMoment B node5447 node5447Labels := by rfl

theorem canonical13376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13376 raw13376Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw13376 raw13376Labels = mixedMoment B raw13376step0 raw13376step0Labels := by
      have ha : raw13376step0 = (fun i j => raw13376 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13376step0 raw13376; decide +kernel
      have hl : raw13376step0Labels = raw13376Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13376 raw13376Labels permutation176 permutation2
    _ = mixedMoment B node5447 node5447Labels := by rfl

theorem canonical13377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13377 raw13377Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw13377 raw13377Labels = mixedMoment B raw13377step0 raw13377step0Labels := by
      have hz : ∀ j, raw13377 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13377step0 = (fun i j => raw13377 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13377step0 raw13377; decide +kernel
      have hl : raw13377step0Labels = raw13377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13377 raw13377Labels permutation434 hz
    _ = mixedMoment B node5452 node5452Labels := by rfl

theorem canonical13378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13378 raw13378Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw13378 raw13378Labels = mixedMoment B raw13378step0 raw13378step0Labels := by
      have hz : ∀ j, raw13378 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13378step0 = (fun i j => raw13378 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13378step0 raw13378; decide +kernel
      have hl : raw13378step0Labels = raw13378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13378 raw13378Labels permutation520 hz
    _ = mixedMoment B node5452 node5452Labels := by rfl

theorem canonical13379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13379 raw13379Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw13379 raw13379Labels = mixedMoment B raw13379step0 raw13379step0Labels := by
      have hz : ∀ j, raw13379 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13379step0 = (fun i j => raw13379 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13379step0 raw13379; decide +kernel
      have hl : raw13379step0Labels = raw13379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13379 raw13379Labels permutation590 hz
    _ = mixedMoment B node5452 node5452Labels := by rfl

theorem canonical13380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13380 raw13380Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw13380 raw13380Labels = mixedMoment B raw13380step0 raw13380step0Labels := by
      have ha : raw13380step0 = (fun i j => raw13380 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13380step0 raw13380; decide +kernel
      have hl : raw13380step0Labels = raw13380Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13380 raw13380Labels permutation176 permutation3
    mixedMoment B raw13380step0 raw13380step0Labels = mixedMoment B raw13380step1 raw13380step1Labels := by
      have ha : raw13380step1 = raw13380step0 := by apply Matrix.ext; unfold raw13380step1 raw13380step0; decide +kernel
      have hl : raw13380step0Labels = labelEmbedding6 ∘ raw13380step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13380step0 raw13380step0Labels raw13380step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

theorem canonical13381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13381 raw13381Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw13381 raw13381Labels = mixedMoment B raw13381step0 raw13381step0Labels := by
      have ha : raw13381step0 = (fun i j => raw13381 (permutation185 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13381step0 raw13381; decide +kernel
      have hl : raw13381step0Labels = raw13381Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13381 raw13381Labels permutation185 permutation2
    _ = mixedMoment B node5202 node5202Labels := by rfl

theorem canonical13382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13382 raw13382Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw13382 raw13382Labels = mixedMoment B raw13382step0 raw13382step0Labels := by
      have hz : ∀ j, raw13382 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13382step0 = (fun i j => raw13382 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13382step0 raw13382; decide +kernel
      have hl : raw13382step0Labels = raw13382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13382 raw13382Labels permutation434 hz
    mixedMoment B raw13382step0 raw13382step0Labels = mixedMoment B raw13382step1 raw13382step1Labels := by
      have ha : raw13382step1 = (fun i j => raw13382step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13382step1 raw13382step0; decide +kernel
      have hl : raw13382step1Labels = raw13382step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13382step0 raw13382step0Labels permutation41 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical13383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13383 raw13383Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw13383 raw13383Labels = mixedMoment B raw13383step0 raw13383step0Labels := by
      have hz : ∀ j, raw13383 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13383step0 = (fun i j => raw13383 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13383step0 raw13383; decide +kernel
      have hl : raw13383step0Labels = raw13383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13383 raw13383Labels permutation520 hz
    mixedMoment B raw13383step0 raw13383step0Labels = mixedMoment B raw13383step1 raw13383step1Labels := by
      have ha : raw13383step1 = (fun i j => raw13383step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13383step1 raw13383step0; decide +kernel
      have hl : raw13383step1Labels = raw13383step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13383step0 raw13383step0Labels permutation41 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical13384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13384 raw13384Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw13384 raw13384Labels = mixedMoment B raw13384step0 raw13384step0Labels := by
      have hz : ∀ j, raw13384 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13384step0 = (fun i j => raw13384 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13384step0 raw13384; decide +kernel
      have hl : raw13384step0Labels = raw13384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13384 raw13384Labels permutation590 hz
    mixedMoment B raw13384step0 raw13384step0Labels = mixedMoment B raw13384step1 raw13384step1Labels := by
      have ha : raw13384step1 = (fun i j => raw13384step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13384step1 raw13384step0; decide +kernel
      have hl : raw13384step1Labels = raw13384step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13384step0 raw13384step0Labels permutation41 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical13385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13385 raw13385Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw13385 raw13385Labels = mixedMoment B raw13385step0 raw13385step0Labels := by
      have ha : raw13385step0 = (fun i j => raw13385 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13385step0 raw13385; decide +kernel
      have hl : raw13385step0Labels = raw13385Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13385 raw13385Labels permutation152 permutation3
    mixedMoment B raw13385step0 raw13385step0Labels = mixedMoment B raw13385step1 raw13385step1Labels := by
      have ha : raw13385step1 = raw13385step0 := by apply Matrix.ext; unfold raw13385step1 raw13385step0; decide +kernel
      have hl : raw13385step0Labels = labelEmbedding6 ∘ raw13385step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13385step0 raw13385step0Labels raw13385step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

theorem canonical13386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13386 raw13386Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw13386 raw13386Labels = mixedMoment B raw13386step0 raw13386step0Labels := by
      have ha : raw13386step0 = (fun i j => raw13386 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13386step0 raw13386; decide +kernel
      have hl : raw13386step0Labels = raw13386Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13386 raw13386Labels permutation161 permutation2
    _ = mixedMoment B node5202 node5202Labels := by rfl

theorem canonical13387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13387 raw13387Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw13387 raw13387Labels = mixedMoment B raw13387step0 raw13387step0Labels := by
      have hz : ∀ j, raw13387 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13387step0 = (fun i j => raw13387 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13387step0 raw13387; decide +kernel
      have hl : raw13387step0Labels = raw13387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13387 raw13387Labels permutation434 hz
    mixedMoment B raw13387step0 raw13387step0Labels = mixedMoment B raw13387step1 raw13387step1Labels := by
      have ha : raw13387step1 = (fun i j => raw13387step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13387step1 raw13387step0; decide +kernel
      have hl : raw13387step1Labels = raw13387step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13387step0 raw13387step0Labels permutation35 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical13388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13388 raw13388Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw13388 raw13388Labels = mixedMoment B raw13388step0 raw13388step0Labels := by
      have hz : ∀ j, raw13388 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13388step0 = (fun i j => raw13388 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13388step0 raw13388; decide +kernel
      have hl : raw13388step0Labels = raw13388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13388 raw13388Labels permutation520 hz
    mixedMoment B raw13388step0 raw13388step0Labels = mixedMoment B raw13388step1 raw13388step1Labels := by
      have ha : raw13388step1 = (fun i j => raw13388step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13388step1 raw13388step0; decide +kernel
      have hl : raw13388step1Labels = raw13388step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13388step0 raw13388step0Labels permutation35 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical13389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13389 raw13389Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw13389 raw13389Labels = mixedMoment B raw13389step0 raw13389step0Labels := by
      have hz : ∀ j, raw13389 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13389step0 = (fun i j => raw13389 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13389step0 raw13389; decide +kernel
      have hl : raw13389step0Labels = raw13389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13389 raw13389Labels permutation590 hz
    mixedMoment B raw13389step0 raw13389step0Labels = mixedMoment B raw13389step1 raw13389step1Labels := by
      have ha : raw13389step1 = (fun i j => raw13389step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13389step1 raw13389step0; decide +kernel
      have hl : raw13389step1Labels = raw13389step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13389step0 raw13389step0Labels permutation35 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical13390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13390 raw13390Labels = mixedMoment B node4581 node4581Labels := by
  calc
    mixedMoment B raw13390 raw13390Labels = mixedMoment B raw13390step0 raw13390step0Labels := by
      have ha : raw13390step0 = (fun i j => raw13390 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13390step0 raw13390; decide +kernel
      have hl : raw13390step0Labels = raw13390Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13390 raw13390Labels permutation155 permutation3
    mixedMoment B raw13390step0 raw13390step0Labels = mixedMoment B raw13390step1 raw13390step1Labels := by
      have ha : raw13390step1 = raw13390step0 := by apply Matrix.ext; unfold raw13390step1 raw13390step0; decide +kernel
      have hl : raw13390step0Labels = labelEmbedding6 ∘ raw13390step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13390step0 raw13390step0Labels raw13390step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4581 node4581Labels := by rfl

theorem canonical13391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13391 raw13391Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw13391 raw13391Labels = mixedMoment B raw13391step0 raw13391step0Labels := by
      have ha : raw13391step0 = (fun i j => raw13391 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13391step0 raw13391; decide +kernel
      have hl : raw13391step0Labels = raw13391Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13391 raw13391Labels permutation155 permutation2
    _ = mixedMoment B node5192 node5192Labels := by rfl

theorem canonical13392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13392 raw13392Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw13392 raw13392Labels = mixedMoment B raw13392step0 raw13392step0Labels := by
      have ha : raw13392step0 = (fun i j => raw13392 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13392step0 raw13392; decide +kernel
      have hl : raw13392step0Labels = raw13392Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13392 raw13392Labels permutation179 permutation2
    _ = mixedMoment B node5192 node5192Labels := by rfl

theorem canonical13393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13393 raw13393Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw13393 raw13393Labels = mixedMoment B raw13393step0 raw13393step0Labels := by
      have hz : ∀ j, raw13393 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13393step0 = (fun i j => raw13393 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13393step0 raw13393; decide +kernel
      have hl : raw13393step0Labels = raw13393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13393 raw13393Labels permutation520 hz
    mixedMoment B raw13393step0 raw13393step0Labels = mixedMoment B raw13393step1 raw13393step1Labels := by
      have ha : raw13393step1 = (fun i j => raw13393step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13393step1 raw13393step0; decide +kernel
      have hl : raw13393step1Labels = raw13393step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13393step0 raw13393step0Labels permutation33 permutation2
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical13394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13394 raw13394Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw13394 raw13394Labels = mixedMoment B raw13394step0 raw13394step0Labels := by
      have hz : ∀ j, raw13394 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13394step0 = (fun i j => raw13394 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13394step0 raw13394; decide +kernel
      have hl : raw13394step0Labels = raw13394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13394 raw13394Labels permutation590 hz
    mixedMoment B raw13394step0 raw13394step0Labels = mixedMoment B raw13394step1 raw13394step1Labels := by
      have ha : raw13394step1 = (fun i j => raw13394step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13394step1 raw13394step0; decide +kernel
      have hl : raw13394step1Labels = raw13394step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13394step0 raw13394step0Labels permutation33 permutation2
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical13395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13395 raw13395Labels = mixedMoment B node4581 node4581Labels := by
  calc
    mixedMoment B raw13395 raw13395Labels = mixedMoment B raw13395step0 raw13395step0Labels := by
      have ha : raw13395step0 = (fun i j => raw13395 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13395step0 raw13395; decide +kernel
      have hl : raw13395step0Labels = raw13395Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13395 raw13395Labels permutation153 permutation3
    mixedMoment B raw13395step0 raw13395step0Labels = mixedMoment B raw13395step1 raw13395step1Labels := by
      have ha : raw13395step1 = raw13395step0 := by apply Matrix.ext; unfold raw13395step1 raw13395step0; decide +kernel
      have hl : raw13395step0Labels = labelEmbedding6 ∘ raw13395step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13395step0 raw13395step0Labels raw13395step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4581 node4581Labels := by rfl

theorem canonical13396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13396 raw13396Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw13396 raw13396Labels = mixedMoment B raw13396step0 raw13396step0Labels := by
      have ha : raw13396step0 = (fun i j => raw13396 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13396step0 raw13396; decide +kernel
      have hl : raw13396step0Labels = raw13396Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13396 raw13396Labels permutation153 permutation2
    _ = mixedMoment B node5192 node5192Labels := by rfl

theorem canonical13397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13397 raw13397Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw13397 raw13397Labels = mixedMoment B raw13397step0 raw13397step0Labels := by
      have ha : raw13397step0 = (fun i j => raw13397 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13397step0 raw13397; decide +kernel
      have hl : raw13397step0Labels = raw13397Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13397 raw13397Labels permutation177 permutation2
    _ = mixedMoment B node5192 node5192Labels := by rfl

theorem canonical13398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13398 raw13398Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw13398 raw13398Labels = mixedMoment B raw13398step0 raw13398step0Labels := by
      have hz : ∀ j, raw13398 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13398step0 = (fun i j => raw13398 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13398step0 raw13398; decide +kernel
      have hl : raw13398step0Labels = raw13398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13398 raw13398Labels permutation434 hz
    mixedMoment B raw13398step0 raw13398step0Labels = mixedMoment B raw13398step1 raw13398step1Labels := by
      have ha : raw13398step1 = (fun i j => raw13398step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13398step1 raw13398step0; decide +kernel
      have hl : raw13398step1Labels = raw13398step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13398step0 raw13398step0Labels permutation33 permutation2
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical13399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13399 raw13399Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw13399 raw13399Labels = mixedMoment B raw13399step0 raw13399step0Labels := by
      have hz : ∀ j, raw13399 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13399step0 = (fun i j => raw13399 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13399step0 raw13399; decide +kernel
      have hl : raw13399step0Labels = raw13399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13399 raw13399Labels permutation590 hz
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical13400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13400 raw13400Labels = mixedMoment B node4581 node4581Labels := by
  calc
    mixedMoment B raw13400 raw13400Labels = mixedMoment B raw13400step0 raw13400step0Labels := by
      have ha : raw13400step0 = (fun i j => raw13400 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13400step0 raw13400; decide +kernel
      have hl : raw13400step0Labels = raw13400Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13400 raw13400Labels permutation152 permutation3
    mixedMoment B raw13400step0 raw13400step0Labels = mixedMoment B raw13400step1 raw13400step1Labels := by
      have ha : raw13400step1 = raw13400step0 := by apply Matrix.ext; unfold raw13400step1 raw13400step0; decide +kernel
      have hl : raw13400step0Labels = labelEmbedding6 ∘ raw13400step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13400step0 raw13400step0Labels raw13400step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4581 node4581Labels := by rfl

theorem canonical13401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13401 raw13401Labels = mixedMoment B node5192 node5192Labels := by
  calc
    _ = mixedMoment B node5192 node5192Labels := by rfl

theorem canonical13402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13402 raw13402Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw13402 raw13402Labels = mixedMoment B raw13402step0 raw13402step0Labels := by
      have ha : raw13402step0 = (fun i j => raw13402 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13402step0 raw13402; decide +kernel
      have hl : raw13402step0Labels = raw13402Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13402 raw13402Labels permutation176 permutation2
    _ = mixedMoment B node5192 node5192Labels := by rfl

theorem canonical13403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13403 raw13403Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw13403 raw13403Labels = mixedMoment B raw13403step0 raw13403step0Labels := by
      have hz : ∀ j, raw13403 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13403step0 = (fun i j => raw13403 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13403step0 raw13403; decide +kernel
      have hl : raw13403step0Labels = raw13403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13403 raw13403Labels permutation434 hz
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical13404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13404 raw13404Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw13404 raw13404Labels = mixedMoment B raw13404step0 raw13404step0Labels := by
      have hz : ∀ j, raw13404 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13404step0 = (fun i j => raw13404 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13404step0 raw13404; decide +kernel
      have hl : raw13404step0Labels = raw13404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13404 raw13404Labels permutation520 hz
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical13435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13435 raw13435Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw13435 raw13435Labels = mixedMoment B raw13435step0 raw13435step0Labels := by
      have hz : ∀ j, raw13435 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13435step0 = (fun i j => raw13435 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13435step0 raw13435; decide +kernel
      have hl : raw13435step0Labels = raw13435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13435 raw13435Labels permutation346 hz
    mixedMoment B raw13435step0 raw13435step0Labels = mixedMoment B raw13435step1 raw13435step1Labels := by
      have ha : raw13435step1 = (fun i j => raw13435step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13435step1 raw13435step0; decide +kernel
      have hl : raw13435step1Labels = raw13435step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13435step0 raw13435step0Labels permutation32 permutation7
    mixedMoment B raw13435step1 raw13435step1Labels = mixedMoment B raw13435step2 raw13435step2Labels := by
      have ha : raw13435step2 = raw13435step1 := by apply Matrix.ext; unfold raw13435step2 raw13435step1; decide +kernel
      have hl : raw13435step1Labels = labelEmbedding10 ∘ raw13435step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13435step1 raw13435step1Labels raw13435step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5273 node5273Labels := by rfl

theorem canonical13436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13436 raw13436Labels = mixedMoment B node5247 node5247Labels := by
  calc
    mixedMoment B raw13436 raw13436Labels = mixedMoment B raw13436step0 raw13436step0Labels := by
      have ha : raw13436step0 = (fun i j => raw13436 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13436step0 raw13436; decide +kernel
      have hl : raw13436step0Labels = raw13436Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13436 raw13436Labels permutation153 permutation7
    mixedMoment B raw13436step0 raw13436step0Labels = mixedMoment B raw13436step1 raw13436step1Labels := by
      have ha : raw13436step1 = raw13436step0 := by apply Matrix.ext; unfold raw13436step1 raw13436step0; decide +kernel
      have hl : raw13436step0Labels = labelEmbedding10 ∘ raw13436step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13436step0 raw13436step0Labels raw13436step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5247 node5247Labels := by rfl

theorem canonical13437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13437 raw13437Labels = mixedMoment B node5247 node5247Labels := by
  calc
    mixedMoment B raw13437 raw13437Labels = mixedMoment B raw13437step0 raw13437step0Labels := by
      have ha : raw13437step0 = (fun i j => raw13437 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13437step0 raw13437; decide +kernel
      have hl : raw13437step0Labels = raw13437Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13437 raw13437Labels permutation152 permutation7
    mixedMoment B raw13437step0 raw13437step0Labels = mixedMoment B raw13437step1 raw13437step1Labels := by
      have ha : raw13437step1 = raw13437step0 := by apply Matrix.ext; unfold raw13437step1 raw13437step0; decide +kernel
      have hl : raw13437step0Labels = labelEmbedding10 ∘ raw13437step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13437step0 raw13437step0Labels raw13437step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5247 node5247Labels := by rfl

theorem canonical13438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13438 raw13438Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw13438 raw13438Labels = mixedMoment B raw13438step0 raw13438step0Labels := by
      have ha : raw13438step0 = (fun i j => raw13438 (permutation217 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13438step0 raw13438; decide +kernel
      have hl : raw13438step0Labels = raw13438Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13438 raw13438Labels permutation217 permutation4
    mixedMoment B raw13438step0 raw13438step0Labels = mixedMoment B raw13438step1 raw13438step1Labels := by
      have ha : raw13438step1 = -raw13438step0 := by apply Matrix.ext; change ∀ i j, raw13438step1 i j = -(raw13438step0 i j); unfold raw13438step1 raw13438step0; decide +kernel
      have hl : raw13438step1Labels = raw13438step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13438step1 raw13438step1Labels = mixedMoment B raw13438step2 raw13438step2Labels := by
      have ha : raw13438step2 = raw13438step1 := by apply Matrix.ext; unfold raw13438step2 raw13438step1; decide +kernel
      have hl : raw13438step1Labels = labelEmbedding7 ∘ raw13438step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13438step1 raw13438step1Labels raw13438step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

theorem canonical13439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13439 raw13439Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw13439 raw13439Labels = mixedMoment B raw13439step0 raw13439step0Labels := by
      have hz : ∀ j, raw13439 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13439step0 = (fun i j => raw13439 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13439step0 raw13439; decide +kernel
      have hl : raw13439step0Labels = raw13439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13439 raw13439Labels permutation346 hz
    mixedMoment B raw13439step0 raw13439step0Labels = mixedMoment B raw13439step1 raw13439step1Labels := by
      have ha : raw13439step1 = (fun i j => raw13439step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13439step1 raw13439step0; decide +kernel
      have hl : raw13439step1Labels = raw13439step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13439step0 raw13439step0Labels permutation32 permutation6
    mixedMoment B raw13439step1 raw13439step1Labels = mixedMoment B raw13439step2 raw13439step2Labels := by
      have ha : raw13439step2 = raw13439step1 := by apply Matrix.ext; unfold raw13439step2 raw13439step1; decide +kernel
      have hl : raw13439step1Labels = labelEmbedding9 ∘ raw13439step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13439step1 raw13439step1Labels raw13439step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13440 raw13440Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw13440 raw13440Labels = mixedMoment B raw13440step0 raw13440step0Labels := by
      have ha : raw13440step0 = (fun i j => raw13440 (permutation178 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13440step0 raw13440; decide +kernel
      have hl : raw13440step0Labels = raw13440Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13440 raw13440Labels permutation178 permutation6
    mixedMoment B raw13440step0 raw13440step0Labels = mixedMoment B raw13440step1 raw13440step1Labels := by
      have ha : raw13440step1 = raw13440step0 := by apply Matrix.ext; unfold raw13440step1 raw13440step0; decide +kernel
      have hl : raw13440step0Labels = labelEmbedding9 ∘ raw13440step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13440step0 raw13440step0Labels raw13440step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

theorem canonical13441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13441 raw13441Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw13441 raw13441Labels = mixedMoment B raw13441step0 raw13441step0Labels := by
      have ha : raw13441step0 = (fun i j => raw13441 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13441step0 raw13441; decide +kernel
      have hl : raw13441step0Labels = raw13441Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13441 raw13441Labels permutation180 permutation6
    mixedMoment B raw13441step0 raw13441step0Labels = mixedMoment B raw13441step1 raw13441step1Labels := by
      have ha : raw13441step1 = raw13441step0 := by apply Matrix.ext; unfold raw13441step1 raw13441step0; decide +kernel
      have hl : raw13441step0Labels = labelEmbedding9 ∘ raw13441step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13441step0 raw13441step0Labels raw13441step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

theorem canonical13442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13442 raw13442Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw13442 raw13442Labels = mixedMoment B raw13442step0 raw13442step0Labels := by
      have ha : raw13442step0 = (fun i j => raw13442 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13442step0 raw13442; decide +kernel
      have hl : raw13442step0Labels = raw13442Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13442 raw13442Labels permutation240 permutation4
    mixedMoment B raw13442step0 raw13442step0Labels = mixedMoment B raw13442step1 raw13442step1Labels := by
      have ha : raw13442step1 = -raw13442step0 := by apply Matrix.ext; change ∀ i j, raw13442step1 i j = -(raw13442step0 i j); unfold raw13442step1 raw13442step0; decide +kernel
      have hl : raw13442step1Labels = raw13442step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13442step1 raw13442step1Labels = mixedMoment B raw13442step2 raw13442step2Labels := by
      have ha : raw13442step2 = raw13442step1 := by apply Matrix.ext; unfold raw13442step2 raw13442step1; decide +kernel
      have hl : raw13442step1Labels = labelEmbedding7 ∘ raw13442step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13442step1 raw13442step1Labels raw13442step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4887 node4887Labels := by rfl

theorem canonical13443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13443 raw13443Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw13443 raw13443Labels = mixedMoment B raw13443step0 raw13443step0Labels := by
      have hz : ∀ j, raw13443 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13443step0 = (fun i j => raw13443 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13443step0 raw13443; decide +kernel
      have hl : raw13443step0Labels = raw13443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13443 raw13443Labels permutation346 hz
    mixedMoment B raw13443step0 raw13443step0Labels = mixedMoment B raw13443step1 raw13443step1Labels := by
      have ha : raw13443step1 = (fun i j => raw13443step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13443step1 raw13443step0; decide +kernel
      have hl : raw13443step1Labels = raw13443step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13443step0 raw13443step0Labels permutation35 permutation6
    mixedMoment B raw13443step1 raw13443step1Labels = mixedMoment B raw13443step2 raw13443step2Labels := by
      have ha : raw13443step2 = raw13443step1 := by apply Matrix.ext; unfold raw13443step2 raw13443step1; decide +kernel
      have hl : raw13443step1Labels = labelEmbedding9 ∘ raw13443step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13443step1 raw13443step1Labels raw13443step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical13444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13444 raw13444Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw13444 raw13444Labels = mixedMoment B raw13444step0 raw13444step0Labels := by
      have ha : raw13444step0 = (fun i j => raw13444 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13444step0 raw13444; decide +kernel
      have hl : raw13444step0Labels = raw13444Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13444 raw13444Labels permutation155 permutation6
    mixedMoment B raw13444step0 raw13444step0Labels = mixedMoment B raw13444step1 raw13444step1Labels := by
      have ha : raw13444step1 = raw13444step0 := by apply Matrix.ext; unfold raw13444step1 raw13444step0; decide +kernel
      have hl : raw13444step0Labels = labelEmbedding9 ∘ raw13444step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13444step0 raw13444step0Labels raw13444step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical13445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13445 raw13445Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw13445 raw13445Labels = mixedMoment B raw13445step0 raw13445step0Labels := by
      have ha : raw13445step0 = (fun i j => raw13445 (permutation157 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13445step0 raw13445; decide +kernel
      have hl : raw13445step0Labels = raw13445Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13445 raw13445Labels permutation157 permutation6
    mixedMoment B raw13445step0 raw13445step0Labels = mixedMoment B raw13445step1 raw13445step1Labels := by
      have ha : raw13445step1 = raw13445step0 := by apply Matrix.ext; unfold raw13445step1 raw13445step0; decide +kernel
      have hl : raw13445step0Labels = labelEmbedding9 ∘ raw13445step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13445step0 raw13445step0Labels raw13445step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical13446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13446 raw13446Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw13446 raw13446Labels = mixedMoment B raw13446step0 raw13446step0Labels := by
      have ha : raw13446step0 = (fun i j => raw13446 (permutation218 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13446step0 raw13446; decide +kernel
      have hl : raw13446step0Labels = raw13446Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13446 raw13446Labels permutation218 permutation4
    mixedMoment B raw13446step0 raw13446step0Labels = mixedMoment B raw13446step1 raw13446step1Labels := by
      have ha : raw13446step1 = -raw13446step0 := by apply Matrix.ext; change ∀ i j, raw13446step1 i j = -(raw13446step0 i j); unfold raw13446step1 raw13446step0; decide +kernel
      have hl : raw13446step1Labels = raw13446step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13446step1 raw13446step1Labels = mixedMoment B raw13446step2 raw13446step2Labels := by
      have ha : raw13446step2 = raw13446step1 := by apply Matrix.ext; unfold raw13446step2 raw13446step1; decide +kernel
      have hl : raw13446step1Labels = labelEmbedding7 ∘ raw13446step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13446step1 raw13446step1Labels raw13446step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4887 node4887Labels := by rfl

theorem canonical13447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13447 raw13447Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw13447 raw13447Labels = mixedMoment B raw13447step0 raw13447step0Labels := by
      have hz : ∀ j, raw13447 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13447step0 = (fun i j => raw13447 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13447step0 raw13447; decide +kernel
      have hl : raw13447step0Labels = raw13447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13447 raw13447Labels permutation346 hz
    mixedMoment B raw13447step0 raw13447step0Labels = mixedMoment B raw13447step1 raw13447step1Labels := by
      have ha : raw13447step1 = (fun i j => raw13447step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13447step1 raw13447step0; decide +kernel
      have hl : raw13447step1Labels = raw13447step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13447step0 raw13447step0Labels permutation33 permutation6
    mixedMoment B raw13447step1 raw13447step1Labels = mixedMoment B raw13447step2 raw13447step2Labels := by
      have ha : raw13447step2 = raw13447step1 := by apply Matrix.ext; unfold raw13447step2 raw13447step1; decide +kernel
      have hl : raw13447step1Labels = labelEmbedding9 ∘ raw13447step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13447step1 raw13447step1Labels raw13447step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical13448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13448 raw13448Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw13448 raw13448Labels = mixedMoment B raw13448step0 raw13448step0Labels := by
      have ha : raw13448step0 = (fun i j => raw13448 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13448step0 raw13448; decide +kernel
      have hl : raw13448step0Labels = raw13448Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13448 raw13448Labels permutation156 permutation6
    mixedMoment B raw13448step0 raw13448step0Labels = mixedMoment B raw13448step1 raw13448step1Labels := by
      have ha : raw13448step1 = raw13448step0 := by apply Matrix.ext; unfold raw13448step1 raw13448step0; decide +kernel
      have hl : raw13448step0Labels = labelEmbedding9 ∘ raw13448step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13448step0 raw13448step0Labels raw13448step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical13449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13449 raw13449Labels = mixedMoment B node2741 node2741Labels := by
  calc
    mixedMoment B raw13449 raw13449Labels = mixedMoment B raw13449step0 raw13449step0Labels := by
      have hz : ∀ j, raw13449 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13449step0 = (fun i j => raw13449 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13449step0 raw13449; decide +kernel
      have hl : raw13449step0Labels = raw13449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13449 raw13449Labels permutation346 hz
    mixedMoment B raw13449step0 raw13449step0Labels = mixedMoment B raw13449step1 raw13449step1Labels := by
      have ha : raw13449step1 = (fun i j => raw13449step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13449step1 raw13449step0; decide +kernel
      have hl : raw13449step1Labels = raw13449step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13449step0 raw13449step0Labels permutation32 permutation7
    mixedMoment B raw13449step1 raw13449step1Labels = mixedMoment B raw13449step2 raw13449step2Labels := by
      have ha : raw13449step2 = raw13449step1 := by apply Matrix.ext; unfold raw13449step2 raw13449step1; decide +kernel
      have hl : raw13449step1Labels = labelEmbedding1 ∘ raw13449step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13449step1 raw13449step1Labels raw13449step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2741 node2741Labels := by rfl

theorem canonical13450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13450 raw13450Labels = mixedMoment B node2703 node2703Labels := by
  calc
    mixedMoment B raw13450 raw13450Labels = mixedMoment B raw13450step0 raw13450step0Labels := by
      have ha : raw13450step0 = (fun i j => raw13450 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13450step0 raw13450; decide +kernel
      have hl : raw13450step0Labels = raw13450Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13450 raw13450Labels permutation153 permutation7
    mixedMoment B raw13450step0 raw13450step0Labels = mixedMoment B raw13450step1 raw13450step1Labels := by
      have ha : raw13450step1 = raw13450step0 := by apply Matrix.ext; unfold raw13450step1 raw13450step0; decide +kernel
      have hl : raw13450step0Labels = labelEmbedding1 ∘ raw13450step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13450step0 raw13450step0Labels raw13450step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2703 node2703Labels := by rfl

theorem canonical13451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13451 raw13451Labels = mixedMoment B node2703 node2703Labels := by
  calc
    mixedMoment B raw13451 raw13451Labels = mixedMoment B raw13451step0 raw13451step0Labels := by
      have ha : raw13451step0 = (fun i j => raw13451 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13451step0 raw13451; decide +kernel
      have hl : raw13451step0Labels = raw13451Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13451 raw13451Labels permutation152 permutation7
    mixedMoment B raw13451step0 raw13451step0Labels = mixedMoment B raw13451step1 raw13451step1Labels := by
      have ha : raw13451step1 = raw13451step0 := by apply Matrix.ext; unfold raw13451step1 raw13451step0; decide +kernel
      have hl : raw13451step0Labels = labelEmbedding1 ∘ raw13451step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13451step0 raw13451step0Labels raw13451step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2703 node2703Labels := by rfl

theorem canonical13452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13452 raw13452Labels = mixedMoment B node3221 node3221Labels := by
  calc
    mixedMoment B raw13452 raw13452Labels = mixedMoment B raw13452step0 raw13452step0Labels := by
      have ha : raw13452step0 = (fun i j => raw13452 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13452step0 raw13452; decide +kernel
      have hl : raw13452step0Labels = raw13452Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13452 raw13452Labels permutation152 permutation7
    mixedMoment B raw13452step0 raw13452step0Labels = mixedMoment B raw13452step1 raw13452step1Labels := by
      have ha : raw13452step1 = raw13452step0 := by apply Matrix.ext; unfold raw13452step1 raw13452step0; decide +kernel
      have hl : raw13452step0Labels = labelEmbedding1 ∘ raw13452step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13452step0 raw13452step0Labels raw13452step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3221 node3221Labels := by rfl

theorem canonical13453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13453 raw13453Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw13453 raw13453Labels = mixedMoment B raw13453step0 raw13453step0Labels := by
      have hz : ∀ j, raw13453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13453step0 = (fun i j => raw13453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13453step0 raw13453; decide +kernel
      have hl : raw13453step0Labels = raw13453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13453 raw13453Labels permutation346 hz
    mixedMoment B raw13453step0 raw13453step0Labels = mixedMoment B raw13453step1 raw13453step1Labels := by
      have ha : raw13453step1 = (fun i j => raw13453step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13453step1 raw13453step0; decide +kernel
      have hl : raw13453step1Labels = raw13453step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13453step0 raw13453step0Labels permutation32 permutation7
    mixedMoment B raw13453step1 raw13453step1Labels = mixedMoment B raw13453step2 raw13453step2Labels := by
      have ha : raw13453step2 = raw13453step1 := by apply Matrix.ext; unfold raw13453step2 raw13453step1; decide +kernel
      have hl : raw13453step1Labels = labelEmbedding1 ∘ raw13453step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13453step1 raw13453step1Labels raw13453step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3053 node3053Labels := by rfl

theorem canonical13454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13454 raw13454Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw13454 raw13454Labels = mixedMoment B raw13454step0 raw13454step0Labels := by
      have ha : raw13454step0 = (fun i j => raw13454 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13454step0 raw13454; decide +kernel
      have hl : raw13454step0Labels = raw13454Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13454 raw13454Labels permutation153 permutation7
    mixedMoment B raw13454step0 raw13454step0Labels = mixedMoment B raw13454step1 raw13454step1Labels := by
      have ha : raw13454step1 = raw13454step0 := by apply Matrix.ext; unfold raw13454step1 raw13454step0; decide +kernel
      have hl : raw13454step0Labels = labelEmbedding1 ∘ raw13454step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13454step0 raw13454step0Labels raw13454step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3023 node3023Labels := by rfl

theorem canonical13455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13455 raw13455Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw13455 raw13455Labels = mixedMoment B raw13455step0 raw13455step0Labels := by
      have ha : raw13455step0 = (fun i j => raw13455 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13455step0 raw13455; decide +kernel
      have hl : raw13455step0Labels = raw13455Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13455 raw13455Labels permutation152 permutation7
    mixedMoment B raw13455step0 raw13455step0Labels = mixedMoment B raw13455step1 raw13455step1Labels := by
      have ha : raw13455step1 = raw13455step0 := by apply Matrix.ext; unfold raw13455step1 raw13455step0; decide +kernel
      have hl : raw13455step0Labels = labelEmbedding1 ∘ raw13455step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13455step0 raw13455step0Labels raw13455step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3023 node3023Labels := by rfl

theorem canonical13456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13456 raw13456Labels = mixedMoment B node3226 node3226Labels := by
  calc
    mixedMoment B raw13456 raw13456Labels = mixedMoment B raw13456step0 raw13456step0Labels := by
      have ha : raw13456step0 = (fun i j => raw13456 (permutation244 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13456step0 raw13456; decide +kernel
      have hl : raw13456step0Labels = raw13456Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13456 raw13456Labels permutation244 permutation5
    mixedMoment B raw13456step0 raw13456step0Labels = mixedMoment B raw13456step1 raw13456step1Labels := by
      have ha : raw13456step1 = -raw13456step0 := by apply Matrix.ext; change ∀ i j, raw13456step1 i j = -(raw13456step0 i j); unfold raw13456step1 raw13456step0; decide +kernel
      have hl : raw13456step1Labels = raw13456step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13456step1 raw13456step1Labels = mixedMoment B raw13456step2 raw13456step2Labels := by
      have ha : raw13456step2 = raw13456step1 := by apply Matrix.ext; unfold raw13456step2 raw13456step1; decide +kernel
      have hl : raw13456step1Labels = labelEmbedding1 ∘ raw13456step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13456step1 raw13456step1Labels raw13456step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3226 node3226Labels := by rfl

theorem canonical13457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13457 raw13457Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw13457 raw13457Labels = mixedMoment B raw13457step0 raw13457step0Labels := by
      have hz : ∀ j, raw13457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13457step0 = (fun i j => raw13457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13457step0 raw13457; decide +kernel
      have hl : raw13457step0Labels = raw13457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13457 raw13457Labels permutation346 hz
    mixedMoment B raw13457step0 raw13457step0Labels = mixedMoment B raw13457step1 raw13457step1Labels := by
      have ha : raw13457step1 = (fun i j => raw13457step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13457step1 raw13457step0; decide +kernel
      have hl : raw13457step1Labels = raw13457step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13457step0 raw13457step0Labels permutation32 permutation7
    mixedMoment B raw13457step1 raw13457step1Labels = mixedMoment B raw13457step2 raw13457step2Labels := by
      have ha : raw13457step2 = raw13457step1 := by apply Matrix.ext; unfold raw13457step2 raw13457step1; decide +kernel
      have hl : raw13457step1Labels = labelEmbedding1 ∘ raw13457step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13457step1 raw13457step1Labels raw13457step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3100 node3100Labels := by rfl

theorem canonical13458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13458 raw13458Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw13458 raw13458Labels = mixedMoment B raw13458step0 raw13458step0Labels := by
      have ha : raw13458step0 = (fun i j => raw13458 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13458step0 raw13458; decide +kernel
      have hl : raw13458step0Labels = raw13458Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13458 raw13458Labels permutation153 permutation7
    mixedMoment B raw13458step0 raw13458step0Labels = mixedMoment B raw13458step1 raw13458step1Labels := by
      have ha : raw13458step1 = raw13458step0 := by apply Matrix.ext; unfold raw13458step1 raw13458step0; decide +kernel
      have hl : raw13458step0Labels = labelEmbedding1 ∘ raw13458step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13458step0 raw13458step0Labels raw13458step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

theorem canonical13459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13459 raw13459Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw13459 raw13459Labels = mixedMoment B raw13459step0 raw13459step0Labels := by
      have ha : raw13459step0 = (fun i j => raw13459 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13459step0 raw13459; decide +kernel
      have hl : raw13459step0Labels = raw13459Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13459 raw13459Labels permutation152 permutation7
    mixedMoment B raw13459step0 raw13459step0Labels = mixedMoment B raw13459step1 raw13459step1Labels := by
      have ha : raw13459step1 = raw13459step0 := by apply Matrix.ext; unfold raw13459step1 raw13459step0; decide +kernel
      have hl : raw13459step0Labels = labelEmbedding1 ∘ raw13459step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13459step0 raw13459step0Labels raw13459step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

theorem canonical13460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13460 raw13460Labels = mixedMoment B node3226 node3226Labels := by
  calc
    mixedMoment B raw13460 raw13460Labels = mixedMoment B raw13460step0 raw13460step0Labels := by
      have ha : raw13460step0 = (fun i j => raw13460 (permutation222 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13460step0 raw13460; decide +kernel
      have hl : raw13460step0Labels = raw13460Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13460 raw13460Labels permutation222 permutation5
    mixedMoment B raw13460step0 raw13460step0Labels = mixedMoment B raw13460step1 raw13460step1Labels := by
      have ha : raw13460step1 = -raw13460step0 := by apply Matrix.ext; change ∀ i j, raw13460step1 i j = -(raw13460step0 i j); unfold raw13460step1 raw13460step0; decide +kernel
      have hl : raw13460step1Labels = raw13460step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13460step1 raw13460step1Labels = mixedMoment B raw13460step2 raw13460step2Labels := by
      have ha : raw13460step2 = raw13460step1 := by apply Matrix.ext; unfold raw13460step2 raw13460step1; decide +kernel
      have hl : raw13460step1Labels = labelEmbedding1 ∘ raw13460step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13460step1 raw13460step1Labels raw13460step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3226 node3226Labels := by rfl

theorem canonical13461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13461 raw13461Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw13461 raw13461Labels = mixedMoment B raw13461step0 raw13461step0Labels := by
      have hz : ∀ j, raw13461 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13461step0 = (fun i j => raw13461 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13461step0 raw13461; decide +kernel
      have hl : raw13461step0Labels = raw13461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13461 raw13461Labels permutation346 hz
    mixedMoment B raw13461step0 raw13461step0Labels = mixedMoment B raw13461step1 raw13461step1Labels := by
      have ha : raw13461step1 = (fun i j => raw13461step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13461step1 raw13461step0; decide +kernel
      have hl : raw13461step1Labels = raw13461step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13461step0 raw13461step0Labels permutation34 permutation7
    mixedMoment B raw13461step1 raw13461step1Labels = mixedMoment B raw13461step2 raw13461step2Labels := by
      have ha : raw13461step2 = raw13461step1 := by apply Matrix.ext; unfold raw13461step2 raw13461step1; decide +kernel
      have hl : raw13461step1Labels = labelEmbedding1 ∘ raw13461step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13461step1 raw13461step1Labels raw13461step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3100 node3100Labels := by rfl

theorem canonical13462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13462 raw13462Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw13462 raw13462Labels = mixedMoment B raw13462step0 raw13462step0Labels := by
      have ha : raw13462step0 = (fun i j => raw13462 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13462step0 raw13462; decide +kernel
      have hl : raw13462step0Labels = raw13462Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13462 raw13462Labels permutation154 permutation7
    mixedMoment B raw13462step0 raw13462step0Labels = mixedMoment B raw13462step1 raw13462step1Labels := by
      have ha : raw13462step1 = raw13462step0 := by apply Matrix.ext; unfold raw13462step1 raw13462step0; decide +kernel
      have hl : raw13462step0Labels = labelEmbedding1 ∘ raw13462step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13462step0 raw13462step0Labels raw13462step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

theorem canonical13553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13553 raw13553Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw13553 raw13553Labels = mixedMoment B raw13553step0 raw13553step0Labels := by
      have hz : ∀ j, raw13553 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13553step0 = (fun i j => raw13553 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13553step0 raw13553; decide +kernel
      have hl : raw13553step0Labels = raw13553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13553 raw13553Labels permutation346 hz
    mixedMoment B raw13553step0 raw13553step0Labels = mixedMoment B raw13553step1 raw13553step1Labels := by
      have ha : raw13553step1 = (fun i j => raw13553step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13553step1 raw13553step0; decide +kernel
      have hl : raw13553step1Labels = raw13553step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13553step0 raw13553step0Labels permutation36 permutation2
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical13554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13554 raw13554Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw13554 raw13554Labels = mixedMoment B raw13554step0 raw13554step0Labels := by
      have hz : ∀ j, raw13554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13554step0 = (fun i j => raw13554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13554step0 raw13554; decide +kernel
      have hl : raw13554step0Labels = raw13554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13554 raw13554Labels permutation346 hz
    mixedMoment B raw13554step0 raw13554step0Labels = mixedMoment B raw13554step1 raw13554step1Labels := by
      have ha : raw13554step1 = (fun i j => raw13554step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13554step1 raw13554step0; decide +kernel
      have hl : raw13554step1Labels = raw13554step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13554step0 raw13554step0Labels permutation36 permutation2
    _ = mixedMoment B node3885 node3885Labels := by rfl

theorem canonical13555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13555 raw13555Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw13555 raw13555Labels = mixedMoment B raw13555step0 raw13555step0Labels := by
      have ha : raw13555step0 = (fun i j => raw13555 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13555step0 raw13555; decide +kernel
      have hl : raw13555step0Labels = raw13555Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13555 raw13555Labels permutation180 permutation2
    _ = mixedMoment B node3849 node3849Labels := by rfl

theorem canonical13556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13556 raw13556Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw13556 raw13556Labels = mixedMoment B raw13556step0 raw13556step0Labels := by
      have hz : ∀ j, raw13556 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13556step0 = (fun i j => raw13556 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13556step0 raw13556; decide +kernel
      have hl : raw13556step0Labels = raw13556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13556 raw13556Labels permutation346 hz
    mixedMoment B raw13556step0 raw13556step0Labels = mixedMoment B raw13556step1 raw13556step1Labels := by
      have ha : raw13556step1 = (fun i j => raw13556step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13556step1 raw13556step0; decide +kernel
      have hl : raw13556step1Labels = raw13556step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13556step0 raw13556step0Labels permutation33 permutation2
    _ = mixedMoment B node3910 node3910Labels := by rfl

theorem canonical13557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13557 raw13557Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw13557 raw13557Labels = mixedMoment B raw13557step0 raw13557step0Labels := by
      have hz : ∀ j, raw13557 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13557step0 = (fun i j => raw13557 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13557step0 raw13557; decide +kernel
      have hl : raw13557step0Labels = raw13557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13557 raw13557Labels permutation346 hz
    mixedMoment B raw13557step0 raw13557step0Labels = mixedMoment B raw13557step1 raw13557step1Labels := by
      have ha : raw13557step1 = (fun i j => raw13557step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13557step1 raw13557step0; decide +kernel
      have hl : raw13557step1Labels = raw13557step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13557step0 raw13557step0Labels permutation35 permutation2
    _ = mixedMoment B node3910 node3910Labels := by rfl

theorem canonical13558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13558 raw13558Labels = mixedMoment B node3904 node3904Labels := by
  calc
    mixedMoment B raw13558 raw13558Labels = mixedMoment B raw13558step0 raw13558step0Labels := by
      have hz : ∀ j, raw13558 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13558step0 = (fun i j => raw13558 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13558step0 raw13558; decide +kernel
      have hl : raw13558step0Labels = raw13558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13558 raw13558Labels permutation346 hz
    mixedMoment B raw13558step0 raw13558step0Labels = mixedMoment B raw13558step1 raw13558step1Labels := by
      have ha : raw13558step1 = (fun i j => raw13558step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13558step1 raw13558step0; decide +kernel
      have hl : raw13558step1Labels = raw13558step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13558step0 raw13558step0Labels permutation50 permutation2
    _ = mixedMoment B node3904 node3904Labels := by rfl

theorem canonical13559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13559 raw13559Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw13559 raw13559Labels = mixedMoment B raw13559step0 raw13559step0Labels := by
      have hz : ∀ j, raw13559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13559step0 = (fun i j => raw13559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13559step0 raw13559; decide +kernel
      have hl : raw13559step0Labels = raw13559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13559 raw13559Labels permutation346 hz
    mixedMoment B raw13559step0 raw13559step0Labels = mixedMoment B raw13559step1 raw13559step1Labels := by
      have ha : raw13559step1 = (fun i j => raw13559step0 (permutation50 i) (permutation0 j)) := by apply Matrix.ext; unfold raw13559step1 raw13559step0; decide +kernel
      have hl : raw13559step1Labels = raw13559step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13559step0 raw13559step0Labels permutation50 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical13560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13560 raw13560Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw13560 raw13560Labels = mixedMoment B raw13560step0 raw13560step0Labels := by
      have hz : ∀ j, raw13560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13560step0 = (fun i j => raw13560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13560step0 raw13560; decide +kernel
      have hl : raw13560step0Labels = raw13560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13560 raw13560Labels permutation346 hz
    mixedMoment B raw13560step0 raw13560step0Labels = mixedMoment B raw13560step1 raw13560step1Labels := by
      have ha : raw13560step1 = (fun i j => raw13560step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13560step1 raw13560step0; decide +kernel
      have hl : raw13560step1Labels = raw13560step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13560step0 raw13560step0Labels permutation50 permutation2
    _ = mixedMoment B node1293 node1293Labels := by rfl

theorem canonical13561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13561 raw13561Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw13561 raw13561Labels = mixedMoment B raw13561step0 raw13561step0Labels := by
      have ha : raw13561step0 = (fun i j => raw13561 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13561step0 raw13561; decide +kernel
      have hl : raw13561step0Labels = raw13561Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13561 raw13561Labels permutation170 permutation2
    _ = mixedMoment B node1260 node1260Labels := by rfl

theorem canonical13562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13562 raw13562Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw13562 raw13562Labels = mixedMoment B raw13562step0 raw13562step0Labels := by
      have hz : ∀ j, raw13562 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13562step0 = (fun i j => raw13562 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13562step0 raw13562; decide +kernel
      have hl : raw13562step0Labels = raw13562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13562 raw13562Labels permutation346 hz
    mixedMoment B raw13562step0 raw13562step0Labels = mixedMoment B raw13562step1 raw13562step1Labels := by
      have ha : raw13562step1 = (fun i j => raw13562step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13562step1 raw13562step0; decide +kernel
      have hl : raw13562step1Labels = raw13562step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13562step0 raw13562step0Labels permutation37 permutation2
    _ = mixedMoment B node1262 node1262Labels := by rfl

theorem canonical13563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13563 raw13563Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw13563 raw13563Labels = mixedMoment B raw13563step0 raw13563step0Labels := by
      have hz : ∀ j, raw13563 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13563step0 = (fun i j => raw13563 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13563step0 raw13563; decide +kernel
      have hl : raw13563step0Labels = raw13563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13563 raw13563Labels permutation346 hz
    mixedMoment B raw13563step0 raw13563step0Labels = mixedMoment B raw13563step1 raw13563step1Labels := by
      have ha : raw13563step1 = (fun i j => raw13563step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13563step1 raw13563step0; decide +kernel
      have hl : raw13563step1Labels = raw13563step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13563step0 raw13563step0Labels permutation36 permutation2
    _ = mixedMoment B node1262 node1262Labels := by rfl

theorem canonical13564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13564 raw13564Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw13564 raw13564Labels = mixedMoment B raw13564step0 raw13564step0Labels := by
      have hz : ∀ j, raw13564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13564step0 = (fun i j => raw13564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13564step0 raw13564; decide +kernel
      have hl : raw13564step0Labels = raw13564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13564 raw13564Labels permutation346 hz
    _ = mixedMoment B node1270 node1270Labels := by rfl

theorem canonical13565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13565 raw13565Labels = mixedMoment B node2589 node2589Labels := by
  calc
    mixedMoment B raw13565 raw13565Labels = mixedMoment B raw13565step0 raw13565step0Labels := by
      have ha : raw13565step0 = (fun i j => raw13565 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13565step0 raw13565; decide +kernel
      have hl : raw13565step0Labels = raw13565Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13565 raw13565Labels permutation194 permutation2
    _ = mixedMoment B node2589 node2589Labels := by rfl

theorem canonical13566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13566 raw13566Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw13566 raw13566Labels = mixedMoment B raw13566step0 raw13566step0Labels := by
      have hz : ∀ j, raw13566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13566step0 = (fun i j => raw13566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13566step0 raw13566; decide +kernel
      have hl : raw13566step0Labels = raw13566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13566 raw13566Labels permutation346 hz
    mixedMoment B raw13566step0 raw13566step0Labels = mixedMoment B raw13566step1 raw13566step1Labels := by
      have ha : raw13566step1 = (fun i j => raw13566step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13566step1 raw13566step0; decide +kernel
      have hl : raw13566step1Labels = raw13566step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13566step0 raw13566step0Labels permutation42 permutation2
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical13567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13567 raw13567Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw13567 raw13567Labels = mixedMoment B raw13567step0 raw13567step0Labels := by
      have hz : ∀ j, raw13567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13567step0 = (fun i j => raw13567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13567step0 raw13567; decide +kernel
      have hl : raw13567step0Labels = raw13567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13567 raw13567Labels permutation346 hz
    mixedMoment B raw13567step0 raw13567step0Labels = mixedMoment B raw13567step1 raw13567step1Labels := by
      have ha : raw13567step1 = (fun i j => raw13567step0 (permutation48 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13567step1 raw13567step0; decide +kernel
      have hl : raw13567step1Labels = raw13567step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13567step0 raw13567step0Labels permutation48 permutation2
    _ = mixedMoment B node2764 node2764Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13568 raw13568Labels = mixedMoment B node2741 node2741Labels := by
  calc
    mixedMoment B raw13568 raw13568Labels = mixedMoment B raw13568step0 raw13568step0Labels := by
      have hz : ∀ j, raw13568 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13568step0 = (fun i j => raw13568 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13568step0 raw13568; decide +kernel
      have hl : raw13568step0Labels = raw13568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13568 raw13568Labels permutation346 hz
    mixedMoment B raw13568step0 raw13568step0Labels = mixedMoment B raw13568step1 raw13568step1Labels := by
      have ha : raw13568step1 = (fun i j => raw13568step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13568step1 raw13568step0; decide +kernel
      have hl : raw13568step1Labels = raw13568step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13568step0 raw13568step0Labels permutation50 permutation2
    _ = mixedMoment B node2741 node2741Labels := by rfl

theorem canonical13569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13569 raw13569Labels = mixedMoment B node2631 node2631Labels := by
  calc
    mixedMoment B raw13569 raw13569Labels = mixedMoment B raw13569step0 raw13569step0Labels := by
      have ha : raw13569step0 = (fun i j => raw13569 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13569step0 raw13569; decide +kernel
      have hl : raw13569step0Labels = raw13569Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13569 raw13569Labels permutation170 permutation2
    _ = mixedMoment B node2631 node2631Labels := by rfl

theorem canonical13570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13570 raw13570Labels = mixedMoment B node2633 node2633Labels := by
  calc
    mixedMoment B raw13570 raw13570Labels = mixedMoment B raw13570step0 raw13570step0Labels := by
      have hz : ∀ j, raw13570 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13570step0 = (fun i j => raw13570 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13570step0 raw13570; decide +kernel
      have hl : raw13570step0Labels = raw13570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13570 raw13570Labels permutation346 hz
    mixedMoment B raw13570step0 raw13570step0Labels = mixedMoment B raw13570step1 raw13570step1Labels := by
      have ha : raw13570step1 = (fun i j => raw13570step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13570step1 raw13570step0; decide +kernel
      have hl : raw13570step1Labels = raw13570step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13570step0 raw13570step0Labels permutation37 permutation2
    _ = mixedMoment B node2633 node2633Labels := by rfl

theorem canonical13571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13571 raw13571Labels = mixedMoment B node2633 node2633Labels := by
  calc
    mixedMoment B raw13571 raw13571Labels = mixedMoment B raw13571step0 raw13571step0Labels := by
      have hz : ∀ j, raw13571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13571step0 = (fun i j => raw13571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13571step0 raw13571; decide +kernel
      have hl : raw13571step0Labels = raw13571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13571 raw13571Labels permutation346 hz
    mixedMoment B raw13571step0 raw13571step0Labels = mixedMoment B raw13571step1 raw13571step1Labels := by
      have ha : raw13571step1 = (fun i j => raw13571step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13571step1 raw13571step0; decide +kernel
      have hl : raw13571step1Labels = raw13571step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13571step0 raw13571step0Labels permutation36 permutation2
    _ = mixedMoment B node2633 node2633Labels := by rfl

theorem canonical13572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13572 raw13572Labels = mixedMoment B node2641 node2641Labels := by
  calc
    mixedMoment B raw13572 raw13572Labels = mixedMoment B raw13572step0 raw13572step0Labels := by
      have hz : ∀ j, raw13572 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13572step0 = (fun i j => raw13572 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13572step0 raw13572; decide +kernel
      have hl : raw13572step0Labels = raw13572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13572 raw13572Labels permutation346 hz
    _ = mixedMoment B node2641 node2641Labels := by rfl

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

theorem canonical1413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1413 raw1413Labels = mixedMoment B node4581 node4581Labels := by
  calc
    mixedMoment B raw1413 raw1413Labels = mixedMoment B raw1413step0 raw1413step0Labels := by
      have ha : raw1413step0 = (fun i j => raw1413 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1413step0 raw1413; decide +kernel
      have hl : raw1413step0Labels = raw1413Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1413 raw1413Labels permutation152 permutation4
    mixedMoment B raw1413step0 raw1413step0Labels = mixedMoment B raw1413step1 raw1413step1Labels := by
      have ha : raw1413step1 = raw1413step0 := by apply Matrix.ext; unfold raw1413step1 raw1413step0; decide +kernel
      have hl : raw1413step0Labels = labelEmbedding7 ∘ raw1413step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1413step0 raw1413step0Labels raw1413step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4581 node4581Labels := by rfl

theorem canonical1414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1414 raw1414Labels = mixedMoment B node1200 node1200Labels := by
  calc
    mixedMoment B raw1414 raw1414Labels = mixedMoment B raw1414step0 raw1414step0Labels := by
      have ha : raw1414step0 = (fun i j => raw1414 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1414step0 raw1414; decide +kernel
      have hl : raw1414step0Labels = raw1414Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1414 raw1414Labels permutation152 permutation4
    _ = mixedMoment B node1200 node1200Labels := by rfl

theorem canonical1415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1415 raw1415Labels = mixedMoment B node3281 node3281Labels := by
  calc
    mixedMoment B raw1415 raw1415Labels = mixedMoment B raw1415step0 raw1415step0Labels := by
      have ha : raw1415step0 = (fun i j => raw1415 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1415step0 raw1415; decide +kernel
      have hl : raw1415step0Labels = raw1415Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1415 raw1415Labels permutation152 permutation6
    mixedMoment B raw1415step0 raw1415step0Labels = mixedMoment B raw1415step1 raw1415step1Labels := by
      have ha : raw1415step1 = -raw1415step0 := by apply Matrix.ext; change ∀ i j, raw1415step1 i j = -(raw1415step0 i j); unfold raw1415step1 raw1415step0; decide +kernel
      have hl : raw1415step1Labels = raw1415step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1415step1 raw1415step1Labels = mixedMoment B raw1415step2 raw1415step2Labels := by
      have ha : raw1415step2 = raw1415step1 := by apply Matrix.ext; unfold raw1415step2 raw1415step1; decide +kernel
      have hl : raw1415step1Labels = labelEmbedding1 ∘ raw1415step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1415step1 raw1415step1Labels raw1415step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3281 node3281Labels := by rfl

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

theorem canonical1812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1812 raw1812Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw1812 raw1812Labels = mixedMoment B raw1812step0 raw1812step0Labels := by
      have ha : raw1812step0 = (fun i j => raw1812 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1812step0 raw1812; decide +kernel
      have hl : raw1812step0Labels = raw1812Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1812 raw1812Labels permutation152 permutation4
    mixedMoment B raw1812step0 raw1812step0Labels = mixedMoment B raw1812step1 raw1812step1Labels := by
      have ha : raw1812step1 = raw1812step0 := by apply Matrix.ext; unfold raw1812step1 raw1812step0; decide +kernel
      have hl : raw1812step0Labels = labelEmbedding7 ∘ raw1812step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1812step0 raw1812step0Labels raw1812step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4887 node4887Labels := by rfl

theorem canonical1813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1813 raw1813Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw1813 raw1813Labels = mixedMoment B raw1813step0 raw1813step0Labels := by
      have ha : raw1813step0 = (fun i j => raw1813 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1813step0 raw1813; decide +kernel
      have hl : raw1813step0Labels = raw1813Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1813 raw1813Labels permutation152 permutation4
    _ = mixedMoment B node2243 node2243Labels := by rfl

theorem canonical1814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1814 raw1814Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw1814 raw1814Labels = mixedMoment B raw1814step0 raw1814step0Labels := by
      have ha : raw1814step0 = (fun i j => raw1814 (permutation212 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1814step0 raw1814; decide +kernel
      have hl : raw1814step0Labels = raw1814Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1814 raw1814Labels permutation212 permutation6
    mixedMoment B raw1814step0 raw1814step0Labels = mixedMoment B raw1814step1 raw1814step1Labels := by
      have ha : raw1814step1 = -raw1814step0 := by apply Matrix.ext; change ∀ i j, raw1814step1 i j = -(raw1814step0 i j); unfold raw1814step1 raw1814step0; decide +kernel
      have hl : raw1814step1Labels = raw1814step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1814step1 raw1814step1Labels = mixedMoment B raw1814step2 raw1814step2Labels := by
      have ha : raw1814step2 = raw1814step1 := by apply Matrix.ext; unfold raw1814step2 raw1814step1; decide +kernel
      have hl : raw1814step1Labels = labelEmbedding1 ∘ raw1814step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1814step1 raw1814step1Labels raw1814step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2243 node2243Labels := by rfl

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

theorem canonical2220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2220 raw2220Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw2220 raw2220Labels = mixedMoment B raw2220step0 raw2220step0Labels := by
      have ha : raw2220step0 = (fun i j => raw2220 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2220step0 raw2220; decide +kernel
      have hl : raw2220step0Labels = raw2220Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2220 raw2220Labels permutation152 permutation5
    mixedMoment B raw2220step0 raw2220step0Labels = mixedMoment B raw2220step1 raw2220step1Labels := by
      have ha : raw2220step1 = raw2220step0 := by apply Matrix.ext; unfold raw2220step1 raw2220step0; decide +kernel
      have hl : raw2220step0Labels = labelEmbedding8 ∘ raw2220step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2220step0 raw2220step0Labels raw2220step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5192 node5192Labels := by rfl

theorem canonical2221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2221 raw2221Labels = mixedMoment B node2853 node2853Labels := by
  calc
    mixedMoment B raw2221 raw2221Labels = mixedMoment B raw2221step0 raw2221step0Labels := by
      have ha : raw2221step0 = (fun i j => raw2221 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2221step0 raw2221; decide +kernel
      have hl : raw2221step0Labels = raw2221Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2221 raw2221Labels permutation152 permutation4
    _ = mixedMoment B node2853 node2853Labels := by rfl

theorem canonical2222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2222 raw2222Labels = mixedMoment B node3620 node3620Labels := by
  calc
    mixedMoment B raw2222 raw2222Labels = mixedMoment B raw2222step0 raw2222step0Labels := by
      have ha : raw2222step0 = (fun i j => raw2222 (permutation216 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2222step0 raw2222; decide +kernel
      have hl : raw2222step0Labels = raw2222Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2222 raw2222Labels permutation216 permutation3
    mixedMoment B raw2222step0 raw2222step0Labels = mixedMoment B raw2222step1 raw2222step1Labels := by
      have ha : raw2222step1 = -raw2222step0 := by apply Matrix.ext; change ∀ i j, raw2222step1 i j = -(raw2222step0 i j); unfold raw2222step1 raw2222step0; decide +kernel
      have hl : raw2222step1Labels = raw2222step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2222step1 raw2222step1Labels = mixedMoment B raw2222step2 raw2222step2Labels := by
      have ha : raw2222step2 = raw2222step1 := by apply Matrix.ext; unfold raw2222step2 raw2222step1; decide +kernel
      have hl : raw2222step1Labels = labelEmbedding1 ∘ raw2222step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2222step1 raw2222step1Labels raw2222step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3620 node3620Labels := by rfl

theorem canonical2226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2226 raw2226Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw2226 raw2226Labels = mixedMoment B raw2226step0 raw2226step0Labels := by
      have ha : raw2226step0 = (fun i j => raw2226 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2226step0 raw2226; decide +kernel
      have hl : raw2226step0Labels = raw2226Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2226 raw2226Labels permutation152 permutation5
    mixedMoment B raw2226step0 raw2226step0Labels = mixedMoment B raw2226step1 raw2226step1Labels := by
      have ha : raw2226step1 = raw2226step0 := by apply Matrix.ext; unfold raw2226step1 raw2226step0; decide +kernel
      have hl : raw2226step0Labels = labelEmbedding8 ∘ raw2226step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2226step0 raw2226step0Labels raw2226step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5202 node5202Labels := by rfl

theorem canonical2227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2227 raw2227Labels = mixedMoment B node2880 node2880Labels := by
  calc
    mixedMoment B raw2227 raw2227Labels = mixedMoment B raw2227step0 raw2227step0Labels := by
      have ha : raw2227step0 = (fun i j => raw2227 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2227step0 raw2227; decide +kernel
      have hl : raw2227step0Labels = raw2227Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2227 raw2227Labels permutation170 permutation4
    _ = mixedMoment B node2880 node2880Labels := by rfl

theorem canonical2228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2228 raw2228Labels = mixedMoment B node3617 node3617Labels := by
  calc
    mixedMoment B raw2228 raw2228Labels = mixedMoment B raw2228step0 raw2228step0Labels := by
      have ha : raw2228step0 = (fun i j => raw2228 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2228step0 raw2228; decide +kernel
      have hl : raw2228step0Labels = raw2228Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2228 raw2228Labels permutation184 permutation3
    mixedMoment B raw2228step0 raw2228step0Labels = mixedMoment B raw2228step1 raw2228step1Labels := by
      have ha : raw2228step1 = -raw2228step0 := by apply Matrix.ext; change ∀ i j, raw2228step1 i j = -(raw2228step0 i j); unfold raw2228step1 raw2228step0; decide +kernel
      have hl : raw2228step1Labels = raw2228step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2228step1 raw2228step1Labels = mixedMoment B raw2228step2 raw2228step2Labels := by
      have ha : raw2228step2 = raw2228step1 := by apply Matrix.ext; unfold raw2228step2 raw2228step1; decide +kernel
      have hl : raw2228step1Labels = labelEmbedding1 ∘ raw2228step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2228step1 raw2228step1Labels raw2228step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3617 node3617Labels := by rfl

theorem canonical2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2262 raw2262Labels = mixedMoment B node5247 node5247Labels := by
  calc
    mixedMoment B raw2262 raw2262Labels = mixedMoment B raw2262step0 raw2262step0Labels := by
      have ha : raw2262step0 = (fun i j => raw2262 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2262step0 raw2262; decide +kernel
      have hl : raw2262step0Labels = raw2262Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2262 raw2262Labels permutation152 permutation4
    mixedMoment B raw2262step0 raw2262step0Labels = mixedMoment B raw2262step1 raw2262step1Labels := by
      have ha : raw2262step1 = raw2262step0 := by apply Matrix.ext; unfold raw2262step1 raw2262step0; decide +kernel
      have hl : raw2262step0Labels = labelEmbedding7 ∘ raw2262step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2262step0 raw2262step0Labels raw2262step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5247 node5247Labels := by rfl

theorem canonical2263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2263 raw2263Labels = mixedMoment B node2703 node2703Labels := by
  calc
    mixedMoment B raw2263 raw2263Labels = mixedMoment B raw2263step0 raw2263step0Labels := by
      have ha : raw2263step0 = (fun i j => raw2263 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2263step0 raw2263; decide +kernel
      have hl : raw2263step0Labels = raw2263Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2263 raw2263Labels permutation152 permutation4
    _ = mixedMoment B node2703 node2703Labels := by rfl

theorem canonical2264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2264 raw2264Labels = mixedMoment B node3496 node3496Labels := by
  calc
    mixedMoment B raw2264 raw2264Labels = mixedMoment B raw2264step0 raw2264step0Labels := by
      have ha : raw2264step0 = (fun i j => raw2264 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2264step0 raw2264; decide +kernel
      have hl : raw2264step0Labels = raw2264Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2264 raw2264Labels permutation152 permutation6
    mixedMoment B raw2264step0 raw2264step0Labels = mixedMoment B raw2264step1 raw2264step1Labels := by
      have ha : raw2264step1 = -raw2264step0 := by apply Matrix.ext; change ∀ i j, raw2264step1 i j = -(raw2264step0 i j); unfold raw2264step1 raw2264step0; decide +kernel
      have hl : raw2264step1Labels = raw2264step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2264step1 raw2264step1Labels = mixedMoment B raw2264step2 raw2264step2Labels := by
      have ha : raw2264step2 = raw2264step1 := by apply Matrix.ext; unfold raw2264step2 raw2264step1; decide +kernel
      have hl : raw2264step1Labels = labelEmbedding1 ∘ raw2264step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2264step1 raw2264step1Labels raw2264step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3496 node3496Labels := by rfl

theorem canonical2289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2289 raw2289Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw2289 raw2289Labels = mixedMoment B raw2289step0 raw2289step0Labels := by
      have ha : raw2289step0 = (fun i j => raw2289 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2289step0 raw2289; decide +kernel
      have hl : raw2289step0Labels = raw2289Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2289 raw2289Labels permutation32 permutation5
    mixedMoment B raw2289step0 raw2289step0Labels = mixedMoment B raw2289step1 raw2289step1Labels := by
      have ha : raw2289step1 = raw2289step0 := by apply Matrix.ext; unfold raw2289step1 raw2289step0; decide +kernel
      have hl : raw2289step0Labels = labelEmbedding8 ∘ raw2289step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2289step0 raw2289step0Labels raw2289step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2290 raw2290Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw2290 raw2290Labels = mixedMoment B raw2290step0 raw2290step0Labels := by
      have ha : raw2290step0 = (fun i j => raw2290 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2290step0 raw2290; decide +kernel
      have hl : raw2290step0Labels = raw2290Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2290 raw2290Labels permutation32 permutation4
    _ = mixedMoment B node3077 node3077Labels := by rfl

theorem canonical2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2291 raw2291Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw2291 raw2291Labels = mixedMoment B raw2291step0 raw2291step0Labels := by
      have ha : raw2291step0 = (fun i j => raw2291 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2291step0 raw2291; decide +kernel
      have hl : raw2291step0Labels = raw2291Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2291 raw2291Labels permutation48 permutation3
    mixedMoment B raw2291step0 raw2291step0Labels = mixedMoment B raw2291step1 raw2291step1Labels := by
      have ha : raw2291step1 = -raw2291step0 := by apply Matrix.ext; change ∀ i j, raw2291step1 i j = -(raw2291step0 i j); unfold raw2291step1 raw2291step0; decide +kernel
      have hl : raw2291step1Labels = raw2291step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2291step1 raw2291step1Labels = mixedMoment B raw2291step2 raw2291step2Labels := by
      have ha : raw2291step2 = raw2291step1 := by apply Matrix.ext; unfold raw2291step2 raw2291step1; decide +kernel
      have hl : raw2291step1Labels = labelEmbedding1 ∘ raw2291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2291step1 raw2291step1Labels raw2291step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

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

theorem canonical2310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2310 raw2310Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw2310 raw2310Labels = mixedMoment B raw2310step0 raw2310step0Labels := by
      have ha : raw2310step0 = (fun i j => raw2310 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2310step0 raw2310; decide +kernel
      have hl : raw2310step0Labels = raw2310Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2310 raw2310Labels permutation32 permutation5
    mixedMoment B raw2310step0 raw2310step0Labels = mixedMoment B raw2310step1 raw2310step1Labels := by
      have ha : raw2310step1 = raw2310step0 := by apply Matrix.ext; unfold raw2310step1 raw2310step0; decide +kernel
      have hl : raw2310step0Labels = labelEmbedding8 ∘ raw2310step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2310step0 raw2310step0Labels raw2310step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

theorem canonical2311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2311 raw2311Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw2311 raw2311Labels = mixedMoment B raw2311step0 raw2311step0Labels := by
      have ha : raw2311step0 = (fun i j => raw2311 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2311step0 raw2311; decide +kernel
      have hl : raw2311step0Labels = raw2311Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2311 raw2311Labels permutation32 permutation4
    _ = mixedMoment B node3053 node3053Labels := by rfl

theorem canonical2312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2312 raw2312Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw2312 raw2312Labels = mixedMoment B raw2312step0 raw2312step0Labels := by
      have ha : raw2312step0 = (fun i j => raw2312 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2312step0 raw2312; decide +kernel
      have hl : raw2312step0Labels = raw2312Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2312 raw2312Labels permutation41 permutation3
    mixedMoment B raw2312step0 raw2312step0Labels = mixedMoment B raw2312step1 raw2312step1Labels := by
      have ha : raw2312step1 = -raw2312step0 := by apply Matrix.ext; change ∀ i j, raw2312step1 i j = -(raw2312step0 i j); unfold raw2312step1 raw2312step0; decide +kernel
      have hl : raw2312step1Labels = raw2312step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2312step1 raw2312step1Labels = mixedMoment B raw2312step2 raw2312step2Labels := by
      have ha : raw2312step2 = raw2312step1 := by apply Matrix.ext; unfold raw2312step2 raw2312step1; decide +kernel
      have hl : raw2312step1Labels = labelEmbedding1 ∘ raw2312step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2312step1 raw2312step1Labels raw2312step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3619 node3619Labels := by rfl

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

theorem canonical2547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2547 raw2547Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw2547 raw2547Labels = mixedMoment B raw2547step0 raw2547step0Labels := by
      have ha : raw2547step0 = (fun i j => raw2547 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2547step0 raw2547; decide +kernel
      have hl : raw2547step0Labels = raw2547Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2547 raw2547Labels permutation152 permutation5
    mixedMoment B raw2547step0 raw2547step0Labels = mixedMoment B raw2547step1 raw2547step1Labels := by
      have ha : raw2547step1 = raw2547step0 := by apply Matrix.ext; unfold raw2547step1 raw2547step0; decide +kernel
      have hl : raw2547step0Labels = labelEmbedding8 ∘ raw2547step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2547step0 raw2547step0Labels raw2547step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

theorem canonical2548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2548 raw2548Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw2548 raw2548Labels = mixedMoment B raw2548step0 raw2548step0Labels := by
      have ha : raw2548step0 = (fun i j => raw2548 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2548step0 raw2548; decide +kernel
      have hl : raw2548step0Labels = raw2548Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2548 raw2548Labels permutation152 permutation4
    _ = mixedMoment B node4025 node4025Labels := by rfl

theorem canonical2549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2549 raw2549Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw2549 raw2549Labels = mixedMoment B raw2549step0 raw2549step0Labels := by
      have ha : raw2549step0 = (fun i j => raw2549 (permutation216 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2549step0 raw2549; decide +kernel
      have hl : raw2549step0Labels = raw2549Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2549 raw2549Labels permutation216 permutation3
    mixedMoment B raw2549step0 raw2549step0Labels = mixedMoment B raw2549step1 raw2549step1Labels := by
      have ha : raw2549step1 = -raw2549step0 := by apply Matrix.ext; change ∀ i j, raw2549step1 i j = -(raw2549step0 i j); unfold raw2549step1 raw2549step0; decide +kernel
      have hl : raw2549step1Labels = raw2549step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2549step1 raw2549step1Labels = mixedMoment B raw2549step2 raw2549step2Labels := by
      have ha : raw2549step2 = raw2549step1 := by apply Matrix.ext; unfold raw2549step2 raw2549step1; decide +kernel
      have hl : raw2549step1Labels = labelEmbedding1 ∘ raw2549step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2549step1 raw2549step1Labels raw2549step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3909 node3909Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11669 raw11669Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw11669 raw11669Labels = mixedMoment B raw11669step0 raw11669step0Labels := by
      have hz : ∀ j, raw11669 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11669step0 = (fun i j => raw11669 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11669step0 raw11669; decide +kernel
      have hl : raw11669step0Labels = raw11669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11669 raw11669Labels permutation265 hz
    mixedMoment B raw11669step0 raw11669step0Labels = mixedMoment B raw11669step1 raw11669step1Labels := by
      have ha : raw11669step1 = (fun i j => raw11669step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11669step1 raw11669step0; decide +kernel
      have hl : raw11669step1Labels = raw11669step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11669step0 raw11669step0Labels permutation32 permutation6
    mixedMoment B raw11669step1 raw11669step1Labels = mixedMoment B raw11669step2 raw11669step2Labels := by
      have ha : raw11669step2 = raw11669step1 := by apply Matrix.ext; unfold raw11669step2 raw11669step1; decide +kernel
      have hl : raw11669step1Labels = labelEmbedding9 ∘ raw11669step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11669step1 raw11669step1Labels raw11669step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical11729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11729 raw11729Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw11729 raw11729Labels = mixedMoment B raw11729step0 raw11729step0Labels := by
      have hz : ∀ j, raw11729 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11729step0 = (fun i j => raw11729 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11729step0 raw11729; decide +kernel
      have hl : raw11729step0Labels = raw11729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11729 raw11729Labels permutation265 hz
    mixedMoment B raw11729step0 raw11729step0Labels = mixedMoment B raw11729step1 raw11729step1Labels := by
      have ha : raw11729step1 = (fun i j => raw11729step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11729step1 raw11729step0; decide +kernel
      have hl : raw11729step1Labels = raw11729step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11729step0 raw11729step0Labels permutation36 permutation7
    mixedMoment B raw11729step1 raw11729step1Labels = mixedMoment B raw11729step2 raw11729step2Labels := by
      have ha : raw11729step2 = raw11729step1 := by apply Matrix.ext; unfold raw11729step2 raw11729step1; decide +kernel
      have hl : raw11729step1Labels = labelEmbedding1 ∘ raw11729step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11729step1 raw11729step1Labels raw11729step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3100 node3100Labels := by rfl

theorem canonical11756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11756 raw11756Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw11756 raw11756Labels = mixedMoment B raw11756step0 raw11756step0Labels := by
      have hz : ∀ j, raw11756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11756step0 = (fun i j => raw11756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11756step0 raw11756; decide +kernel
      have hl : raw11756step0Labels = raw11756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11756 raw11756Labels permutation346 hz
    mixedMoment B raw11756step0 raw11756step0Labels = mixedMoment B raw11756step1 raw11756step1Labels := by
      have hz : ∀ j, raw11756step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11756step1 = (fun i j => raw11756step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11756step1 raw11756step0; decide +kernel
      have hl : raw11756step1Labels = raw11756step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11756step0 raw11756step0Labels permutation56 hz
    mixedMoment B raw11756step1 raw11756step1Labels = mixedMoment B raw11756step2 raw11756step2Labels := by
      have ha : raw11756step2 = -raw11756step1 := by apply Matrix.ext; change ∀ i j, raw11756step2 i j = -(raw11756step1 i j); unfold raw11756step2 raw11756step1; decide +kernel
      have hl : raw11756step2Labels = raw11756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical93
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12005 raw12005Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw12005 raw12005Labels = mixedMoment B raw12005step0 raw12005step0Labels := by
      have hz : ∀ j, raw12005 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12005step0 = (fun i j => raw12005 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12005step0 raw12005; decide +kernel
      have hl : raw12005step0Labels = raw12005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12005 raw12005Labels permutation265 hz
    mixedMoment B raw12005step0 raw12005step0Labels = mixedMoment B raw12005step1 raw12005step1Labels := by
      have ha : raw12005step1 = (fun i j => raw12005step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12005step1 raw12005step0; decide +kernel
      have hl : raw12005step1Labels = raw12005step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12005step0 raw12005step0Labels permutation32 permutation6
    mixedMoment B raw12005step1 raw12005step1Labels = mixedMoment B raw12005step2 raw12005step2Labels := by
      have ha : raw12005step2 = raw12005step1 := by apply Matrix.ext; unfold raw12005step2 raw12005step1; decide +kernel
      have hl : raw12005step1Labels = labelEmbedding9 ∘ raw12005step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12005step1 raw12005step1Labels raw12005step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12049 raw12049Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw12049 raw12049Labels = mixedMoment B raw12049step0 raw12049step0Labels := by
      have hz : ∀ j, raw12049 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12049step0 = (fun i j => raw12049 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12049step0 raw12049; decide +kernel
      have hl : raw12049step0Labels = raw12049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12049 raw12049Labels permutation265 hz
    mixedMoment B raw12049step0 raw12049step0Labels = mixedMoment B raw12049step1 raw12049step1Labels := by
      have ha : raw12049step1 = (fun i j => raw12049step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12049step1 raw12049step0; decide +kernel
      have hl : raw12049step1Labels = raw12049step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12049step0 raw12049step0Labels permutation32 permutation7
    mixedMoment B raw12049step1 raw12049step1Labels = mixedMoment B raw12049step2 raw12049step2Labels := by
      have ha : raw12049step2 = raw12049step1 := by apply Matrix.ext; unfold raw12049step2 raw12049step1; decide +kernel
      have hl : raw12049step1Labels = labelEmbedding1 ∘ raw12049step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12049step1 raw12049step1Labels raw12049step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3053 node3053Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical95
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12191 raw12191Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw12191 raw12191Labels = mixedMoment B raw12191step0 raw12191step0Labels := by
      have hz : ∀ j, raw12191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12191step0 = (fun i j => raw12191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12191step0 raw12191; decide +kernel
      have hl : raw12191step0Labels = raw12191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12191 raw12191Labels permutation346 hz
    mixedMoment B raw12191step0 raw12191step0Labels = mixedMoment B raw12191step1 raw12191step1Labels := by
      have ha : raw12191step1 = (fun i j => raw12191step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12191step1 raw12191step0; decide +kernel
      have hl : raw12191step1Labels = raw12191step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12191step0 raw12191step0Labels permutation32 permutation6
    mixedMoment B raw12191step1 raw12191step1Labels = mixedMoment B raw12191step2 raw12191step2Labels := by
      have ha : raw12191step2 = raw12191step1 := by apply Matrix.ext; unfold raw12191step2 raw12191step1; decide +kernel
      have hl : raw12191step1Labels = labelEmbedding9 ∘ raw12191step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12191step1 raw12191step1Labels raw12191step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical12212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12212 raw12212Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw12212 raw12212Labels = mixedMoment B raw12212step0 raw12212step0Labels := by
      have hz : ∀ j, raw12212 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12212step0 = (fun i j => raw12212 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12212step0 raw12212; decide +kernel
      have hl : raw12212step0Labels = raw12212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12212 raw12212Labels permutation346 hz
    mixedMoment B raw12212step0 raw12212step0Labels = mixedMoment B raw12212step1 raw12212step1Labels := by
      have ha : raw12212step1 = (fun i j => raw12212step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12212step1 raw12212step0; decide +kernel
      have hl : raw12212step1Labels = raw12212step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12212step0 raw12212step0Labels permutation36 permutation7
    mixedMoment B raw12212step1 raw12212step1Labels = mixedMoment B raw12212step2 raw12212step2Labels := by
      have ha : raw12212step2 = raw12212step1 := by apply Matrix.ext; unfold raw12212step2 raw12212step1; decide +kernel
      have hl : raw12212step1Labels = labelEmbedding1 ∘ raw12212step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12212step1 raw12212step1Labels raw12212step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3100 node3100Labels := by rfl

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

theorem canonical12467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12467 raw12467Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw12467 raw12467Labels = mixedMoment B raw12467step0 raw12467step0Labels := by
      have ha : raw12467step0 = (fun i j => raw12467 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12467step0 raw12467; decide +kernel
      have hl : raw12467step0Labels = raw12467Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12467 raw12467Labels permutation152 permutation6
    mixedMoment B raw12467step0 raw12467step0Labels = mixedMoment B raw12467step1 raw12467step1Labels := by
      have ha : raw12467step1 = raw12467step0 := by apply Matrix.ext; unfold raw12467step1 raw12467step0; decide +kernel
      have hl : raw12467step0Labels = labelEmbedding9 ∘ raw12467step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12467step0 raw12467step0Labels raw12467step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical12503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12503 raw12503Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw12503 raw12503Labels = mixedMoment B raw12503step0 raw12503step0Labels := by
      have ha : raw12503step0 = (fun i j => raw12503 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12503step0 raw12503; decide +kernel
      have hl : raw12503step0Labels = raw12503Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12503 raw12503Labels permutation157 permutation7
    mixedMoment B raw12503step0 raw12503step0Labels = mixedMoment B raw12503step1 raw12503step1Labels := by
      have ha : raw12503step1 = raw12503step0 := by apply Matrix.ext; unfold raw12503step1 raw12503step0; decide +kernel
      have hl : raw12503step0Labels = labelEmbedding1 ∘ raw12503step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12503step0 raw12503step0Labels raw12503step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

theorem canonical12519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12519 raw12519Labels = mixedMoment B node3550 node3550Labels := by
  calc
    mixedMoment B raw12519 raw12519Labels = mixedMoment B raw12519step0 raw12519step0Labels := by
      have ha : raw12519step0 = (fun i j => raw12519 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12519step0 raw12519; decide +kernel
      have hl : raw12519step0Labels = raw12519Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12519 raw12519Labels permutation212 permutation4
    mixedMoment B raw12519step0 raw12519step0Labels = mixedMoment B raw12519step1 raw12519step1Labels := by
      have ha : raw12519step1 = -raw12519step0 := by apply Matrix.ext; change ∀ i j, raw12519step1 i j = -(raw12519step0 i j); unfold raw12519step1 raw12519step0; decide +kernel
      have hl : raw12519step1Labels = raw12519step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3550 node3550Labels := by rfl

theorem canonical12520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12520 raw12520Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw12520 raw12520Labels = mixedMoment B raw12520step0 raw12520step0Labels := by
      have ha : raw12520step0 = (fun i j => raw12520 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12520step0 raw12520; decide +kernel
      have hl : raw12520step0Labels = raw12520Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12520 raw12520Labels permutation212 permutation4
    mixedMoment B raw12520step0 raw12520step0Labels = mixedMoment B raw12520step1 raw12520step1Labels := by
      have ha : raw12520step1 = -raw12520step0 := by apply Matrix.ext; change ∀ i j, raw12520step1 i j = -(raw12520step0 i j); unfold raw12520step1 raw12520step0; decide +kernel
      have hl : raw12520step1Labels = raw12520step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3571 node3571Labels := by rfl

theorem canonical12528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12528 raw12528Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw12528 raw12528Labels = mixedMoment B raw12528step0 raw12528step0Labels := by
      have hz : ∀ j, raw12528 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12528step0 = (fun i j => raw12528 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12528step0 raw12528; decide +kernel
      have hl : raw12528step0Labels = raw12528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12528 raw12528Labels permutation265 hz
    mixedMoment B raw12528step0 raw12528step0Labels = mixedMoment B raw12528step1 raw12528step1Labels := by
      have ha : raw12528step1 = (fun i j => raw12528step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12528step1 raw12528step0; decide +kernel
      have hl : raw12528step1Labels = raw12528step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12528step0 raw12528step0Labels permutation38 permutation4
    mixedMoment B raw12528step1 raw12528step1Labels = mixedMoment B raw12528step2 raw12528step2Labels := by
      have ha : raw12528step2 = -raw12528step1 := by apply Matrix.ext; change ∀ i j, raw12528step2 i j = -(raw12528step1 i j); unfold raw12528step2 raw12528step1; decide +kernel
      have hl : raw12528step2Labels = raw12528step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3581 node3581Labels := by rfl

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

theorem canonical12652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12652 raw12652Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw12652 raw12652Labels = mixedMoment B raw12652step0 raw12652step0Labels := by
      have hz : ∀ j, raw12652 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12652step0 = (fun i j => raw12652 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12652step0 raw12652; decide +kernel
      have hl : raw12652step0Labels = raw12652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12652 raw12652Labels permutation265 hz
    mixedMoment B raw12652step0 raw12652step0Labels = mixedMoment B raw12652step1 raw12652step1Labels := by
      have ha : raw12652step1 = (fun i j => raw12652step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12652step1 raw12652step0; decide +kernel
      have hl : raw12652step1Labels = raw12652step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12652step0 raw12652step0Labels permutation32 permutation7
    mixedMoment B raw12652step1 raw12652step1Labels = mixedMoment B raw12652step2 raw12652step2Labels := by
      have ha : raw12652step2 = raw12652step1 := by apply Matrix.ext; unfold raw12652step2 raw12652step1; decide +kernel
      have hl : raw12652step1Labels = labelEmbedding10 ∘ raw12652step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12652step1 raw12652step1Labels raw12652step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5273 node5273Labels := by rfl

theorem canonical12653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12653 raw12653Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw12653 raw12653Labels = mixedMoment B raw12653step0 raw12653step0Labels := by
      have ha : raw12653step0 = (fun i j => raw12653 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12653step0 raw12653; decide +kernel
      have hl : raw12653step0Labels = raw12653Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12653 raw12653Labels permutation212 permutation4
    mixedMoment B raw12653step0 raw12653step0Labels = mixedMoment B raw12653step1 raw12653step1Labels := by
      have ha : raw12653step1 = -raw12653step0 := by apply Matrix.ext; change ∀ i j, raw12653step1 i j = -(raw12653step0 i j); unfold raw12653step1 raw12653step0; decide +kernel
      have hl : raw12653step1Labels = raw12653step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12653step1 raw12653step1Labels = mixedMoment B raw12653step2 raw12653step2Labels := by
      have ha : raw12653step2 = raw12653step1 := by apply Matrix.ext; unfold raw12653step2 raw12653step1; decide +kernel
      have hl : raw12653step1Labels = labelEmbedding7 ∘ raw12653step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12653step1 raw12653step1Labels raw12653step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4887 node4887Labels := by rfl

theorem canonical12654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12654 raw12654Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw12654 raw12654Labels = mixedMoment B raw12654step0 raw12654step0Labels := by
      have ha : raw12654step0 = (fun i j => raw12654 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12654step0 raw12654; decide +kernel
      have hl : raw12654step0Labels = raw12654Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12654 raw12654Labels permutation154 permutation6
    mixedMoment B raw12654step0 raw12654step0Labels = mixedMoment B raw12654step1 raw12654step1Labels := by
      have ha : raw12654step1 = raw12654step0 := by apply Matrix.ext; unfold raw12654step1 raw12654step0; decide +kernel
      have hl : raw12654step0Labels = labelEmbedding9 ∘ raw12654step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12654step0 raw12654step0Labels raw12654step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical12658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12658 raw12658Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw12658 raw12658Labels = mixedMoment B raw12658step0 raw12658step0Labels := by
      have hz : ∀ j, raw12658 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12658step0 = (fun i j => raw12658 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12658step0 raw12658; decide +kernel
      have hl : raw12658step0Labels = raw12658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12658 raw12658Labels permutation265 hz
    mixedMoment B raw12658step0 raw12658step0Labels = mixedMoment B raw12658step1 raw12658step1Labels := by
      have ha : raw12658step1 = (fun i j => raw12658step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12658step1 raw12658step0; decide +kernel
      have hl : raw12658step1Labels = raw12658step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12658step0 raw12658step0Labels permutation35 permutation6
    mixedMoment B raw12658step1 raw12658step1Labels = mixedMoment B raw12658step2 raw12658step2Labels := by
      have ha : raw12658step2 = raw12658step1 := by apply Matrix.ext; unfold raw12658step2 raw12658step1; decide +kernel
      have hl : raw12658step1Labels = labelEmbedding9 ∘ raw12658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12658step1 raw12658step1Labels raw12658step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical12660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12660 raw12660Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw12660 raw12660Labels = mixedMoment B raw12660step0 raw12660step0Labels := by
      have hz : ∀ j, raw12660 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12660step0 = (fun i j => raw12660 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12660step0 raw12660; decide +kernel
      have hl : raw12660step0Labels = raw12660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12660 raw12660Labels permutation265 hz
    mixedMoment B raw12660step0 raw12660step0Labels = mixedMoment B raw12660step1 raw12660step1Labels := by
      have ha : raw12660step1 = (fun i j => raw12660step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12660step1 raw12660step0; decide +kernel
      have hl : raw12660step1Labels = raw12660step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12660step0 raw12660step0Labels permutation33 permutation6
    mixedMoment B raw12660step1 raw12660step1Labels = mixedMoment B raw12660step2 raw12660step2Labels := by
      have ha : raw12660step2 = raw12660step1 := by apply Matrix.ext; unfold raw12660step2 raw12660step1; decide +kernel
      have hl : raw12660step1Labels = labelEmbedding9 ∘ raw12660step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12660step1 raw12660step1Labels raw12660step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical12666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12666 raw12666Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw12666 raw12666Labels = mixedMoment B raw12666step0 raw12666step0Labels := by
      have ha : raw12666step0 = (fun i j => raw12666 (permutation234 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12666step0 raw12666; decide +kernel
      have hl : raw12666step0Labels = raw12666Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12666 raw12666Labels permutation234 permutation4
    mixedMoment B raw12666step0 raw12666step0Labels = mixedMoment B raw12666step1 raw12666step1Labels := by
      have ha : raw12666step1 = -raw12666step0 := by apply Matrix.ext; change ∀ i j, raw12666step1 i j = -(raw12666step0 i j); unfold raw12666step1 raw12666step0; decide +kernel
      have hl : raw12666step1Labels = raw12666step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3571 node3571Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4581 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4581 node4581Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1200 node1200Labels + mixedMoment B node3281 node3281Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1413 singletonSmall4581
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4581) = raw1413Labels := by decide +kernel
  rw [hl, canonical1413 B hB] at h
  have hc0 : mixedMoment B raw1413 (Fin.cases (0 : Fin 2) singletonSmall4581) =
      mixedMoment B node1200 node1200Labels := by
    have ha : raw1413 = raw1414 := by apply Matrix.ext; unfold raw1413 raw1414; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4581 = raw1414Labels := by decide +kernel
    rw [ha, hj, canonical1414 B hB]
  have hc1 : mixedMoment B raw1413 (Fin.cases (1 : Fin 2) singletonSmall4581) =
      mixedMoment B node3281 node3281Labels := by
    have ha : raw1413 = raw1415 := by apply Matrix.ext; unfold raw1413 raw1415; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4581 = raw1415Labels := by decide +kernel
    rw [ha, hj, canonical1415 B hB]
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

theorem singleton4887 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4887 node4887Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2243 node2243Labels + mixedMoment B node2243 node2243Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1812 singletonSmall4887
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4887) = raw1812Labels := by decide +kernel
  rw [hl, canonical1812 B hB] at h
  have hc0 : mixedMoment B raw1812 (Fin.cases (0 : Fin 2) singletonSmall4887) =
      mixedMoment B node2243 node2243Labels := by
    have ha : raw1812 = raw1813 := by apply Matrix.ext; unfold raw1812 raw1813; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4887 = raw1813Labels := by decide +kernel
    rw [ha, hj, canonical1813 B hB]
  have hc1 : mixedMoment B raw1812 (Fin.cases (1 : Fin 2) singletonSmall4887) =
      mixedMoment B node2243 node2243Labels := by
    have ha : raw1812 = raw1814 := by apply Matrix.ext; unfold raw1812 raw1814; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4887 = raw1814Labels := by decide +kernel
    rw [ha, hj, canonical1814 B hB]
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

theorem singleton5192 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5192 node5192Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2853 node2853Labels + mixedMoment B node3620 node3620Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2220 singletonSmall5192
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5192) = raw2220Labels := by decide +kernel
  rw [hl, canonical2220 B hB] at h
  have hc0 : mixedMoment B raw2220 (Fin.cases (0 : Fin 2) singletonSmall5192) =
      mixedMoment B node2853 node2853Labels := by
    have ha : raw2220 = raw2221 := by apply Matrix.ext; unfold raw2220 raw2221; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5192 = raw2221Labels := by decide +kernel
    rw [ha, hj, canonical2221 B hB]
  have hc1 : mixedMoment B raw2220 (Fin.cases (1 : Fin 2) singletonSmall5192) =
      mixedMoment B node3620 node3620Labels := by
    have ha : raw2220 = raw2222 := by apply Matrix.ext; unfold raw2220 raw2222; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5192 = raw2222Labels := by decide +kernel
    rw [ha, hj, canonical2222 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5202 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5202 node5202Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2880 node2880Labels + mixedMoment B node3617 node3617Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2226 singletonSmall5202
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5202) = raw2226Labels := by decide +kernel
  rw [hl, canonical2226 B hB] at h
  have hc0 : mixedMoment B raw2226 (Fin.cases (0 : Fin 2) singletonSmall5202) =
      mixedMoment B node2880 node2880Labels := by
    have ha : raw2226 = raw2227 := by apply Matrix.ext; unfold raw2226 raw2227; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5202 = raw2227Labels := by decide +kernel
    rw [ha, hj, canonical2227 B hB]
  have hc1 : mixedMoment B raw2226 (Fin.cases (1 : Fin 2) singletonSmall5202) =
      mixedMoment B node3617 node3617Labels := by
    have ha : raw2226 = raw2228 := by apply Matrix.ext; unfold raw2226 raw2228; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5202 = raw2228Labels := by decide +kernel
    rw [ha, hj, canonical2228 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5247 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5247 node5247Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2703 node2703Labels + mixedMoment B node3496 node3496Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2262 singletonSmall5247
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5247) = raw2262Labels := by decide +kernel
  rw [hl, canonical2262 B hB] at h
  have hc0 : mixedMoment B raw2262 (Fin.cases (0 : Fin 2) singletonSmall5247) =
      mixedMoment B node2703 node2703Labels := by
    have ha : raw2262 = raw2263 := by apply Matrix.ext; unfold raw2262 raw2263; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5247 = raw2263Labels := by decide +kernel
    rw [ha, hj, canonical2263 B hB]
  have hc1 : mixedMoment B raw2262 (Fin.cases (1 : Fin 2) singletonSmall5247) =
      mixedMoment B node3496 node3496Labels := by
    have ha : raw2262 = raw2264 := by apply Matrix.ext; unfold raw2262 raw2264; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5247 = raw2264Labels := by decide +kernel
    rw [ha, hj, canonical2264 B hB]
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

theorem singleton5284 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5284 node5284Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3077 node3077Labels + mixedMoment B node3625 node3625Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2289 singletonSmall5284
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5284) = raw2289Labels := by decide +kernel
  rw [hl, canonical2289 B hB] at h
  have hc0 : mixedMoment B raw2289 (Fin.cases (0 : Fin 2) singletonSmall5284) =
      mixedMoment B node3077 node3077Labels := by
    have ha : raw2289 = raw2290 := by apply Matrix.ext; unfold raw2289 raw2290; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5284 = raw2290Labels := by decide +kernel
    rw [ha, hj, canonical2290 B hB]
  have hc1 : mixedMoment B raw2289 (Fin.cases (1 : Fin 2) singletonSmall5284) =
      mixedMoment B node3625 node3625Labels := by
    have ha : raw2289 = raw2291 := by apply Matrix.ext; unfold raw2289 raw2291; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5284 = raw2291Labels := by decide +kernel
    rw [ha, hj, canonical2291 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5301 node5301Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3053 node3053Labels + mixedMoment B node3619 node3619Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2310 singletonSmall5301
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5301) = raw2310Labels := by decide +kernel
  rw [hl, canonical2310 B hB] at h
  have hc0 : mixedMoment B raw2310 (Fin.cases (0 : Fin 2) singletonSmall5301) =
      mixedMoment B node3053 node3053Labels := by
    have ha : raw2310 = raw2311 := by apply Matrix.ext; unfold raw2310 raw2311; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5301 = raw2311Labels := by decide +kernel
    rw [ha, hj, canonical2311 B hB]
  have hc1 : mixedMoment B raw2310 (Fin.cases (1 : Fin 2) singletonSmall5301) =
      mixedMoment B node3619 node3619Labels := by
    have ha : raw2310 = raw2312 := by apply Matrix.ext; unfold raw2310 raw2312; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5301 = raw2312Labels := by decide +kernel
    rw [ha, hj, canonical2312 B hB]
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

theorem singleton5447 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5447 node5447Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node4025 node4025Labels + mixedMoment B node3909 node3909Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2547 singletonSmall5447
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5447) = raw2547Labels := by decide +kernel
  rw [hl, canonical2547 B hB] at h
  have hc0 : mixedMoment B raw2547 (Fin.cases (0 : Fin 2) singletonSmall5447) =
      mixedMoment B node4025 node4025Labels := by
    have ha : raw2547 = raw2548 := by apply Matrix.ext; unfold raw2547 raw2548; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5447 = raw2548Labels := by decide +kernel
    rw [ha, hj, canonical2548 B hB]
  have hc1 : mixedMoment B raw2547 (Fin.cases (1 : Fin 2) singletonSmall5447) =
      mixedMoment B node3909 node3909Labels := by
    have ha : raw2547 = raw2549 := by apply Matrix.ext; unfold raw2547 raw2549; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5447 = raw2549Labels := by decide +kernel
    rw [ha, hj, canonical2549 B hB]
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

theorem sound1200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1200 node1200Labels = Sparse.eval nodeValue1200 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1200) = mixedMoment B node1200 node1200Labels := rfl
  simpa [nodeValue1200, Sparse.eval] using hc.symm

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

theorem sound1260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1260 node1260Labels = Sparse.eval nodeValue1260 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1260) = mixedMoment B node1260 node1260Labels := rfl
  simpa [nodeValue1260, Sparse.eval] using hc.symm

theorem sound1262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1262 node1262Labels = Sparse.eval nodeValue1262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1262) = mixedMoment B node1262 node1262Labels := rfl
  simpa [nodeValue1262, Sparse.eval] using hc.symm

theorem sound1270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1270 node1270Labels = Sparse.eval nodeValue1270 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1270) = mixedMoment B node1270 node1270Labels := rfl
  simpa [nodeValue1270, Sparse.eval] using hc.symm

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

theorem sound1293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1293 node1293Labels = Sparse.eval nodeValue1293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1293) = mixedMoment B node1293 node1293Labels := rfl
  simpa [nodeValue1293, Sparse.eval] using hc.symm

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

theorem sound2589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2589 node2589Labels = Sparse.eval nodeValue2589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2589) = mixedMoment B node2589 node2589Labels := rfl
  simpa [nodeValue2589, Sparse.eval] using hc.symm

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

theorem sound2631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2631 node2631Labels = Sparse.eval nodeValue2631 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2631) = mixedMoment B node2631 node2631Labels := rfl
  simpa [nodeValue2631, Sparse.eval] using hc.symm

theorem sound2633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2633 node2633Labels = Sparse.eval nodeValue2633 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2633) = mixedMoment B node2633 node2633Labels := rfl
  simpa [nodeValue2633, Sparse.eval] using hc.symm

theorem sound2641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2641 node2641Labels = Sparse.eval nodeValue2641 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2641) = mixedMoment B node2641 node2641Labels := rfl
  simpa [nodeValue2641, Sparse.eval] using hc.symm

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

theorem zero2741 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2741 node2741Labels = 0 := by
  exact mixedMoment_order_one B hB node2741 node2741Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2703 node2703Labels = Sparse.eval nodeValue2703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2703) = mixedMoment B node2703 node2703Labels := rfl
  simpa [nodeValue2703, Sparse.eval] using hc.symm

theorem sound2741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2741 node2741Labels = Sparse.eval nodeValue2741 (mixedVector B) := by
  simpa only [nodeValue2741, Sparse.eval_nil] using zero2741 B _hB _hF

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

theorem sound2764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2764 node2764Labels = Sparse.eval nodeValue2764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2764) = mixedMoment B node2764 node2764Labels := rfl
  simpa [nodeValue2764, Sparse.eval] using hc.symm

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

theorem sound2853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2853 node2853Labels = Sparse.eval nodeValue2853 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2853) = mixedMoment B node2853 node2853Labels := rfl
  simpa [nodeValue2853, Sparse.eval] using hc.symm

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

theorem sound2880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2880 node2880Labels = Sparse.eval nodeValue2880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2880) = mixedMoment B node2880 node2880Labels := rfl
  simpa [nodeValue2880, Sparse.eval] using hc.symm

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

theorem sound3023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3023 node3023Labels = Sparse.eval nodeValue3023 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3023) = mixedMoment B node3023 node3023Labels := rfl
  simpa [nodeValue3023, Sparse.eval] using hc.symm

theorem sound3053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3053 node3053Labels = Sparse.eval nodeValue3053 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3053) = mixedMoment B node3053 node3053Labels := rfl
  simpa [nodeValue3053, Sparse.eval] using hc.symm

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

theorem sound3073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3073 node3073Labels = Sparse.eval nodeValue3073 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3073) = mixedMoment B node3073 node3073Labels := rfl
  simpa [nodeValue3073, Sparse.eval] using hc.symm

theorem sound3074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3074 node3074Labels = Sparse.eval nodeValue3074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3074) = mixedMoment B node3074 node3074Labels := rfl
  simpa [nodeValue3074, Sparse.eval] using hc.symm

theorem sound3077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3077 node3077Labels = Sparse.eval nodeValue3077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3077) = mixedMoment B node3077 node3077Labels := rfl
  simpa [nodeValue3077, Sparse.eval] using hc.symm

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

theorem sound3221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3221 node3221Labels = Sparse.eval nodeValue3221 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3221) = mixedMoment B node3221 node3221Labels := rfl
  simpa [nodeValue3221, Sparse.eval] using hc.symm

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

theorem sound3281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3281 node3281Labels = Sparse.eval nodeValue3281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3281) = mixedMoment B node3281 node3281Labels := rfl
  simpa [nodeValue3281, Sparse.eval] using hc.symm

theorem sound3292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3292 node3292Labels = Sparse.eval nodeValue3292 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3292) = mixedMoment B node3292 node3292Labels := rfl
  simpa [nodeValue3292, Sparse.eval] using hc.symm

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

theorem zero3489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3489 node3489Labels = 0 := by
  exact mixedMoment_alpha B hF node3489 node3489Labels 1 permutation434
    (by decide +kernel)

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

theorem sound3489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3489 node3489Labels = Sparse.eval nodeValue3489 (mixedVector B) := by
  simpa only [nodeValue3489, Sparse.eval_nil] using zero3489 B _hB _hF

theorem sound3496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3496 node3496Labels = Sparse.eval nodeValue3496 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3496) = mixedMoment B node3496 node3496Labels := rfl
  simpa [nodeValue3496, Sparse.eval] using hc.symm

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

theorem sound3550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3550 node3550Labels = Sparse.eval nodeValue3550 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3550) = mixedMoment B node3550 node3550Labels := rfl
  simpa [nodeValue3550, Sparse.eval] using hc.symm

theorem sound3551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3551 node3551Labels = Sparse.eval nodeValue3551 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3551) = mixedMoment B node3551 node3551Labels := rfl
  simpa [nodeValue3551, Sparse.eval] using hc.symm

theorem sound3571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3571 node3571Labels = Sparse.eval nodeValue3571 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3571) = mixedMoment B node3571 node3571Labels := rfl
  simpa [nodeValue3571, Sparse.eval] using hc.symm

theorem sound3581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3581 node3581Labels = Sparse.eval nodeValue3581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3581) = mixedMoment B node3581 node3581Labels := rfl
  simpa [nodeValue3581, Sparse.eval] using hc.symm

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

theorem sound3617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3617 node3617Labels = Sparse.eval nodeValue3617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3617) = mixedMoment B node3617 node3617Labels := rfl
  simpa [nodeValue3617, Sparse.eval] using hc.symm

theorem sound3619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3619 node3619Labels = Sparse.eval nodeValue3619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3619) = mixedMoment B node3619 node3619Labels := rfl
  simpa [nodeValue3619, Sparse.eval] using hc.symm

theorem sound3620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3620 node3620Labels = Sparse.eval nodeValue3620 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3620) = mixedMoment B node3620 node3620Labels := rfl
  simpa [nodeValue3620, Sparse.eval] using hc.symm

theorem sound3625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3625 node3625Labels = Sparse.eval nodeValue3625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3625) = mixedMoment B node3625 node3625Labels := rfl
  simpa [nodeValue3625, Sparse.eval] using hc.symm

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

theorem sound3885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3885 node3885Labels = Sparse.eval nodeValue3885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3885) = mixedMoment B node3885 node3885Labels := rfl
  simpa [nodeValue3885, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3904 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3904 node3904Labels = 0 := by
  exact mixedMoment_order_one B hB node3904 node3904Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3904 node3904Labels = Sparse.eval nodeValue3904 (mixedVector B) := by
  simpa only [nodeValue3904, Sparse.eval_nil] using zero3904 B _hB _hF

theorem sound3909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3909 node3909Labels = Sparse.eval nodeValue3909 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3909) = mixedMoment B node3909 node3909Labels := rfl
  simpa [nodeValue3909, Sparse.eval] using hc.symm

theorem sound3910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3910 node3910Labels = Sparse.eval nodeValue3910 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3910) = mixedMoment B node3910 node3910Labels := rfl
  simpa [nodeValue3910, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4025 node4025Labels = Sparse.eval nodeValue4025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4025) = mixedMoment B node4025 node4025Labels := rfl
  simpa [nodeValue4025, Sparse.eval] using hc.symm

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

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

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

theorem sound4581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4581 node4581Labels = Sparse.eval nodeValue4581 (mixedVector B) := by
  have h := singleton4581 B _hB
  rw [sound1200 B _hB _hF, sound3281 B _hB _hF] at h
  norm_num [nodeValue4581, nodeValue1200, nodeValue3281, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4601 node4601Labels = Sparse.eval nodeValue4601 (mixedVector B) := by
  have h := singleton4601 B _hB
  rw [sound1235 B _hB _hF, sound3292 B _hB _hF] at h
  norm_num [nodeValue4601, nodeValue1235, nodeValue3292, Sparse.eval] at h ⊢
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

theorem sound4885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4885 node4885Labels = Sparse.eval nodeValue4885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4885) = mixedMoment B node4885 node4885Labels := rfl
  simpa [nodeValue4885, Sparse.eval] using hc.symm

theorem sound4887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4887 node4887Labels = Sparse.eval nodeValue4887 (mixedVector B) := by
  have h := singleton4887 B _hB
  rw [sound2243 B _hB _hF] at h
  norm_num [nodeValue4887, nodeValue2243, Sparse.eval] at h ⊢
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

theorem sound5192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5192 node5192Labels = Sparse.eval nodeValue5192 (mixedVector B) := by
  have h := singleton5192 B _hB
  rw [sound2853 B _hB _hF, sound3620 B _hB _hF] at h
  norm_num [nodeValue5192, nodeValue2853, nodeValue3620, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5202 node5202Labels = Sparse.eval nodeValue5202 (mixedVector B) := by
  have h := singleton5202 B _hB
  rw [sound2880 B _hB _hF, sound3617 B _hB _hF] at h
  norm_num [nodeValue5202, nodeValue2880, nodeValue3617, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5247 node5247Labels = Sparse.eval nodeValue5247 (mixedVector B) := by
  have h := singleton5247 B _hB
  rw [sound2703 B _hB _hF, sound3496 B _hB _hF] at h
  norm_num [nodeValue5247, nodeValue2703, nodeValue3496, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5273 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5273 node5273Labels = 0 := by
  exact mixedMoment_order_one B hB node5273 node5273Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5273 node5273Labels = Sparse.eval nodeValue5273 (mixedVector B) := by
  simpa only [nodeValue5273, Sparse.eval_nil] using zero5273 B _hB _hF

theorem sound5281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5281 node5281Labels = Sparse.eval nodeValue5281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5281) = mixedMoment B node5281 node5281Labels := rfl
  simpa [nodeValue5281, Sparse.eval] using hc.symm

theorem sound5284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5284 node5284Labels = Sparse.eval nodeValue5284 (mixedVector B) := by
  have h := singleton5284 B _hB
  rw [sound3077 B _hB _hF, sound3625 B _hB _hF] at h
  norm_num [nodeValue5284, nodeValue3077, nodeValue3625, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5286 node5286Labels = Sparse.eval nodeValue5286 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5286) = mixedMoment B node5286 node5286Labels := rfl
  simpa [nodeValue5286, Sparse.eval] using hc.symm

theorem sound5301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5301 node5301Labels = Sparse.eval nodeValue5301 (mixedVector B) := by
  have h := singleton5301 B _hB
  rw [sound3053 B _hB _hF, sound3619 B _hB _hF] at h
  norm_num [nodeValue5301, nodeValue3053, nodeValue3619, Sparse.eval] at h ⊢
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

theorem sound5447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5447 node5447Labels = Sparse.eval nodeValue5447 (mixedVector B) := by
  have h := singleton5447 B _hB
  rw [sound3909 B _hB _hF, sound4025 B _hB _hF] at h
  norm_num [nodeValue5447, nodeValue3909, nodeValue4025, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources25
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq814 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm814 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA814 + difference 4 0) (sourceB814 + difference 0 4) sourceC814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2105) := by
    have ha : (tripleCharges (sourceA814 + difference 4 0) (sourceB814 + difference 0 4) sourceC814) = raw13369 := by
      apply Matrix.ext; unfold tripleCharges sourceA814 sourceB814 sourceC814 difference raw13369; decide +kernel
    rw [ha]
    exact (canonical13369 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA814 + difference 4 1) (sourceB814 + difference 1 4) sourceC814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA814 + difference 4 1) (sourceB814 + difference 1 4) sourceC814) = raw12528 := by
      apply Matrix.ext; unfold tripleCharges sourceA814 sourceB814 sourceC814 difference raw12528; decide +kernel
    rw [ha]
    exact (canonical12528 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA814 + difference 4 2) (sourceB814 + difference 2 4) sourceC814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA814 + difference 4 2) (sourceB814 + difference 2 4) sourceC814) = raw13372 := by
      apply Matrix.ext; unfold tripleCharges sourceA814 sourceB814 sourceC814 difference raw13372; decide +kernel
    rw [ha]
    exact (canonical13372 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA814 + difference 4 3) (sourceB814 + difference 3 4) sourceC814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3073) := by
    have ha : (tripleCharges (sourceA814 + difference 4 3) (sourceB814 + difference 3 4) sourceC814) = raw13371 := by
      apply Matrix.ext; unfold tripleCharges sourceA814 sourceB814 sourceC814 difference raw13371; decide +kernel
    rw [ha]
    exact (canonical13371 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA814 + difference 4 4) (sourceB814 + difference 4 4) sourceC814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA814 + difference 4 4) (sourceB814 + difference 4 4) sourceC814) = raw12520 := by
      apply Matrix.ext; unfold tripleCharges sourceA814 sourceB814 sourceC814 difference raw12520; decide +kernel
    rw [ha]
    exact (canonical12520 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA814 + difference 4 5) (sourceB814 + difference 5 4) sourceC814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA814 + difference 4 5) (sourceB814 + difference 5 4) sourceC814) = raw13373 := by
      apply Matrix.ext; unfold tripleCharges sourceA814 sourceB814 sourceC814 difference raw13373; decide +kernel
    rw [ha]
    exact (canonical13373 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA814 + sourceB814) sourceC814) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA814 + sourceB814) sourceC814) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA814 sourceB814 sourceC814 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA814 sourceB814 sourceC814
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm814, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq815 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm815 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA815 + difference 0 4) (sourceB815 + difference 4 0) sourceC815) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3489) := by
    have ha : (tripleCharges (sourceA815 + difference 0 4) (sourceB815 + difference 4 0) sourceC815) = raw13366 := by
      apply Matrix.ext; unfold tripleCharges sourceA815 sourceB815 sourceC815 difference raw13366; decide +kernel
    rw [ha]
    exact (canonical13366 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA815 + difference 1 4) (sourceB815 + difference 4 1) sourceC815) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3551) := by
    have ha : (tripleCharges (sourceA815 + difference 1 4) (sourceB815 + difference 4 1) sourceC815) = raw13374 := by
      apply Matrix.ext; unfold tripleCharges sourceA815 sourceB815 sourceC815 difference raw13374; decide +kernel
    rw [ha]
    exact (canonical13374 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA815 + difference 2 4) (sourceB815 + difference 4 2) sourceC815) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3551) := by
    have ha : (tripleCharges (sourceA815 + difference 2 4) (sourceB815 + difference 4 2) sourceC815) = raw12928 := by
      apply Matrix.ext; unfold tripleCharges sourceA815 sourceB815 sourceC815 difference raw12928; decide +kernel
    rw [ha]
    exact (canonical12928 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA815 + difference 3 4) (sourceB815 + difference 4 3) sourceC815) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA815 + difference 3 4) (sourceB815 + difference 4 3) sourceC815) = raw12666 := by
      apply Matrix.ext; unfold tripleCharges sourceA815 sourceB815 sourceC815 difference raw12666; decide +kernel
    rw [ha]
    exact (canonical12666 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA815 + difference 4 4) (sourceB815 + difference 4 4) sourceC815) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA815 + difference 4 4) (sourceB815 + difference 4 4) sourceC815) = raw12520 := by
      apply Matrix.ext; unfold tripleCharges sourceA815 sourceB815 sourceC815 difference raw12520; decide +kernel
    rw [ha]
    exact (canonical12520 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA815 + difference 5 4) (sourceB815 + difference 4 5) sourceC815) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3550) := by
    have ha : (tripleCharges (sourceA815 + difference 5 4) (sourceB815 + difference 4 5) sourceC815) = raw12519 := by
      apply Matrix.ext; unfold tripleCharges sourceA815 sourceB815 sourceC815 difference raw12519; decide +kernel
    rw [ha]
    exact (canonical12519 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA815 + sourceB815) sourceC815) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA815 + sourceB815) sourceC815) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA815 sourceB815 sourceC815 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA815 sourceB815 sourceC815
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm815, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq816 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm816 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA816 + difference 0 1) (sourceB816 + difference 1 0) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA816 + difference 0 1) (sourceB816 + difference 1 0) sourceC816) = raw13375 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13375; decide +kernel
    rw [ha]
    exact (canonical13375 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA816 + difference 0 2) (sourceB816 + difference 2 0) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA816 + difference 0 2) (sourceB816 + difference 2 0) sourceC816) = raw13376 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13376; decide +kernel
    rw [ha]
    exact (canonical13376 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA816 + difference 0 3) (sourceB816 + difference 3 0) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA816 + difference 0 3) (sourceB816 + difference 3 0) sourceC816) = raw13377 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13377; decide +kernel
    rw [ha]
    exact (canonical13377 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA816 + difference 0 4) (sourceB816 + difference 4 0) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA816 + difference 0 4) (sourceB816 + difference 4 0) sourceC816) = raw13378 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13378; decide +kernel
    rw [ha]
    exact (canonical13378 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA816 + difference 0 5) (sourceB816 + difference 5 0) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA816 + difference 0 5) (sourceB816 + difference 5 0) sourceC816) = raw13379 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13379; decide +kernel
    rw [ha]
    exact (canonical13379 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA816 + difference 1 0) (sourceB816 + difference 0 1) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA816 + difference 1 0) (sourceB816 + difference 0 1) sourceC816) = raw13380 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13380; decide +kernel
    rw [ha]
    exact (canonical13380 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA816 + difference 1 2) (sourceB816 + difference 2 1) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5202) := by
    have ha : (tripleCharges (sourceA816 + difference 1 2) (sourceB816 + difference 2 1) sourceC816) = raw13381 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13381; decide +kernel
    rw [ha]
    exact (canonical13381 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA816 + difference 1 3) (sourceB816 + difference 3 1) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA816 + difference 1 3) (sourceB816 + difference 3 1) sourceC816) = raw13382 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13382; decide +kernel
    rw [ha]
    exact (canonical13382 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA816 + difference 1 4) (sourceB816 + difference 4 1) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA816 + difference 1 4) (sourceB816 + difference 4 1) sourceC816) = raw13383 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13383; decide +kernel
    rw [ha]
    exact (canonical13383 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA816 + difference 1 5) (sourceB816 + difference 5 1) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA816 + difference 1 5) (sourceB816 + difference 5 1) sourceC816) = raw13384 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13384; decide +kernel
    rw [ha]
    exact (canonical13384 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA816 + difference 2 0) (sourceB816 + difference 0 2) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA816 + difference 2 0) (sourceB816 + difference 0 2) sourceC816) = raw13385 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13385; decide +kernel
    rw [ha]
    exact (canonical13385 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA816 + difference 2 1) (sourceB816 + difference 1 2) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5202) := by
    have ha : (tripleCharges (sourceA816 + difference 2 1) (sourceB816 + difference 1 2) sourceC816) = raw13386 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13386; decide +kernel
    rw [ha]
    exact (canonical13386 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA816 + difference 2 3) (sourceB816 + difference 3 2) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA816 + difference 2 3) (sourceB816 + difference 3 2) sourceC816) = raw13387 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13387; decide +kernel
    rw [ha]
    exact (canonical13387 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA816 + difference 2 4) (sourceB816 + difference 4 2) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA816 + difference 2 4) (sourceB816 + difference 4 2) sourceC816) = raw13388 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13388; decide +kernel
    rw [ha]
    exact (canonical13388 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA816 + difference 2 5) (sourceB816 + difference 5 2) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA816 + difference 2 5) (sourceB816 + difference 5 2) sourceC816) = raw13389 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13389; decide +kernel
    rw [ha]
    exact (canonical13389 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA816 + difference 3 0) (sourceB816 + difference 0 3) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4581) := by
    have ha : (tripleCharges (sourceA816 + difference 3 0) (sourceB816 + difference 0 3) sourceC816) = raw13390 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13390; decide +kernel
    rw [ha]
    exact (canonical13390 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA816 + difference 3 1) (sourceB816 + difference 1 3) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA816 + difference 3 1) (sourceB816 + difference 1 3) sourceC816) = raw13391 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13391; decide +kernel
    rw [ha]
    exact (canonical13391 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA816 + difference 3 2) (sourceB816 + difference 2 3) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA816 + difference 3 2) (sourceB816 + difference 2 3) sourceC816) = raw13392 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13392; decide +kernel
    rw [ha]
    exact (canonical13392 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA816 + difference 3 4) (sourceB816 + difference 4 3) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA816 + difference 3 4) (sourceB816 + difference 4 3) sourceC816) = raw13393 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13393; decide +kernel
    rw [ha]
    exact (canonical13393 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA816 + difference 3 5) (sourceB816 + difference 5 3) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA816 + difference 3 5) (sourceB816 + difference 5 3) sourceC816) = raw13394 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13394; decide +kernel
    rw [ha]
    exact (canonical13394 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA816 + difference 4 0) (sourceB816 + difference 0 4) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4581) := by
    have ha : (tripleCharges (sourceA816 + difference 4 0) (sourceB816 + difference 0 4) sourceC816) = raw13395 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13395; decide +kernel
    rw [ha]
    exact (canonical13395 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA816 + difference 4 1) (sourceB816 + difference 1 4) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA816 + difference 4 1) (sourceB816 + difference 1 4) sourceC816) = raw13396 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13396; decide +kernel
    rw [ha]
    exact (canonical13396 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA816 + difference 4 2) (sourceB816 + difference 2 4) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA816 + difference 4 2) (sourceB816 + difference 2 4) sourceC816) = raw13397 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13397; decide +kernel
    rw [ha]
    exact (canonical13397 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA816 + difference 4 3) (sourceB816 + difference 3 4) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA816 + difference 4 3) (sourceB816 + difference 3 4) sourceC816) = raw13398 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13398; decide +kernel
    rw [ha]
    exact (canonical13398 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA816 + difference 4 5) (sourceB816 + difference 5 4) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA816 + difference 4 5) (sourceB816 + difference 5 4) sourceC816) = raw13399 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13399; decide +kernel
    rw [ha]
    exact (canonical13399 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA816 + difference 5 0) (sourceB816 + difference 0 5) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4581) := by
    have ha : (tripleCharges (sourceA816 + difference 5 0) (sourceB816 + difference 0 5) sourceC816) = raw13400 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13400; decide +kernel
    rw [ha]
    exact (canonical13400 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA816 + difference 5 1) (sourceB816 + difference 1 5) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA816 + difference 5 1) (sourceB816 + difference 1 5) sourceC816) = raw13401 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13401; decide +kernel
    rw [ha]
    exact (canonical13401 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA816 + difference 5 2) (sourceB816 + difference 2 5) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA816 + difference 5 2) (sourceB816 + difference 2 5) sourceC816) = raw13402 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13402; decide +kernel
    rw [ha]
    exact (canonical13402 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA816 + difference 5 3) (sourceB816 + difference 3 5) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA816 + difference 5 3) (sourceB816 + difference 3 5) sourceC816) = raw13403 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13403; decide +kernel
    rw [ha]
    exact (canonical13403 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA816 + difference 5 4) (sourceB816 + difference 4 5) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA816 + difference 5 4) (sourceB816 + difference 4 5) sourceC816) = raw13404 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13404; decide +kernel
    rw [ha]
    exact (canonical13404 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA816 sourceB816 sourceC816
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm816, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq818 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm818 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA818 + difference 0 1) (sourceB818 + difference 1 0) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA818 + difference 0 1) (sourceB818 + difference 1 0) sourceC818) = raw12652 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw12652; decide +kernel
    rw [ha]
    exact (canonical12652 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA818 + difference 0 2) (sourceB818 + difference 2 0) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA818 + difference 0 2) (sourceB818 + difference 2 0) sourceC818) = raw13435 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13435; decide +kernel
    rw [ha]
    exact (canonical13435 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA818 + difference 0 3) (sourceB818 + difference 3 0) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA818 + difference 0 3) (sourceB818 + difference 3 0) sourceC818) = raw13322 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13322; decide +kernel
    rw [ha]
    exact (canonical13322 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA818 + difference 0 4) (sourceB818 + difference 4 0) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA818 + difference 0 4) (sourceB818 + difference 4 0) sourceC818) = raw13436 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13436; decide +kernel
    rw [ha]
    exact (canonical13436 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA818 + difference 0 5) (sourceB818 + difference 5 0) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA818 + difference 0 5) (sourceB818 + difference 5 0) sourceC818) = raw13437 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13437; decide +kernel
    rw [ha]
    exact (canonical13437 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA818 + difference 1 0) (sourceB818 + difference 0 1) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA818 + difference 1 0) (sourceB818 + difference 0 1) sourceC818) = raw13438 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13438; decide +kernel
    rw [ha]
    exact (canonical13438 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA818 + difference 1 2) (sourceB818 + difference 2 1) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA818 + difference 1 2) (sourceB818 + difference 2 1) sourceC818) = raw13439 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13439; decide +kernel
    rw [ha]
    exact (canonical13439 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA818 + difference 1 3) (sourceB818 + difference 3 1) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA818 + difference 1 3) (sourceB818 + difference 3 1) sourceC818) = raw13327 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13327; decide +kernel
    rw [ha]
    exact (canonical13327 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA818 + difference 1 4) (sourceB818 + difference 4 1) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA818 + difference 1 4) (sourceB818 + difference 4 1) sourceC818) = raw13440 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13440; decide +kernel
    rw [ha]
    exact (canonical13440 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA818 + difference 1 5) (sourceB818 + difference 5 1) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA818 + difference 1 5) (sourceB818 + difference 5 1) sourceC818) = raw13441 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13441; decide +kernel
    rw [ha]
    exact (canonical13441 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA818 + difference 2 0) (sourceB818 + difference 0 2) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA818 + difference 2 0) (sourceB818 + difference 0 2) sourceC818) = raw13071 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13071; decide +kernel
    rw [ha]
    exact (canonical13071 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA818 + difference 2 1) (sourceB818 + difference 1 2) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA818 + difference 2 1) (sourceB818 + difference 1 2) sourceC818) = raw12005 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw12005; decide +kernel
    rw [ha]
    exact (canonical12005 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA818 + difference 2 3) (sourceB818 + difference 3 2) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA818 + difference 2 3) (sourceB818 + difference 3 2) sourceC818) = raw12887 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw12887; decide +kernel
    rw [ha]
    exact (canonical12887 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA818 + difference 2 4) (sourceB818 + difference 4 2) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA818 + difference 2 4) (sourceB818 + difference 4 2) sourceC818) = raw13072 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13072; decide +kernel
    rw [ha]
    exact (canonical13072 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA818 + difference 2 5) (sourceB818 + difference 5 2) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA818 + difference 2 5) (sourceB818 + difference 5 2) sourceC818) = raw13073 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13073; decide +kernel
    rw [ha]
    exact (canonical13073 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA818 + difference 3 0) (sourceB818 + difference 0 3) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA818 + difference 3 0) (sourceB818 + difference 0 3) sourceC818) = raw13442 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13442; decide +kernel
    rw [ha]
    exact (canonical13442 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA818 + difference 3 1) (sourceB818 + difference 1 3) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA818 + difference 3 1) (sourceB818 + difference 1 3) sourceC818) = raw12658 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw12658; decide +kernel
    rw [ha]
    exact (canonical12658 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA818 + difference 3 2) (sourceB818 + difference 2 3) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA818 + difference 3 2) (sourceB818 + difference 2 3) sourceC818) = raw13443 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13443; decide +kernel
    rw [ha]
    exact (canonical13443 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA818 + difference 3 4) (sourceB818 + difference 4 3) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA818 + difference 3 4) (sourceB818 + difference 4 3) sourceC818) = raw13444 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13444; decide +kernel
    rw [ha]
    exact (canonical13444 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA818 + difference 3 5) (sourceB818 + difference 5 3) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA818 + difference 3 5) (sourceB818 + difference 5 3) sourceC818) = raw13445 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13445; decide +kernel
    rw [ha]
    exact (canonical13445 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA818 + difference 4 0) (sourceB818 + difference 0 4) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA818 + difference 4 0) (sourceB818 + difference 0 4) sourceC818) = raw13446 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13446; decide +kernel
    rw [ha]
    exact (canonical13446 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA818 + difference 4 1) (sourceB818 + difference 1 4) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA818 + difference 4 1) (sourceB818 + difference 1 4) sourceC818) = raw12660 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw12660; decide +kernel
    rw [ha]
    exact (canonical12660 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA818 + difference 4 2) (sourceB818 + difference 2 4) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA818 + difference 4 2) (sourceB818 + difference 2 4) sourceC818) = raw13447 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13447; decide +kernel
    rw [ha]
    exact (canonical13447 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA818 + difference 4 3) (sourceB818 + difference 3 4) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA818 + difference 4 3) (sourceB818 + difference 3 4) sourceC818) = raw13331 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13331; decide +kernel
    rw [ha]
    exact (canonical13331 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA818 + difference 4 5) (sourceB818 + difference 5 4) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA818 + difference 4 5) (sourceB818 + difference 5 4) sourceC818) = raw13448 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13448; decide +kernel
    rw [ha]
    exact (canonical13448 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA818 + difference 5 0) (sourceB818 + difference 0 5) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA818 + difference 5 0) (sourceB818 + difference 0 5) sourceC818) = raw12653 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw12653; decide +kernel
    rw [ha]
    exact (canonical12653 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA818 + difference 5 1) (sourceB818 + difference 1 5) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA818 + difference 5 1) (sourceB818 + difference 1 5) sourceC818) = raw11669 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw11669; decide +kernel
    rw [ha]
    exact (canonical11669 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA818 + difference 5 2) (sourceB818 + difference 2 5) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA818 + difference 5 2) (sourceB818 + difference 2 5) sourceC818) = raw12191 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw12191; decide +kernel
    rw [ha]
    exact (canonical12191 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA818 + difference 5 3) (sourceB818 + difference 3 5) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA818 + difference 5 3) (sourceB818 + difference 3 5) sourceC818) = raw12467 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw12467; decide +kernel
    rw [ha]
    exact (canonical12467 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA818 + difference 5 4) (sourceB818 + difference 4 5) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA818 + difference 5 4) (sourceB818 + difference 4 5) sourceC818) = raw12654 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw12654; decide +kernel
    rw [ha]
    exact (canonical12654 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA818 sourceB818 sourceC818
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm818, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq819 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm819 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA819 + difference 0 1) (sourceB819 + difference 1 0) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2741) := by
    have ha : (tripleCharges (sourceA819 + difference 0 1) (sourceB819 + difference 1 0) sourceC819) = raw13082 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13082; decide +kernel
    rw [ha]
    exact (canonical13082 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA819 + difference 0 2) (sourceB819 + difference 2 0) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2741) := by
    have ha : (tripleCharges (sourceA819 + difference 0 2) (sourceB819 + difference 2 0) sourceC819) = raw13449 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13449; decide +kernel
    rw [ha]
    exact (canonical13449 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA819 + difference 0 3) (sourceB819 + difference 3 0) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2703) := by
    have ha : (tripleCharges (sourceA819 + difference 0 3) (sourceB819 + difference 3 0) sourceC819) = raw13352 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13352; decide +kernel
    rw [ha]
    exact (canonical13352 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA819 + difference 0 4) (sourceB819 + difference 4 0) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2703) := by
    have ha : (tripleCharges (sourceA819 + difference 0 4) (sourceB819 + difference 4 0) sourceC819) = raw13450 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13450; decide +kernel
    rw [ha]
    exact (canonical13450 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA819 + difference 0 5) (sourceB819 + difference 5 0) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2703) := by
    have ha : (tripleCharges (sourceA819 + difference 0 5) (sourceB819 + difference 5 0) sourceC819) = raw13451 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13451; decide +kernel
    rw [ha]
    exact (canonical13451 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA819 + difference 1 0) (sourceB819 + difference 0 1) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA819 + difference 1 0) (sourceB819 + difference 0 1) sourceC819) = raw13452 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13452; decide +kernel
    rw [ha]
    exact (canonical13452 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA819 + difference 1 2) (sourceB819 + difference 2 1) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA819 + difference 1 2) (sourceB819 + difference 2 1) sourceC819) = raw13453 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13453; decide +kernel
    rw [ha]
    exact (canonical13453 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA819 + difference 1 3) (sourceB819 + difference 3 1) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA819 + difference 1 3) (sourceB819 + difference 3 1) sourceC819) = raw13357 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13357; decide +kernel
    rw [ha]
    exact (canonical13357 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA819 + difference 1 4) (sourceB819 + difference 4 1) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA819 + difference 1 4) (sourceB819 + difference 4 1) sourceC819) = raw13454 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13454; decide +kernel
    rw [ha]
    exact (canonical13454 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA819 + difference 1 5) (sourceB819 + difference 5 1) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA819 + difference 1 5) (sourceB819 + difference 5 1) sourceC819) = raw13455 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13455; decide +kernel
    rw [ha]
    exact (canonical13455 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA819 + difference 2 0) (sourceB819 + difference 0 2) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA819 + difference 2 0) (sourceB819 + difference 0 2) sourceC819) = raw13085 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13085; decide +kernel
    rw [ha]
    exact (canonical13085 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA819 + difference 2 1) (sourceB819 + difference 1 2) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA819 + difference 2 1) (sourceB819 + difference 1 2) sourceC819) = raw12049 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw12049; decide +kernel
    rw [ha]
    exact (canonical12049 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA819 + difference 2 3) (sourceB819 + difference 3 2) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA819 + difference 2 3) (sourceB819 + difference 3 2) sourceC819) = raw12915 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw12915; decide +kernel
    rw [ha]
    exact (canonical12915 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA819 + difference 2 4) (sourceB819 + difference 4 2) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA819 + difference 2 4) (sourceB819 + difference 4 2) sourceC819) = raw13087 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13087; decide +kernel
    rw [ha]
    exact (canonical13087 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA819 + difference 2 5) (sourceB819 + difference 5 2) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA819 + difference 2 5) (sourceB819 + difference 5 2) sourceC819) = raw13088 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13088; decide +kernel
    rw [ha]
    exact (canonical13088 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA819 + difference 3 0) (sourceB819 + difference 0 3) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3226) := by
    have ha : (tripleCharges (sourceA819 + difference 3 0) (sourceB819 + difference 0 3) sourceC819) = raw13456 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13456; decide +kernel
    rw [ha]
    exact (canonical13456 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA819 + difference 3 1) (sourceB819 + difference 1 3) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA819 + difference 3 1) (sourceB819 + difference 1 3) sourceC819) = raw13093 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13093; decide +kernel
    rw [ha]
    exact (canonical13093 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA819 + difference 3 2) (sourceB819 + difference 2 3) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA819 + difference 3 2) (sourceB819 + difference 2 3) sourceC819) = raw13457 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13457; decide +kernel
    rw [ha]
    exact (canonical13457 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA819 + difference 3 4) (sourceB819 + difference 4 3) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA819 + difference 3 4) (sourceB819 + difference 4 3) sourceC819) = raw13458 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13458; decide +kernel
    rw [ha]
    exact (canonical13458 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA819 + difference 3 5) (sourceB819 + difference 5 3) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA819 + difference 3 5) (sourceB819 + difference 5 3) sourceC819) = raw13459 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13459; decide +kernel
    rw [ha]
    exact (canonical13459 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA819 + difference 4 0) (sourceB819 + difference 0 4) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3226) := by
    have ha : (tripleCharges (sourceA819 + difference 4 0) (sourceB819 + difference 0 4) sourceC819) = raw13460 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13460; decide +kernel
    rw [ha]
    exact (canonical13460 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA819 + difference 4 1) (sourceB819 + difference 1 4) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA819 + difference 4 1) (sourceB819 + difference 1 4) sourceC819) = raw13097 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13097; decide +kernel
    rw [ha]
    exact (canonical13097 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA819 + difference 4 2) (sourceB819 + difference 2 4) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA819 + difference 4 2) (sourceB819 + difference 2 4) sourceC819) = raw13461 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13461; decide +kernel
    rw [ha]
    exact (canonical13461 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA819 + difference 4 3) (sourceB819 + difference 3 4) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA819 + difference 4 3) (sourceB819 + difference 3 4) sourceC819) = raw13363 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13363; decide +kernel
    rw [ha]
    exact (canonical13363 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA819 + difference 4 5) (sourceB819 + difference 5 4) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA819 + difference 4 5) (sourceB819 + difference 5 4) sourceC819) = raw13462 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13462; decide +kernel
    rw [ha]
    exact (canonical13462 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA819 + difference 5 0) (sourceB819 + difference 0 5) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3226) := by
    have ha : (tripleCharges (sourceA819 + difference 5 0) (sourceB819 + difference 0 5) sourceC819) = raw13358 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13358; decide +kernel
    rw [ha]
    exact (canonical13358 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA819 + difference 5 1) (sourceB819 + difference 1 5) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA819 + difference 5 1) (sourceB819 + difference 1 5) sourceC819) = raw11729 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw11729; decide +kernel
    rw [ha]
    exact (canonical11729 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA819 + difference 5 2) (sourceB819 + difference 2 5) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA819 + difference 5 2) (sourceB819 + difference 2 5) sourceC819) = raw12212 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw12212; decide +kernel
    rw [ha]
    exact (canonical12212 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA819 + difference 5 3) (sourceB819 + difference 3 5) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA819 + difference 5 3) (sourceB819 + difference 3 5) sourceC819) = raw12503 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw12503; decide +kernel
    rw [ha]
    exact (canonical12503 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA819 + difference 5 4) (sourceB819 + difference 4 5) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA819 + difference 5 4) (sourceB819 + difference 4 5) sourceC819) = raw13359 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13359; decide +kernel
    rw [ha]
    exact (canonical13359 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA819 sourceB819 sourceC819
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm819, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq823 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm823 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA823 + difference 0 0) (sourceB823 + difference 0 0) sourceC823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA823 + difference 0 0) (sourceB823 + difference 0 0) sourceC823) = raw13553 := by
      apply Matrix.ext; unfold tripleCharges sourceA823 sourceB823 sourceC823 difference raw13553; decide +kernel
    rw [ha]
    exact (canonical13553 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA823 + difference 0 1) (sourceB823 + difference 1 0) sourceC823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA823 + difference 0 1) (sourceB823 + difference 1 0) sourceC823) = raw13554 := by
      apply Matrix.ext; unfold tripleCharges sourceA823 sourceB823 sourceC823 difference raw13554; decide +kernel
    rw [ha]
    exact (canonical13554 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA823 + difference 0 2) (sourceB823 + difference 2 0) sourceC823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA823 + difference 0 2) (sourceB823 + difference 2 0) sourceC823) = raw13555 := by
      apply Matrix.ext; unfold tripleCharges sourceA823 sourceB823 sourceC823 difference raw13555; decide +kernel
    rw [ha]
    exact (canonical13555 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA823 + difference 0 3) (sourceB823 + difference 3 0) sourceC823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA823 + difference 0 3) (sourceB823 + difference 3 0) sourceC823) = raw13556 := by
      apply Matrix.ext; unfold tripleCharges sourceA823 sourceB823 sourceC823 difference raw13556; decide +kernel
    rw [ha]
    exact (canonical13556 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA823 + difference 0 4) (sourceB823 + difference 4 0) sourceC823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA823 + difference 0 4) (sourceB823 + difference 4 0) sourceC823) = raw13557 := by
      apply Matrix.ext; unfold tripleCharges sourceA823 sourceB823 sourceC823 difference raw13557; decide +kernel
    rw [ha]
    exact (canonical13557 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA823 + difference 0 5) (sourceB823 + difference 5 0) sourceC823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3904) := by
    have ha : (tripleCharges (sourceA823 + difference 0 5) (sourceB823 + difference 5 0) sourceC823) = raw13558 := by
      apply Matrix.ext; unfold tripleCharges sourceA823 sourceB823 sourceC823 difference raw13558; decide +kernel
    rw [ha]
    exact (canonical13558 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA823 + sourceB823) sourceC823) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA823 + sourceB823) sourceC823) = raw13559 := by
      apply Matrix.ext; unfold doubleCharges sourceA823 sourceB823 sourceC823 raw13559; decide +kernel
    rw [ha]
    exact (canonical13559 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA823 sourceB823 sourceC823
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm823, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq824 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm824 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA824 + difference 0 0) (sourceB824 + difference 0 0) sourceC824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA824 + difference 0 0) (sourceB824 + difference 0 0) sourceC824) = raw13553 := by
      apply Matrix.ext; unfold tripleCharges sourceA824 sourceB824 sourceC824 difference raw13553; decide +kernel
    rw [ha]
    exact (canonical13553 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA824 + difference 1 0) (sourceB824 + difference 0 1) sourceC824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA824 + difference 1 0) (sourceB824 + difference 0 1) sourceC824) = raw13560 := by
      apply Matrix.ext; unfold tripleCharges sourceA824 sourceB824 sourceC824 difference raw13560; decide +kernel
    rw [ha]
    exact (canonical13560 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA824 + difference 2 0) (sourceB824 + difference 0 2) sourceC824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA824 + difference 2 0) (sourceB824 + difference 0 2) sourceC824) = raw13561 := by
      apply Matrix.ext; unfold tripleCharges sourceA824 sourceB824 sourceC824 difference raw13561; decide +kernel
    rw [ha]
    exact (canonical13561 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA824 + difference 3 0) (sourceB824 + difference 0 3) sourceC824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA824 + difference 3 0) (sourceB824 + difference 0 3) sourceC824) = raw13562 := by
      apply Matrix.ext; unfold tripleCharges sourceA824 sourceB824 sourceC824 difference raw13562; decide +kernel
    rw [ha]
    exact (canonical13562 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA824 + difference 4 0) (sourceB824 + difference 0 4) sourceC824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA824 + difference 4 0) (sourceB824 + difference 0 4) sourceC824) = raw13563 := by
      apply Matrix.ext; unfold tripleCharges sourceA824 sourceB824 sourceC824 difference raw13563; decide +kernel
    rw [ha]
    exact (canonical13563 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA824 + difference 5 0) (sourceB824 + difference 0 5) sourceC824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA824 + difference 5 0) (sourceB824 + difference 0 5) sourceC824) = raw13564 := by
      apply Matrix.ext; unfold tripleCharges sourceA824 sourceB824 sourceC824 difference raw13564; decide +kernel
    rw [ha]
    exact (canonical13564 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA824 + sourceB824) sourceC824) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA824 + sourceB824) sourceC824) = raw13559 := by
      apply Matrix.ext; unfold doubleCharges sourceA824 sourceB824 sourceC824 raw13559; decide +kernel
    rw [ha]
    exact (canonical13559 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA824 sourceB824 sourceC824
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm824, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq825 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm825 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA825 + difference 1 0) (sourceB825 + difference 0 1) sourceC825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA825 + difference 1 0) (sourceB825 + difference 0 1) sourceC825) = raw13560 := by
      apply Matrix.ext; unfold tripleCharges sourceA825 sourceB825 sourceC825 difference raw13560; decide +kernel
    rw [ha]
    exact (canonical13560 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA825 + difference 1 1) (sourceB825 + difference 1 1) sourceC825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA825 + difference 1 1) (sourceB825 + difference 1 1) sourceC825) = raw13553 := by
      apply Matrix.ext; unfold tripleCharges sourceA825 sourceB825 sourceC825 difference raw13553; decide +kernel
    rw [ha]
    exact (canonical13553 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA825 + difference 1 2) (sourceB825 + difference 2 1) sourceC825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2589) := by
    have ha : (tripleCharges (sourceA825 + difference 1 2) (sourceB825 + difference 2 1) sourceC825) = raw13565 := by
      apply Matrix.ext; unfold tripleCharges sourceA825 sourceB825 sourceC825 difference raw13565; decide +kernel
    rw [ha]
    exact (canonical13565 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA825 + difference 1 3) (sourceB825 + difference 3 1) sourceC825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA825 + difference 1 3) (sourceB825 + difference 3 1) sourceC825) = raw13566 := by
      apply Matrix.ext; unfold tripleCharges sourceA825 sourceB825 sourceC825 difference raw13566; decide +kernel
    rw [ha]
    exact (canonical13566 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA825 + difference 1 4) (sourceB825 + difference 4 1) sourceC825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA825 + difference 1 4) (sourceB825 + difference 4 1) sourceC825) = raw13567 := by
      apply Matrix.ext; unfold tripleCharges sourceA825 sourceB825 sourceC825 difference raw13567; decide +kernel
    rw [ha]
    exact (canonical13567 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA825 + difference 1 5) (sourceB825 + difference 5 1) sourceC825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2741) := by
    have ha : (tripleCharges (sourceA825 + difference 1 5) (sourceB825 + difference 5 1) sourceC825) = raw13568 := by
      apply Matrix.ext; unfold tripleCharges sourceA825 sourceB825 sourceC825 difference raw13568; decide +kernel
    rw [ha]
    exact (canonical13568 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA825 + sourceB825) sourceC825) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA825 + sourceB825) sourceC825) = raw13559 := by
      apply Matrix.ext; unfold doubleCharges sourceA825 sourceB825 sourceC825 raw13559; decide +kernel
    rw [ha]
    exact (canonical13559 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA825 sourceB825 sourceC825
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm825, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq826 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm826 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA826 + difference 0 1) (sourceB826 + difference 1 0) sourceC826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA826 + difference 0 1) (sourceB826 + difference 1 0) sourceC826) = raw13554 := by
      apply Matrix.ext; unfold tripleCharges sourceA826 sourceB826 sourceC826 difference raw13554; decide +kernel
    rw [ha]
    exact (canonical13554 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA826 + difference 1 1) (sourceB826 + difference 1 1) sourceC826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA826 + difference 1 1) (sourceB826 + difference 1 1) sourceC826) = raw13553 := by
      apply Matrix.ext; unfold tripleCharges sourceA826 sourceB826 sourceC826 difference raw13553; decide +kernel
    rw [ha]
    exact (canonical13553 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA826 + difference 2 1) (sourceB826 + difference 1 2) sourceC826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2631) := by
    have ha : (tripleCharges (sourceA826 + difference 2 1) (sourceB826 + difference 1 2) sourceC826) = raw13569 := by
      apply Matrix.ext; unfold tripleCharges sourceA826 sourceB826 sourceC826 difference raw13569; decide +kernel
    rw [ha]
    exact (canonical13569 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA826 + difference 3 1) (sourceB826 + difference 1 3) sourceC826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2633) := by
    have ha : (tripleCharges (sourceA826 + difference 3 1) (sourceB826 + difference 1 3) sourceC826) = raw13570 := by
      apply Matrix.ext; unfold tripleCharges sourceA826 sourceB826 sourceC826 difference raw13570; decide +kernel
    rw [ha]
    exact (canonical13570 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA826 + difference 4 1) (sourceB826 + difference 1 4) sourceC826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2633) := by
    have ha : (tripleCharges (sourceA826 + difference 4 1) (sourceB826 + difference 1 4) sourceC826) = raw13571 := by
      apply Matrix.ext; unfold tripleCharges sourceA826 sourceB826 sourceC826 difference raw13571; decide +kernel
    rw [ha]
    exact (canonical13571 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA826 + difference 5 1) (sourceB826 + difference 1 5) sourceC826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2641) := by
    have ha : (tripleCharges (sourceA826 + difference 5 1) (sourceB826 + difference 1 5) sourceC826) = raw13572 := by
      apply Matrix.ext; unfold tripleCharges sourceA826 sourceB826 sourceC826 difference raw13572; decide +kernel
    rw [ha]
    exact (canonical13572 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA826 + sourceB826) sourceC826) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA826 + sourceB826) sourceC826) = raw13559 := by
      apply Matrix.ext; unfold doubleCharges sourceA826 sourceB826 sourceC826 raw13559; decide +kernel
    rw [ha]
    exact (canonical13559 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA826 sourceB826 sourceC826
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm826, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck704 : Integer.Sparse.reindex keyMap MixedData.row704 = numericRow704 := by decide +kernel

theorem numericCheck704 (x : Master → ℝ) : Integer.Sparse.eval numericRow704 x =
    (1 : ℝ) * reducedSource704 x := by
  norm_num [numericRow704, reducedSource704, Integer.Sparse.eval, Sparse.eval, nodeValue2105, nodeValue3073, nodeValue3571, nodeValue3581, nodeValue4083]

theorem reindexCheck705 : Integer.Sparse.reindex keyMap MixedData.row705 = numericRow705 := by decide +kernel

theorem numericCheck705 (x : Master → ℝ) : Integer.Sparse.eval numericRow705 x =
    (1 : ℝ) * reducedSource705 x := by
  norm_num [numericRow705, reducedSource705, Integer.Sparse.eval, Sparse.eval, nodeValue3489, nodeValue3550, nodeValue3551, nodeValue3571, nodeValue4083]

theorem reindexCheck706 : Integer.Sparse.reindex keyMap MixedData.row706 = numericRow706 := by decide +kernel

theorem numericCheck706 (x : Master → ℝ) : Integer.Sparse.eval numericRow706 x =
    (2880 : ℝ) * reducedSource706 x := by
  norm_num [numericRow706, reducedSource706, Integer.Sparse.eval, Sparse.eval, nodeValue4581, nodeValue4601, nodeValue5192, nodeValue5202, nodeValue5284, nodeValue5292, nodeValue5447, nodeValue5452]
  ring

theorem reindexCheck708 : Integer.Sparse.reindex keyMap MixedData.row708 = numericRow708 := by decide +kernel

theorem numericCheck708 (x : Master → ℝ) : Integer.Sparse.eval numericRow708 x =
    (2880 : ℝ) * reducedSource708 x := by
  norm_num [numericRow708, reducedSource708, Integer.Sparse.eval, Sparse.eval, nodeValue4885, nodeValue4887, nodeValue5247, nodeValue5273, nodeValue5281, nodeValue5286, nodeValue5292, nodeValue5301]
  ring

theorem reindexCheck709 : Integer.Sparse.reindex keyMap MixedData.row709 = numericRow709 := by decide +kernel

theorem numericCheck709 (x : Master → ℝ) : Integer.Sparse.eval numericRow709 x =
    (720 : ℝ) * reducedSource709 x := by
  norm_num [numericRow709, reducedSource709, Integer.Sparse.eval, Sparse.eval, nodeValue2703, nodeValue2741, nodeValue3023, nodeValue3053, nodeValue3074, nodeValue3100, nodeValue3221, nodeValue3226]
  ring

theorem reindexCheck713 : Integer.Sparse.reindex keyMap MixedData.row713 = numericRow713 := by decide +kernel

theorem numericCheck713 (x : Master → ℝ) : Integer.Sparse.eval numericRow713 x =
    (1 : ℝ) * reducedSource713 x := by
  norm_num [numericRow713, reducedSource713, Integer.Sparse.eval, Sparse.eval, nodeValue2764, nodeValue3849, nodeValue3885, nodeValue3904, nodeValue3910, nodeValue4091]

theorem reindexCheck714 : Integer.Sparse.reindex keyMap MixedData.row714 = numericRow714 := by decide +kernel

theorem numericCheck714 (x : Master → ℝ) : Integer.Sparse.eval numericRow714 x =
    (1 : ℝ) * reducedSource714 x := by
  norm_num [numericRow714, reducedSource714, Integer.Sparse.eval, Sparse.eval, nodeValue1260, nodeValue1262, nodeValue1270, nodeValue1293, nodeValue2764, nodeValue4091]

theorem reindexCheck715 : Integer.Sparse.reindex keyMap MixedData.row715 = numericRow715 := by decide +kernel

theorem numericCheck715 (x : Master → ℝ) : Integer.Sparse.eval numericRow715 x =
    (1 : ℝ) * reducedSource715 x := by
  norm_num [numericRow715, reducedSource715, Integer.Sparse.eval, Sparse.eval, nodeValue1293, nodeValue2589, nodeValue2741, nodeValue2764, nodeValue4091]

theorem reindexCheck716 : Integer.Sparse.reindex keyMap MixedData.row716 = numericRow716 := by decide +kernel

theorem numericCheck716 (x : Master → ℝ) : Integer.Sparse.eval numericRow716 x =
    (1 : ℝ) * reducedSource716 x := by
  norm_num [numericRow716, reducedSource716, Integer.Sparse.eval, Sparse.eval, nodeValue2631, nodeValue2633, nodeValue2641, nodeValue2764, nodeValue3885, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero704 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource704 (mixedVector B) = 0 := by
  have h2105 : mixedVector B (Sum.inr 2105) = Sparse.eval nodeValue2105 (mixedVector B) := by
    change mixedMoment B node2105 node2105Labels = _
    exact sound2105 B hB hF
  have h3073 : mixedVector B (Sum.inr 3073) = Sparse.eval nodeValue3073 (mixedVector B) := by
    change mixedMoment B node3073 node3073Labels = _
    exact sound3073 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h3581 : mixedVector B (Sum.inr 3581) = Sparse.eval nodeValue3581 (mixedVector B) := by
    change mixedMoment B node3581 node3581Labels = _
    exact sound3581 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm814, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2105, h3073, h3571, h3581, h4083, reducedSource704] using sourceEq814 B hB

theorem rowSound704 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row704 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck704, numericCheck704, reducedZero704 B hB hF, mul_zero]

theorem reducedZero705 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource705 (mixedVector B) = 0 := by
  have h3489 : mixedVector B (Sum.inr 3489) = Sparse.eval nodeValue3489 (mixedVector B) := by
    change mixedMoment B node3489 node3489Labels = _
    exact sound3489 B hB hF
  have h3550 : mixedVector B (Sum.inr 3550) = Sparse.eval nodeValue3550 (mixedVector B) := by
    change mixedMoment B node3550 node3550Labels = _
    exact sound3550 B hB hF
  have h3551 : mixedVector B (Sum.inr 3551) = Sparse.eval nodeValue3551 (mixedVector B) := by
    change mixedMoment B node3551 node3551Labels = _
    exact sound3551 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm815, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3489, h3550, h3551, h3571, h4083, reducedSource705] using sourceEq815 B hB

theorem rowSound705 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row705 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck705, numericCheck705, reducedZero705 B hB hF, mul_zero]

theorem reducedZero706 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource706 (mixedVector B) = 0 := by
  have h4581 : mixedVector B (Sum.inr 4581) = Sparse.eval nodeValue4581 (mixedVector B) := by
    change mixedMoment B node4581 node4581Labels = _
    exact sound4581 B hB hF
  have h4601 : mixedVector B (Sum.inr 4601) = Sparse.eval nodeValue4601 (mixedVector B) := by
    change mixedMoment B node4601 node4601Labels = _
    exact sound4601 B hB hF
  have h5192 : mixedVector B (Sum.inr 5192) = Sparse.eval nodeValue5192 (mixedVector B) := by
    change mixedMoment B node5192 node5192Labels = _
    exact sound5192 B hB hF
  have h5202 : mixedVector B (Sum.inr 5202) = Sparse.eval nodeValue5202 (mixedVector B) := by
    change mixedMoment B node5202 node5202Labels = _
    exact sound5202 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292_e B hB hF
  have h5447 : mixedVector B (Sum.inr 5447) = Sparse.eval nodeValue5447 (mixedVector B) := by
    change mixedMoment B node5447 node5447Labels = _
    exact sound5447 B hB hF
  have h5452 : mixedVector B (Sum.inr 5452) = Sparse.eval nodeValue5452 (mixedVector B) := by
    change mixedMoment B node5452 node5452Labels = _
    exact sound5452_e B hB hF
  simpa only [sourceForm816, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4581, h4601, h5192, h5202, h5284, h5292, h5447, h5452, reducedSource706] using sourceEq816 B hB

theorem rowSound706 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row706 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck706, numericCheck706, reducedZero706 B hB hF, mul_zero]

theorem reducedZero708 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource708 (mixedVector B) = 0 := by
  have h4885 : mixedVector B (Sum.inr 4885) = Sparse.eval nodeValue4885 (mixedVector B) := by
    change mixedMoment B node4885 node4885Labels = _
    exact sound4885 B hB hF
  have h4887 : mixedVector B (Sum.inr 4887) = Sparse.eval nodeValue4887 (mixedVector B) := by
    change mixedMoment B node4887 node4887Labels = _
    exact sound4887 B hB hF
  have h5247 : mixedVector B (Sum.inr 5247) = Sparse.eval nodeValue5247 (mixedVector B) := by
    change mixedMoment B node5247 node5247Labels = _
    exact sound5247 B hB hF
  have h5273 : mixedVector B (Sum.inr 5273) = Sparse.eval nodeValue5273 (mixedVector B) := by
    change mixedMoment B node5273 node5273Labels = _
    exact sound5273 B hB hF
  have h5281 : mixedVector B (Sum.inr 5281) = Sparse.eval nodeValue5281 (mixedVector B) := by
    change mixedMoment B node5281 node5281Labels = _
    exact sound5281 B hB hF
  have h5286 : mixedVector B (Sum.inr 5286) = Sparse.eval nodeValue5286 (mixedVector B) := by
    change mixedMoment B node5286 node5286Labels = _
    exact sound5286 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292_e B hB hF
  have h5301 : mixedVector B (Sum.inr 5301) = Sparse.eval nodeValue5301 (mixedVector B) := by
    change mixedMoment B node5301 node5301Labels = _
    exact sound5301 B hB hF
  simpa only [sourceForm818, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4885, h4887, h5247, h5273, h5281, h5286, h5292, h5301, reducedSource708] using sourceEq818 B hB

theorem rowSound708 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row708 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck708, numericCheck708, reducedZero708 B hB hF, mul_zero]

theorem reducedZero709 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource709 (mixedVector B) = 0 := by
  have h2703 : mixedVector B (Sum.inr 2703) = Sparse.eval nodeValue2703 (mixedVector B) := by
    change mixedMoment B node2703 node2703Labels = _
    exact sound2703 B hB hF
  have h2741 : mixedVector B (Sum.inr 2741) = Sparse.eval nodeValue2741 (mixedVector B) := by
    change mixedMoment B node2741 node2741Labels = _
    exact sound2741 B hB hF
  have h3023 : mixedVector B (Sum.inr 3023) = Sparse.eval nodeValue3023 (mixedVector B) := by
    change mixedMoment B node3023 node3023Labels = _
    exact sound3023 B hB hF
  have h3053 : mixedVector B (Sum.inr 3053) = Sparse.eval nodeValue3053 (mixedVector B) := by
    change mixedMoment B node3053 node3053Labels = _
    exact sound3053 B hB hF
  have h3074 : mixedVector B (Sum.inr 3074) = Sparse.eval nodeValue3074 (mixedVector B) := by
    change mixedMoment B node3074 node3074Labels = _
    exact sound3074 B hB hF
  have h3100 : mixedVector B (Sum.inr 3100) = Sparse.eval nodeValue3100 (mixedVector B) := by
    change mixedMoment B node3100 node3100Labels = _
    exact sound3100_e B hB hF
  have h3221 : mixedVector B (Sum.inr 3221) = Sparse.eval nodeValue3221 (mixedVector B) := by
    change mixedMoment B node3221 node3221Labels = _
    exact sound3221 B hB hF
  have h3226 : mixedVector B (Sum.inr 3226) = Sparse.eval nodeValue3226 (mixedVector B) := by
    change mixedMoment B node3226 node3226Labels = _
    exact sound3226_e B hB hF
  simpa only [sourceForm819, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2703, h2741, h3023, h3053, h3074, h3100, h3221, h3226, reducedSource709] using sourceEq819 B hB

theorem rowSound709 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row709 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck709, numericCheck709, reducedZero709 B hB hF, mul_zero]

theorem reducedZero713 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource713 (mixedVector B) = 0 := by
  have h2764 : mixedVector B (Sum.inr 2764) = Sparse.eval nodeValue2764 (mixedVector B) := by
    change mixedMoment B node2764 node2764Labels = _
    exact sound2764 B hB hF
  have h3849 : mixedVector B (Sum.inr 3849) = Sparse.eval nodeValue3849 (mixedVector B) := by
    change mixedMoment B node3849 node3849Labels = _
    exact sound3849 B hB hF
  have h3885 : mixedVector B (Sum.inr 3885) = Sparse.eval nodeValue3885 (mixedVector B) := by
    change mixedMoment B node3885 node3885Labels = _
    exact sound3885 B hB hF
  have h3904 : mixedVector B (Sum.inr 3904) = Sparse.eval nodeValue3904 (mixedVector B) := by
    change mixedMoment B node3904 node3904Labels = _
    exact sound3904 B hB hF
  have h3910 : mixedVector B (Sum.inr 3910) = Sparse.eval nodeValue3910 (mixedVector B) := by
    change mixedMoment B node3910 node3910Labels = _
    exact sound3910 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm823, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2764, h3849, h3885, h3904, h3910, h4091, reducedSource713] using sourceEq823 B hB

theorem rowSound713 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row713 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck713, numericCheck713, reducedZero713 B hB hF, mul_zero]

theorem reducedZero714 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource714 (mixedVector B) = 0 := by
  have h1260 : mixedVector B (Sum.inr 1260) = Sparse.eval nodeValue1260 (mixedVector B) := by
    change mixedMoment B node1260 node1260Labels = _
    exact sound1260 B hB hF
  have h1262 : mixedVector B (Sum.inr 1262) = Sparse.eval nodeValue1262 (mixedVector B) := by
    change mixedMoment B node1262 node1262Labels = _
    exact sound1262 B hB hF
  have h1270 : mixedVector B (Sum.inr 1270) = Sparse.eval nodeValue1270 (mixedVector B) := by
    change mixedMoment B node1270 node1270Labels = _
    exact sound1270 B hB hF
  have h1293 : mixedVector B (Sum.inr 1293) = Sparse.eval nodeValue1293 (mixedVector B) := by
    change mixedMoment B node1293 node1293Labels = _
    exact sound1293 B hB hF
  have h2764 : mixedVector B (Sum.inr 2764) = Sparse.eval nodeValue2764 (mixedVector B) := by
    change mixedMoment B node2764 node2764Labels = _
    exact sound2764 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm824, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1260, h1262, h1270, h1293, h2764, h4091, reducedSource714] using sourceEq824 B hB

theorem rowSound714 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row714 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck714, numericCheck714, reducedZero714 B hB hF, mul_zero]

theorem reducedZero715 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource715 (mixedVector B) = 0 := by
  have h1293 : mixedVector B (Sum.inr 1293) = Sparse.eval nodeValue1293 (mixedVector B) := by
    change mixedMoment B node1293 node1293Labels = _
    exact sound1293 B hB hF
  have h2589 : mixedVector B (Sum.inr 2589) = Sparse.eval nodeValue2589 (mixedVector B) := by
    change mixedMoment B node2589 node2589Labels = _
    exact sound2589 B hB hF
  have h2741 : mixedVector B (Sum.inr 2741) = Sparse.eval nodeValue2741 (mixedVector B) := by
    change mixedMoment B node2741 node2741Labels = _
    exact sound2741 B hB hF
  have h2764 : mixedVector B (Sum.inr 2764) = Sparse.eval nodeValue2764 (mixedVector B) := by
    change mixedMoment B node2764 node2764Labels = _
    exact sound2764 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm825, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1293, h2589, h2741, h2764, h4091, reducedSource715] using sourceEq825 B hB

theorem rowSound715 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row715 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck715, numericCheck715, reducedZero715 B hB hF, mul_zero]

theorem reducedZero716 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource716 (mixedVector B) = 0 := by
  have h2631 : mixedVector B (Sum.inr 2631) = Sparse.eval nodeValue2631 (mixedVector B) := by
    change mixedMoment B node2631 node2631Labels = _
    exact sound2631 B hB hF
  have h2633 : mixedVector B (Sum.inr 2633) = Sparse.eval nodeValue2633 (mixedVector B) := by
    change mixedMoment B node2633 node2633Labels = _
    exact sound2633 B hB hF
  have h2641 : mixedVector B (Sum.inr 2641) = Sparse.eval nodeValue2641 (mixedVector B) := by
    change mixedMoment B node2641 node2641Labels = _
    exact sound2641 B hB hF
  have h2764 : mixedVector B (Sum.inr 2764) = Sparse.eval nodeValue2764 (mixedVector B) := by
    change mixedMoment B node2764 node2764Labels = _
    exact sound2764 B hB hF
  have h3885 : mixedVector B (Sum.inr 3885) = Sparse.eval nodeValue3885 (mixedVector B) := by
    change mixedMoment B node3885 node3885Labels = _
    exact sound3885 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm826, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2631, h2633, h2641, h2764, h3885, h4091, reducedSource716] using sourceEq826 B hB

theorem rowSound716 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row716 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck716, numericCheck716, reducedZero716 B hB hF, mul_zero]

theorem sourceRowsAt704 : MixedData.sourceRows (704 : Fin 2425) =
    MixedData.row704 := by decide +kernel

theorem sourceRowsAt705 : MixedData.sourceRows (705 : Fin 2425) =
    MixedData.row705 := by decide +kernel

theorem sourceRowsAt706 : MixedData.sourceRows (706 : Fin 2425) =
    MixedData.row706 := by decide +kernel

theorem sourceRowsAt707 : MixedData.sourceRows (707 : Fin 2425) =
    MixedData.row707 := by decide +kernel

theorem sourceRowsAt708 : MixedData.sourceRows (708 : Fin 2425) =
    MixedData.row708 := by decide +kernel

theorem sourceRowsAt709 : MixedData.sourceRows (709 : Fin 2425) =
    MixedData.row709 := by decide +kernel

theorem sourceRowsAt710 : MixedData.sourceRows (710 : Fin 2425) =
    MixedData.row710 := by decide +kernel

theorem sourceRowsAt711 : MixedData.sourceRows (711 : Fin 2425) =
    MixedData.row711 := by decide +kernel

theorem sourceRowsAt712 : MixedData.sourceRows (712 : Fin 2425) =
    MixedData.row712 := by decide +kernel

theorem sourceRowsAt713 : MixedData.sourceRows (713 : Fin 2425) =
    MixedData.row713 := by decide +kernel

theorem sourceRowsAt714 : MixedData.sourceRows (714 : Fin 2425) =
    MixedData.row714 := by decide +kernel

theorem sourceRowsAt715 : MixedData.sourceRows (715 : Fin 2425) =
    MixedData.row715 := by decide +kernel

theorem sourceRowsAt716 : MixedData.sourceRows (716 : Fin 2425) =
    MixedData.row716 := by decide +kernel

theorem sourceRowsAt717 : MixedData.sourceRows (717 : Fin 2425) =
    MixedData.row717 := by decide +kernel

theorem sourceRowsAt718 : MixedData.sourceRows (718 : Fin 2425) =
    MixedData.row718 := by decide +kernel

theorem sourceRowsAt719 : MixedData.sourceRows (719 : Fin 2425) =
    MixedData.row719 := by decide +kernel

theorem chunkSound44_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 44) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 704 ∨ k.val = 705 ∨ k.val = 706 ∨ k.val = 707 ∨ k.val = 708 ∨ k.val = 709 ∨ k.val = 710 ∨ k.val = 711 ∨ k.val = 712 ∨ k.val = 713 ∨ k.val = 714 ∨ k.val = 715 ∨ k.val = 716 ∨ k.val = 717 ∨ k.val = 718 ∨ k.val = 719 := by omega
  rcases heq with h704 | h705 | h706 | h707 | h708 | h709 | h710 | h711 | h712 | h713 | h714 | h715 | h716 | h717 | h718 | h719
  · have he : k = (704 : Fin 2425) := Fin.ext h704
    subst k
    rw [sourceRowsAt704]
    exact rowSound704 B hB hF
  · have he : k = (705 : Fin 2425) := Fin.ext h705
    subst k
    rw [sourceRowsAt705]
    exact rowSound705 B hB hF
  · have he : k = (706 : Fin 2425) := Fin.ext h706
    subst k
    rw [sourceRowsAt706]
    exact rowSound706 B hB hF
  · have he : k = (707 : Fin 2425) := Fin.ext h707
    subst k
    rw [sourceRowsAt707]
    exact rowSound707_e B hB hF
  · have he : k = (708 : Fin 2425) := Fin.ext h708
    subst k
    rw [sourceRowsAt708]
    exact rowSound708 B hB hF
  · have he : k = (709 : Fin 2425) := Fin.ext h709
    subst k
    rw [sourceRowsAt709]
    exact rowSound709 B hB hF
  · have he : k = (710 : Fin 2425) := Fin.ext h710
    subst k
    rw [sourceRowsAt710]
    exact rowSound710_e B hB hF
  · have he : k = (711 : Fin 2425) := Fin.ext h711
    subst k
    rw [sourceRowsAt711]
    exact rowSound711_e B hB hF
  · have he : k = (712 : Fin 2425) := Fin.ext h712
    subst k
    rw [sourceRowsAt712]
    exact rowSound712_e B hB hF
  · have he : k = (713 : Fin 2425) := Fin.ext h713
    subst k
    rw [sourceRowsAt713]
    exact rowSound713 B hB hF
  · have he : k = (714 : Fin 2425) := Fin.ext h714
    subst k
    rw [sourceRowsAt714]
    exact rowSound714 B hB hF
  · have he : k = (715 : Fin 2425) := Fin.ext h715
    subst k
    rw [sourceRowsAt715]
    exact rowSound715 B hB hF
  · have he : k = (716 : Fin 2425) := Fin.ext h716
    subst k
    rw [sourceRowsAt716]
    exact rowSound716 B hB hF
  · have he : k = (717 : Fin 2425) := Fin.ext h717
    subst k
    rw [sourceRowsAt717]
    exact rowSound717_e B hB hF
  · have he : k = (718 : Fin 2425) := Fin.ext h718
    subst k
    rw [sourceRowsAt718]
    exact rowSound718_e B hB hF
  · have he : k = (719 : Fin 2425) := Fin.ext h719
    subst k
    rw [sourceRowsAt719]
    exact rowSound719_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44_e_oai
