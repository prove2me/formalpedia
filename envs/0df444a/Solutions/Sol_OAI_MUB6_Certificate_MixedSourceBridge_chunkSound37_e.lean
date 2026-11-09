-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound37_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:37:50.04425+00:00
-- url     : https://prove2.me/submissions/9302e90d-5c63-4faa-a289-7513a10adc5f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E111
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E127
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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3087_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3100_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3109_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3204_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3227_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound592_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound599_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound600_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound607_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw402 raw402Labels = mixedMoment B node3120 node3120Labels := by
  calc
    mixedMoment B raw402 raw402Labels = mixedMoment B raw402step0 raw402step0Labels := by
      have ha : raw402step0 = (fun i j => raw402 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw402step0 raw402; decide +kernel
      have hl : raw402step0Labels = raw402Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw402 raw402Labels permutation8 permutation5
    mixedMoment B raw402step0 raw402step0Labels = mixedMoment B raw402step1 raw402step1Labels := by
      have ha : raw402step1 = raw402step0 := by apply Matrix.ext; unfold raw402step1 raw402step0; decide +kernel
      have hl : raw402step0Labels = labelEmbedding1 ∘ raw402step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw402step0 raw402step0Labels raw402step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3120 node3120Labels := by rfl

theorem canonical403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw403 raw403Labels = mixedMoment B node416 node416Labels := by
  calc
    mixedMoment B raw403 raw403Labels = mixedMoment B raw403step0 raw403step0Labels := by
      have ha : raw403step0 = (fun i j => raw403 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw403step0 raw403; decide +kernel
      have hl : raw403step0Labels = raw403Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw403 raw403Labels permutation11 permutation4
    _ = mixedMoment B node416 node416Labels := by rfl

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

theorem canonical11634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11634 raw11634Labels = mixedMoment B node2720 node2720Labels := by
  calc
    _ = mixedMoment B node2720 node2720Labels := by rfl

theorem canonical11635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11635 raw11635Labels = mixedMoment B node3805 node3805Labels := by
  calc
    _ = mixedMoment B node3805 node3805Labels := by rfl

theorem canonical11636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11636 raw11636Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw11636 raw11636Labels = mixedMoment B raw11636step0 raw11636step0Labels := by
      have ha : raw11636step0 = (fun i j => raw11636 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11636step0 raw11636; decide +kernel
      have hl : raw11636step0Labels = raw11636Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11636 raw11636Labels permutation176 permutation2
    _ = mixedMoment B node3874 node3874Labels := by rfl

theorem canonical11637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11637 raw11637Labels = mixedMoment B node3903 node3903Labels := by
  calc
    mixedMoment B raw11637 raw11637Labels = mixedMoment B raw11637step0 raw11637step0Labels := by
      have hz : ∀ j, raw11637 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11637step0 = (fun i j => raw11637 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11637step0 raw11637; decide +kernel
      have hl : raw11637step0Labels = raw11637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11637 raw11637Labels permutation434 hz
    _ = mixedMoment B node3903 node3903Labels := by rfl

theorem canonical11638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11638 raw11638Labels = mixedMoment B node3903 node3903Labels := by
  calc
    mixedMoment B raw11638 raw11638Labels = mixedMoment B raw11638step0 raw11638step0Labels := by
      have hz : ∀ j, raw11638 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11638step0 = (fun i j => raw11638 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11638step0 raw11638; decide +kernel
      have hl : raw11638step0Labels = raw11638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11638 raw11638Labels permutation520 hz
    _ = mixedMoment B node3903 node3903Labels := by rfl

theorem canonical11639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11639 raw11639Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw11639 raw11639Labels = mixedMoment B raw11639step0 raw11639step0Labels := by
      have ha : raw11639step0 = (fun i j => raw11639 (permutation626 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11639step0 raw11639; decide +kernel
      have hl : raw11639step0Labels = raw11639Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11639 raw11639Labels permutation626 permutation4
    mixedMoment B raw11639step0 raw11639step0Labels = mixedMoment B raw11639step1 raw11639step1Labels := by
      have ha : raw11639step1 = -raw11639step0 := by apply Matrix.ext; change ∀ i j, raw11639step1 i j = -(raw11639step0 i j); unfold raw11639step1 raw11639step0; decide +kernel
      have hl : raw11639step1Labels = raw11639step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3812 node3812Labels := by rfl

theorem canonical11640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11640 raw11640Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw11640 raw11640Labels = mixedMoment B raw11640step0 raw11640step0Labels := by
      have hz : ∀ j, raw11640 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11640step0 = (fun i j => raw11640 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11640step0 raw11640; decide +kernel
      have hl : raw11640step0Labels = raw11640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11640 raw11640Labels permutation520 hz
    mixedMoment B raw11640step0 raw11640step0Labels = mixedMoment B raw11640step1 raw11640step1Labels := by
      have hz : ∀ j, raw11640step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11640step1 = (fun i j => raw11640step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11640step1 raw11640step0; decide +kernel
      have hl : raw11640step1Labels = raw11640step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11640step0 raw11640step0Labels permutation104 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical11641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11641 raw11641Labels = mixedMoment B node1259 node1259Labels := by
  calc
    mixedMoment B raw11641 raw11641Labels = mixedMoment B raw11641step0 raw11641step0Labels := by
      have ha : raw11641step0 = (fun i j => raw11641 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11641step0 raw11641; decide +kernel
      have hl : raw11641step0Labels = raw11641Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11641 raw11641Labels permutation176 permutation2
    _ = mixedMoment B node1259 node1259Labels := by rfl

theorem canonical11642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11642 raw11642Labels = mixedMoment B node1233 node1233Labels := by
  calc
    mixedMoment B raw11642 raw11642Labels = mixedMoment B raw11642step0 raw11642step0Labels := by
      have ha : raw11642step0 = (fun i j => raw11642 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11642step0 raw11642; decide +kernel
      have hl : raw11642step0Labels = raw11642Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11642 raw11642Labels permutation160 permutation2
    _ = mixedMoment B node1233 node1233Labels := by rfl

theorem canonical11643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11643 raw11643Labels = mixedMoment B node1214 node1214Labels := by
  calc
    mixedMoment B raw11643 raw11643Labels = mixedMoment B raw11643step0 raw11643step0Labels := by
      have ha : raw11643step0 = (fun i j => raw11643 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11643step0 raw11643; decide +kernel
      have hl : raw11643step0Labels = raw11643Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11643 raw11643Labels permutation155 permutation2
    _ = mixedMoment B node1214 node1214Labels := by rfl

theorem canonical11644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11644 raw11644Labels = mixedMoment B node1214 node1214Labels := by
  calc
    mixedMoment B raw11644 raw11644Labels = mixedMoment B raw11644step0 raw11644step0Labels := by
      have ha : raw11644step0 = (fun i j => raw11644 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11644step0 raw11644; decide +kernel
      have hl : raw11644step0Labels = raw11644Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11644 raw11644Labels permutation153 permutation2
    _ = mixedMoment B node1214 node1214Labels := by rfl

theorem canonical11645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11645 raw11645Labels = mixedMoment B node1212 node1212Labels := by
  calc
    _ = mixedMoment B node1212 node1212Labels := by rfl

theorem canonical11646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11646 raw11646Labels = mixedMoment B node2630 node2630Labels := by
  calc
    mixedMoment B raw11646 raw11646Labels = mixedMoment B raw11646step0 raw11646step0Labels := by
      have ha : raw11646step0 = (fun i j => raw11646 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11646step0 raw11646; decide +kernel
      have hl : raw11646step0Labels = raw11646Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11646 raw11646Labels permutation176 permutation2
    _ = mixedMoment B node2630 node2630Labels := by rfl

theorem canonical11647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11647 raw11647Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw11647 raw11647Labels = mixedMoment B raw11647step0 raw11647step0Labels := by
      have hz : ∀ j, raw11647 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11647step0 = (fun i j => raw11647 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11647step0 raw11647; decide +kernel
      have hl : raw11647step0Labels = raw11647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11647 raw11647Labels permutation434 hz
    mixedMoment B raw11647step0 raw11647step0Labels = mixedMoment B raw11647step1 raw11647step1Labels := by
      have ha : raw11647step1 = (fun i j => raw11647step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11647step1 raw11647step0; decide +kernel
      have hl : raw11647step1Labels = raw11647step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11647step0 raw11647step0Labels permutation38 permutation2
    _ = mixedMoment B node2763 node2763Labels := by rfl

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

theorem canonical11648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11648 raw11648Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw11648 raw11648Labels = mixedMoment B raw11648step0 raw11648step0Labels := by
      have hz : ∀ j, raw11648 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11648step0 = (fun i j => raw11648 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11648step0 raw11648; decide +kernel
      have hl : raw11648step0Labels = raw11648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11648 raw11648Labels permutation520 hz
    mixedMoment B raw11648step0 raw11648step0Labels = mixedMoment B raw11648step1 raw11648step1Labels := by
      have ha : raw11648step1 = (fun i j => raw11648step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11648step1 raw11648step0; decide +kernel
      have hl : raw11648step1Labels = raw11648step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11648step0 raw11648step0Labels permutation38 permutation2
    _ = mixedMoment B node2763 node2763Labels := by rfl

theorem canonical11649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11649 raw11649Labels = mixedMoment B node2757 node2757Labels := by
  calc
    mixedMoment B raw11649 raw11649Labels = mixedMoment B raw11649step0 raw11649step0Labels := by
      have ha : raw11649step0 = (fun i j => raw11649 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11649step0 raw11649; decide +kernel
      have hl : raw11649step0Labels = raw11649Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11649 raw11649Labels permutation194 permutation2
    _ = mixedMoment B node2757 node2757Labels := by rfl

theorem canonical11650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11650 raw11650Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw11650 raw11650Labels = mixedMoment B raw11650step0 raw11650step0Labels := by
      have ha : raw11650step0 = (fun i j => raw11650 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11650step0 raw11650; decide +kernel
      have hl : raw11650step0Labels = raw11650Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11650 raw11650Labels permutation160 permutation2
    _ = mixedMoment B node2508 node2508Labels := by rfl

theorem canonical11651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11651 raw11651Labels = mixedMoment B node2481 node2481Labels := by
  calc
    mixedMoment B raw11651 raw11651Labels = mixedMoment B raw11651step0 raw11651step0Labels := by
      have ha : raw11651step0 = (fun i j => raw11651 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11651step0 raw11651; decide +kernel
      have hl : raw11651step0Labels = raw11651Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11651 raw11651Labels permutation155 permutation2
    _ = mixedMoment B node2481 node2481Labels := by rfl

theorem canonical11652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11652 raw11652Labels = mixedMoment B node2481 node2481Labels := by
  calc
    mixedMoment B raw11652 raw11652Labels = mixedMoment B raw11652step0 raw11652step0Labels := by
      have ha : raw11652step0 = (fun i j => raw11652 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11652step0 raw11652; decide +kernel
      have hl : raw11652step0Labels = raw11652Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11652 raw11652Labels permutation153 permutation2
    _ = mixedMoment B node2481 node2481Labels := by rfl

theorem canonical11653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11653 raw11653Labels = mixedMoment B node2479 node2479Labels := by
  calc
    _ = mixedMoment B node2479 node2479Labels := by rfl

theorem canonical11654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11654 raw11654Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw11654 raw11654Labels = mixedMoment B raw11654step0 raw11654step0Labels := by
      have hz : ∀ j, raw11654 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11654step0 = (fun i j => raw11654 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11654step0 raw11654; decide +kernel
      have hl : raw11654step0Labels = raw11654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11654 raw11654Labels permutation434 hz
    mixedMoment B raw11654step0 raw11654step0Labels = mixedMoment B raw11654step1 raw11654step1Labels := by
      have ha : raw11654step1 = (fun i j => raw11654step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11654step1 raw11654step0; decide +kernel
      have hl : raw11654step1Labels = raw11654step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11654step0 raw11654step0Labels permutation34 permutation2
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical11655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11655 raw11655Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw11655 raw11655Labels = mixedMoment B raw11655step0 raw11655step0Labels := by
      have hz : ∀ j, raw11655 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11655step0 = (fun i j => raw11655 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11655step0 raw11655; decide +kernel
      have hl : raw11655step0Labels = raw11655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11655 raw11655Labels permutation520 hz
    mixedMoment B raw11655step0 raw11655step0Labels = mixedMoment B raw11655step1 raw11655step1Labels := by
      have ha : raw11655step1 = (fun i j => raw11655step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11655step1 raw11655step0; decide +kernel
      have hl : raw11655step1Labels = raw11655step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11655step0 raw11655step0Labels permutation34 permutation2
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical11656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11656 raw11656Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw11656 raw11656Labels = mixedMoment B raw11656step0 raw11656step0Labels := by
      have ha : raw11656step0 = (fun i j => raw11656 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11656step0 raw11656; decide +kernel
      have hl : raw11656step0Labels = raw11656Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11656 raw11656Labels permutation173 permutation2
    _ = mixedMoment B node2730 node2730Labels := by rfl

theorem canonical11657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11657 raw11657Labels = mixedMoment B node2616 node2616Labels := by
  calc
    mixedMoment B raw11657 raw11657Labels = mixedMoment B raw11657step0 raw11657step0Labels := by
      have ha : raw11657step0 = (fun i j => raw11657 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11657step0 raw11657; decide +kernel
      have hl : raw11657step0Labels = raw11657Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11657 raw11657Labels permutation179 permutation2
    _ = mixedMoment B node2616 node2616Labels := by rfl

theorem canonical11658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11658 raw11658Labels = mixedMoment B node2616 node2616Labels := by
  calc
    mixedMoment B raw11658 raw11658Labels = mixedMoment B raw11658step0 raw11658step0Labels := by
      have ha : raw11658step0 = (fun i j => raw11658 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11658step0 raw11658; decide +kernel
      have hl : raw11658step0Labels = raw11658Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11658 raw11658Labels permutation177 permutation2
    _ = mixedMoment B node2616 node2616Labels := by rfl

theorem canonical11659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11659 raw11659Labels = mixedMoment B node2614 node2614Labels := by
  calc
    mixedMoment B raw11659 raw11659Labels = mixedMoment B raw11659step0 raw11659step0Labels := by
      have ha : raw11659step0 = (fun i j => raw11659 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11659step0 raw11659; decide +kernel
      have hl : raw11659step0Labels = raw11659Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11659 raw11659Labels permutation176 permutation2
    _ = mixedMoment B node2614 node2614Labels := by rfl

theorem canonical11720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11720 raw11720Labels = mixedMoment B node2728 node2728Labels := by
  calc
    mixedMoment B raw11720 raw11720Labels = mixedMoment B raw11720step0 raw11720step0Labels := by
      have ha : raw11720step0 = (fun i j => raw11720 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11720step0 raw11720; decide +kernel
      have hl : raw11720step0Labels = raw11720Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11720 raw11720Labels permutation180 permutation7
    mixedMoment B raw11720step0 raw11720step0Labels = mixedMoment B raw11720step1 raw11720step1Labels := by
      have ha : raw11720step1 = raw11720step0 := by apply Matrix.ext; unfold raw11720step1 raw11720step0; decide +kernel
      have hl : raw11720step0Labels = labelEmbedding1 ∘ raw11720step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11720step0 raw11720step0Labels raw11720step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2728 node2728Labels := by rfl

theorem canonical11721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11721 raw11721Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw11721 raw11721Labels = mixedMoment B raw11721step0 raw11721step0Labels := by
      have hz : ∀ j, raw11721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11721step0 = (fun i j => raw11721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11721step0 raw11721; decide +kernel
      have hl : raw11721step0Labels = raw11721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11721 raw11721Labels permutation346 hz
    mixedMoment B raw11721step0 raw11721step0Labels = mixedMoment B raw11721step1 raw11721step1Labels := by
      have ha : raw11721step1 = (fun i j => raw11721step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11721step1 raw11721step0; decide +kernel
      have hl : raw11721step1Labels = raw11721step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11721step0 raw11721step0Labels permutation36 permutation7
    mixedMoment B raw11721step1 raw11721step1Labels = mixedMoment B raw11721step2 raw11721step2Labels := by
      have ha : raw11721step2 = raw11721step1 := by apply Matrix.ext; unfold raw11721step2 raw11721step1; decide +kernel
      have hl : raw11721step1Labels = labelEmbedding1 ∘ raw11721step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11721step1 raw11721step1Labels raw11721step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical11722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11722 raw11722Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw11722 raw11722Labels = mixedMoment B raw11722step0 raw11722step0Labels := by
      have ha : raw11722step0 = (fun i j => raw11722 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11722step0 raw11722; decide +kernel
      have hl : raw11722step0Labels = raw11722Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11722 raw11722Labels permutation181 permutation7
    mixedMoment B raw11722step0 raw11722step0Labels = mixedMoment B raw11722step1 raw11722step1Labels := by
      have ha : raw11722step1 = raw11722step0 := by apply Matrix.ext; unfold raw11722step1 raw11722step0; decide +kernel
      have hl : raw11722step0Labels = labelEmbedding1 ∘ raw11722step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11722step0 raw11722step0Labels raw11722step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2718 node2718Labels := by rfl

theorem canonical11723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11723 raw11723Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw11723 raw11723Labels = mixedMoment B raw11723step0 raw11723step0Labels := by
      have ha : raw11723step0 = (fun i j => raw11723 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11723step0 raw11723; decide +kernel
      have hl : raw11723step0Labels = raw11723Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11723 raw11723Labels permutation180 permutation7
    mixedMoment B raw11723step0 raw11723step0Labels = mixedMoment B raw11723step1 raw11723step1Labels := by
      have ha : raw11723step1 = raw11723step0 := by apply Matrix.ext; unfold raw11723step1 raw11723step0; decide +kernel
      have hl : raw11723step0Labels = labelEmbedding1 ∘ raw11723step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11723step0 raw11723step0Labels raw11723step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2718 node2718Labels := by rfl

theorem canonical11724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11724 raw11724Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw11724 raw11724Labels = mixedMoment B raw11724step0 raw11724step0Labels := by
      have ha : raw11724step0 = (fun i j => raw11724 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11724step0 raw11724; decide +kernel
      have hl : raw11724step0Labels = raw11724Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11724 raw11724Labels permutation180 permutation7
    mixedMoment B raw11724step0 raw11724step0Labels = mixedMoment B raw11724step1 raw11724step1Labels := by
      have ha : raw11724step1 = raw11724step0 := by apply Matrix.ext; unfold raw11724step1 raw11724step0; decide +kernel
      have hl : raw11724step0Labels = labelEmbedding1 ∘ raw11724step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11724step0 raw11724step0Labels raw11724step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical11725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11725 raw11725Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw11725 raw11725Labels = mixedMoment B raw11725step0 raw11725step0Labels := by
      have hz : ∀ j, raw11725 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11725step0 = (fun i j => raw11725 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11725step0 raw11725; decide +kernel
      have hl : raw11725step0Labels = raw11725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11725 raw11725Labels permutation265 hz
    mixedMoment B raw11725step0 raw11725step0Labels = mixedMoment B raw11725step1 raw11725step1Labels := by
      have ha : raw11725step1 = (fun i j => raw11725step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11725step1 raw11725step0; decide +kernel
      have hl : raw11725step1Labels = raw11725step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11725step0 raw11725step0Labels permutation40 permutation5
    mixedMoment B raw11725step1 raw11725step1Labels = mixedMoment B raw11725step2 raw11725step2Labels := by
      have ha : raw11725step2 = -raw11725step1 := by apply Matrix.ext; change ∀ i j, raw11725step2 i j = -(raw11725step1 i j); unfold raw11725step2 raw11725step1; decide +kernel
      have hl : raw11725step2Labels = raw11725step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11725step2 raw11725step2Labels = mixedMoment B raw11725step3 raw11725step3Labels := by
      have ha : raw11725step3 = raw11725step2 := by apply Matrix.ext; unfold raw11725step3 raw11725step2; decide +kernel
      have hl : raw11725step2Labels = labelEmbedding1 ∘ raw11725step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11725step2 raw11725step2Labels raw11725step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3227 node3227Labels := by rfl

theorem canonical11726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11726 raw11726Labels = mixedMoment B node3120 node3120Labels := by
  calc
    mixedMoment B raw11726 raw11726Labels = mixedMoment B raw11726step0 raw11726step0Labels := by
      have hz : ∀ j, raw11726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11726step0 = (fun i j => raw11726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11726step0 raw11726; decide +kernel
      have hl : raw11726step0Labels = raw11726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11726 raw11726Labels permutation346 hz
    mixedMoment B raw11726step0 raw11726step0Labels = mixedMoment B raw11726step1 raw11726step1Labels := by
      have hz : ∀ j, raw11726step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11726step1 = (fun i j => raw11726step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11726step1 raw11726step0; decide +kernel
      have hl : raw11726step1Labels = raw11726step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11726step0 raw11726step0Labels permutation56 hz
    mixedMoment B raw11726step1 raw11726step1Labels = mixedMoment B raw11726step2 raw11726step2Labels := by
      have ha : raw11726step2 = (fun i j => raw11726step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11726step2 raw11726step1; decide +kernel
      have hl : raw11726step2Labels = raw11726step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11726step1 raw11726step1Labels permutation12 permutation7
    mixedMoment B raw11726step2 raw11726step2Labels = mixedMoment B raw11726step3 raw11726step3Labels := by
      have ha : raw11726step3 = raw11726step2 := by apply Matrix.ext; unfold raw11726step3 raw11726step2; decide +kernel
      have hl : raw11726step2Labels = labelEmbedding1 ∘ raw11726step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11726step2 raw11726step2Labels raw11726step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3120 node3120Labels := by rfl

theorem canonical11727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11727 raw11727Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw11727 raw11727Labels = mixedMoment B raw11727step0 raw11727step0Labels := by
      have hz : ∀ j, raw11727 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11727step0 = (fun i j => raw11727 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11727step0 raw11727; decide +kernel
      have hl : raw11727step0Labels = raw11727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11727 raw11727Labels permutation265 hz
    mixedMoment B raw11727step0 raw11727step0Labels = mixedMoment B raw11727step1 raw11727step1Labels := by
      have ha : raw11727step1 = (fun i j => raw11727step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11727step1 raw11727step0; decide +kernel
      have hl : raw11727step1Labels = raw11727step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11727step0 raw11727step0Labels permutation37 permutation7
    mixedMoment B raw11727step1 raw11727step1Labels = mixedMoment B raw11727step2 raw11727step2Labels := by
      have ha : raw11727step2 = raw11727step1 := by apply Matrix.ext; unfold raw11727step2 raw11727step1; decide +kernel
      have hl : raw11727step1Labels = labelEmbedding1 ∘ raw11727step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11727step1 raw11727step1Labels raw11727step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3097 node3097Labels := by rfl

theorem canonical11728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11728 raw11728Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw11728 raw11728Labels = mixedMoment B raw11728step0 raw11728step0Labels := by
      have hz : ∀ j, raw11728 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11728step0 = (fun i j => raw11728 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11728step0 raw11728; decide +kernel
      have hl : raw11728step0Labels = raw11728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11728 raw11728Labels permutation265 hz
    mixedMoment B raw11728step0 raw11728step0Labels = mixedMoment B raw11728step1 raw11728step1Labels := by
      have ha : raw11728step1 = (fun i j => raw11728step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11728step1 raw11728step0; decide +kernel
      have hl : raw11728step1Labels = raw11728step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11728step0 raw11728step0Labels permutation36 permutation7
    mixedMoment B raw11728step1 raw11728step1Labels = mixedMoment B raw11728step2 raw11728step2Labels := by
      have ha : raw11728step2 = raw11728step1 := by apply Matrix.ext; unfold raw11728step2 raw11728step1; decide +kernel
      have hl : raw11728step1Labels = labelEmbedding1 ∘ raw11728step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11728step1 raw11728step1Labels raw11728step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3097 node3097Labels := by rfl

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

theorem canonical11730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11730 raw11730Labels = mixedMoment B node3199 node3199Labels := by
  calc
    mixedMoment B raw11730 raw11730Labels = mixedMoment B raw11730step0 raw11730step0Labels := by
      have ha : raw11730step0 = (fun i j => raw11730 (permutation161 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11730step0 raw11730; decide +kernel
      have hl : raw11730step0Labels = raw11730Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11730 raw11730Labels permutation161 permutation5
    mixedMoment B raw11730step0 raw11730step0Labels = mixedMoment B raw11730step1 raw11730step1Labels := by
      have ha : raw11730step1 = -raw11730step0 := by apply Matrix.ext; change ∀ i j, raw11730step1 i j = -(raw11730step0 i j); unfold raw11730step1 raw11730step0; decide +kernel
      have hl : raw11730step1Labels = raw11730step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11730step1 raw11730step1Labels = mixedMoment B raw11730step2 raw11730step2Labels := by
      have ha : raw11730step2 = raw11730step1 := by apply Matrix.ext; unfold raw11730step2 raw11730step1; decide +kernel
      have hl : raw11730step1Labels = labelEmbedding1 ∘ raw11730step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11730step1 raw11730step1Labels raw11730step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3199 node3199Labels := by rfl

theorem canonical11731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11731 raw11731Labels = mixedMoment B node3041 node3041Labels := by
  calc
    mixedMoment B raw11731 raw11731Labels = mixedMoment B raw11731step0 raw11731step0Labels := by
      have ha : raw11731step0 = (fun i j => raw11731 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11731step0 raw11731; decide +kernel
      have hl : raw11731step0Labels = raw11731Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11731 raw11731Labels permutation180 permutation7
    mixedMoment B raw11731step0 raw11731step0Labels = mixedMoment B raw11731step1 raw11731step1Labels := by
      have ha : raw11731step1 = raw11731step0 := by apply Matrix.ext; unfold raw11731step1 raw11731step0; decide +kernel
      have hl : raw11731step0Labels = labelEmbedding1 ∘ raw11731step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11731step0 raw11731step0Labels raw11731step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3041 node3041Labels := by rfl

theorem canonical11732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11732 raw11732Labels = mixedMoment B node3034 node3034Labels := by
  calc
    mixedMoment B raw11732 raw11732Labels = mixedMoment B raw11732step0 raw11732step0Labels := by
      have ha : raw11732step0 = (fun i j => raw11732 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11732step0 raw11732; decide +kernel
      have hl : raw11732step0Labels = raw11732Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11732 raw11732Labels permutation181 permutation7
    mixedMoment B raw11732step0 raw11732step0Labels = mixedMoment B raw11732step1 raw11732step1Labels := by
      have ha : raw11732step1 = raw11732step0 := by apply Matrix.ext; unfold raw11732step1 raw11732step0; decide +kernel
      have hl : raw11732step0Labels = labelEmbedding1 ∘ raw11732step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11732step0 raw11732step0Labels raw11732step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3034 node3034Labels := by rfl

theorem canonical11733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11733 raw11733Labels = mixedMoment B node3034 node3034Labels := by
  calc
    mixedMoment B raw11733 raw11733Labels = mixedMoment B raw11733step0 raw11733step0Labels := by
      have ha : raw11733step0 = (fun i j => raw11733 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11733step0 raw11733; decide +kernel
      have hl : raw11733step0Labels = raw11733Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11733 raw11733Labels permutation180 permutation7
    mixedMoment B raw11733step0 raw11733step0Labels = mixedMoment B raw11733step1 raw11733step1Labels := by
      have ha : raw11733step1 = raw11733step0 := by apply Matrix.ext; unfold raw11733step1 raw11733step0; decide +kernel
      have hl : raw11733step0Labels = labelEmbedding1 ∘ raw11733step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11733step0 raw11733step0Labels raw11733step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3034 node3034Labels := by rfl

theorem canonical11734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11734 raw11734Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw11734 raw11734Labels = mixedMoment B raw11734step0 raw11734step0Labels := by
      have ha : raw11734step0 = (fun i j => raw11734 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11734step0 raw11734; decide +kernel
      have hl : raw11734step0Labels = raw11734Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11734 raw11734Labels permutation180 permutation7
    mixedMoment B raw11734step0 raw11734step0Labels = mixedMoment B raw11734step1 raw11734step1Labels := by
      have ha : raw11734step1 = raw11734step0 := by apply Matrix.ext; unfold raw11734step1 raw11734step0; decide +kernel
      have hl : raw11734step0Labels = labelEmbedding1 ∘ raw11734step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11734step0 raw11734step0Labels raw11734step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical11735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11735 raw11735Labels = mixedMoment B node3204 node3204Labels := by
  calc
    mixedMoment B raw11735 raw11735Labels = mixedMoment B raw11735step0 raw11735step0Labels := by
      have ha : raw11735step0 = (fun i j => raw11735 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11735step0 raw11735; decide +kernel
      have hl : raw11735step0Labels = raw11735Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11735 raw11735Labels permutation166 permutation5
    mixedMoment B raw11735step0 raw11735step0Labels = mixedMoment B raw11735step1 raw11735step1Labels := by
      have ha : raw11735step1 = -raw11735step0 := by apply Matrix.ext; change ∀ i j, raw11735step1 i j = -(raw11735step0 i j); unfold raw11735step1 raw11735step0; decide +kernel
      have hl : raw11735step1Labels = raw11735step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11735step1 raw11735step1Labels = mixedMoment B raw11735step2 raw11735step2Labels := by
      have ha : raw11735step2 = raw11735step1 := by apply Matrix.ext; unfold raw11735step2 raw11735step1; decide +kernel
      have hl : raw11735step1Labels = labelEmbedding1 ∘ raw11735step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11735step1 raw11735step1Labels raw11735step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3204 node3204Labels := by rfl

theorem canonical11736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11736 raw11736Labels = mixedMoment B node3091 node3091Labels := by
  calc
    mixedMoment B raw11736 raw11736Labels = mixedMoment B raw11736step0 raw11736step0Labels := by
      have ha : raw11736step0 = (fun i j => raw11736 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11736step0 raw11736; decide +kernel
      have hl : raw11736step0Labels = raw11736Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11736 raw11736Labels permutation180 permutation7
    mixedMoment B raw11736step0 raw11736step0Labels = mixedMoment B raw11736step1 raw11736step1Labels := by
      have ha : raw11736step1 = raw11736step0 := by apply Matrix.ext; unfold raw11736step1 raw11736step0; decide +kernel
      have hl : raw11736step0Labels = labelEmbedding1 ∘ raw11736step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11736step0 raw11736step0Labels raw11736step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3091 node3091Labels := by rfl

theorem canonical11737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11737 raw11737Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw11737 raw11737Labels = mixedMoment B raw11737step0 raw11737step0Labels := by
      have hz : ∀ j, raw11737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11737step0 = (fun i j => raw11737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11737step0 raw11737; decide +kernel
      have hl : raw11737step0Labels = raw11737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11737 raw11737Labels permutation346 hz
    mixedMoment B raw11737step0 raw11737step0Labels = mixedMoment B raw11737step1 raw11737step1Labels := by
      have ha : raw11737step1 = (fun i j => raw11737step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11737step1 raw11737step0; decide +kernel
      have hl : raw11737step1Labels = raw11737step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11737step0 raw11737step0Labels permutation36 permutation7
    mixedMoment B raw11737step1 raw11737step1Labels = mixedMoment B raw11737step2 raw11737step2Labels := by
      have ha : raw11737step2 = raw11737step1 := by apply Matrix.ext; unfold raw11737step2 raw11737step1; decide +kernel
      have hl : raw11737step1Labels = labelEmbedding1 ∘ raw11737step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11737step1 raw11737step1Labels raw11737step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3109 node3109Labels := by rfl

theorem canonical11738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11738 raw11738Labels = mixedMoment B node3084 node3084Labels := by
  calc
    mixedMoment B raw11738 raw11738Labels = mixedMoment B raw11738step0 raw11738step0Labels := by
      have ha : raw11738step0 = (fun i j => raw11738 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11738step0 raw11738; decide +kernel
      have hl : raw11738step0Labels = raw11738Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11738 raw11738Labels permutation180 permutation7
    mixedMoment B raw11738step0 raw11738step0Labels = mixedMoment B raw11738step1 raw11738step1Labels := by
      have ha : raw11738step1 = raw11738step0 := by apply Matrix.ext; unfold raw11738step1 raw11738step0; decide +kernel
      have hl : raw11738step0Labels = labelEmbedding1 ∘ raw11738step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11738step0 raw11738step0Labels raw11738step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3084 node3084Labels := by rfl

theorem canonical11739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11739 raw11739Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw11739 raw11739Labels = mixedMoment B raw11739step0 raw11739step0Labels := by
      have ha : raw11739step0 = (fun i j => raw11739 (permutation177 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11739step0 raw11739; decide +kernel
      have hl : raw11739step0Labels = raw11739Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11739 raw11739Labels permutation177 permutation7
    mixedMoment B raw11739step0 raw11739step0Labels = mixedMoment B raw11739step1 raw11739step1Labels := by
      have ha : raw11739step1 = raw11739step0 := by apply Matrix.ext; unfold raw11739step1 raw11739step0; decide +kernel
      have hl : raw11739step0Labels = labelEmbedding1 ∘ raw11739step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11739step0 raw11739step0Labels raw11739step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3087 node3087Labels := by rfl

theorem canonical11740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11740 raw11740Labels = mixedMoment B node3204 node3204Labels := by
  calc
    mixedMoment B raw11740 raw11740Labels = mixedMoment B raw11740step0 raw11740step0Labels := by
      have ha : raw11740step0 = (fun i j => raw11740 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11740step0 raw11740; decide +kernel
      have hl : raw11740step0Labels = raw11740Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11740 raw11740Labels permutation160 permutation5
    mixedMoment B raw11740step0 raw11740step0Labels = mixedMoment B raw11740step1 raw11740step1Labels := by
      have ha : raw11740step1 = -raw11740step0 := by apply Matrix.ext; change ∀ i j, raw11740step1 i j = -(raw11740step0 i j); unfold raw11740step1 raw11740step0; decide +kernel
      have hl : raw11740step1Labels = raw11740step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11740step1 raw11740step1Labels = mixedMoment B raw11740step2 raw11740step2Labels := by
      have ha : raw11740step2 = raw11740step1 := by apply Matrix.ext; unfold raw11740step2 raw11740step1; decide +kernel
      have hl : raw11740step1Labels = labelEmbedding1 ∘ raw11740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11740step1 raw11740step1Labels raw11740step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3204 node3204Labels := by rfl

theorem canonical11741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11741 raw11741Labels = mixedMoment B node3091 node3091Labels := by
  calc
    mixedMoment B raw11741 raw11741Labels = mixedMoment B raw11741step0 raw11741step0Labels := by
      have ha : raw11741step0 = (fun i j => raw11741 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11741step0 raw11741; decide +kernel
      have hl : raw11741step0Labels = raw11741Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11741 raw11741Labels permutation181 permutation7
    mixedMoment B raw11741step0 raw11741step0Labels = mixedMoment B raw11741step1 raw11741step1Labels := by
      have ha : raw11741step1 = raw11741step0 := by apply Matrix.ext; unfold raw11741step1 raw11741step0; decide +kernel
      have hl : raw11741step0Labels = labelEmbedding1 ∘ raw11741step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11741step0 raw11741step0Labels raw11741step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3091 node3091Labels := by rfl

theorem canonical11742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11742 raw11742Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw11742 raw11742Labels = mixedMoment B raw11742step0 raw11742step0Labels := by
      have hz : ∀ j, raw11742 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11742step0 = (fun i j => raw11742 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11742step0 raw11742; decide +kernel
      have hl : raw11742step0Labels = raw11742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11742 raw11742Labels permutation346 hz
    mixedMoment B raw11742step0 raw11742step0Labels = mixedMoment B raw11742step1 raw11742step1Labels := by
      have ha : raw11742step1 = (fun i j => raw11742step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11742step1 raw11742step0; decide +kernel
      have hl : raw11742step1Labels = raw11742step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11742step0 raw11742step0Labels permutation37 permutation7
    mixedMoment B raw11742step1 raw11742step1Labels = mixedMoment B raw11742step2 raw11742step2Labels := by
      have ha : raw11742step2 = raw11742step1 := by apply Matrix.ext; unfold raw11742step2 raw11742step1; decide +kernel
      have hl : raw11742step1Labels = labelEmbedding1 ∘ raw11742step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11742step1 raw11742step1Labels raw11742step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3109 node3109Labels := by rfl

theorem canonical11743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11743 raw11743Labels = mixedMoment B node3084 node3084Labels := by
  calc
    mixedMoment B raw11743 raw11743Labels = mixedMoment B raw11743step0 raw11743step0Labels := by
      have ha : raw11743step0 = (fun i j => raw11743 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11743step0 raw11743; decide +kernel
      have hl : raw11743step0Labels = raw11743Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11743 raw11743Labels permutation181 permutation7
    mixedMoment B raw11743step0 raw11743step0Labels = mixedMoment B raw11743step1 raw11743step1Labels := by
      have ha : raw11743step1 = raw11743step0 := by apply Matrix.ext; unfold raw11743step1 raw11743step0; decide +kernel
      have hl : raw11743step0Labels = labelEmbedding1 ∘ raw11743step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11743step0 raw11743step0Labels raw11743step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3084 node3084Labels := by rfl

theorem canonical11744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11744 raw11744Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw11744 raw11744Labels = mixedMoment B raw11744step0 raw11744step0Labels := by
      have ha : raw11744step0 = (fun i j => raw11744 (permutation179 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11744step0 raw11744; decide +kernel
      have hl : raw11744step0Labels = raw11744Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11744 raw11744Labels permutation179 permutation7
    mixedMoment B raw11744step0 raw11744step0Labels = mixedMoment B raw11744step1 raw11744step1Labels := by
      have ha : raw11744step1 = raw11744step0 := by apply Matrix.ext; unfold raw11744step1 raw11744step0; decide +kernel
      have hl : raw11744step0Labels = labelEmbedding1 ∘ raw11744step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11744step0 raw11744step0Labels raw11744step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3087 node3087Labels := by rfl

theorem canonical11745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11745 raw11745Labels = mixedMoment B node2471 node2471Labels := by
  calc
    mixedMoment B raw11745 raw11745Labels = mixedMoment B raw11745step0 raw11745step0Labels := by
      have ha : raw11745step0 = (fun i j => raw11745 (permutation640 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11745step0 raw11745; decide +kernel
      have hl : raw11745step0Labels = raw11745Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11745 raw11745Labels permutation640 permutation5
    mixedMoment B raw11745step0 raw11745step0Labels = mixedMoment B raw11745step1 raw11745step1Labels := by
      have ha : raw11745step1 = raw11745step0 := by apply Matrix.ext; unfold raw11745step1 raw11745step0; decide +kernel
      have hl : raw11745step0Labels = labelEmbedding1 ∘ raw11745step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11745step0 raw11745step0Labels raw11745step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2471 node2471Labels := by rfl

theorem canonical11746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11746 raw11746Labels = mixedMoment B node2472 node2472Labels := by
  calc
    mixedMoment B raw11746 raw11746Labels = mixedMoment B raw11746step0 raw11746step0Labels := by
      have ha : raw11746step0 = (fun i j => raw11746 (permutation639 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11746step0 raw11746; decide +kernel
      have hl : raw11746step0Labels = raw11746Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11746 raw11746Labels permutation639 permutation5
    mixedMoment B raw11746step0 raw11746step0Labels = mixedMoment B raw11746step1 raw11746step1Labels := by
      have ha : raw11746step1 = raw11746step0 := by apply Matrix.ext; unfold raw11746step1 raw11746step0; decide +kernel
      have hl : raw11746step0Labels = labelEmbedding1 ∘ raw11746step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11746step0 raw11746step0Labels raw11746step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2472 node2472Labels := by rfl

theorem canonical11747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11747 raw11747Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw11747 raw11747Labels = mixedMoment B raw11747step0 raw11747step0Labels := by
      have hz : ∀ j, raw11747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11747step0 = (fun i j => raw11747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11747step0 raw11747; decide +kernel
      have hl : raw11747step0Labels = raw11747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11747 raw11747Labels permutation346 hz
    mixedMoment B raw11747step0 raw11747step0Labels = mixedMoment B raw11747step1 raw11747step1Labels := by
      have ha : raw11747step1 = (fun i j => raw11747step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11747step1 raw11747step0; decide +kernel
      have hl : raw11747step1Labels = raw11747step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11747step0 raw11747step0Labels permutation145 permutation5
    mixedMoment B raw11747step1 raw11747step1Labels = mixedMoment B raw11747step2 raw11747step2Labels := by
      have ha : raw11747step2 = raw11747step1 := by apply Matrix.ext; unfold raw11747step2 raw11747step1; decide +kernel
      have hl : raw11747step1Labels = labelEmbedding1 ∘ raw11747step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11747step1 raw11747step1Labels raw11747step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2754 node2754Labels := by rfl

theorem canonical11748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11748 raw11748Labels = mixedMoment B node2484 node2484Labels := by
  calc
    mixedMoment B raw11748 raw11748Labels = mixedMoment B raw11748step0 raw11748step0Labels := by
      have ha : raw11748step0 = (fun i j => raw11748 (permutation644 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11748step0 raw11748; decide +kernel
      have hl : raw11748step0Labels = raw11748Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11748 raw11748Labels permutation644 permutation5
    mixedMoment B raw11748step0 raw11748step0Labels = mixedMoment B raw11748step1 raw11748step1Labels := by
      have ha : raw11748step1 = raw11748step0 := by apply Matrix.ext; unfold raw11748step1 raw11748step0; decide +kernel
      have hl : raw11748step0Labels = labelEmbedding1 ∘ raw11748step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11748step0 raw11748step0Labels raw11748step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2484 node2484Labels := by rfl

theorem canonical11749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11749 raw11749Labels = mixedMoment B node2484 node2484Labels := by
  calc
    mixedMoment B raw11749 raw11749Labels = mixedMoment B raw11749step0 raw11749step0Labels := by
      have ha : raw11749step0 = (fun i j => raw11749 (permutation638 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11749step0 raw11749; decide +kernel
      have hl : raw11749step0Labels = raw11749Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11749 raw11749Labels permutation638 permutation5
    mixedMoment B raw11749step0 raw11749step0Labels = mixedMoment B raw11749step1 raw11749step1Labels := by
      have ha : raw11749step1 = raw11749step0 := by apply Matrix.ext; unfold raw11749step1 raw11749step0; decide +kernel
      have hl : raw11749step0Labels = labelEmbedding1 ∘ raw11749step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11749step0 raw11749step0Labels raw11749step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2484 node2484Labels := by rfl

theorem canonical11750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11750 raw11750Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw11750 raw11750Labels = mixedMoment B raw11750step0 raw11750step0Labels := by
      have ha : raw11750step0 = (fun i j => raw11750 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11750step0 raw11750; decide +kernel
      have hl : raw11750step0Labels = raw11750Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11750 raw11750Labels permutation160 permutation4
    mixedMoment B raw11750step0 raw11750step0Labels = mixedMoment B raw11750step1 raw11750step1Labels := by
      have ha : raw11750step1 = -raw11750step0 := by apply Matrix.ext; change ∀ i j, raw11750step1 i j = -(raw11750step0 i j); unfold raw11750step1 raw11750step0; decide +kernel
      have hl : raw11750step1Labels = raw11750step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3525 node3525Labels := by rfl

theorem canonical11751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11751 raw11751Labels = mixedMoment B node3505 node3505Labels := by
  calc
    mixedMoment B raw11751 raw11751Labels = mixedMoment B raw11751step0 raw11751step0Labels := by
      have ha : raw11751step0 = (fun i j => raw11751 (permutation197 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11751step0 raw11751; decide +kernel
      have hl : raw11751step0Labels = raw11751Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11751 raw11751Labels permutation197 permutation2
    mixedMoment B raw11751step0 raw11751step0Labels = mixedMoment B raw11751step1 raw11751step1Labels := by
      have ha : raw11751step1 = -raw11751step0 := by apply Matrix.ext; change ∀ i j, raw11751step1 i j = -(raw11751step0 i j); unfold raw11751step1 raw11751step0; decide +kernel
      have hl : raw11751step1Labels = raw11751step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3505 node3505Labels := by rfl

theorem canonical11752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11752 raw11752Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw11752 raw11752Labels = mixedMoment B raw11752step0 raw11752step0Labels := by
      have hz : ∀ j, raw11752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11752step0 = (fun i j => raw11752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11752step0 raw11752; decide +kernel
      have hl : raw11752step0Labels = raw11752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11752 raw11752Labels permutation346 hz
    mixedMoment B raw11752step0 raw11752step0Labels = mixedMoment B raw11752step1 raw11752step1Labels := by
      have ha : raw11752step1 = (fun i j => raw11752step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11752step1 raw11752step0; decide +kernel
      have hl : raw11752step1Labels = raw11752step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11752step0 raw11752step0Labels permutation50 permutation2
    mixedMoment B raw11752step1 raw11752step1Labels = mixedMoment B raw11752step2 raw11752step2Labels := by
      have ha : raw11752step2 = -raw11752step1 := by apply Matrix.ext; change ∀ i j, raw11752step2 i j = -(raw11752step1 i j); unfold raw11752step2 raw11752step1; decide +kernel
      have hl : raw11752step2Labels = raw11752step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3581 node3581Labels := by rfl

theorem canonical11753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11753 raw11753Labels = mixedMoment B node3503 node3503Labels := by
  calc
    mixedMoment B raw11753 raw11753Labels = mixedMoment B raw11753step0 raw11753step0Labels := by
      have ha : raw11753step0 = (fun i j => raw11753 (permutation195 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11753step0 raw11753; decide +kernel
      have hl : raw11753step0Labels = raw11753Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11753 raw11753Labels permutation195 permutation2
    mixedMoment B raw11753step0 raw11753step0Labels = mixedMoment B raw11753step1 raw11753step1Labels := by
      have ha : raw11753step1 = -raw11753step0 := by apply Matrix.ext; change ∀ i j, raw11753step1 i j = -(raw11753step0 i j); unfold raw11753step1 raw11753step0; decide +kernel
      have hl : raw11753step1Labels = raw11753step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3503 node3503Labels := by rfl

theorem canonical11754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11754 raw11754Labels = mixedMoment B node3503 node3503Labels := by
  calc
    mixedMoment B raw11754 raw11754Labels = mixedMoment B raw11754step0 raw11754step0Labels := by
      have ha : raw11754step0 = (fun i j => raw11754 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11754step0 raw11754; decide +kernel
      have hl : raw11754step0Labels = raw11754Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11754 raw11754Labels permutation194 permutation2
    mixedMoment B raw11754step0 raw11754step0Labels = mixedMoment B raw11754step1 raw11754step1Labels := by
      have ha : raw11754step1 = -raw11754step0 := by apply Matrix.ext; change ∀ i j, raw11754step1 i j = -(raw11754step0 i j); unfold raw11754step1 raw11754step0; decide +kernel
      have hl : raw11754step1Labels = raw11754step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3503 node3503Labels := by rfl

theorem canonical11755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11755 raw11755Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw11755 raw11755Labels = mixedMoment B raw11755step0 raw11755step0Labels := by
      have ha : raw11755step0 = (fun i j => raw11755 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11755step0 raw11755; decide +kernel
      have hl : raw11755step0Labels = raw11755Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11755 raw11755Labels permutation194 permutation2
    mixedMoment B raw11755step0 raw11755step0Labels = mixedMoment B raw11755step1 raw11755step1Labels := by
      have ha : raw11755step1 = -raw11755step0 := by apply Matrix.ext; change ∀ i j, raw11755step1 i j = -(raw11755step0 i j); unfold raw11755step1 raw11755step0; decide +kernel
      have hl : raw11755step1Labels = raw11755step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3532 node3532Labels := by rfl

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

theorem canonical11757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11757 raw11757Labels = mixedMoment B node3373 node3373Labels := by
  calc
    mixedMoment B raw11757 raw11757Labels = mixedMoment B raw11757step0 raw11757step0Labels := by
      have ha : raw11757step0 = (fun i j => raw11757 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11757step0 raw11757; decide +kernel
      have hl : raw11757step0Labels = raw11757Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11757 raw11757Labels permutation160 permutation4
    mixedMoment B raw11757step0 raw11757step0Labels = mixedMoment B raw11757step1 raw11757step1Labels := by
      have ha : raw11757step1 = -raw11757step0 := by apply Matrix.ext; change ∀ i j, raw11757step1 i j = -(raw11757step0 i j); unfold raw11757step1 raw11757step0; decide +kernel
      have hl : raw11757step1Labels = raw11757step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3373 node3373Labels := by rfl

theorem canonical11758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11758 raw11758Labels = mixedMoment B node3376 node3376Labels := by
  calc
    mixedMoment B raw11758 raw11758Labels = mixedMoment B raw11758step0 raw11758step0Labels := by
      have ha : raw11758step0 = (fun i j => raw11758 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11758step0 raw11758; decide +kernel
      have hl : raw11758step0Labels = raw11758Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11758 raw11758Labels permutation164 permutation4
    mixedMoment B raw11758step0 raw11758step0Labels = mixedMoment B raw11758step1 raw11758step1Labels := by
      have ha : raw11758step1 = -raw11758step0 := by apply Matrix.ext; change ∀ i j, raw11758step1 i j = -(raw11758step0 i j); unfold raw11758step1 raw11758step0; decide +kernel
      have hl : raw11758step1Labels = raw11758step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3376 node3376Labels := by rfl

theorem canonical11759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11759 raw11759Labels = mixedMoment B node3376 node3376Labels := by
  calc
    mixedMoment B raw11759 raw11759Labels = mixedMoment B raw11759step0 raw11759step0Labels := by
      have ha : raw11759step0 = (fun i j => raw11759 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11759step0 raw11759; decide +kernel
      have hl : raw11759step0Labels = raw11759Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11759 raw11759Labels permutation158 permutation4
    mixedMoment B raw11759step0 raw11759step0Labels = mixedMoment B raw11759step1 raw11759step1Labels := by
      have ha : raw11759step1 = -raw11759step0 := by apply Matrix.ext; change ∀ i j, raw11759step1 i j = -(raw11759step0 i j); unfold raw11759step1 raw11759step0; decide +kernel
      have hl : raw11759step1Labels = raw11759step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3376 node3376Labels := by rfl

theorem canonical11760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11760 raw11760Labels = mixedMoment B node2980 node2980Labels := by
  calc
    mixedMoment B raw11760 raw11760Labels = mixedMoment B raw11760step0 raw11760step0Labels := by
      have ha : raw11760step0 = (fun i j => raw11760 (permutation640 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11760step0 raw11760; decide +kernel
      have hl : raw11760step0Labels = raw11760Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11760 raw11760Labels permutation640 permutation4
    _ = mixedMoment B node2980 node2980Labels := by rfl

theorem canonical11761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11761 raw11761Labels = mixedMoment B node2012 node2012Labels := by
  calc
    mixedMoment B raw11761 raw11761Labels = mixedMoment B raw11761step0 raw11761step0Labels := by
      have ha : raw11761step0 = (fun i j => raw11761 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11761step0 raw11761; decide +kernel
      have hl : raw11761step0Labels = raw11761Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11761 raw11761Labels permutation160 permutation4
    mixedMoment B raw11761step0 raw11761step0Labels = mixedMoment B raw11761step1 raw11761step1Labels := by
      have ha : raw11761step1 = -raw11761step0 := by apply Matrix.ext; change ∀ i j, raw11761step1 i j = -(raw11761step0 i j); unfold raw11761step1 raw11761step0; decide +kernel
      have hl : raw11761step1Labels = raw11761step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2012 node2012Labels := by rfl

theorem canonical11762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11762 raw11762Labels = mixedMoment B node3500 node3500Labels := by
  calc
    mixedMoment B raw11762 raw11762Labels = mixedMoment B raw11762step0 raw11762step0Labels := by
      have ha : raw11762step0 = (fun i j => raw11762 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11762step0 raw11762; decide +kernel
      have hl : raw11762step0Labels = raw11762Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11762 raw11762Labels permutation160 permutation4
    mixedMoment B raw11762step0 raw11762step0Labels = mixedMoment B raw11762step1 raw11762step1Labels := by
      have ha : raw11762step1 = -raw11762step0 := by apply Matrix.ext; change ∀ i j, raw11762step1 i j = -(raw11762step0 i j); unfold raw11762step1 raw11762step0; decide +kernel
      have hl : raw11762step1Labels = raw11762step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3500 node3500Labels := by rfl

theorem canonical11763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11763 raw11763Labels = mixedMoment B node3500 node3500Labels := by
  calc
    mixedMoment B raw11763 raw11763Labels = mixedMoment B raw11763step0 raw11763step0Labels := by
      have ha : raw11763step0 = (fun i j => raw11763 (permutation166 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11763step0 raw11763; decide +kernel
      have hl : raw11763step0Labels = raw11763Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11763 raw11763Labels permutation166 permutation4
    mixedMoment B raw11763step0 raw11763step0Labels = mixedMoment B raw11763step1 raw11763step1Labels := by
      have ha : raw11763step1 = -raw11763step0 := by apply Matrix.ext; change ∀ i j, raw11763step1 i j = -(raw11763step0 i j); unfold raw11763step1 raw11763step0; decide +kernel
      have hl : raw11763step1Labels = raw11763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3500 node3500Labels := by rfl

theorem canonical11764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11764 raw11764Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw11764 raw11764Labels = mixedMoment B raw11764step0 raw11764step0Labels := by
      have ha : raw11764step0 = (fun i j => raw11764 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11764step0 raw11764; decide +kernel
      have hl : raw11764step0Labels = raw11764Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11764 raw11764Labels permutation161 permutation4
    mixedMoment B raw11764step0 raw11764step0Labels = mixedMoment B raw11764step1 raw11764step1Labels := by
      have ha : raw11764step1 = -raw11764step0 := by apply Matrix.ext; change ∀ i j, raw11764step1 i j = -(raw11764step0 i j); unfold raw11764step1 raw11764step0; decide +kernel
      have hl : raw11764step1Labels = raw11764step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3526 node3526Labels := by rfl

theorem canonical11765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11765 raw11765Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw11765 raw11765Labels = mixedMoment B raw11765step0 raw11765step0Labels := by
      have ha : raw11765step0 = (fun i j => raw11765 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11765step0 raw11765; decide +kernel
      have hl : raw11765step0Labels = raw11765Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11765 raw11765Labels permutation164 permutation4
    mixedMoment B raw11765step0 raw11765step0Labels = mixedMoment B raw11765step1 raw11765step1Labels := by
      have ha : raw11765step1 = -raw11765step0 := by apply Matrix.ext; change ∀ i j, raw11765step1 i j = -(raw11765step0 i j); unfold raw11765step1 raw11765step0; decide +kernel
      have hl : raw11765step1Labels = raw11765step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2020 node2020Labels := by rfl

theorem canonical11766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11766 raw11766Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw11766 raw11766Labels = mixedMoment B raw11766step0 raw11766step0Labels := by
      have hz : ∀ j, raw11766 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11766step0 = (fun i j => raw11766 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11766step0 raw11766; decide +kernel
      have hl : raw11766step0Labels = raw11766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11766 raw11766Labels permutation346 hz
    mixedMoment B raw11766step0 raw11766step0Labels = mixedMoment B raw11766step1 raw11766step1Labels := by
      have ha : raw11766step1 = (fun i j => raw11766step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11766step1 raw11766step0; decide +kernel
      have hl : raw11766step1Labels = raw11766step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11766step0 raw11766step0Labels permutation34 permutation4
    mixedMoment B raw11766step1 raw11766step1Labels = mixedMoment B raw11766step2 raw11766step2Labels := by
      have ha : raw11766step2 = -raw11766step1 := by apply Matrix.ext; change ∀ i j, raw11766step2 i j = -(raw11766step1 i j); unfold raw11766step2 raw11766step1; decide +kernel
      have hl : raw11766step2Labels = raw11766step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical11767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11767 raw11767Labels = mixedMoment B node3503 node3503Labels := by
  calc
    mixedMoment B raw11767 raw11767Labels = mixedMoment B raw11767step0 raw11767step0Labels := by
      have ha : raw11767step0 = (fun i j => raw11767 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11767step0 raw11767; decide +kernel
      have hl : raw11767step0Labels = raw11767Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11767 raw11767Labels permutation164 permutation4
    mixedMoment B raw11767step0 raw11767step0Labels = mixedMoment B raw11767step1 raw11767step1Labels := by
      have ha : raw11767step1 = -raw11767step0 := by apply Matrix.ext; change ∀ i j, raw11767step1 i j = -(raw11767step0 i j); unfold raw11767step1 raw11767step0; decide +kernel
      have hl : raw11767step1Labels = raw11767step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3503 node3503Labels := by rfl

theorem canonical11768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11768 raw11768Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw11768 raw11768Labels = mixedMoment B raw11768step0 raw11768step0Labels := by
      have ha : raw11768step0 = (fun i j => raw11768 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11768step0 raw11768; decide +kernel
      have hl : raw11768step0Labels = raw11768Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11768 raw11768Labels permutation164 permutation4
    mixedMoment B raw11768step0 raw11768step0Labels = mixedMoment B raw11768step1 raw11768step1Labels := by
      have ha : raw11768step1 = -raw11768step0 := by apply Matrix.ext; change ∀ i j, raw11768step1 i j = -(raw11768step0 i j); unfold raw11768step1 raw11768step0; decide +kernel
      have hl : raw11768step1Labels = raw11768step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3532 node3532Labels := by rfl

theorem canonical11769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11769 raw11769Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw11769 raw11769Labels = mixedMoment B raw11769step0 raw11769step0Labels := by
      have hz : ∀ j, raw11769 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11769step0 = (fun i j => raw11769 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11769step0 raw11769; decide +kernel
      have hl : raw11769step0Labels = raw11769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11769 raw11769Labels permutation265 hz
    mixedMoment B raw11769step0 raw11769step0Labels = mixedMoment B raw11769step1 raw11769step1Labels := by
      have ha : raw11769step1 = (fun i j => raw11769step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11769step1 raw11769step0; decide +kernel
      have hl : raw11769step1Labels = raw11769step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11769step0 raw11769step0Labels permutation40 permutation4
    mixedMoment B raw11769step1 raw11769step1Labels = mixedMoment B raw11769step2 raw11769step2Labels := by
      have ha : raw11769step2 = -raw11769step1 := by apply Matrix.ext; change ∀ i j, raw11769step2 i j = -(raw11769step1 i j); unfold raw11769step2 raw11769step1; decide +kernel
      have hl : raw11769step2Labels = raw11769step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical11770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11770 raw11770Labels = mixedMoment B node3503 node3503Labels := by
  calc
    mixedMoment B raw11770 raw11770Labels = mixedMoment B raw11770step0 raw11770step0Labels := by
      have ha : raw11770step0 = (fun i j => raw11770 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11770step0 raw11770; decide +kernel
      have hl : raw11770step0Labels = raw11770Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11770 raw11770Labels permutation158 permutation4
    mixedMoment B raw11770step0 raw11770step0Labels = mixedMoment B raw11770step1 raw11770step1Labels := by
      have ha : raw11770step1 = -raw11770step0 := by apply Matrix.ext; change ∀ i j, raw11770step1 i j = -(raw11770step0 i j); unfold raw11770step1 raw11770step0; decide +kernel
      have hl : raw11770step1Labels = raw11770step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3503 node3503Labels := by rfl

theorem canonical11771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11771 raw11771Labels = mixedMoment B node2983 node2983Labels := by
  calc
    mixedMoment B raw11771 raw11771Labels = mixedMoment B raw11771step0 raw11771step0Labels := by
      have ha : raw11771step0 = (fun i j => raw11771 (permutation646 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11771step0 raw11771; decide +kernel
      have hl : raw11771step0Labels = raw11771Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11771 raw11771Labels permutation646 permutation4
    _ = mixedMoment B node2983 node2983Labels := by rfl

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

theorem canonical7738 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7738 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7738 = injectiveMoment H raw7738step0 := by
      have heq : raw7738step0 = (fun i j => raw7738 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7738 permutation13 permutation1
    _ = injectiveMoment H node65 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical808 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw808 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw808 = injectiveMoment H raw808step0 := by
      have heq : raw808step0 = -raw808 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw808).symm
    injectiveMoment H raw808step0 = injectiveMoment H raw808step1 := by
      have heq : raw808step1 = (fun i j => raw808step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw808step0 permutation9 permutation8
    _ = injectiveMoment H node176 := by rfl

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

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4134 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4134 = injectiveMoment H raw4134step0 := by
      have heq : raw4134step0 = (fun i j => raw4134 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4134 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

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

theorem sound176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node176 = Sparse.eval value176 (momentVector H) := by
  have heq : pivotMatrix176 = (fun u v => node176 (pivotPermutation176 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node176 = injectiveMoment H pivotMatrix176 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix176 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix176 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix176 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (0 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix176 (1 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (1 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix176 (2 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix176 (2 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node176 + (injectiveMoment H (mergeFirst pivotMatrix176 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix176 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix176 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value176, value36, value57, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair416 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node416 node416Labels = Sparse.eval singlePairValue416 (familyPairVector B) := by
  have hp := single_label_three B hB node416
  have hl : node416Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node416 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 1) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node416 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 2) = PairSemantics.raw7738 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node416 PairSemantics.raw7738; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7738 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value26 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 3) = PairSemantics.raw914 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node416 PairSemantics.raw914; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical914 hH).trans (PairSemantics.sound26 hH)
  have hm4 : familyPairMoment B (groupedColumns node416 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value176 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node416 (EqualityPatterns.family3.label 4) = PairSemantics.raw808 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node416 PairSemantics.raw808; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical808 hH).trans (PairSemantics.sound176 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue416, PairSemantics.value0, PairSemantics.value4, PairSemantics.value26, PairSemantics.value65, PairSemantics.value176, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton3120 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node3120 node3120Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node416 node416Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw402 singletonSmall3120
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall3120) = raw402Labels := by decide +kernel
  rw [hl, canonical402 B hB] at h
  have hc0 : mixedMoment B raw402 (Fin.cases (0 : Fin 1) singletonSmall3120) =
      mixedMoment B node416 node416Labels := by
    have ha : raw402 = raw403 := by apply Matrix.ext; unfold raw402 raw403; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall3120 = raw403Labels := by decide +kernel
    rw [ha, hj, canonical403 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
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

theorem sound1212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1212 node1212Labels = Sparse.eval nodeValue1212 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1212) = mixedMoment B node1212 node1212Labels := rfl
  simpa [nodeValue1212, Sparse.eval] using hc.symm

theorem sound1214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1214 node1214Labels = Sparse.eval nodeValue1214 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1214) = mixedMoment B node1214 node1214Labels := rfl
  simpa [nodeValue1214, Sparse.eval] using hc.symm

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

theorem sound1233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1233 node1233Labels = Sparse.eval nodeValue1233 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1233) = mixedMoment B node1233 node1233Labels := rfl
  simpa [nodeValue1233, Sparse.eval] using hc.symm

theorem sound1259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1259 node1259Labels = Sparse.eval nodeValue1259 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1259) = mixedMoment B node1259 node1259Labels := rfl
  simpa [nodeValue1259, Sparse.eval] using hc.symm

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

theorem sound2012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2012 node2012Labels = Sparse.eval nodeValue2012 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2012) = mixedMoment B node2012 node2012Labels := rfl
  simpa [nodeValue2012, Sparse.eval] using hc.symm

theorem sound2020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2020 node2020Labels = Sparse.eval nodeValue2020 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2020) = mixedMoment B node2020 node2020Labels := rfl
  simpa [nodeValue2020, Sparse.eval] using hc.symm

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

theorem sound2471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2471 node2471Labels = Sparse.eval nodeValue2471 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2471) = mixedMoment B node2471 node2471Labels := rfl
  simpa [nodeValue2471, Sparse.eval] using hc.symm

theorem sound2472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2472 node2472Labels = Sparse.eval nodeValue2472 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2472) = mixedMoment B node2472 node2472Labels := rfl
  simpa [nodeValue2472, Sparse.eval] using hc.symm

theorem sound2479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2479 node2479Labels = Sparse.eval nodeValue2479 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2479) = mixedMoment B node2479 node2479Labels := rfl
  simpa [nodeValue2479, Sparse.eval] using hc.symm

theorem sound2481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2481 node2481Labels = Sparse.eval nodeValue2481 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2481) = mixedMoment B node2481 node2481Labels := rfl
  simpa [nodeValue2481, Sparse.eval] using hc.symm

theorem sound2484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2484 node2484Labels = Sparse.eval nodeValue2484 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2484) = mixedMoment B node2484 node2484Labels := rfl
  simpa [nodeValue2484, Sparse.eval] using hc.symm

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

theorem sound2508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2508 node2508Labels = Sparse.eval nodeValue2508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2508) = mixedMoment B node2508 node2508Labels := rfl
  simpa [nodeValue2508, Sparse.eval] using hc.symm

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

theorem sound2614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2614 node2614Labels = Sparse.eval nodeValue2614 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2614) = mixedMoment B node2614 node2614Labels := rfl
  simpa [nodeValue2614, Sparse.eval] using hc.symm

theorem sound2616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2616 node2616Labels = Sparse.eval nodeValue2616 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2616) = mixedMoment B node2616 node2616Labels := rfl
  simpa [nodeValue2616, Sparse.eval] using hc.symm

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

theorem sound2630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2630 node2630Labels = Sparse.eval nodeValue2630 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2630) = mixedMoment B node2630 node2630Labels := rfl
  simpa [nodeValue2630, Sparse.eval] using hc.symm

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

theorem zero2720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2720 node2720Labels = 0 := by
  exact mixedMoment_alpha B hF node2720 node2720Labels 1 permutation203
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

theorem sound2718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2718 node2718Labels = Sparse.eval nodeValue2718 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2718) = mixedMoment B node2718 node2718Labels := rfl
  simpa [nodeValue2718, Sparse.eval] using hc.symm

theorem sound2720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2720 node2720Labels = Sparse.eval nodeValue2720 (mixedVector B) := by
  simpa only [nodeValue2720, Sparse.eval_nil] using zero2720 B _hB _hF

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

theorem sound2739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2739 node2739Labels = Sparse.eval nodeValue2739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2739) = mixedMoment B node2739 node2739Labels := rfl
  simpa [nodeValue2739, Sparse.eval] using hc.symm

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

theorem sound416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node416 node416Labels = Sparse.eval nodeValue416 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue416 (familyPairVector B) := singlePair416 B _hB
    _ = _ := by
      norm_num [singlePairValue416, nodeValue416, Sparse.eval, mixedVector]
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

theorem sound2754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2754 node2754Labels = Sparse.eval nodeValue2754 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2754) = mixedMoment B node2754 node2754Labels := rfl
  simpa [nodeValue2754, Sparse.eval] using hc.symm

theorem sound2757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2757 node2757Labels = Sparse.eval nodeValue2757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2757) = mixedMoment B node2757 node2757Labels := rfl
  simpa [nodeValue2757, Sparse.eval] using hc.symm

theorem sound2763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2763 node2763Labels = Sparse.eval nodeValue2763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2763) = mixedMoment B node2763 node2763Labels := rfl
  simpa [nodeValue2763, Sparse.eval] using hc.symm

theorem sound2764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2764 node2764Labels = Sparse.eval nodeValue2764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2764) = mixedMoment B node2764 node2764Labels := rfl
  simpa [nodeValue2764, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2980 node2980Labels = Sparse.eval nodeValue2980 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2980) = mixedMoment B node2980 node2980Labels := rfl
  simpa [nodeValue2980, Sparse.eval] using hc.symm

theorem sound2983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2983 node2983Labels = Sparse.eval nodeValue2983 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2983) = mixedMoment B node2983 node2983Labels := rfl
  simpa [nodeValue2983, Sparse.eval] using hc.symm

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

theorem sound3034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3034 node3034Labels = Sparse.eval nodeValue3034 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3034) = mixedMoment B node3034 node3034Labels := rfl
  simpa [nodeValue3034, Sparse.eval] using hc.symm

theorem sound3037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3037 node3037Labels = Sparse.eval nodeValue3037 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3037) = mixedMoment B node3037 node3037Labels := rfl
  simpa [nodeValue3037, Sparse.eval] using hc.symm

theorem sound3041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3041 node3041Labels = Sparse.eval nodeValue3041 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3041) = mixedMoment B node3041 node3041Labels := rfl
  simpa [nodeValue3041, Sparse.eval] using hc.symm

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

theorem sound3084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3084 node3084Labels = Sparse.eval nodeValue3084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3084) = mixedMoment B node3084 node3084Labels := rfl
  simpa [nodeValue3084, Sparse.eval] using hc.symm

theorem sound3091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3091 node3091Labels = Sparse.eval nodeValue3091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3091) = mixedMoment B node3091 node3091Labels := rfl
  simpa [nodeValue3091, Sparse.eval] using hc.symm

theorem sound3097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3097 node3097Labels = Sparse.eval nodeValue3097 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3097) = mixedMoment B node3097 node3097Labels := rfl
  simpa [nodeValue3097, Sparse.eval] using hc.symm

theorem sound3120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3120 node3120Labels = Sparse.eval nodeValue3120 (mixedVector B) := by
  have h := singleton3120 B _hB
  rw [sound416 B _hB _hF] at h
  norm_num [nodeValue3120, nodeValue416, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound3199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3199 node3199Labels = Sparse.eval nodeValue3199 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3199) = mixedMoment B node3199 node3199Labels := rfl
  simpa [nodeValue3199, Sparse.eval] using hc.symm

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

theorem sound3373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3373 node3373Labels = Sparse.eval nodeValue3373 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3373) = mixedMoment B node3373 node3373Labels := rfl
  simpa [nodeValue3373, Sparse.eval] using hc.symm

theorem sound3376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3376 node3376Labels = Sparse.eval nodeValue3376 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3376) = mixedMoment B node3376 node3376Labels := rfl
  simpa [nodeValue3376, Sparse.eval] using hc.symm

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

theorem sound3500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3500 node3500Labels = Sparse.eval nodeValue3500 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3500) = mixedMoment B node3500 node3500Labels := rfl
  simpa [nodeValue3500, Sparse.eval] using hc.symm

theorem sound3503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3503 node3503Labels = Sparse.eval nodeValue3503 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3503) = mixedMoment B node3503 node3503Labels := rfl
  simpa [nodeValue3503, Sparse.eval] using hc.symm

theorem sound3505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3505 node3505Labels = Sparse.eval nodeValue3505 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3505) = mixedMoment B node3505 node3505Labels := rfl
  simpa [nodeValue3505, Sparse.eval] using hc.symm

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

theorem zero3525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3525 node3525Labels = 0 := by
  exact mixedMoment_alpha B hF node3525 node3525Labels 1 permutation434
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

theorem sound3525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3525 node3525Labels = Sparse.eval nodeValue3525 (mixedVector B) := by
  simpa only [nodeValue3525, Sparse.eval_nil] using zero3525 B _hB _hF

theorem sound3526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3526 node3526Labels = Sparse.eval nodeValue3526 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3526) = mixedMoment B node3526 node3526Labels := rfl
  simpa [nodeValue3526, Sparse.eval] using hc.symm

theorem sound3532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3532 node3532Labels = Sparse.eval nodeValue3532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3532) = mixedMoment B node3532 node3532Labels := rfl
  simpa [nodeValue3532, Sparse.eval] using hc.symm

theorem sound3534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3534 node3534Labels = Sparse.eval nodeValue3534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3534) = mixedMoment B node3534 node3534Labels := rfl
  simpa [nodeValue3534, Sparse.eval] using hc.symm

theorem sound3572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3572 node3572Labels = Sparse.eval nodeValue3572 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3572) = mixedMoment B node3572 node3572Labels := rfl
  simpa [nodeValue3572, Sparse.eval] using hc.symm

theorem sound3581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3581 node3581Labels = Sparse.eval nodeValue3581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3581) = mixedMoment B node3581 node3581Labels := rfl
  simpa [nodeValue3581, Sparse.eval] using hc.symm

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

theorem sound3805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3805 node3805Labels = Sparse.eval nodeValue3805 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3805) = mixedMoment B node3805 node3805Labels := rfl
  simpa [nodeValue3805, Sparse.eval] using hc.symm

theorem sound3812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3812 node3812Labels = Sparse.eval nodeValue3812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3812) = mixedMoment B node3812 node3812Labels := rfl
  simpa [nodeValue3812, Sparse.eval] using hc.symm

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

theorem sound3874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3874 node3874Labels = Sparse.eval nodeValue3874 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3874) = mixedMoment B node3874 node3874Labels := rfl
  simpa [nodeValue3874, Sparse.eval] using hc.symm

theorem sound3903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3903 node3903Labels = Sparse.eval nodeValue3903 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3903) = mixedMoment B node3903 node3903Labels := rfl
  simpa [nodeValue3903, Sparse.eval] using hc.symm

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

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources21
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq685 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm685 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA685 + difference 0 0) (sourceB685 + difference 0 0) sourceC685) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA685 + difference 0 0) (sourceB685 + difference 0 0) sourceC685) = raw11634 := by
      apply Matrix.ext; unfold tripleCharges sourceA685 sourceB685 sourceC685 difference raw11634; decide +kernel
    rw [ha]
    exact (canonical11634 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA685 + difference 0 1) (sourceB685 + difference 1 0) sourceC685) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA685 + difference 0 1) (sourceB685 + difference 1 0) sourceC685) = raw11635 := by
      apply Matrix.ext; unfold tripleCharges sourceA685 sourceB685 sourceC685 difference raw11635; decide +kernel
    rw [ha]
    exact (canonical11635 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA685 + difference 0 2) (sourceB685 + difference 2 0) sourceC685) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA685 + difference 0 2) (sourceB685 + difference 2 0) sourceC685) = raw11636 := by
      apply Matrix.ext; unfold tripleCharges sourceA685 sourceB685 sourceC685 difference raw11636; decide +kernel
    rw [ha]
    exact (canonical11636 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA685 + difference 0 3) (sourceB685 + difference 3 0) sourceC685) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3903) := by
    have ha : (tripleCharges (sourceA685 + difference 0 3) (sourceB685 + difference 3 0) sourceC685) = raw11637 := by
      apply Matrix.ext; unfold tripleCharges sourceA685 sourceB685 sourceC685 difference raw11637; decide +kernel
    rw [ha]
    exact (canonical11637 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA685 + difference 0 4) (sourceB685 + difference 4 0) sourceC685) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3903) := by
    have ha : (tripleCharges (sourceA685 + difference 0 4) (sourceB685 + difference 4 0) sourceC685) = raw11638 := by
      apply Matrix.ext; unfold tripleCharges sourceA685 sourceB685 sourceC685 difference raw11638; decide +kernel
    rw [ha]
    exact (canonical11638 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA685 + difference 0 5) (sourceB685 + difference 5 0) sourceC685) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA685 + difference 0 5) (sourceB685 + difference 5 0) sourceC685) = raw11639 := by
      apply Matrix.ext; unfold tripleCharges sourceA685 sourceB685 sourceC685 difference raw11639; decide +kernel
    rw [ha]
    exact (canonical11639 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA685 + sourceB685) sourceC685) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA685 + sourceB685) sourceC685) = raw11640 := by
      apply Matrix.ext; unfold doubleCharges sourceA685 sourceB685 sourceC685 raw11640; decide +kernel
    rw [ha]
    exact (canonical11640 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA685 sourceB685 sourceC685
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm685, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq686 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm686 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA686 + difference 0 0) (sourceB686 + difference 0 0) sourceC686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA686 + difference 0 0) (sourceB686 + difference 0 0) sourceC686) = raw11634 := by
      apply Matrix.ext; unfold tripleCharges sourceA686 sourceB686 sourceC686 difference raw11634; decide +kernel
    rw [ha]
    exact (canonical11634 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA686 + difference 1 0) (sourceB686 + difference 0 1) sourceC686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1259) := by
    have ha : (tripleCharges (sourceA686 + difference 1 0) (sourceB686 + difference 0 1) sourceC686) = raw11641 := by
      apply Matrix.ext; unfold tripleCharges sourceA686 sourceB686 sourceC686 difference raw11641; decide +kernel
    rw [ha]
    exact (canonical11641 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA686 + difference 2 0) (sourceB686 + difference 0 2) sourceC686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1233) := by
    have ha : (tripleCharges (sourceA686 + difference 2 0) (sourceB686 + difference 0 2) sourceC686) = raw11642 := by
      apply Matrix.ext; unfold tripleCharges sourceA686 sourceB686 sourceC686 difference raw11642; decide +kernel
    rw [ha]
    exact (canonical11642 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA686 + difference 3 0) (sourceB686 + difference 0 3) sourceC686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1214) := by
    have ha : (tripleCharges (sourceA686 + difference 3 0) (sourceB686 + difference 0 3) sourceC686) = raw11643 := by
      apply Matrix.ext; unfold tripleCharges sourceA686 sourceB686 sourceC686 difference raw11643; decide +kernel
    rw [ha]
    exact (canonical11643 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA686 + difference 4 0) (sourceB686 + difference 0 4) sourceC686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1214) := by
    have ha : (tripleCharges (sourceA686 + difference 4 0) (sourceB686 + difference 0 4) sourceC686) = raw11644 := by
      apply Matrix.ext; unfold tripleCharges sourceA686 sourceB686 sourceC686 difference raw11644; decide +kernel
    rw [ha]
    exact (canonical11644 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA686 + difference 5 0) (sourceB686 + difference 0 5) sourceC686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1212) := by
    have ha : (tripleCharges (sourceA686 + difference 5 0) (sourceB686 + difference 0 5) sourceC686) = raw11645 := by
      apply Matrix.ext; unfold tripleCharges sourceA686 sourceB686 sourceC686 difference raw11645; decide +kernel
    rw [ha]
    exact (canonical11645 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA686 + sourceB686) sourceC686) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA686 + sourceB686) sourceC686) = raw11640 := by
      apply Matrix.ext; unfold doubleCharges sourceA686 sourceB686 sourceC686 raw11640; decide +kernel
    rw [ha]
    exact (canonical11640 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA686 sourceB686 sourceC686
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm686, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq687 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm687 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA687 + difference 1 0) (sourceB687 + difference 0 1) sourceC687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1259) := by
    have ha : (tripleCharges (sourceA687 + difference 1 0) (sourceB687 + difference 0 1) sourceC687) = raw11641 := by
      apply Matrix.ext; unfold tripleCharges sourceA687 sourceB687 sourceC687 difference raw11641; decide +kernel
    rw [ha]
    exact (canonical11641 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA687 + difference 1 1) (sourceB687 + difference 1 1) sourceC687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA687 + difference 1 1) (sourceB687 + difference 1 1) sourceC687) = raw11634 := by
      apply Matrix.ext; unfold tripleCharges sourceA687 sourceB687 sourceC687 difference raw11634; decide +kernel
    rw [ha]
    exact (canonical11634 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA687 + difference 1 2) (sourceB687 + difference 2 1) sourceC687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2630) := by
    have ha : (tripleCharges (sourceA687 + difference 1 2) (sourceB687 + difference 2 1) sourceC687) = raw11646 := by
      apply Matrix.ext; unfold tripleCharges sourceA687 sourceB687 sourceC687 difference raw11646; decide +kernel
    rw [ha]
    exact (canonical11646 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA687 + difference 1 3) (sourceB687 + difference 3 1) sourceC687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA687 + difference 1 3) (sourceB687 + difference 3 1) sourceC687) = raw11647 := by
      apply Matrix.ext; unfold tripleCharges sourceA687 sourceB687 sourceC687 difference raw11647; decide +kernel
    rw [ha]
    exact (canonical11647 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA687 + difference 1 4) (sourceB687 + difference 4 1) sourceC687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA687 + difference 1 4) (sourceB687 + difference 4 1) sourceC687) = raw11648 := by
      apply Matrix.ext; unfold tripleCharges sourceA687 sourceB687 sourceC687 difference raw11648; decide +kernel
    rw [ha]
    exact (canonical11648 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA687 + difference 1 5) (sourceB687 + difference 5 1) sourceC687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2757) := by
    have ha : (tripleCharges (sourceA687 + difference 1 5) (sourceB687 + difference 5 1) sourceC687) = raw11649 := by
      apply Matrix.ext; unfold tripleCharges sourceA687 sourceB687 sourceC687 difference raw11649; decide +kernel
    rw [ha]
    exact (canonical11649 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA687 + sourceB687) sourceC687) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA687 + sourceB687) sourceC687) = raw11640 := by
      apply Matrix.ext; unfold doubleCharges sourceA687 sourceB687 sourceC687 raw11640; decide +kernel
    rw [ha]
    exact (canonical11640 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA687 sourceB687 sourceC687
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm687, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq688 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm688 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA688 + difference 0 1) (sourceB688 + difference 1 0) sourceC688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA688 + difference 0 1) (sourceB688 + difference 1 0) sourceC688) = raw11635 := by
      apply Matrix.ext; unfold tripleCharges sourceA688 sourceB688 sourceC688 difference raw11635; decide +kernel
    rw [ha]
    exact (canonical11635 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA688 + difference 1 1) (sourceB688 + difference 1 1) sourceC688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA688 + difference 1 1) (sourceB688 + difference 1 1) sourceC688) = raw11634 := by
      apply Matrix.ext; unfold tripleCharges sourceA688 sourceB688 sourceC688 difference raw11634; decide +kernel
    rw [ha]
    exact (canonical11634 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA688 + difference 2 1) (sourceB688 + difference 1 2) sourceC688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA688 + difference 2 1) (sourceB688 + difference 1 2) sourceC688) = raw11650 := by
      apply Matrix.ext; unfold tripleCharges sourceA688 sourceB688 sourceC688 difference raw11650; decide +kernel
    rw [ha]
    exact (canonical11650 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA688 + difference 3 1) (sourceB688 + difference 1 3) sourceC688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2481) := by
    have ha : (tripleCharges (sourceA688 + difference 3 1) (sourceB688 + difference 1 3) sourceC688) = raw11651 := by
      apply Matrix.ext; unfold tripleCharges sourceA688 sourceB688 sourceC688 difference raw11651; decide +kernel
    rw [ha]
    exact (canonical11651 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA688 + difference 4 1) (sourceB688 + difference 1 4) sourceC688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2481) := by
    have ha : (tripleCharges (sourceA688 + difference 4 1) (sourceB688 + difference 1 4) sourceC688) = raw11652 := by
      apply Matrix.ext; unfold tripleCharges sourceA688 sourceB688 sourceC688 difference raw11652; decide +kernel
    rw [ha]
    exact (canonical11652 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA688 + difference 5 1) (sourceB688 + difference 1 5) sourceC688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2479) := by
    have ha : (tripleCharges (sourceA688 + difference 5 1) (sourceB688 + difference 1 5) sourceC688) = raw11653 := by
      apply Matrix.ext; unfold tripleCharges sourceA688 sourceB688 sourceC688 difference raw11653; decide +kernel
    rw [ha]
    exact (canonical11653 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA688 + sourceB688) sourceC688) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA688 + sourceB688) sourceC688) = raw11640 := by
      apply Matrix.ext; unfold doubleCharges sourceA688 sourceB688 sourceC688 raw11640; decide +kernel
    rw [ha]
    exact (canonical11640 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA688 sourceB688 sourceC688
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm688, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq689 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm689 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA689 + difference 2 0) (sourceB689 + difference 0 2) sourceC689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1233) := by
    have ha : (tripleCharges (sourceA689 + difference 2 0) (sourceB689 + difference 0 2) sourceC689) = raw11642 := by
      apply Matrix.ext; unfold tripleCharges sourceA689 sourceB689 sourceC689 difference raw11642; decide +kernel
    rw [ha]
    exact (canonical11642 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA689 + difference 2 1) (sourceB689 + difference 1 2) sourceC689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA689 + difference 2 1) (sourceB689 + difference 1 2) sourceC689) = raw11650 := by
      apply Matrix.ext; unfold tripleCharges sourceA689 sourceB689 sourceC689 difference raw11650; decide +kernel
    rw [ha]
    exact (canonical11650 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA689 + difference 2 2) (sourceB689 + difference 2 2) sourceC689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA689 + difference 2 2) (sourceB689 + difference 2 2) sourceC689) = raw11634 := by
      apply Matrix.ext; unfold tripleCharges sourceA689 sourceB689 sourceC689 difference raw11634; decide +kernel
    rw [ha]
    exact (canonical11634 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA689 + difference 2 3) (sourceB689 + difference 3 2) sourceC689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA689 + difference 2 3) (sourceB689 + difference 3 2) sourceC689) = raw11654 := by
      apply Matrix.ext; unfold tripleCharges sourceA689 sourceB689 sourceC689 difference raw11654; decide +kernel
    rw [ha]
    exact (canonical11654 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA689 + difference 2 4) (sourceB689 + difference 4 2) sourceC689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA689 + difference 2 4) (sourceB689 + difference 4 2) sourceC689) = raw11655 := by
      apply Matrix.ext; unfold tripleCharges sourceA689 sourceB689 sourceC689 difference raw11655; decide +kernel
    rw [ha]
    exact (canonical11655 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA689 + difference 2 5) (sourceB689 + difference 5 2) sourceC689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA689 + difference 2 5) (sourceB689 + difference 5 2) sourceC689) = raw11656 := by
      apply Matrix.ext; unfold tripleCharges sourceA689 sourceB689 sourceC689 difference raw11656; decide +kernel
    rw [ha]
    exact (canonical11656 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA689 + sourceB689) sourceC689) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA689 + sourceB689) sourceC689) = raw11640 := by
      apply Matrix.ext; unfold doubleCharges sourceA689 sourceB689 sourceC689 raw11640; decide +kernel
    rw [ha]
    exact (canonical11640 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA689 sourceB689 sourceC689
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm689, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq690 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm690 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA690 + difference 0 2) (sourceB690 + difference 2 0) sourceC690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA690 + difference 0 2) (sourceB690 + difference 2 0) sourceC690) = raw11636 := by
      apply Matrix.ext; unfold tripleCharges sourceA690 sourceB690 sourceC690 difference raw11636; decide +kernel
    rw [ha]
    exact (canonical11636 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA690 + difference 1 2) (sourceB690 + difference 2 1) sourceC690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2630) := by
    have ha : (tripleCharges (sourceA690 + difference 1 2) (sourceB690 + difference 2 1) sourceC690) = raw11646 := by
      apply Matrix.ext; unfold tripleCharges sourceA690 sourceB690 sourceC690 difference raw11646; decide +kernel
    rw [ha]
    exact (canonical11646 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA690 + difference 2 2) (sourceB690 + difference 2 2) sourceC690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA690 + difference 2 2) (sourceB690 + difference 2 2) sourceC690) = raw11634 := by
      apply Matrix.ext; unfold tripleCharges sourceA690 sourceB690 sourceC690 difference raw11634; decide +kernel
    rw [ha]
    exact (canonical11634 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA690 + difference 3 2) (sourceB690 + difference 2 3) sourceC690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2616) := by
    have ha : (tripleCharges (sourceA690 + difference 3 2) (sourceB690 + difference 2 3) sourceC690) = raw11657 := by
      apply Matrix.ext; unfold tripleCharges sourceA690 sourceB690 sourceC690 difference raw11657; decide +kernel
    rw [ha]
    exact (canonical11657 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA690 + difference 4 2) (sourceB690 + difference 2 4) sourceC690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2616) := by
    have ha : (tripleCharges (sourceA690 + difference 4 2) (sourceB690 + difference 2 4) sourceC690) = raw11658 := by
      apply Matrix.ext; unfold tripleCharges sourceA690 sourceB690 sourceC690 difference raw11658; decide +kernel
    rw [ha]
    exact (canonical11658 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA690 + difference 5 2) (sourceB690 + difference 2 5) sourceC690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2614) := by
    have ha : (tripleCharges (sourceA690 + difference 5 2) (sourceB690 + difference 2 5) sourceC690) = raw11659 := by
      apply Matrix.ext; unfold tripleCharges sourceA690 sourceB690 sourceC690 difference raw11659; decide +kernel
    rw [ha]
    exact (canonical11659 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA690 + sourceB690) sourceC690) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA690 + sourceB690) sourceC690) = raw11640 := by
      apply Matrix.ext; unfold doubleCharges sourceA690 sourceB690 sourceC690 raw11640; decide +kernel
    rw [ha]
    exact (canonical11640 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA690 sourceB690 sourceC690
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm690, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq693 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm693 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA693 + difference 0 1) (sourceB693 + difference 1 0) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2728) := by
    have ha : (tripleCharges (sourceA693 + difference 0 1) (sourceB693 + difference 1 0) sourceC693) = raw11720 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11720; decide +kernel
    rw [ha]
    exact (canonical11720 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA693 + difference 0 2) (sourceB693 + difference 2 0) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA693 + difference 0 2) (sourceB693 + difference 2 0) sourceC693) = raw11721 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11721; decide +kernel
    rw [ha]
    exact (canonical11721 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA693 + difference 0 3) (sourceB693 + difference 3 0) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA693 + difference 0 3) (sourceB693 + difference 3 0) sourceC693) = raw11722 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11722; decide +kernel
    rw [ha]
    exact (canonical11722 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA693 + difference 0 4) (sourceB693 + difference 4 0) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA693 + difference 0 4) (sourceB693 + difference 4 0) sourceC693) = raw11723 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11723; decide +kernel
    rw [ha]
    exact (canonical11723 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA693 + difference 0 5) (sourceB693 + difference 5 0) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA693 + difference 0 5) (sourceB693 + difference 5 0) sourceC693) = raw11724 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11724; decide +kernel
    rw [ha]
    exact (canonical11724 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA693 + difference 1 0) (sourceB693 + difference 0 1) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA693 + difference 1 0) (sourceB693 + difference 0 1) sourceC693) = raw11725 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11725; decide +kernel
    rw [ha]
    exact (canonical11725 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA693 + difference 1 2) (sourceB693 + difference 2 1) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA693 + difference 1 2) (sourceB693 + difference 2 1) sourceC693) = raw11726 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11726; decide +kernel
    rw [ha]
    exact (canonical11726 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA693 + difference 1 3) (sourceB693 + difference 3 1) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA693 + difference 1 3) (sourceB693 + difference 3 1) sourceC693) = raw11727 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11727; decide +kernel
    rw [ha]
    exact (canonical11727 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA693 + difference 1 4) (sourceB693 + difference 4 1) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA693 + difference 1 4) (sourceB693 + difference 4 1) sourceC693) = raw11728 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11728; decide +kernel
    rw [ha]
    exact (canonical11728 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA693 + difference 1 5) (sourceB693 + difference 5 1) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA693 + difference 1 5) (sourceB693 + difference 5 1) sourceC693) = raw11729 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11729; decide +kernel
    rw [ha]
    exact (canonical11729 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA693 + difference 2 0) (sourceB693 + difference 0 2) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA693 + difference 2 0) (sourceB693 + difference 0 2) sourceC693) = raw11730 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11730; decide +kernel
    rw [ha]
    exact (canonical11730 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA693 + difference 2 1) (sourceB693 + difference 1 2) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3041) := by
    have ha : (tripleCharges (sourceA693 + difference 2 1) (sourceB693 + difference 1 2) sourceC693) = raw11731 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11731; decide +kernel
    rw [ha]
    exact (canonical11731 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA693 + difference 2 3) (sourceB693 + difference 3 2) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3034) := by
    have ha : (tripleCharges (sourceA693 + difference 2 3) (sourceB693 + difference 3 2) sourceC693) = raw11732 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11732; decide +kernel
    rw [ha]
    exact (canonical11732 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA693 + difference 2 4) (sourceB693 + difference 4 2) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3034) := by
    have ha : (tripleCharges (sourceA693 + difference 2 4) (sourceB693 + difference 4 2) sourceC693) = raw11733 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11733; decide +kernel
    rw [ha]
    exact (canonical11733 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA693 + difference 2 5) (sourceB693 + difference 5 2) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA693 + difference 2 5) (sourceB693 + difference 5 2) sourceC693) = raw11734 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11734; decide +kernel
    rw [ha]
    exact (canonical11734 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA693 + difference 3 0) (sourceB693 + difference 0 3) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3204) := by
    have ha : (tripleCharges (sourceA693 + difference 3 0) (sourceB693 + difference 0 3) sourceC693) = raw11735 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11735; decide +kernel
    rw [ha]
    exact (canonical11735 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA693 + difference 3 1) (sourceB693 + difference 1 3) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3091) := by
    have ha : (tripleCharges (sourceA693 + difference 3 1) (sourceB693 + difference 1 3) sourceC693) = raw11736 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11736; decide +kernel
    rw [ha]
    exact (canonical11736 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA693 + difference 3 2) (sourceB693 + difference 2 3) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA693 + difference 3 2) (sourceB693 + difference 2 3) sourceC693) = raw11737 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11737; decide +kernel
    rw [ha]
    exact (canonical11737 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA693 + difference 3 4) (sourceB693 + difference 4 3) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3084) := by
    have ha : (tripleCharges (sourceA693 + difference 3 4) (sourceB693 + difference 4 3) sourceC693) = raw11738 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11738; decide +kernel
    rw [ha]
    exact (canonical11738 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA693 + difference 3 5) (sourceB693 + difference 5 3) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA693 + difference 3 5) (sourceB693 + difference 5 3) sourceC693) = raw11739 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11739; decide +kernel
    rw [ha]
    exact (canonical11739 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA693 + difference 4 0) (sourceB693 + difference 0 4) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3204) := by
    have ha : (tripleCharges (sourceA693 + difference 4 0) (sourceB693 + difference 0 4) sourceC693) = raw11740 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11740; decide +kernel
    rw [ha]
    exact (canonical11740 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA693 + difference 4 1) (sourceB693 + difference 1 4) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3091) := by
    have ha : (tripleCharges (sourceA693 + difference 4 1) (sourceB693 + difference 1 4) sourceC693) = raw11741 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11741; decide +kernel
    rw [ha]
    exact (canonical11741 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA693 + difference 4 2) (sourceB693 + difference 2 4) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA693 + difference 4 2) (sourceB693 + difference 2 4) sourceC693) = raw11742 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11742; decide +kernel
    rw [ha]
    exact (canonical11742 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA693 + difference 4 3) (sourceB693 + difference 3 4) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3084) := by
    have ha : (tripleCharges (sourceA693 + difference 4 3) (sourceB693 + difference 3 4) sourceC693) = raw11743 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11743; decide +kernel
    rw [ha]
    exact (canonical11743 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA693 + difference 4 5) (sourceB693 + difference 5 4) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA693 + difference 4 5) (sourceB693 + difference 5 4) sourceC693) = raw11744 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11744; decide +kernel
    rw [ha]
    exact (canonical11744 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA693 + difference 5 0) (sourceB693 + difference 0 5) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA693 + difference 5 0) (sourceB693 + difference 0 5) sourceC693) = raw11745 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11745; decide +kernel
    rw [ha]
    exact (canonical11745 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA693 + difference 5 1) (sourceB693 + difference 1 5) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2472) := by
    have ha : (tripleCharges (sourceA693 + difference 5 1) (sourceB693 + difference 1 5) sourceC693) = raw11746 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11746; decide +kernel
    rw [ha]
    exact (canonical11746 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA693 + difference 5 2) (sourceB693 + difference 2 5) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA693 + difference 5 2) (sourceB693 + difference 2 5) sourceC693) = raw11747 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11747; decide +kernel
    rw [ha]
    exact (canonical11747 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA693 + difference 5 3) (sourceB693 + difference 3 5) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2484) := by
    have ha : (tripleCharges (sourceA693 + difference 5 3) (sourceB693 + difference 3 5) sourceC693) = raw11748 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11748; decide +kernel
    rw [ha]
    exact (canonical11748 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA693 + difference 5 4) (sourceB693 + difference 4 5) sourceC693) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2484) := by
    have ha : (tripleCharges (sourceA693 + difference 5 4) (sourceB693 + difference 4 5) sourceC693) = raw11749 := by
      apply Matrix.ext; unfold tripleCharges sourceA693 sourceB693 sourceC693 difference raw11749; decide +kernel
    rw [ha]
    exact (canonical11749 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA693 sourceB693 sourceC693
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm693, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq694 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm694 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA694 + difference 0 0) (sourceB694 + difference 0 0) sourceC694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA694 + difference 0 0) (sourceB694 + difference 0 0) sourceC694) = raw11750 := by
      apply Matrix.ext; unfold tripleCharges sourceA694 sourceB694 sourceC694 difference raw11750; decide +kernel
    rw [ha]
    exact (canonical11750 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA694 + difference 0 1) (sourceB694 + difference 1 0) sourceC694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3505) := by
    have ha : (tripleCharges (sourceA694 + difference 0 1) (sourceB694 + difference 1 0) sourceC694) = raw11751 := by
      apply Matrix.ext; unfold tripleCharges sourceA694 sourceB694 sourceC694 difference raw11751; decide +kernel
    rw [ha]
    exact (canonical11751 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA694 + difference 0 2) (sourceB694 + difference 2 0) sourceC694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA694 + difference 0 2) (sourceB694 + difference 2 0) sourceC694) = raw11752 := by
      apply Matrix.ext; unfold tripleCharges sourceA694 sourceB694 sourceC694 difference raw11752; decide +kernel
    rw [ha]
    exact (canonical11752 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA694 + difference 0 3) (sourceB694 + difference 3 0) sourceC694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA694 + difference 0 3) (sourceB694 + difference 3 0) sourceC694) = raw11753 := by
      apply Matrix.ext; unfold tripleCharges sourceA694 sourceB694 sourceC694 difference raw11753; decide +kernel
    rw [ha]
    exact (canonical11753 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA694 + difference 0 4) (sourceB694 + difference 4 0) sourceC694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA694 + difference 0 4) (sourceB694 + difference 4 0) sourceC694) = raw11754 := by
      apply Matrix.ext; unfold tripleCharges sourceA694 sourceB694 sourceC694 difference raw11754; decide +kernel
    rw [ha]
    exact (canonical11754 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA694 + difference 0 5) (sourceB694 + difference 5 0) sourceC694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA694 + difference 0 5) (sourceB694 + difference 5 0) sourceC694) = raw11755 := by
      apply Matrix.ext; unfold tripleCharges sourceA694 sourceB694 sourceC694 difference raw11755; decide +kernel
    rw [ha]
    exact (canonical11755 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA694 + sourceB694) sourceC694) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA694 + sourceB694) sourceC694) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA694 sourceB694 sourceC694 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA694 sourceB694 sourceC694
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm694, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq695 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm695 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA695 + difference 0 1) (sourceB695 + difference 1 0) sourceC695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3505) := by
    have ha : (tripleCharges (sourceA695 + difference 0 1) (sourceB695 + difference 1 0) sourceC695) = raw11751 := by
      apply Matrix.ext; unfold tripleCharges sourceA695 sourceB695 sourceC695 difference raw11751; decide +kernel
    rw [ha]
    exact (canonical11751 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA695 + difference 1 1) (sourceB695 + difference 1 1) sourceC695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA695 + difference 1 1) (sourceB695 + difference 1 1) sourceC695) = raw11750 := by
      apply Matrix.ext; unfold tripleCharges sourceA695 sourceB695 sourceC695 difference raw11750; decide +kernel
    rw [ha]
    exact (canonical11750 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA695 + difference 2 1) (sourceB695 + difference 1 2) sourceC695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3373) := by
    have ha : (tripleCharges (sourceA695 + difference 2 1) (sourceB695 + difference 1 2) sourceC695) = raw11757 := by
      apply Matrix.ext; unfold tripleCharges sourceA695 sourceB695 sourceC695 difference raw11757; decide +kernel
    rw [ha]
    exact (canonical11757 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA695 + difference 3 1) (sourceB695 + difference 1 3) sourceC695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA695 + difference 3 1) (sourceB695 + difference 1 3) sourceC695) = raw11758 := by
      apply Matrix.ext; unfold tripleCharges sourceA695 sourceB695 sourceC695 difference raw11758; decide +kernel
    rw [ha]
    exact (canonical11758 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA695 + difference 4 1) (sourceB695 + difference 1 4) sourceC695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA695 + difference 4 1) (sourceB695 + difference 1 4) sourceC695) = raw11759 := by
      apply Matrix.ext; unfold tripleCharges sourceA695 sourceB695 sourceC695 difference raw11759; decide +kernel
    rw [ha]
    exact (canonical11759 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA695 + difference 5 1) (sourceB695 + difference 1 5) sourceC695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2980) := by
    have ha : (tripleCharges (sourceA695 + difference 5 1) (sourceB695 + difference 1 5) sourceC695) = raw11760 := by
      apply Matrix.ext; unfold tripleCharges sourceA695 sourceB695 sourceC695 difference raw11760; decide +kernel
    rw [ha]
    exact (canonical11760 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA695 + sourceB695) sourceC695) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA695 + sourceB695) sourceC695) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA695 sourceB695 sourceC695 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA695 sourceB695 sourceC695
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm695, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq696 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm696 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA696 + difference 2 0) (sourceB696 + difference 0 2) sourceC696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2012) := by
    have ha : (tripleCharges (sourceA696 + difference 2 0) (sourceB696 + difference 0 2) sourceC696) = raw11761 := by
      apply Matrix.ext; unfold tripleCharges sourceA696 sourceB696 sourceC696 difference raw11761; decide +kernel
    rw [ha]
    exact (canonical11761 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA696 + difference 2 1) (sourceB696 + difference 1 2) sourceC696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3373) := by
    have ha : (tripleCharges (sourceA696 + difference 2 1) (sourceB696 + difference 1 2) sourceC696) = raw11757 := by
      apply Matrix.ext; unfold tripleCharges sourceA696 sourceB696 sourceC696 difference raw11757; decide +kernel
    rw [ha]
    exact (canonical11757 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA696 + difference 2 2) (sourceB696 + difference 2 2) sourceC696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA696 + difference 2 2) (sourceB696 + difference 2 2) sourceC696) = raw11750 := by
      apply Matrix.ext; unfold tripleCharges sourceA696 sourceB696 sourceC696 difference raw11750; decide +kernel
    rw [ha]
    exact (canonical11750 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA696 + difference 2 3) (sourceB696 + difference 3 2) sourceC696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3500) := by
    have ha : (tripleCharges (sourceA696 + difference 2 3) (sourceB696 + difference 3 2) sourceC696) = raw11762 := by
      apply Matrix.ext; unfold tripleCharges sourceA696 sourceB696 sourceC696 difference raw11762; decide +kernel
    rw [ha]
    exact (canonical11762 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA696 + difference 2 4) (sourceB696 + difference 4 2) sourceC696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3500) := by
    have ha : (tripleCharges (sourceA696 + difference 2 4) (sourceB696 + difference 4 2) sourceC696) = raw11763 := by
      apply Matrix.ext; unfold tripleCharges sourceA696 sourceB696 sourceC696 difference raw11763; decide +kernel
    rw [ha]
    exact (canonical11763 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA696 + difference 2 5) (sourceB696 + difference 5 2) sourceC696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA696 + difference 2 5) (sourceB696 + difference 5 2) sourceC696) = raw11764 := by
      apply Matrix.ext; unfold tripleCharges sourceA696 sourceB696 sourceC696 difference raw11764; decide +kernel
    rw [ha]
    exact (canonical11764 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA696 + sourceB696) sourceC696) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA696 + sourceB696) sourceC696) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA696 sourceB696 sourceC696 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA696 sourceB696 sourceC696
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm696, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq697 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm697 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA697 + difference 3 0) (sourceB697 + difference 0 3) sourceC697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2020) := by
    have ha : (tripleCharges (sourceA697 + difference 3 0) (sourceB697 + difference 0 3) sourceC697) = raw11765 := by
      apply Matrix.ext; unfold tripleCharges sourceA697 sourceB697 sourceC697 difference raw11765; decide +kernel
    rw [ha]
    exact (canonical11765 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA697 + difference 3 1) (sourceB697 + difference 1 3) sourceC697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA697 + difference 3 1) (sourceB697 + difference 1 3) sourceC697) = raw11758 := by
      apply Matrix.ext; unfold tripleCharges sourceA697 sourceB697 sourceC697 difference raw11758; decide +kernel
    rw [ha]
    exact (canonical11758 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA697 + difference 3 2) (sourceB697 + difference 2 3) sourceC697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA697 + difference 3 2) (sourceB697 + difference 2 3) sourceC697) = raw11766 := by
      apply Matrix.ext; unfold tripleCharges sourceA697 sourceB697 sourceC697 difference raw11766; decide +kernel
    rw [ha]
    exact (canonical11766 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA697 + difference 3 3) (sourceB697 + difference 3 3) sourceC697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA697 + difference 3 3) (sourceB697 + difference 3 3) sourceC697) = raw11750 := by
      apply Matrix.ext; unfold tripleCharges sourceA697 sourceB697 sourceC697 difference raw11750; decide +kernel
    rw [ha]
    exact (canonical11750 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA697 + difference 3 4) (sourceB697 + difference 4 3) sourceC697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA697 + difference 3 4) (sourceB697 + difference 4 3) sourceC697) = raw11767 := by
      apply Matrix.ext; unfold tripleCharges sourceA697 sourceB697 sourceC697 difference raw11767; decide +kernel
    rw [ha]
    exact (canonical11767 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA697 + difference 3 5) (sourceB697 + difference 5 3) sourceC697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA697 + difference 3 5) (sourceB697 + difference 5 3) sourceC697) = raw11768 := by
      apply Matrix.ext; unfold tripleCharges sourceA697 sourceB697 sourceC697 difference raw11768; decide +kernel
    rw [ha]
    exact (canonical11768 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA697 + sourceB697) sourceC697) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA697 + sourceB697) sourceC697) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA697 sourceB697 sourceC697 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA697 sourceB697 sourceC697
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm697, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq698 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm698 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA698 + difference 0 3) (sourceB698 + difference 3 0) sourceC698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA698 + difference 0 3) (sourceB698 + difference 3 0) sourceC698) = raw11753 := by
      apply Matrix.ext; unfold tripleCharges sourceA698 sourceB698 sourceC698 difference raw11753; decide +kernel
    rw [ha]
    exact (canonical11753 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA698 + difference 1 3) (sourceB698 + difference 3 1) sourceC698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA698 + difference 1 3) (sourceB698 + difference 3 1) sourceC698) = raw11769 := by
      apply Matrix.ext; unfold tripleCharges sourceA698 sourceB698 sourceC698 difference raw11769; decide +kernel
    rw [ha]
    exact (canonical11769 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA698 + difference 2 3) (sourceB698 + difference 3 2) sourceC698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3500) := by
    have ha : (tripleCharges (sourceA698 + difference 2 3) (sourceB698 + difference 3 2) sourceC698) = raw11762 := by
      apply Matrix.ext; unfold tripleCharges sourceA698 sourceB698 sourceC698 difference raw11762; decide +kernel
    rw [ha]
    exact (canonical11762 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA698 + difference 3 3) (sourceB698 + difference 3 3) sourceC698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA698 + difference 3 3) (sourceB698 + difference 3 3) sourceC698) = raw11750 := by
      apply Matrix.ext; unfold tripleCharges sourceA698 sourceB698 sourceC698 difference raw11750; decide +kernel
    rw [ha]
    exact (canonical11750 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA698 + difference 4 3) (sourceB698 + difference 3 4) sourceC698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA698 + difference 4 3) (sourceB698 + difference 3 4) sourceC698) = raw11770 := by
      apply Matrix.ext; unfold tripleCharges sourceA698 sourceB698 sourceC698 difference raw11770; decide +kernel
    rw [ha]
    exact (canonical11770 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA698 + difference 5 3) (sourceB698 + difference 3 5) sourceC698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2983) := by
    have ha : (tripleCharges (sourceA698 + difference 5 3) (sourceB698 + difference 3 5) sourceC698) = raw11771 := by
      apply Matrix.ext; unfold tripleCharges sourceA698 sourceB698 sourceC698 difference raw11771; decide +kernel
    rw [ha]
    exact (canonical11771 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA698 + sourceB698) sourceC698) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA698 + sourceB698) sourceC698) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA698 sourceB698 sourceC698 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA698 sourceB698 sourceC698
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm698, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck593 : Integer.Sparse.reindex keyMap MixedData.row593 = numericRow593 := by decide +kernel

theorem numericCheck593 (x : Master → ℝ) : Integer.Sparse.eval numericRow593 x =
    (1 : ℝ) * reducedSource593 x := by
  norm_num [numericRow593, reducedSource593, Integer.Sparse.eval, Sparse.eval, nodeValue2720, nodeValue3805, nodeValue3812, nodeValue3874, nodeValue3903, nodeValue4092]

theorem reindexCheck594 : Integer.Sparse.reindex keyMap MixedData.row594 = numericRow594 := by decide +kernel

theorem numericCheck594 (x : Master → ℝ) : Integer.Sparse.eval numericRow594 x =
    (1 : ℝ) * reducedSource594 x := by
  norm_num [numericRow594, reducedSource594, Integer.Sparse.eval, Sparse.eval, nodeValue1212, nodeValue1214, nodeValue1233, nodeValue1259, nodeValue2720, nodeValue4092]

theorem reindexCheck595 : Integer.Sparse.reindex keyMap MixedData.row595 = numericRow595 := by decide +kernel

theorem numericCheck595 (x : Master → ℝ) : Integer.Sparse.eval numericRow595 x =
    (1 : ℝ) * reducedSource595 x := by
  norm_num [numericRow595, reducedSource595, Integer.Sparse.eval, Sparse.eval, nodeValue1259, nodeValue2630, nodeValue2720, nodeValue2757, nodeValue2763, nodeValue4092]

theorem reindexCheck596 : Integer.Sparse.reindex keyMap MixedData.row596 = numericRow596 := by decide +kernel

theorem numericCheck596 (x : Master → ℝ) : Integer.Sparse.eval numericRow596 x =
    (1 : ℝ) * reducedSource596 x := by
  norm_num [numericRow596, reducedSource596, Integer.Sparse.eval, Sparse.eval, nodeValue2479, nodeValue2481, nodeValue2508, nodeValue2720, nodeValue3805, nodeValue4092]

theorem reindexCheck597 : Integer.Sparse.reindex keyMap MixedData.row597 = numericRow597 := by decide +kernel

theorem numericCheck597 (x : Master → ℝ) : Integer.Sparse.eval numericRow597 x =
    (1 : ℝ) * reducedSource597 x := by
  norm_num [numericRow597, reducedSource597, Integer.Sparse.eval, Sparse.eval, nodeValue1233, nodeValue2508, nodeValue2720, nodeValue2730, nodeValue2739, nodeValue4092]

theorem reindexCheck598 : Integer.Sparse.reindex keyMap MixedData.row598 = numericRow598 := by decide +kernel

theorem numericCheck598 (x : Master → ℝ) : Integer.Sparse.eval numericRow598 x =
    (1 : ℝ) * reducedSource598 x := by
  norm_num [numericRow598, reducedSource598, Integer.Sparse.eval, Sparse.eval, nodeValue2614, nodeValue2616, nodeValue2630, nodeValue2720, nodeValue3874, nodeValue4092]

theorem reindexCheck601 : Integer.Sparse.reindex keyMap MixedData.row601 = numericRow601 := by decide +kernel

theorem numericCheck601 (x : Master → ℝ) : Integer.Sparse.eval numericRow601 x =
    (8640 : ℝ) * reducedSource601 x := by
  norm_num [numericRow601, reducedSource601, Integer.Sparse.eval, Sparse.eval, nodeValue2471, nodeValue2472, nodeValue2484, nodeValue2718, nodeValue2721, nodeValue2728, nodeValue2754, nodeValue2764, nodeValue3034, nodeValue3037, nodeValue3041, nodeValue3084, nodeValue3087, nodeValue3091, nodeValue3097, nodeValue3100, nodeValue3109, nodeValue3120, nodeValue3199, nodeValue3204, nodeValue3227] <;> ring

theorem reindexCheck602 : Integer.Sparse.reindex keyMap MixedData.row602 = numericRow602 := by decide +kernel

theorem numericCheck602 (x : Master → ℝ) : Integer.Sparse.eval numericRow602 x =
    (1 : ℝ) * reducedSource602 x := by
  norm_num [numericRow602, reducedSource602, Integer.Sparse.eval, Sparse.eval, nodeValue3503, nodeValue3505, nodeValue3525, nodeValue3532, nodeValue3581, nodeValue4083]

theorem reindexCheck603 : Integer.Sparse.reindex keyMap MixedData.row603 = numericRow603 := by decide +kernel

theorem numericCheck603 (x : Master → ℝ) : Integer.Sparse.eval numericRow603 x =
    (1 : ℝ) * reducedSource603 x := by
  norm_num [numericRow603, reducedSource603, Integer.Sparse.eval, Sparse.eval, nodeValue2980, nodeValue3373, nodeValue3376, nodeValue3505, nodeValue3525, nodeValue4083]

theorem reindexCheck604 : Integer.Sparse.reindex keyMap MixedData.row604 = numericRow604 := by decide +kernel

theorem numericCheck604 (x : Master → ℝ) : Integer.Sparse.eval numericRow604 x =
    (1 : ℝ) * reducedSource604 x := by
  norm_num [numericRow604, reducedSource604, Integer.Sparse.eval, Sparse.eval, nodeValue2012, nodeValue3373, nodeValue3500, nodeValue3525, nodeValue3526, nodeValue4083]

theorem reindexCheck605 : Integer.Sparse.reindex keyMap MixedData.row605 = numericRow605 := by decide +kernel

theorem numericCheck605 (x : Master → ℝ) : Integer.Sparse.eval numericRow605 x =
    (1 : ℝ) * reducedSource605 x := by
  norm_num [numericRow605, reducedSource605, Integer.Sparse.eval, Sparse.eval, nodeValue2020, nodeValue3376, nodeValue3503, nodeValue3525, nodeValue3532, nodeValue3534, nodeValue4083]

theorem reindexCheck606 : Integer.Sparse.reindex keyMap MixedData.row606 = numericRow606 := by decide +kernel

theorem numericCheck606 (x : Master → ℝ) : Integer.Sparse.eval numericRow606 x =
    (1 : ℝ) * reducedSource606 x := by
  norm_num [numericRow606, reducedSource606, Integer.Sparse.eval, Sparse.eval, nodeValue2983, nodeValue3500, nodeValue3503, nodeValue3525, nodeValue3572, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero593 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource593 (mixedVector B) = 0 := by
  have h2720 : mixedVector B (Sum.inr 2720) = Sparse.eval nodeValue2720 (mixedVector B) := by
    change mixedMoment B node2720 node2720Labels = _
    exact sound2720 B hB hF
  have h3805 : mixedVector B (Sum.inr 3805) = Sparse.eval nodeValue3805 (mixedVector B) := by
    change mixedMoment B node3805 node3805Labels = _
    exact sound3805 B hB hF
  have h3812 : mixedVector B (Sum.inr 3812) = Sparse.eval nodeValue3812 (mixedVector B) := by
    change mixedMoment B node3812 node3812Labels = _
    exact sound3812 B hB hF
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h3903 : mixedVector B (Sum.inr 3903) = Sparse.eval nodeValue3903 (mixedVector B) := by
    change mixedMoment B node3903 node3903Labels = _
    exact sound3903 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm685, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2720, h3805, h3812, h3874, h3903, h4092, reducedSource593] using sourceEq685 B hB

theorem rowSound593 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row593 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck593, numericCheck593, reducedZero593 B hB hF, mul_zero]

theorem reducedZero594 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource594 (mixedVector B) = 0 := by
  have h1212 : mixedVector B (Sum.inr 1212) = Sparse.eval nodeValue1212 (mixedVector B) := by
    change mixedMoment B node1212 node1212Labels = _
    exact sound1212 B hB hF
  have h1214 : mixedVector B (Sum.inr 1214) = Sparse.eval nodeValue1214 (mixedVector B) := by
    change mixedMoment B node1214 node1214Labels = _
    exact sound1214 B hB hF
  have h1233 : mixedVector B (Sum.inr 1233) = Sparse.eval nodeValue1233 (mixedVector B) := by
    change mixedMoment B node1233 node1233Labels = _
    exact sound1233 B hB hF
  have h1259 : mixedVector B (Sum.inr 1259) = Sparse.eval nodeValue1259 (mixedVector B) := by
    change mixedMoment B node1259 node1259Labels = _
    exact sound1259 B hB hF
  have h2720 : mixedVector B (Sum.inr 2720) = Sparse.eval nodeValue2720 (mixedVector B) := by
    change mixedMoment B node2720 node2720Labels = _
    exact sound2720 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm686, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1212, h1214, h1233, h1259, h2720, h4092, reducedSource594] using sourceEq686 B hB

theorem rowSound594 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row594 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck594, numericCheck594, reducedZero594 B hB hF, mul_zero]

theorem reducedZero595 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource595 (mixedVector B) = 0 := by
  have h1259 : mixedVector B (Sum.inr 1259) = Sparse.eval nodeValue1259 (mixedVector B) := by
    change mixedMoment B node1259 node1259Labels = _
    exact sound1259 B hB hF
  have h2630 : mixedVector B (Sum.inr 2630) = Sparse.eval nodeValue2630 (mixedVector B) := by
    change mixedMoment B node2630 node2630Labels = _
    exact sound2630 B hB hF
  have h2720 : mixedVector B (Sum.inr 2720) = Sparse.eval nodeValue2720 (mixedVector B) := by
    change mixedMoment B node2720 node2720Labels = _
    exact sound2720 B hB hF
  have h2757 : mixedVector B (Sum.inr 2757) = Sparse.eval nodeValue2757 (mixedVector B) := by
    change mixedMoment B node2757 node2757Labels = _
    exact sound2757 B hB hF
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm687, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1259, h2630, h2720, h2757, h2763, h4092, reducedSource595] using sourceEq687 B hB

theorem rowSound595 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row595 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck595, numericCheck595, reducedZero595 B hB hF, mul_zero]

theorem reducedZero596 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource596 (mixedVector B) = 0 := by
  have h2479 : mixedVector B (Sum.inr 2479) = Sparse.eval nodeValue2479 (mixedVector B) := by
    change mixedMoment B node2479 node2479Labels = _
    exact sound2479 B hB hF
  have h2481 : mixedVector B (Sum.inr 2481) = Sparse.eval nodeValue2481 (mixedVector B) := by
    change mixedMoment B node2481 node2481Labels = _
    exact sound2481 B hB hF
  have h2508 : mixedVector B (Sum.inr 2508) = Sparse.eval nodeValue2508 (mixedVector B) := by
    change mixedMoment B node2508 node2508Labels = _
    exact sound2508 B hB hF
  have h2720 : mixedVector B (Sum.inr 2720) = Sparse.eval nodeValue2720 (mixedVector B) := by
    change mixedMoment B node2720 node2720Labels = _
    exact sound2720 B hB hF
  have h3805 : mixedVector B (Sum.inr 3805) = Sparse.eval nodeValue3805 (mixedVector B) := by
    change mixedMoment B node3805 node3805Labels = _
    exact sound3805 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm688, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2479, h2481, h2508, h2720, h3805, h4092, reducedSource596] using sourceEq688 B hB

theorem rowSound596 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row596 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck596, numericCheck596, reducedZero596 B hB hF, mul_zero]

theorem reducedZero597 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource597 (mixedVector B) = 0 := by
  have h1233 : mixedVector B (Sum.inr 1233) = Sparse.eval nodeValue1233 (mixedVector B) := by
    change mixedMoment B node1233 node1233Labels = _
    exact sound1233 B hB hF
  have h2508 : mixedVector B (Sum.inr 2508) = Sparse.eval nodeValue2508 (mixedVector B) := by
    change mixedMoment B node2508 node2508Labels = _
    exact sound2508 B hB hF
  have h2720 : mixedVector B (Sum.inr 2720) = Sparse.eval nodeValue2720 (mixedVector B) := by
    change mixedMoment B node2720 node2720Labels = _
    exact sound2720 B hB hF
  have h2730 : mixedVector B (Sum.inr 2730) = Sparse.eval nodeValue2730 (mixedVector B) := by
    change mixedMoment B node2730 node2730Labels = _
    exact sound2730 B hB hF
  have h2739 : mixedVector B (Sum.inr 2739) = Sparse.eval nodeValue2739 (mixedVector B) := by
    change mixedMoment B node2739 node2739Labels = _
    exact sound2739 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm689, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1233, h2508, h2720, h2730, h2739, h4092, reducedSource597] using sourceEq689 B hB

theorem rowSound597 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row597 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck597, numericCheck597, reducedZero597 B hB hF, mul_zero]

theorem reducedZero598 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource598 (mixedVector B) = 0 := by
  have h2614 : mixedVector B (Sum.inr 2614) = Sparse.eval nodeValue2614 (mixedVector B) := by
    change mixedMoment B node2614 node2614Labels = _
    exact sound2614 B hB hF
  have h2616 : mixedVector B (Sum.inr 2616) = Sparse.eval nodeValue2616 (mixedVector B) := by
    change mixedMoment B node2616 node2616Labels = _
    exact sound2616 B hB hF
  have h2630 : mixedVector B (Sum.inr 2630) = Sparse.eval nodeValue2630 (mixedVector B) := by
    change mixedMoment B node2630 node2630Labels = _
    exact sound2630 B hB hF
  have h2720 : mixedVector B (Sum.inr 2720) = Sparse.eval nodeValue2720 (mixedVector B) := by
    change mixedMoment B node2720 node2720Labels = _
    exact sound2720 B hB hF
  have h3874 : mixedVector B (Sum.inr 3874) = Sparse.eval nodeValue3874 (mixedVector B) := by
    change mixedMoment B node3874 node3874Labels = _
    exact sound3874 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm690, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2614, h2616, h2630, h2720, h3874, h4092, reducedSource598] using sourceEq690 B hB

theorem rowSound598 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row598 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck598, numericCheck598, reducedZero598 B hB hF, mul_zero]

theorem reducedZero601 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource601 (mixedVector B) = 0 := by
  have h2471 : mixedVector B (Sum.inr 2471) = Sparse.eval nodeValue2471 (mixedVector B) := by
    change mixedMoment B node2471 node2471Labels = _
    exact sound2471 B hB hF
  have h2472 : mixedVector B (Sum.inr 2472) = Sparse.eval nodeValue2472 (mixedVector B) := by
    change mixedMoment B node2472 node2472Labels = _
    exact sound2472 B hB hF
  have h2484 : mixedVector B (Sum.inr 2484) = Sparse.eval nodeValue2484 (mixedVector B) := by
    change mixedMoment B node2484 node2484Labels = _
    exact sound2484 B hB hF
  have h2718 : mixedVector B (Sum.inr 2718) = Sparse.eval nodeValue2718 (mixedVector B) := by
    change mixedMoment B node2718 node2718Labels = _
    exact sound2718 B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h2728 : mixedVector B (Sum.inr 2728) = Sparse.eval nodeValue2728 (mixedVector B) := by
    change mixedMoment B node2728 node2728Labels = _
    exact sound2728 B hB hF
  have h2754 : mixedVector B (Sum.inr 2754) = Sparse.eval nodeValue2754 (mixedVector B) := by
    change mixedMoment B node2754 node2754Labels = _
    exact sound2754 B hB hF
  have h2764 : mixedVector B (Sum.inr 2764) = Sparse.eval nodeValue2764 (mixedVector B) := by
    change mixedMoment B node2764 node2764Labels = _
    exact sound2764 B hB hF
  have h3034 : mixedVector B (Sum.inr 3034) = Sparse.eval nodeValue3034 (mixedVector B) := by
    change mixedMoment B node3034 node3034Labels = _
    exact sound3034 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3041 : mixedVector B (Sum.inr 3041) = Sparse.eval nodeValue3041 (mixedVector B) := by
    change mixedMoment B node3041 node3041Labels = _
    exact sound3041 B hB hF
  have h3084 : mixedVector B (Sum.inr 3084) = Sparse.eval nodeValue3084 (mixedVector B) := by
    change mixedMoment B node3084 node3084Labels = _
    exact sound3084 B hB hF
  have h3087 : mixedVector B (Sum.inr 3087) = Sparse.eval nodeValue3087 (mixedVector B) := by
    change mixedMoment B node3087 node3087Labels = _
    exact sound3087_e B hB hF
  have h3091 : mixedVector B (Sum.inr 3091) = Sparse.eval nodeValue3091 (mixedVector B) := by
    change mixedMoment B node3091 node3091Labels = _
    exact sound3091 B hB hF
  have h3097 : mixedVector B (Sum.inr 3097) = Sparse.eval nodeValue3097 (mixedVector B) := by
    change mixedMoment B node3097 node3097Labels = _
    exact sound3097 B hB hF
  have h3100 : mixedVector B (Sum.inr 3100) = Sparse.eval nodeValue3100 (mixedVector B) := by
    change mixedMoment B node3100 node3100Labels = _
    exact sound3100_e B hB hF
  have h3109 : mixedVector B (Sum.inr 3109) = Sparse.eval nodeValue3109 (mixedVector B) := by
    change mixedMoment B node3109 node3109Labels = _
    exact sound3109_e B hB hF
  have h3120 : mixedVector B (Sum.inr 3120) = Sparse.eval nodeValue3120 (mixedVector B) := by
    change mixedMoment B node3120 node3120Labels = _
    exact sound3120 B hB hF
  have h3199 : mixedVector B (Sum.inr 3199) = Sparse.eval nodeValue3199 (mixedVector B) := by
    change mixedMoment B node3199 node3199Labels = _
    exact sound3199 B hB hF
  have h3204 : mixedVector B (Sum.inr 3204) = Sparse.eval nodeValue3204 (mixedVector B) := by
    change mixedMoment B node3204 node3204Labels = _
    exact sound3204_e B hB hF
  have h3227 : mixedVector B (Sum.inr 3227) = Sparse.eval nodeValue3227 (mixedVector B) := by
    change mixedMoment B node3227 node3227Labels = _
    exact sound3227_e B hB hF
  simpa only [sourceForm693, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2471, h2472, h2484, h2718, h2721, h2728, h2754, h2764, h3034, h3037, h3041, h3084, h3087, h3091, h3097, h3100, h3109, h3120, h3199, h3204, h3227, reducedSource601] using sourceEq693 B hB

theorem rowSound601 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row601 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck601, numericCheck601, reducedZero601 B hB hF, mul_zero]

theorem reducedZero602 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource602 (mixedVector B) = 0 := by
  have h3503 : mixedVector B (Sum.inr 3503) = Sparse.eval nodeValue3503 (mixedVector B) := by
    change mixedMoment B node3503 node3503Labels = _
    exact sound3503 B hB hF
  have h3505 : mixedVector B (Sum.inr 3505) = Sparse.eval nodeValue3505 (mixedVector B) := by
    change mixedMoment B node3505 node3505Labels = _
    exact sound3505 B hB hF
  have h3525 : mixedVector B (Sum.inr 3525) = Sparse.eval nodeValue3525 (mixedVector B) := by
    change mixedMoment B node3525 node3525Labels = _
    exact sound3525 B hB hF
  have h3532 : mixedVector B (Sum.inr 3532) = Sparse.eval nodeValue3532 (mixedVector B) := by
    change mixedMoment B node3532 node3532Labels = _
    exact sound3532 B hB hF
  have h3581 : mixedVector B (Sum.inr 3581) = Sparse.eval nodeValue3581 (mixedVector B) := by
    change mixedMoment B node3581 node3581Labels = _
    exact sound3581 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm694, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3503, h3505, h3525, h3532, h3581, h4083, reducedSource602] using sourceEq694 B hB

theorem rowSound602 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row602 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck602, numericCheck602, reducedZero602 B hB hF, mul_zero]

theorem reducedZero603 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource603 (mixedVector B) = 0 := by
  have h2980 : mixedVector B (Sum.inr 2980) = Sparse.eval nodeValue2980 (mixedVector B) := by
    change mixedMoment B node2980 node2980Labels = _
    exact sound2980 B hB hF
  have h3373 : mixedVector B (Sum.inr 3373) = Sparse.eval nodeValue3373 (mixedVector B) := by
    change mixedMoment B node3373 node3373Labels = _
    exact sound3373 B hB hF
  have h3376 : mixedVector B (Sum.inr 3376) = Sparse.eval nodeValue3376 (mixedVector B) := by
    change mixedMoment B node3376 node3376Labels = _
    exact sound3376 B hB hF
  have h3505 : mixedVector B (Sum.inr 3505) = Sparse.eval nodeValue3505 (mixedVector B) := by
    change mixedMoment B node3505 node3505Labels = _
    exact sound3505 B hB hF
  have h3525 : mixedVector B (Sum.inr 3525) = Sparse.eval nodeValue3525 (mixedVector B) := by
    change mixedMoment B node3525 node3525Labels = _
    exact sound3525 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm695, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2980, h3373, h3376, h3505, h3525, h4083, reducedSource603] using sourceEq695 B hB

theorem rowSound603 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row603 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck603, numericCheck603, reducedZero603 B hB hF, mul_zero]

theorem reducedZero604 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource604 (mixedVector B) = 0 := by
  have h2012 : mixedVector B (Sum.inr 2012) = Sparse.eval nodeValue2012 (mixedVector B) := by
    change mixedMoment B node2012 node2012Labels = _
    exact sound2012 B hB hF
  have h3373 : mixedVector B (Sum.inr 3373) = Sparse.eval nodeValue3373 (mixedVector B) := by
    change mixedMoment B node3373 node3373Labels = _
    exact sound3373 B hB hF
  have h3500 : mixedVector B (Sum.inr 3500) = Sparse.eval nodeValue3500 (mixedVector B) := by
    change mixedMoment B node3500 node3500Labels = _
    exact sound3500 B hB hF
  have h3525 : mixedVector B (Sum.inr 3525) = Sparse.eval nodeValue3525 (mixedVector B) := by
    change mixedMoment B node3525 node3525Labels = _
    exact sound3525 B hB hF
  have h3526 : mixedVector B (Sum.inr 3526) = Sparse.eval nodeValue3526 (mixedVector B) := by
    change mixedMoment B node3526 node3526Labels = _
    exact sound3526 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm696, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2012, h3373, h3500, h3525, h3526, h4083, reducedSource604] using sourceEq696 B hB

theorem rowSound604 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row604 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck604, numericCheck604, reducedZero604 B hB hF, mul_zero]

theorem reducedZero605 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource605 (mixedVector B) = 0 := by
  have h2020 : mixedVector B (Sum.inr 2020) = Sparse.eval nodeValue2020 (mixedVector B) := by
    change mixedMoment B node2020 node2020Labels = _
    exact sound2020 B hB hF
  have h3376 : mixedVector B (Sum.inr 3376) = Sparse.eval nodeValue3376 (mixedVector B) := by
    change mixedMoment B node3376 node3376Labels = _
    exact sound3376 B hB hF
  have h3503 : mixedVector B (Sum.inr 3503) = Sparse.eval nodeValue3503 (mixedVector B) := by
    change mixedMoment B node3503 node3503Labels = _
    exact sound3503 B hB hF
  have h3525 : mixedVector B (Sum.inr 3525) = Sparse.eval nodeValue3525 (mixedVector B) := by
    change mixedMoment B node3525 node3525Labels = _
    exact sound3525 B hB hF
  have h3532 : mixedVector B (Sum.inr 3532) = Sparse.eval nodeValue3532 (mixedVector B) := by
    change mixedMoment B node3532 node3532Labels = _
    exact sound3532 B hB hF
  have h3534 : mixedVector B (Sum.inr 3534) = Sparse.eval nodeValue3534 (mixedVector B) := by
    change mixedMoment B node3534 node3534Labels = _
    exact sound3534 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm697, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2020, h3376, h3503, h3525, h3532, h3534, h4083, reducedSource605] using sourceEq697 B hB

theorem rowSound605 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row605 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck605, numericCheck605, reducedZero605 B hB hF, mul_zero]

theorem reducedZero606 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource606 (mixedVector B) = 0 := by
  have h2983 : mixedVector B (Sum.inr 2983) = Sparse.eval nodeValue2983 (mixedVector B) := by
    change mixedMoment B node2983 node2983Labels = _
    exact sound2983 B hB hF
  have h3500 : mixedVector B (Sum.inr 3500) = Sparse.eval nodeValue3500 (mixedVector B) := by
    change mixedMoment B node3500 node3500Labels = _
    exact sound3500 B hB hF
  have h3503 : mixedVector B (Sum.inr 3503) = Sparse.eval nodeValue3503 (mixedVector B) := by
    change mixedMoment B node3503 node3503Labels = _
    exact sound3503 B hB hF
  have h3525 : mixedVector B (Sum.inr 3525) = Sparse.eval nodeValue3525 (mixedVector B) := by
    change mixedMoment B node3525 node3525Labels = _
    exact sound3525 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm698, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2983, h3500, h3503, h3525, h3572, h4083, reducedSource606] using sourceEq698 B hB

theorem rowSound606 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row606 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck606, numericCheck606, reducedZero606 B hB hF, mul_zero]

theorem sourceRowsAt592 : MixedData.sourceRows (592 : Fin 2425) =
    MixedData.row592 := by decide +kernel

theorem sourceRowsAt593 : MixedData.sourceRows (593 : Fin 2425) =
    MixedData.row593 := by decide +kernel

theorem sourceRowsAt594 : MixedData.sourceRows (594 : Fin 2425) =
    MixedData.row594 := by decide +kernel

theorem sourceRowsAt595 : MixedData.sourceRows (595 : Fin 2425) =
    MixedData.row595 := by decide +kernel

theorem sourceRowsAt596 : MixedData.sourceRows (596 : Fin 2425) =
    MixedData.row596 := by decide +kernel

theorem sourceRowsAt597 : MixedData.sourceRows (597 : Fin 2425) =
    MixedData.row597 := by decide +kernel

theorem sourceRowsAt598 : MixedData.sourceRows (598 : Fin 2425) =
    MixedData.row598 := by decide +kernel

theorem sourceRowsAt599 : MixedData.sourceRows (599 : Fin 2425) =
    MixedData.row599 := by decide +kernel

theorem sourceRowsAt600 : MixedData.sourceRows (600 : Fin 2425) =
    MixedData.row600 := by decide +kernel

theorem sourceRowsAt601 : MixedData.sourceRows (601 : Fin 2425) =
    MixedData.row601 := by decide +kernel

theorem sourceRowsAt602 : MixedData.sourceRows (602 : Fin 2425) =
    MixedData.row602 := by decide +kernel

theorem sourceRowsAt603 : MixedData.sourceRows (603 : Fin 2425) =
    MixedData.row603 := by decide +kernel

theorem sourceRowsAt604 : MixedData.sourceRows (604 : Fin 2425) =
    MixedData.row604 := by decide +kernel

theorem sourceRowsAt605 : MixedData.sourceRows (605 : Fin 2425) =
    MixedData.row605 := by decide +kernel

theorem sourceRowsAt606 : MixedData.sourceRows (606 : Fin 2425) =
    MixedData.row606 := by decide +kernel

theorem sourceRowsAt607 : MixedData.sourceRows (607 : Fin 2425) =
    MixedData.row607 := by decide +kernel

theorem chunkSound37_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 37) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 592 ∨ k.val = 593 ∨ k.val = 594 ∨ k.val = 595 ∨ k.val = 596 ∨ k.val = 597 ∨ k.val = 598 ∨ k.val = 599 ∨ k.val = 600 ∨ k.val = 601 ∨ k.val = 602 ∨ k.val = 603 ∨ k.val = 604 ∨ k.val = 605 ∨ k.val = 606 ∨ k.val = 607 := by omega
  rcases heq with h592 | h593 | h594 | h595 | h596 | h597 | h598 | h599 | h600 | h601 | h602 | h603 | h604 | h605 | h606 | h607
  · have he : k = (592 : Fin 2425) := Fin.ext h592
    subst k
    rw [sourceRowsAt592]
    exact rowSound592_e B hB hF
  · have he : k = (593 : Fin 2425) := Fin.ext h593
    subst k
    rw [sourceRowsAt593]
    exact rowSound593 B hB hF
  · have he : k = (594 : Fin 2425) := Fin.ext h594
    subst k
    rw [sourceRowsAt594]
    exact rowSound594 B hB hF
  · have he : k = (595 : Fin 2425) := Fin.ext h595
    subst k
    rw [sourceRowsAt595]
    exact rowSound595 B hB hF
  · have he : k = (596 : Fin 2425) := Fin.ext h596
    subst k
    rw [sourceRowsAt596]
    exact rowSound596 B hB hF
  · have he : k = (597 : Fin 2425) := Fin.ext h597
    subst k
    rw [sourceRowsAt597]
    exact rowSound597 B hB hF
  · have he : k = (598 : Fin 2425) := Fin.ext h598
    subst k
    rw [sourceRowsAt598]
    exact rowSound598 B hB hF
  · have he : k = (599 : Fin 2425) := Fin.ext h599
    subst k
    rw [sourceRowsAt599]
    exact rowSound599_e B hB hF
  · have he : k = (600 : Fin 2425) := Fin.ext h600
    subst k
    rw [sourceRowsAt600]
    exact rowSound600_e B hB hF
  · have he : k = (601 : Fin 2425) := Fin.ext h601
    subst k
    rw [sourceRowsAt601]
    exact rowSound601 B hB hF
  · have he : k = (602 : Fin 2425) := Fin.ext h602
    subst k
    rw [sourceRowsAt602]
    exact rowSound602 B hB hF
  · have he : k = (603 : Fin 2425) := Fin.ext h603
    subst k
    rw [sourceRowsAt603]
    exact rowSound603 B hB hF
  · have he : k = (604 : Fin 2425) := Fin.ext h604
    subst k
    rw [sourceRowsAt604]
    exact rowSound604 B hB hF
  · have he : k = (605 : Fin 2425) := Fin.ext h605
    subst k
    rw [sourceRowsAt605]
    exact rowSound605 B hB hF
  · have he : k = (606 : Fin 2425) := Fin.ext h606
    subst k
    rw [sourceRowsAt606]
    exact rowSound606 B hB hF
  · have he : k = (607 : Fin 2425) := Fin.ext h607
    subst k
    rw [sourceRowsAt607]
    exact rowSound607_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound37_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound37_e_oai
