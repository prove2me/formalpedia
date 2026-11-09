-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound45_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:18:39.575292+00:00
-- url     : https://prove2.me/submissions/98e8fcdd-4538-40ae-9235-507b3c7cc466

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound2766_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3087_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3100_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3851_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5292_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5433_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound720_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound722_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound726_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound727_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound730_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound731_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound732_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound733_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound734_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound735_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem canonical13618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13618 raw13618Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw13618 raw13618Labels = mixedMoment B raw13618step0 raw13618step0Labels := by
      have ha : raw13618step0 = (fun i j => raw13618 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13618step0 raw13618; decide +kernel
      have hl : raw13618step0Labels = raw13618Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13618 raw13618Labels permutation152 permutation7
    mixedMoment B raw13618step0 raw13618step0Labels = mixedMoment B raw13618step1 raw13618step1Labels := by
      have ha : raw13618step1 = raw13618step0 := by apply Matrix.ext; unfold raw13618step1 raw13618step0; decide +kernel
      have hl : raw13618step0Labels = labelEmbedding10 ∘ raw13618step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13618step0 raw13618step0Labels raw13618step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5256 node5256Labels := by rfl

theorem canonical13623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13623 raw13623Labels = mixedMoment B node5263 node5263Labels := by
  calc
    mixedMoment B raw13623 raw13623Labels = mixedMoment B raw13623step0 raw13623step0Labels := by
      have ha : raw13623step0 = (fun i j => raw13623 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13623step0 raw13623; decide +kernel
      have hl : raw13623step0Labels = raw13623Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13623 raw13623Labels permutation180 permutation6
    mixedMoment B raw13623step0 raw13623step0Labels = mixedMoment B raw13623step1 raw13623step1Labels := by
      have ha : raw13623step1 = raw13623step0 := by apply Matrix.ext; unfold raw13623step1 raw13623step0; decide +kernel
      have hl : raw13623step0Labels = labelEmbedding9 ∘ raw13623step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13623step0 raw13623step0Labels raw13623step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5263 node5263Labels := by rfl

theorem canonical13632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13632 raw13632Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw13632 raw13632Labels = mixedMoment B raw13632step0 raw13632step0Labels := by
      have ha : raw13632step0 = (fun i j => raw13632 (permutation181 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13632step0 raw13632; decide +kernel
      have hl : raw13632step0Labels = raw13632Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13632 raw13632Labels permutation181 permutation6
    mixedMoment B raw13632step0 raw13632step0Labels = mixedMoment B raw13632step1 raw13632step1Labels := by
      have ha : raw13632step1 = raw13632step0 := by apply Matrix.ext; unfold raw13632step1 raw13632step0; decide +kernel
      have hl : raw13632step0Labels = labelEmbedding9 ∘ raw13632step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13632step0 raw13632step0Labels raw13632step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

theorem canonical13637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13637 raw13637Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw13637 raw13637Labels = mixedMoment B raw13637step0 raw13637step0Labels := by
      have ha : raw13637step0 = (fun i j => raw13637 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13637step0 raw13637; decide +kernel
      have hl : raw13637step0Labels = raw13637Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13637 raw13637Labels permutation180 permutation6
    mixedMoment B raw13637step0 raw13637step0Labels = mixedMoment B raw13637step1 raw13637step1Labels := by
      have ha : raw13637step1 = raw13637step0 := by apply Matrix.ext; unfold raw13637step1 raw13637step0; decide +kernel
      have hl : raw13637step0Labels = labelEmbedding9 ∘ raw13637step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13637step0 raw13637step0Labels raw13637step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

theorem canonical13640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13640 raw13640Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw13640 raw13640Labels = mixedMoment B raw13640step0 raw13640step0Labels := by
      have hz : ∀ j, raw13640 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13640step0 = (fun i j => raw13640 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13640step0 raw13640; decide +kernel
      have hl : raw13640step0Labels = raw13640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13640 raw13640Labels permutation346 hz
    mixedMoment B raw13640step0 raw13640step0Labels = mixedMoment B raw13640step1 raw13640step1Labels := by
      have ha : raw13640step1 = (fun i j => raw13640step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13640step1 raw13640step0; decide +kernel
      have hl : raw13640step1Labels = raw13640step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13640step0 raw13640step0Labels permutation50 permutation4
    mixedMoment B raw13640step1 raw13640step1Labels = mixedMoment B raw13640step2 raw13640step2Labels := by
      have ha : raw13640step2 = -raw13640step1 := by apply Matrix.ext; change ∀ i j, raw13640step2 i j = -(raw13640step1 i j); unfold raw13640step2 raw13640step1; decide +kernel
      have hl : raw13640step2Labels = raw13640step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13640step2 raw13640step2Labels = mixedMoment B raw13640step3 raw13640step3Labels := by
      have ha : raw13640step3 = raw13640step2 := by apply Matrix.ext; unfold raw13640step3 raw13640step2; decide +kernel
      have hl : raw13640step2Labels = labelEmbedding7 ∘ raw13640step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13640step2 raw13640step2Labels raw13640step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4893 node4893Labels := by rfl

theorem canonical13641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13641 raw13641Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw13641 raw13641Labels = mixedMoment B raw13641step0 raw13641step0Labels := by
      have hz : ∀ j, raw13641 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13641step0 = (fun i j => raw13641 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13641step0 raw13641; decide +kernel
      have hl : raw13641step0Labels = raw13641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13641 raw13641Labels permutation346 hz
    mixedMoment B raw13641step0 raw13641step0Labels = mixedMoment B raw13641step1 raw13641step1Labels := by
      have hz : ∀ j, raw13641step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13641step1 = (fun i j => raw13641step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13641step1 raw13641step0; decide +kernel
      have hl : raw13641step1Labels = raw13641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13641step0 raw13641step0Labels permutation56 hz
    mixedMoment B raw13641step1 raw13641step1Labels = mixedMoment B raw13641step2 raw13641step2Labels := by
      have ha : raw13641step2 = (fun i j => raw13641step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13641step2 raw13641step1; decide +kernel
      have hl : raw13641step2Labels = raw13641step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13641step1 raw13641step1Labels permutation12 permutation6
    mixedMoment B raw13641step2 raw13641step2Labels = mixedMoment B raw13641step3 raw13641step3Labels := by
      have ha : raw13641step3 = raw13641step2 := by apply Matrix.ext; unfold raw13641step3 raw13641step2; decide +kernel
      have hl : raw13641step2Labels = labelEmbedding9 ∘ raw13641step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13641step2 raw13641step2Labels raw13641step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5307 node5307Labels := by rfl

theorem canonical13644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13644 raw13644Labels = mixedMoment B node3085 node3085Labels := by
  calc
    mixedMoment B raw13644 raw13644Labels = mixedMoment B raw13644step0 raw13644step0Labels := by
      have ha : raw13644step0 = (fun i j => raw13644 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13644step0 raw13644; decide +kernel
      have hl : raw13644step0Labels = raw13644Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13644 raw13644Labels permutation180 permutation6
    _ = mixedMoment B node3085 node3085Labels := by rfl

theorem canonical13649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13649 raw13649Labels = mixedMoment B node2728 node2728Labels := by
  calc
    mixedMoment B raw13649 raw13649Labels = mixedMoment B raw13649step0 raw13649step0Labels := by
      have ha : raw13649step0 = (fun i j => raw13649 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13649step0 raw13649; decide +kernel
      have hl : raw13649step0Labels = raw13649Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13649 raw13649Labels permutation180 permutation6
    _ = mixedMoment B node2728 node2728Labels := by rfl

theorem canonical13660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13660 raw13660Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw13660 raw13660Labels = mixedMoment B raw13660step0 raw13660step0Labels := by
      have ha : raw13660step0 = (fun i j => raw13660 (permutation181 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13660step0 raw13660; decide +kernel
      have hl : raw13660step0Labels = raw13660Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13660 raw13660Labels permutation181 permutation6
    _ = mixedMoment B node2718 node2718Labels := by rfl

theorem canonical13665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13665 raw13665Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw13665 raw13665Labels = mixedMoment B raw13665step0 raw13665step0Labels := by
      have ha : raw13665step0 = (fun i j => raw13665 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13665step0 raw13665; decide +kernel
      have hl : raw13665step0Labels = raw13665Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13665 raw13665Labels permutation180 permutation6
    _ = mixedMoment B node2718 node2718Labels := by rfl

theorem canonical13668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13668 raw13668Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw13668 raw13668Labels = mixedMoment B raw13668step0 raw13668step0Labels := by
      have hz : ∀ j, raw13668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13668step0 = (fun i j => raw13668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13668step0 raw13668; decide +kernel
      have hl : raw13668step0Labels = raw13668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13668 raw13668Labels permutation346 hz
    mixedMoment B raw13668step0 raw13668step0Labels = mixedMoment B raw13668step1 raw13668step1Labels := by
      have ha : raw13668step1 = (fun i j => raw13668step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13668step1 raw13668step0; decide +kernel
      have hl : raw13668step1Labels = raw13668step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13668step0 raw13668step0Labels permutation36 permutation6
    _ = mixedMoment B node2263 node2263Labels := by rfl

theorem canonical13669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13669 raw13669Labels = mixedMoment B node2785 node2785Labels := by
  calc
    mixedMoment B raw13669 raw13669Labels = mixedMoment B raw13669step0 raw13669step0Labels := by
      have hz : ∀ j, raw13669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13669step0 = (fun i j => raw13669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13669step0 raw13669; decide +kernel
      have hl : raw13669step0Labels = raw13669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13669 raw13669Labels permutation346 hz
    mixedMoment B raw13669step0 raw13669step0Labels = mixedMoment B raw13669step1 raw13669step1Labels := by
      have hz : ∀ j, raw13669step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13669step1 = (fun i j => raw13669step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13669step1 raw13669step0; decide +kernel
      have hl : raw13669step1Labels = raw13669step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13669step0 raw13669step0Labels permutation56 hz
    mixedMoment B raw13669step1 raw13669step1Labels = mixedMoment B raw13669step2 raw13669step2Labels := by
      have ha : raw13669step2 = (fun i j => raw13669step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13669step2 raw13669step1; decide +kernel
      have hl : raw13669step2Labels = raw13669step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13669step1 raw13669step1Labels permutation12 permutation6
    _ = mixedMoment B node2785 node2785Labels := by rfl

theorem canonical13671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13671 raw13671Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw13671 raw13671Labels = mixedMoment B raw13671step0 raw13671step0Labels := by
      have hz : ∀ j, raw13671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13671step0 = (fun i j => raw13671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13671step0 raw13671; decide +kernel
      have hl : raw13671step0Labels = raw13671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13671 raw13671Labels permutation346 hz
    mixedMoment B raw13671step0 raw13671step0Labels = mixedMoment B raw13671step1 raw13671step1Labels := by
      have ha : raw13671step1 = (fun i j => raw13671step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13671step1 raw13671step0; decide +kernel
      have hl : raw13671step1Labels = raw13671step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13671step0 raw13671step0Labels permutation33 permutation6
    _ = mixedMoment B node2766 node2766Labels := by rfl

theorem canonical13672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13672 raw13672Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw13672 raw13672Labels = mixedMoment B raw13672step0 raw13672step0Labels := by
      have hz : ∀ j, raw13672 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13672step0 = (fun i j => raw13672 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13672step0 raw13672; decide +kernel
      have hl : raw13672step0Labels = raw13672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13672 raw13672Labels permutation346 hz
    mixedMoment B raw13672step0 raw13672step0Labels = mixedMoment B raw13672step1 raw13672step1Labels := by
      have ha : raw13672step1 = (fun i j => raw13672step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13672step1 raw13672step0; decide +kernel
      have hl : raw13672step1Labels = raw13672step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13672step0 raw13672step0Labels permutation35 permutation6
    _ = mixedMoment B node2766 node2766Labels := by rfl

theorem canonical13673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13673 raw13673Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw13673 raw13673Labels = mixedMoment B raw13673step0 raw13673step0Labels := by
      have ha : raw13673step0 = (fun i j => raw13673 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13673step0 raw13673; decide +kernel
      have hl : raw13673step0Labels = raw13673Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13673 raw13673Labels permutation194 permutation7
    mixedMoment B raw13673step0 raw13673step0Labels = mixedMoment B raw13673step1 raw13673step1Labels := by
      have ha : raw13673step1 = -raw13673step0 := by apply Matrix.ext; change ∀ i j, raw13673step1 i j = -(raw13673step0 i j); unfold raw13673step1 raw13673step0; decide +kernel
      have hl : raw13673step1Labels = raw13673step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13673step1 raw13673step1Labels = mixedMoment B raw13673step2 raw13673step2Labels := by
      have ha : raw13673step2 = raw13673step1 := by apply Matrix.ext; unfold raw13673step2 raw13673step1; decide +kernel
      have hl : raw13673step1Labels = labelEmbedding10 ∘ raw13673step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13673step1 raw13673step1Labels raw13673step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical13674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13674 raw13674Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw13674 raw13674Labels = mixedMoment B raw13674step0 raw13674step0Labels := by
      have ha : raw13674step0 = (fun i j => raw13674 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13674step0 raw13674; decide +kernel
      have hl : raw13674step0Labels = raw13674Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13674 raw13674Labels permutation180 permutation2
    _ = mixedMoment B node5408 node5408Labels := by rfl

theorem canonical13675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13675 raw13675Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw13675 raw13675Labels = mixedMoment B raw13675step0 raw13675step0Labels := by
      have ha : raw13675step0 = (fun i j => raw13675 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13675step0 raw13675; decide +kernel
      have hl : raw13675step0Labels = raw13675Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13675 raw13675Labels permutation194 permutation7
    mixedMoment B raw13675step0 raw13675step0Labels = mixedMoment B raw13675step1 raw13675step1Labels := by
      have ha : raw13675step1 = -raw13675step0 := by apply Matrix.ext; change ∀ i j, raw13675step1 i j = -(raw13675step0 i j); unfold raw13675step1 raw13675step0; decide +kernel
      have hl : raw13675step1Labels = raw13675step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13675step1 raw13675step1Labels = mixedMoment B raw13675step2 raw13675step2Labels := by
      have ha : raw13675step2 = raw13675step1 := by apply Matrix.ext; unfold raw13675step2 raw13675step1; decide +kernel
      have hl : raw13675step1Labels = labelEmbedding10 ∘ raw13675step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13675step1 raw13675step1Labels raw13675step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical13676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13676 raw13676Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw13676 raw13676Labels = mixedMoment B raw13676step0 raw13676step0Labels := by
      have ha : raw13676step0 = (fun i j => raw13676 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13676step0 raw13676; decide +kernel
      have hl : raw13676step0Labels = raw13676Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13676 raw13676Labels permutation195 permutation7
    mixedMoment B raw13676step0 raw13676step0Labels = mixedMoment B raw13676step1 raw13676step1Labels := by
      have ha : raw13676step1 = -raw13676step0 := by apply Matrix.ext; change ∀ i j, raw13676step1 i j = -(raw13676step0 i j); unfold raw13676step1 raw13676step0; decide +kernel
      have hl : raw13676step1Labels = raw13676step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13676step1 raw13676step1Labels = mixedMoment B raw13676step2 raw13676step2Labels := by
      have ha : raw13676step2 = raw13676step1 := by apply Matrix.ext; unfold raw13676step2 raw13676step1; decide +kernel
      have hl : raw13676step1Labels = labelEmbedding10 ∘ raw13676step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13676step1 raw13676step1Labels raw13676step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical13677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13677 raw13677Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw13677 raw13677Labels = mixedMoment B raw13677step0 raw13677step0Labels := by
      have hz : ∀ j, raw13677 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13677step0 = (fun i j => raw13677 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13677step0 raw13677; decide +kernel
      have hl : raw13677step0Labels = raw13677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13677 raw13677Labels permutation590 hz
    mixedMoment B raw13677step0 raw13677step0Labels = mixedMoment B raw13677step1 raw13677step1Labels := by
      have ha : raw13677step1 = (fun i j => raw13677step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13677step1 raw13677step0; decide +kernel
      have hl : raw13677step1Labels = raw13677step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13677step0 raw13677step0Labels permutation38 permutation7
    mixedMoment B raw13677step1 raw13677step1Labels = mixedMoment B raw13677step2 raw13677step2Labels := by
      have ha : raw13677step2 = -raw13677step1 := by apply Matrix.ext; change ∀ i j, raw13677step2 i j = -(raw13677step1 i j); unfold raw13677step2 raw13677step1; decide +kernel
      have hl : raw13677step2Labels = raw13677step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13677step2 raw13677step2Labels = mixedMoment B raw13677step3 raw13677step3Labels := by
      have ha : raw13677step3 = raw13677step2 := by apply Matrix.ext; unfold raw13677step3 raw13677step2; decide +kernel
      have hl : raw13677step2Labels = labelEmbedding10 ∘ raw13677step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13677step2 raw13677step2Labels raw13677step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

theorem canonical13678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13678 raw13678Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw13678 raw13678Labels = mixedMoment B raw13678step0 raw13678step0Labels := by
      have ha : raw13678step0 = (fun i j => raw13678 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13678step0 raw13678; decide +kernel
      have hl : raw13678step0Labels = raw13678Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13678 raw13678Labels permutation194 permutation2
    _ = mixedMoment B node4601 node4601Labels := by rfl

theorem canonical13679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13679 raw13679Labels = mixedMoment B node5100 node5100Labels := by
  calc
    mixedMoment B raw13679 raw13679Labels = mixedMoment B raw13679step0 raw13679step0Labels := by
      have ha : raw13679step0 = (fun i j => raw13679 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13679step0 raw13679; decide +kernel
      have hl : raw13679step0Labels = raw13679Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13679 raw13679Labels permutation194 permutation2
    _ = mixedMoment B node5100 node5100Labels := by rfl

theorem canonical13680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13680 raw13680Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw13680 raw13680Labels = mixedMoment B raw13680step0 raw13680step0Labels := by
      have ha : raw13680step0 = (fun i j => raw13680 (permutation186 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13680step0 raw13680; decide +kernel
      have hl : raw13680step0Labels = raw13680Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13680 raw13680Labels permutation186 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical13681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13681 raw13681Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw13681 raw13681Labels = mixedMoment B raw13681step0 raw13681step0Labels := by
      have ha : raw13681step0 = (fun i j => raw13681 (permutation192 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13681step0 raw13681; decide +kernel
      have hl : raw13681step0Labels = raw13681Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13681 raw13681Labels permutation192 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical13682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13682 raw13682Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw13682 raw13682Labels = mixedMoment B raw13682step0 raw13682step0Labels := by
      have hz : ∀ j, raw13682 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13682step0 = (fun i j => raw13682 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13682step0 raw13682; decide +kernel
      have hl : raw13682step0Labels = raw13682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13682 raw13682Labels permutation590 hz
    mixedMoment B raw13682step0 raw13682step0Labels = mixedMoment B raw13682step1 raw13682step1Labels := by
      have ha : raw13682step1 = (fun i j => raw13682step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13682step1 raw13682step0; decide +kernel
      have hl : raw13682step1Labels = raw13682step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13682step0 raw13682step0Labels permutation38 permutation2
    _ = mixedMoment B node5273 node5273Labels := by rfl

theorem canonical13683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13683 raw13683Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw13683 raw13683Labels = mixedMoment B raw13683step0 raw13683step0Labels := by
      have ha : raw13683step0 = (fun i j => raw13683 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13683step0 raw13683; decide +kernel
      have hl : raw13683step0Labels = raw13683Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13683 raw13683Labels permutation161 permutation3
    mixedMoment B raw13683step0 raw13683step0Labels = mixedMoment B raw13683step1 raw13683step1Labels := by
      have ha : raw13683step1 = raw13683step0 := by apply Matrix.ext; unfold raw13683step1 raw13683step0; decide +kernel
      have hl : raw13683step0Labels = labelEmbedding6 ∘ raw13683step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13683step0 raw13683step0Labels raw13683step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

theorem canonical13684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13684 raw13684Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw13684 raw13684Labels = mixedMoment B raw13684step0 raw13684step0Labels := by
      have ha : raw13684step0 = (fun i j => raw13684 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13684step0 raw13684; decide +kernel
      have hl : raw13684step0Labels = raw13684Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13684 raw13684Labels permutation156 permutation2
    _ = mixedMoment B node5197 node5197Labels := by rfl

theorem canonical13685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13685 raw13685Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw13685 raw13685Labels = mixedMoment B raw13685step0 raw13685step0Labels := by
      have ha : raw13685step0 = (fun i j => raw13685 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13685step0 raw13685; decide +kernel
      have hl : raw13685step0Labels = raw13685Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13685 raw13685Labels permutation159 permutation2
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical13686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13686 raw13686Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw13686 raw13686Labels = mixedMoment B raw13686step0 raw13686step0Labels := by
      have ha : raw13686step0 = (fun i j => raw13686 (permutation165 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13686step0 raw13686; decide +kernel
      have hl : raw13686step0Labels = raw13686Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13686 raw13686Labels permutation165 permutation2
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical13687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13687 raw13687Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw13687 raw13687Labels = mixedMoment B raw13687step0 raw13687step0Labels := by
      have hz : ∀ j, raw13687 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13687step0 = (fun i j => raw13687 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13687step0 raw13687; decide +kernel
      have hl : raw13687step0Labels = raw13687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13687 raw13687Labels permutation590 hz
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical13688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13688 raw13688Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw13688 raw13688Labels = mixedMoment B raw13688step0 raw13688step0Labels := by
      have ha : raw13688step0 = (fun i j => raw13688 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13688step0 raw13688; decide +kernel
      have hl : raw13688step0Labels = raw13688Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13688 raw13688Labels permutation181 permutation2
    _ = mixedMoment B node4590 node4590Labels := by rfl

theorem canonical13689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13689 raw13689Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw13689 raw13689Labels = mixedMoment B raw13689step0 raw13689step0Labels := by
      have ha : raw13689step0 = (fun i j => raw13689 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13689step0 raw13689; decide +kernel
      have hl : raw13689step0Labels = raw13689Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13689 raw13689Labels permutation157 permutation2
    _ = mixedMoment B node5185 node5185Labels := by rfl

theorem canonical13690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13690 raw13690Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw13690 raw13690Labels = mixedMoment B raw13690step0 raw13690step0Labels := by
      have ha : raw13690step0 = (fun i j => raw13690 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13690step0 raw13690; decide +kernel
      have hl : raw13690step0Labels = raw13690Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13690 raw13690Labels permutation181 permutation2
    _ = mixedMoment B node5073 node5073Labels := by rfl

theorem canonical13691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13691 raw13691Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw13691 raw13691Labels = mixedMoment B raw13691step0 raw13691step0Labels := by
      have ha : raw13691step0 = (fun i j => raw13691 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13691step0 raw13691; decide +kernel
      have hl : raw13691step0Labels = raw13691Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13691 raw13691Labels permutation179 permutation2
    _ = mixedMoment B node5250 node5250Labels := by rfl

theorem canonical13692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13692 raw13692Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw13692 raw13692Labels = mixedMoment B raw13692step0 raw13692step0Labels := by
      have hz : ∀ j, raw13692 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13692step0 = (fun i j => raw13692 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13692step0 raw13692; decide +kernel
      have hl : raw13692step0Labels = raw13692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13692 raw13692Labels permutation590 hz
    mixedMoment B raw13692step0 raw13692step0Labels = mixedMoment B raw13692step1 raw13692step1Labels := by
      have ha : raw13692step1 = (fun i j => raw13692step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13692step1 raw13692step0; decide +kernel
      have hl : raw13692step1Labels = raw13692step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13692step0 raw13692step0Labels permutation39 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical13693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13693 raw13693Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw13693 raw13693Labels = mixedMoment B raw13693step0 raw13693step0Labels := by
      have ha : raw13693step0 = (fun i j => raw13693 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13693step0 raw13693; decide +kernel
      have hl : raw13693step0Labels = raw13693Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13693 raw13693Labels permutation180 permutation2
    _ = mixedMoment B node4590 node4590Labels := by rfl

theorem canonical13694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13694 raw13694Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw13694 raw13694Labels = mixedMoment B raw13694step0 raw13694step0Labels := by
      have ha : raw13694step0 = (fun i j => raw13694 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13694step0 raw13694; decide +kernel
      have hl : raw13694step0Labels = raw13694Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13694 raw13694Labels permutation156 permutation2
    _ = mixedMoment B node5185 node5185Labels := by rfl

theorem canonical13695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13695 raw13695Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw13695 raw13695Labels = mixedMoment B raw13695step0 raw13695step0Labels := by
      have ha : raw13695step0 = (fun i j => raw13695 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13695step0 raw13695; decide +kernel
      have hl : raw13695step0Labels = raw13695Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13695 raw13695Labels permutation180 permutation2
    _ = mixedMoment B node5073 node5073Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13696 raw13696Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw13696 raw13696Labels = mixedMoment B raw13696step0 raw13696step0Labels := by
      have ha : raw13696step0 = (fun i j => raw13696 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13696step0 raw13696; decide +kernel
      have hl : raw13696step0Labels = raw13696Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13696 raw13696Labels permutation177 permutation2
    _ = mixedMoment B node5250 node5250Labels := by rfl

theorem canonical13697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13697 raw13697Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw13697 raw13697Labels = mixedMoment B raw13697step0 raw13697step0Labels := by
      have hz : ∀ j, raw13697 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13697step0 = (fun i j => raw13697 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13697step0 raw13697; decide +kernel
      have hl : raw13697step0Labels = raw13697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13697 raw13697Labels permutation590 hz
    mixedMoment B raw13697step0 raw13697step0Labels = mixedMoment B raw13697step1 raw13697step1Labels := by
      have ha : raw13697step1 = (fun i j => raw13697step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13697step1 raw13697step0; decide +kernel
      have hl : raw13697step1Labels = raw13697step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13697step0 raw13697step0Labels permutation38 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical13698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13698 raw13698Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw13698 raw13698Labels = mixedMoment B raw13698step0 raw13698step0Labels := by
      have ha : raw13698step0 = (fun i j => raw13698 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13698step0 raw13698; decide +kernel
      have hl : raw13698step0Labels = raw13698Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13698 raw13698Labels permutation152 permutation3
    mixedMoment B raw13698step0 raw13698step0Labels = mixedMoment B raw13698step1 raw13698step1Labels := by
      have ha : raw13698step1 = raw13698step0 := by apply Matrix.ext; unfold raw13698step1 raw13698step0; decide +kernel
      have hl : raw13698step0Labels = labelEmbedding6 ∘ raw13698step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13698step0 raw13698step0Labels raw13698step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4589 node4589Labels := by rfl

theorem canonical13699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13699 raw13699Labels = mixedMoment B node5187 node5187Labels := by
  calc
    _ = mixedMoment B node5187 node5187Labels := by rfl

theorem canonical13700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13700 raw13700Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw13700 raw13700Labels = mixedMoment B raw13700step0 raw13700step0Labels := by
      have ha : raw13700step0 = (fun i j => raw13700 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13700step0 raw13700; decide +kernel
      have hl : raw13700step0Labels = raw13700Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13700 raw13700Labels permutation176 permutation2
    _ = mixedMoment B node5076 node5076Labels := by rfl

theorem canonical13701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13701 raw13701Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw13701 raw13701Labels = mixedMoment B raw13701step0 raw13701step0Labels := by
      have ha : raw13701step0 = (fun i j => raw13701 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13701step0 raw13701; decide +kernel
      have hl : raw13701step0Labels = raw13701Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13701 raw13701Labels permutation176 permutation2
    _ = mixedMoment B node5251 node5251Labels := by rfl

theorem canonical13702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13702 raw13702Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw13702 raw13702Labels = mixedMoment B raw13702step0 raw13702step0Labels := by
      have ha : raw13702step0 = (fun i j => raw13702 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13702step0 raw13702; decide +kernel
      have hl : raw13702step0Labels = raw13702Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13702 raw13702Labels permutation178 permutation2
    _ = mixedMoment B node5251 node5251Labels := by rfl

theorem canonical13733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13733 raw13733Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw13733 raw13733Labels = mixedMoment B raw13733step0 raw13733step0Labels := by
      have ha : raw13733step0 = (fun i j => raw13733 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13733step0 raw13733; decide +kernel
      have hl : raw13733step0Labels = raw13733Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13733 raw13733Labels permutation194 permutation7
    mixedMoment B raw13733step0 raw13733step0Labels = mixedMoment B raw13733step1 raw13733step1Labels := by
      have ha : raw13733step1 = -raw13733step0 := by apply Matrix.ext; change ∀ i j, raw13733step1 i j = -(raw13733step0 i j); unfold raw13733step1 raw13733step0; decide +kernel
      have hl : raw13733step1Labels = raw13733step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13733step1 raw13733step1Labels = mixedMoment B raw13733step2 raw13733step2Labels := by
      have ha : raw13733step2 = raw13733step1 := by apply Matrix.ext; unfold raw13733step2 raw13733step1; decide +kernel
      have hl : raw13733step1Labels = labelEmbedding1 ∘ raw13733step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13733step1 raw13733step1Labels raw13733step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3849 node3849Labels := by rfl

theorem canonical13734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13734 raw13734Labels = mixedMoment B node3806 node3806Labels := by
  calc
    mixedMoment B raw13734 raw13734Labels = mixedMoment B raw13734step0 raw13734step0Labels := by
      have ha : raw13734step0 = (fun i j => raw13734 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13734step0 raw13734; decide +kernel
      have hl : raw13734step0Labels = raw13734Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13734 raw13734Labels permutation194 permutation7
    mixedMoment B raw13734step0 raw13734step0Labels = mixedMoment B raw13734step1 raw13734step1Labels := by
      have ha : raw13734step1 = -raw13734step0 := by apply Matrix.ext; change ∀ i j, raw13734step1 i j = -(raw13734step0 i j); unfold raw13734step1 raw13734step0; decide +kernel
      have hl : raw13734step1Labels = raw13734step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13734step1 raw13734step1Labels = mixedMoment B raw13734step2 raw13734step2Labels := by
      have ha : raw13734step2 = raw13734step1 := by apply Matrix.ext; unfold raw13734step2 raw13734step1; decide +kernel
      have hl : raw13734step1Labels = labelEmbedding1 ∘ raw13734step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13734step1 raw13734step1Labels raw13734step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3806 node3806Labels := by rfl

theorem canonical13735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13735 raw13735Labels = mixedMoment B node3851 node3851Labels := by
  calc
    mixedMoment B raw13735 raw13735Labels = mixedMoment B raw13735step0 raw13735step0Labels := by
      have ha : raw13735step0 = (fun i j => raw13735 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13735step0 raw13735; decide +kernel
      have hl : raw13735step0Labels = raw13735Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13735 raw13735Labels permutation194 permutation7
    mixedMoment B raw13735step0 raw13735step0Labels = mixedMoment B raw13735step1 raw13735step1Labels := by
      have ha : raw13735step1 = -raw13735step0 := by apply Matrix.ext; change ∀ i j, raw13735step1 i j = -(raw13735step0 i j); unfold raw13735step1 raw13735step0; decide +kernel
      have hl : raw13735step1Labels = raw13735step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13735step1 raw13735step1Labels = mixedMoment B raw13735step2 raw13735step2Labels := by
      have ha : raw13735step2 = raw13735step1 := by apply Matrix.ext; unfold raw13735step2 raw13735step1; decide +kernel
      have hl : raw13735step1Labels = labelEmbedding1 ∘ raw13735step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13735step1 raw13735step1Labels raw13735step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3851 node3851Labels := by rfl

theorem canonical13736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13736 raw13736Labels = mixedMoment B node3851 node3851Labels := by
  calc
    mixedMoment B raw13736 raw13736Labels = mixedMoment B raw13736step0 raw13736step0Labels := by
      have ha : raw13736step0 = (fun i j => raw13736 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13736step0 raw13736; decide +kernel
      have hl : raw13736step0Labels = raw13736Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13736 raw13736Labels permutation195 permutation7
    mixedMoment B raw13736step0 raw13736step0Labels = mixedMoment B raw13736step1 raw13736step1Labels := by
      have ha : raw13736step1 = -raw13736step0 := by apply Matrix.ext; change ∀ i j, raw13736step1 i j = -(raw13736step0 i j); unfold raw13736step1 raw13736step0; decide +kernel
      have hl : raw13736step1Labels = raw13736step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13736step1 raw13736step1Labels = mixedMoment B raw13736step2 raw13736step2Labels := by
      have ha : raw13736step2 = raw13736step1 := by apply Matrix.ext; unfold raw13736step2 raw13736step1; decide +kernel
      have hl : raw13736step1Labels = labelEmbedding1 ∘ raw13736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13736step1 raw13736step1Labels raw13736step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3851 node3851Labels := by rfl

theorem canonical13737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13737 raw13737Labels = mixedMoment B node3859 node3859Labels := by
  calc
    mixedMoment B raw13737 raw13737Labels = mixedMoment B raw13737step0 raw13737step0Labels := by
      have hz : ∀ j, raw13737 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13737step0 = (fun i j => raw13737 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13737step0 raw13737; decide +kernel
      have hl : raw13737step0Labels = raw13737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13737 raw13737Labels permutation590 hz
    mixedMoment B raw13737step0 raw13737step0Labels = mixedMoment B raw13737step1 raw13737step1Labels := by
      have ha : raw13737step1 = (fun i j => raw13737step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13737step1 raw13737step0; decide +kernel
      have hl : raw13737step1Labels = raw13737step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13737step0 raw13737step0Labels permutation38 permutation7
    mixedMoment B raw13737step1 raw13737step1Labels = mixedMoment B raw13737step2 raw13737step2Labels := by
      have ha : raw13737step2 = -raw13737step1 := by apply Matrix.ext; change ∀ i j, raw13737step2 i j = -(raw13737step1 i j); unfold raw13737step2 raw13737step1; decide +kernel
      have hl : raw13737step2Labels = raw13737step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13737step2 raw13737step2Labels = mixedMoment B raw13737step3 raw13737step3Labels := by
      have ha : raw13737step3 = raw13737step2 := by apply Matrix.ext; unfold raw13737step3 raw13737step2; decide +kernel
      have hl : raw13737step2Labels = labelEmbedding1 ∘ raw13737step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13737step2 raw13737step2Labels raw13737step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3859 node3859Labels := by rfl

theorem canonical13738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13738 raw13738Labels = mixedMoment B node3292 node3292Labels := by
  calc
    mixedMoment B raw13738 raw13738Labels = mixedMoment B raw13738step0 raw13738step0Labels := by
      have ha : raw13738step0 = (fun i j => raw13738 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13738step0 raw13738; decide +kernel
      have hl : raw13738step0Labels = raw13738Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13738 raw13738Labels permutation194 permutation7
    mixedMoment B raw13738step0 raw13738step0Labels = mixedMoment B raw13738step1 raw13738step1Labels := by
      have ha : raw13738step1 = -raw13738step0 := by apply Matrix.ext; change ∀ i j, raw13738step1 i j = -(raw13738step0 i j); unfold raw13738step1 raw13738step0; decide +kernel
      have hl : raw13738step1Labels = raw13738step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13738step1 raw13738step1Labels = mixedMoment B raw13738step2 raw13738step2Labels := by
      have ha : raw13738step2 = raw13738step1 := by apply Matrix.ext; unfold raw13738step2 raw13738step1; decide +kernel
      have hl : raw13738step1Labels = labelEmbedding1 ∘ raw13738step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13738step1 raw13738step1Labels raw13738step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3292 node3292Labels := by rfl

theorem canonical13739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13739 raw13739Labels = mixedMoment B node3469 node3469Labels := by
  calc
    mixedMoment B raw13739 raw13739Labels = mixedMoment B raw13739step0 raw13739step0Labels := by
      have ha : raw13739step0 = (fun i j => raw13739 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13739step0 raw13739; decide +kernel
      have hl : raw13739step0Labels = raw13739Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13739 raw13739Labels permutation194 permutation7
    mixedMoment B raw13739step0 raw13739step0Labels = mixedMoment B raw13739step1 raw13739step1Labels := by
      have ha : raw13739step1 = -raw13739step0 := by apply Matrix.ext; change ∀ i j, raw13739step1 i j = -(raw13739step0 i j); unfold raw13739step1 raw13739step0; decide +kernel
      have hl : raw13739step1Labels = raw13739step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13739step1 raw13739step1Labels = mixedMoment B raw13739step2 raw13739step2Labels := by
      have ha : raw13739step2 = raw13739step1 := by apply Matrix.ext; unfold raw13739step2 raw13739step1; decide +kernel
      have hl : raw13739step1Labels = labelEmbedding1 ∘ raw13739step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13739step1 raw13739step1Labels raw13739step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3469 node3469Labels := by rfl

theorem canonical13740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13740 raw13740Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw13740 raw13740Labels = mixedMoment B raw13740step0 raw13740step0Labels := by
      have ha : raw13740step0 = (fun i j => raw13740 (permutation196 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13740step0 raw13740; decide +kernel
      have hl : raw13740step0Labels = raw13740Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13740 raw13740Labels permutation196 permutation7
    mixedMoment B raw13740step0 raw13740step0Labels = mixedMoment B raw13740step1 raw13740step1Labels := by
      have ha : raw13740step1 = -raw13740step0 := by apply Matrix.ext; change ∀ i j, raw13740step1 i j = -(raw13740step0 i j); unfold raw13740step1 raw13740step0; decide +kernel
      have hl : raw13740step1Labels = raw13740step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13740step1 raw13740step1Labels = mixedMoment B raw13740step2 raw13740step2Labels := by
      have ha : raw13740step2 = raw13740step1 := by apply Matrix.ext; unfold raw13740step2 raw13740step1; decide +kernel
      have hl : raw13740step1Labels = labelEmbedding1 ∘ raw13740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13740step1 raw13740step1Labels raw13740step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

theorem canonical13741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13741 raw13741Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw13741 raw13741Labels = mixedMoment B raw13741step0 raw13741step0Labels := by
      have ha : raw13741step0 = (fun i j => raw13741 (permutation198 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13741step0 raw13741; decide +kernel
      have hl : raw13741step0Labels = raw13741Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13741 raw13741Labels permutation198 permutation7
    mixedMoment B raw13741step0 raw13741step0Labels = mixedMoment B raw13741step1 raw13741step1Labels := by
      have ha : raw13741step1 = -raw13741step0 := by apply Matrix.ext; change ∀ i j, raw13741step1 i j = -(raw13741step0 i j); unfold raw13741step1 raw13741step0; decide +kernel
      have hl : raw13741step1Labels = raw13741step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13741step1 raw13741step1Labels = mixedMoment B raw13741step2 raw13741step2Labels := by
      have ha : raw13741step2 = raw13741step1 := by apply Matrix.ext; unfold raw13741step2 raw13741step1; decide +kernel
      have hl : raw13741step1Labels = labelEmbedding1 ∘ raw13741step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13741step1 raw13741step1Labels raw13741step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

theorem canonical13742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13742 raw13742Labels = mixedMoment B node3546 node3546Labels := by
  calc
    mixedMoment B raw13742 raw13742Labels = mixedMoment B raw13742step0 raw13742step0Labels := by
      have hz : ∀ j, raw13742 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13742step0 = (fun i j => raw13742 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13742step0 raw13742; decide +kernel
      have hl : raw13742step0Labels = raw13742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13742 raw13742Labels permutation590 hz
    mixedMoment B raw13742step0 raw13742step0Labels = mixedMoment B raw13742step1 raw13742step1Labels := by
      have ha : raw13742step1 = (fun i j => raw13742step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13742step1 raw13742step0; decide +kernel
      have hl : raw13742step1Labels = raw13742step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13742step0 raw13742step0Labels permutation38 permutation7
    mixedMoment B raw13742step1 raw13742step1Labels = mixedMoment B raw13742step2 raw13742step2Labels := by
      have ha : raw13742step2 = -raw13742step1 := by apply Matrix.ext; change ∀ i j, raw13742step2 i j = -(raw13742step1 i j); unfold raw13742step2 raw13742step1; decide +kernel
      have hl : raw13742step2Labels = raw13742step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13742step2 raw13742step2Labels = mixedMoment B raw13742step3 raw13742step3Labels := by
      have ha : raw13742step3 = raw13742step2 := by apply Matrix.ext; unfold raw13742step3 raw13742step2; decide +kernel
      have hl : raw13742step2Labels = labelEmbedding1 ∘ raw13742step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13742step2 raw13742step2Labels raw13742step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3546 node3546Labels := by rfl

theorem canonical13743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13743 raw13743Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw13743 raw13743Labels = mixedMoment B raw13743step0 raw13743step0Labels := by
      have ha : raw13743step0 = (fun i j => raw13743 (permutation161 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13743step0 raw13743; decide +kernel
      have hl : raw13743step0Labels = raw13743Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13743 raw13743Labels permutation161 permutation5
    mixedMoment B raw13743step0 raw13743step0Labels = mixedMoment B raw13743step1 raw13743step1Labels := by
      have ha : raw13743step1 = -raw13743step0 := by apply Matrix.ext; change ∀ i j, raw13743step1 i j = -(raw13743step0 i j); unfold raw13743step1 raw13743step0; decide +kernel
      have hl : raw13743step1Labels = raw13743step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13743step1 raw13743step1Labels = mixedMoment B raw13743step2 raw13743step2Labels := by
      have ha : raw13743step2 = raw13743step1 := by apply Matrix.ext; unfold raw13743step2 raw13743step1; decide +kernel
      have hl : raw13743step1Labels = labelEmbedding1 ∘ raw13743step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13743step1 raw13743step1Labels raw13743step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

theorem canonical13744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13744 raw13744Labels = mixedMoment B node3569 node3569Labels := by
  calc
    mixedMoment B raw13744 raw13744Labels = mixedMoment B raw13744step0 raw13744step0Labels := by
      have ha : raw13744step0 = (fun i j => raw13744 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13744step0 raw13744; decide +kernel
      have hl : raw13744step0Labels = raw13744Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13744 raw13744Labels permutation194 permutation7
    mixedMoment B raw13744step0 raw13744step0Labels = mixedMoment B raw13744step1 raw13744step1Labels := by
      have ha : raw13744step1 = -raw13744step0 := by apply Matrix.ext; change ∀ i j, raw13744step1 i j = -(raw13744step0 i j); unfold raw13744step1 raw13744step0; decide +kernel
      have hl : raw13744step1Labels = raw13744step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13744step1 raw13744step1Labels = mixedMoment B raw13744step2 raw13744step2Labels := by
      have ha : raw13744step2 = raw13744step1 := by apply Matrix.ext; unfold raw13744step2 raw13744step1; decide +kernel
      have hl : raw13744step1Labels = labelEmbedding1 ∘ raw13744step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13744step1 raw13744step1Labels raw13744step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3569 node3569Labels := by rfl

theorem canonical13745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13745 raw13745Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw13745 raw13745Labels = mixedMoment B raw13745step0 raw13745step0Labels := by
      have ha : raw13745step0 = (fun i j => raw13745 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13745step0 raw13745; decide +kernel
      have hl : raw13745step0Labels = raw13745Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13745 raw13745Labels permutation194 permutation7
    mixedMoment B raw13745step0 raw13745step0Labels = mixedMoment B raw13745step1 raw13745step1Labels := by
      have ha : raw13745step1 = -raw13745step0 := by apply Matrix.ext; change ∀ i j, raw13745step1 i j = -(raw13745step0 i j); unfold raw13745step1 raw13745step0; decide +kernel
      have hl : raw13745step1Labels = raw13745step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13745step1 raw13745step1Labels = mixedMoment B raw13745step2 raw13745step2Labels := by
      have ha : raw13745step2 = raw13745step1 := by apply Matrix.ext; unfold raw13745step2 raw13745step1; decide +kernel
      have hl : raw13745step1Labels = labelEmbedding1 ∘ raw13745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13745step1 raw13745step1Labels raw13745step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

theorem canonical13746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13746 raw13746Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw13746 raw13746Labels = mixedMoment B raw13746step0 raw13746step0Labels := by
      have ha : raw13746step0 = (fun i j => raw13746 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13746step0 raw13746; decide +kernel
      have hl : raw13746step0Labels = raw13746Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13746 raw13746Labels permutation195 permutation7
    mixedMoment B raw13746step0 raw13746step0Labels = mixedMoment B raw13746step1 raw13746step1Labels := by
      have ha : raw13746step1 = -raw13746step0 := by apply Matrix.ext; change ∀ i j, raw13746step1 i j = -(raw13746step0 i j); unfold raw13746step1 raw13746step0; decide +kernel
      have hl : raw13746step1Labels = raw13746step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13746step1 raw13746step1Labels = mixedMoment B raw13746step2 raw13746step2Labels := by
      have ha : raw13746step2 = raw13746step1 := by apply Matrix.ext; unfold raw13746step2 raw13746step1; decide +kernel
      have hl : raw13746step1Labels = labelEmbedding1 ∘ raw13746step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13746step1 raw13746step1Labels raw13746step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

theorem canonical13747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13747 raw13747Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw13747 raw13747Labels = mixedMoment B raw13747step0 raw13747step0Labels := by
      have hz : ∀ j, raw13747 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13747step0 = (fun i j => raw13747 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13747step0 raw13747; decide +kernel
      have hl : raw13747step0Labels = raw13747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13747 raw13747Labels permutation590 hz
    mixedMoment B raw13747step0 raw13747step0Labels = mixedMoment B raw13747step1 raw13747step1Labels := by
      have ha : raw13747step1 = (fun i j => raw13747step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13747step1 raw13747step0; decide +kernel
      have hl : raw13747step1Labels = raw13747step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13747step0 raw13747step0Labels permutation38 permutation7
    mixedMoment B raw13747step1 raw13747step1Labels = mixedMoment B raw13747step2 raw13747step2Labels := by
      have ha : raw13747step2 = -raw13747step1 := by apply Matrix.ext; change ∀ i j, raw13747step2 i j = -(raw13747step1 i j); unfold raw13747step2 raw13747step1; decide +kernel
      have hl : raw13747step2Labels = raw13747step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13747step2 raw13747step2Labels = mixedMoment B raw13747step3 raw13747step3Labels := by
      have ha : raw13747step3 = raw13747step2 := by apply Matrix.ext; unfold raw13747step3 raw13747step2; decide +kernel
      have hl : raw13747step2Labels = labelEmbedding1 ∘ raw13747step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13747step2 raw13747step2Labels raw13747step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

theorem canonical13748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13748 raw13748Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw13748 raw13748Labels = mixedMoment B raw13748step0 raw13748step0Labels := by
      have ha : raw13748step0 = (fun i j => raw13748 (permutation165 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13748step0 raw13748; decide +kernel
      have hl : raw13748step0Labels = raw13748Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13748 raw13748Labels permutation165 permutation5
    mixedMoment B raw13748step0 raw13748step0Labels = mixedMoment B raw13748step1 raw13748step1Labels := by
      have ha : raw13748step1 = -raw13748step0 := by apply Matrix.ext; change ∀ i j, raw13748step1 i j = -(raw13748step0 i j); unfold raw13748step1 raw13748step0; decide +kernel
      have hl : raw13748step1Labels = raw13748step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13748step1 raw13748step1Labels = mixedMoment B raw13748step2 raw13748step2Labels := by
      have ha : raw13748step2 = raw13748step1 := by apply Matrix.ext; unfold raw13748step2 raw13748step1; decide +kernel
      have hl : raw13748step1Labels = labelEmbedding1 ∘ raw13748step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13748step1 raw13748step1Labels raw13748step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

theorem canonical13749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13749 raw13749Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw13749 raw13749Labels = mixedMoment B raw13749step0 raw13749step0Labels := by
      have ha : raw13749step0 = (fun i j => raw13749 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13749step0 raw13749; decide +kernel
      have hl : raw13749step0Labels = raw13749Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13749 raw13749Labels permutation195 permutation7
    mixedMoment B raw13749step0 raw13749step0Labels = mixedMoment B raw13749step1 raw13749step1Labels := by
      have ha : raw13749step1 = -raw13749step0 := by apply Matrix.ext; change ∀ i j, raw13749step1 i j = -(raw13749step0 i j); unfold raw13749step1 raw13749step0; decide +kernel
      have hl : raw13749step1Labels = raw13749step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13749step1 raw13749step1Labels = mixedMoment B raw13749step2 raw13749step2Labels := by
      have ha : raw13749step2 = raw13749step1 := by apply Matrix.ext; unfold raw13749step2 raw13749step1; decide +kernel
      have hl : raw13749step1Labels = labelEmbedding1 ∘ raw13749step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13749step1 raw13749step1Labels raw13749step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

theorem canonical13750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13750 raw13750Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw13750 raw13750Labels = mixedMoment B raw13750step0 raw13750step0Labels := by
      have ha : raw13750step0 = (fun i j => raw13750 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13750step0 raw13750; decide +kernel
      have hl : raw13750step0Labels = raw13750Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13750 raw13750Labels permutation195 permutation7
    mixedMoment B raw13750step0 raw13750step0Labels = mixedMoment B raw13750step1 raw13750step1Labels := by
      have ha : raw13750step1 = -raw13750step0 := by apply Matrix.ext; change ∀ i j, raw13750step1 i j = -(raw13750step0 i j); unfold raw13750step1 raw13750step0; decide +kernel
      have hl : raw13750step1Labels = raw13750step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13750step1 raw13750step1Labels = mixedMoment B raw13750step2 raw13750step2Labels := by
      have ha : raw13750step2 = raw13750step1 := by apply Matrix.ext; unfold raw13750step2 raw13750step1; decide +kernel
      have hl : raw13750step1Labels = labelEmbedding1 ∘ raw13750step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13750step1 raw13750step1Labels raw13750step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

theorem canonical13751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13751 raw13751Labels = mixedMoment B node3531 node3531Labels := by
  calc
    mixedMoment B raw13751 raw13751Labels = mixedMoment B raw13751step0 raw13751step0Labels := by
      have ha : raw13751step0 = (fun i j => raw13751 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13751step0 raw13751; decide +kernel
      have hl : raw13751step0Labels = raw13751Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13751 raw13751Labels permutation195 permutation7
    mixedMoment B raw13751step0 raw13751step0Labels = mixedMoment B raw13751step1 raw13751step1Labels := by
      have ha : raw13751step1 = -raw13751step0 := by apply Matrix.ext; change ∀ i j, raw13751step1 i j = -(raw13751step0 i j); unfold raw13751step1 raw13751step0; decide +kernel
      have hl : raw13751step1Labels = raw13751step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13751step1 raw13751step1Labels = mixedMoment B raw13751step2 raw13751step2Labels := by
      have ha : raw13751step2 = raw13751step1 := by apply Matrix.ext; unfold raw13751step2 raw13751step1; decide +kernel
      have hl : raw13751step1Labels = labelEmbedding1 ∘ raw13751step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13751step1 raw13751step1Labels raw13751step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3531 node3531Labels := by rfl

theorem canonical13752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13752 raw13752Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw13752 raw13752Labels = mixedMoment B raw13752step0 raw13752step0Labels := by
      have hz : ∀ j, raw13752 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13752step0 = (fun i j => raw13752 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13752step0 raw13752; decide +kernel
      have hl : raw13752step0Labels = raw13752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13752 raw13752Labels permutation590 hz
    mixedMoment B raw13752step0 raw13752step0Labels = mixedMoment B raw13752step1 raw13752step1Labels := by
      have ha : raw13752step1 = (fun i j => raw13752step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13752step1 raw13752step0; decide +kernel
      have hl : raw13752step1Labels = raw13752step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13752step0 raw13752step0Labels permutation39 permutation7
    mixedMoment B raw13752step1 raw13752step1Labels = mixedMoment B raw13752step2 raw13752step2Labels := by
      have ha : raw13752step2 = -raw13752step1 := by apply Matrix.ext; change ∀ i j, raw13752step2 i j = -(raw13752step1 i j); unfold raw13752step2 raw13752step1; decide +kernel
      have hl : raw13752step2Labels = raw13752step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13752step2 raw13752step2Labels = mixedMoment B raw13752step3 raw13752step3Labels := by
      have ha : raw13752step3 = raw13752step2 := by apply Matrix.ext; unfold raw13752step3 raw13752step2; decide +kernel
      have hl : raw13752step2Labels = labelEmbedding1 ∘ raw13752step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13752step2 raw13752step2Labels raw13752step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical13753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13753 raw13753Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw13753 raw13753Labels = mixedMoment B raw13753step0 raw13753step0Labels := by
      have ha : raw13753step0 = (fun i j => raw13753 (permutation159 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13753step0 raw13753; decide +kernel
      have hl : raw13753step0Labels = raw13753Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13753 raw13753Labels permutation159 permutation5
    mixedMoment B raw13753step0 raw13753step0Labels = mixedMoment B raw13753step1 raw13753step1Labels := by
      have ha : raw13753step1 = -raw13753step0 := by apply Matrix.ext; change ∀ i j, raw13753step1 i j = -(raw13753step0 i j); unfold raw13753step1 raw13753step0; decide +kernel
      have hl : raw13753step1Labels = raw13753step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13753step1 raw13753step1Labels = mixedMoment B raw13753step2 raw13753step2Labels := by
      have ha : raw13753step2 = raw13753step1 := by apply Matrix.ext; unfold raw13753step2 raw13753step1; decide +kernel
      have hl : raw13753step1Labels = labelEmbedding1 ∘ raw13753step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13753step1 raw13753step1Labels raw13753step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

theorem canonical13754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13754 raw13754Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw13754 raw13754Labels = mixedMoment B raw13754step0 raw13754step0Labels := by
      have ha : raw13754step0 = (fun i j => raw13754 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13754step0 raw13754; decide +kernel
      have hl : raw13754step0Labels = raw13754Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13754 raw13754Labels permutation194 permutation7
    mixedMoment B raw13754step0 raw13754step0Labels = mixedMoment B raw13754step1 raw13754step1Labels := by
      have ha : raw13754step1 = -raw13754step0 := by apply Matrix.ext; change ∀ i j, raw13754step1 i j = -(raw13754step0 i j); unfold raw13754step1 raw13754step0; decide +kernel
      have hl : raw13754step1Labels = raw13754step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13754step1 raw13754step1Labels = mixedMoment B raw13754step2 raw13754step2Labels := by
      have ha : raw13754step2 = raw13754step1 := by apply Matrix.ext; unfold raw13754step2 raw13754step1; decide +kernel
      have hl : raw13754step1Labels = labelEmbedding1 ∘ raw13754step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13754step1 raw13754step1Labels raw13754step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

theorem canonical13755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13755 raw13755Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw13755 raw13755Labels = mixedMoment B raw13755step0 raw13755step0Labels := by
      have ha : raw13755step0 = (fun i j => raw13755 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13755step0 raw13755; decide +kernel
      have hl : raw13755step0Labels = raw13755Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13755 raw13755Labels permutation194 permutation7
    mixedMoment B raw13755step0 raw13755step0Labels = mixedMoment B raw13755step1 raw13755step1Labels := by
      have ha : raw13755step1 = -raw13755step0 := by apply Matrix.ext; change ∀ i j, raw13755step1 i j = -(raw13755step0 i j); unfold raw13755step1 raw13755step0; decide +kernel
      have hl : raw13755step1Labels = raw13755step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13755step1 raw13755step1Labels = mixedMoment B raw13755step2 raw13755step2Labels := by
      have ha : raw13755step2 = raw13755step1 := by apply Matrix.ext; unfold raw13755step2 raw13755step1; decide +kernel
      have hl : raw13755step1Labels = labelEmbedding1 ∘ raw13755step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13755step1 raw13755step1Labels raw13755step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

theorem canonical13756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13756 raw13756Labels = mixedMoment B node3531 node3531Labels := by
  calc
    mixedMoment B raw13756 raw13756Labels = mixedMoment B raw13756step0 raw13756step0Labels := by
      have ha : raw13756step0 = (fun i j => raw13756 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13756step0 raw13756; decide +kernel
      have hl : raw13756step0Labels = raw13756Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13756 raw13756Labels permutation194 permutation7
    mixedMoment B raw13756step0 raw13756step0Labels = mixedMoment B raw13756step1 raw13756step1Labels := by
      have ha : raw13756step1 = -raw13756step0 := by apply Matrix.ext; change ∀ i j, raw13756step1 i j = -(raw13756step0 i j); unfold raw13756step1 raw13756step0; decide +kernel
      have hl : raw13756step1Labels = raw13756step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13756step1 raw13756step1Labels = mixedMoment B raw13756step2 raw13756step2Labels := by
      have ha : raw13756step2 = raw13756step1 := by apply Matrix.ext; unfold raw13756step2 raw13756step1; decide +kernel
      have hl : raw13756step1Labels = labelEmbedding1 ∘ raw13756step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13756step1 raw13756step1Labels raw13756step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3531 node3531Labels := by rfl

theorem canonical13757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13757 raw13757Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw13757 raw13757Labels = mixedMoment B raw13757step0 raw13757step0Labels := by
      have hz : ∀ j, raw13757 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13757step0 = (fun i j => raw13757 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13757step0 raw13757; decide +kernel
      have hl : raw13757step0Labels = raw13757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13757 raw13757Labels permutation590 hz
    mixedMoment B raw13757step0 raw13757step0Labels = mixedMoment B raw13757step1 raw13757step1Labels := by
      have ha : raw13757step1 = (fun i j => raw13757step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13757step1 raw13757step0; decide +kernel
      have hl : raw13757step1Labels = raw13757step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13757step0 raw13757step0Labels permutation38 permutation7
    mixedMoment B raw13757step1 raw13757step1Labels = mixedMoment B raw13757step2 raw13757step2Labels := by
      have ha : raw13757step2 = -raw13757step1 := by apply Matrix.ext; change ∀ i j, raw13757step2 i j = -(raw13757step1 i j); unfold raw13757step2 raw13757step1; decide +kernel
      have hl : raw13757step2Labels = raw13757step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13757step2 raw13757step2Labels = mixedMoment B raw13757step3 raw13757step3Labels := by
      have ha : raw13757step3 = raw13757step2 := by apply Matrix.ext; unfold raw13757step3 raw13757step2; decide +kernel
      have hl : raw13757step2Labels = labelEmbedding1 ∘ raw13757step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13757step2 raw13757step2Labels raw13757step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical13758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13758 raw13758Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw13758 raw13758Labels = mixedMoment B raw13758step0 raw13758step0Labels := by
      have ha : raw13758step0 = (fun i j => raw13758 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13758step0 raw13758; decide +kernel
      have hl : raw13758step0Labels = raw13758Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13758 raw13758Labels permutation160 permutation5
    mixedMoment B raw13758step0 raw13758step0Labels = mixedMoment B raw13758step1 raw13758step1Labels := by
      have ha : raw13758step1 = -raw13758step0 := by apply Matrix.ext; change ∀ i j, raw13758step1 i j = -(raw13758step0 i j); unfold raw13758step1 raw13758step0; decide +kernel
      have hl : raw13758step1Labels = raw13758step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13758step1 raw13758step1Labels = mixedMoment B raw13758step2 raw13758step2Labels := by
      have ha : raw13758step2 = raw13758step1 := by apply Matrix.ext; unfold raw13758step2 raw13758step1; decide +kernel
      have hl : raw13758step1Labels = labelEmbedding1 ∘ raw13758step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13758step1 raw13758step1Labels raw13758step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

theorem canonical13759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13759 raw13759Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw13759 raw13759Labels = mixedMoment B raw13759step0 raw13759step0Labels := by
      have ha : raw13759step0 = (fun i j => raw13759 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13759step0 raw13759; decide +kernel
      have hl : raw13759step0Labels = raw13759Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13759 raw13759Labels permutation194 permutation7
    mixedMoment B raw13759step0 raw13759step0Labels = mixedMoment B raw13759step1 raw13759step1Labels := by
      have ha : raw13759step1 = -raw13759step0 := by apply Matrix.ext; change ∀ i j, raw13759step1 i j = -(raw13759step0 i j); unfold raw13759step1 raw13759step0; decide +kernel
      have hl : raw13759step1Labels = raw13759step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13759step1 raw13759step1Labels = mixedMoment B raw13759step2 raw13759step2Labels := by
      have ha : raw13759step2 = raw13759step1 := by apply Matrix.ext; unfold raw13759step2 raw13759step1; decide +kernel
      have hl : raw13759step1Labels = labelEmbedding1 ∘ raw13759step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13759step1 raw13759step1Labels raw13759step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3537 node3537Labels := by rfl

theorem canonical13760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13760 raw13760Labels = mixedMoment B node3477 node3477Labels := by
  calc
    mixedMoment B raw13760 raw13760Labels = mixedMoment B raw13760step0 raw13760step0Labels := by
      have ha : raw13760step0 = (fun i j => raw13760 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13760step0 raw13760; decide +kernel
      have hl : raw13760step0Labels = raw13760Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13760 raw13760Labels permutation194 permutation7
    mixedMoment B raw13760step0 raw13760step0Labels = mixedMoment B raw13760step1 raw13760step1Labels := by
      have ha : raw13760step1 = -raw13760step0 := by apply Matrix.ext; change ∀ i j, raw13760step1 i j = -(raw13760step0 i j); unfold raw13760step1 raw13760step0; decide +kernel
      have hl : raw13760step1Labels = raw13760step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13760step1 raw13760step1Labels = mixedMoment B raw13760step2 raw13760step2Labels := by
      have ha : raw13760step2 = raw13760step1 := by apply Matrix.ext; unfold raw13760step2 raw13760step1; decide +kernel
      have hl : raw13760step1Labels = labelEmbedding1 ∘ raw13760step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13760step1 raw13760step1Labels raw13760step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3477 node3477Labels := by rfl

theorem canonical13761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13761 raw13761Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw13761 raw13761Labels = mixedMoment B raw13761step0 raw13761step0Labels := by
      have ha : raw13761step0 = (fun i j => raw13761 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13761step0 raw13761; decide +kernel
      have hl : raw13761step0Labels = raw13761Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13761 raw13761Labels permutation194 permutation7
    mixedMoment B raw13761step0 raw13761step0Labels = mixedMoment B raw13761step1 raw13761step1Labels := by
      have ha : raw13761step1 = -raw13761step0 := by apply Matrix.ext; change ∀ i j, raw13761step1 i j = -(raw13761step0 i j); unfold raw13761step1 raw13761step0; decide +kernel
      have hl : raw13761step1Labels = raw13761step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13761step1 raw13761step1Labels = mixedMoment B raw13761step2 raw13761step2Labels := by
      have ha : raw13761step2 = raw13761step1 := by apply Matrix.ext; unfold raw13761step2 raw13761step1; decide +kernel
      have hl : raw13761step1Labels = labelEmbedding1 ∘ raw13761step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13761step1 raw13761step1Labels raw13761step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

theorem canonical13762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13762 raw13762Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw13762 raw13762Labels = mixedMoment B raw13762step0 raw13762step0Labels := by
      have ha : raw13762step0 = (fun i j => raw13762 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13762step0 raw13762; decide +kernel
      have hl : raw13762step0Labels = raw13762Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13762 raw13762Labels permutation195 permutation7
    mixedMoment B raw13762step0 raw13762step0Labels = mixedMoment B raw13762step1 raw13762step1Labels := by
      have ha : raw13762step1 = -raw13762step0 := by apply Matrix.ext; change ∀ i j, raw13762step1 i j = -(raw13762step0 i j); unfold raw13762step1 raw13762step0; decide +kernel
      have hl : raw13762step1Labels = raw13762step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13762step1 raw13762step1Labels = mixedMoment B raw13762step2 raw13762step2Labels := by
      have ha : raw13762step2 = raw13762step1 := by apply Matrix.ext; unfold raw13762step2 raw13762step1; decide +kernel
      have hl : raw13762step1Labels = labelEmbedding1 ∘ raw13762step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13762step1 raw13762step1Labels raw13762step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

theorem canonical13763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13763 raw13763Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw13763 raw13763Labels = mixedMoment B raw13763step0 raw13763step0Labels := by
      have ha : raw13763step0 = (fun i j => raw13763 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13763step0 raw13763; decide +kernel
      have hl : raw13763step0Labels = raw13763Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13763 raw13763Labels permutation194 permutation2
    _ = mixedMoment B node1235 node1235Labels := by rfl

theorem canonical13764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13764 raw13764Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw13764 raw13764Labels = mixedMoment B raw13764step0 raw13764step0Labels := by
      have ha : raw13764step0 = (fun i j => raw13764 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13764step0 raw13764; decide +kernel
      have hl : raw13764step0Labels = raw13764Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13764 raw13764Labels permutation180 permutation2
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical13765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13765 raw13765Labels = mixedMoment B node2510 node2510Labels := by
  calc
    mixedMoment B raw13765 raw13765Labels = mixedMoment B raw13765step0 raw13765step0Labels := by
      have ha : raw13765step0 = (fun i j => raw13765 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13765step0 raw13765; decide +kernel
      have hl : raw13765step0Labels = raw13765Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13765 raw13765Labels permutation194 permutation2
    _ = mixedMoment B node2510 node2510Labels := by rfl

theorem canonical13766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13766 raw13766Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw13766 raw13766Labels = mixedMoment B raw13766step0 raw13766step0Labels := by
      have ha : raw13766step0 = (fun i j => raw13766 (permutation186 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13766step0 raw13766; decide +kernel
      have hl : raw13766step0Labels = raw13766Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13766 raw13766Labels permutation186 permutation2
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical13767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13767 raw13767Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw13767 raw13767Labels = mixedMoment B raw13767step0 raw13767step0Labels := by
      have ha : raw13767step0 = (fun i j => raw13767 (permutation192 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13767step0 raw13767; decide +kernel
      have hl : raw13767step0Labels = raw13767Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13767 raw13767Labels permutation192 permutation2
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical13768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13768 raw13768Labels = mixedMoment B node2741 node2741Labels := by
  calc
    mixedMoment B raw13768 raw13768Labels = mixedMoment B raw13768step0 raw13768step0Labels := by
      have hz : ∀ j, raw13768 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13768step0 = (fun i j => raw13768 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13768step0 raw13768; decide +kernel
      have hl : raw13768step0Labels = raw13768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13768 raw13768Labels permutation590 hz
    mixedMoment B raw13768step0 raw13768step0Labels = mixedMoment B raw13768step1 raw13768step1Labels := by
      have ha : raw13768step1 = (fun i j => raw13768step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13768step1 raw13768step0; decide +kernel
      have hl : raw13768step1Labels = raw13768step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13768step0 raw13768step0Labels permutation38 permutation2
    _ = mixedMoment B node2741 node2741Labels := by rfl

theorem canonical13769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13769 raw13769Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw13769 raw13769Labels = mixedMoment B raw13769step0 raw13769step0Labels := by
      have hz : ∀ j, raw13769 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13769step0 = (fun i j => raw13769 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13769step0 raw13769; decide +kernel
      have hl : raw13769step0Labels = raw13769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13769 raw13769Labels permutation590 hz
    mixedMoment B raw13769step0 raw13769step0Labels = mixedMoment B raw13769step1 raw13769step1Labels := by
      have ha : raw13769step1 = (fun i j => raw13769step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw13769step1 raw13769step0; decide +kernel
      have hl : raw13769step1Labels = raw13769step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13769step0 raw13769step0Labels permutation38 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical13770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13770 raw13770Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw13770 raw13770Labels = mixedMoment B raw13770step0 raw13770step0Labels := by
      have ha : raw13770step0 = (fun i j => raw13770 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13770step0 raw13770; decide +kernel
      have hl : raw13770step0Labels = raw13770Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13770 raw13770Labels permutation156 permutation2
    _ = mixedMoment B node3875 node3875Labels := by rfl

theorem canonical13771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13771 raw13771Labels = mixedMoment B node2631 node2631Labels := by
  calc
    mixedMoment B raw13771 raw13771Labels = mixedMoment B raw13771step0 raw13771step0Labels := by
      have ha : raw13771step0 = (fun i j => raw13771 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13771step0 raw13771; decide +kernel
      have hl : raw13771step0Labels = raw13771Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13771 raw13771Labels permutation156 permutation2
    _ = mixedMoment B node2631 node2631Labels := by rfl

theorem canonical13772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13772 raw13772Labels = mixedMoment B node2615 node2615Labels := by
  calc
    mixedMoment B raw13772 raw13772Labels = mixedMoment B raw13772step0 raw13772step0Labels := by
      have ha : raw13772step0 = (fun i j => raw13772 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13772step0 raw13772; decide +kernel
      have hl : raw13772step0Labels = raw13772Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13772 raw13772Labels permutation157 permutation2
    _ = mixedMoment B node2615 node2615Labels := by rfl

theorem canonical13773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13773 raw13773Labels = mixedMoment B node2615 node2615Labels := by
  calc
    mixedMoment B raw13773 raw13773Labels = mixedMoment B raw13773step0 raw13773step0Labels := by
      have ha : raw13773step0 = (fun i j => raw13773 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13773step0 raw13773; decide +kernel
      have hl : raw13773step0Labels = raw13773Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13773 raw13773Labels permutation156 permutation2
    _ = mixedMoment B node2615 node2615Labels := by rfl

theorem canonical13774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13774 raw13774Labels = mixedMoment B node2617 node2617Labels := by
  calc
    _ = mixedMoment B node2617 node2617Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13835 raw13835Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw13835 raw13835Labels = mixedMoment B raw13835step0 raw13835step0Labels := by
      have hz : ∀ j, raw13835 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13835step0 = (fun i j => raw13835 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13835step0 raw13835; decide +kernel
      have hl : raw13835step0Labels = raw13835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13835 raw13835Labels permutation265 hz
    mixedMoment B raw13835step0 raw13835step0Labels = mixedMoment B raw13835step1 raw13835step1Labels := by
      have ha : raw13835step1 = (fun i j => raw13835step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13835step1 raw13835step0; decide +kernel
      have hl : raw13835step1Labels = raw13835step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13835step0 raw13835step0Labels permutation32 permutation7
    mixedMoment B raw13835step1 raw13835step1Labels = mixedMoment B raw13835step2 raw13835step2Labels := by
      have ha : raw13835step2 = raw13835step1 := by apply Matrix.ext; unfold raw13835step2 raw13835step1; decide +kernel
      have hl : raw13835step1Labels = labelEmbedding10 ∘ raw13835step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13835step1 raw13835step1Labels raw13835step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical13836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13836 raw13836Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw13836 raw13836Labels = mixedMoment B raw13836step0 raw13836step0Labels := by
      have ha : raw13836step0 = (fun i j => raw13836 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13836step0 raw13836; decide +kernel
      have hl : raw13836step0Labels = raw13836Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13836 raw13836Labels permutation152 permutation7
    mixedMoment B raw13836step0 raw13836step0Labels = mixedMoment B raw13836step1 raw13836step1Labels := by
      have ha : raw13836step1 = raw13836step0 := by apply Matrix.ext; unfold raw13836step1 raw13836step0; decide +kernel
      have hl : raw13836step0Labels = labelEmbedding10 ∘ raw13836step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13836step0 raw13836step0Labels raw13836step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical13837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13837 raw13837Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw13837 raw13837Labels = mixedMoment B raw13837step0 raw13837step0Labels := by
      have ha : raw13837step0 = (fun i j => raw13837 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13837step0 raw13837; decide +kernel
      have hl : raw13837step0Labels = raw13837Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13837 raw13837Labels permutation154 permutation7
    mixedMoment B raw13837step0 raw13837step0Labels = mixedMoment B raw13837step1 raw13837step1Labels := by
      have ha : raw13837step1 = raw13837step0 := by apply Matrix.ext; unfold raw13837step1 raw13837step0; decide +kernel
      have hl : raw13837step0Labels = labelEmbedding10 ∘ raw13837step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13837step0 raw13837step0Labels raw13837step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical13838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13838 raw13838Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw13838 raw13838Labels = mixedMoment B raw13838step0 raw13838step0Labels := by
      have ha : raw13838step0 = (fun i j => raw13838 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13838step0 raw13838; decide +kernel
      have hl : raw13838step0Labels = raw13838Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13838 raw13838Labels permutation152 permutation7
    mixedMoment B raw13838step0 raw13838step0Labels = mixedMoment B raw13838step1 raw13838step1Labels := by
      have ha : raw13838step1 = raw13838step0 := by apply Matrix.ext; unfold raw13838step1 raw13838step0; decide +kernel
      have hl : raw13838step0Labels = labelEmbedding10 ∘ raw13838step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13838step0 raw13838step0Labels raw13838step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical13839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13839 raw13839Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw13839 raw13839Labels = mixedMoment B raw13839step0 raw13839step0Labels := by
      have ha : raw13839step0 = (fun i j => raw13839 (permutation197 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13839step0 raw13839; decide +kernel
      have hl : raw13839step0Labels = raw13839Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13839 raw13839Labels permutation197 permutation4
    mixedMoment B raw13839step0 raw13839step0Labels = mixedMoment B raw13839step1 raw13839step1Labels := by
      have ha : raw13839step1 = -raw13839step0 := by apply Matrix.ext; change ∀ i j, raw13839step1 i j = -(raw13839step0 i j); unfold raw13839step1 raw13839step0; decide +kernel
      have hl : raw13839step1Labels = raw13839step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13839step1 raw13839step1Labels = mixedMoment B raw13839step2 raw13839step2Labels := by
      have ha : raw13839step2 = raw13839step1 := by apply Matrix.ext; unfold raw13839step2 raw13839step1; decide +kernel
      have hl : raw13839step1Labels = labelEmbedding7 ∘ raw13839step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13839step1 raw13839step1Labels raw13839step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical13840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13840 raw13840Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw13840 raw13840Labels = mixedMoment B raw13840step0 raw13840step0Labels := by
      have ha : raw13840step0 = (fun i j => raw13840 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13840step0 raw13840; decide +kernel
      have hl : raw13840step0Labels = raw13840Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13840 raw13840Labels permutation180 permutation6
    mixedMoment B raw13840step0 raw13840step0Labels = mixedMoment B raw13840step1 raw13840step1Labels := by
      have ha : raw13840step1 = raw13840step0 := by apply Matrix.ext; unfold raw13840step1 raw13840step0; decide +kernel
      have hl : raw13840step0Labels = labelEmbedding9 ∘ raw13840step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13840step0 raw13840step0Labels raw13840step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

theorem canonical13841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13841 raw13841Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw13841 raw13841Labels = mixedMoment B raw13841step0 raw13841step0Labels := by
      have ha : raw13841step0 = (fun i j => raw13841 (permutation177 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13841step0 raw13841; decide +kernel
      have hl : raw13841step0Labels = raw13841Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13841 raw13841Labels permutation177 permutation6
    mixedMoment B raw13841step0 raw13841step0Labels = mixedMoment B raw13841step1 raw13841step1Labels := by
      have ha : raw13841step1 = raw13841step0 := by apply Matrix.ext; unfold raw13841step1 raw13841step0; decide +kernel
      have hl : raw13841step0Labels = labelEmbedding9 ∘ raw13841step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13841step0 raw13841step0Labels raw13841step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical13842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13842 raw13842Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw13842 raw13842Labels = mixedMoment B raw13842step0 raw13842step0Labels := by
      have ha : raw13842step0 = (fun i j => raw13842 (permutation179 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13842step0 raw13842; decide +kernel
      have hl : raw13842step0Labels = raw13842Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13842 raw13842Labels permutation179 permutation6
    mixedMoment B raw13842step0 raw13842step0Labels = mixedMoment B raw13842step1 raw13842step1Labels := by
      have ha : raw13842step1 = raw13842step0 := by apply Matrix.ext; unfold raw13842step1 raw13842step0; decide +kernel
      have hl : raw13842step0Labels = labelEmbedding9 ∘ raw13842step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13842step0 raw13842step0Labels raw13842step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical13843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13843 raw13843Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw13843 raw13843Labels = mixedMoment B raw13843step0 raw13843step0Labels := by
      have hz : ∀ j, raw13843 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13843step0 = (fun i j => raw13843 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13843step0 raw13843; decide +kernel
      have hl : raw13843step0Labels = raw13843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13843 raw13843Labels permutation346 hz
    mixedMoment B raw13843step0 raw13843step0Labels = mixedMoment B raw13843step1 raw13843step1Labels := by
      have ha : raw13843step1 = (fun i j => raw13843step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13843step1 raw13843step0; decide +kernel
      have hl : raw13843step1Labels = raw13843step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13843step0 raw13843step0Labels permutation36 permutation6
    mixedMoment B raw13843step1 raw13843step1Labels = mixedMoment B raw13843step2 raw13843step2Labels := by
      have ha : raw13843step2 = raw13843step1 := by apply Matrix.ext; unfold raw13843step2 raw13843step1; decide +kernel
      have hl : raw13843step1Labels = labelEmbedding9 ∘ raw13843step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13843step1 raw13843step1Labels raw13843step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical13844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13844 raw13844Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw13844 raw13844Labels = mixedMoment B raw13844step0 raw13844step0Labels := by
      have ha : raw13844step0 = (fun i j => raw13844 (permutation195 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13844step0 raw13844; decide +kernel
      have hl : raw13844step0Labels = raw13844Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13844 raw13844Labels permutation195 permutation4
    mixedMoment B raw13844step0 raw13844step0Labels = mixedMoment B raw13844step1 raw13844step1Labels := by
      have ha : raw13844step1 = -raw13844step0 := by apply Matrix.ext; change ∀ i j, raw13844step1 i j = -(raw13844step0 i j); unfold raw13844step1 raw13844step0; decide +kernel
      have hl : raw13844step1Labels = raw13844step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13844step1 raw13844step1Labels = mixedMoment B raw13844step2 raw13844step2Labels := by
      have ha : raw13844step2 = raw13844step1 := by apply Matrix.ext; unfold raw13844step2 raw13844step1; decide +kernel
      have hl : raw13844step1Labels = labelEmbedding7 ∘ raw13844step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13844step1 raw13844step1Labels raw13844step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical13845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13845 raw13845Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw13845 raw13845Labels = mixedMoment B raw13845step0 raw13845step0Labels := by
      have hz : ∀ j, raw13845 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13845step0 = (fun i j => raw13845 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13845step0 raw13845; decide +kernel
      have hl : raw13845step0Labels = raw13845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13845 raw13845Labels permutation265 hz
    mixedMoment B raw13845step0 raw13845step0Labels = mixedMoment B raw13845step1 raw13845step1Labels := by
      have ha : raw13845step1 = (fun i j => raw13845step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13845step1 raw13845step0; decide +kernel
      have hl : raw13845step1Labels = raw13845step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13845step0 raw13845step0Labels permutation37 permutation6
    mixedMoment B raw13845step1 raw13845step1Labels = mixedMoment B raw13845step2 raw13845step2Labels := by
      have ha : raw13845step2 = raw13845step1 := by apply Matrix.ext; unfold raw13845step2 raw13845step1; decide +kernel
      have hl : raw13845step1Labels = labelEmbedding9 ∘ raw13845step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13845step1 raw13845step1Labels raw13845step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical13846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13846 raw13846Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw13846 raw13846Labels = mixedMoment B raw13846step0 raw13846step0Labels := by
      have ha : raw13846step0 = (fun i j => raw13846 (permutation181 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13846step0 raw13846; decide +kernel
      have hl : raw13846step0Labels = raw13846Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13846 raw13846Labels permutation181 permutation6
    mixedMoment B raw13846step0 raw13846step0Labels = mixedMoment B raw13846step1 raw13846step1Labels := by
      have ha : raw13846step1 = raw13846step0 := by apply Matrix.ext; unfold raw13846step1 raw13846step0; decide +kernel
      have hl : raw13846step0Labels = labelEmbedding9 ∘ raw13846step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13846step0 raw13846step0Labels raw13846step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

theorem canonical13847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13847 raw13847Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw13847 raw13847Labels = mixedMoment B raw13847step0 raw13847step0Labels := by
      have ha : raw13847step0 = (fun i j => raw13847 (permutation179 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13847step0 raw13847; decide +kernel
      have hl : raw13847step0Labels = raw13847Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13847 raw13847Labels permutation179 permutation6
    mixedMoment B raw13847step0 raw13847step0Labels = mixedMoment B raw13847step1 raw13847step1Labels := by
      have ha : raw13847step1 = raw13847step0 := by apply Matrix.ext; unfold raw13847step1 raw13847step0; decide +kernel
      have hl : raw13847step0Labels = labelEmbedding9 ∘ raw13847step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13847step0 raw13847step0Labels raw13847step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5256 node5256Labels := by rfl

theorem canonical13848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13848 raw13848Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw13848 raw13848Labels = mixedMoment B raw13848step0 raw13848step0Labels := by
      have ha : raw13848step0 = (fun i j => raw13848 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13848step0 raw13848; decide +kernel
      have hl : raw13848step0Labels = raw13848Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13848 raw13848Labels permutation194 permutation4
    mixedMoment B raw13848step0 raw13848step0Labels = mixedMoment B raw13848step1 raw13848step1Labels := by
      have ha : raw13848step1 = -raw13848step0 := by apply Matrix.ext; change ∀ i j, raw13848step1 i j = -(raw13848step0 i j); unfold raw13848step1 raw13848step0; decide +kernel
      have hl : raw13848step1Labels = raw13848step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13848step1 raw13848step1Labels = mixedMoment B raw13848step2 raw13848step2Labels := by
      have ha : raw13848step2 = raw13848step1 := by apply Matrix.ext; unfold raw13848step2 raw13848step1; decide +kernel
      have hl : raw13848step1Labels = labelEmbedding7 ∘ raw13848step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13848step1 raw13848step1Labels raw13848step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical13849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13849 raw13849Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw13849 raw13849Labels = mixedMoment B raw13849step0 raw13849step0Labels := by
      have hz : ∀ j, raw13849 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13849step0 = (fun i j => raw13849 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13849step0 raw13849; decide +kernel
      have hl : raw13849step0Labels = raw13849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13849 raw13849Labels permutation265 hz
    mixedMoment B raw13849step0 raw13849step0Labels = mixedMoment B raw13849step1 raw13849step1Labels := by
      have ha : raw13849step1 = (fun i j => raw13849step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13849step1 raw13849step0; decide +kernel
      have hl : raw13849step1Labels = raw13849step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13849step0 raw13849step0Labels permutation36 permutation6
    mixedMoment B raw13849step1 raw13849step1Labels = mixedMoment B raw13849step2 raw13849step2Labels := by
      have ha : raw13849step2 = raw13849step1 := by apply Matrix.ext; unfold raw13849step2 raw13849step1; decide +kernel
      have hl : raw13849step1Labels = labelEmbedding9 ∘ raw13849step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13849step1 raw13849step1Labels raw13849step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical13850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13850 raw13850Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw13850 raw13850Labels = mixedMoment B raw13850step0 raw13850step0Labels := by
      have ha : raw13850step0 = (fun i j => raw13850 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13850step0 raw13850; decide +kernel
      have hl : raw13850step0Labels = raw13850Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13850 raw13850Labels permutation180 permutation6
    mixedMoment B raw13850step0 raw13850step0Labels = mixedMoment B raw13850step1 raw13850step1Labels := by
      have ha : raw13850step1 = raw13850step0 := by apply Matrix.ext; unfold raw13850step1 raw13850step0; decide +kernel
      have hl : raw13850step0Labels = labelEmbedding9 ∘ raw13850step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13850step0 raw13850step0Labels raw13850step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

theorem canonical13851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13851 raw13851Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw13851 raw13851Labels = mixedMoment B raw13851step0 raw13851step0Labels := by
      have ha : raw13851step0 = (fun i j => raw13851 (permutation177 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13851step0 raw13851; decide +kernel
      have hl : raw13851step0Labels = raw13851Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13851 raw13851Labels permutation177 permutation6
    mixedMoment B raw13851step0 raw13851step0Labels = mixedMoment B raw13851step1 raw13851step1Labels := by
      have ha : raw13851step1 = raw13851step0 := by apply Matrix.ext; unfold raw13851step1 raw13851step0; decide +kernel
      have hl : raw13851step0Labels = labelEmbedding9 ∘ raw13851step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13851step0 raw13851step0Labels raw13851step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5256 node5256Labels := by rfl

theorem canonical13852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13852 raw13852Labels = mixedMoment B node4833 node4833Labels := by
  calc
    mixedMoment B raw13852 raw13852Labels = mixedMoment B raw13852step0 raw13852step0Labels := by
      have ha : raw13852step0 = (fun i j => raw13852 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13852step0 raw13852; decide +kernel
      have hl : raw13852step0Labels = raw13852Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13852 raw13852Labels permutation176 permutation4
    mixedMoment B raw13852step0 raw13852step0Labels = mixedMoment B raw13852step1 raw13852step1Labels := by
      have ha : raw13852step1 = -raw13852step0 := by apply Matrix.ext; change ∀ i j, raw13852step1 i j = -(raw13852step0 i j); unfold raw13852step1 raw13852step0; decide +kernel
      have hl : raw13852step1Labels = raw13852step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13852step1 raw13852step1Labels = mixedMoment B raw13852step2 raw13852step2Labels := by
      have ha : raw13852step2 = raw13852step1 := by apply Matrix.ext; unfold raw13852step2 raw13852step1; decide +kernel
      have hl : raw13852step1Labels = labelEmbedding7 ∘ raw13852step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13852step1 raw13852step1Labels raw13852step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4833 node4833Labels := by rfl

theorem canonical13853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13853 raw13853Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw13853 raw13853Labels = mixedMoment B raw13853step0 raw13853step0Labels := by
      have hz : ∀ j, raw13853 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13853step0 = (fun i j => raw13853 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13853step0 raw13853; decide +kernel
      have hl : raw13853step0Labels = raw13853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13853 raw13853Labels permutation265 hz
    mixedMoment B raw13853step0 raw13853step0Labels = mixedMoment B raw13853step1 raw13853step1Labels := by
      have ha : raw13853step1 = (fun i j => raw13853step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13853step1 raw13853step0; decide +kernel
      have hl : raw13853step1Labels = raw13853step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13853step0 raw13853step0Labels permutation32 permutation6
    mixedMoment B raw13853step1 raw13853step1Labels = mixedMoment B raw13853step2 raw13853step2Labels := by
      have ha : raw13853step2 = raw13853step1 := by apply Matrix.ext; unfold raw13853step2 raw13853step1; decide +kernel
      have hl : raw13853step1Labels = labelEmbedding9 ∘ raw13853step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13853step1 raw13853step1Labels raw13853step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5273 node5273Labels := by rfl

theorem canonical13854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13854 raw13854Labels = mixedMoment B node5227 node5227Labels := by
  calc
    mixedMoment B raw13854 raw13854Labels = mixedMoment B raw13854step0 raw13854step0Labels := by
      have ha : raw13854step0 = (fun i j => raw13854 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13854step0 raw13854; decide +kernel
      have hl : raw13854step0Labels = raw13854Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13854 raw13854Labels permutation176 permutation6
    mixedMoment B raw13854step0 raw13854step0Labels = mixedMoment B raw13854step1 raw13854step1Labels := by
      have ha : raw13854step1 = raw13854step0 := by apply Matrix.ext; unfold raw13854step1 raw13854step0; decide +kernel
      have hl : raw13854step0Labels = labelEmbedding9 ∘ raw13854step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13854step0 raw13854step0Labels raw13854step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5227 node5227Labels := by rfl

theorem canonical13855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13855 raw13855Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw13855 raw13855Labels = mixedMoment B raw13855step0 raw13855step0Labels := by
      have ha : raw13855step0 = (fun i j => raw13855 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13855step0 raw13855; decide +kernel
      have hl : raw13855step0Labels = raw13855Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13855 raw13855Labels permutation176 permutation6
    mixedMoment B raw13855step0 raw13855step0Labels = mixedMoment B raw13855step1 raw13855step1Labels := by
      have ha : raw13855step1 = raw13855step0 := by apply Matrix.ext; unfold raw13855step1 raw13855step0; decide +kernel
      have hl : raw13855step0Labels = labelEmbedding9 ∘ raw13855step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13855step0 raw13855step0Labels raw13855step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical13856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13856 raw13856Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw13856 raw13856Labels = mixedMoment B raw13856step0 raw13856step0Labels := by
      have ha : raw13856step0 = (fun i j => raw13856 (permutation178 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13856step0 raw13856; decide +kernel
      have hl : raw13856step0Labels = raw13856Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13856 raw13856Labels permutation178 permutation6
    mixedMoment B raw13856step0 raw13856step0Labels = mixedMoment B raw13856step1 raw13856step1Labels := by
      have ha : raw13856step1 = raw13856step0 := by apply Matrix.ext; unfold raw13856step1 raw13856step0; decide +kernel
      have hl : raw13856step0Labels = labelEmbedding9 ∘ raw13856step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13856step0 raw13856step0Labels raw13856step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical13857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13857 raw13857Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw13857 raw13857Labels = mixedMoment B raw13857step0 raw13857step0Labels := by
      have hz : ∀ j, raw13857 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13857step0 = (fun i j => raw13857 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13857step0 raw13857; decide +kernel
      have hl : raw13857step0Labels = raw13857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13857 raw13857Labels permutation265 hz
    mixedMoment B raw13857step0 raw13857step0Labels = mixedMoment B raw13857step1 raw13857step1Labels := by
      have ha : raw13857step1 = (fun i j => raw13857step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13857step1 raw13857step0; decide +kernel
      have hl : raw13857step1Labels = raw13857step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13857step0 raw13857step0Labels permutation36 permutation6
    _ = mixedMoment B node3100 node3100Labels := by rfl

theorem canonical13858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13858 raw13858Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw13858 raw13858Labels = mixedMoment B raw13858step0 raw13858step0Labels := by
      have ha : raw13858step0 = (fun i j => raw13858 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13858step0 raw13858; decide +kernel
      have hl : raw13858step0Labels = raw13858Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13858 raw13858Labels permutation180 permutation6
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical13859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13859 raw13859Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw13859 raw13859Labels = mixedMoment B raw13859step0 raw13859step0Labels := by
      have ha : raw13859step0 = (fun i j => raw13859 (permutation177 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13859step0 raw13859; decide +kernel
      have hl : raw13859step0Labels = raw13859Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13859 raw13859Labels permutation177 permutation6
    _ = mixedMoment B node3087 node3087Labels := by rfl

theorem canonical13860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13860 raw13860Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw13860 raw13860Labels = mixedMoment B raw13860step0 raw13860step0Labels := by
      have ha : raw13860step0 = (fun i j => raw13860 (permutation179 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13860step0 raw13860; decide +kernel
      have hl : raw13860step0Labels = raw13860Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13860 raw13860Labels permutation179 permutation6
    _ = mixedMoment B node3087 node3087Labels := by rfl

theorem canonical13861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13861 raw13861Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw13861 raw13861Labels = mixedMoment B raw13861step0 raw13861step0Labels := by
      have ha : raw13861step0 = (fun i j => raw13861 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13861step0 raw13861; decide +kernel
      have hl : raw13861step0Labels = raw13861Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13861 raw13861Labels permutation180 permutation6
    _ = mixedMoment B node2214 node2214Labels := by rfl

theorem canonical13862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13862 raw13862Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw13862 raw13862Labels = mixedMoment B raw13862step0 raw13862step0Labels := by
      have ha : raw13862step0 = (fun i j => raw13862 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13862step0 raw13862; decide +kernel
      have hl : raw13862step0Labels = raw13862Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13862 raw13862Labels permutation180 permutation6
    _ = mixedMoment B node2676 node2676Labels := by rfl

theorem canonical13863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13863 raw13863Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw13863 raw13863Labels = mixedMoment B raw13863step0 raw13863step0Labels := by
      have ha : raw13863step0 = (fun i j => raw13863 (permutation177 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13863step0 raw13863; decide +kernel
      have hl : raw13863step0Labels = raw13863Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13863 raw13863Labels permutation177 permutation6
    _ = mixedMoment B node2730 node2730Labels := by rfl

theorem canonical13864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13864 raw13864Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw13864 raw13864Labels = mixedMoment B raw13864step0 raw13864step0Labels := by
      have ha : raw13864step0 = (fun i j => raw13864 (permutation179 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13864step0 raw13864; decide +kernel
      have hl : raw13864step0Labels = raw13864Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13864 raw13864Labels permutation179 permutation6
    _ = mixedMoment B node2730 node2730Labels := by rfl

theorem canonical13865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13865 raw13865Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw13865 raw13865Labels = mixedMoment B raw13865step0 raw13865step0Labels := by
      have hz : ∀ j, raw13865 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13865step0 = (fun i j => raw13865 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13865step0 raw13865; decide +kernel
      have hl : raw13865step0Labels = raw13865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13865 raw13865Labels permutation346 hz
    mixedMoment B raw13865step0 raw13865step0Labels = mixedMoment B raw13865step1 raw13865step1Labels := by
      have ha : raw13865step1 = (fun i j => raw13865step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13865step1 raw13865step0; decide +kernel
      have hl : raw13865step1Labels = raw13865step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13865step0 raw13865step0Labels permutation36 permutation6
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical13866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13866 raw13866Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw13866 raw13866Labels = mixedMoment B raw13866step0 raw13866step0Labels := by
      have ha : raw13866step0 = (fun i j => raw13866 (permutation181 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13866step0 raw13866; decide +kernel
      have hl : raw13866step0Labels = raw13866Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13866 raw13866Labels permutation181 permutation6
    _ = mixedMoment B node2202 node2202Labels := by rfl

theorem canonical13867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13867 raw13867Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw13867 raw13867Labels = mixedMoment B raw13867step0 raw13867step0Labels := by
      have hz : ∀ j, raw13867 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13867step0 = (fun i j => raw13867 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13867step0 raw13867; decide +kernel
      have hl : raw13867step0Labels = raw13867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13867 raw13867Labels permutation265 hz
    mixedMoment B raw13867step0 raw13867step0Labels = mixedMoment B raw13867step1 raw13867step1Labels := by
      have ha : raw13867step1 = (fun i j => raw13867step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13867step1 raw13867step0; decide +kernel
      have hl : raw13867step1Labels = raw13867step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13867step0 raw13867step0Labels permutation37 permutation6
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical13868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13868 raw13868Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw13868 raw13868Labels = mixedMoment B raw13868step0 raw13868step0Labels := by
      have ha : raw13868step0 = (fun i j => raw13868 (permutation181 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13868step0 raw13868; decide +kernel
      have hl : raw13868step0Labels = raw13868Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13868 raw13868Labels permutation181 permutation6
    _ = mixedMoment B node2669 node2669Labels := by rfl

theorem canonical13869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13869 raw13869Labels = mixedMoment B node2720 node2720Labels := by
  calc
    mixedMoment B raw13869 raw13869Labels = mixedMoment B raw13869step0 raw13869step0Labels := by
      have ha : raw13869step0 = (fun i j => raw13869 (permutation179 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13869step0 raw13869; decide +kernel
      have hl : raw13869step0Labels = raw13869Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13869 raw13869Labels permutation179 permutation6
    _ = mixedMoment B node2720 node2720Labels := by rfl

theorem canonical13870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13870 raw13870Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw13870 raw13870Labels = mixedMoment B raw13870step0 raw13870step0Labels := by
      have ha : raw13870step0 = (fun i j => raw13870 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13870step0 raw13870; decide +kernel
      have hl : raw13870step0Labels = raw13870Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13870 raw13870Labels permutation180 permutation6
    _ = mixedMoment B node2202 node2202Labels := by rfl

theorem canonical13871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13871 raw13871Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw13871 raw13871Labels = mixedMoment B raw13871step0 raw13871step0Labels := by
      have hz : ∀ j, raw13871 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13871step0 = (fun i j => raw13871 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13871step0 raw13871; decide +kernel
      have hl : raw13871step0Labels = raw13871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13871 raw13871Labels permutation265 hz
    mixedMoment B raw13871step0 raw13871step0Labels = mixedMoment B raw13871step1 raw13871step1Labels := by
      have ha : raw13871step1 = (fun i j => raw13871step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13871step1 raw13871step0; decide +kernel
      have hl : raw13871step1Labels = raw13871step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13871step0 raw13871step0Labels permutation36 permutation6
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical13872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13872 raw13872Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw13872 raw13872Labels = mixedMoment B raw13872step0 raw13872step0Labels := by
      have ha : raw13872step0 = (fun i j => raw13872 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13872step0 raw13872; decide +kernel
      have hl : raw13872step0Labels = raw13872Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13872 raw13872Labels permutation180 permutation6
    _ = mixedMoment B node2669 node2669Labels := by rfl

theorem canonical13873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13873 raw13873Labels = mixedMoment B node2720 node2720Labels := by
  calc
    mixedMoment B raw13873 raw13873Labels = mixedMoment B raw13873step0 raw13873step0Labels := by
      have ha : raw13873step0 = (fun i j => raw13873 (permutation177 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13873step0 raw13873; decide +kernel
      have hl : raw13873step0Labels = raw13873Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13873 raw13873Labels permutation177 permutation6
    _ = mixedMoment B node2720 node2720Labels := by rfl

theorem canonical13874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13874 raw13874Labels = mixedMoment B node2204 node2204Labels := by
  calc
    mixedMoment B raw13874 raw13874Labels = mixedMoment B raw13874step0 raw13874step0Labels := by
      have ha : raw13874step0 = (fun i j => raw13874 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13874step0 raw13874; decide +kernel
      have hl : raw13874step0Labels = raw13874Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13874 raw13874Labels permutation176 permutation6
    _ = mixedMoment B node2204 node2204Labels := by rfl

theorem canonical13875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13875 raw13875Labels = mixedMoment B node2741 node2741Labels := by
  calc
    mixedMoment B raw13875 raw13875Labels = mixedMoment B raw13875step0 raw13875step0Labels := by
      have hz : ∀ j, raw13875 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13875step0 = (fun i j => raw13875 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13875step0 raw13875; decide +kernel
      have hl : raw13875step0Labels = raw13875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13875 raw13875Labels permutation265 hz
    mixedMoment B raw13875step0 raw13875step0Labels = mixedMoment B raw13875step1 raw13875step1Labels := by
      have ha : raw13875step1 = (fun i j => raw13875step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13875step1 raw13875step0; decide +kernel
      have hl : raw13875step1Labels = raw13875step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13875step0 raw13875step0Labels permutation32 permutation6
    _ = mixedMoment B node2741 node2741Labels := by rfl

theorem canonical13876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13876 raw13876Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw13876 raw13876Labels = mixedMoment B raw13876step0 raw13876step0Labels := by
      have ha : raw13876step0 = (fun i j => raw13876 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13876step0 raw13876; decide +kernel
      have hl : raw13876step0Labels = raw13876Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13876 raw13876Labels permutation176 permutation6
    _ = mixedMoment B node2671 node2671Labels := by rfl

theorem canonical13877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13877 raw13877Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw13877 raw13877Labels = mixedMoment B raw13877step0 raw13877step0Labels := by
      have ha : raw13877step0 = (fun i j => raw13877 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13877step0 raw13877; decide +kernel
      have hl : raw13877step0Labels = raw13877Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13877 raw13877Labels permutation176 permutation6
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical13878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13878 raw13878Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw13878 raw13878Labels = mixedMoment B raw13878step0 raw13878step0Labels := by
      have ha : raw13878step0 = (fun i j => raw13878 (permutation178 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13878step0 raw13878; decide +kernel
      have hl : raw13878step0Labels = raw13878Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13878 raw13878Labels permutation178 permutation6
    _ = mixedMoment B node2721 node2721Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2094 raw2094Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw2094 raw2094Labels = mixedMoment B raw2094step0 raw2094step0Labels := by
      have ha : raw2094step0 = (fun i j => raw2094 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2094step0 raw2094; decide +kernel
      have hl : raw2094step0Labels = raw2094Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2094 raw2094Labels permutation152 permutation4
    mixedMoment B raw2094step0 raw2094step0Labels = mixedMoment B raw2094step1 raw2094step1Labels := by
      have ha : raw2094step1 = raw2094step0 := by apply Matrix.ext; unfold raw2094step1 raw2094step0; decide +kernel
      have hl : raw2094step0Labels = labelEmbedding7 ∘ raw2094step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2094step0 raw2094step0Labels raw2094step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

theorem canonical2095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2095 raw2095Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw2095 raw2095Labels = mixedMoment B raw2095step0 raw2095step0Labels := by
      have ha : raw2095step0 = (fun i j => raw2095 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2095step0 raw2095; decide +kernel
      have hl : raw2095step0Labels = raw2095Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2095 raw2095Labels permutation152 permutation4
    _ = mixedMoment B node2480 node2480Labels := by rfl

theorem canonical2096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2096 raw2096Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw2096 raw2096Labels = mixedMoment B raw2096step0 raw2096step0Labels := by
      have ha : raw2096step0 = (fun i j => raw2096 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2096step0 raw2096; decide +kernel
      have hl : raw2096step0Labels = raw2096Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2096 raw2096Labels permutation158 permutation6
    mixedMoment B raw2096step0 raw2096step0Labels = mixedMoment B raw2096step1 raw2096step1Labels := by
      have ha : raw2096step1 = -raw2096step0 := by apply Matrix.ext; change ∀ i j, raw2096step1 i j = -(raw2096step0 i j); unfold raw2096step1 raw2096step0; decide +kernel
      have hl : raw2096step1Labels = raw2096step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2096step1 raw2096step1Labels = mixedMoment B raw2096step2 raw2096step2Labels := by
      have ha : raw2096step2 = raw2096step1 := by apply Matrix.ext; unfold raw2096step2 raw2096step1; decide +kernel
      have hl : raw2096step1Labels = labelEmbedding1 ∘ raw2096step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2096step1 raw2096step1Labels raw2096step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

theorem canonical2100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2100 raw2100Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw2100 raw2100Labels = mixedMoment B raw2100step0 raw2100step0Labels := by
      have ha : raw2100step0 = (fun i j => raw2100 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2100step0 raw2100; decide +kernel
      have hl : raw2100step0Labels = raw2100Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2100 raw2100Labels permutation152 permutation4
    mixedMoment B raw2100step0 raw2100step0Labels = mixedMoment B raw2100step1 raw2100step1Labels := by
      have ha : raw2100step1 = raw2100step0 := by apply Matrix.ext; unfold raw2100step1 raw2100step0; decide +kernel
      have hl : raw2100step0Labels = labelEmbedding7 ∘ raw2100step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2100step0 raw2100step0Labels raw2100step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5076 node5076Labels := by rfl

theorem canonical2101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2101 raw2101Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw2101 raw2101Labels = mixedMoment B raw2101step0 raw2101step0Labels := by
      have ha : raw2101step0 = (fun i j => raw2101 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2101step0 raw2101; decide +kernel
      have hl : raw2101step0Labels = raw2101Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2101 raw2101Labels permutation152 permutation4
    _ = mixedMoment B node2483 node2483Labels := by rfl

theorem canonical2102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2102 raw2102Labels = mixedMoment B node3477 node3477Labels := by
  calc
    mixedMoment B raw2102 raw2102Labels = mixedMoment B raw2102step0 raw2102step0Labels := by
      have ha : raw2102step0 = (fun i j => raw2102 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2102step0 raw2102; decide +kernel
      have hl : raw2102step0Labels = raw2102Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2102 raw2102Labels permutation170 permutation6
    mixedMoment B raw2102step0 raw2102step0Labels = mixedMoment B raw2102step1 raw2102step1Labels := by
      have ha : raw2102step1 = -raw2102step0 := by apply Matrix.ext; change ∀ i j, raw2102step1 i j = -(raw2102step0 i j); unfold raw2102step1 raw2102step0; decide +kernel
      have hl : raw2102step1Labels = raw2102step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2102step1 raw2102step1Labels = mixedMoment B raw2102step2 raw2102step2Labels := by
      have ha : raw2102step2 = raw2102step1 := by apply Matrix.ext; unfold raw2102step2 raw2102step1; decide +kernel
      have hl : raw2102step1Labels = labelEmbedding1 ∘ raw2102step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2102step1 raw2102step1Labels raw2102step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3477 node3477Labels := by rfl

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

theorem canonical2247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2247 raw2247Labels = mixedMoment B node5227 node5227Labels := by
  calc
    mixedMoment B raw2247 raw2247Labels = mixedMoment B raw2247step0 raw2247step0Labels := by
      have ha : raw2247step0 = (fun i j => raw2247 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2247step0 raw2247; decide +kernel
      have hl : raw2247step0Labels = raw2247Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2247 raw2247Labels permutation152 permutation4
    mixedMoment B raw2247step0 raw2247step0Labels = mixedMoment B raw2247step1 raw2247step1Labels := by
      have ha : raw2247step1 = raw2247step0 := by apply Matrix.ext; unfold raw2247step1 raw2247step0; decide +kernel
      have hl : raw2247step0Labels = labelEmbedding7 ∘ raw2247step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2247step0 raw2247step0Labels raw2247step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5227 node5227Labels := by rfl

theorem canonical2248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2248 raw2248Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw2248 raw2248Labels = mixedMoment B raw2248step0 raw2248step0Labels := by
      have ha : raw2248step0 = (fun i j => raw2248 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2248step0 raw2248; decide +kernel
      have hl : raw2248step0Labels = raw2248Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2248 raw2248Labels permutation152 permutation4
    _ = mixedMoment B node2671 node2671Labels := by rfl

theorem canonical2249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2249 raw2249Labels = mixedMoment B node3390 node3390Labels := by
  calc
    mixedMoment B raw2249 raw2249Labels = mixedMoment B raw2249step0 raw2249step0Labels := by
      have ha : raw2249step0 = (fun i j => raw2249 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2249step0 raw2249; decide +kernel
      have hl : raw2249step0Labels = raw2249Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2249 raw2249Labels permutation152 permutation6
    mixedMoment B raw2249step0 raw2249step0Labels = mixedMoment B raw2249step1 raw2249step1Labels := by
      have ha : raw2249step1 = -raw2249step0 := by apply Matrix.ext; change ∀ i j, raw2249step1 i j = -(raw2249step0 i j); unfold raw2249step1 raw2249step0; decide +kernel
      have hl : raw2249step1Labels = raw2249step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2249step1 raw2249step1Labels = mixedMoment B raw2249step2 raw2249step2Labels := by
      have ha : raw2249step2 = raw2249step1 := by apply Matrix.ext; unfold raw2249step2 raw2249step1; decide +kernel
      have hl : raw2249step1Labels = labelEmbedding1 ∘ raw2249step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2249step1 raw2249step1Labels raw2249step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3390 node3390Labels := by rfl

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

theorem canonical2274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2274 raw2274Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw2274 raw2274Labels = mixedMoment B raw2274step0 raw2274step0Labels := by
      have ha : raw2274step0 = (fun i j => raw2274 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2274step0 raw2274; decide +kernel
      have hl : raw2274step0Labels = raw2274Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2274 raw2274Labels permutation32 permutation4
    mixedMoment B raw2274step0 raw2274step0Labels = mixedMoment B raw2274step1 raw2274step1Labels := by
      have ha : raw2274step1 = raw2274step0 := by apply Matrix.ext; unfold raw2274step1 raw2274step0; decide +kernel
      have hl : raw2274step0Labels = labelEmbedding7 ∘ raw2274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2274step0 raw2274step0Labels raw2274step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2275 raw2275Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw2275 raw2275Labels = mixedMoment B raw2275step0 raw2275step0Labels := by
      have ha : raw2275step0 = (fun i j => raw2275 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2275step0 raw2275; decide +kernel
      have hl : raw2275step0Labels = raw2275Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2275 raw2275Labels permutation32 permutation4
    _ = mixedMoment B node2723 node2723Labels := by rfl

theorem canonical2276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2276 raw2276Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw2276 raw2276Labels = mixedMoment B raw2276step0 raw2276step0Labels := by
      have ha : raw2276step0 = (fun i j => raw2276 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2276step0 raw2276; decide +kernel
      have hl : raw2276step0Labels = raw2276Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2276 raw2276Labels permutation32 permutation6
    mixedMoment B raw2276step0 raw2276step0Labels = mixedMoment B raw2276step1 raw2276step1Labels := by
      have ha : raw2276step1 = -raw2276step0 := by apply Matrix.ext; change ∀ i j, raw2276step1 i j = -(raw2276step0 i j); unfold raw2276step1 raw2276step0; decide +kernel
      have hl : raw2276step1Labels = raw2276step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2276step1 raw2276step1Labels = mixedMoment B raw2276step2 raw2276step2Labels := by
      have ha : raw2276step2 = raw2276step1 := by apply Matrix.ext; unfold raw2276step2 raw2276step1; decide +kernel
      have hl : raw2276step1Labels = labelEmbedding1 ∘ raw2276step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2276step1 raw2276step1Labels raw2276step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

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

theorem canonical2292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2292 raw2292Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw2292 raw2292Labels = mixedMoment B raw2292step0 raw2292step0Labels := by
      have ha : raw2292step0 = (fun i j => raw2292 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2292step0 raw2292; decide +kernel
      have hl : raw2292step0Labels = raw2292Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2292 raw2292Labels permutation32 permutation4
    mixedMoment B raw2292step0 raw2292step0Labels = mixedMoment B raw2292step1 raw2292step1Labels := by
      have ha : raw2292step1 = raw2292step0 := by apply Matrix.ext; unfold raw2292step1 raw2292step0; decide +kernel
      have hl : raw2292step0Labels = labelEmbedding7 ∘ raw2292step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2292step0 raw2292step0Labels raw2292step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical2293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2293 raw2293Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw2293 raw2293Labels = mixedMoment B raw2293step0 raw2293step0Labels := by
      have ha : raw2293step0 = (fun i j => raw2293 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2293step0 raw2293; decide +kernel
      have hl : raw2293step0Labels = raw2293Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2293 raw2293Labels permutation32 permutation4
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2294 raw2294Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw2294 raw2294Labels = mixedMoment B raw2294step0 raw2294step0Labels := by
      have ha : raw2294step0 = (fun i j => raw2294 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2294step0 raw2294; decide +kernel
      have hl : raw2294step0Labels = raw2294Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2294 raw2294Labels permutation38 permutation6
    mixedMoment B raw2294step0 raw2294step0Labels = mixedMoment B raw2294step1 raw2294step1Labels := by
      have ha : raw2294step1 = -raw2294step0 := by apply Matrix.ext; change ∀ i j, raw2294step1 i j = -(raw2294step0 i j); unfold raw2294step1 raw2294step0; decide +kernel
      have hl : raw2294step1Labels = raw2294step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2294step1 raw2294step1Labels = mixedMoment B raw2294step2 raw2294step2Labels := by
      have ha : raw2294step2 = raw2294step1 := by apply Matrix.ext; unfold raw2294step2 raw2294step1; decide +kernel
      have hl : raw2294step1Labels = labelEmbedding1 ∘ raw2294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2294step1 raw2294step1Labels raw2294step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

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

theorem canonical2520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2520 raw2520Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw2520 raw2520Labels = mixedMoment B raw2520step0 raw2520step0Labels := by
      have ha : raw2520step0 = (fun i j => raw2520 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2520step0 raw2520; decide +kernel
      have hl : raw2520step0Labels = raw2520Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2520 raw2520Labels permutation152 permutation4
    mixedMoment B raw2520step0 raw2520step0Labels = mixedMoment B raw2520step1 raw2520step1Labels := by
      have ha : raw2520step1 = raw2520step0 := by apply Matrix.ext; unfold raw2520step1 raw2520step0; decide +kernel
      have hl : raw2520step0Labels = labelEmbedding7 ∘ raw2520step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2520step0 raw2520step0Labels raw2520step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical2521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2521 raw2521Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw2521 raw2521Labels = mixedMoment B raw2521step0 raw2521step0Labels := by
      have ha : raw2521step0 = (fun i j => raw2521 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2521step0 raw2521; decide +kernel
      have hl : raw2521step0Labels = raw2521Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2521 raw2521Labels permutation152 permutation4
    _ = mixedMoment B node3849 node3849Labels := by rfl

theorem canonical2522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2522 raw2522Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw2522 raw2522Labels = mixedMoment B raw2522step0 raw2522step0Labels := by
      have ha : raw2522step0 = (fun i j => raw2522 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2522step0 raw2522; decide +kernel
      have hl : raw2522step0Labels = raw2522Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2522 raw2522Labels permutation200 permutation6
    mixedMoment B raw2522step0 raw2522step0Labels = mixedMoment B raw2522step1 raw2522step1Labels := by
      have ha : raw2522step1 = -raw2522step0 := by apply Matrix.ext; change ∀ i j, raw2522step1 i j = -(raw2522step0 i j); unfold raw2522step1 raw2522step0; decide +kernel
      have hl : raw2522step1Labels = raw2522step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2522step1 raw2522step1Labels = mixedMoment B raw2522step2 raw2522step2Labels := by
      have ha : raw2522step2 = raw2522step1 := by apply Matrix.ext; unfold raw2522step2 raw2522step1; decide +kernel
      have hl : raw2522step1Labels = labelEmbedding1 ∘ raw2522step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2522step1 raw2522step1Labels raw2522step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5073 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5073 node5073Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2480 node2480Labels + mixedMoment B node3467 node3467Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2094 singletonSmall5073
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5073) = raw2094Labels := by decide +kernel
  rw [hl, canonical2094 B hB] at h
  have hc0 : mixedMoment B raw2094 (Fin.cases (0 : Fin 2) singletonSmall5073) =
      mixedMoment B node2480 node2480Labels := by
    have ha : raw2094 = raw2095 := by apply Matrix.ext; unfold raw2094 raw2095; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5073 = raw2095Labels := by decide +kernel
    rw [ha, hj, canonical2095 B hB]
  have hc1 : mixedMoment B raw2094 (Fin.cases (1 : Fin 2) singletonSmall5073) =
      mixedMoment B node3467 node3467Labels := by
    have ha : raw2094 = raw2096 := by apply Matrix.ext; unfold raw2094 raw2096; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5073 = raw2096Labels := by decide +kernel
    rw [ha, hj, canonical2096 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5076 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5076 node5076Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2483 node2483Labels + mixedMoment B node3477 node3477Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2100 singletonSmall5076
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5076) = raw2100Labels := by decide +kernel
  rw [hl, canonical2100 B hB] at h
  have hc0 : mixedMoment B raw2100 (Fin.cases (0 : Fin 2) singletonSmall5076) =
      mixedMoment B node2483 node2483Labels := by
    have ha : raw2100 = raw2101 := by apply Matrix.ext; unfold raw2100 raw2101; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5076 = raw2101Labels := by decide +kernel
    rw [ha, hj, canonical2101 B hB]
  have hc1 : mixedMoment B raw2100 (Fin.cases (1 : Fin 2) singletonSmall5076) =
      mixedMoment B node3477 node3477Labels := by
    have ha : raw2100 = raw2102 := by apply Matrix.ext; unfold raw2100 raw2102; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5076 = raw2102Labels := by decide +kernel
    rw [ha, hj, canonical2102 B hB]
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

theorem singleton5227 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5227 node5227Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2671 node2671Labels + mixedMoment B node3390 node3390Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2247 singletonSmall5227
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5227) = raw2247Labels := by decide +kernel
  rw [hl, canonical2247 B hB] at h
  have hc0 : mixedMoment B raw2247 (Fin.cases (0 : Fin 2) singletonSmall5227) =
      mixedMoment B node2671 node2671Labels := by
    have ha : raw2247 = raw2248 := by apply Matrix.ext; unfold raw2247 raw2248; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5227 = raw2248Labels := by decide +kernel
    rw [ha, hj, canonical2248 B hB]
  have hc1 : mixedMoment B raw2247 (Fin.cases (1 : Fin 2) singletonSmall5227) =
      mixedMoment B node3390 node3390Labels := by
    have ha : raw2247 = raw2249 := by apply Matrix.ext; unfold raw2247 raw2249; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5227 = raw2249Labels := by decide +kernel
    rw [ha, hj, canonical2249 B hB]
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

theorem singleton5259 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5259 node5259Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2723 node2723Labels + mixedMoment B node3544 node3544Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2274 singletonSmall5259
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5259) = raw2274Labels := by decide +kernel
  rw [hl, canonical2274 B hB] at h
  have hc0 : mixedMoment B raw2274 (Fin.cases (0 : Fin 2) singletonSmall5259) =
      mixedMoment B node2723 node2723Labels := by
    have ha : raw2274 = raw2275 := by apply Matrix.ext; unfold raw2274 raw2275; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5259 = raw2275Labels := by decide +kernel
    rw [ha, hj, canonical2275 B hB]
  have hc1 : mixedMoment B raw2274 (Fin.cases (1 : Fin 2) singletonSmall5259) =
      mixedMoment B node3544 node3544Labels := by
    have ha : raw2274 = raw2276 := by apply Matrix.ext; unfold raw2274 raw2276; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5259 = raw2276Labels := by decide +kernel
    rw [ha, hj, canonical2276 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5290 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5290 node5290Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2764 node2764Labels + mixedMoment B node3581 node3581Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2292 singletonSmall5290
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5290) = raw2292Labels := by decide +kernel
  rw [hl, canonical2292 B hB] at h
  have hc0 : mixedMoment B raw2292 (Fin.cases (0 : Fin 2) singletonSmall5290) =
      mixedMoment B node2764 node2764Labels := by
    have ha : raw2292 = raw2293 := by apply Matrix.ext; unfold raw2292 raw2293; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5290 = raw2293Labels := by decide +kernel
    rw [ha, hj, canonical2293 B hB]
  have hc1 : mixedMoment B raw2292 (Fin.cases (1 : Fin 2) singletonSmall5290) =
      mixedMoment B node3581 node3581Labels := by
    have ha : raw2292 = raw2294 := by apply Matrix.ext; unfold raw2292 raw2294; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5290 = raw2294Labels := by decide +kernel
    rw [ha, hj, canonical2294 B hB]
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

theorem singleton5431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5431 node5431Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3849 node3849Labels + mixedMoment B node3875 node3875Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2520 singletonSmall5431
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5431) = raw2520Labels := by decide +kernel
  rw [hl, canonical2520 B hB] at h
  have hc0 : mixedMoment B raw2520 (Fin.cases (0 : Fin 2) singletonSmall5431) =
      mixedMoment B node3849 node3849Labels := by
    have ha : raw2520 = raw2521 := by apply Matrix.ext; unfold raw2520 raw2521; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5431 = raw2521Labels := by decide +kernel
    rw [ha, hj, canonical2521 B hB]
  have hc1 : mixedMoment B raw2520 (Fin.cases (1 : Fin 2) singletonSmall5431) =
      mixedMoment B node3875 node3875Labels := by
    have ha : raw2520 = raw2522 := by apply Matrix.ext; unfold raw2520 raw2522; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5431 = raw2522Labels := by decide +kernel
    rw [ha, hj, canonical2522 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5440 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5440 node5440Labels = 0 := by
  exact mixedMoment_order_one B hB node5440 node5440Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2202 node2202Labels = Sparse.eval nodeValue2202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2202) = mixedMoment B node2202 node2202Labels := rfl
  simpa [nodeValue2202, Sparse.eval] using hc.symm

theorem sound2204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2204 node2204Labels = Sparse.eval nodeValue2204 (mixedVector B) := by
  simpa only [nodeValue2204, Sparse.eval_nil] using zero2204 B _hB _hF

theorem sound2214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2214 node2214Labels = Sparse.eval nodeValue2214 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2214) = mixedMoment B node2214 node2214Labels := rfl
  simpa [nodeValue2214, Sparse.eval] using hc.symm

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

theorem sound2263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2263 node2263Labels = Sparse.eval nodeValue2263 (mixedVector B) := by
  simpa only [nodeValue2263, Sparse.eval_nil] using zero2263 B _hB _hF

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

theorem sound2480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2480 node2480Labels = Sparse.eval nodeValue2480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2480) = mixedMoment B node2480 node2480Labels := rfl
  simpa [nodeValue2480, Sparse.eval] using hc.symm

theorem sound2483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2483 node2483Labels = Sparse.eval nodeValue2483 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2483) = mixedMoment B node2483 node2483Labels := rfl
  simpa [nodeValue2483, Sparse.eval] using hc.symm

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

theorem zero2510 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2510 node2510Labels = 0 := by
  exact mixedMoment_order_one B hB node2510 node2510Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2510 node2510Labels = Sparse.eval nodeValue2510 (mixedVector B) := by
  simpa only [nodeValue2510, Sparse.eval_nil] using zero2510 B _hB _hF

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

theorem sound2615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2615 node2615Labels = Sparse.eval nodeValue2615 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2615) = mixedMoment B node2615 node2615Labels := rfl
  simpa [nodeValue2615, Sparse.eval] using hc.symm

theorem sound2617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2617 node2617Labels = Sparse.eval nodeValue2617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2617) = mixedMoment B node2617 node2617Labels := rfl
  simpa [nodeValue2617, Sparse.eval] using hc.symm

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

theorem sound2669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2669 node2669Labels = Sparse.eval nodeValue2669 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2669) = mixedMoment B node2669 node2669Labels := rfl
  simpa [nodeValue2669, Sparse.eval] using hc.symm

theorem sound2671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2671 node2671Labels = Sparse.eval nodeValue2671 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2671) = mixedMoment B node2671 node2671Labels := rfl
  simpa [nodeValue2671, Sparse.eval] using hc.symm

theorem sound2676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2676 node2676Labels = Sparse.eval nodeValue2676 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2676) = mixedMoment B node2676 node2676Labels := rfl
  simpa [nodeValue2676, Sparse.eval] using hc.symm

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

theorem sound2723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2723 node2723Labels = Sparse.eval nodeValue2723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2723) = mixedMoment B node2723 node2723Labels := rfl
  simpa [nodeValue2723, Sparse.eval] using hc.symm

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

theorem sound2741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2741 node2741Labels = Sparse.eval nodeValue2741 (mixedVector B) := by
  simpa only [nodeValue2741, Sparse.eval_nil] using zero2741 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2785 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2785 node2785Labels = 0 := by
  exact mixedMoment_order_one B hB node2785 node2785Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2785 node2785Labels = Sparse.eval nodeValue2785 (mixedVector B) := by
  simpa only [nodeValue2785, Sparse.eval_nil] using zero2785 B _hB _hF

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

theorem sound3037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3037 node3037Labels = Sparse.eval nodeValue3037 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3037) = mixedMoment B node3037 node3037Labels := rfl
  simpa [nodeValue3037, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3085 node3085Labels = 0 := by
  exact mixedMoment_alpha B hF node3085 node3085Labels 2 permutation158
    (by decide +kernel)

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

theorem sound3085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3085 node3085Labels = Sparse.eval nodeValue3085 (mixedVector B) := by
  simpa only [nodeValue3085, Sparse.eval_nil] using zero3085 B _hB _hF

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

theorem sound3288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3288 node3288Labels = Sparse.eval nodeValue3288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3288) = mixedMoment B node3288 node3288Labels := rfl
  simpa [nodeValue3288, Sparse.eval] using hc.symm

theorem sound3289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3289 node3289Labels = Sparse.eval nodeValue3289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3289) = mixedMoment B node3289 node3289Labels := rfl
  simpa [nodeValue3289, Sparse.eval] using hc.symm

theorem sound3290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3290 node3290Labels = Sparse.eval nodeValue3290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3290) = mixedMoment B node3290 node3290Labels := rfl
  simpa [nodeValue3290, Sparse.eval] using hc.symm

theorem sound3292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3292 node3292Labels = Sparse.eval nodeValue3292 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3292) = mixedMoment B node3292 node3292Labels := rfl
  simpa [nodeValue3292, Sparse.eval] using hc.symm

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

theorem sound3390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3390 node3390Labels = Sparse.eval nodeValue3390 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3390) = mixedMoment B node3390 node3390Labels := rfl
  simpa [nodeValue3390, Sparse.eval] using hc.symm

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

theorem zero3469 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3469 node3469Labels = 0 := by
  exact mixedMoment_order_one B hB node3469 node3469Labels 1
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

theorem sound3467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3467 node3467Labels = Sparse.eval nodeValue3467 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3467) = mixedMoment B node3467 node3467Labels := rfl
  simpa [nodeValue3467, Sparse.eval] using hc.symm

theorem sound3469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3469 node3469Labels = Sparse.eval nodeValue3469 (mixedVector B) := by
  simpa only [nodeValue3469, Sparse.eval_nil] using zero3469 B _hB _hF

theorem sound3477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3477 node3477Labels = Sparse.eval nodeValue3477 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3477) = mixedMoment B node3477 node3477Labels := rfl
  simpa [nodeValue3477, Sparse.eval] using hc.symm

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

theorem zero3531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3531 node3531Labels = 0 := by
  exact mixedMoment_alpha B hF node3531 node3531Labels 1 permutation437
    (by decide +kernel)

theorem zero3546 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3546 node3546Labels = 0 := by
  exact mixedMoment_order_one B hB node3546 node3546Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3529 node3529Labels = Sparse.eval nodeValue3529 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3529) = mixedMoment B node3529 node3529Labels := rfl
  simpa [nodeValue3529, Sparse.eval] using hc.symm

theorem sound3531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3531 node3531Labels = Sparse.eval nodeValue3531 (mixedVector B) := by
  simpa only [nodeValue3531, Sparse.eval_nil] using zero3531 B _hB _hF

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

theorem sound3537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3537 node3537Labels = Sparse.eval nodeValue3537 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3537) = mixedMoment B node3537 node3537Labels := rfl
  simpa [nodeValue3537, Sparse.eval] using hc.symm

theorem sound3539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3539 node3539Labels = Sparse.eval nodeValue3539 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3539) = mixedMoment B node3539 node3539Labels := rfl
  simpa [nodeValue3539, Sparse.eval] using hc.symm

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

theorem sound3546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3546 node3546Labels = Sparse.eval nodeValue3546 (mixedVector B) := by
  simpa only [nodeValue3546, Sparse.eval_nil] using zero3546 B _hB _hF

theorem sound3569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3569 node3569Labels = Sparse.eval nodeValue3569 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3569) = mixedMoment B node3569 node3569Labels := rfl
  simpa [nodeValue3569, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3806 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3806 node3806Labels = 0 := by
  exact mixedMoment_order_one B hB node3806 node3806Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3806 node3806Labels = Sparse.eval nodeValue3806 (mixedVector B) := by
  simpa only [nodeValue3806, Sparse.eval_nil] using zero3806 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3859 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3859 node3859Labels = 0 := by
  exact mixedMoment_order_one B hB node3859 node3859Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3859 node3859Labels = Sparse.eval nodeValue3859 (mixedVector B) := by
  simpa only [nodeValue3859, Sparse.eval_nil] using zero3859 B _hB _hF

theorem sound3875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3875 node3875Labels = Sparse.eval nodeValue3875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3875) = mixedMoment B node3875 node3875Labels := rfl
  simpa [nodeValue3875, Sparse.eval] using hc.symm

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

theorem sound4589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4589 node4589Labels = Sparse.eval nodeValue4589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4589) = mixedMoment B node4589 node4589Labels := rfl
  simpa [nodeValue4589, Sparse.eval] using hc.symm

theorem sound4590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4590 node4590Labels = Sparse.eval nodeValue4590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4590) = mixedMoment B node4590 node4590Labels := rfl
  simpa [nodeValue4590, Sparse.eval] using hc.symm

theorem sound4599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4599 node4599Labels = Sparse.eval nodeValue4599 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4599) = mixedMoment B node4599 node4599Labels := rfl
  simpa [nodeValue4599, Sparse.eval] using hc.symm

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

theorem sound4893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4893 node4893Labels = Sparse.eval nodeValue4893 (mixedVector B) := by
  simpa only [nodeValue4893, Sparse.eval_nil] using zero4893 B _hB _hF

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

theorem zero5100 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5100 node5100Labels = 0 := by
  exact mixedMoment_order_one B hB node5100 node5100Labels 1
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

theorem sound5073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5073 node5073Labels = Sparse.eval nodeValue5073 (mixedVector B) := by
  have h := singleton5073 B _hB
  rw [sound2480 B _hB _hF, sound3467 B _hB _hF] at h
  norm_num [nodeValue5073, nodeValue2480, nodeValue3467, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5076 node5076Labels = Sparse.eval nodeValue5076 (mixedVector B) := by
  have h := singleton5076 B _hB
  rw [sound2483 B _hB _hF, sound3477 B _hB _hF] at h
  norm_num [nodeValue5076, nodeValue2483, nodeValue3477, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5100 node5100Labels = Sparse.eval nodeValue5100 (mixedVector B) := by
  simpa only [nodeValue5100, Sparse.eval_nil] using zero5100 B _hB _hF

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

theorem sound5185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5185 node5185Labels = Sparse.eval nodeValue5185 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5185) = mixedMoment B node5185 node5185Labels := rfl
  simpa [nodeValue5185, Sparse.eval] using hc.symm

theorem sound5187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5187 node5187Labels = Sparse.eval nodeValue5187 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5187) = mixedMoment B node5187 node5187Labels := rfl
  simpa [nodeValue5187, Sparse.eval] using hc.symm

theorem sound5197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5197 node5197Labels = Sparse.eval nodeValue5197 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5197) = mixedMoment B node5197 node5197Labels := rfl
  simpa [nodeValue5197, Sparse.eval] using hc.symm

theorem sound5226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5226 node5226Labels = Sparse.eval nodeValue5226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5226) = mixedMoment B node5226 node5226Labels := rfl
  simpa [nodeValue5226, Sparse.eval] using hc.symm

theorem sound5227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5227 node5227Labels = Sparse.eval nodeValue5227 (mixedVector B) := by
  have h := singleton5227 B _hB
  rw [sound2671 B _hB _hF, sound3390 B _hB _hF] at h
  norm_num [nodeValue5227, nodeValue2671, nodeValue3390, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5231 node5231Labels = Sparse.eval nodeValue5231 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5231) = mixedMoment B node5231 node5231Labels := rfl
  simpa [nodeValue5231, Sparse.eval] using hc.symm

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

theorem zero5250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5250 node5250Labels = 0 := by
  exact mixedMoment_alpha B hF node5250 node5250Labels 1 permutation200
    (by decide +kernel)

theorem zero5256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5256 node5256Labels = 0 := by
  exact mixedMoment_alpha B hF node5256 node5256Labels 1 permutation203
    (by decide +kernel)

theorem zero5273 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5273 node5273Labels = 0 := by
  exact mixedMoment_order_one B hB node5273 node5273Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5307 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5307 node5307Labels = 0 := by
  exact mixedMoment_order_one B hB node5307 node5307Labels 1
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

theorem sound5250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5250 node5250Labels = Sparse.eval nodeValue5250 (mixedVector B) := by
  simpa only [nodeValue5250, Sparse.eval_nil] using zero5250 B _hB _hF

theorem sound5251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5251 node5251Labels = Sparse.eval nodeValue5251 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5251) = mixedMoment B node5251 node5251Labels := rfl
  simpa [nodeValue5251, Sparse.eval] using hc.symm

theorem sound5255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5255 node5255Labels = Sparse.eval nodeValue5255 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5255) = mixedMoment B node5255 node5255Labels := rfl
  simpa [nodeValue5255, Sparse.eval] using hc.symm

theorem sound5256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5256 node5256Labels = Sparse.eval nodeValue5256 (mixedVector B) := by
  simpa only [nodeValue5256, Sparse.eval_nil] using zero5256 B _hB _hF

theorem sound5257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5257 node5257Labels = Sparse.eval nodeValue5257 (mixedVector B) := by
  have h := singleton5257 B _hB
  rw [sound2721 B _hB _hF, sound3532 B _hB _hF] at h
  norm_num [nodeValue5257, nodeValue2721, nodeValue3532, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5259 node5259Labels = Sparse.eval nodeValue5259 (mixedVector B) := by
  have h := singleton5259 B _hB
  rw [sound2723 B _hB _hF, sound3544 B _hB _hF] at h
  norm_num [nodeValue5259, nodeValue2723, nodeValue3544, Sparse.eval] at h ⊢
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

theorem sound5271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5271 node5271Labels = Sparse.eval nodeValue5271 (mixedVector B) := by
  have h := singleton5271 B _hB
  rw [sound2739 B _hB _hF, sound3534 B _hB _hF] at h
  norm_num [nodeValue5271, nodeValue2739, nodeValue3534, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5273 node5273Labels = Sparse.eval nodeValue5273 (mixedVector B) := by
  simpa only [nodeValue5273, Sparse.eval_nil] using zero5273 B _hB _hF

theorem sound5281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5281 node5281Labels = Sparse.eval nodeValue5281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5281) = mixedMoment B node5281 node5281Labels := rfl
  simpa [nodeValue5281, Sparse.eval] using hc.symm

theorem sound5290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5290 node5290Labels = Sparse.eval nodeValue5290 (mixedVector B) := by
  have h := singleton5290 B _hB
  rw [sound2764 B _hB _hF, sound3581 B _hB _hF] at h
  norm_num [nodeValue5290, nodeValue2764, nodeValue3581, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5307 node5307Labels = Sparse.eval nodeValue5307 (mixedVector B) := by
  simpa only [nodeValue5307, Sparse.eval_nil] using zero5307 B _hB _hF

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

theorem zero5408 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5408 node5408Labels = 0 := by
  exact mixedMoment_order_one B hB node5408 node5408Labels 1
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

theorem sound5408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5408 node5408Labels = Sparse.eval nodeValue5408 (mixedVector B) := by
  simpa only [nodeValue5408, Sparse.eval_nil] using zero5408 B _hB _hF

theorem sound5431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5431 node5431Labels = Sparse.eval nodeValue5431 (mixedVector B) := by
  have h := singleton5431 B _hB
  rw [sound3849 B _hB _hF, sound3875 B _hB _hF] at h
  norm_num [nodeValue5431, nodeValue3849, nodeValue3875, Sparse.eval] at h ⊢
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

theorem sound5440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5440 node5440Labels = Sparse.eval nodeValue5440 (mixedVector B) := by
  simpa only [nodeValue5440, Sparse.eval_nil] using zero5440 B _hB _hF

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

theorem sourceEq831 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm831 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA831 + difference 0 1) (sourceB831 + difference 1 0) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA831 + difference 0 1) (sourceB831 + difference 1 0) sourceC831) = raw13673 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13673; decide +kernel
    rw [ha]
    exact (canonical13673 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA831 + difference 0 2) (sourceB831 + difference 2 0) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5408) := by
    have ha : (tripleCharges (sourceA831 + difference 0 2) (sourceB831 + difference 2 0) sourceC831) = raw13674 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13674; decide +kernel
    rw [ha]
    exact (canonical13674 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA831 + difference 0 3) (sourceB831 + difference 3 0) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA831 + difference 0 3) (sourceB831 + difference 3 0) sourceC831) = raw13675 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13675; decide +kernel
    rw [ha]
    exact (canonical13675 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA831 + difference 0 4) (sourceB831 + difference 4 0) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA831 + difference 0 4) (sourceB831 + difference 4 0) sourceC831) = raw13676 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13676; decide +kernel
    rw [ha]
    exact (canonical13676 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA831 + difference 0 5) (sourceB831 + difference 5 0) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA831 + difference 0 5) (sourceB831 + difference 5 0) sourceC831) = raw13677 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13677; decide +kernel
    rw [ha]
    exact (canonical13677 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA831 + difference 1 0) (sourceB831 + difference 0 1) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA831 + difference 1 0) (sourceB831 + difference 0 1) sourceC831) = raw13678 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13678; decide +kernel
    rw [ha]
    exact (canonical13678 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA831 + difference 1 2) (sourceB831 + difference 2 1) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5100) := by
    have ha : (tripleCharges (sourceA831 + difference 1 2) (sourceB831 + difference 2 1) sourceC831) = raw13679 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13679; decide +kernel
    rw [ha]
    exact (canonical13679 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA831 + difference 1 3) (sourceB831 + difference 3 1) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA831 + difference 1 3) (sourceB831 + difference 3 1) sourceC831) = raw13680 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13680; decide +kernel
    rw [ha]
    exact (canonical13680 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA831 + difference 1 4) (sourceB831 + difference 4 1) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA831 + difference 1 4) (sourceB831 + difference 4 1) sourceC831) = raw13681 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13681; decide +kernel
    rw [ha]
    exact (canonical13681 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA831 + difference 1 5) (sourceB831 + difference 5 1) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA831 + difference 1 5) (sourceB831 + difference 5 1) sourceC831) = raw13682 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13682; decide +kernel
    rw [ha]
    exact (canonical13682 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA831 + difference 2 0) (sourceB831 + difference 0 2) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA831 + difference 2 0) (sourceB831 + difference 0 2) sourceC831) = raw13683 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13683; decide +kernel
    rw [ha]
    exact (canonical13683 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA831 + difference 2 1) (sourceB831 + difference 1 2) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5197) := by
    have ha : (tripleCharges (sourceA831 + difference 2 1) (sourceB831 + difference 1 2) sourceC831) = raw13684 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13684; decide +kernel
    rw [ha]
    exact (canonical13684 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA831 + difference 2 3) (sourceB831 + difference 3 2) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA831 + difference 2 3) (sourceB831 + difference 3 2) sourceC831) = raw13685 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13685; decide +kernel
    rw [ha]
    exact (canonical13685 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA831 + difference 2 4) (sourceB831 + difference 4 2) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA831 + difference 2 4) (sourceB831 + difference 4 2) sourceC831) = raw13686 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13686; decide +kernel
    rw [ha]
    exact (canonical13686 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA831 + difference 2 5) (sourceB831 + difference 5 2) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA831 + difference 2 5) (sourceB831 + difference 5 2) sourceC831) = raw13687 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13687; decide +kernel
    rw [ha]
    exact (canonical13687 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA831 + difference 3 0) (sourceB831 + difference 0 3) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA831 + difference 3 0) (sourceB831 + difference 0 3) sourceC831) = raw13688 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13688; decide +kernel
    rw [ha]
    exact (canonical13688 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA831 + difference 3 1) (sourceB831 + difference 1 3) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA831 + difference 3 1) (sourceB831 + difference 1 3) sourceC831) = raw13689 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13689; decide +kernel
    rw [ha]
    exact (canonical13689 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA831 + difference 3 2) (sourceB831 + difference 2 3) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA831 + difference 3 2) (sourceB831 + difference 2 3) sourceC831) = raw13690 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13690; decide +kernel
    rw [ha]
    exact (canonical13690 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA831 + difference 3 4) (sourceB831 + difference 4 3) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA831 + difference 3 4) (sourceB831 + difference 4 3) sourceC831) = raw13691 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13691; decide +kernel
    rw [ha]
    exact (canonical13691 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA831 + difference 3 5) (sourceB831 + difference 5 3) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA831 + difference 3 5) (sourceB831 + difference 5 3) sourceC831) = raw13692 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13692; decide +kernel
    rw [ha]
    exact (canonical13692 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA831 + difference 4 0) (sourceB831 + difference 0 4) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA831 + difference 4 0) (sourceB831 + difference 0 4) sourceC831) = raw13693 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13693; decide +kernel
    rw [ha]
    exact (canonical13693 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA831 + difference 4 1) (sourceB831 + difference 1 4) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA831 + difference 4 1) (sourceB831 + difference 1 4) sourceC831) = raw13694 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13694; decide +kernel
    rw [ha]
    exact (canonical13694 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA831 + difference 4 2) (sourceB831 + difference 2 4) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA831 + difference 4 2) (sourceB831 + difference 2 4) sourceC831) = raw13695 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13695; decide +kernel
    rw [ha]
    exact (canonical13695 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA831 + difference 4 3) (sourceB831 + difference 3 4) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA831 + difference 4 3) (sourceB831 + difference 3 4) sourceC831) = raw13696 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13696; decide +kernel
    rw [ha]
    exact (canonical13696 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA831 + difference 4 5) (sourceB831 + difference 5 4) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA831 + difference 4 5) (sourceB831 + difference 5 4) sourceC831) = raw13697 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13697; decide +kernel
    rw [ha]
    exact (canonical13697 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA831 + difference 5 0) (sourceB831 + difference 0 5) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA831 + difference 5 0) (sourceB831 + difference 0 5) sourceC831) = raw13698 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13698; decide +kernel
    rw [ha]
    exact (canonical13698 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA831 + difference 5 1) (sourceB831 + difference 1 5) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5187) := by
    have ha : (tripleCharges (sourceA831 + difference 5 1) (sourceB831 + difference 1 5) sourceC831) = raw13699 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13699; decide +kernel
    rw [ha]
    exact (canonical13699 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA831 + difference 5 2) (sourceB831 + difference 2 5) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA831 + difference 5 2) (sourceB831 + difference 2 5) sourceC831) = raw13700 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13700; decide +kernel
    rw [ha]
    exact (canonical13700 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA831 + difference 5 3) (sourceB831 + difference 3 5) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA831 + difference 5 3) (sourceB831 + difference 3 5) sourceC831) = raw13701 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13701; decide +kernel
    rw [ha]
    exact (canonical13701 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA831 + difference 5 4) (sourceB831 + difference 4 5) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA831 + difference 5 4) (sourceB831 + difference 4 5) sourceC831) = raw13702 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13702; decide +kernel
    rw [ha]
    exact (canonical13702 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA831 sourceB831 sourceC831
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm831, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources26
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq833 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm833 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA833 + difference 0 1) (sourceB833 + difference 1 0) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA833 + difference 0 1) (sourceB833 + difference 1 0) sourceC833) = raw13733 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13733; decide +kernel
    rw [ha]
    exact (canonical13733 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA833 + difference 0 2) (sourceB833 + difference 2 0) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3806) := by
    have ha : (tripleCharges (sourceA833 + difference 0 2) (sourceB833 + difference 2 0) sourceC833) = raw13734 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13734; decide +kernel
    rw [ha]
    exact (canonical13734 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA833 + difference 0 3) (sourceB833 + difference 3 0) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3851) := by
    have ha : (tripleCharges (sourceA833 + difference 0 3) (sourceB833 + difference 3 0) sourceC833) = raw13735 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13735; decide +kernel
    rw [ha]
    exact (canonical13735 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA833 + difference 0 4) (sourceB833 + difference 4 0) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3851) := by
    have ha : (tripleCharges (sourceA833 + difference 0 4) (sourceB833 + difference 4 0) sourceC833) = raw13736 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13736; decide +kernel
    rw [ha]
    exact (canonical13736 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA833 + difference 0 5) (sourceB833 + difference 5 0) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3859) := by
    have ha : (tripleCharges (sourceA833 + difference 0 5) (sourceB833 + difference 5 0) sourceC833) = raw13737 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13737; decide +kernel
    rw [ha]
    exact (canonical13737 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA833 + difference 1 0) (sourceB833 + difference 0 1) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3292) := by
    have ha : (tripleCharges (sourceA833 + difference 1 0) (sourceB833 + difference 0 1) sourceC833) = raw13738 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13738; decide +kernel
    rw [ha]
    exact (canonical13738 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA833 + difference 1 2) (sourceB833 + difference 2 1) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3469) := by
    have ha : (tripleCharges (sourceA833 + difference 1 2) (sourceB833 + difference 2 1) sourceC833) = raw13739 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13739; decide +kernel
    rw [ha]
    exact (canonical13739 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA833 + difference 1 3) (sourceB833 + difference 3 1) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA833 + difference 1 3) (sourceB833 + difference 3 1) sourceC833) = raw13740 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13740; decide +kernel
    rw [ha]
    exact (canonical13740 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA833 + difference 1 4) (sourceB833 + difference 4 1) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA833 + difference 1 4) (sourceB833 + difference 4 1) sourceC833) = raw13741 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13741; decide +kernel
    rw [ha]
    exact (canonical13741 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA833 + difference 1 5) (sourceB833 + difference 5 1) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3546) := by
    have ha : (tripleCharges (sourceA833 + difference 1 5) (sourceB833 + difference 5 1) sourceC833) = raw13742 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13742; decide +kernel
    rw [ha]
    exact (canonical13742 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA833 + difference 2 0) (sourceB833 + difference 0 2) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA833 + difference 2 0) (sourceB833 + difference 0 2) sourceC833) = raw13743 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13743; decide +kernel
    rw [ha]
    exact (canonical13743 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA833 + difference 2 1) (sourceB833 + difference 1 2) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3569) := by
    have ha : (tripleCharges (sourceA833 + difference 2 1) (sourceB833 + difference 1 2) sourceC833) = raw13744 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13744; decide +kernel
    rw [ha]
    exact (canonical13744 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA833 + difference 2 3) (sourceB833 + difference 3 2) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA833 + difference 2 3) (sourceB833 + difference 3 2) sourceC833) = raw13745 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13745; decide +kernel
    rw [ha]
    exact (canonical13745 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA833 + difference 2 4) (sourceB833 + difference 4 2) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA833 + difference 2 4) (sourceB833 + difference 4 2) sourceC833) = raw13746 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13746; decide +kernel
    rw [ha]
    exact (canonical13746 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA833 + difference 2 5) (sourceB833 + difference 5 2) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA833 + difference 2 5) (sourceB833 + difference 5 2) sourceC833) = raw13747 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13747; decide +kernel
    rw [ha]
    exact (canonical13747 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA833 + difference 3 0) (sourceB833 + difference 0 3) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA833 + difference 3 0) (sourceB833 + difference 0 3) sourceC833) = raw13748 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13748; decide +kernel
    rw [ha]
    exact (canonical13748 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA833 + difference 3 1) (sourceB833 + difference 1 3) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA833 + difference 3 1) (sourceB833 + difference 1 3) sourceC833) = raw13749 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13749; decide +kernel
    rw [ha]
    exact (canonical13749 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA833 + difference 3 2) (sourceB833 + difference 2 3) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA833 + difference 3 2) (sourceB833 + difference 2 3) sourceC833) = raw13750 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13750; decide +kernel
    rw [ha]
    exact (canonical13750 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA833 + difference 3 4) (sourceB833 + difference 4 3) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA833 + difference 3 4) (sourceB833 + difference 4 3) sourceC833) = raw13751 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13751; decide +kernel
    rw [ha]
    exact (canonical13751 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA833 + difference 3 5) (sourceB833 + difference 5 3) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA833 + difference 3 5) (sourceB833 + difference 5 3) sourceC833) = raw13752 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13752; decide +kernel
    rw [ha]
    exact (canonical13752 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA833 + difference 4 0) (sourceB833 + difference 0 4) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA833 + difference 4 0) (sourceB833 + difference 0 4) sourceC833) = raw13753 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13753; decide +kernel
    rw [ha]
    exact (canonical13753 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA833 + difference 4 1) (sourceB833 + difference 1 4) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA833 + difference 4 1) (sourceB833 + difference 1 4) sourceC833) = raw13754 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13754; decide +kernel
    rw [ha]
    exact (canonical13754 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA833 + difference 4 2) (sourceB833 + difference 2 4) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA833 + difference 4 2) (sourceB833 + difference 2 4) sourceC833) = raw13755 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13755; decide +kernel
    rw [ha]
    exact (canonical13755 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA833 + difference 4 3) (sourceB833 + difference 3 4) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA833 + difference 4 3) (sourceB833 + difference 3 4) sourceC833) = raw13756 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13756; decide +kernel
    rw [ha]
    exact (canonical13756 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA833 + difference 4 5) (sourceB833 + difference 5 4) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA833 + difference 4 5) (sourceB833 + difference 5 4) sourceC833) = raw13757 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13757; decide +kernel
    rw [ha]
    exact (canonical13757 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA833 + difference 5 0) (sourceB833 + difference 0 5) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA833 + difference 5 0) (sourceB833 + difference 0 5) sourceC833) = raw13758 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13758; decide +kernel
    rw [ha]
    exact (canonical13758 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA833 + difference 5 1) (sourceB833 + difference 1 5) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3537) := by
    have ha : (tripleCharges (sourceA833 + difference 5 1) (sourceB833 + difference 1 5) sourceC833) = raw13759 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13759; decide +kernel
    rw [ha]
    exact (canonical13759 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA833 + difference 5 2) (sourceB833 + difference 2 5) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3477) := by
    have ha : (tripleCharges (sourceA833 + difference 5 2) (sourceB833 + difference 2 5) sourceC833) = raw13760 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13760; decide +kernel
    rw [ha]
    exact (canonical13760 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA833 + difference 5 3) (sourceB833 + difference 3 5) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA833 + difference 5 3) (sourceB833 + difference 3 5) sourceC833) = raw13761 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13761; decide +kernel
    rw [ha]
    exact (canonical13761 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA833 + difference 5 4) (sourceB833 + difference 4 5) sourceC833) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA833 + difference 5 4) (sourceB833 + difference 4 5) sourceC833) = raw13762 := by
      apply Matrix.ext; unfold tripleCharges sourceA833 sourceB833 sourceC833 difference raw13762; decide +kernel
    rw [ha]
    exact (canonical13762 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA833 sourceB833 sourceC833
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm833, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq834 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm834 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA834 + difference 1 0) (sourceB834 + difference 0 1) sourceC834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1235) := by
    have ha : (tripleCharges (sourceA834 + difference 1 0) (sourceB834 + difference 0 1) sourceC834) = raw13763 := by
      apply Matrix.ext; unfold tripleCharges sourceA834 sourceB834 sourceC834 difference raw13763; decide +kernel
    rw [ha]
    exact (canonical13763 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA834 + difference 1 1) (sourceB834 + difference 1 1) sourceC834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA834 + difference 1 1) (sourceB834 + difference 1 1) sourceC834) = raw13764 := by
      apply Matrix.ext; unfold tripleCharges sourceA834 sourceB834 sourceC834 difference raw13764; decide +kernel
    rw [ha]
    exact (canonical13764 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA834 + difference 1 2) (sourceB834 + difference 2 1) sourceC834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2510) := by
    have ha : (tripleCharges (sourceA834 + difference 1 2) (sourceB834 + difference 2 1) sourceC834) = raw13765 := by
      apply Matrix.ext; unfold tripleCharges sourceA834 sourceB834 sourceC834 difference raw13765; decide +kernel
    rw [ha]
    exact (canonical13765 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA834 + difference 1 3) (sourceB834 + difference 3 1) sourceC834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA834 + difference 1 3) (sourceB834 + difference 3 1) sourceC834) = raw13766 := by
      apply Matrix.ext; unfold tripleCharges sourceA834 sourceB834 sourceC834 difference raw13766; decide +kernel
    rw [ha]
    exact (canonical13766 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA834 + difference 1 4) (sourceB834 + difference 4 1) sourceC834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA834 + difference 1 4) (sourceB834 + difference 4 1) sourceC834) = raw13767 := by
      apply Matrix.ext; unfold tripleCharges sourceA834 sourceB834 sourceC834 difference raw13767; decide +kernel
    rw [ha]
    exact (canonical13767 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA834 + difference 1 5) (sourceB834 + difference 5 1) sourceC834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2741) := by
    have ha : (tripleCharges (sourceA834 + difference 1 5) (sourceB834 + difference 5 1) sourceC834) = raw13768 := by
      apply Matrix.ext; unfold tripleCharges sourceA834 sourceB834 sourceC834 difference raw13768; decide +kernel
    rw [ha]
    exact (canonical13768 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA834 + sourceB834) sourceC834) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA834 + sourceB834) sourceC834) = raw13769 := by
      apply Matrix.ext; unfold doubleCharges sourceA834 sourceB834 sourceC834 raw13769; decide +kernel
    rw [ha]
    exact (canonical13769 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA834 sourceB834 sourceC834
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm834, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq835 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm835 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA835 + difference 0 1) (sourceB835 + difference 1 0) sourceC835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA835 + difference 0 1) (sourceB835 + difference 1 0) sourceC835) = raw13770 := by
      apply Matrix.ext; unfold tripleCharges sourceA835 sourceB835 sourceC835 difference raw13770; decide +kernel
    rw [ha]
    exact (canonical13770 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA835 + difference 1 1) (sourceB835 + difference 1 1) sourceC835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA835 + difference 1 1) (sourceB835 + difference 1 1) sourceC835) = raw13764 := by
      apply Matrix.ext; unfold tripleCharges sourceA835 sourceB835 sourceC835 difference raw13764; decide +kernel
    rw [ha]
    exact (canonical13764 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA835 + difference 2 1) (sourceB835 + difference 1 2) sourceC835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2631) := by
    have ha : (tripleCharges (sourceA835 + difference 2 1) (sourceB835 + difference 1 2) sourceC835) = raw13771 := by
      apply Matrix.ext; unfold tripleCharges sourceA835 sourceB835 sourceC835 difference raw13771; decide +kernel
    rw [ha]
    exact (canonical13771 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA835 + difference 3 1) (sourceB835 + difference 1 3) sourceC835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2615) := by
    have ha : (tripleCharges (sourceA835 + difference 3 1) (sourceB835 + difference 1 3) sourceC835) = raw13772 := by
      apply Matrix.ext; unfold tripleCharges sourceA835 sourceB835 sourceC835 difference raw13772; decide +kernel
    rw [ha]
    exact (canonical13772 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA835 + difference 4 1) (sourceB835 + difference 1 4) sourceC835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2615) := by
    have ha : (tripleCharges (sourceA835 + difference 4 1) (sourceB835 + difference 1 4) sourceC835) = raw13773 := by
      apply Matrix.ext; unfold tripleCharges sourceA835 sourceB835 sourceC835 difference raw13773; decide +kernel
    rw [ha]
    exact (canonical13773 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA835 + difference 5 1) (sourceB835 + difference 1 5) sourceC835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2617) := by
    have ha : (tripleCharges (sourceA835 + difference 5 1) (sourceB835 + difference 1 5) sourceC835) = raw13774 := by
      apply Matrix.ext; unfold tripleCharges sourceA835 sourceB835 sourceC835 difference raw13774; decide +kernel
    rw [ha]
    exact (canonical13774 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA835 + sourceB835) sourceC835) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA835 + sourceB835) sourceC835) = raw13769 := by
      apply Matrix.ext; unfold doubleCharges sourceA835 sourceB835 sourceC835 raw13769; decide +kernel
    rw [ha]
    exact (canonical13769 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA835 sourceB835 sourceC835
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm835, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq838 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm838 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA838 + difference 0 1) (sourceB838 + difference 1 0) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA838 + difference 0 1) (sourceB838 + difference 1 0) sourceC838) = raw13835 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13835; decide +kernel
    rw [ha]
    exact (canonical13835 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA838 + difference 0 2) (sourceB838 + difference 2 0) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA838 + difference 0 2) (sourceB838 + difference 2 0) sourceC838) = raw13836 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13836; decide +kernel
    rw [ha]
    exact (canonical13836 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA838 + difference 0 3) (sourceB838 + difference 3 0) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA838 + difference 0 3) (sourceB838 + difference 3 0) sourceC838) = raw13837 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13837; decide +kernel
    rw [ha]
    exact (canonical13837 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA838 + difference 0 4) (sourceB838 + difference 4 0) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA838 + difference 0 4) (sourceB838 + difference 4 0) sourceC838) = raw13838 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13838; decide +kernel
    rw [ha]
    exact (canonical13838 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA838 + difference 0 5) (sourceB838 + difference 5 0) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA838 + difference 0 5) (sourceB838 + difference 5 0) sourceC838) = raw13618 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13618; decide +kernel
    rw [ha]
    exact (canonical13618 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA838 + difference 1 0) (sourceB838 + difference 0 1) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA838 + difference 1 0) (sourceB838 + difference 0 1) sourceC838) = raw13839 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13839; decide +kernel
    rw [ha]
    exact (canonical13839 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA838 + difference 1 2) (sourceB838 + difference 2 1) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA838 + difference 1 2) (sourceB838 + difference 2 1) sourceC838) = raw13840 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13840; decide +kernel
    rw [ha]
    exact (canonical13840 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA838 + difference 1 3) (sourceB838 + difference 3 1) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA838 + difference 1 3) (sourceB838 + difference 3 1) sourceC838) = raw13841 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13841; decide +kernel
    rw [ha]
    exact (canonical13841 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA838 + difference 1 4) (sourceB838 + difference 4 1) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA838 + difference 1 4) (sourceB838 + difference 4 1) sourceC838) = raw13842 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13842; decide +kernel
    rw [ha]
    exact (canonical13842 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA838 + difference 1 5) (sourceB838 + difference 5 1) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5263) := by
    have ha : (tripleCharges (sourceA838 + difference 1 5) (sourceB838 + difference 5 1) sourceC838) = raw13623 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13623; decide +kernel
    rw [ha]
    exact (canonical13623 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA838 + difference 2 0) (sourceB838 + difference 0 2) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA838 + difference 2 0) (sourceB838 + difference 0 2) sourceC838) = raw13640 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13640; decide +kernel
    rw [ha]
    exact (canonical13640 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA838 + difference 2 1) (sourceB838 + difference 1 2) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA838 + difference 2 1) (sourceB838 + difference 1 2) sourceC838) = raw13641 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13641; decide +kernel
    rw [ha]
    exact (canonical13641 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA838 + difference 2 3) (sourceB838 + difference 3 2) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA838 + difference 2 3) (sourceB838 + difference 3 2) sourceC838) = raw13447 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13447; decide +kernel
    rw [ha]
    exact (canonical13447 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA838 + difference 2 4) (sourceB838 + difference 4 2) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA838 + difference 2 4) (sourceB838 + difference 4 2) sourceC838) = raw13443 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13443; decide +kernel
    rw [ha]
    exact (canonical13443 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA838 + difference 2 5) (sourceB838 + difference 5 2) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA838 + difference 2 5) (sourceB838 + difference 5 2) sourceC838) = raw13843 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13843; decide +kernel
    rw [ha]
    exact (canonical13843 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA838 + difference 3 0) (sourceB838 + difference 0 3) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA838 + difference 3 0) (sourceB838 + difference 0 3) sourceC838) = raw13844 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13844; decide +kernel
    rw [ha]
    exact (canonical13844 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA838 + difference 3 1) (sourceB838 + difference 1 3) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA838 + difference 3 1) (sourceB838 + difference 1 3) sourceC838) = raw13845 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13845; decide +kernel
    rw [ha]
    exact (canonical13845 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA838 + difference 3 2) (sourceB838 + difference 2 3) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA838 + difference 3 2) (sourceB838 + difference 2 3) sourceC838) = raw13846 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13846; decide +kernel
    rw [ha]
    exact (canonical13846 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA838 + difference 3 4) (sourceB838 + difference 4 3) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA838 + difference 3 4) (sourceB838 + difference 4 3) sourceC838) = raw13847 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13847; decide +kernel
    rw [ha]
    exact (canonical13847 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA838 + difference 3 5) (sourceB838 + difference 5 3) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA838 + difference 3 5) (sourceB838 + difference 5 3) sourceC838) = raw13632 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13632; decide +kernel
    rw [ha]
    exact (canonical13632 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA838 + difference 4 0) (sourceB838 + difference 0 4) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA838 + difference 4 0) (sourceB838 + difference 0 4) sourceC838) = raw13848 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13848; decide +kernel
    rw [ha]
    exact (canonical13848 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA838 + difference 4 1) (sourceB838 + difference 1 4) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA838 + difference 4 1) (sourceB838 + difference 1 4) sourceC838) = raw13849 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13849; decide +kernel
    rw [ha]
    exact (canonical13849 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA838 + difference 4 2) (sourceB838 + difference 2 4) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA838 + difference 4 2) (sourceB838 + difference 2 4) sourceC838) = raw13850 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13850; decide +kernel
    rw [ha]
    exact (canonical13850 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA838 + difference 4 3) (sourceB838 + difference 3 4) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA838 + difference 4 3) (sourceB838 + difference 3 4) sourceC838) = raw13851 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13851; decide +kernel
    rw [ha]
    exact (canonical13851 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA838 + difference 4 5) (sourceB838 + difference 5 4) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA838 + difference 4 5) (sourceB838 + difference 5 4) sourceC838) = raw13637 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13637; decide +kernel
    rw [ha]
    exact (canonical13637 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA838 + difference 5 0) (sourceB838 + difference 0 5) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA838 + difference 5 0) (sourceB838 + difference 0 5) sourceC838) = raw13852 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13852; decide +kernel
    rw [ha]
    exact (canonical13852 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA838 + difference 5 1) (sourceB838 + difference 1 5) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA838 + difference 5 1) (sourceB838 + difference 1 5) sourceC838) = raw13853 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13853; decide +kernel
    rw [ha]
    exact (canonical13853 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA838 + difference 5 2) (sourceB838 + difference 2 5) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5227) := by
    have ha : (tripleCharges (sourceA838 + difference 5 2) (sourceB838 + difference 2 5) sourceC838) = raw13854 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13854; decide +kernel
    rw [ha]
    exact (canonical13854 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA838 + difference 5 3) (sourceB838 + difference 3 5) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA838 + difference 5 3) (sourceB838 + difference 3 5) sourceC838) = raw13855 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13855; decide +kernel
    rw [ha]
    exact (canonical13855 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA838 + difference 5 4) (sourceB838 + difference 4 5) sourceC838) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA838 + difference 5 4) (sourceB838 + difference 4 5) sourceC838) = raw13856 := by
      apply Matrix.ext; unfold tripleCharges sourceA838 sourceB838 sourceC838 difference raw13856; decide +kernel
    rw [ha]
    exact (canonical13856 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA838 sourceB838 sourceC838
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm838, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq839 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm839 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA839 + difference 0 1) (sourceB839 + difference 1 0) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA839 + difference 0 1) (sourceB839 + difference 1 0) sourceC839) = raw13857 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13857; decide +kernel
    rw [ha]
    exact (canonical13857 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA839 + difference 0 2) (sourceB839 + difference 2 0) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA839 + difference 0 2) (sourceB839 + difference 2 0) sourceC839) = raw13858 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13858; decide +kernel
    rw [ha]
    exact (canonical13858 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA839 + difference 0 3) (sourceB839 + difference 3 0) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA839 + difference 0 3) (sourceB839 + difference 3 0) sourceC839) = raw13859 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13859; decide +kernel
    rw [ha]
    exact (canonical13859 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA839 + difference 0 4) (sourceB839 + difference 4 0) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA839 + difference 0 4) (sourceB839 + difference 4 0) sourceC839) = raw13860 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13860; decide +kernel
    rw [ha]
    exact (canonical13860 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA839 + difference 0 5) (sourceB839 + difference 5 0) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3085) := by
    have ha : (tripleCharges (sourceA839 + difference 0 5) (sourceB839 + difference 5 0) sourceC839) = raw13644 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13644; decide +kernel
    rw [ha]
    exact (canonical13644 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA839 + difference 1 0) (sourceB839 + difference 0 1) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA839 + difference 1 0) (sourceB839 + difference 0 1) sourceC839) = raw13861 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13861; decide +kernel
    rw [ha]
    exact (canonical13861 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA839 + difference 1 2) (sourceB839 + difference 2 1) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2676) := by
    have ha : (tripleCharges (sourceA839 + difference 1 2) (sourceB839 + difference 2 1) sourceC839) = raw13862 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13862; decide +kernel
    rw [ha]
    exact (canonical13862 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA839 + difference 1 3) (sourceB839 + difference 3 1) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA839 + difference 1 3) (sourceB839 + difference 3 1) sourceC839) = raw13863 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13863; decide +kernel
    rw [ha]
    exact (canonical13863 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA839 + difference 1 4) (sourceB839 + difference 4 1) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA839 + difference 1 4) (sourceB839 + difference 4 1) sourceC839) = raw13864 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13864; decide +kernel
    rw [ha]
    exact (canonical13864 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA839 + difference 1 5) (sourceB839 + difference 5 1) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2728) := by
    have ha : (tripleCharges (sourceA839 + difference 1 5) (sourceB839 + difference 5 1) sourceC839) = raw13649 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13649; decide +kernel
    rw [ha]
    exact (canonical13649 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA839 + difference 2 0) (sourceB839 + difference 0 2) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA839 + difference 2 0) (sourceB839 + difference 0 2) sourceC839) = raw13668 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13668; decide +kernel
    rw [ha]
    exact (canonical13668 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA839 + difference 2 1) (sourceB839 + difference 1 2) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2785) := by
    have ha : (tripleCharges (sourceA839 + difference 2 1) (sourceB839 + difference 1 2) sourceC839) = raw13669 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13669; decide +kernel
    rw [ha]
    exact (canonical13669 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA839 + difference 2 3) (sourceB839 + difference 3 2) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA839 + difference 2 3) (sourceB839 + difference 3 2) sourceC839) = raw13671 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13671; decide +kernel
    rw [ha]
    exact (canonical13671 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA839 + difference 2 4) (sourceB839 + difference 4 2) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA839 + difference 2 4) (sourceB839 + difference 4 2) sourceC839) = raw13672 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13672; decide +kernel
    rw [ha]
    exact (canonical13672 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA839 + difference 2 5) (sourceB839 + difference 5 2) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA839 + difference 2 5) (sourceB839 + difference 5 2) sourceC839) = raw13865 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13865; decide +kernel
    rw [ha]
    exact (canonical13865 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA839 + difference 3 0) (sourceB839 + difference 0 3) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA839 + difference 3 0) (sourceB839 + difference 0 3) sourceC839) = raw13866 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13866; decide +kernel
    rw [ha]
    exact (canonical13866 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA839 + difference 3 1) (sourceB839 + difference 1 3) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA839 + difference 3 1) (sourceB839 + difference 1 3) sourceC839) = raw13867 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13867; decide +kernel
    rw [ha]
    exact (canonical13867 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA839 + difference 3 2) (sourceB839 + difference 2 3) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA839 + difference 3 2) (sourceB839 + difference 2 3) sourceC839) = raw13868 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13868; decide +kernel
    rw [ha]
    exact (canonical13868 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA839 + difference 3 4) (sourceB839 + difference 4 3) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA839 + difference 3 4) (sourceB839 + difference 4 3) sourceC839) = raw13869 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13869; decide +kernel
    rw [ha]
    exact (canonical13869 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA839 + difference 3 5) (sourceB839 + difference 5 3) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA839 + difference 3 5) (sourceB839 + difference 5 3) sourceC839) = raw13660 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13660; decide +kernel
    rw [ha]
    exact (canonical13660 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA839 + difference 4 0) (sourceB839 + difference 0 4) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA839 + difference 4 0) (sourceB839 + difference 0 4) sourceC839) = raw13870 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13870; decide +kernel
    rw [ha]
    exact (canonical13870 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA839 + difference 4 1) (sourceB839 + difference 1 4) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA839 + difference 4 1) (sourceB839 + difference 1 4) sourceC839) = raw13871 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13871; decide +kernel
    rw [ha]
    exact (canonical13871 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA839 + difference 4 2) (sourceB839 + difference 2 4) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA839 + difference 4 2) (sourceB839 + difference 2 4) sourceC839) = raw13872 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13872; decide +kernel
    rw [ha]
    exact (canonical13872 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA839 + difference 4 3) (sourceB839 + difference 3 4) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA839 + difference 4 3) (sourceB839 + difference 3 4) sourceC839) = raw13873 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13873; decide +kernel
    rw [ha]
    exact (canonical13873 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA839 + difference 4 5) (sourceB839 + difference 5 4) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA839 + difference 4 5) (sourceB839 + difference 5 4) sourceC839) = raw13665 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13665; decide +kernel
    rw [ha]
    exact (canonical13665 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA839 + difference 5 0) (sourceB839 + difference 0 5) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2204) := by
    have ha : (tripleCharges (sourceA839 + difference 5 0) (sourceB839 + difference 0 5) sourceC839) = raw13874 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13874; decide +kernel
    rw [ha]
    exact (canonical13874 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA839 + difference 5 1) (sourceB839 + difference 1 5) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2741) := by
    have ha : (tripleCharges (sourceA839 + difference 5 1) (sourceB839 + difference 1 5) sourceC839) = raw13875 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13875; decide +kernel
    rw [ha]
    exact (canonical13875 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA839 + difference 5 2) (sourceB839 + difference 2 5) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA839 + difference 5 2) (sourceB839 + difference 2 5) sourceC839) = raw13876 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13876; decide +kernel
    rw [ha]
    exact (canonical13876 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA839 + difference 5 3) (sourceB839 + difference 3 5) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA839 + difference 5 3) (sourceB839 + difference 3 5) sourceC839) = raw13877 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13877; decide +kernel
    rw [ha]
    exact (canonical13877 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA839 + difference 5 4) (sourceB839 + difference 4 5) sourceC839) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA839 + difference 5 4) (sourceB839 + difference 4 5) sourceC839) = raw13878 := by
      apply Matrix.ext; unfold tripleCharges sourceA839 sourceB839 sourceC839 difference raw13878; decide +kernel
    rw [ha]
    exact (canonical13878 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA839 sourceB839 sourceC839
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm839, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck721 : Integer.Sparse.reindex keyMap MixedData.row721 = numericRow721 := by decide +kernel

theorem numericCheck721 (x : Master → ℝ) : Integer.Sparse.eval numericRow721 x =
    (8640 : ℝ) * reducedSource721 x := by
  norm_num [numericRow721, reducedSource721, Integer.Sparse.eval, Sparse.eval, nodeValue4589, nodeValue4590, nodeValue4599, nodeValue4601, nodeValue5073, nodeValue5076, nodeValue5100, nodeValue5185, nodeValue5187, nodeValue5197, nodeValue5250, nodeValue5251, nodeValue5257, nodeValue5259, nodeValue5273, nodeValue5281, nodeValue5290, nodeValue5408, nodeValue5431, nodeValue5433, nodeValue5440]
  ring

theorem reindexCheck723 : Integer.Sparse.reindex keyMap MixedData.row723 = numericRow723 := by decide +kernel

theorem numericCheck723 (x : Master → ℝ) : Integer.Sparse.eval numericRow723 x =
    (2160 : ℝ) * reducedSource723 x := by
  norm_num [numericRow723, reducedSource723, Integer.Sparse.eval, Sparse.eval, nodeValue3288, nodeValue3289, nodeValue3290, nodeValue3292, nodeValue3467, nodeValue3469, nodeValue3477, nodeValue3529, nodeValue3531, nodeValue3532, nodeValue3537, nodeValue3539, nodeValue3544, nodeValue3546, nodeValue3569, nodeValue3571, nodeValue3581, nodeValue3806, nodeValue3849, nodeValue3851, nodeValue3859]
  ring

theorem reindexCheck724 : Integer.Sparse.reindex keyMap MixedData.row724 = numericRow724 := by decide +kernel

theorem numericCheck724 (x : Master → ℝ) : Integer.Sparse.eval numericRow724 x =
    (1 : ℝ) * reducedSource724 x := by
  norm_num [numericRow724, reducedSource724, Integer.Sparse.eval, Sparse.eval, nodeValue1235, nodeValue2510, nodeValue2721, nodeValue2741, nodeValue4091]

theorem reindexCheck725 : Integer.Sparse.reindex keyMap MixedData.row725 = numericRow725 := by decide +kernel

theorem numericCheck725 (x : Master → ℝ) : Integer.Sparse.eval numericRow725 x =
    (1 : ℝ) * reducedSource725 x := by
  norm_num [numericRow725, reducedSource725, Integer.Sparse.eval, Sparse.eval, nodeValue2615, nodeValue2617, nodeValue2631, nodeValue2721, nodeValue3875, nodeValue4091]

theorem reindexCheck728 : Integer.Sparse.reindex keyMap MixedData.row728 = numericRow728 := by decide +kernel

theorem numericCheck728 (x : Master → ℝ) : Integer.Sparse.eval numericRow728 x =
    (5760 : ℝ) * reducedSource728 x := by
  norm_num [numericRow728, reducedSource728, Integer.Sparse.eval, Sparse.eval, nodeValue4802, nodeValue4805, nodeValue4833, nodeValue4893, nodeValue5226, nodeValue5227, nodeValue5231, nodeValue5255, nodeValue5256, nodeValue5257, nodeValue5263, nodeValue5265, nodeValue5271, nodeValue5273, nodeValue5290, nodeValue5292, nodeValue5307]
  ring

theorem reindexCheck729 : Integer.Sparse.reindex keyMap MixedData.row729 = numericRow729 := by decide +kernel

theorem numericCheck729 (x : Master → ℝ) : Integer.Sparse.eval numericRow729 x =
    (4320 : ℝ) * reducedSource729 x := by
  norm_num [numericRow729, reducedSource729, Integer.Sparse.eval, Sparse.eval, nodeValue2202, nodeValue2204, nodeValue2214, nodeValue2263, nodeValue2669, nodeValue2671, nodeValue2676, nodeValue2718, nodeValue2720, nodeValue2721, nodeValue2728, nodeValue2730, nodeValue2739, nodeValue2741, nodeValue2764, nodeValue2766, nodeValue2785, nodeValue3037, nodeValue3085, nodeValue3087, nodeValue3100]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero721 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource721 (mixedVector B) = 0 := by
  have h4589 : mixedVector B (Sum.inr 4589) = Sparse.eval nodeValue4589 (mixedVector B) := by
    change mixedMoment B node4589 node4589Labels = _
    exact sound4589 B hB hF
  have h4590 : mixedVector B (Sum.inr 4590) = Sparse.eval nodeValue4590 (mixedVector B) := by
    change mixedMoment B node4590 node4590Labels = _
    exact sound4590 B hB hF
  have h4599 : mixedVector B (Sum.inr 4599) = Sparse.eval nodeValue4599 (mixedVector B) := by
    change mixedMoment B node4599 node4599Labels = _
    exact sound4599 B hB hF
  have h4601 : mixedVector B (Sum.inr 4601) = Sparse.eval nodeValue4601 (mixedVector B) := by
    change mixedMoment B node4601 node4601Labels = _
    exact sound4601 B hB hF
  have h5073 : mixedVector B (Sum.inr 5073) = Sparse.eval nodeValue5073 (mixedVector B) := by
    change mixedMoment B node5073 node5073Labels = _
    exact sound5073 B hB hF
  have h5076 : mixedVector B (Sum.inr 5076) = Sparse.eval nodeValue5076 (mixedVector B) := by
    change mixedMoment B node5076 node5076Labels = _
    exact sound5076 B hB hF
  have h5100 : mixedVector B (Sum.inr 5100) = Sparse.eval nodeValue5100 (mixedVector B) := by
    change mixedMoment B node5100 node5100Labels = _
    exact sound5100 B hB hF
  have h5185 : mixedVector B (Sum.inr 5185) = Sparse.eval nodeValue5185 (mixedVector B) := by
    change mixedMoment B node5185 node5185Labels = _
    exact sound5185 B hB hF
  have h5187 : mixedVector B (Sum.inr 5187) = Sparse.eval nodeValue5187 (mixedVector B) := by
    change mixedMoment B node5187 node5187Labels = _
    exact sound5187 B hB hF
  have h5197 : mixedVector B (Sum.inr 5197) = Sparse.eval nodeValue5197 (mixedVector B) := by
    change mixedMoment B node5197 node5197Labels = _
    exact sound5197 B hB hF
  have h5250 : mixedVector B (Sum.inr 5250) = Sparse.eval nodeValue5250 (mixedVector B) := by
    change mixedMoment B node5250 node5250Labels = _
    exact sound5250 B hB hF
  have h5251 : mixedVector B (Sum.inr 5251) = Sparse.eval nodeValue5251 (mixedVector B) := by
    change mixedMoment B node5251 node5251Labels = _
    exact sound5251 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5273 : mixedVector B (Sum.inr 5273) = Sparse.eval nodeValue5273 (mixedVector B) := by
    change mixedMoment B node5273 node5273Labels = _
    exact sound5273 B hB hF
  have h5281 : mixedVector B (Sum.inr 5281) = Sparse.eval nodeValue5281 (mixedVector B) := by
    change mixedMoment B node5281 node5281Labels = _
    exact sound5281 B hB hF
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  have h5408 : mixedVector B (Sum.inr 5408) = Sparse.eval nodeValue5408 (mixedVector B) := by
    change mixedMoment B node5408 node5408Labels = _
    exact sound5408 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433_e B hB hF
  have h5440 : mixedVector B (Sum.inr 5440) = Sparse.eval nodeValue5440 (mixedVector B) := by
    change mixedMoment B node5440 node5440Labels = _
    exact sound5440 B hB hF
  simpa only [sourceForm831, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4589, h4590, h4599, h4601, h5073, h5076, h5100, h5185, h5187, h5197, h5250, h5251, h5257, h5259, h5273, h5281, h5290, h5408, h5431, h5433, h5440, reducedSource721] using sourceEq831 B hB

theorem rowSound721 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row721 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck721, numericCheck721, reducedZero721 B hB hF, mul_zero]

theorem reducedZero723 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource723 (mixedVector B) = 0 := by
  have h3288 : mixedVector B (Sum.inr 3288) = Sparse.eval nodeValue3288 (mixedVector B) := by
    change mixedMoment B node3288 node3288Labels = _
    exact sound3288 B hB hF
  have h3289 : mixedVector B (Sum.inr 3289) = Sparse.eval nodeValue3289 (mixedVector B) := by
    change mixedMoment B node3289 node3289Labels = _
    exact sound3289 B hB hF
  have h3290 : mixedVector B (Sum.inr 3290) = Sparse.eval nodeValue3290 (mixedVector B) := by
    change mixedMoment B node3290 node3290Labels = _
    exact sound3290 B hB hF
  have h3292 : mixedVector B (Sum.inr 3292) = Sparse.eval nodeValue3292 (mixedVector B) := by
    change mixedMoment B node3292 node3292Labels = _
    exact sound3292 B hB hF
  have h3467 : mixedVector B (Sum.inr 3467) = Sparse.eval nodeValue3467 (mixedVector B) := by
    change mixedMoment B node3467 node3467Labels = _
    exact sound3467 B hB hF
  have h3469 : mixedVector B (Sum.inr 3469) = Sparse.eval nodeValue3469 (mixedVector B) := by
    change mixedMoment B node3469 node3469Labels = _
    exact sound3469 B hB hF
  have h3477 : mixedVector B (Sum.inr 3477) = Sparse.eval nodeValue3477 (mixedVector B) := by
    change mixedMoment B node3477 node3477Labels = _
    exact sound3477 B hB hF
  have h3529 : mixedVector B (Sum.inr 3529) = Sparse.eval nodeValue3529 (mixedVector B) := by
    change mixedMoment B node3529 node3529Labels = _
    exact sound3529 B hB hF
  have h3531 : mixedVector B (Sum.inr 3531) = Sparse.eval nodeValue3531 (mixedVector B) := by
    change mixedMoment B node3531 node3531Labels = _
    exact sound3531 B hB hF
  have h3532 : mixedVector B (Sum.inr 3532) = Sparse.eval nodeValue3532 (mixedVector B) := by
    change mixedMoment B node3532 node3532Labels = _
    exact sound3532 B hB hF
  have h3537 : mixedVector B (Sum.inr 3537) = Sparse.eval nodeValue3537 (mixedVector B) := by
    change mixedMoment B node3537 node3537Labels = _
    exact sound3537 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h3546 : mixedVector B (Sum.inr 3546) = Sparse.eval nodeValue3546 (mixedVector B) := by
    change mixedMoment B node3546 node3546Labels = _
    exact sound3546 B hB hF
  have h3569 : mixedVector B (Sum.inr 3569) = Sparse.eval nodeValue3569 (mixedVector B) := by
    change mixedMoment B node3569 node3569Labels = _
    exact sound3569 B hB hF
  have h3571 : mixedVector B (Sum.inr 3571) = Sparse.eval nodeValue3571 (mixedVector B) := by
    change mixedMoment B node3571 node3571Labels = _
    exact sound3571 B hB hF
  have h3581 : mixedVector B (Sum.inr 3581) = Sparse.eval nodeValue3581 (mixedVector B) := by
    change mixedMoment B node3581 node3581Labels = _
    exact sound3581 B hB hF
  have h3806 : mixedVector B (Sum.inr 3806) = Sparse.eval nodeValue3806 (mixedVector B) := by
    change mixedMoment B node3806 node3806Labels = _
    exact sound3806 B hB hF
  have h3849 : mixedVector B (Sum.inr 3849) = Sparse.eval nodeValue3849 (mixedVector B) := by
    change mixedMoment B node3849 node3849Labels = _
    exact sound3849 B hB hF
  have h3851 : mixedVector B (Sum.inr 3851) = Sparse.eval nodeValue3851 (mixedVector B) := by
    change mixedMoment B node3851 node3851Labels = _
    exact sound3851_e B hB hF
  have h3859 : mixedVector B (Sum.inr 3859) = Sparse.eval nodeValue3859 (mixedVector B) := by
    change mixedMoment B node3859 node3859Labels = _
    exact sound3859 B hB hF
  simpa only [sourceForm833, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3288, h3289, h3290, h3292, h3467, h3469, h3477, h3529, h3531, h3532, h3537, h3539, h3544, h3546, h3569, h3571, h3581, h3806, h3849, h3851, h3859, reducedSource723] using sourceEq833 B hB

theorem rowSound723 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row723 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck723, numericCheck723, reducedZero723 B hB hF, mul_zero]

theorem reducedZero724 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource724 (mixedVector B) = 0 := by
  have h1235 : mixedVector B (Sum.inr 1235) = Sparse.eval nodeValue1235 (mixedVector B) := by
    change mixedMoment B node1235 node1235Labels = _
    exact sound1235 B hB hF
  have h2510 : mixedVector B (Sum.inr 2510) = Sparse.eval nodeValue2510 (mixedVector B) := by
    change mixedMoment B node2510 node2510Labels = _
    exact sound2510 B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h2741 : mixedVector B (Sum.inr 2741) = Sparse.eval nodeValue2741 (mixedVector B) := by
    change mixedMoment B node2741 node2741Labels = _
    exact sound2741 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm834, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1235, h2510, h2721, h2741, h4091, reducedSource724] using sourceEq834 B hB

theorem rowSound724 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row724 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck724, numericCheck724, reducedZero724 B hB hF, mul_zero]

theorem reducedZero725 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource725 (mixedVector B) = 0 := by
  have h2615 : mixedVector B (Sum.inr 2615) = Sparse.eval nodeValue2615 (mixedVector B) := by
    change mixedMoment B node2615 node2615Labels = _
    exact sound2615 B hB hF
  have h2617 : mixedVector B (Sum.inr 2617) = Sparse.eval nodeValue2617 (mixedVector B) := by
    change mixedMoment B node2617 node2617Labels = _
    exact sound2617 B hB hF
  have h2631 : mixedVector B (Sum.inr 2631) = Sparse.eval nodeValue2631 (mixedVector B) := by
    change mixedMoment B node2631 node2631Labels = _
    exact sound2631 B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h3875 : mixedVector B (Sum.inr 3875) = Sparse.eval nodeValue3875 (mixedVector B) := by
    change mixedMoment B node3875 node3875Labels = _
    exact sound3875 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm835, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2615, h2617, h2631, h2721, h3875, h4091, reducedSource725] using sourceEq835 B hB

theorem rowSound725 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row725 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck725, numericCheck725, reducedZero725 B hB hF, mul_zero]

theorem reducedZero728 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource728 (mixedVector B) = 0 := by
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4833 : mixedVector B (Sum.inr 4833) = Sparse.eval nodeValue4833 (mixedVector B) := by
    change mixedMoment B node4833 node4833Labels = _
    exact sound4833 B hB hF
  have h4893 : mixedVector B (Sum.inr 4893) = Sparse.eval nodeValue4893 (mixedVector B) := by
    change mixedMoment B node4893 node4893Labels = _
    exact sound4893 B hB hF
  have h5226 : mixedVector B (Sum.inr 5226) = Sparse.eval nodeValue5226 (mixedVector B) := by
    change mixedMoment B node5226 node5226Labels = _
    exact sound5226 B hB hF
  have h5227 : mixedVector B (Sum.inr 5227) = Sparse.eval nodeValue5227 (mixedVector B) := by
    change mixedMoment B node5227 node5227Labels = _
    exact sound5227 B hB hF
  have h5231 : mixedVector B (Sum.inr 5231) = Sparse.eval nodeValue5231 (mixedVector B) := by
    change mixedMoment B node5231 node5231Labels = _
    exact sound5231 B hB hF
  have h5255 : mixedVector B (Sum.inr 5255) = Sparse.eval nodeValue5255 (mixedVector B) := by
    change mixedMoment B node5255 node5255Labels = _
    exact sound5255 B hB hF
  have h5256 : mixedVector B (Sum.inr 5256) = Sparse.eval nodeValue5256 (mixedVector B) := by
    change mixedMoment B node5256 node5256Labels = _
    exact sound5256 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5263 : mixedVector B (Sum.inr 5263) = Sparse.eval nodeValue5263 (mixedVector B) := by
    change mixedMoment B node5263 node5263Labels = _
    exact sound5263 B hB hF
  have h5265 : mixedVector B (Sum.inr 5265) = Sparse.eval nodeValue5265 (mixedVector B) := by
    change mixedMoment B node5265 node5265Labels = _
    exact sound5265 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  have h5273 : mixedVector B (Sum.inr 5273) = Sparse.eval nodeValue5273 (mixedVector B) := by
    change mixedMoment B node5273 node5273Labels = _
    exact sound5273 B hB hF
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292_e B hB hF
  have h5307 : mixedVector B (Sum.inr 5307) = Sparse.eval nodeValue5307 (mixedVector B) := by
    change mixedMoment B node5307 node5307Labels = _
    exact sound5307 B hB hF
  simpa only [sourceForm838, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4802, h4805, h4833, h4893, h5226, h5227, h5231, h5255, h5256, h5257, h5263, h5265, h5271, h5273, h5290, h5292, h5307, reducedSource728] using sourceEq838 B hB

theorem rowSound728 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row728 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck728, numericCheck728, reducedZero728 B hB hF, mul_zero]

theorem reducedZero729 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource729 (mixedVector B) = 0 := by
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h2204 : mixedVector B (Sum.inr 2204) = Sparse.eval nodeValue2204 (mixedVector B) := by
    change mixedMoment B node2204 node2204Labels = _
    exact sound2204 B hB hF
  have h2214 : mixedVector B (Sum.inr 2214) = Sparse.eval nodeValue2214 (mixedVector B) := by
    change mixedMoment B node2214 node2214Labels = _
    exact sound2214 B hB hF
  have h2263 : mixedVector B (Sum.inr 2263) = Sparse.eval nodeValue2263 (mixedVector B) := by
    change mixedMoment B node2263 node2263Labels = _
    exact sound2263 B hB hF
  have h2669 : mixedVector B (Sum.inr 2669) = Sparse.eval nodeValue2669 (mixedVector B) := by
    change mixedMoment B node2669 node2669Labels = _
    exact sound2669 B hB hF
  have h2671 : mixedVector B (Sum.inr 2671) = Sparse.eval nodeValue2671 (mixedVector B) := by
    change mixedMoment B node2671 node2671Labels = _
    exact sound2671 B hB hF
  have h2676 : mixedVector B (Sum.inr 2676) = Sparse.eval nodeValue2676 (mixedVector B) := by
    change mixedMoment B node2676 node2676Labels = _
    exact sound2676 B hB hF
  have h2718 : mixedVector B (Sum.inr 2718) = Sparse.eval nodeValue2718 (mixedVector B) := by
    change mixedMoment B node2718 node2718Labels = _
    exact sound2718 B hB hF
  have h2720 : mixedVector B (Sum.inr 2720) = Sparse.eval nodeValue2720 (mixedVector B) := by
    change mixedMoment B node2720 node2720Labels = _
    exact sound2720 B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h2728 : mixedVector B (Sum.inr 2728) = Sparse.eval nodeValue2728 (mixedVector B) := by
    change mixedMoment B node2728 node2728Labels = _
    exact sound2728 B hB hF
  have h2730 : mixedVector B (Sum.inr 2730) = Sparse.eval nodeValue2730 (mixedVector B) := by
    change mixedMoment B node2730 node2730Labels = _
    exact sound2730 B hB hF
  have h2739 : mixedVector B (Sum.inr 2739) = Sparse.eval nodeValue2739 (mixedVector B) := by
    change mixedMoment B node2739 node2739Labels = _
    exact sound2739 B hB hF
  have h2741 : mixedVector B (Sum.inr 2741) = Sparse.eval nodeValue2741 (mixedVector B) := by
    change mixedMoment B node2741 node2741Labels = _
    exact sound2741 B hB hF
  have h2764 : mixedVector B (Sum.inr 2764) = Sparse.eval nodeValue2764 (mixedVector B) := by
    change mixedMoment B node2764 node2764Labels = _
    exact sound2764 B hB hF
  have h2766 : mixedVector B (Sum.inr 2766) = Sparse.eval nodeValue2766 (mixedVector B) := by
    change mixedMoment B node2766 node2766Labels = _
    exact sound2766_e B hB hF
  have h2785 : mixedVector B (Sum.inr 2785) = Sparse.eval nodeValue2785 (mixedVector B) := by
    change mixedMoment B node2785 node2785Labels = _
    exact sound2785 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3085 : mixedVector B (Sum.inr 3085) = Sparse.eval nodeValue3085 (mixedVector B) := by
    change mixedMoment B node3085 node3085Labels = _
    exact sound3085 B hB hF
  have h3087 : mixedVector B (Sum.inr 3087) = Sparse.eval nodeValue3087 (mixedVector B) := by
    change mixedMoment B node3087 node3087Labels = _
    exact sound3087_e B hB hF
  have h3100 : mixedVector B (Sum.inr 3100) = Sparse.eval nodeValue3100 (mixedVector B) := by
    change mixedMoment B node3100 node3100Labels = _
    exact sound3100_e B hB hF
  simpa only [sourceForm839, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2202, h2204, h2214, h2263, h2669, h2671, h2676, h2718, h2720, h2721, h2728, h2730, h2739, h2741, h2764, h2766, h2785, h3037, h3085, h3087, h3100, reducedSource729] using sourceEq839 B hB

theorem rowSound729 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row729 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck729, numericCheck729, reducedZero729 B hB hF, mul_zero]

theorem sourceRowsAt720 : MixedData.sourceRows (720 : Fin 2425) =
    MixedData.row720 := by decide +kernel

theorem sourceRowsAt721 : MixedData.sourceRows (721 : Fin 2425) =
    MixedData.row721 := by decide +kernel

theorem sourceRowsAt722 : MixedData.sourceRows (722 : Fin 2425) =
    MixedData.row722 := by decide +kernel

theorem sourceRowsAt723 : MixedData.sourceRows (723 : Fin 2425) =
    MixedData.row723 := by decide +kernel

theorem sourceRowsAt724 : MixedData.sourceRows (724 : Fin 2425) =
    MixedData.row724 := by decide +kernel

theorem sourceRowsAt725 : MixedData.sourceRows (725 : Fin 2425) =
    MixedData.row725 := by decide +kernel

theorem sourceRowsAt726 : MixedData.sourceRows (726 : Fin 2425) =
    MixedData.row726 := by decide +kernel

theorem sourceRowsAt727 : MixedData.sourceRows (727 : Fin 2425) =
    MixedData.row727 := by decide +kernel

theorem sourceRowsAt728 : MixedData.sourceRows (728 : Fin 2425) =
    MixedData.row728 := by decide +kernel

theorem sourceRowsAt729 : MixedData.sourceRows (729 : Fin 2425) =
    MixedData.row729 := by decide +kernel

theorem sourceRowsAt730 : MixedData.sourceRows (730 : Fin 2425) =
    MixedData.row730 := by decide +kernel

theorem sourceRowsAt731 : MixedData.sourceRows (731 : Fin 2425) =
    MixedData.row731 := by decide +kernel

theorem sourceRowsAt732 : MixedData.sourceRows (732 : Fin 2425) =
    MixedData.row732 := by decide +kernel

theorem sourceRowsAt733 : MixedData.sourceRows (733 : Fin 2425) =
    MixedData.row733 := by decide +kernel

theorem sourceRowsAt734 : MixedData.sourceRows (734 : Fin 2425) =
    MixedData.row734 := by decide +kernel

theorem sourceRowsAt735 : MixedData.sourceRows (735 : Fin 2425) =
    MixedData.row735 := by decide +kernel

theorem chunkSound45_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 45) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 720 ∨ k.val = 721 ∨ k.val = 722 ∨ k.val = 723 ∨ k.val = 724 ∨ k.val = 725 ∨ k.val = 726 ∨ k.val = 727 ∨ k.val = 728 ∨ k.val = 729 ∨ k.val = 730 ∨ k.val = 731 ∨ k.val = 732 ∨ k.val = 733 ∨ k.val = 734 ∨ k.val = 735 := by omega
  rcases heq with h720 | h721 | h722 | h723 | h724 | h725 | h726 | h727 | h728 | h729 | h730 | h731 | h732 | h733 | h734 | h735
  · have he : k = (720 : Fin 2425) := Fin.ext h720
    subst k
    rw [sourceRowsAt720]
    exact rowSound720_e B hB hF
  · have he : k = (721 : Fin 2425) := Fin.ext h721
    subst k
    rw [sourceRowsAt721]
    exact rowSound721 B hB hF
  · have he : k = (722 : Fin 2425) := Fin.ext h722
    subst k
    rw [sourceRowsAt722]
    exact rowSound722_e B hB hF
  · have he : k = (723 : Fin 2425) := Fin.ext h723
    subst k
    rw [sourceRowsAt723]
    exact rowSound723 B hB hF
  · have he : k = (724 : Fin 2425) := Fin.ext h724
    subst k
    rw [sourceRowsAt724]
    exact rowSound724 B hB hF
  · have he : k = (725 : Fin 2425) := Fin.ext h725
    subst k
    rw [sourceRowsAt725]
    exact rowSound725 B hB hF
  · have he : k = (726 : Fin 2425) := Fin.ext h726
    subst k
    rw [sourceRowsAt726]
    exact rowSound726_e B hB hF
  · have he : k = (727 : Fin 2425) := Fin.ext h727
    subst k
    rw [sourceRowsAt727]
    exact rowSound727_e B hB hF
  · have he : k = (728 : Fin 2425) := Fin.ext h728
    subst k
    rw [sourceRowsAt728]
    exact rowSound728 B hB hF
  · have he : k = (729 : Fin 2425) := Fin.ext h729
    subst k
    rw [sourceRowsAt729]
    exact rowSound729 B hB hF
  · have he : k = (730 : Fin 2425) := Fin.ext h730
    subst k
    rw [sourceRowsAt730]
    exact rowSound730_e B hB hF
  · have he : k = (731 : Fin 2425) := Fin.ext h731
    subst k
    rw [sourceRowsAt731]
    exact rowSound731_e B hB hF
  · have he : k = (732 : Fin 2425) := Fin.ext h732
    subst k
    rw [sourceRowsAt732]
    exact rowSound732_e B hB hF
  · have he : k = (733 : Fin 2425) := Fin.ext h733
    subst k
    rw [sourceRowsAt733]
    exact rowSound733_e B hB hF
  · have he : k = (734 : Fin 2425) := Fin.ext h734
    subst k
    rw [sourceRowsAt734]
    exact rowSound734_e B hB hF
  · have he : k = (735 : Fin 2425) := Fin.ext h735
    subst k
    rw [sourceRowsAt735]
    exact rowSound735_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound45_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound45_e_oai
