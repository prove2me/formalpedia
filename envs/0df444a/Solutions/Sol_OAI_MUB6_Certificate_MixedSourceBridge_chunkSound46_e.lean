-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound46_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:19:06.323934+00:00
-- url     : https://prove2.me/submissions/a039f8d1-8ada-4a9d-bed1-8390ed772c89

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound2766_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5292_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5433_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5452_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound736_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound737_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound738_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound739_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound740_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound741_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound742_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound743_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound744_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound749_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound750_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound751_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem canonical13642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13642 raw13642Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw13642 raw13642Labels = mixedMoment B raw13642step0 raw13642step0Labels := by
      have ha : raw13642step0 = (fun i j => raw13642 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13642step0 raw13642; decide +kernel
      have hl : raw13642step0Labels = raw13642Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13642 raw13642Labels permutation180 permutation6
    mixedMoment B raw13642step0 raw13642step0Labels = mixedMoment B raw13642step1 raw13642step1Labels := by
      have ha : raw13642step1 = raw13642step0 := by apply Matrix.ext; unfold raw13642step1 raw13642step0; decide +kernel
      have hl : raw13642step0Labels = labelEmbedding9 ∘ raw13642step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13642step0 raw13642step0Labels raw13642step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14203 raw14203Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw14203 raw14203Labels = mixedMoment B raw14203step0 raw14203step0Labels := by
      have hz : ∀ j, raw14203 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14203step0 = (fun i j => raw14203 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14203step0 raw14203; decide +kernel
      have hl : raw14203step0Labels = raw14203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14203 raw14203Labels permutation265 hz
    mixedMoment B raw14203step0 raw14203step0Labels = mixedMoment B raw14203step1 raw14203step1Labels := by
      have ha : raw14203step1 = (fun i j => raw14203step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14203step1 raw14203step0; decide +kernel
      have hl : raw14203step1Labels = raw14203step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14203step0 raw14203step0Labels permutation35 permutation4
    mixedMoment B raw14203step1 raw14203step1Labels = mixedMoment B raw14203step2 raw14203step2Labels := by
      have ha : raw14203step2 = -raw14203step1 := by apply Matrix.ext; change ∀ i j, raw14203step2 i j = -(raw14203step1 i j); unfold raw14203step2 raw14203step1; decide +kernel
      have hl : raw14203step2Labels = raw14203step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14203step2 raw14203step2Labels = mixedMoment B raw14203step3 raw14203step3Labels := by
      have ha : raw14203step3 = raw14203step2 := by apply Matrix.ext; unfold raw14203step3 raw14203step2; decide +kernel
      have hl : raw14203step2Labels = labelEmbedding7 ∘ raw14203step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14203step2 raw14203step2Labels raw14203step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4838 node4838Labels := by rfl

theorem canonical14204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14204 raw14204Labels = mixedMoment B node5247 node5247Labels := by
  calc
    mixedMoment B raw14204 raw14204Labels = mixedMoment B raw14204step0 raw14204step0Labels := by
      have ha : raw14204step0 = (fun i j => raw14204 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14204step0 raw14204; decide +kernel
      have hl : raw14204step0Labels = raw14204Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14204 raw14204Labels permutation155 permutation6
    mixedMoment B raw14204step0 raw14204step0Labels = mixedMoment B raw14204step1 raw14204step1Labels := by
      have ha : raw14204step1 = raw14204step0 := by apply Matrix.ext; unfold raw14204step1 raw14204step0; decide +kernel
      have hl : raw14204step0Labels = labelEmbedding9 ∘ raw14204step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14204step0 raw14204step0Labels raw14204step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5247 node5247Labels := by rfl

theorem canonical14205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14205 raw14205Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw14205 raw14205Labels = mixedMoment B raw14205step0 raw14205step0Labels := by
      have hz : ∀ j, raw14205 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14205step0 = (fun i j => raw14205 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14205step0 raw14205; decide +kernel
      have hl : raw14205step0Labels = raw14205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14205 raw14205Labels permutation265 hz
    mixedMoment B raw14205step0 raw14205step0Labels = mixedMoment B raw14205step1 raw14205step1Labels := by
      have ha : raw14205step1 = (fun i j => raw14205step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14205step1 raw14205step0; decide +kernel
      have hl : raw14205step1Labels = raw14205step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14205step0 raw14205step0Labels permutation35 permutation6
    mixedMoment B raw14205step1 raw14205step1Labels = mixedMoment B raw14205step2 raw14205step2Labels := by
      have ha : raw14205step2 = raw14205step1 := by apply Matrix.ext; unfold raw14205step2 raw14205step1; decide +kernel
      have hl : raw14205step1Labels = labelEmbedding9 ∘ raw14205step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14205step1 raw14205step1Labels raw14205step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

theorem canonical14206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14206 raw14206Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw14206 raw14206Labels = mixedMoment B raw14206step0 raw14206step0Labels := by
      have hz : ∀ j, raw14206 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14206step0 = (fun i j => raw14206 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14206step0 raw14206; decide +kernel
      have hl : raw14206step0Labels = raw14206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14206 raw14206Labels permutation265 hz
    mixedMoment B raw14206step0 raw14206step0Labels = mixedMoment B raw14206step1 raw14206step1Labels := by
      have ha : raw14206step1 = (fun i j => raw14206step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14206step1 raw14206step0; decide +kernel
      have hl : raw14206step1Labels = raw14206step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14206step0 raw14206step0Labels permutation35 permutation6
    mixedMoment B raw14206step1 raw14206step1Labels = mixedMoment B raw14206step2 raw14206step2Labels := by
      have ha : raw14206step2 = raw14206step1 := by apply Matrix.ext; unfold raw14206step2 raw14206step1; decide +kernel
      have hl : raw14206step1Labels = labelEmbedding9 ∘ raw14206step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14206step1 raw14206step1Labels raw14206step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14251 raw14251Labels = mixedMoment B node5283 node5283Labels := by
  calc
    mixedMoment B raw14251 raw14251Labels = mixedMoment B raw14251step0 raw14251step0Labels := by
      have ha : raw14251step0 = (fun i j => raw14251 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14251step0 raw14251; decide +kernel
      have hl : raw14251step0Labels = raw14251Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14251 raw14251Labels permutation152 permutation7
    mixedMoment B raw14251step0 raw14251step0Labels = mixedMoment B raw14251step1 raw14251step1Labels := by
      have ha : raw14251step1 = raw14251step0 := by apply Matrix.ext; unfold raw14251step1 raw14251step0; decide +kernel
      have hl : raw14251step0Labels = labelEmbedding10 ∘ raw14251step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14251step0 raw14251step0Labels raw14251step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5283 node5283Labels := by rfl

theorem canonical14252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14252 raw14252Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw14252 raw14252Labels = mixedMoment B raw14252step0 raw14252step0Labels := by
      have hz : ∀ j, raw14252 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14252step0 = (fun i j => raw14252 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14252step0 raw14252; decide +kernel
      have hl : raw14252step0Labels = raw14252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14252 raw14252Labels permutation265 hz
    mixedMoment B raw14252step0 raw14252step0Labels = mixedMoment B raw14252step1 raw14252step1Labels := by
      have ha : raw14252step1 = (fun i j => raw14252step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14252step1 raw14252step0; decide +kernel
      have hl : raw14252step1Labels = raw14252step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14252step0 raw14252step0Labels permutation32 permutation7
    mixedMoment B raw14252step1 raw14252step1Labels = mixedMoment B raw14252step2 raw14252step2Labels := by
      have ha : raw14252step2 = raw14252step1 := by apply Matrix.ext; unfold raw14252step2 raw14252step1; decide +kernel
      have hl : raw14252step1Labels = labelEmbedding10 ∘ raw14252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14252step1 raw14252step1Labels raw14252step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

theorem canonical14253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14253 raw14253Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw14253 raw14253Labels = mixedMoment B raw14253step0 raw14253step0Labels := by
      have hz : ∀ j, raw14253 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14253step0 = (fun i j => raw14253 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14253step0 raw14253; decide +kernel
      have hl : raw14253step0Labels = raw14253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14253 raw14253Labels permutation265 hz
    mixedMoment B raw14253step0 raw14253step0Labels = mixedMoment B raw14253step1 raw14253step1Labels := by
      have ha : raw14253step1 = (fun i j => raw14253step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14253step1 raw14253step0; decide +kernel
      have hl : raw14253step1Labels = raw14253step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14253step0 raw14253step0Labels permutation35 permutation7
    mixedMoment B raw14253step1 raw14253step1Labels = mixedMoment B raw14253step2 raw14253step2Labels := by
      have ha : raw14253step2 = raw14253step1 := by apply Matrix.ext; unfold raw14253step2 raw14253step1; decide +kernel
      have hl : raw14253step1Labels = labelEmbedding10 ∘ raw14253step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14253step1 raw14253step1Labels raw14253step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical14254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14254 raw14254Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw14254 raw14254Labels = mixedMoment B raw14254step0 raw14254step0Labels := by
      have hz : ∀ j, raw14254 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14254step0 = (fun i j => raw14254 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14254step0 raw14254; decide +kernel
      have hl : raw14254step0Labels = raw14254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14254 raw14254Labels permutation265 hz
    mixedMoment B raw14254step0 raw14254step0Labels = mixedMoment B raw14254step1 raw14254step1Labels := by
      have ha : raw14254step1 = (fun i j => raw14254step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14254step1 raw14254step0; decide +kernel
      have hl : raw14254step1Labels = raw14254step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14254step0 raw14254step0Labels permutation33 permutation7
    mixedMoment B raw14254step1 raw14254step1Labels = mixedMoment B raw14254step2 raw14254step2Labels := by
      have ha : raw14254step2 = raw14254step1 := by apply Matrix.ext; unfold raw14254step2 raw14254step1; decide +kernel
      have hl : raw14254step1Labels = labelEmbedding10 ∘ raw14254step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14254step1 raw14254step1Labels raw14254step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical14255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14255 raw14255Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw14255 raw14255Labels = mixedMoment B raw14255step0 raw14255step0Labels := by
      have hz : ∀ j, raw14255 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14255step0 = (fun i j => raw14255 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14255step0 raw14255; decide +kernel
      have hl : raw14255step0Labels = raw14255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14255 raw14255Labels permutation346 hz
    mixedMoment B raw14255step0 raw14255step0Labels = mixedMoment B raw14255step1 raw14255step1Labels := by
      have hz : ∀ j, raw14255step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14255step1 = (fun i j => raw14255step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14255step1 raw14255step0; decide +kernel
      have hl : raw14255step1Labels = raw14255step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14255step0 raw14255step0Labels permutation56 hz
    mixedMoment B raw14255step1 raw14255step1Labels = mixedMoment B raw14255step2 raw14255step2Labels := by
      have hz : ∀ i, raw14255step1 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw14255step2 = (fun i j => raw14255step1 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw14255step2 raw14255step1; decide +kernel
      have hl : raw14255step2Labels = (fun j => raw14255step1Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14255step1 raw14255step1Labels permutation2 hz
    mixedMoment B raw14255step2 raw14255step2Labels = mixedMoment B raw14255step3 raw14255step3Labels := by
      have ha : raw14255step3 = -raw14255step2 := by apply Matrix.ext; change ∀ i j, raw14255step3 i j = -(raw14255step2 i j); unfold raw14255step3 raw14255step2; decide +kernel
      have hl : raw14255step3Labels = raw14255step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14255step3 raw14255step3Labels = mixedMoment B raw14255step4 raw14255step4Labels := by
      have ha : raw14255step4 = raw14255step3 := by apply Matrix.ext; unfold raw14255step4 raw14255step3; decide +kernel
      have hl : raw14255step3Labels = labelEmbedding3 ∘ raw14255step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14255step3 raw14255step3Labels raw14255step4Labels labelEmbedding3 hl
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical14256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14256 raw14256Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw14256 raw14256Labels = mixedMoment B raw14256step0 raw14256step0Labels := by
      have hz : ∀ j, raw14256 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14256step0 = (fun i j => raw14256 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14256step0 raw14256; decide +kernel
      have hl : raw14256step0Labels = raw14256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14256 raw14256Labels permutation346 hz
    mixedMoment B raw14256step0 raw14256step0Labels = mixedMoment B raw14256step1 raw14256step1Labels := by
      have ha : raw14256step1 = (fun i j => raw14256step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14256step1 raw14256step0; decide +kernel
      have hl : raw14256step1Labels = raw14256step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14256step0 raw14256step0Labels permutation32 permutation6
    mixedMoment B raw14256step1 raw14256step1Labels = mixedMoment B raw14256step2 raw14256step2Labels := by
      have ha : raw14256step2 = raw14256step1 := by apply Matrix.ext; unfold raw14256step2 raw14256step1; decide +kernel
      have hl : raw14256step1Labels = labelEmbedding9 ∘ raw14256step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14256step1 raw14256step1Labels raw14256step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5273 node5273Labels := by rfl

theorem canonical14257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14257 raw14257Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw14257 raw14257Labels = mixedMoment B raw14257step0 raw14257step0Labels := by
      have hz : ∀ j, raw14257 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14257step0 = (fun i j => raw14257 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14257step0 raw14257; decide +kernel
      have hl : raw14257step0Labels = raw14257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14257 raw14257Labels permutation265 hz
    mixedMoment B raw14257step0 raw14257step0Labels = mixedMoment B raw14257step1 raw14257step1Labels := by
      have ha : raw14257step1 = (fun i j => raw14257step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14257step1 raw14257step0; decide +kernel
      have hl : raw14257step1Labels = raw14257step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14257step0 raw14257step0Labels permutation33 permutation4
    mixedMoment B raw14257step1 raw14257step1Labels = mixedMoment B raw14257step2 raw14257step2Labels := by
      have ha : raw14257step2 = -raw14257step1 := by apply Matrix.ext; change ∀ i j, raw14257step2 i j = -(raw14257step1 i j); unfold raw14257step2 raw14257step1; decide +kernel
      have hl : raw14257step2Labels = raw14257step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14257step2 raw14257step2Labels = mixedMoment B raw14257step3 raw14257step3Labels := by
      have ha : raw14257step3 = raw14257step2 := by apply Matrix.ext; unfold raw14257step3 raw14257step2; decide +kernel
      have hl : raw14257step2Labels = labelEmbedding7 ∘ raw14257step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14257step2 raw14257step2Labels raw14257step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4838 node4838Labels := by rfl

theorem canonical14258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14258 raw14258Labels = mixedMoment B node5247 node5247Labels := by
  calc
    mixedMoment B raw14258 raw14258Labels = mixedMoment B raw14258step0 raw14258step0Labels := by
      have ha : raw14258step0 = (fun i j => raw14258 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14258step0 raw14258; decide +kernel
      have hl : raw14258step0Labels = raw14258Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14258 raw14258Labels permutation153 permutation6
    mixedMoment B raw14258step0 raw14258step0Labels = mixedMoment B raw14258step1 raw14258step1Labels := by
      have ha : raw14258step1 = raw14258step0 := by apply Matrix.ext; unfold raw14258step1 raw14258step0; decide +kernel
      have hl : raw14258step0Labels = labelEmbedding9 ∘ raw14258step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14258step0 raw14258step0Labels raw14258step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5247 node5247Labels := by rfl

theorem canonical14259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14259 raw14259Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw14259 raw14259Labels = mixedMoment B raw14259step0 raw14259step0Labels := by
      have hz : ∀ j, raw14259 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14259step0 = (fun i j => raw14259 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14259step0 raw14259; decide +kernel
      have hl : raw14259step0Labels = raw14259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14259 raw14259Labels permutation265 hz
    mixedMoment B raw14259step0 raw14259step0Labels = mixedMoment B raw14259step1 raw14259step1Labels := by
      have ha : raw14259step1 = (fun i j => raw14259step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14259step1 raw14259step0; decide +kernel
      have hl : raw14259step1Labels = raw14259step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14259step0 raw14259step0Labels permutation33 permutation6
    mixedMoment B raw14259step1 raw14259step1Labels = mixedMoment B raw14259step2 raw14259step2Labels := by
      have ha : raw14259step2 = raw14259step1 := by apply Matrix.ext; unfold raw14259step2 raw14259step1; decide +kernel
      have hl : raw14259step1Labels = labelEmbedding9 ∘ raw14259step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14259step1 raw14259step1Labels raw14259step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

theorem canonical14260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14260 raw14260Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw14260 raw14260Labels = mixedMoment B raw14260step0 raw14260step0Labels := by
      have hz : ∀ j, raw14260 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14260step0 = (fun i j => raw14260 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14260step0 raw14260; decide +kernel
      have hl : raw14260step0Labels = raw14260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14260 raw14260Labels permutation265 hz
    mixedMoment B raw14260step0 raw14260step0Labels = mixedMoment B raw14260step1 raw14260step1Labels := by
      have ha : raw14260step1 = (fun i j => raw14260step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14260step1 raw14260step0; decide +kernel
      have hl : raw14260step1Labels = raw14260step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14260step0 raw14260step0Labels permutation33 permutation6
    mixedMoment B raw14260step1 raw14260step1Labels = mixedMoment B raw14260step2 raw14260step2Labels := by
      have ha : raw14260step2 = raw14260step1 := by apply Matrix.ext; unfold raw14260step2 raw14260step1; decide +kernel
      have hl : raw14260step1Labels = labelEmbedding9 ∘ raw14260step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14260step1 raw14260step1Labels raw14260step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical14261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14261 raw14261Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw14261 raw14261Labels = mixedMoment B raw14261step0 raw14261step0Labels := by
      have hz : ∀ j, raw14261 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14261step0 = (fun i j => raw14261 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14261step0 raw14261; decide +kernel
      have hl : raw14261step0Labels = raw14261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14261 raw14261Labels permutation265 hz
    mixedMoment B raw14261step0 raw14261step0Labels = mixedMoment B raw14261step1 raw14261step1Labels := by
      have ha : raw14261step1 = (fun i j => raw14261step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14261step1 raw14261step0; decide +kernel
      have hl : raw14261step1Labels = raw14261step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14261step0 raw14261step0Labels permutation32 permutation4
    mixedMoment B raw14261step1 raw14261step1Labels = mixedMoment B raw14261step2 raw14261step2Labels := by
      have ha : raw14261step2 = -raw14261step1 := by apply Matrix.ext; change ∀ i j, raw14261step2 i j = -(raw14261step1 i j); unfold raw14261step2 raw14261step1; decide +kernel
      have hl : raw14261step2Labels = raw14261step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14261step2 raw14261step2Labels = mixedMoment B raw14261step3 raw14261step3Labels := by
      have ha : raw14261step3 = raw14261step2 := by apply Matrix.ext; unfold raw14261step3 raw14261step2; decide +kernel
      have hl : raw14261step2Labels = labelEmbedding7 ∘ raw14261step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14261step2 raw14261step2Labels raw14261step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4838 node4838Labels := by rfl

theorem canonical14262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14262 raw14262Labels = mixedMoment B node5247 node5247Labels := by
  calc
    mixedMoment B raw14262 raw14262Labels = mixedMoment B raw14262step0 raw14262step0Labels := by
      have ha : raw14262step0 = (fun i j => raw14262 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14262step0 raw14262; decide +kernel
      have hl : raw14262step0Labels = raw14262Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14262 raw14262Labels permutation152 permutation6
    mixedMoment B raw14262step0 raw14262step0Labels = mixedMoment B raw14262step1 raw14262step1Labels := by
      have ha : raw14262step1 = raw14262step0 := by apply Matrix.ext; unfold raw14262step1 raw14262step0; decide +kernel
      have hl : raw14262step0Labels = labelEmbedding9 ∘ raw14262step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14262step0 raw14262step0Labels raw14262step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5247 node5247Labels := by rfl

theorem canonical14263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14263 raw14263Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw14263 raw14263Labels = mixedMoment B raw14263step0 raw14263step0Labels := by
      have hz : ∀ j, raw14263 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14263step0 = (fun i j => raw14263 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14263step0 raw14263; decide +kernel
      have hl : raw14263step0Labels = raw14263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14263 raw14263Labels permutation265 hz
    mixedMoment B raw14263step0 raw14263step0Labels = mixedMoment B raw14263step1 raw14263step1Labels := by
      have ha : raw14263step1 = (fun i j => raw14263step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14263step1 raw14263step0; decide +kernel
      have hl : raw14263step1Labels = raw14263step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14263step0 raw14263step0Labels permutation32 permutation6
    mixedMoment B raw14263step1 raw14263step1Labels = mixedMoment B raw14263step2 raw14263step2Labels := by
      have ha : raw14263step2 = raw14263step1 := by apply Matrix.ext; unfold raw14263step2 raw14263step1; decide +kernel
      have hl : raw14263step1Labels = labelEmbedding9 ∘ raw14263step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14263step1 raw14263step1Labels raw14263step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

theorem canonical14264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14264 raw14264Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw14264 raw14264Labels = mixedMoment B raw14264step0 raw14264step0Labels := by
      have ha : raw14264step0 = (fun i j => raw14264 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14264step0 raw14264; decide +kernel
      have hl : raw14264step0Labels = raw14264Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14264 raw14264Labels permutation240 permutation7
    mixedMoment B raw14264step0 raw14264step0Labels = mixedMoment B raw14264step1 raw14264step1Labels := by
      have ha : raw14264step1 = -raw14264step0 := by apply Matrix.ext; change ∀ i j, raw14264step1 i j = -(raw14264step0 i j); unfold raw14264step1 raw14264step0; decide +kernel
      have hl : raw14264step1Labels = raw14264step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14264step1 raw14264step1Labels = mixedMoment B raw14264step2 raw14264step2Labels := by
      have ha : raw14264step2 = raw14264step1 := by apply Matrix.ext; unfold raw14264step2 raw14264step1; decide +kernel
      have hl : raw14264step1Labels = labelEmbedding10 ∘ raw14264step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14264step1 raw14264step1Labels raw14264step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical14265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14265 raw14265Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw14265 raw14265Labels = mixedMoment B raw14265step0 raw14265step0Labels := by
      have ha : raw14265step0 = (fun i j => raw14265 (permutation242 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14265step0 raw14265; decide +kernel
      have hl : raw14265step0Labels = raw14265Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14265 raw14265Labels permutation242 permutation7
    mixedMoment B raw14265step0 raw14265step0Labels = mixedMoment B raw14265step1 raw14265step1Labels := by
      have ha : raw14265step1 = -raw14265step0 := by apply Matrix.ext; change ∀ i j, raw14265step1 i j = -(raw14265step0 i j); unfold raw14265step1 raw14265step0; decide +kernel
      have hl : raw14265step1Labels = raw14265step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14265step1 raw14265step1Labels = mixedMoment B raw14265step2 raw14265step2Labels := by
      have ha : raw14265step2 = raw14265step1 := by apply Matrix.ext; unfold raw14265step2 raw14265step1; decide +kernel
      have hl : raw14265step1Labels = labelEmbedding10 ∘ raw14265step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14265step1 raw14265step1Labels raw14265step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical14266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14266 raw14266Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw14266 raw14266Labels = mixedMoment B raw14266step0 raw14266step0Labels := by
      have hz : ∀ j, raw14266 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14266step0 = (fun i j => raw14266 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14266step0 raw14266; decide +kernel
      have hl : raw14266step0Labels = raw14266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14266 raw14266Labels permutation520 hz
    mixedMoment B raw14266step0 raw14266step0Labels = mixedMoment B raw14266step1 raw14266step1Labels := by
      have ha : raw14266step1 = (fun i j => raw14266step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14266step1 raw14266step0; decide +kernel
      have hl : raw14266step1Labels = raw14266step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14266step0 raw14266step0Labels permutation50 permutation7
    mixedMoment B raw14266step1 raw14266step1Labels = mixedMoment B raw14266step2 raw14266step2Labels := by
      have ha : raw14266step2 = -raw14266step1 := by apply Matrix.ext; change ∀ i j, raw14266step2 i j = -(raw14266step1 i j); unfold raw14266step2 raw14266step1; decide +kernel
      have hl : raw14266step2Labels = raw14266step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14266step2 raw14266step2Labels = mixedMoment B raw14266step3 raw14266step3Labels := by
      have ha : raw14266step3 = raw14266step2 := by apply Matrix.ext; unfold raw14266step3 raw14266step2; decide +kernel
      have hl : raw14266step2Labels = labelEmbedding10 ∘ raw14266step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14266step2 raw14266step2Labels raw14266step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical14267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14267 raw14267Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw14267 raw14267Labels = mixedMoment B raw14267step0 raw14267step0Labels := by
      have hz : ∀ j, raw14267 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14267step0 = (fun i j => raw14267 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14267step0 raw14267; decide +kernel
      have hl : raw14267step0Labels = raw14267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14267 raw14267Labels permutation590 hz
    mixedMoment B raw14267step0 raw14267step0Labels = mixedMoment B raw14267step1 raw14267step1Labels := by
      have ha : raw14267step1 = (fun i j => raw14267step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14267step1 raw14267step0; decide +kernel
      have hl : raw14267step1Labels = raw14267step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14267step0 raw14267step0Labels permutation50 permutation7
    mixedMoment B raw14267step1 raw14267step1Labels = mixedMoment B raw14267step2 raw14267step2Labels := by
      have ha : raw14267step2 = -raw14267step1 := by apply Matrix.ext; change ∀ i j, raw14267step2 i j = -(raw14267step1 i j); unfold raw14267step2 raw14267step1; decide +kernel
      have hl : raw14267step2Labels = raw14267step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14267step2 raw14267step2Labels = mixedMoment B raw14267step3 raw14267step3Labels := by
      have ha : raw14267step3 = raw14267step2 := by apply Matrix.ext; unfold raw14267step3 raw14267step2; decide +kernel
      have hl : raw14267step2Labels = labelEmbedding10 ∘ raw14267step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14267step2 raw14267step2Labels raw14267step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical14268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14268 raw14268Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw14268 raw14268Labels = mixedMoment B raw14268step0 raw14268step0Labels := by
      have ha : raw14268step0 = (fun i j => raw14268 (permutation192 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14268step0 raw14268; decide +kernel
      have hl : raw14268step0Labels = raw14268Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14268 raw14268Labels permutation192 permutation2
    _ = mixedMoment B node4456 node4456Labels := by rfl

theorem canonical14269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14269 raw14269Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw14269 raw14269Labels = mixedMoment B raw14269step0 raw14269step0Labels := by
      have ha : raw14269step0 = (fun i j => raw14269 (permutation192 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14269step0 raw14269; decide +kernel
      have hl : raw14269step0Labels = raw14269Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14269 raw14269Labels permutation192 permutation2
    _ = mixedMoment B node4864 node4864Labels := by rfl

theorem canonical14270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14270 raw14270Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw14270 raw14270Labels = mixedMoment B raw14270step0 raw14270step0Labels := by
      have hz : ∀ j, raw14270 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14270step0 = (fun i j => raw14270 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14270step0 raw14270; decide +kernel
      have hl : raw14270step0Labels = raw14270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14270 raw14270Labels permutation520 hz
    mixedMoment B raw14270step0 raw14270step0Labels = mixedMoment B raw14270step1 raw14270step1Labels := by
      have ha : raw14270step1 = (fun i j => raw14270step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14270step1 raw14270step0; decide +kernel
      have hl : raw14270step1Labels = raw14270step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14270step0 raw14270step0Labels permutation42 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

theorem canonical14271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14271 raw14271Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw14271 raw14271Labels = mixedMoment B raw14271step0 raw14271step0Labels := by
      have hz : ∀ j, raw14271 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14271step0 = (fun i j => raw14271 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14271step0 raw14271; decide +kernel
      have hl : raw14271step0Labels = raw14271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14271 raw14271Labels permutation590 hz
    mixedMoment B raw14271step0 raw14271step0Labels = mixedMoment B raw14271step1 raw14271step1Labels := by
      have ha : raw14271step1 = (fun i j => raw14271step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14271step1 raw14271step0; decide +kernel
      have hl : raw14271step1Labels = raw14271step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14271step0 raw14271step0Labels permutation42 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

theorem canonical14272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14272 raw14272Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw14272 raw14272Labels = mixedMoment B raw14272step0 raw14272step0Labels := by
      have ha : raw14272step0 = (fun i j => raw14272 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14272step0 raw14272; decide +kernel
      have hl : raw14272step0Labels = raw14272Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14272 raw14272Labels permutation168 permutation2
    _ = mixedMoment B node4456 node4456Labels := by rfl

theorem canonical14273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14273 raw14273Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw14273 raw14273Labels = mixedMoment B raw14273step0 raw14273step0Labels := by
      have ha : raw14273step0 = (fun i j => raw14273 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14273step0 raw14273; decide +kernel
      have hl : raw14273step0Labels = raw14273Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14273 raw14273Labels permutation168 permutation2
    _ = mixedMoment B node4864 node4864Labels := by rfl

theorem canonical14274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14274 raw14274Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw14274 raw14274Labels = mixedMoment B raw14274step0 raw14274step0Labels := by
      have hz : ∀ j, raw14274 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14274step0 = (fun i j => raw14274 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14274step0 raw14274; decide +kernel
      have hl : raw14274step0Labels = raw14274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14274 raw14274Labels permutation520 hz
    mixedMoment B raw14274step0 raw14274step0Labels = mixedMoment B raw14274step1 raw14274step1Labels := by
      have ha : raw14274step1 = (fun i j => raw14274step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14274step1 raw14274step0; decide +kernel
      have hl : raw14274step1Labels = raw14274step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14274step0 raw14274step0Labels permutation36 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

theorem canonical14275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14275 raw14275Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw14275 raw14275Labels = mixedMoment B raw14275step0 raw14275step0Labels := by
      have hz : ∀ j, raw14275 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14275step0 = (fun i j => raw14275 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14275step0 raw14275; decide +kernel
      have hl : raw14275step0Labels = raw14275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14275 raw14275Labels permutation590 hz
    mixedMoment B raw14275step0 raw14275step0Labels = mixedMoment B raw14275step1 raw14275step1Labels := by
      have ha : raw14275step1 = (fun i j => raw14275step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14275step1 raw14275step0; decide +kernel
      have hl : raw14275step1Labels = raw14275step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14275step0 raw14275step0Labels permutation36 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

theorem canonical14276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14276 raw14276Labels = mixedMoment B node4438 node4438Labels := by
  calc
    mixedMoment B raw14276 raw14276Labels = mixedMoment B raw14276step0 raw14276step0Labels := by
      have ha : raw14276step0 = (fun i j => raw14276 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14276step0 raw14276; decide +kernel
      have hl : raw14276step0Labels = raw14276Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14276 raw14276Labels permutation155 permutation2
    _ = mixedMoment B node4438 node4438Labels := by rfl

theorem canonical14277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14277 raw14277Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw14277 raw14277Labels = mixedMoment B raw14277step0 raw14277step0Labels := by
      have ha : raw14277step0 = (fun i j => raw14277 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14277step0 raw14277; decide +kernel
      have hl : raw14277step0Labels = raw14277Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14277 raw14277Labels permutation155 permutation2
    _ = mixedMoment B node4851 node4851Labels := by rfl

theorem canonical14278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14278 raw14278Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw14278 raw14278Labels = mixedMoment B raw14278step0 raw14278step0Labels := by
      have ha : raw14278step0 = (fun i j => raw14278 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14278step0 raw14278; decide +kernel
      have hl : raw14278step0Labels = raw14278Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14278 raw14278Labels permutation179 permutation2
    _ = mixedMoment B node4851 node4851Labels := by rfl

theorem canonical14279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14279 raw14279Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw14279 raw14279Labels = mixedMoment B raw14279step0 raw14279step0Labels := by
      have hz : ∀ j, raw14279 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14279step0 = (fun i j => raw14279 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14279step0 raw14279; decide +kernel
      have hl : raw14279step0Labels = raw14279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14279 raw14279Labels permutation520 hz
    mixedMoment B raw14279step0 raw14279step0Labels = mixedMoment B raw14279step1 raw14279step1Labels := by
      have ha : raw14279step1 = (fun i j => raw14279step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14279step1 raw14279step0; decide +kernel
      have hl : raw14279step1Labels = raw14279step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14279step0 raw14279step0Labels permutation33 permutation2
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical14280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14280 raw14280Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw14280 raw14280Labels = mixedMoment B raw14280step0 raw14280step0Labels := by
      have hz : ∀ j, raw14280 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14280step0 = (fun i j => raw14280 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14280step0 raw14280; decide +kernel
      have hl : raw14280step0Labels = raw14280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14280 raw14280Labels permutation590 hz
    mixedMoment B raw14280step0 raw14280step0Labels = mixedMoment B raw14280step1 raw14280step1Labels := by
      have ha : raw14280step1 = (fun i j => raw14280step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14280step1 raw14280step0; decide +kernel
      have hl : raw14280step1Labels = raw14280step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14280step0 raw14280step0Labels permutation33 permutation2
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical14281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14281 raw14281Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw14281 raw14281Labels = mixedMoment B raw14281step0 raw14281step0Labels := by
      have ha : raw14281step0 = (fun i j => raw14281 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14281step0 raw14281; decide +kernel
      have hl : raw14281step0Labels = raw14281Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14281 raw14281Labels permutation156 permutation2
    _ = mixedMoment B node4439 node4439Labels := by rfl

theorem canonical14282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14282 raw14282Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw14282 raw14282Labels = mixedMoment B raw14282step0 raw14282step0Labels := by
      have ha : raw14282step0 = (fun i j => raw14282 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14282step0 raw14282; decide +kernel
      have hl : raw14282step0Labels = raw14282Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14282 raw14282Labels permutation156 permutation2
    _ = mixedMoment B node4852 node4852Labels := by rfl

theorem canonical14283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14283 raw14283Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw14283 raw14283Labels = mixedMoment B raw14283step0 raw14283step0Labels := by
      have ha : raw14283step0 = (fun i j => raw14283 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14283step0 raw14283; decide +kernel
      have hl : raw14283step0Labels = raw14283Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14283 raw14283Labels permutation180 permutation2
    _ = mixedMoment B node4852 node4852Labels := by rfl

theorem canonical14284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14284 raw14284Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw14284 raw14284Labels = mixedMoment B raw14284step0 raw14284step0Labels := by
      have hz : ∀ j, raw14284 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14284step0 = (fun i j => raw14284 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14284step0 raw14284; decide +kernel
      have hl : raw14284step0Labels = raw14284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14284 raw14284Labels permutation590 hz
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical14285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14285 raw14285Labels = mixedMoment B node4885 node4885Labels := by
  calc
    _ = mixedMoment B node4885 node4885Labels := by rfl

theorem canonical14286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14286 raw14286Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw14286 raw14286Labels = mixedMoment B raw14286step0 raw14286step0Labels := by
      have ha : raw14286step0 = (fun i j => raw14286 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14286step0 raw14286; decide +kernel
      have hl : raw14286step0Labels = raw14286Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14286 raw14286Labels permutation240 permutation7
    mixedMoment B raw14286step0 raw14286step0Labels = mixedMoment B raw14286step1 raw14286step1Labels := by
      have ha : raw14286step1 = -raw14286step0 := by apply Matrix.ext; change ∀ i j, raw14286step1 i j = -(raw14286step0 i j); unfold raw14286step1 raw14286step0; decide +kernel
      have hl : raw14286step1Labels = raw14286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14286step1 raw14286step1Labels = mixedMoment B raw14286step2 raw14286step2Labels := by
      have ha : raw14286step2 = raw14286step1 := by apply Matrix.ext; unfold raw14286step2 raw14286step1; decide +kernel
      have hl : raw14286step1Labels = labelEmbedding1 ∘ raw14286step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14286step1 raw14286step1Labels raw14286step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2750 node2750Labels := by rfl

theorem canonical14287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14287 raw14287Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw14287 raw14287Labels = mixedMoment B raw14287step0 raw14287step0Labels := by
      have ha : raw14287step0 = (fun i j => raw14287 (permutation242 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14287step0 raw14287; decide +kernel
      have hl : raw14287step0Labels = raw14287Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14287 raw14287Labels permutation242 permutation7
    mixedMoment B raw14287step0 raw14287step0Labels = mixedMoment B raw14287step1 raw14287step1Labels := by
      have ha : raw14287step1 = -raw14287step0 := by apply Matrix.ext; change ∀ i j, raw14287step1 i j = -(raw14287step0 i j); unfold raw14287step1 raw14287step0; decide +kernel
      have hl : raw14287step1Labels = raw14287step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14287step1 raw14287step1Labels = mixedMoment B raw14287step2 raw14287step2Labels := by
      have ha : raw14287step2 = raw14287step1 := by apply Matrix.ext; unfold raw14287step2 raw14287step1; decide +kernel
      have hl : raw14287step1Labels = labelEmbedding1 ∘ raw14287step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14287step1 raw14287step1Labels raw14287step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2750 node2750Labels := by rfl

theorem canonical14288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14288 raw14288Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw14288 raw14288Labels = mixedMoment B raw14288step0 raw14288step0Labels := by
      have hz : ∀ j, raw14288 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14288step0 = (fun i j => raw14288 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14288step0 raw14288; decide +kernel
      have hl : raw14288step0Labels = raw14288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14288 raw14288Labels permutation520 hz
    mixedMoment B raw14288step0 raw14288step0Labels = mixedMoment B raw14288step1 raw14288step1Labels := by
      have ha : raw14288step1 = (fun i j => raw14288step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14288step1 raw14288step0; decide +kernel
      have hl : raw14288step1Labels = raw14288step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14288step0 raw14288step0Labels permutation50 permutation7
    mixedMoment B raw14288step1 raw14288step1Labels = mixedMoment B raw14288step2 raw14288step2Labels := by
      have ha : raw14288step2 = -raw14288step1 := by apply Matrix.ext; change ∀ i j, raw14288step2 i j = -(raw14288step1 i j); unfold raw14288step2 raw14288step1; decide +kernel
      have hl : raw14288step2Labels = raw14288step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14288step2 raw14288step2Labels = mixedMoment B raw14288step3 raw14288step3Labels := by
      have ha : raw14288step3 = raw14288step2 := by apply Matrix.ext; unfold raw14288step3 raw14288step2; decide +kernel
      have hl : raw14288step2Labels = labelEmbedding1 ∘ raw14288step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14288step2 raw14288step2Labels raw14288step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2766 node2766Labels := by rfl

theorem canonical14289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14289 raw14289Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw14289 raw14289Labels = mixedMoment B raw14289step0 raw14289step0Labels := by
      have hz : ∀ j, raw14289 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14289step0 = (fun i j => raw14289 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14289step0 raw14289; decide +kernel
      have hl : raw14289step0Labels = raw14289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14289 raw14289Labels permutation590 hz
    mixedMoment B raw14289step0 raw14289step0Labels = mixedMoment B raw14289step1 raw14289step1Labels := by
      have ha : raw14289step1 = (fun i j => raw14289step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14289step1 raw14289step0; decide +kernel
      have hl : raw14289step1Labels = raw14289step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14289step0 raw14289step0Labels permutation50 permutation7
    mixedMoment B raw14289step1 raw14289step1Labels = mixedMoment B raw14289step2 raw14289step2Labels := by
      have ha : raw14289step2 = -raw14289step1 := by apply Matrix.ext; change ∀ i j, raw14289step2 i j = -(raw14289step1 i j); unfold raw14289step2 raw14289step1; decide +kernel
      have hl : raw14289step2Labels = raw14289step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14289step2 raw14289step2Labels = mixedMoment B raw14289step3 raw14289step3Labels := by
      have ha : raw14289step3 = raw14289step2 := by apply Matrix.ext; unfold raw14289step3 raw14289step2; decide +kernel
      have hl : raw14289step2Labels = labelEmbedding1 ∘ raw14289step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14289step2 raw14289step2Labels raw14289step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2766 node2766Labels := by rfl

theorem canonical14290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14290 raw14290Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw14290 raw14290Labels = mixedMoment B raw14290step0 raw14290step0Labels := by
      have ha : raw14290step0 = (fun i j => raw14290 (permutation242 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14290step0 raw14290; decide +kernel
      have hl : raw14290step0Labels = raw14290Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14290 raw14290Labels permutation242 permutation7
    mixedMoment B raw14290step0 raw14290step0Labels = mixedMoment B raw14290step1 raw14290step1Labels := by
      have ha : raw14290step1 = -raw14290step0 := by apply Matrix.ext; change ∀ i j, raw14290step1 i j = -(raw14290step0 i j); unfold raw14290step1 raw14290step0; decide +kernel
      have hl : raw14290step1Labels = raw14290step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14290step1 raw14290step1Labels = mixedMoment B raw14290step2 raw14290step2Labels := by
      have ha : raw14290step2 = raw14290step1 := by apply Matrix.ext; unfold raw14290step2 raw14290step1; decide +kernel
      have hl : raw14290step1Labels = labelEmbedding1 ∘ raw14290step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14290step1 raw14290step1Labels raw14290step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1706 node1706Labels := by rfl

theorem canonical14291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14291 raw14291Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw14291 raw14291Labels = mixedMoment B raw14291step0 raw14291step0Labels := by
      have ha : raw14291step0 = (fun i j => raw14291 (permutation242 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14291step0 raw14291; decide +kernel
      have hl : raw14291step0Labels = raw14291Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14291 raw14291Labels permutation242 permutation7
    mixedMoment B raw14291step0 raw14291step0Labels = mixedMoment B raw14291step1 raw14291step1Labels := by
      have ha : raw14291step1 = -raw14291step0 := by apply Matrix.ext; change ∀ i j, raw14291step1 i j = -(raw14291step0 i j); unfold raw14291step1 raw14291step0; decide +kernel
      have hl : raw14291step1Labels = raw14291step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14291step1 raw14291step1Labels = mixedMoment B raw14291step2 raw14291step2Labels := by
      have ha : raw14291step2 = raw14291step1 := by apply Matrix.ext; unfold raw14291step2 raw14291step1; decide +kernel
      have hl : raw14291step1Labels = labelEmbedding1 ∘ raw14291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14291step1 raw14291step1Labels raw14291step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2241 node2241Labels := by rfl

theorem canonical14292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14292 raw14292Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw14292 raw14292Labels = mixedMoment B raw14292step0 raw14292step0Labels := by
      have hz : ∀ j, raw14292 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14292step0 = (fun i j => raw14292 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14292step0 raw14292; decide +kernel
      have hl : raw14292step0Labels = raw14292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14292 raw14292Labels permutation520 hz
    mixedMoment B raw14292step0 raw14292step0Labels = mixedMoment B raw14292step1 raw14292step1Labels := by
      have ha : raw14292step1 = (fun i j => raw14292step0 (permutation52 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14292step1 raw14292step0; decide +kernel
      have hl : raw14292step1Labels = raw14292step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14292step0 raw14292step0Labels permutation52 permutation7
    mixedMoment B raw14292step1 raw14292step1Labels = mixedMoment B raw14292step2 raw14292step2Labels := by
      have ha : raw14292step2 = -raw14292step1 := by apply Matrix.ext; change ∀ i j, raw14292step2 i j = -(raw14292step1 i j); unfold raw14292step2 raw14292step1; decide +kernel
      have hl : raw14292step2Labels = raw14292step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14292step2 raw14292step2Labels = mixedMoment B raw14292step3 raw14292step3Labels := by
      have ha : raw14292step3 = raw14292step2 := by apply Matrix.ext; unfold raw14292step3 raw14292step2; decide +kernel
      have hl : raw14292step2Labels = labelEmbedding1 ∘ raw14292step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14292step2 raw14292step2Labels raw14292step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

theorem canonical14293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14293 raw14293Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw14293 raw14293Labels = mixedMoment B raw14293step0 raw14293step0Labels := by
      have hz : ∀ j, raw14293 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14293step0 = (fun i j => raw14293 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14293step0 raw14293; decide +kernel
      have hl : raw14293step0Labels = raw14293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14293 raw14293Labels permutation590 hz
    mixedMoment B raw14293step0 raw14293step0Labels = mixedMoment B raw14293step1 raw14293step1Labels := by
      have ha : raw14293step1 = (fun i j => raw14293step0 (permutation52 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14293step1 raw14293step0; decide +kernel
      have hl : raw14293step1Labels = raw14293step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14293step0 raw14293step0Labels permutation52 permutation7
    mixedMoment B raw14293step1 raw14293step1Labels = mixedMoment B raw14293step2 raw14293step2Labels := by
      have ha : raw14293step2 = -raw14293step1 := by apply Matrix.ext; change ∀ i j, raw14293step2 i j = -(raw14293step1 i j); unfold raw14293step2 raw14293step1; decide +kernel
      have hl : raw14293step2Labels = raw14293step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14293step2 raw14293step2Labels = mixedMoment B raw14293step3 raw14293step3Labels := by
      have ha : raw14293step3 = raw14293step2 := by apply Matrix.ext; unfold raw14293step3 raw14293step2; decide +kernel
      have hl : raw14293step2Labels = labelEmbedding1 ∘ raw14293step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14293step2 raw14293step2Labels raw14293step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

theorem canonical14294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14294 raw14294Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw14294 raw14294Labels = mixedMoment B raw14294step0 raw14294step0Labels := by
      have ha : raw14294step0 = (fun i j => raw14294 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14294step0 raw14294; decide +kernel
      have hl : raw14294step0Labels = raw14294Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14294 raw14294Labels permutation240 permutation7
    mixedMoment B raw14294step0 raw14294step0Labels = mixedMoment B raw14294step1 raw14294step1Labels := by
      have ha : raw14294step1 = -raw14294step0 := by apply Matrix.ext; change ∀ i j, raw14294step1 i j = -(raw14294step0 i j); unfold raw14294step1 raw14294step0; decide +kernel
      have hl : raw14294step1Labels = raw14294step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14294step1 raw14294step1Labels = mixedMoment B raw14294step2 raw14294step2Labels := by
      have ha : raw14294step2 = raw14294step1 := by apply Matrix.ext; unfold raw14294step2 raw14294step1; decide +kernel
      have hl : raw14294step1Labels = labelEmbedding1 ∘ raw14294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14294step1 raw14294step1Labels raw14294step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1706 node1706Labels := by rfl

theorem canonical14295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14295 raw14295Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw14295 raw14295Labels = mixedMoment B raw14295step0 raw14295step0Labels := by
      have ha : raw14295step0 = (fun i j => raw14295 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14295step0 raw14295; decide +kernel
      have hl : raw14295step0Labels = raw14295Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14295 raw14295Labels permutation240 permutation7
    mixedMoment B raw14295step0 raw14295step0Labels = mixedMoment B raw14295step1 raw14295step1Labels := by
      have ha : raw14295step1 = -raw14295step0 := by apply Matrix.ext; change ∀ i j, raw14295step1 i j = -(raw14295step0 i j); unfold raw14295step1 raw14295step0; decide +kernel
      have hl : raw14295step1Labels = raw14295step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14295step1 raw14295step1Labels = mixedMoment B raw14295step2 raw14295step2Labels := by
      have ha : raw14295step2 = raw14295step1 := by apply Matrix.ext; unfold raw14295step2 raw14295step1; decide +kernel
      have hl : raw14295step1Labels = labelEmbedding1 ∘ raw14295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14295step1 raw14295step1Labels raw14295step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2241 node2241Labels := by rfl

theorem canonical14296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14296 raw14296Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw14296 raw14296Labels = mixedMoment B raw14296step0 raw14296step0Labels := by
      have hz : ∀ j, raw14296 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14296step0 = (fun i j => raw14296 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14296step0 raw14296; decide +kernel
      have hl : raw14296step0Labels = raw14296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14296 raw14296Labels permutation520 hz
    mixedMoment B raw14296step0 raw14296step0Labels = mixedMoment B raw14296step1 raw14296step1Labels := by
      have ha : raw14296step1 = (fun i j => raw14296step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14296step1 raw14296step0; decide +kernel
      have hl : raw14296step1Labels = raw14296step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14296step0 raw14296step0Labels permutation50 permutation7
    mixedMoment B raw14296step1 raw14296step1Labels = mixedMoment B raw14296step2 raw14296step2Labels := by
      have ha : raw14296step2 = -raw14296step1 := by apply Matrix.ext; change ∀ i j, raw14296step2 i j = -(raw14296step1 i j); unfold raw14296step2 raw14296step1; decide +kernel
      have hl : raw14296step2Labels = raw14296step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14296step2 raw14296step2Labels = mixedMoment B raw14296step3 raw14296step3Labels := by
      have ha : raw14296step3 = raw14296step2 := by apply Matrix.ext; unfold raw14296step3 raw14296step2; decide +kernel
      have hl : raw14296step2Labels = labelEmbedding1 ∘ raw14296step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14296step2 raw14296step2Labels raw14296step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

theorem canonical14297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14297 raw14297Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw14297 raw14297Labels = mixedMoment B raw14297step0 raw14297step0Labels := by
      have hz : ∀ j, raw14297 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14297step0 = (fun i j => raw14297 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14297step0 raw14297; decide +kernel
      have hl : raw14297step0Labels = raw14297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14297 raw14297Labels permutation590 hz
    mixedMoment B raw14297step0 raw14297step0Labels = mixedMoment B raw14297step1 raw14297step1Labels := by
      have ha : raw14297step1 = (fun i j => raw14297step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14297step1 raw14297step0; decide +kernel
      have hl : raw14297step1Labels = raw14297step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14297step0 raw14297step0Labels permutation50 permutation7
    mixedMoment B raw14297step1 raw14297step1Labels = mixedMoment B raw14297step2 raw14297step2Labels := by
      have ha : raw14297step2 = -raw14297step1 := by apply Matrix.ext; change ∀ i j, raw14297step2 i j = -(raw14297step1 i j); unfold raw14297step2 raw14297step1; decide +kernel
      have hl : raw14297step2Labels = raw14297step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14297step2 raw14297step2Labels = mixedMoment B raw14297step3 raw14297step3Labels := by
      have ha : raw14297step3 = raw14297step2 := by apply Matrix.ext; unfold raw14297step3 raw14297step2; decide +kernel
      have hl : raw14297step2Labels = labelEmbedding1 ∘ raw14297step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14297step2 raw14297step2Labels raw14297step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

theorem canonical14298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14298 raw14298Labels = mixedMoment B node1705 node1705Labels := by
  calc
    mixedMoment B raw14298 raw14298Labels = mixedMoment B raw14298step0 raw14298step0Labels := by
      have ha : raw14298step0 = (fun i j => raw14298 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14298step0 raw14298; decide +kernel
      have hl : raw14298step0Labels = raw14298Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14298 raw14298Labels permutation240 permutation7
    mixedMoment B raw14298step0 raw14298step0Labels = mixedMoment B raw14298step1 raw14298step1Labels := by
      have ha : raw14298step1 = -raw14298step0 := by apply Matrix.ext; change ∀ i j, raw14298step1 i j = -(raw14298step0 i j); unfold raw14298step1 raw14298step0; decide +kernel
      have hl : raw14298step1Labels = raw14298step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14298step1 raw14298step1Labels = mixedMoment B raw14298step2 raw14298step2Labels := by
      have ha : raw14298step2 = raw14298step1 := by apply Matrix.ext; unfold raw14298step2 raw14298step1; decide +kernel
      have hl : raw14298step1Labels = labelEmbedding1 ∘ raw14298step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14298step1 raw14298step1Labels raw14298step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1705 node1705Labels := by rfl

theorem canonical14299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14299 raw14299Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw14299 raw14299Labels = mixedMoment B raw14299step0 raw14299step0Labels := by
      have ha : raw14299step0 = (fun i j => raw14299 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14299step0 raw14299; decide +kernel
      have hl : raw14299step0Labels = raw14299Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14299 raw14299Labels permutation240 permutation7
    mixedMoment B raw14299step0 raw14299step0Labels = mixedMoment B raw14299step1 raw14299step1Labels := by
      have ha : raw14299step1 = -raw14299step0 := by apply Matrix.ext; change ∀ i j, raw14299step1 i j = -(raw14299step0 i j); unfold raw14299step1 raw14299step0; decide +kernel
      have hl : raw14299step1Labels = raw14299step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14299step1 raw14299step1Labels = mixedMoment B raw14299step2 raw14299step2Labels := by
      have ha : raw14299step2 = raw14299step1 := by apply Matrix.ext; unfold raw14299step2 raw14299step1; decide +kernel
      have hl : raw14299step1Labels = labelEmbedding1 ∘ raw14299step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14299step1 raw14299step1Labels raw14299step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2240 node2240Labels := by rfl

theorem canonical14300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14300 raw14300Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw14300 raw14300Labels = mixedMoment B raw14300step0 raw14300step0Labels := by
      have ha : raw14300step0 = (fun i j => raw14300 (permutation242 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14300step0 raw14300; decide +kernel
      have hl : raw14300step0Labels = raw14300Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14300 raw14300Labels permutation242 permutation7
    mixedMoment B raw14300step0 raw14300step0Labels = mixedMoment B raw14300step1 raw14300step1Labels := by
      have ha : raw14300step1 = -raw14300step0 := by apply Matrix.ext; change ∀ i j, raw14300step1 i j = -(raw14300step0 i j); unfold raw14300step1 raw14300step0; decide +kernel
      have hl : raw14300step1Labels = raw14300step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14300step1 raw14300step1Labels = mixedMoment B raw14300step2 raw14300step2Labels := by
      have ha : raw14300step2 = raw14300step1 := by apply Matrix.ext; unfold raw14300step2 raw14300step1; decide +kernel
      have hl : raw14300step1Labels = labelEmbedding1 ∘ raw14300step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14300step1 raw14300step1Labels raw14300step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2240 node2240Labels := by rfl

theorem canonical14301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14301 raw14301Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw14301 raw14301Labels = mixedMoment B raw14301step0 raw14301step0Labels := by
      have hz : ∀ j, raw14301 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14301step0 = (fun i j => raw14301 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14301step0 raw14301; decide +kernel
      have hl : raw14301step0Labels = raw14301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14301 raw14301Labels permutation520 hz
    mixedMoment B raw14301step0 raw14301step0Labels = mixedMoment B raw14301step1 raw14301step1Labels := by
      have ha : raw14301step1 = (fun i j => raw14301step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14301step1 raw14301step0; decide +kernel
      have hl : raw14301step1Labels = raw14301step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14301step0 raw14301step0Labels permutation50 permutation7
    mixedMoment B raw14301step1 raw14301step1Labels = mixedMoment B raw14301step2 raw14301step2Labels := by
      have ha : raw14301step2 = -raw14301step1 := by apply Matrix.ext; change ∀ i j, raw14301step2 i j = -(raw14301step1 i j); unfold raw14301step2 raw14301step1; decide +kernel
      have hl : raw14301step2Labels = raw14301step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14301step2 raw14301step2Labels = mixedMoment B raw14301step3 raw14301step3Labels := by
      have ha : raw14301step3 = raw14301step2 := by apply Matrix.ext; unfold raw14301step3 raw14301step2; decide +kernel
      have hl : raw14301step2Labels = labelEmbedding1 ∘ raw14301step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14301step2 raw14301step2Labels raw14301step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

theorem canonical14302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14302 raw14302Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw14302 raw14302Labels = mixedMoment B raw14302step0 raw14302step0Labels := by
      have hz : ∀ j, raw14302 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14302step0 = (fun i j => raw14302 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14302step0 raw14302; decide +kernel
      have hl : raw14302step0Labels = raw14302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14302 raw14302Labels permutation590 hz
    mixedMoment B raw14302step0 raw14302step0Labels = mixedMoment B raw14302step1 raw14302step1Labels := by
      have ha : raw14302step1 = (fun i j => raw14302step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14302step1 raw14302step0; decide +kernel
      have hl : raw14302step1Labels = raw14302step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14302step0 raw14302step0Labels permutation50 permutation7
    mixedMoment B raw14302step1 raw14302step1Labels = mixedMoment B raw14302step2 raw14302step2Labels := by
      have ha : raw14302step2 = -raw14302step1 := by apply Matrix.ext; change ∀ i j, raw14302step2 i j = -(raw14302step1 i j); unfold raw14302step2 raw14302step1; decide +kernel
      have hl : raw14302step2Labels = raw14302step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14302step2 raw14302step2Labels = mixedMoment B raw14302step3 raw14302step3Labels := by
      have ha : raw14302step3 = raw14302step2 := by apply Matrix.ext; unfold raw14302step3 raw14302step2; decide +kernel
      have hl : raw14302step2Labels = labelEmbedding1 ∘ raw14302step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14302step2 raw14302step2Labels raw14302step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

theorem canonical14303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14303 raw14303Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw14303 raw14303Labels = mixedMoment B raw14303step0 raw14303step0Labels := by
      have ha : raw14303step0 = (fun i j => raw14303 (permutation260 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14303step0 raw14303; decide +kernel
      have hl : raw14303step0Labels = raw14303Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14303 raw14303Labels permutation260 permutation7
    mixedMoment B raw14303step0 raw14303step0Labels = mixedMoment B raw14303step1 raw14303step1Labels := by
      have ha : raw14303step1 = -raw14303step0 := by apply Matrix.ext; change ∀ i j, raw14303step1 i j = -(raw14303step0 i j); unfold raw14303step1 raw14303step0; decide +kernel
      have hl : raw14303step1Labels = raw14303step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14303step1 raw14303step1Labels = mixedMoment B raw14303step2 raw14303step2Labels := by
      have ha : raw14303step2 = raw14303step1 := by apply Matrix.ext; unfold raw14303step2 raw14303step1; decide +kernel
      have hl : raw14303step1Labels = labelEmbedding1 ∘ raw14303step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14303step1 raw14303step1Labels raw14303step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

theorem canonical14304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14304 raw14304Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw14304 raw14304Labels = mixedMoment B raw14304step0 raw14304step0Labels := by
      have ha : raw14304step0 = (fun i j => raw14304 (permutation260 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14304step0 raw14304; decide +kernel
      have hl : raw14304step0Labels = raw14304Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14304 raw14304Labels permutation260 permutation7
    mixedMoment B raw14304step0 raw14304step0Labels = mixedMoment B raw14304step1 raw14304step1Labels := by
      have ha : raw14304step1 = -raw14304step0 := by apply Matrix.ext; change ∀ i j, raw14304step1 i j = -(raw14304step0 i j); unfold raw14304step1 raw14304step0; decide +kernel
      have hl : raw14304step1Labels = raw14304step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14304step1 raw14304step1Labels = mixedMoment B raw14304step2 raw14304step2Labels := by
      have ha : raw14304step2 = raw14304step1 := by apply Matrix.ext; unfold raw14304step2 raw14304step1; decide +kernel
      have hl : raw14304step1Labels = labelEmbedding1 ∘ raw14304step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14304step1 raw14304step1Labels raw14304step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

theorem canonical14305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14305 raw14305Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw14305 raw14305Labels = mixedMoment B raw14305step0 raw14305step0Labels := by
      have ha : raw14305step0 = (fun i j => raw14305 (permutation262 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14305step0 raw14305; decide +kernel
      have hl : raw14305step0Labels = raw14305Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14305 raw14305Labels permutation262 permutation7
    mixedMoment B raw14305step0 raw14305step0Labels = mixedMoment B raw14305step1 raw14305step1Labels := by
      have ha : raw14305step1 = -raw14305step0 := by apply Matrix.ext; change ∀ i j, raw14305step1 i j = -(raw14305step0 i j); unfold raw14305step1 raw14305step0; decide +kernel
      have hl : raw14305step1Labels = raw14305step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14305step1 raw14305step1Labels = mixedMoment B raw14305step2 raw14305step2Labels := by
      have ha : raw14305step2 = raw14305step1 := by apply Matrix.ext; unfold raw14305step2 raw14305step1; decide +kernel
      have hl : raw14305step1Labels = labelEmbedding1 ∘ raw14305step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14305step1 raw14305step1Labels raw14305step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

theorem canonical14306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14306 raw14306Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw14306 raw14306Labels = mixedMoment B raw14306step0 raw14306step0Labels := by
      have hz : ∀ j, raw14306 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14306step0 = (fun i j => raw14306 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14306step0 raw14306; decide +kernel
      have hl : raw14306step0Labels = raw14306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14306 raw14306Labels permutation590 hz
    mixedMoment B raw14306step0 raw14306step0Labels = mixedMoment B raw14306step1 raw14306step1Labels := by
      have ha : raw14306step1 = (fun i j => raw14306step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14306step1 raw14306step0; decide +kernel
      have hl : raw14306step1Labels = raw14306step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14306step0 raw14306step0Labels permutation50 permutation7
    mixedMoment B raw14306step1 raw14306step1Labels = mixedMoment B raw14306step2 raw14306step2Labels := by
      have ha : raw14306step2 = -raw14306step1 := by apply Matrix.ext; change ∀ i j, raw14306step2 i j = -(raw14306step1 i j); unfold raw14306step2 raw14306step1; decide +kernel
      have hl : raw14306step2Labels = raw14306step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14306step2 raw14306step2Labels = mixedMoment B raw14306step3 raw14306step3Labels := by
      have ha : raw14306step3 = raw14306step2 := by apply Matrix.ext; unfold raw14306step3 raw14306step2; decide +kernel
      have hl : raw14306step2Labels = labelEmbedding1 ∘ raw14306step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14306step2 raw14306step2Labels raw14306step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

theorem canonical14307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14307 raw14307Labels = mixedMoment B node2252 node2252Labels := by
  calc
    mixedMoment B raw14307 raw14307Labels = mixedMoment B raw14307step0 raw14307step0Labels := by
      have ha : raw14307step0 = (fun i j => raw14307 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14307step0 raw14307; decide +kernel
      have hl : raw14307step0Labels = raw14307Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14307 raw14307Labels permutation240 permutation7
    mixedMoment B raw14307step0 raw14307step0Labels = mixedMoment B raw14307step1 raw14307step1Labels := by
      have ha : raw14307step1 = -raw14307step0 := by apply Matrix.ext; change ∀ i j, raw14307step1 i j = -(raw14307step0 i j); unfold raw14307step1 raw14307step0; decide +kernel
      have hl : raw14307step1Labels = raw14307step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14307step1 raw14307step1Labels = mixedMoment B raw14307step2 raw14307step2Labels := by
      have ha : raw14307step2 = raw14307step1 := by apply Matrix.ext; unfold raw14307step2 raw14307step1; decide +kernel
      have hl : raw14307step1Labels = labelEmbedding1 ∘ raw14307step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14307step1 raw14307step1Labels raw14307step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2252 node2252Labels := by rfl

theorem canonical14308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14308 raw14308Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw14308 raw14308Labels = mixedMoment B raw14308step0 raw14308step0Labels := by
      have ha : raw14308step0 = (fun i j => raw14308 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14308step0 raw14308; decide +kernel
      have hl : raw14308step0Labels = raw14308Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14308 raw14308Labels permutation155 permutation3
    mixedMoment B raw14308step0 raw14308step0Labels = mixedMoment B raw14308step1 raw14308step1Labels := by
      have ha : raw14308step1 = raw14308step0 := by apply Matrix.ext; unfold raw14308step1 raw14308step0; decide +kernel
      have hl : raw14308step0Labels = labelEmbedding6 ∘ raw14308step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14308step0 raw14308step0Labels raw14308step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical14309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14309 raw14309Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw14309 raw14309Labels = mixedMoment B raw14309step0 raw14309step0Labels := by
      have ha : raw14309step0 = (fun i j => raw14309 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14309step0 raw14309; decide +kernel
      have hl : raw14309step0Labels = raw14309Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14309 raw14309Labels permutation179 permutation3
    mixedMoment B raw14309step0 raw14309step0Labels = mixedMoment B raw14309step1 raw14309step1Labels := by
      have ha : raw14309step1 = raw14309step0 := by apply Matrix.ext; unfold raw14309step1 raw14309step0; decide +kernel
      have hl : raw14309step0Labels = labelEmbedding6 ∘ raw14309step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14309step0 raw14309step0Labels raw14309step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical14310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14310 raw14310Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw14310 raw14310Labels = mixedMoment B raw14310step0 raw14310step0Labels := by
      have ha : raw14310step0 = (fun i j => raw14310 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14310step0 raw14310; decide +kernel
      have hl : raw14310step0Labels = raw14310Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14310 raw14310Labels permutation240 permutation5
    mixedMoment B raw14310step0 raw14310step0Labels = mixedMoment B raw14310step1 raw14310step1Labels := by
      have ha : raw14310step1 = -raw14310step0 := by apply Matrix.ext; change ∀ i j, raw14310step1 i j = -(raw14310step0 i j); unfold raw14310step1 raw14310step0; decide +kernel
      have hl : raw14310step1Labels = raw14310step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14310step1 raw14310step1Labels = mixedMoment B raw14310step2 raw14310step2Labels := by
      have ha : raw14310step2 = raw14310step1 := by apply Matrix.ext; unfold raw14310step2 raw14310step1; decide +kernel
      have hl : raw14310step1Labels = labelEmbedding8 ∘ raw14310step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14310step1 raw14310step1Labels raw14310step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical14311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14311 raw14311Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw14311 raw14311Labels = mixedMoment B raw14311step0 raw14311step0Labels := by
      have ha : raw14311step0 = (fun i j => raw14311 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14311step0 raw14311; decide +kernel
      have hl : raw14311step0Labels = raw14311Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14311 raw14311Labels permutation260 permutation5
    mixedMoment B raw14311step0 raw14311step0Labels = mixedMoment B raw14311step1 raw14311step1Labels := by
      have ha : raw14311step1 = -raw14311step0 := by apply Matrix.ext; change ∀ i j, raw14311step1 i j = -(raw14311step0 i j); unfold raw14311step1 raw14311step0; decide +kernel
      have hl : raw14311step1Labels = raw14311step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14311step1 raw14311step1Labels = mixedMoment B raw14311step2 raw14311step2Labels := by
      have ha : raw14311step2 = raw14311step1 := by apply Matrix.ext; unfold raw14311step2 raw14311step1; decide +kernel
      have hl : raw14311step1Labels = labelEmbedding8 ∘ raw14311step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14311step1 raw14311step1Labels raw14311step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical14312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14312 raw14312Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw14312 raw14312Labels = mixedMoment B raw14312step0 raw14312step0Labels := by
      have ha : raw14312step0 = (fun i j => raw14312 (permutation243 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14312step0 raw14312; decide +kernel
      have hl : raw14312step0Labels = raw14312Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14312 raw14312Labels permutation243 permutation5
    mixedMoment B raw14312step0 raw14312step0Labels = mixedMoment B raw14312step1 raw14312step1Labels := by
      have ha : raw14312step1 = -raw14312step0 := by apply Matrix.ext; change ∀ i j, raw14312step1 i j = -(raw14312step0 i j); unfold raw14312step1 raw14312step0; decide +kernel
      have hl : raw14312step1Labels = raw14312step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14312step1 raw14312step1Labels = mixedMoment B raw14312step2 raw14312step2Labels := by
      have ha : raw14312step2 = raw14312step1 := by apply Matrix.ext; unfold raw14312step2 raw14312step1; decide +kernel
      have hl : raw14312step1Labels = labelEmbedding8 ∘ raw14312step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14312step1 raw14312step1Labels raw14312step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

theorem canonical14313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14313 raw14313Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw14313 raw14313Labels = mixedMoment B raw14313step0 raw14313step0Labels := by
      have ha : raw14313step0 = (fun i j => raw14313 (permutation193 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14313step0 raw14313; decide +kernel
      have hl : raw14313step0Labels = raw14313Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14313 raw14313Labels permutation193 permutation3
    mixedMoment B raw14313step0 raw14313step0Labels = mixedMoment B raw14313step1 raw14313step1Labels := by
      have ha : raw14313step1 = raw14313step0 := by apply Matrix.ext; unfold raw14313step1 raw14313step0; decide +kernel
      have hl : raw14313step0Labels = labelEmbedding6 ∘ raw14313step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14313step0 raw14313step0Labels raw14313step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

theorem canonical14314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14314 raw14314Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw14314 raw14314Labels = mixedMoment B raw14314step0 raw14314step0Labels := by
      have ha : raw14314step0 = (fun i j => raw14314 (permutation243 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14314step0 raw14314; decide +kernel
      have hl : raw14314step0Labels = raw14314Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14314 raw14314Labels permutation243 permutation5
    mixedMoment B raw14314step0 raw14314step0Labels = mixedMoment B raw14314step1 raw14314step1Labels := by
      have ha : raw14314step1 = -raw14314step0 := by apply Matrix.ext; change ∀ i j, raw14314step1 i j = -(raw14314step0 i j); unfold raw14314step1 raw14314step0; decide +kernel
      have hl : raw14314step1Labels = raw14314step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14314step1 raw14314step1Labels = mixedMoment B raw14314step2 raw14314step2Labels := by
      have ha : raw14314step2 = raw14314step1 := by apply Matrix.ext; unfold raw14314step2 raw14314step1; decide +kernel
      have hl : raw14314step1Labels = labelEmbedding8 ∘ raw14314step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14314step1 raw14314step1Labels raw14314step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical14315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14315 raw14315Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw14315 raw14315Labels = mixedMoment B raw14315step0 raw14315step0Labels := by
      have ha : raw14315step0 = (fun i j => raw14315 (permutation263 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14315step0 raw14315; decide +kernel
      have hl : raw14315step0Labels = raw14315Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14315 raw14315Labels permutation263 permutation5
    mixedMoment B raw14315step0 raw14315step0Labels = mixedMoment B raw14315step1 raw14315step1Labels := by
      have ha : raw14315step1 = -raw14315step0 := by apply Matrix.ext; change ∀ i j, raw14315step1 i j = -(raw14315step0 i j); unfold raw14315step1 raw14315step0; decide +kernel
      have hl : raw14315step1Labels = raw14315step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14315step1 raw14315step1Labels = mixedMoment B raw14315step2 raw14315step2Labels := by
      have ha : raw14315step2 = raw14315step1 := by apply Matrix.ext; unfold raw14315step2 raw14315step1; decide +kernel
      have hl : raw14315step1Labels = labelEmbedding8 ∘ raw14315step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14315step1 raw14315step1Labels raw14315step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical14316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14316 raw14316Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw14316 raw14316Labels = mixedMoment B raw14316step0 raw14316step0Labels := by
      have ha : raw14316step0 = (fun i j => raw14316 (permutation241 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14316step0 raw14316; decide +kernel
      have hl : raw14316step0Labels = raw14316Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14316 raw14316Labels permutation241 permutation5
    mixedMoment B raw14316step0 raw14316step0Labels = mixedMoment B raw14316step1 raw14316step1Labels := by
      have ha : raw14316step1 = -raw14316step0 := by apply Matrix.ext; change ∀ i j, raw14316step1 i j = -(raw14316step0 i j); unfold raw14316step1 raw14316step0; decide +kernel
      have hl : raw14316step1Labels = raw14316step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14316step1 raw14316step1Labels = mixedMoment B raw14316step2 raw14316step2Labels := by
      have ha : raw14316step2 = raw14316step1 := by apply Matrix.ext; unfold raw14316step2 raw14316step1; decide +kernel
      have hl : raw14316step1Labels = labelEmbedding8 ∘ raw14316step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14316step1 raw14316step1Labels raw14316step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

theorem canonical14317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14317 raw14317Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw14317 raw14317Labels = mixedMoment B raw14317step0 raw14317step0Labels := by
      have ha : raw14317step0 = (fun i j => raw14317 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14317step0 raw14317; decide +kernel
      have hl : raw14317step0Labels = raw14317Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14317 raw14317Labels permutation169 permutation3
    mixedMoment B raw14317step0 raw14317step0Labels = mixedMoment B raw14317step1 raw14317step1Labels := by
      have ha : raw14317step1 = raw14317step0 := by apply Matrix.ext; unfold raw14317step1 raw14317step0; decide +kernel
      have hl : raw14317step0Labels = labelEmbedding6 ∘ raw14317step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14317step0 raw14317step0Labels raw14317step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

theorem canonical14318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14318 raw14318Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw14318 raw14318Labels = mixedMoment B raw14318step0 raw14318step0Labels := by
      have ha : raw14318step0 = (fun i j => raw14318 (permutation241 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14318step0 raw14318; decide +kernel
      have hl : raw14318step0Labels = raw14318Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14318 raw14318Labels permutation241 permutation5
    mixedMoment B raw14318step0 raw14318step0Labels = mixedMoment B raw14318step1 raw14318step1Labels := by
      have ha : raw14318step1 = -raw14318step0 := by apply Matrix.ext; change ∀ i j, raw14318step1 i j = -(raw14318step0 i j); unfold raw14318step1 raw14318step0; decide +kernel
      have hl : raw14318step1Labels = raw14318step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14318step1 raw14318step1Labels = mixedMoment B raw14318step2 raw14318step2Labels := by
      have ha : raw14318step2 = raw14318step1 := by apply Matrix.ext; unfold raw14318step2 raw14318step1; decide +kernel
      have hl : raw14318step1Labels = labelEmbedding8 ∘ raw14318step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14318step1 raw14318step1Labels raw14318step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical14319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14319 raw14319Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw14319 raw14319Labels = mixedMoment B raw14319step0 raw14319step0Labels := by
      have ha : raw14319step0 = (fun i j => raw14319 (permutation261 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14319step0 raw14319; decide +kernel
      have hl : raw14319step0Labels = raw14319Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14319 raw14319Labels permutation261 permutation5
    mixedMoment B raw14319step0 raw14319step0Labels = mixedMoment B raw14319step1 raw14319step1Labels := by
      have ha : raw14319step1 = -raw14319step0 := by apply Matrix.ext; change ∀ i j, raw14319step1 i j = -(raw14319step0 i j); unfold raw14319step1 raw14319step0; decide +kernel
      have hl : raw14319step1Labels = raw14319step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14319step1 raw14319step1Labels = mixedMoment B raw14319step2 raw14319step2Labels := by
      have ha : raw14319step2 = raw14319step1 := by apply Matrix.ext; unfold raw14319step2 raw14319step1; decide +kernel
      have hl : raw14319step1Labels = labelEmbedding8 ∘ raw14319step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14319step1 raw14319step1Labels raw14319step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical14320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14320 raw14320Labels = mixedMoment B node4248 node4248Labels := by
  calc
    mixedMoment B raw14320 raw14320Labels = mixedMoment B raw14320step0 raw14320step0Labels := by
      have ha : raw14320step0 = (fun i j => raw14320 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14320step0 raw14320; decide +kernel
      have hl : raw14320step0Labels = raw14320Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14320 raw14320Labels permutation155 permutation3
    mixedMoment B raw14320step0 raw14320step0Labels = mixedMoment B raw14320step1 raw14320step1Labels := by
      have ha : raw14320step1 = raw14320step0 := by apply Matrix.ext; unfold raw14320step1 raw14320step0; decide +kernel
      have hl : raw14320step0Labels = labelEmbedding6 ∘ raw14320step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14320step0 raw14320step0Labels raw14320step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4248 node4248Labels := by rfl

theorem canonical14321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14321 raw14321Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw14321 raw14321Labels = mixedMoment B raw14321step0 raw14321step0Labels := by
      have ha : raw14321step0 = (fun i j => raw14321 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14321step0 raw14321; decide +kernel
      have hl : raw14321step0Labels = raw14321Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14321 raw14321Labels permutation155 permutation3
    mixedMoment B raw14321step0 raw14321step0Labels = mixedMoment B raw14321step1 raw14321step1Labels := by
      have ha : raw14321step1 = raw14321step0 := by apply Matrix.ext; unfold raw14321step1 raw14321step0; decide +kernel
      have hl : raw14321step0Labels = labelEmbedding6 ∘ raw14321step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14321step0 raw14321step0Labels raw14321step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

theorem canonical14322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14322 raw14322Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw14322 raw14322Labels = mixedMoment B raw14322step0 raw14322step0Labels := by
      have ha : raw14322step0 = (fun i j => raw14322 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14322step0 raw14322; decide +kernel
      have hl : raw14322step0Labels = raw14322Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14322 raw14322Labels permutation179 permutation3
    mixedMoment B raw14322step0 raw14322step0Labels = mixedMoment B raw14322step1 raw14322step1Labels := by
      have ha : raw14322step1 = raw14322step0 := by apply Matrix.ext; unfold raw14322step1 raw14322step0; decide +kernel
      have hl : raw14322step0Labels = labelEmbedding6 ∘ raw14322step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14322step0 raw14322step0Labels raw14322step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

theorem canonical14323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14323 raw14323Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw14323 raw14323Labels = mixedMoment B raw14323step0 raw14323step0Labels := by
      have ha : raw14323step0 = (fun i j => raw14323 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14323step0 raw14323; decide +kernel
      have hl : raw14323step0Labels = raw14323Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14323 raw14323Labels permutation240 permutation5
    mixedMoment B raw14323step0 raw14323step0Labels = mixedMoment B raw14323step1 raw14323step1Labels := by
      have ha : raw14323step1 = -raw14323step0 := by apply Matrix.ext; change ∀ i j, raw14323step1 i j = -(raw14323step0 i j); unfold raw14323step1 raw14323step0; decide +kernel
      have hl : raw14323step1Labels = raw14323step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14323step1 raw14323step1Labels = mixedMoment B raw14323step2 raw14323step2Labels := by
      have ha : raw14323step2 = raw14323step1 := by apply Matrix.ext; unfold raw14323step2 raw14323step1; decide +kernel
      have hl : raw14323step1Labels = labelEmbedding8 ∘ raw14323step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14323step1 raw14323step1Labels raw14323step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

theorem canonical14324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14324 raw14324Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw14324 raw14324Labels = mixedMoment B raw14324step0 raw14324step0Labels := by
      have ha : raw14324step0 = (fun i j => raw14324 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14324step0 raw14324; decide +kernel
      have hl : raw14324step0Labels = raw14324Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14324 raw14324Labels permutation260 permutation5
    mixedMoment B raw14324step0 raw14324step0Labels = mixedMoment B raw14324step1 raw14324step1Labels := by
      have ha : raw14324step1 = -raw14324step0 := by apply Matrix.ext; change ∀ i j, raw14324step1 i j = -(raw14324step0 i j); unfold raw14324step1 raw14324step0; decide +kernel
      have hl : raw14324step1Labels = raw14324step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14324step1 raw14324step1Labels = mixedMoment B raw14324step2 raw14324step2Labels := by
      have ha : raw14324step2 = raw14324step1 := by apply Matrix.ext; unfold raw14324step2 raw14324step1; decide +kernel
      have hl : raw14324step1Labels = labelEmbedding8 ∘ raw14324step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14324step1 raw14324step1Labels raw14324step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

theorem canonical14325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14325 raw14325Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw14325 raw14325Labels = mixedMoment B raw14325step0 raw14325step0Labels := by
      have ha : raw14325step0 = (fun i j => raw14325 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14325step0 raw14325; decide +kernel
      have hl : raw14325step0Labels = raw14325Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14325 raw14325Labels permutation156 permutation3
    mixedMoment B raw14325step0 raw14325step0Labels = mixedMoment B raw14325step1 raw14325step1Labels := by
      have ha : raw14325step1 = raw14325step0 := by apply Matrix.ext; unfold raw14325step1 raw14325step0; decide +kernel
      have hl : raw14325step0Labels = labelEmbedding6 ∘ raw14325step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14325step0 raw14325step0Labels raw14325step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

theorem canonical14326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14326 raw14326Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw14326 raw14326Labels = mixedMoment B raw14326step0 raw14326step0Labels := by
      have ha : raw14326step0 = (fun i j => raw14326 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14326step0 raw14326; decide +kernel
      have hl : raw14326step0Labels = raw14326Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14326 raw14326Labels permutation156 permutation3
    mixedMoment B raw14326step0 raw14326step0Labels = mixedMoment B raw14326step1 raw14326step1Labels := by
      have ha : raw14326step1 = raw14326step0 := by apply Matrix.ext; unfold raw14326step1 raw14326step0; decide +kernel
      have hl : raw14326step0Labels = labelEmbedding6 ∘ raw14326step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14326step0 raw14326step0Labels raw14326step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical14327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14327 raw14327Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw14327 raw14327Labels = mixedMoment B raw14327step0 raw14327step0Labels := by
      have ha : raw14327step0 = (fun i j => raw14327 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14327step0 raw14327; decide +kernel
      have hl : raw14327step0Labels = raw14327Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14327 raw14327Labels permutation180 permutation3
    mixedMoment B raw14327step0 raw14327step0Labels = mixedMoment B raw14327step1 raw14327step1Labels := by
      have ha : raw14327step1 = raw14327step0 := by apply Matrix.ext; unfold raw14327step1 raw14327step0; decide +kernel
      have hl : raw14327step0Labels = labelEmbedding6 ∘ raw14327step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14327step0 raw14327step0Labels raw14327step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical14328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14328 raw14328Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw14328 raw14328Labels = mixedMoment B raw14328step0 raw14328step0Labels := by
      have ha : raw14328step0 = (fun i j => raw14328 (permutation246 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14328step0 raw14328; decide +kernel
      have hl : raw14328step0Labels = raw14328Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14328 raw14328Labels permutation246 permutation5
    mixedMoment B raw14328step0 raw14328step0Labels = mixedMoment B raw14328step1 raw14328step1Labels := by
      have ha : raw14328step1 = -raw14328step0 := by apply Matrix.ext; change ∀ i j, raw14328step1 i j = -(raw14328step0 i j); unfold raw14328step1 raw14328step0; decide +kernel
      have hl : raw14328step1Labels = raw14328step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14328step1 raw14328step1Labels = mixedMoment B raw14328step2 raw14328step2Labels := by
      have ha : raw14328step2 = raw14328step1 := by apply Matrix.ext; unfold raw14328step2 raw14328step1; decide +kernel
      have hl : raw14328step1Labels = labelEmbedding8 ∘ raw14328step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14328step1 raw14328step1Labels raw14328step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

theorem canonical14329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14329 raw14329Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw14329 raw14329Labels = mixedMoment B raw14329step0 raw14329step0Labels := by
      have hz : ∀ j, raw14329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14329step0 = (fun i j => raw14329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14329step0 raw14329; decide +kernel
      have hl : raw14329step0Labels = raw14329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14329 raw14329Labels permutation434 hz
    mixedMoment B raw14329step0 raw14329step0Labels = mixedMoment B raw14329step1 raw14329step1Labels := by
      have ha : raw14329step1 = (fun i j => raw14329step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14329step1 raw14329step0; decide +kernel
      have hl : raw14329step1Labels = raw14329step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14329step0 raw14329step0Labels permutation32 permutation3
    mixedMoment B raw14329step1 raw14329step1Labels = mixedMoment B raw14329step2 raw14329step2Labels := by
      have ha : raw14329step2 = raw14329step1 := by apply Matrix.ext; unfold raw14329step2 raw14329step1; decide +kernel
      have hl : raw14329step1Labels = labelEmbedding6 ∘ raw14329step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14329step1 raw14329step1Labels raw14329step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

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

theorem canonical1731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1731 raw1731Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw1731 raw1731Labels = mixedMoment B raw1731step0 raw1731step0Labels := by
      have ha : raw1731step0 = (fun i j => raw1731 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1731step0 raw1731; decide +kernel
      have hl : raw1731step0Labels = raw1731Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1731 raw1731Labels permutation152 permutation4
    mixedMoment B raw1731step0 raw1731step0Labels = mixedMoment B raw1731step1 raw1731step1Labels := by
      have ha : raw1731step1 = raw1731step0 := by apply Matrix.ext; unfold raw1731step1 raw1731step0; decide +kernel
      have hl : raw1731step0Labels = labelEmbedding7 ∘ raw1731step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1731step0 raw1731step0Labels raw1731step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

theorem canonical1732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1732 raw1732Labels = mixedMoment B node2019 node2019Labels := by
  calc
    mixedMoment B raw1732 raw1732Labels = mixedMoment B raw1732step0 raw1732step0Labels := by
      have ha : raw1732step0 = (fun i j => raw1732 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1732step0 raw1732; decide +kernel
      have hl : raw1732step0Labels = raw1732Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1732 raw1732Labels permutation152 permutation4
    _ = mixedMoment B node2019 node2019Labels := by rfl

theorem canonical1733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1733 raw1733Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw1733 raw1733Labels = mixedMoment B raw1733step0 raw1733step0Labels := by
      have ha : raw1733step0 = (fun i j => raw1733 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1733step0 raw1733; decide +kernel
      have hl : raw1733step0Labels = raw1733Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1733 raw1733Labels permutation160 permutation6
    mixedMoment B raw1733step0 raw1733step0Labels = mixedMoment B raw1733step1 raw1733step1Labels := by
      have ha : raw1733step1 = -raw1733step0 := by apply Matrix.ext; change ∀ i j, raw1733step1 i j = -(raw1733step0 i j); unfold raw1733step1 raw1733step0; decide +kernel
      have hl : raw1733step1Labels = raw1733step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1733step1 raw1733step1Labels = mixedMoment B raw1733step2 raw1733step2Labels := by
      have ha : raw1733step2 = raw1733step1 := by apply Matrix.ext; unfold raw1733step2 raw1733step1; decide +kernel
      have hl : raw1733step1Labels = labelEmbedding1 ∘ raw1733step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1733step1 raw1733step1Labels raw1733step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2190 node2190Labels := by rfl

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

theorem canonical1761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1761 raw1761Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw1761 raw1761Labels = mixedMoment B raw1761step0 raw1761step0Labels := by
      have ha : raw1761step0 = (fun i j => raw1761 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1761step0 raw1761; decide +kernel
      have hl : raw1761step0Labels = raw1761Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1761 raw1761Labels permutation152 permutation4
    mixedMoment B raw1761step0 raw1761step0Labels = mixedMoment B raw1761step1 raw1761step1Labels := by
      have ha : raw1761step1 = raw1761step0 := by apply Matrix.ext; unfold raw1761step1 raw1761step0; decide +kernel
      have hl : raw1761step0Labels = labelEmbedding7 ∘ raw1761step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1761step0 raw1761step0Labels raw1761step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

theorem canonical1762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1762 raw1762Labels = mixedMoment B node2051 node2051Labels := by
  calc
    mixedMoment B raw1762 raw1762Labels = mixedMoment B raw1762step0 raw1762step0Labels := by
      have ha : raw1762step0 = (fun i j => raw1762 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1762step0 raw1762; decide +kernel
      have hl : raw1762step0Labels = raw1762Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1762 raw1762Labels permutation152 permutation4
    _ = mixedMoment B node2051 node2051Labels := by rfl

theorem canonical1763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1763 raw1763Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw1763 raw1763Labels = mixedMoment B raw1763step0 raw1763step0Labels := by
      have ha : raw1763step0 = (fun i j => raw1763 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1763step0 raw1763; decide +kernel
      have hl : raw1763step0Labels = raw1763Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1763 raw1763Labels permutation152 permutation6
    mixedMoment B raw1763step0 raw1763step0Labels = mixedMoment B raw1763step1 raw1763step1Labels := by
      have ha : raw1763step1 = -raw1763step0 := by apply Matrix.ext; change ∀ i j, raw1763step1 i j = -(raw1763step0 i j); unfold raw1763step1 raw1763step0; decide +kernel
      have hl : raw1763step1Labels = raw1763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1763step1 raw1763step1Labels = mixedMoment B raw1763step2 raw1763step2Labels := by
      have ha : raw1763step2 = raw1763step1 := by apply Matrix.ext; unfold raw1763step2 raw1763step1; decide +kernel
      have hl : raw1763step1Labels = labelEmbedding1 ∘ raw1763step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1763step1 raw1763step1Labels raw1763step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2191 node2191Labels := by rfl

theorem canonical1788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1788 raw1788Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw1788 raw1788Labels = mixedMoment B raw1788step0 raw1788step0Labels := by
      have ha : raw1788step0 = (fun i j => raw1788 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1788step0 raw1788; decide +kernel
      have hl : raw1788step0Labels = raw1788Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1788 raw1788Labels permutation152 permutation4
    mixedMoment B raw1788step0 raw1788step0Labels = mixedMoment B raw1788step1 raw1788step1Labels := by
      have ha : raw1788step1 = raw1788step0 := by apply Matrix.ext; unfold raw1788step1 raw1788step0; decide +kernel
      have hl : raw1788step0Labels = labelEmbedding7 ∘ raw1788step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1788step0 raw1788step0Labels raw1788step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

theorem canonical1789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1789 raw1789Labels = mixedMoment B node2105 node2105Labels := by
  calc
    mixedMoment B raw1789 raw1789Labels = mixedMoment B raw1789step0 raw1789step0Labels := by
      have ha : raw1789step0 = (fun i j => raw1789 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1789step0 raw1789; decide +kernel
      have hl : raw1789step0Labels = raw1789Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1789 raw1789Labels permutation152 permutation4
    _ = mixedMoment B node2105 node2105Labels := by rfl

theorem canonical1790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1790 raw1790Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw1790 raw1790Labels = mixedMoment B raw1790step0 raw1790step0Labels := by
      have ha : raw1790step0 = (fun i j => raw1790 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1790step0 raw1790; decide +kernel
      have hl : raw1790step0Labels = raw1790Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1790 raw1790Labels permutation182 permutation6
    mixedMoment B raw1790step0 raw1790step0Labels = mixedMoment B raw1790step1 raw1790step1Labels := by
      have ha : raw1790step1 = -raw1790step0 := by apply Matrix.ext; change ∀ i j, raw1790step1 i j = -(raw1790step0 i j); unfold raw1790step1 raw1790step0; decide +kernel
      have hl : raw1790step1Labels = raw1790step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1790step1 raw1790step1Labels = mixedMoment B raw1790step2 raw1790step2Labels := by
      have ha : raw1790step2 = raw1790step1 := by apply Matrix.ext; unfold raw1790step2 raw1790step1; decide +kernel
      have hl : raw1790step1Labels = labelEmbedding1 ∘ raw1790step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1790step1 raw1790step1Labels raw1790step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2241 node2241Labels := by rfl

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

theorem canonical1815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1815 raw1815Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw1815 raw1815Labels = mixedMoment B raw1815step0 raw1815step0Labels := by
      have ha : raw1815step0 = (fun i j => raw1815 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1815step0 raw1815; decide +kernel
      have hl : raw1815step0Labels = raw1815Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1815 raw1815Labels permutation32 permutation4
    mixedMoment B raw1815step0 raw1815step0Labels = mixedMoment B raw1815step1 raw1815step1Labels := by
      have ha : raw1815step1 = raw1815step0 := by apply Matrix.ext; unfold raw1815step1 raw1815step0; decide +kernel
      have hl : raw1815step0Labels = labelEmbedding7 ∘ raw1815step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1815step0 raw1815step0Labels raw1815step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical1816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1816 raw1816Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw1816 raw1816Labels = mixedMoment B raw1816step0 raw1816step0Labels := by
      have ha : raw1816step0 = (fun i j => raw1816 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1816step0 raw1816; decide +kernel
      have hl : raw1816step0Labels = raw1816Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1816 raw1816Labels permutation32 permutation4
    _ = mixedMoment B node2244 node2244Labels := by rfl

theorem canonical1817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1817 raw1817Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw1817 raw1817Labels = mixedMoment B raw1817step0 raw1817step0Labels := by
      have ha : raw1817step0 = (fun i j => raw1817 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1817step0 raw1817; decide +kernel
      have hl : raw1817step0Labels = raw1817Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1817 raw1817Labels permutation44 permutation6
    mixedMoment B raw1817step0 raw1817step0Labels = mixedMoment B raw1817step1 raw1817step1Labels := by
      have ha : raw1817step1 = -raw1817step0 := by apply Matrix.ext; change ∀ i j, raw1817step1 i j = -(raw1817step0 i j); unfold raw1817step1 raw1817step0; decide +kernel
      have hl : raw1817step1Labels = raw1817step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1817step1 raw1817step1Labels = mixedMoment B raw1817step2 raw1817step2Labels := by
      have ha : raw1817step2 = raw1817step1 := by apply Matrix.ext; unfold raw1817step2 raw1817step1; decide +kernel
      have hl : raw1817step1Labels = labelEmbedding1 ∘ raw1817step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1817step1 raw1817step1Labels raw1817step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

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

theorem canonical2253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2253 raw2253Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw2253 raw2253Labels = mixedMoment B raw2253step0 raw2253step0Labels := by
      have ha : raw2253step0 = (fun i j => raw2253 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2253step0 raw2253; decide +kernel
      have hl : raw2253step0Labels = raw2253Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2253 raw2253Labels permutation32 permutation4
    mixedMoment B raw2253step0 raw2253step0Labels = mixedMoment B raw2253step1 raw2253step1Labels := by
      have ha : raw2253step1 = raw2253step0 := by apply Matrix.ext; unfold raw2253step1 raw2253step0; decide +kernel
      have hl : raw2253step0Labels = labelEmbedding7 ∘ raw2253step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2253step0 raw2253step0Labels raw2253step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

theorem canonical2254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2254 raw2254Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw2254 raw2254Labels = mixedMoment B raw2254step0 raw2254step0Labels := by
      have ha : raw2254step0 = (fun i j => raw2254 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2254step0 raw2254; decide +kernel
      have hl : raw2254step0Labels = raw2254Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2254 raw2254Labels permutation32 permutation4
    _ = mixedMoment B node2684 node2684Labels := by rfl

theorem canonical2255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2255 raw2255Labels = mixedMoment B node3394 node3394Labels := by
  calc
    mixedMoment B raw2255 raw2255Labels = mixedMoment B raw2255step0 raw2255step0Labels := by
      have ha : raw2255step0 = (fun i j => raw2255 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2255step0 raw2255; decide +kernel
      have hl : raw2255step0Labels = raw2255Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2255 raw2255Labels permutation32 permutation6
    mixedMoment B raw2255step0 raw2255step0Labels = mixedMoment B raw2255step1 raw2255step1Labels := by
      have ha : raw2255step1 = -raw2255step0 := by apply Matrix.ext; change ∀ i j, raw2255step1 i j = -(raw2255step0 i j); unfold raw2255step1 raw2255step0; decide +kernel
      have hl : raw2255step1Labels = raw2255step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2255step1 raw2255step1Labels = mixedMoment B raw2255step2 raw2255step2Labels := by
      have ha : raw2255step2 = raw2255step1 := by apply Matrix.ext; unfold raw2255step2 raw2255step1; decide +kernel
      have hl : raw2255step1Labels = labelEmbedding1 ∘ raw2255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2255step1 raw2255step1Labels raw2255step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3394 node3394Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5431 raw5431Labels = mixedMoment B node5283 node5283Labels := by
  calc
    mixedMoment B raw5431 raw5431Labels = mixedMoment B raw5431step0 raw5431step0Labels := by
      have ha : raw5431step0 = (fun i j => raw5431 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5431step0 raw5431; decide +kernel
      have hl : raw5431step0Labels = raw5431Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5431 raw5431Labels permutation240 permutation7
    mixedMoment B raw5431step0 raw5431step0Labels = mixedMoment B raw5431step1 raw5431step1Labels := by
      have ha : raw5431step1 = -raw5431step0 := by apply Matrix.ext; change ∀ i j, raw5431step1 i j = -(raw5431step0 i j); unfold raw5431step1 raw5431step0; decide +kernel
      have hl : raw5431step1Labels = raw5431step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5431step1 raw5431step1Labels = mixedMoment B raw5431step2 raw5431step2Labels := by
      have ha : raw5431step2 = raw5431step1 := by apply Matrix.ext; unfold raw5431step2 raw5431step1; decide +kernel
      have hl : raw5431step1Labels = labelEmbedding10 ∘ raw5431step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5431step1 raw5431step1Labels raw5431step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5283 node5283Labels := by rfl

theorem canonical5436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5436 raw5436Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw5436 raw5436Labels = mixedMoment B raw5436step0 raw5436step0Labels := by
      have ha : raw5436step0 = (fun i j => raw5436 (permutation185 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5436step0 raw5436; decide +kernel
      have hl : raw5436step0Labels = raw5436Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5436 raw5436Labels permutation185 permutation2
    _ = mixedMoment B node4887 node4887Labels := by rfl

theorem canonical5441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5441 raw5441Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw5441 raw5441Labels = mixedMoment B raw5441step0 raw5441step0Labels := by
      have ha : raw5441step0 = (fun i j => raw5441 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5441step0 raw5441; decide +kernel
      have hl : raw5441step0Labels = raw5441Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5441 raw5441Labels permutation161 permutation2
    _ = mixedMoment B node4887 node4887Labels := by rfl

theorem canonical5442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5442 raw5442Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw5442 raw5442Labels = mixedMoment B raw5442step0 raw5442step0Labels := by
      have ha : raw5442step0 = (fun i j => raw5442 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5442step0 raw5442; decide +kernel
      have hl : raw5442step0Labels = raw5442Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5442 raw5442Labels permutation154 permutation2
    _ = mixedMoment B node4439 node4439Labels := by rfl

theorem canonical5443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5443 raw5443Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw5443 raw5443Labels = mixedMoment B raw5443step0 raw5443step0Labels := by
      have ha : raw5443step0 = (fun i j => raw5443 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5443step0 raw5443; decide +kernel
      have hl : raw5443step0Labels = raw5443Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5443 raw5443Labels permutation154 permutation2
    _ = mixedMoment B node4852 node4852Labels := by rfl

theorem canonical5444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5444 raw5444Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw5444 raw5444Labels = mixedMoment B raw5444step0 raw5444step0Labels := by
      have ha : raw5444step0 = (fun i j => raw5444 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5444step0 raw5444; decide +kernel
      have hl : raw5444step0Labels = raw5444Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5444 raw5444Labels permutation178 permutation2
    _ = mixedMoment B node4852 node4852Labels := by rfl

theorem canonical5445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5445 raw5445Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw5445 raw5445Labels = mixedMoment B raw5445step0 raw5445step0Labels := by
      have hz : ∀ j, raw5445 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5445step0 = (fun i j => raw5445 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5445step0 raw5445; decide +kernel
      have hl : raw5445step0Labels = raw5445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5445 raw5445Labels permutation520 hz
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical5451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5451 raw5451Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw5451 raw5451Labels = mixedMoment B raw5451step0 raw5451step0Labels := by
      have ha : raw5451step0 = (fun i j => raw5451 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5451step0 raw5451; decide +kernel
      have hl : raw5451step0Labels = raw5451Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5451 raw5451Labels permutation153 permutation2
    _ = mixedMoment B node4885 node4885Labels := by rfl

theorem canonical5491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5491 raw5491Labels = mixedMoment B node2752 node2752Labels := by
  calc
    mixedMoment B raw5491 raw5491Labels = mixedMoment B raw5491step0 raw5491step0Labels := by
      have ha : raw5491step0 = (fun i j => raw5491 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5491step0 raw5491; decide +kernel
      have hl : raw5491step0Labels = raw5491Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5491 raw5491Labels permutation240 permutation7
    mixedMoment B raw5491step0 raw5491step0Labels = mixedMoment B raw5491step1 raw5491step1Labels := by
      have ha : raw5491step1 = -raw5491step0 := by apply Matrix.ext; change ∀ i j, raw5491step1 i j = -(raw5491step0 i j); unfold raw5491step1 raw5491step0; decide +kernel
      have hl : raw5491step1Labels = raw5491step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5491step1 raw5491step1Labels = mixedMoment B raw5491step2 raw5491step2Labels := by
      have ha : raw5491step2 = raw5491step1 := by apply Matrix.ext; unfold raw5491step2 raw5491step1; decide +kernel
      have hl : raw5491step1Labels = labelEmbedding1 ∘ raw5491step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5491step1 raw5491step1Labels raw5491step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2752 node2752Labels := by rfl

theorem canonical5496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5496 raw5496Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw5496 raw5496Labels = mixedMoment B raw5496step0 raw5496step0Labels := by
      have ha : raw5496step0 = (fun i j => raw5496 (permutation243 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5496step0 raw5496; decide +kernel
      have hl : raw5496step0Labels = raw5496Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5496 raw5496Labels permutation243 permutation7
    mixedMoment B raw5496step0 raw5496step0Labels = mixedMoment B raw5496step1 raw5496step1Labels := by
      have ha : raw5496step1 = -raw5496step0 := by apply Matrix.ext; change ∀ i j, raw5496step1 i j = -(raw5496step0 i j); unfold raw5496step1 raw5496step0; decide +kernel
      have hl : raw5496step1Labels = raw5496step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5496step1 raw5496step1Labels = mixedMoment B raw5496step2 raw5496step2Labels := by
      have ha : raw5496step2 = raw5496step1 := by apply Matrix.ext; unfold raw5496step2 raw5496step1; decide +kernel
      have hl : raw5496step1Labels = labelEmbedding1 ∘ raw5496step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5496step1 raw5496step1Labels raw5496step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2243 node2243Labels := by rfl

theorem canonical5501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5501 raw5501Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw5501 raw5501Labels = mixedMoment B raw5501step0 raw5501step0Labels := by
      have ha : raw5501step0 = (fun i j => raw5501 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5501step0 raw5501; decide +kernel
      have hl : raw5501step0Labels = raw5501Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5501 raw5501Labels permutation241 permutation7
    mixedMoment B raw5501step0 raw5501step0Labels = mixedMoment B raw5501step1 raw5501step1Labels := by
      have ha : raw5501step1 = -raw5501step0 := by apply Matrix.ext; change ∀ i j, raw5501step1 i j = -(raw5501step0 i j); unfold raw5501step1 raw5501step0; decide +kernel
      have hl : raw5501step1Labels = raw5501step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5501step1 raw5501step1Labels = mixedMoment B raw5501step2 raw5501step2Labels := by
      have ha : raw5501step2 = raw5501step1 := by apply Matrix.ext; unfold raw5501step2 raw5501step1; decide +kernel
      have hl : raw5501step1Labels = labelEmbedding1 ∘ raw5501step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5501step1 raw5501step1Labels raw5501step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2243 node2243Labels := by rfl

theorem canonical5502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5502 raw5502Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw5502 raw5502Labels = mixedMoment B raw5502step0 raw5502step0Labels := by
      have ha : raw5502step0 = (fun i j => raw5502 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5502step0 raw5502; decide +kernel
      have hl : raw5502step0Labels = raw5502Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5502 raw5502Labels permutation240 permutation7
    mixedMoment B raw5502step0 raw5502step0Labels = mixedMoment B raw5502step1 raw5502step1Labels := by
      have ha : raw5502step1 = -raw5502step0 := by apply Matrix.ext; change ∀ i j, raw5502step1 i j = -(raw5502step0 i j); unfold raw5502step1 raw5502step0; decide +kernel
      have hl : raw5502step1Labels = raw5502step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5502step1 raw5502step1Labels = mixedMoment B raw5502step2 raw5502step2Labels := by
      have ha : raw5502step2 = raw5502step1 := by apply Matrix.ext; unfold raw5502step2 raw5502step1; decide +kernel
      have hl : raw5502step1Labels = labelEmbedding1 ∘ raw5502step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5502step1 raw5502step1Labels raw5502step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

theorem canonical5503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5503 raw5503Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw5503 raw5503Labels = mixedMoment B raw5503step0 raw5503step0Labels := by
      have ha : raw5503step0 = (fun i j => raw5503 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5503step0 raw5503; decide +kernel
      have hl : raw5503step0Labels = raw5503Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5503 raw5503Labels permutation240 permutation7
    mixedMoment B raw5503step0 raw5503step0Labels = mixedMoment B raw5503step1 raw5503step1Labels := by
      have ha : raw5503step1 = -raw5503step0 := by apply Matrix.ext; change ∀ i j, raw5503step1 i j = -(raw5503step0 i j); unfold raw5503step1 raw5503step0; decide +kernel
      have hl : raw5503step1Labels = raw5503step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5503step1 raw5503step1Labels = mixedMoment B raw5503step2 raw5503step2Labels := by
      have ha : raw5503step2 = raw5503step1 := by apply Matrix.ext; unfold raw5503step2 raw5503step1; decide +kernel
      have hl : raw5503step1Labels = labelEmbedding1 ∘ raw5503step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5503step1 raw5503step1Labels raw5503step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5504 raw5504Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw5504 raw5504Labels = mixedMoment B raw5504step0 raw5504step0Labels := by
      have ha : raw5504step0 = (fun i j => raw5504 (permutation242 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5504step0 raw5504; decide +kernel
      have hl : raw5504step0Labels = raw5504Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5504 raw5504Labels permutation242 permutation7
    mixedMoment B raw5504step0 raw5504step0Labels = mixedMoment B raw5504step1 raw5504step1Labels := by
      have ha : raw5504step1 = -raw5504step0 := by apply Matrix.ext; change ∀ i j, raw5504step1 i j = -(raw5504step0 i j); unfold raw5504step1 raw5504step0; decide +kernel
      have hl : raw5504step1Labels = raw5504step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5504step1 raw5504step1Labels = mixedMoment B raw5504step2 raw5504step2Labels := by
      have ha : raw5504step2 = raw5504step1 := by apply Matrix.ext; unfold raw5504step2 raw5504step1; decide +kernel
      have hl : raw5504step1Labels = labelEmbedding1 ∘ raw5504step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5504step1 raw5504step1Labels raw5504step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

theorem canonical5505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5505 raw5505Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw5505 raw5505Labels = mixedMoment B raw5505step0 raw5505step0Labels := by
      have hz : ∀ j, raw5505 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5505step0 = (fun i j => raw5505 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5505step0 raw5505; decide +kernel
      have hl : raw5505step0Labels = raw5505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5505 raw5505Labels permutation520 hz
    mixedMoment B raw5505step0 raw5505step0Labels = mixedMoment B raw5505step1 raw5505step1Labels := by
      have ha : raw5505step1 = (fun i j => raw5505step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5505step1 raw5505step0; decide +kernel
      have hl : raw5505step1Labels = raw5505step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5505step0 raw5505step0Labels permutation50 permutation7
    mixedMoment B raw5505step1 raw5505step1Labels = mixedMoment B raw5505step2 raw5505step2Labels := by
      have ha : raw5505step2 = -raw5505step1 := by apply Matrix.ext; change ∀ i j, raw5505step2 i j = -(raw5505step1 i j); unfold raw5505step2 raw5505step1; decide +kernel
      have hl : raw5505step2Labels = raw5505step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5505step2 raw5505step2Labels = mixedMoment B raw5505step3 raw5505step3Labels := by
      have ha : raw5505step3 = raw5505step2 := by apply Matrix.ext; unfold raw5505step3 raw5505step2; decide +kernel
      have hl : raw5505step2Labels = labelEmbedding1 ∘ raw5505step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5505step2 raw5505step2Labels raw5505step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

theorem canonical5511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5511 raw5511Labels = mixedMoment B node2252 node2252Labels := by
  calc
    mixedMoment B raw5511 raw5511Labels = mixedMoment B raw5511step0 raw5511step0Labels := by
      have ha : raw5511step0 = (fun i j => raw5511 (permutation260 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5511step0 raw5511; decide +kernel
      have hl : raw5511step0Labels = raw5511Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5511 raw5511Labels permutation260 permutation7
    mixedMoment B raw5511step0 raw5511step0Labels = mixedMoment B raw5511step1 raw5511step1Labels := by
      have ha : raw5511step1 = -raw5511step0 := by apply Matrix.ext; change ∀ i j, raw5511step1 i j = -(raw5511step0 i j); unfold raw5511step1 raw5511step0; decide +kernel
      have hl : raw5511step1Labels = raw5511step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5511step1 raw5511step1Labels = mixedMoment B raw5511step2 raw5511step2Labels := by
      have ha : raw5511step2 = raw5511step1 := by apply Matrix.ext; unfold raw5511step2 raw5511step1; decide +kernel
      have hl : raw5511step1Labels = labelEmbedding1 ∘ raw5511step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5511step1 raw5511step1Labels raw5511step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2252 node2252Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw966 raw966Labels = mixedMoment B node4248 node4248Labels := by
  calc
    mixedMoment B raw966 raw966Labels = mixedMoment B raw966step0 raw966step0Labels := by
      have ha : raw966step0 = (fun i j => raw966 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw966step0 raw966; decide +kernel
      have hl : raw966step0Labels = raw966Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw966 raw966Labels permutation152 permutation4
    mixedMoment B raw966step0 raw966step0Labels = mixedMoment B raw966step1 raw966step1Labels := by
      have ha : raw966step1 = raw966step0 := by apply Matrix.ext; unfold raw966step1 raw966step0; decide +kernel
      have hl : raw966step0Labels = labelEmbedding7 ∘ raw966step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw966step0 raw966step0Labels raw966step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4248 node4248Labels := by rfl

theorem canonical967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw967 raw967Labels = mixedMoment B node782 node782Labels := by
  calc
    mixedMoment B raw967 raw967Labels = mixedMoment B raw967step0 raw967step0Labels := by
      have ha : raw967step0 = (fun i j => raw967 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw967step0 raw967; decide +kernel
      have hl : raw967step0Labels = raw967Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw967 raw967Labels permutation152 permutation4
    _ = mixedMoment B node782 node782Labels := by rfl

theorem canonical968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw968 raw968Labels = mixedMoment B node782 node782Labels := by
  calc
    mixedMoment B raw968 raw968Labels = mixedMoment B raw968step0 raw968step0Labels := by
      have ha : raw968step0 = (fun i j => raw968 (permutation212 i) (permutation6 j)) := by apply Matrix.ext; unfold raw968step0 raw968; decide +kernel
      have hl : raw968step0Labels = raw968Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw968 raw968Labels permutation212 permutation6
    mixedMoment B raw968step0 raw968step0Labels = mixedMoment B raw968step1 raw968step1Labels := by
      have ha : raw968step1 = -raw968step0 := by apply Matrix.ext; change ∀ i j, raw968step1 i j = -(raw968step0 i j); unfold raw968step1 raw968step0; decide +kernel
      have hl : raw968step1Labels = raw968step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw968step1 raw968step1Labels = mixedMoment B raw968step2 raw968step2Labels := by
      have ha : raw968step2 = raw968step1 := by apply Matrix.ext; unfold raw968step2 raw968step1; decide +kernel
      have hl : raw968step1Labels = labelEmbedding1 ∘ raw968step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw968step1 raw968step1Labels raw968step2Labels labelEmbedding1 hl
    _ = mixedMoment B node782 node782Labels := by rfl

theorem canonical969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw969 raw969Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw969 raw969Labels = mixedMoment B raw969step0 raw969step0Labels := by
      have ha : raw969step0 = (fun i j => raw969 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw969step0 raw969; decide +kernel
      have hl : raw969step0Labels = raw969Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw969 raw969Labels permutation152 permutation4
    mixedMoment B raw969step0 raw969step0Labels = mixedMoment B raw969step1 raw969step1Labels := by
      have ha : raw969step1 = raw969step0 := by apply Matrix.ext; unfold raw969step1 raw969step0; decide +kernel
      have hl : raw969step0Labels = labelEmbedding7 ∘ raw969step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw969step0 raw969step0Labels raw969step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

theorem canonical970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw970 raw970Labels = mixedMoment B node783 node783Labels := by
  calc
    mixedMoment B raw970 raw970Labels = mixedMoment B raw970step0 raw970step0Labels := by
      have ha : raw970step0 = (fun i j => raw970 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw970step0 raw970; decide +kernel
      have hl : raw970step0Labels = raw970Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw970 raw970Labels permutation152 permutation4
    _ = mixedMoment B node783 node783Labels := by rfl

theorem canonical971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw971 raw971Labels = mixedMoment B node803 node803Labels := by
  calc
    mixedMoment B raw971 raw971Labels = mixedMoment B raw971step0 raw971step0Labels := by
      have ha : raw971step0 = (fun i j => raw971 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw971step0 raw971; decide +kernel
      have hl : raw971step0Labels = raw971Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw971 raw971Labels permutation200 permutation6
    mixedMoment B raw971step0 raw971step0Labels = mixedMoment B raw971step1 raw971step1Labels := by
      have ha : raw971step1 = -raw971step0 := by apply Matrix.ext; change ∀ i j, raw971step1 i j = -(raw971step0 i j); unfold raw971step1 raw971step0; decide +kernel
      have hl : raw971step1Labels = raw971step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw971step1 raw971step1Labels = mixedMoment B raw971step2 raw971step2Labels := by
      have ha : raw971step2 = raw971step1 := by apply Matrix.ext; unfold raw971step2 raw971step1; decide +kernel
      have hl : raw971step1Labels = labelEmbedding1 ∘ raw971step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw971step1 raw971step1Labels raw971step2Labels labelEmbedding1 hl
    _ = mixedMoment B node803 node803Labels := by rfl

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

theorem canonical11319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11319 raw11319Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw11319 raw11319Labels = mixedMoment B raw11319step0 raw11319step0Labels := by
      have hz : ∀ j, raw11319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11319step0 = (fun i j => raw11319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11319step0 raw11319; decide +kernel
      have hl : raw11319step0Labels = raw11319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11319 raw11319Labels permutation434 hz
    mixedMoment B raw11319step0 raw11319step0Labels = mixedMoment B raw11319step1 raw11319step1Labels := by
      have ha : raw11319step1 = (fun i j => raw11319step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11319step1 raw11319step0; decide +kernel
      have hl : raw11319step1Labels = raw11319step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11319step0 raw11319step0Labels permutation32 permutation3
    mixedMoment B raw11319step1 raw11319step1Labels = mixedMoment B raw11319step2 raw11319step2Labels := by
      have ha : raw11319step2 = raw11319step1 := by apply Matrix.ext; unfold raw11319step2 raw11319step1; decide +kernel
      have hl : raw11319step1Labels = labelEmbedding6 ∘ raw11319step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11319step1 raw11319step1Labels raw11319step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5452 node5452Labels := by rfl

theorem canonical11324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11324 raw11324Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw11324 raw11324Labels = mixedMoment B raw11324step0 raw11324step0Labels := by
      have hz : ∀ j, raw11324 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11324step0 = (fun i j => raw11324 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11324step0 raw11324; decide +kernel
      have hl : raw11324step0Labels = raw11324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11324 raw11324Labels permutation434 hz
    mixedMoment B raw11324step0 raw11324step0Labels = mixedMoment B raw11324step1 raw11324step1Labels := by
      have ha : raw11324step1 = (fun i j => raw11324step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11324step1 raw11324step0; decide +kernel
      have hl : raw11324step1Labels = raw11324step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11324step0 raw11324step0Labels permutation49 permutation5
    mixedMoment B raw11324step1 raw11324step1Labels = mixedMoment B raw11324step2 raw11324step2Labels := by
      have ha : raw11324step2 = -raw11324step1 := by apply Matrix.ext; change ∀ i j, raw11324step2 i j = -(raw11324step1 i j); unfold raw11324step2 raw11324step1; decide +kernel
      have hl : raw11324step2Labels = raw11324step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11324step2 raw11324step2Labels = mixedMoment B raw11324step3 raw11324step3Labels := by
      have ha : raw11324step3 = raw11324step2 := by apply Matrix.ext; unfold raw11324step3 raw11324step2; decide +kernel
      have hl : raw11324step2Labels = labelEmbedding8 ∘ raw11324step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11324step2 raw11324step2Labels raw11324step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical11329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11329 raw11329Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw11329 raw11329Labels = mixedMoment B raw11329step0 raw11329step0Labels := by
      have hz : ∀ j, raw11329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11329step0 = (fun i j => raw11329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11329step0 raw11329; decide +kernel
      have hl : raw11329step0Labels = raw11329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11329 raw11329Labels permutation434 hz
    mixedMoment B raw11329step0 raw11329step0Labels = mixedMoment B raw11329step1 raw11329step1Labels := by
      have ha : raw11329step1 = (fun i j => raw11329step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11329step1 raw11329step0; decide +kernel
      have hl : raw11329step1Labels = raw11329step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11329step0 raw11329step0Labels permutation48 permutation5
    mixedMoment B raw11329step1 raw11329step1Labels = mixedMoment B raw11329step2 raw11329step2Labels := by
      have ha : raw11329step2 = -raw11329step1 := by apply Matrix.ext; change ∀ i j, raw11329step2 i j = -(raw11329step1 i j); unfold raw11329step2 raw11329step1; decide +kernel
      have hl : raw11329step2Labels = raw11329step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11329step2 raw11329step2Labels = mixedMoment B raw11329step3 raw11329step3Labels := by
      have ha : raw11329step3 = raw11329step2 := by apply Matrix.ext; unfold raw11329step3 raw11329step2; decide +kernel
      have hl : raw11329step2Labels = labelEmbedding8 ∘ raw11329step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11329step2 raw11329step2Labels raw11329step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical11330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11330 raw11330Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw11330 raw11330Labels = mixedMoment B raw11330step0 raw11330step0Labels := by
      have ha : raw11330step0 = (fun i j => raw11330 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11330step0 raw11330; decide +kernel
      have hl : raw11330step0Labels = raw11330Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11330 raw11330Labels permutation154 permutation3
    mixedMoment B raw11330step0 raw11330step0Labels = mixedMoment B raw11330step1 raw11330step1Labels := by
      have ha : raw11330step1 = raw11330step0 := by apply Matrix.ext; unfold raw11330step1 raw11330step0; decide +kernel
      have hl : raw11330step0Labels = labelEmbedding6 ∘ raw11330step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11330step0 raw11330step0Labels raw11330step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

theorem canonical11331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11331 raw11331Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw11331 raw11331Labels = mixedMoment B raw11331step0 raw11331step0Labels := by
      have ha : raw11331step0 = (fun i j => raw11331 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11331step0 raw11331; decide +kernel
      have hl : raw11331step0Labels = raw11331Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11331 raw11331Labels permutation154 permutation3
    mixedMoment B raw11331step0 raw11331step0Labels = mixedMoment B raw11331step1 raw11331step1Labels := by
      have ha : raw11331step1 = raw11331step0 := by apply Matrix.ext; unfold raw11331step1 raw11331step0; decide +kernel
      have hl : raw11331step0Labels = labelEmbedding6 ∘ raw11331step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11331step0 raw11331step0Labels raw11331step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical11332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11332 raw11332Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw11332 raw11332Labels = mixedMoment B raw11332step0 raw11332step0Labels := by
      have ha : raw11332step0 = (fun i j => raw11332 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11332step0 raw11332; decide +kernel
      have hl : raw11332step0Labels = raw11332Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11332 raw11332Labels permutation178 permutation3
    mixedMoment B raw11332step0 raw11332step0Labels = mixedMoment B raw11332step1 raw11332step1Labels := by
      have ha : raw11332step1 = raw11332step0 := by apply Matrix.ext; unfold raw11332step1 raw11332step0; decide +kernel
      have hl : raw11332step0Labels = labelEmbedding6 ∘ raw11332step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11332step0 raw11332step0Labels raw11332step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical11333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11333 raw11333Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw11333 raw11333Labels = mixedMoment B raw11333step0 raw11333step0Labels := by
      have ha : raw11333step0 = (fun i j => raw11333 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11333step0 raw11333; decide +kernel
      have hl : raw11333step0Labels = raw11333Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11333 raw11333Labels permutation224 permutation5
    mixedMoment B raw11333step0 raw11333step0Labels = mixedMoment B raw11333step1 raw11333step1Labels := by
      have ha : raw11333step1 = -raw11333step0 := by apply Matrix.ext; change ∀ i j, raw11333step1 i j = -(raw11333step0 i j); unfold raw11333step1 raw11333step0; decide +kernel
      have hl : raw11333step1Labels = raw11333step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11333step1 raw11333step1Labels = mixedMoment B raw11333step2 raw11333step2Labels := by
      have ha : raw11333step2 = raw11333step1 := by apply Matrix.ext; unfold raw11333step2 raw11333step1; decide +kernel
      have hl : raw11333step1Labels = labelEmbedding8 ∘ raw11333step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11333step1 raw11333step1Labels raw11333step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

theorem canonical11339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11339 raw11339Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw11339 raw11339Labels = mixedMoment B raw11339step0 raw11339step0Labels := by
      have hz : ∀ j, raw11339 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11339step0 = (fun i j => raw11339 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11339step0 raw11339; decide +kernel
      have hl : raw11339step0Labels = raw11339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11339 raw11339Labels permutation434 hz
    mixedMoment B raw11339step0 raw11339step0Labels = mixedMoment B raw11339step1 raw11339step1Labels := by
      have ha : raw11339step1 = (fun i j => raw11339step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11339step1 raw11339step0; decide +kernel
      have hl : raw11339step1Labels = raw11339step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11339step0 raw11339step0Labels permutation33 permutation3
    mixedMoment B raw11339step1 raw11339step1Labels = mixedMoment B raw11339step2 raw11339step2Labels := by
      have ha : raw11339step2 = raw11339step1 := by apply Matrix.ext; unfold raw11339step2 raw11339step1; decide +kernel
      have hl : raw11339step1Labels = labelEmbedding6 ∘ raw11339step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11339step1 raw11339step1Labels raw11339step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

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

theorem canonical1254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1254 raw1254Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw1254 raw1254Labels = mixedMoment B raw1254step0 raw1254step0Labels := by
      have ha : raw1254step0 = (fun i j => raw1254 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1254step0 raw1254; decide +kernel
      have hl : raw1254step0Labels = raw1254Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1254 raw1254Labels permutation152 permutation4
    mixedMoment B raw1254step0 raw1254step0Labels = mixedMoment B raw1254step1 raw1254step1Labels := by
      have ha : raw1254step1 = raw1254step0 := by apply Matrix.ext; unfold raw1254step1 raw1254step0; decide +kernel
      have hl : raw1254step0Labels = labelEmbedding7 ∘ raw1254step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1254step0 raw1254step0Labels raw1254step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

theorem canonical1255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1255 raw1255Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw1255 raw1255Labels = mixedMoment B raw1255step0 raw1255step0Labels := by
      have ha : raw1255step0 = (fun i j => raw1255 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1255step0 raw1255; decide +kernel
      have hl : raw1255step0Labels = raw1255Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1255 raw1255Labels permutation152 permutation4
    _ = mixedMoment B node1039 node1039Labels := by rfl

theorem canonical1256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1256 raw1256Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw1256 raw1256Labels = mixedMoment B raw1256step0 raw1256step0Labels := by
      have ha : raw1256step0 = (fun i j => raw1256 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1256step0 raw1256; decide +kernel
      have hl : raw1256step0Labels = raw1256Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1256 raw1256Labels permutation182 permutation6
    mixedMoment B raw1256step0 raw1256step0Labels = mixedMoment B raw1256step1 raw1256step1Labels := by
      have ha : raw1256step1 = -raw1256step0 := by apply Matrix.ext; change ∀ i j, raw1256step1 i j = -(raw1256step0 i j); unfold raw1256step1 raw1256step0; decide +kernel
      have hl : raw1256step1Labels = raw1256step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1256step1 raw1256step1Labels = mixedMoment B raw1256step2 raw1256step2Labels := by
      have ha : raw1256step2 = raw1256step1 := by apply Matrix.ext; unfold raw1256step2 raw1256step1; decide +kernel
      have hl : raw1256step1Labels = labelEmbedding1 ∘ raw1256step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1256step1 raw1256step1Labels raw1256step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1706 node1706Labels := by rfl

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

theorem canonical12193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12193 raw12193Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw12193 raw12193Labels = mixedMoment B raw12193step0 raw12193step0Labels := by
      have hz : ∀ j, raw12193 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12193step0 = (fun i j => raw12193 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12193step0 raw12193; decide +kernel
      have hl : raw12193step0Labels = raw12193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12193 raw12193Labels permutation265 hz
    mixedMoment B raw12193step0 raw12193step0Labels = mixedMoment B raw12193step1 raw12193step1Labels := by
      have ha : raw12193step1 = (fun i j => raw12193step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12193step1 raw12193step0; decide +kernel
      have hl : raw12193step1Labels = raw12193step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12193step0 raw12193step0Labels permutation34 permutation6
    mixedMoment B raw12193step1 raw12193step1Labels = mixedMoment B raw12193step2 raw12193step2Labels := by
      have ha : raw12193step2 = raw12193step1 := by apply Matrix.ext; unfold raw12193step2 raw12193step1; decide +kernel
      have hl : raw12193step1Labels = labelEmbedding9 ∘ raw12193step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12193step1 raw12193step1Labels raw12193step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical12195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12195 raw12195Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw12195 raw12195Labels = mixedMoment B raw12195step0 raw12195step0Labels := by
      have hz : ∀ j, raw12195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12195step0 = (fun i j => raw12195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12195step0 raw12195; decide +kernel
      have hl : raw12195step0Labels = raw12195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12195 raw12195Labels permutation346 hz
    mixedMoment B raw12195step0 raw12195step0Labels = mixedMoment B raw12195step1 raw12195step1Labels := by
      have hz : ∀ j, raw12195step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12195step1 = (fun i j => raw12195step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12195step1 raw12195step0; decide +kernel
      have hl : raw12195step1Labels = raw12195step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12195step0 raw12195step0Labels permutation56 hz
    mixedMoment B raw12195step1 raw12195step1Labels = mixedMoment B raw12195step2 raw12195step2Labels := by
      have ha : raw12195step2 = (fun i j => raw12195step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12195step2 raw12195step1; decide +kernel
      have hl : raw12195step2Labels = raw12195step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12195step1 raw12195step1Labels permutation10 permutation6
    mixedMoment B raw12195step2 raw12195step2Labels = mixedMoment B raw12195step3 raw12195step3Labels := by
      have ha : raw12195step3 = raw12195step2 := by apply Matrix.ext; unfold raw12195step3 raw12195step2; decide +kernel
      have hl : raw12195step2Labels = labelEmbedding9 ∘ raw12195step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12195step2 raw12195step2Labels raw12195step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5307 node5307Labels := by rfl

theorem canonical12197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12197 raw12197Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw12197 raw12197Labels = mixedMoment B raw12197step0 raw12197step0Labels := by
      have hz : ∀ j, raw12197 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12197step0 = (fun i j => raw12197 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12197step0 raw12197; decide +kernel
      have hl : raw12197step0Labels = raw12197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12197 raw12197Labels permutation265 hz
    mixedMoment B raw12197step0 raw12197step0Labels = mixedMoment B raw12197step1 raw12197step1Labels := by
      have ha : raw12197step1 = (fun i j => raw12197step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12197step1 raw12197step0; decide +kernel
      have hl : raw12197step1Labels = raw12197step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12197step0 raw12197step0Labels permutation32 permutation6
    mixedMoment B raw12197step1 raw12197step1Labels = mixedMoment B raw12197step2 raw12197step2Labels := by
      have ha : raw12197step2 = raw12197step1 := by apply Matrix.ext; unfold raw12197step2 raw12197step1; decide +kernel
      have hl : raw12197step1Labels = labelEmbedding9 ∘ raw12197step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12197step1 raw12197step1Labels raw12197step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical12199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12199 raw12199Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw12199 raw12199Labels = mixedMoment B raw12199step0 raw12199step0Labels := by
      have hz : ∀ j, raw12199 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12199step0 = (fun i j => raw12199 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12199step0 raw12199; decide +kernel
      have hl : raw12199step0Labels = raw12199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12199 raw12199Labels permutation346 hz
    mixedMoment B raw12199step0 raw12199step0Labels = mixedMoment B raw12199step1 raw12199step1Labels := by
      have hz : ∀ j, raw12199step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12199step1 = (fun i j => raw12199step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12199step1 raw12199step0; decide +kernel
      have hl : raw12199step1Labels = raw12199step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12199step0 raw12199step0Labels permutation56 hz
    mixedMoment B raw12199step1 raw12199step1Labels = mixedMoment B raw12199step2 raw12199step2Labels := by
      have ha : raw12199step2 = (fun i j => raw12199step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12199step2 raw12199step1; decide +kernel
      have hl : raw12199step2Labels = raw12199step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12199step1 raw12199step1Labels permutation8 permutation6
    mixedMoment B raw12199step2 raw12199step2Labels = mixedMoment B raw12199step3 raw12199step3Labels := by
      have ha : raw12199step3 = raw12199step2 := by apply Matrix.ext; unfold raw12199step3 raw12199step2; decide +kernel
      have hl : raw12199step2Labels = labelEmbedding9 ∘ raw12199step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12199step2 raw12199step2Labels raw12199step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5307 node5307Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4248 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4248 node4248Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node782 node782Labels + mixedMoment B node782 node782Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw966 singletonSmall4248
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4248) = raw966Labels := by decide +kernel
  rw [hl, canonical966 B hB] at h
  have hc0 : mixedMoment B raw966 (Fin.cases (0 : Fin 2) singletonSmall4248) =
      mixedMoment B node782 node782Labels := by
    have ha : raw966 = raw967 := by apply Matrix.ext; unfold raw966 raw967; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4248 = raw967Labels := by decide +kernel
    rw [ha, hj, canonical967 B hB]
  have hc1 : mixedMoment B raw966 (Fin.cases (1 : Fin 2) singletonSmall4248) =
      mixedMoment B node782 node782Labels := by
    have ha : raw966 = raw968 := by apply Matrix.ext; unfold raw966 raw968; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4248 = raw968Labels := by decide +kernel
    rw [ha, hj, canonical968 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4249 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4249 node4249Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node783 node783Labels + mixedMoment B node803 node803Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw969 singletonSmall4249
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4249) = raw969Labels := by decide +kernel
  rw [hl, canonical969 B hB] at h
  have hc0 : mixedMoment B raw969 (Fin.cases (0 : Fin 2) singletonSmall4249) =
      mixedMoment B node783 node783Labels := by
    have ha : raw969 = raw970 := by apply Matrix.ext; unfold raw969 raw970; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4249 = raw970Labels := by decide +kernel
    rw [ha, hj, canonical970 B hB]
  have hc1 : mixedMoment B raw969 (Fin.cases (1 : Fin 2) singletonSmall4249) =
      mixedMoment B node803 node803Labels := by
    have ha : raw969 = raw971 := by apply Matrix.ext; unfold raw969 raw971; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4249 = raw971Labels := by decide +kernel
    rw [ha, hj, canonical971 B hB]
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

theorem singleton4456 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4456 node4456Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1039 node1039Labels + mixedMoment B node1706 node1706Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1254 singletonSmall4456
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4456) = raw1254Labels := by decide +kernel
  rw [hl, canonical1254 B hB] at h
  have hc0 : mixedMoment B raw1254 (Fin.cases (0 : Fin 2) singletonSmall4456) =
      mixedMoment B node1039 node1039Labels := by
    have ha : raw1254 = raw1255 := by apply Matrix.ext; unfold raw1254 raw1255; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4456 = raw1255Labels := by decide +kernel
    rw [ha, hj, canonical1255 B hB]
  have hc1 : mixedMoment B raw1254 (Fin.cases (1 : Fin 2) singletonSmall4456) =
      mixedMoment B node1706 node1706Labels := by
    have ha : raw1254 = raw1256 := by apply Matrix.ext; unfold raw1254 raw1256; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4456 = raw1256Labels := by decide +kernel
    rw [ha, hj, canonical1256 B hB]
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

theorem singleton4801 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4801 node4801Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2019 node2019Labels + mixedMoment B node2190 node2190Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1731 singletonSmall4801
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4801) = raw1731Labels := by decide +kernel
  rw [hl, canonical1731 B hB] at h
  have hc0 : mixedMoment B raw1731 (Fin.cases (0 : Fin 2) singletonSmall4801) =
      mixedMoment B node2019 node2019Labels := by
    have ha : raw1731 = raw1732 := by apply Matrix.ext; unfold raw1731 raw1732; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4801 = raw1732Labels := by decide +kernel
    rw [ha, hj, canonical1732 B hB]
  have hc1 : mixedMoment B raw1731 (Fin.cases (1 : Fin 2) singletonSmall4801) =
      mixedMoment B node2190 node2190Labels := by
    have ha : raw1731 = raw1733 := by apply Matrix.ext; unfold raw1731 raw1733; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4801 = raw1733Labels := by decide +kernel
    rw [ha, hj, canonical1733 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4831 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4831 node4831Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2051 node2051Labels + mixedMoment B node2191 node2191Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1761 singletonSmall4831
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4831) = raw1761Labels := by decide +kernel
  rw [hl, canonical1761 B hB] at h
  have hc0 : mixedMoment B raw1761 (Fin.cases (0 : Fin 2) singletonSmall4831) =
      mixedMoment B node2051 node2051Labels := by
    have ha : raw1761 = raw1762 := by apply Matrix.ext; unfold raw1761 raw1762; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4831 = raw1762Labels := by decide +kernel
    rw [ha, hj, canonical1762 B hB]
  have hc1 : mixedMoment B raw1761 (Fin.cases (1 : Fin 2) singletonSmall4831) =
      mixedMoment B node2191 node2191Labels := by
    have ha : raw1761 = raw1763 := by apply Matrix.ext; unfold raw1761 raw1763; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4831 = raw1763Labels := by decide +kernel
    rw [ha, hj, canonical1763 B hB]
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

theorem singleton4864 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4864 node4864Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2105 node2105Labels + mixedMoment B node2241 node2241Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1788 singletonSmall4864
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4864) = raw1788Labels := by decide +kernel
  rw [hl, canonical1788 B hB] at h
  have hc0 : mixedMoment B raw1788 (Fin.cases (0 : Fin 2) singletonSmall4864) =
      mixedMoment B node2105 node2105Labels := by
    have ha : raw1788 = raw1789 := by apply Matrix.ext; unfold raw1788 raw1789; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4864 = raw1789Labels := by decide +kernel
    rw [ha, hj, canonical1789 B hB]
  have hc1 : mixedMoment B raw1788 (Fin.cases (1 : Fin 2) singletonSmall4864) =
      mixedMoment B node2241 node2241Labels := by
    have ha : raw1788 = raw1790 := by apply Matrix.ext; unfold raw1788 raw1790; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4864 = raw1790Labels := by decide +kernel
    rw [ha, hj, canonical1790 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4888 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4888 node4888Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2244 node2244Labels + mixedMoment B node2262 node2262Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1815 singletonSmall4888
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4888) = raw1815Labels := by decide +kernel
  rw [hl, canonical1815 B hB] at h
  have hc0 : mixedMoment B raw1815 (Fin.cases (0 : Fin 2) singletonSmall4888) =
      mixedMoment B node2244 node2244Labels := by
    have ha : raw1815 = raw1816 := by apply Matrix.ext; unfold raw1815 raw1816; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4888 = raw1816Labels := by decide +kernel
    rw [ha, hj, canonical1816 B hB]
  have hc1 : mixedMoment B raw1815 (Fin.cases (1 : Fin 2) singletonSmall4888) =
      mixedMoment B node2262 node2262Labels := by
    have ha : raw1815 = raw1817 := by apply Matrix.ext; unfold raw1815 raw1817; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4888 = raw1817Labels := by decide +kernel
    rw [ha, hj, canonical1817 B hB]
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

theorem singleton5237 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5237 node5237Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2684 node2684Labels + mixedMoment B node3394 node3394Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2253 singletonSmall5237
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5237) = raw2253Labels := by decide +kernel
  rw [hl, canonical2253 B hB] at h
  have hc0 : mixedMoment B raw2253 (Fin.cases (0 : Fin 2) singletonSmall5237) =
      mixedMoment B node2684 node2684Labels := by
    have ha : raw2253 = raw2254 := by apply Matrix.ext; unfold raw2253 raw2254; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5237 = raw2254Labels := by decide +kernel
    rw [ha, hj, canonical2254 B hB]
  have hc1 : mixedMoment B raw2253 (Fin.cases (1 : Fin 2) singletonSmall5237) =
      mixedMoment B node3394 node3394Labels := by
    have ha : raw2253 = raw2255 := by apply Matrix.ext; unfold raw2253 raw2255; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5237 = raw2255Labels := by decide +kernel
    rw [ha, hj, canonical2255 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node782 node782Labels = Sparse.eval nodeValue782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 782) = mixedMoment B node782 node782Labels := rfl
  simpa [nodeValue782, Sparse.eval] using hc.symm

theorem sound783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node783 node783Labels = Sparse.eval nodeValue783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 783) = mixedMoment B node783 node783Labels := rfl
  simpa [nodeValue783, Sparse.eval] using hc.symm

theorem sound803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node803 node803Labels = Sparse.eval nodeValue803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 803) = mixedMoment B node803 node803Labels := rfl
  simpa [nodeValue803, Sparse.eval] using hc.symm

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

theorem sound1039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1039 node1039Labels = Sparse.eval nodeValue1039 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1039) = mixedMoment B node1039 node1039Labels := rfl
  simpa [nodeValue1039, Sparse.eval] using hc.symm

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

theorem zero1705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1705 node1705Labels = 0 := by
  exact mixedMoment_alpha B hF node1705 node1705Labels 1 permutation437
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

theorem sound1705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1705 node1705Labels = Sparse.eval nodeValue1705 (mixedVector B) := by
  simpa only [nodeValue1705, Sparse.eval_nil] using zero1705 B _hB _hF

theorem sound1706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1706 node1706Labels = Sparse.eval nodeValue1706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1706) = mixedMoment B node1706 node1706Labels := rfl
  simpa [nodeValue1706, Sparse.eval] using hc.symm

theorem sound1713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1713 node1713Labels = Sparse.eval nodeValue1713 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1713) = mixedMoment B node1713 node1713Labels := rfl
  simpa [nodeValue1713, Sparse.eval] using hc.symm

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

theorem sound2051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2051 node2051Labels = Sparse.eval nodeValue2051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2051) = mixedMoment B node2051 node2051Labels := rfl
  simpa [nodeValue2051, Sparse.eval] using hc.symm

theorem sound2105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2105 node2105Labels = Sparse.eval nodeValue2105 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2105) = mixedMoment B node2105 node2105Labels := rfl
  simpa [nodeValue2105, Sparse.eval] using hc.symm

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

theorem sound2190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2190 node2190Labels = Sparse.eval nodeValue2190 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2190) = mixedMoment B node2190 node2190Labels := rfl
  simpa [nodeValue2190, Sparse.eval] using hc.symm

theorem sound2191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2191 node2191Labels = Sparse.eval nodeValue2191 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2191) = mixedMoment B node2191 node2191Labels := rfl
  simpa [nodeValue2191, Sparse.eval] using hc.symm

theorem sound2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2202 node2202Labels = Sparse.eval nodeValue2202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2202) = mixedMoment B node2202 node2202Labels := rfl
  simpa [nodeValue2202, Sparse.eval] using hc.symm

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

theorem sound2240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2240 node2240Labels = Sparse.eval nodeValue2240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2240) = mixedMoment B node2240 node2240Labels := rfl
  simpa [nodeValue2240, Sparse.eval] using hc.symm

theorem sound2241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2241 node2241Labels = Sparse.eval nodeValue2241 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2241) = mixedMoment B node2241 node2241Labels := rfl
  simpa [nodeValue2241, Sparse.eval] using hc.symm

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

theorem sound2245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2245 node2245Labels = Sparse.eval nodeValue2245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2245) = mixedMoment B node2245 node2245Labels := rfl
  simpa [nodeValue2245, Sparse.eval] using hc.symm

theorem sound2250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2250 node2250Labels = Sparse.eval nodeValue2250 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2250) = mixedMoment B node2250 node2250Labels := rfl
  simpa [nodeValue2250, Sparse.eval] using hc.symm

theorem sound2252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2252 node2252Labels = Sparse.eval nodeValue2252 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2252) = mixedMoment B node2252 node2252Labels := rfl
  simpa [nodeValue2252, Sparse.eval] using hc.symm

theorem sound2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2262 node2262Labels = Sparse.eval nodeValue2262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2262) = mixedMoment B node2262 node2262Labels := rfl
  simpa [nodeValue2262, Sparse.eval] using hc.symm

theorem sound2263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2263 node2263Labels = Sparse.eval nodeValue2263 (mixedVector B) := by
  simpa only [nodeValue2263, Sparse.eval_nil] using zero2263 B _hB _hF

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

theorem sound2671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2671 node2671Labels = Sparse.eval nodeValue2671 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2671) = mixedMoment B node2671 node2671Labels := rfl
  simpa [nodeValue2671, Sparse.eval] using hc.symm

theorem sound2684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2684 node2684Labels = Sparse.eval nodeValue2684 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2684) = mixedMoment B node2684 node2684Labels := rfl
  simpa [nodeValue2684, Sparse.eval] using hc.symm

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

theorem sound2721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2721 node2721Labels = Sparse.eval nodeValue2721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2721) = mixedMoment B node2721 node2721Labels := rfl
  simpa [nodeValue2721, Sparse.eval] using hc.symm

theorem sound2739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2739 node2739Labels = Sparse.eval nodeValue2739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2739) = mixedMoment B node2739 node2739Labels := rfl
  simpa [nodeValue2739, Sparse.eval] using hc.symm

theorem sound2750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2750 node2750Labels = Sparse.eval nodeValue2750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2750) = mixedMoment B node2750 node2750Labels := rfl
  simpa [nodeValue2750, Sparse.eval] using hc.symm

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

theorem zero2752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2752 node2752Labels = 0 := by
  exact mixedMoment_alpha B hF node2752 node2752Labels 1 permutation152
    (by decide +kernel)

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

theorem sound2752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2752 node2752Labels = Sparse.eval nodeValue2752 (mixedVector B) := by
  simpa only [nodeValue2752, Sparse.eval_nil] using zero2752 B _hB _hF

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

theorem sound3053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3053 node3053Labels = Sparse.eval nodeValue3053 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3053) = mixedMoment B node3053 node3053Labels := rfl
  simpa [nodeValue3053, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3394 node3394Labels = Sparse.eval nodeValue3394 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3394) = mixedMoment B node3394 node3394Labels := rfl
  simpa [nodeValue3394, Sparse.eval] using hc.symm

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

theorem sound3619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3619 node3619Labels = Sparse.eval nodeValue3619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3619) = mixedMoment B node3619 node3619Labels := rfl
  simpa [nodeValue3619, Sparse.eval] using hc.symm

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4248 node4248Labels = Sparse.eval nodeValue4248 (mixedVector B) := by
  have h := singleton4248 B _hB
  rw [sound782 B _hB _hF] at h
  norm_num [nodeValue4248, nodeValue782, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4249 node4249Labels = Sparse.eval nodeValue4249 (mixedVector B) := by
  have h := singleton4249 B _hB
  rw [sound783 B _hB _hF, sound803 B _hB _hF] at h
  norm_num [nodeValue4249, nodeValue783, nodeValue803, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4438 node4438Labels = 0 := by
  exact mixedMoment_alpha B hF node4438 node4438Labels 1 permutation152
    (by decide +kernel)

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

theorem sound4438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4438 node4438Labels = Sparse.eval nodeValue4438 (mixedVector B) := by
  simpa only [nodeValue4438, Sparse.eval_nil] using zero4438 B _hB _hF

theorem sound4439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4439 node4439Labels = Sparse.eval nodeValue4439 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4439) = mixedMoment B node4439 node4439Labels := rfl
  simpa [nodeValue4439, Sparse.eval] using hc.symm

theorem sound4456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4456 node4456Labels = Sparse.eval nodeValue4456 (mixedVector B) := by
  have h := singleton4456 B _hB
  rw [sound1039 B _hB _hF, sound1706 B _hB _hF] at h
  norm_num [nodeValue4456, nodeValue1039, nodeValue1706, Sparse.eval] at h ⊢
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

theorem sound4801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4801 node4801Labels = Sparse.eval nodeValue4801 (mixedVector B) := by
  have h := singleton4801 B _hB
  rw [sound2019 B _hB _hF, sound2190 B _hB _hF] at h
  norm_num [nodeValue4801, nodeValue2019, nodeValue2190, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4802 node4802Labels = Sparse.eval nodeValue4802 (mixedVector B) := by
  have h := singleton4802 B _hB
  rw [sound2020 B _hB _hF, sound2202 B _hB _hF] at h
  norm_num [nodeValue4802, nodeValue2020, nodeValue2202, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4831 node4831Labels = Sparse.eval nodeValue4831 (mixedVector B) := by
  have h := singleton4831 B _hB
  rw [sound2051 B _hB _hF, sound2191 B _hB _hF] at h
  norm_num [nodeValue4831, nodeValue2051, nodeValue2191, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4833 node4833Labels = Sparse.eval nodeValue4833 (mixedVector B) := by
  simpa only [nodeValue4833, Sparse.eval_nil] using zero4833 B _hB _hF

theorem sound4838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4838 node4838Labels = Sparse.eval nodeValue4838 (mixedVector B) := by
  simpa only [nodeValue4838, Sparse.eval_nil] using zero4838 B _hB _hF

theorem sound4851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4851 node4851Labels = Sparse.eval nodeValue4851 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4851) = mixedMoment B node4851 node4851Labels := rfl
  simpa [nodeValue4851, Sparse.eval] using hc.symm

theorem sound4852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4852 node4852Labels = Sparse.eval nodeValue4852 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4852) = mixedMoment B node4852 node4852Labels := rfl
  simpa [nodeValue4852, Sparse.eval] using hc.symm

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

theorem sound4864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4864 node4864Labels = Sparse.eval nodeValue4864 (mixedVector B) := by
  have h := singleton4864 B _hB
  rw [sound2105 B _hB _hF, sound2241 B _hB _hF] at h
  norm_num [nodeValue4864, nodeValue2105, nodeValue2241, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4888 node4888Labels = Sparse.eval nodeValue4888 (mixedVector B) := by
  have h := singleton4888 B _hB
  rw [sound2244 B _hB _hF, sound2262 B _hB _hF] at h
  norm_num [nodeValue4888, nodeValue2244, nodeValue2262, Sparse.eval] at h ⊢
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

theorem sound5227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5227 node5227Labels = Sparse.eval nodeValue5227 (mixedVector B) := by
  have h := singleton5227 B _hB
  rw [sound2671 B _hB _hF, sound3390 B _hB _hF] at h
  norm_num [nodeValue5227, nodeValue2671, nodeValue3390, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5237 node5237Labels = Sparse.eval nodeValue5237 (mixedVector B) := by
  have h := singleton5237 B _hB
  rw [sound2684 B _hB _hF, sound3394 B _hB _hF] at h
  norm_num [nodeValue5237, nodeValue2684, nodeValue3394, Sparse.eval] at h ⊢
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

theorem zero5283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5283 node5283Labels = 0 := by
  exact mixedMoment_alpha B hF node5283 node5283Labels 1 permutation152
    (by decide +kernel)

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

theorem sound5257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5257 node5257Labels = Sparse.eval nodeValue5257 (mixedVector B) := by
  have h := singleton5257 B _hB
  rw [sound2721 B _hB _hF, sound3532 B _hB _hF] at h
  norm_num [nodeValue5257, nodeValue2721, nodeValue3532, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5283 node5283Labels = Sparse.eval nodeValue5283 (mixedVector B) := by
  simpa only [nodeValue5283, Sparse.eval_nil] using zero5283 B _hB _hF

theorem sound5301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5301 node5301Labels = Sparse.eval nodeValue5301 (mixedVector B) := by
  have h := singleton5301 B _hB
  rw [sound3053 B _hB _hF, sound3619 B _hB _hF] at h
  norm_num [nodeValue5301, nodeValue3053, nodeValue3619, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5307 node5307Labels = Sparse.eval nodeValue5307 (mixedVector B) := by
  simpa only [nodeValue5307, Sparse.eval_nil] using zero5307 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources26
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq855 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm855 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA855 + difference 0 1) (sourceB855 + difference 1 0) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5283) := by
    have ha : (tripleCharges (sourceA855 + difference 0 1) (sourceB855 + difference 1 0) sourceC855) = raw14251 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14251; decide +kernel
    rw [ha]
    exact (canonical14251 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA855 + difference 0 2) (sourceB855 + difference 2 0) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA855 + difference 0 2) (sourceB855 + difference 2 0) sourceC855) = raw14252 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14252; decide +kernel
    rw [ha]
    exact (canonical14252 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA855 + difference 0 3) (sourceB855 + difference 3 0) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA855 + difference 0 3) (sourceB855 + difference 3 0) sourceC855) = raw14253 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14253; decide +kernel
    rw [ha]
    exact (canonical14253 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA855 + difference 0 4) (sourceB855 + difference 4 0) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA855 + difference 0 4) (sourceB855 + difference 4 0) sourceC855) = raw14254 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14254; decide +kernel
    rw [ha]
    exact (canonical14254 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA855 + difference 0 5) (sourceB855 + difference 5 0) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA855 + difference 0 5) (sourceB855 + difference 5 0) sourceC855) = raw13835 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw13835; decide +kernel
    rw [ha]
    exact (canonical13835 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA855 + difference 1 0) (sourceB855 + difference 0 1) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA855 + difference 1 0) (sourceB855 + difference 0 1) sourceC855) = raw13852 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw13852; decide +kernel
    rw [ha]
    exact (canonical13852 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA855 + difference 1 2) (sourceB855 + difference 2 1) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5227) := by
    have ha : (tripleCharges (sourceA855 + difference 1 2) (sourceB855 + difference 2 1) sourceC855) = raw13854 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw13854; decide +kernel
    rw [ha]
    exact (canonical13854 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA855 + difference 1 3) (sourceB855 + difference 3 1) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA855 + difference 1 3) (sourceB855 + difference 3 1) sourceC855) = raw13855 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw13855; decide +kernel
    rw [ha]
    exact (canonical13855 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA855 + difference 1 4) (sourceB855 + difference 4 1) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA855 + difference 1 4) (sourceB855 + difference 4 1) sourceC855) = raw13856 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw13856; decide +kernel
    rw [ha]
    exact (canonical13856 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA855 + difference 1 5) (sourceB855 + difference 5 1) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA855 + difference 1 5) (sourceB855 + difference 5 1) sourceC855) = raw13642 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw13642; decide +kernel
    rw [ha]
    exact (canonical13642 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA855 + difference 2 0) (sourceB855 + difference 0 2) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA855 + difference 2 0) (sourceB855 + difference 0 2) sourceC855) = raw14255 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14255; decide +kernel
    rw [ha]
    exact (canonical14255 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA855 + difference 2 1) (sourceB855 + difference 1 2) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA855 + difference 2 1) (sourceB855 + difference 1 2) sourceC855) = raw14256 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14256; decide +kernel
    rw [ha]
    exact (canonical14256 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA855 + difference 2 3) (sourceB855 + difference 3 2) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA855 + difference 2 3) (sourceB855 + difference 3 2) sourceC855) = raw12199 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw12199; decide +kernel
    rw [ha]
    exact (canonical12199 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA855 + difference 2 4) (sourceB855 + difference 4 2) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA855 + difference 2 4) (sourceB855 + difference 4 2) sourceC855) = raw12195 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw12195; decide +kernel
    rw [ha]
    exact (canonical12195 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA855 + difference 2 5) (sourceB855 + difference 5 2) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA855 + difference 2 5) (sourceB855 + difference 5 2) sourceC855) = raw13641 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw13641; decide +kernel
    rw [ha]
    exact (canonical13641 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA855 + difference 3 0) (sourceB855 + difference 0 3) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA855 + difference 3 0) (sourceB855 + difference 0 3) sourceC855) = raw14203 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14203; decide +kernel
    rw [ha]
    exact (canonical14203 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA855 + difference 3 1) (sourceB855 + difference 1 3) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA855 + difference 3 1) (sourceB855 + difference 1 3) sourceC855) = raw14204 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14204; decide +kernel
    rw [ha]
    exact (canonical14204 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA855 + difference 3 2) (sourceB855 + difference 2 3) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA855 + difference 3 2) (sourceB855 + difference 2 3) sourceC855) = raw14205 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14205; decide +kernel
    rw [ha]
    exact (canonical14205 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA855 + difference 3 4) (sourceB855 + difference 4 3) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA855 + difference 3 4) (sourceB855 + difference 4 3) sourceC855) = raw14206 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14206; decide +kernel
    rw [ha]
    exact (canonical14206 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA855 + difference 3 5) (sourceB855 + difference 5 3) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA855 + difference 3 5) (sourceB855 + difference 5 3) sourceC855) = raw13845 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw13845; decide +kernel
    rw [ha]
    exact (canonical13845 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA855 + difference 4 0) (sourceB855 + difference 0 4) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA855 + difference 4 0) (sourceB855 + difference 0 4) sourceC855) = raw14257 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14257; decide +kernel
    rw [ha]
    exact (canonical14257 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA855 + difference 4 1) (sourceB855 + difference 1 4) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA855 + difference 4 1) (sourceB855 + difference 1 4) sourceC855) = raw14258 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14258; decide +kernel
    rw [ha]
    exact (canonical14258 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA855 + difference 4 2) (sourceB855 + difference 2 4) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA855 + difference 4 2) (sourceB855 + difference 2 4) sourceC855) = raw14259 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14259; decide +kernel
    rw [ha]
    exact (canonical14259 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA855 + difference 4 3) (sourceB855 + difference 3 4) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA855 + difference 4 3) (sourceB855 + difference 3 4) sourceC855) = raw14260 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14260; decide +kernel
    rw [ha]
    exact (canonical14260 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA855 + difference 4 5) (sourceB855 + difference 5 4) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA855 + difference 4 5) (sourceB855 + difference 5 4) sourceC855) = raw13849 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw13849; decide +kernel
    rw [ha]
    exact (canonical13849 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA855 + difference 5 0) (sourceB855 + difference 0 5) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA855 + difference 5 0) (sourceB855 + difference 0 5) sourceC855) = raw14261 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14261; decide +kernel
    rw [ha]
    exact (canonical14261 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA855 + difference 5 1) (sourceB855 + difference 1 5) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA855 + difference 5 1) (sourceB855 + difference 1 5) sourceC855) = raw14262 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14262; decide +kernel
    rw [ha]
    exact (canonical14262 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA855 + difference 5 2) (sourceB855 + difference 2 5) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA855 + difference 5 2) (sourceB855 + difference 2 5) sourceC855) = raw14263 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw14263; decide +kernel
    rw [ha]
    exact (canonical14263 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA855 + difference 5 3) (sourceB855 + difference 3 5) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA855 + difference 5 3) (sourceB855 + difference 3 5) sourceC855) = raw12197 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw12197; decide +kernel
    rw [ha]
    exact (canonical12197 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA855 + difference 5 4) (sourceB855 + difference 4 5) sourceC855) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA855 + difference 5 4) (sourceB855 + difference 4 5) sourceC855) = raw12193 := by
      apply Matrix.ext; unfold tripleCharges sourceA855 sourceB855 sourceC855 difference raw12193; decide +kernel
    rw [ha]
    exact (canonical12193 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA855 sourceB855 sourceC855
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm855, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq856 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm856 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA856 + difference 0 1) (sourceB856 + difference 1 0) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA856 + difference 0 1) (sourceB856 + difference 1 0) sourceC856) = raw14264 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14264; decide +kernel
    rw [ha]
    exact (canonical14264 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA856 + difference 0 2) (sourceB856 + difference 2 0) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA856 + difference 0 2) (sourceB856 + difference 2 0) sourceC856) = raw14265 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14265; decide +kernel
    rw [ha]
    exact (canonical14265 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA856 + difference 0 3) (sourceB856 + difference 3 0) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5283) := by
    have ha : (tripleCharges (sourceA856 + difference 0 3) (sourceB856 + difference 3 0) sourceC856) = raw5431 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw5431; decide +kernel
    rw [ha]
    exact (canonical5431 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA856 + difference 0 4) (sourceB856 + difference 4 0) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA856 + difference 0 4) (sourceB856 + difference 4 0) sourceC856) = raw14266 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14266; decide +kernel
    rw [ha]
    exact (canonical14266 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA856 + difference 0 5) (sourceB856 + difference 5 0) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA856 + difference 0 5) (sourceB856 + difference 5 0) sourceC856) = raw14267 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14267; decide +kernel
    rw [ha]
    exact (canonical14267 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA856 + difference 1 0) (sourceB856 + difference 0 1) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA856 + difference 1 0) (sourceB856 + difference 0 1) sourceC856) = raw14268 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14268; decide +kernel
    rw [ha]
    exact (canonical14268 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA856 + difference 1 2) (sourceB856 + difference 2 1) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA856 + difference 1 2) (sourceB856 + difference 2 1) sourceC856) = raw14269 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14269; decide +kernel
    rw [ha]
    exact (canonical14269 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA856 + difference 1 3) (sourceB856 + difference 3 1) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA856 + difference 1 3) (sourceB856 + difference 3 1) sourceC856) = raw5436 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw5436; decide +kernel
    rw [ha]
    exact (canonical5436 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA856 + difference 1 4) (sourceB856 + difference 4 1) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA856 + difference 1 4) (sourceB856 + difference 4 1) sourceC856) = raw14270 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14270; decide +kernel
    rw [ha]
    exact (canonical14270 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA856 + difference 1 5) (sourceB856 + difference 5 1) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA856 + difference 1 5) (sourceB856 + difference 5 1) sourceC856) = raw14271 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14271; decide +kernel
    rw [ha]
    exact (canonical14271 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA856 + difference 2 0) (sourceB856 + difference 0 2) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA856 + difference 2 0) (sourceB856 + difference 0 2) sourceC856) = raw14272 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14272; decide +kernel
    rw [ha]
    exact (canonical14272 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA856 + difference 2 1) (sourceB856 + difference 1 2) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA856 + difference 2 1) (sourceB856 + difference 1 2) sourceC856) = raw14273 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14273; decide +kernel
    rw [ha]
    exact (canonical14273 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA856 + difference 2 3) (sourceB856 + difference 3 2) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA856 + difference 2 3) (sourceB856 + difference 3 2) sourceC856) = raw5441 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw5441; decide +kernel
    rw [ha]
    exact (canonical5441 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA856 + difference 2 4) (sourceB856 + difference 4 2) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA856 + difference 2 4) (sourceB856 + difference 4 2) sourceC856) = raw14274 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14274; decide +kernel
    rw [ha]
    exact (canonical14274 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA856 + difference 2 5) (sourceB856 + difference 5 2) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA856 + difference 2 5) (sourceB856 + difference 5 2) sourceC856) = raw14275 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14275; decide +kernel
    rw [ha]
    exact (canonical14275 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA856 + difference 3 0) (sourceB856 + difference 0 3) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4438) := by
    have ha : (tripleCharges (sourceA856 + difference 3 0) (sourceB856 + difference 0 3) sourceC856) = raw14276 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14276; decide +kernel
    rw [ha]
    exact (canonical14276 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA856 + difference 3 1) (sourceB856 + difference 1 3) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA856 + difference 3 1) (sourceB856 + difference 1 3) sourceC856) = raw14277 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14277; decide +kernel
    rw [ha]
    exact (canonical14277 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA856 + difference 3 2) (sourceB856 + difference 2 3) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA856 + difference 3 2) (sourceB856 + difference 2 3) sourceC856) = raw14278 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14278; decide +kernel
    rw [ha]
    exact (canonical14278 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA856 + difference 3 4) (sourceB856 + difference 4 3) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA856 + difference 3 4) (sourceB856 + difference 4 3) sourceC856) = raw14279 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14279; decide +kernel
    rw [ha]
    exact (canonical14279 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA856 + difference 3 5) (sourceB856 + difference 5 3) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA856 + difference 3 5) (sourceB856 + difference 5 3) sourceC856) = raw14280 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14280; decide +kernel
    rw [ha]
    exact (canonical14280 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA856 + difference 4 0) (sourceB856 + difference 0 4) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA856 + difference 4 0) (sourceB856 + difference 0 4) sourceC856) = raw14281 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14281; decide +kernel
    rw [ha]
    exact (canonical14281 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA856 + difference 4 1) (sourceB856 + difference 1 4) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA856 + difference 4 1) (sourceB856 + difference 1 4) sourceC856) = raw14282 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14282; decide +kernel
    rw [ha]
    exact (canonical14282 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA856 + difference 4 2) (sourceB856 + difference 2 4) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA856 + difference 4 2) (sourceB856 + difference 2 4) sourceC856) = raw14283 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14283; decide +kernel
    rw [ha]
    exact (canonical14283 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA856 + difference 4 3) (sourceB856 + difference 3 4) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA856 + difference 4 3) (sourceB856 + difference 3 4) sourceC856) = raw5451 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw5451; decide +kernel
    rw [ha]
    exact (canonical5451 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA856 + difference 4 5) (sourceB856 + difference 5 4) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA856 + difference 4 5) (sourceB856 + difference 5 4) sourceC856) = raw14284 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14284; decide +kernel
    rw [ha]
    exact (canonical14284 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA856 + difference 5 0) (sourceB856 + difference 0 5) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA856 + difference 5 0) (sourceB856 + difference 0 5) sourceC856) = raw5442 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw5442; decide +kernel
    rw [ha]
    exact (canonical5442 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA856 + difference 5 1) (sourceB856 + difference 1 5) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA856 + difference 5 1) (sourceB856 + difference 1 5) sourceC856) = raw5443 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw5443; decide +kernel
    rw [ha]
    exact (canonical5443 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA856 + difference 5 2) (sourceB856 + difference 2 5) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA856 + difference 5 2) (sourceB856 + difference 2 5) sourceC856) = raw5444 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw5444; decide +kernel
    rw [ha]
    exact (canonical5444 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA856 + difference 5 3) (sourceB856 + difference 3 5) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA856 + difference 5 3) (sourceB856 + difference 3 5) sourceC856) = raw14285 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw14285; decide +kernel
    rw [ha]
    exact (canonical14285 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA856 + difference 5 4) (sourceB856 + difference 4 5) sourceC856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA856 + difference 5 4) (sourceB856 + difference 4 5) sourceC856) = raw5445 := by
      apply Matrix.ext; unfold tripleCharges sourceA856 sourceB856 sourceC856 difference raw5445; decide +kernel
    rw [ha]
    exact (canonical5445 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA856 sourceB856 sourceC856
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm856, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq857 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm857 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA857 + difference 0 1) (sourceB857 + difference 1 0) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA857 + difference 0 1) (sourceB857 + difference 1 0) sourceC857) = raw14286 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14286; decide +kernel
    rw [ha]
    exact (canonical14286 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA857 + difference 0 2) (sourceB857 + difference 2 0) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA857 + difference 0 2) (sourceB857 + difference 2 0) sourceC857) = raw14287 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14287; decide +kernel
    rw [ha]
    exact (canonical14287 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA857 + difference 0 3) (sourceB857 + difference 3 0) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2752) := by
    have ha : (tripleCharges (sourceA857 + difference 0 3) (sourceB857 + difference 3 0) sourceC857) = raw5491 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw5491; decide +kernel
    rw [ha]
    exact (canonical5491 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA857 + difference 0 4) (sourceB857 + difference 4 0) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA857 + difference 0 4) (sourceB857 + difference 4 0) sourceC857) = raw14288 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14288; decide +kernel
    rw [ha]
    exact (canonical14288 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA857 + difference 0 5) (sourceB857 + difference 5 0) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA857 + difference 0 5) (sourceB857 + difference 5 0) sourceC857) = raw14289 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14289; decide +kernel
    rw [ha]
    exact (canonical14289 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA857 + difference 1 0) (sourceB857 + difference 0 1) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA857 + difference 1 0) (sourceB857 + difference 0 1) sourceC857) = raw14290 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14290; decide +kernel
    rw [ha]
    exact (canonical14290 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA857 + difference 1 2) (sourceB857 + difference 2 1) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA857 + difference 1 2) (sourceB857 + difference 2 1) sourceC857) = raw14291 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14291; decide +kernel
    rw [ha]
    exact (canonical14291 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA857 + difference 1 3) (sourceB857 + difference 3 1) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA857 + difference 1 3) (sourceB857 + difference 3 1) sourceC857) = raw5496 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw5496; decide +kernel
    rw [ha]
    exact (canonical5496 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA857 + difference 1 4) (sourceB857 + difference 4 1) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA857 + difference 1 4) (sourceB857 + difference 4 1) sourceC857) = raw14292 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14292; decide +kernel
    rw [ha]
    exact (canonical14292 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA857 + difference 1 5) (sourceB857 + difference 5 1) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA857 + difference 1 5) (sourceB857 + difference 5 1) sourceC857) = raw14293 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14293; decide +kernel
    rw [ha]
    exact (canonical14293 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA857 + difference 2 0) (sourceB857 + difference 0 2) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA857 + difference 2 0) (sourceB857 + difference 0 2) sourceC857) = raw14294 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14294; decide +kernel
    rw [ha]
    exact (canonical14294 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA857 + difference 2 1) (sourceB857 + difference 1 2) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA857 + difference 2 1) (sourceB857 + difference 1 2) sourceC857) = raw14295 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14295; decide +kernel
    rw [ha]
    exact (canonical14295 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA857 + difference 2 3) (sourceB857 + difference 3 2) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA857 + difference 2 3) (sourceB857 + difference 3 2) sourceC857) = raw5501 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw5501; decide +kernel
    rw [ha]
    exact (canonical5501 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA857 + difference 2 4) (sourceB857 + difference 4 2) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA857 + difference 2 4) (sourceB857 + difference 4 2) sourceC857) = raw14296 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14296; decide +kernel
    rw [ha]
    exact (canonical14296 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA857 + difference 2 5) (sourceB857 + difference 5 2) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA857 + difference 2 5) (sourceB857 + difference 5 2) sourceC857) = raw14297 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14297; decide +kernel
    rw [ha]
    exact (canonical14297 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA857 + difference 3 0) (sourceB857 + difference 0 3) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1705) := by
    have ha : (tripleCharges (sourceA857 + difference 3 0) (sourceB857 + difference 0 3) sourceC857) = raw14298 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14298; decide +kernel
    rw [ha]
    exact (canonical14298 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA857 + difference 3 1) (sourceB857 + difference 1 3) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA857 + difference 3 1) (sourceB857 + difference 1 3) sourceC857) = raw14299 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14299; decide +kernel
    rw [ha]
    exact (canonical14299 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA857 + difference 3 2) (sourceB857 + difference 2 3) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA857 + difference 3 2) (sourceB857 + difference 2 3) sourceC857) = raw14300 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14300; decide +kernel
    rw [ha]
    exact (canonical14300 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA857 + difference 3 4) (sourceB857 + difference 4 3) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA857 + difference 3 4) (sourceB857 + difference 4 3) sourceC857) = raw14301 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14301; decide +kernel
    rw [ha]
    exact (canonical14301 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA857 + difference 3 5) (sourceB857 + difference 5 3) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA857 + difference 3 5) (sourceB857 + difference 5 3) sourceC857) = raw14302 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14302; decide +kernel
    rw [ha]
    exact (canonical14302 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA857 + difference 4 0) (sourceB857 + difference 0 4) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA857 + difference 4 0) (sourceB857 + difference 0 4) sourceC857) = raw14303 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14303; decide +kernel
    rw [ha]
    exact (canonical14303 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA857 + difference 4 1) (sourceB857 + difference 1 4) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA857 + difference 4 1) (sourceB857 + difference 1 4) sourceC857) = raw14304 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14304; decide +kernel
    rw [ha]
    exact (canonical14304 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA857 + difference 4 2) (sourceB857 + difference 2 4) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA857 + difference 4 2) (sourceB857 + difference 2 4) sourceC857) = raw14305 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14305; decide +kernel
    rw [ha]
    exact (canonical14305 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA857 + difference 4 3) (sourceB857 + difference 3 4) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2252) := by
    have ha : (tripleCharges (sourceA857 + difference 4 3) (sourceB857 + difference 3 4) sourceC857) = raw5511 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw5511; decide +kernel
    rw [ha]
    exact (canonical5511 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA857 + difference 4 5) (sourceB857 + difference 5 4) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA857 + difference 4 5) (sourceB857 + difference 5 4) sourceC857) = raw14306 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14306; decide +kernel
    rw [ha]
    exact (canonical14306 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA857 + difference 5 0) (sourceB857 + difference 0 5) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA857 + difference 5 0) (sourceB857 + difference 0 5) sourceC857) = raw5502 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw5502; decide +kernel
    rw [ha]
    exact (canonical5502 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA857 + difference 5 1) (sourceB857 + difference 1 5) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA857 + difference 5 1) (sourceB857 + difference 1 5) sourceC857) = raw5503 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw5503; decide +kernel
    rw [ha]
    exact (canonical5503 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA857 + difference 5 2) (sourceB857 + difference 2 5) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA857 + difference 5 2) (sourceB857 + difference 2 5) sourceC857) = raw5504 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw5504; decide +kernel
    rw [ha]
    exact (canonical5504 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA857 + difference 5 3) (sourceB857 + difference 3 5) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2252) := by
    have ha : (tripleCharges (sourceA857 + difference 5 3) (sourceB857 + difference 3 5) sourceC857) = raw14307 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw14307; decide +kernel
    rw [ha]
    exact (canonical14307 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA857 + difference 5 4) (sourceB857 + difference 4 5) sourceC857) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA857 + difference 5 4) (sourceB857 + difference 4 5) sourceC857) = raw5505 := by
      apply Matrix.ext; unfold tripleCharges sourceA857 sourceB857 sourceC857 difference raw5505; decide +kernel
    rw [ha]
    exact (canonical5505 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA857 sourceB857 sourceC857
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm857, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq858 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm858 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA858 + difference 0 1) (sourceB858 + difference 1 0) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA858 + difference 0 1) (sourceB858 + difference 1 0) sourceC858) = raw14308 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14308; decide +kernel
    rw [ha]
    exact (canonical14308 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA858 + difference 0 2) (sourceB858 + difference 2 0) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA858 + difference 0 2) (sourceB858 + difference 2 0) sourceC858) = raw14309 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14309; decide +kernel
    rw [ha]
    exact (canonical14309 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA858 + difference 0 3) (sourceB858 + difference 3 0) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA858 + difference 0 3) (sourceB858 + difference 3 0) sourceC858) = raw11319 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw11319; decide +kernel
    rw [ha]
    exact (canonical11319 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA858 + difference 0 4) (sourceB858 + difference 4 0) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA858 + difference 0 4) (sourceB858 + difference 4 0) sourceC858) = raw14310 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14310; decide +kernel
    rw [ha]
    exact (canonical14310 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA858 + difference 0 5) (sourceB858 + difference 5 0) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA858 + difference 0 5) (sourceB858 + difference 5 0) sourceC858) = raw14311 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14311; decide +kernel
    rw [ha]
    exact (canonical14311 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA858 + difference 1 0) (sourceB858 + difference 0 1) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA858 + difference 1 0) (sourceB858 + difference 0 1) sourceC858) = raw14312 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14312; decide +kernel
    rw [ha]
    exact (canonical14312 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA858 + difference 1 2) (sourceB858 + difference 2 1) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA858 + difference 1 2) (sourceB858 + difference 2 1) sourceC858) = raw14313 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14313; decide +kernel
    rw [ha]
    exact (canonical14313 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA858 + difference 1 3) (sourceB858 + difference 3 1) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA858 + difference 1 3) (sourceB858 + difference 3 1) sourceC858) = raw11324 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw11324; decide +kernel
    rw [ha]
    exact (canonical11324 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA858 + difference 1 4) (sourceB858 + difference 4 1) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA858 + difference 1 4) (sourceB858 + difference 4 1) sourceC858) = raw14314 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14314; decide +kernel
    rw [ha]
    exact (canonical14314 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA858 + difference 1 5) (sourceB858 + difference 5 1) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA858 + difference 1 5) (sourceB858 + difference 5 1) sourceC858) = raw14315 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14315; decide +kernel
    rw [ha]
    exact (canonical14315 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA858 + difference 2 0) (sourceB858 + difference 0 2) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA858 + difference 2 0) (sourceB858 + difference 0 2) sourceC858) = raw14316 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14316; decide +kernel
    rw [ha]
    exact (canonical14316 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA858 + difference 2 1) (sourceB858 + difference 1 2) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA858 + difference 2 1) (sourceB858 + difference 1 2) sourceC858) = raw14317 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14317; decide +kernel
    rw [ha]
    exact (canonical14317 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA858 + difference 2 3) (sourceB858 + difference 3 2) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA858 + difference 2 3) (sourceB858 + difference 3 2) sourceC858) = raw11329 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw11329; decide +kernel
    rw [ha]
    exact (canonical11329 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA858 + difference 2 4) (sourceB858 + difference 4 2) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA858 + difference 2 4) (sourceB858 + difference 4 2) sourceC858) = raw14318 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14318; decide +kernel
    rw [ha]
    exact (canonical14318 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA858 + difference 2 5) (sourceB858 + difference 5 2) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA858 + difference 2 5) (sourceB858 + difference 5 2) sourceC858) = raw14319 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14319; decide +kernel
    rw [ha]
    exact (canonical14319 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA858 + difference 3 0) (sourceB858 + difference 0 3) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4248) := by
    have ha : (tripleCharges (sourceA858 + difference 3 0) (sourceB858 + difference 0 3) sourceC858) = raw14320 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14320; decide +kernel
    rw [ha]
    exact (canonical14320 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA858 + difference 3 1) (sourceB858 + difference 1 3) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA858 + difference 3 1) (sourceB858 + difference 1 3) sourceC858) = raw14321 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14321; decide +kernel
    rw [ha]
    exact (canonical14321 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA858 + difference 3 2) (sourceB858 + difference 2 3) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA858 + difference 3 2) (sourceB858 + difference 2 3) sourceC858) = raw14322 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14322; decide +kernel
    rw [ha]
    exact (canonical14322 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA858 + difference 3 4) (sourceB858 + difference 4 3) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA858 + difference 3 4) (sourceB858 + difference 4 3) sourceC858) = raw14323 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14323; decide +kernel
    rw [ha]
    exact (canonical14323 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA858 + difference 3 5) (sourceB858 + difference 5 3) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA858 + difference 3 5) (sourceB858 + difference 5 3) sourceC858) = raw14324 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14324; decide +kernel
    rw [ha]
    exact (canonical14324 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA858 + difference 4 0) (sourceB858 + difference 0 4) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA858 + difference 4 0) (sourceB858 + difference 0 4) sourceC858) = raw14325 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14325; decide +kernel
    rw [ha]
    exact (canonical14325 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA858 + difference 4 1) (sourceB858 + difference 1 4) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA858 + difference 4 1) (sourceB858 + difference 1 4) sourceC858) = raw14326 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14326; decide +kernel
    rw [ha]
    exact (canonical14326 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA858 + difference 4 2) (sourceB858 + difference 2 4) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA858 + difference 4 2) (sourceB858 + difference 2 4) sourceC858) = raw14327 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14327; decide +kernel
    rw [ha]
    exact (canonical14327 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA858 + difference 4 3) (sourceB858 + difference 3 4) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA858 + difference 4 3) (sourceB858 + difference 3 4) sourceC858) = raw11339 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw11339; decide +kernel
    rw [ha]
    exact (canonical11339 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA858 + difference 4 5) (sourceB858 + difference 5 4) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA858 + difference 4 5) (sourceB858 + difference 5 4) sourceC858) = raw14328 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14328; decide +kernel
    rw [ha]
    exact (canonical14328 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA858 + difference 5 0) (sourceB858 + difference 0 5) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA858 + difference 5 0) (sourceB858 + difference 0 5) sourceC858) = raw11330 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw11330; decide +kernel
    rw [ha]
    exact (canonical11330 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA858 + difference 5 1) (sourceB858 + difference 1 5) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA858 + difference 5 1) (sourceB858 + difference 1 5) sourceC858) = raw11331 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw11331; decide +kernel
    rw [ha]
    exact (canonical11331 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA858 + difference 5 2) (sourceB858 + difference 2 5) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA858 + difference 5 2) (sourceB858 + difference 2 5) sourceC858) = raw11332 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw11332; decide +kernel
    rw [ha]
    exact (canonical11332 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA858 + difference 5 3) (sourceB858 + difference 3 5) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA858 + difference 5 3) (sourceB858 + difference 3 5) sourceC858) = raw14329 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw14329; decide +kernel
    rw [ha]
    exact (canonical14329 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA858 + difference 5 4) (sourceB858 + difference 4 5) sourceC858) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA858 + difference 5 4) (sourceB858 + difference 4 5) sourceC858) = raw11333 := by
      apply Matrix.ext; unfold tripleCharges sourceA858 sourceB858 sourceC858 difference raw11333; decide +kernel
    rw [ha]
    exact (canonical11333 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA858 sourceB858 sourceC858
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm858, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck745 : Integer.Sparse.reindex keyMap MixedData.row745 = numericRow745 := by decide +kernel

theorem numericCheck745 (x : Master → ℝ) : Integer.Sparse.eval numericRow745 x =
    (5760 : ℝ) * reducedSource745 x := by
  norm_num [numericRow745, reducedSource745, Integer.Sparse.eval, Sparse.eval, nodeValue4083, nodeValue4833, nodeValue4838, nodeValue5227, nodeValue5237, nodeValue5247, nodeValue5257, nodeValue5271, nodeValue5273, nodeValue5283, nodeValue5292, nodeValue5301, nodeValue5307] <;> ring

theorem reindexCheck746 : Integer.Sparse.reindex keyMap MixedData.row746 = numericRow746 := by decide +kernel

theorem numericCheck746 (x : Master → ℝ) : Integer.Sparse.eval numericRow746 x =
    (8640 : ℝ) * reducedSource746 x := by
  norm_num [numericRow746, reducedSource746, Integer.Sparse.eval, Sparse.eval, nodeValue4438, nodeValue4439, nodeValue4456, nodeValue4851, nodeValue4852, nodeValue4864, nodeValue4885, nodeValue4887, nodeValue4888, nodeValue4889, nodeValue4893, nodeValue5281, nodeValue5283, nodeValue5292] <;> ring

theorem reindexCheck747 : Integer.Sparse.reindex keyMap MixedData.row747 = numericRow747 := by decide +kernel

theorem numericCheck747 (x : Master → ℝ) : Integer.Sparse.eval numericRow747 x =
    (2160 : ℝ) * reducedSource747 x := by
  norm_num [numericRow747, reducedSource747, Integer.Sparse.eval, Sparse.eval, nodeValue1705, nodeValue1706, nodeValue1713, nodeValue2240, nodeValue2241, nodeValue2243, nodeValue2250, nodeValue2252, nodeValue2262, nodeValue2263, nodeValue2277, nodeValue2750, nodeValue2752, nodeValue2766] <;> ring

theorem reindexCheck748 : Integer.Sparse.reindex keyMap MixedData.row748 = numericRow748 := by decide +kernel

theorem numericCheck748 (x : Master → ℝ) : Integer.Sparse.eval numericRow748 x =
    (4320 : ℝ) * reducedSource748 x := by
  norm_num [numericRow748, reducedSource748, Integer.Sparse.eval, Sparse.eval, nodeValue4248, nodeValue4249, nodeValue4801, nodeValue4802, nodeValue4831, nodeValue4888, nodeValue5433, nodeValue5452] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero745 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource745 (mixedVector B) = 0 := by
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  have h4833 : mixedVector B (Sum.inr 4833) = Sparse.eval nodeValue4833 (mixedVector B) := by
    change mixedMoment B node4833 node4833Labels = _
    exact sound4833 B hB hF
  have h4838 : mixedVector B (Sum.inr 4838) = Sparse.eval nodeValue4838 (mixedVector B) := by
    change mixedMoment B node4838 node4838Labels = _
    exact sound4838 B hB hF
  have h5227 : mixedVector B (Sum.inr 5227) = Sparse.eval nodeValue5227 (mixedVector B) := by
    change mixedMoment B node5227 node5227Labels = _
    exact sound5227 B hB hF
  have h5237 : mixedVector B (Sum.inr 5237) = Sparse.eval nodeValue5237 (mixedVector B) := by
    change mixedMoment B node5237 node5237Labels = _
    exact sound5237 B hB hF
  have h5247 : mixedVector B (Sum.inr 5247) = Sparse.eval nodeValue5247 (mixedVector B) := by
    change mixedMoment B node5247 node5247Labels = _
    exact sound5247 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  have h5273 : mixedVector B (Sum.inr 5273) = Sparse.eval nodeValue5273 (mixedVector B) := by
    change mixedMoment B node5273 node5273Labels = _
    exact sound5273 B hB hF
  have h5283 : mixedVector B (Sum.inr 5283) = Sparse.eval nodeValue5283 (mixedVector B) := by
    change mixedMoment B node5283 node5283Labels = _
    exact sound5283 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292_e B hB hF
  have h5301 : mixedVector B (Sum.inr 5301) = Sparse.eval nodeValue5301 (mixedVector B) := by
    change mixedMoment B node5301 node5301Labels = _
    exact sound5301 B hB hF
  have h5307 : mixedVector B (Sum.inr 5307) = Sparse.eval nodeValue5307 (mixedVector B) := by
    change mixedMoment B node5307 node5307Labels = _
    exact sound5307 B hB hF
  simpa only [sourceForm855, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4083, h4833, h4838, h5227, h5237, h5247, h5257, h5271, h5273, h5283, h5292, h5301, h5307, reducedSource745] using sourceEq855 B hB

theorem rowSound745 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row745 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck745, numericCheck745, reducedZero745 B hB hF, mul_zero]

theorem reducedZero746 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource746 (mixedVector B) = 0 := by
  have h4438 : mixedVector B (Sum.inr 4438) = Sparse.eval nodeValue4438 (mixedVector B) := by
    change mixedMoment B node4438 node4438Labels = _
    exact sound4438 B hB hF
  have h4439 : mixedVector B (Sum.inr 4439) = Sparse.eval nodeValue4439 (mixedVector B) := by
    change mixedMoment B node4439 node4439Labels = _
    exact sound4439 B hB hF
  have h4456 : mixedVector B (Sum.inr 4456) = Sparse.eval nodeValue4456 (mixedVector B) := by
    change mixedMoment B node4456 node4456Labels = _
    exact sound4456 B hB hF
  have h4851 : mixedVector B (Sum.inr 4851) = Sparse.eval nodeValue4851 (mixedVector B) := by
    change mixedMoment B node4851 node4851Labels = _
    exact sound4851 B hB hF
  have h4852 : mixedVector B (Sum.inr 4852) = Sparse.eval nodeValue4852 (mixedVector B) := by
    change mixedMoment B node4852 node4852Labels = _
    exact sound4852 B hB hF
  have h4864 : mixedVector B (Sum.inr 4864) = Sparse.eval nodeValue4864 (mixedVector B) := by
    change mixedMoment B node4864 node4864Labels = _
    exact sound4864 B hB hF
  have h4885 : mixedVector B (Sum.inr 4885) = Sparse.eval nodeValue4885 (mixedVector B) := by
    change mixedMoment B node4885 node4885Labels = _
    exact sound4885 B hB hF
  have h4887 : mixedVector B (Sum.inr 4887) = Sparse.eval nodeValue4887 (mixedVector B) := by
    change mixedMoment B node4887 node4887Labels = _
    exact sound4887 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h4893 : mixedVector B (Sum.inr 4893) = Sparse.eval nodeValue4893 (mixedVector B) := by
    change mixedMoment B node4893 node4893Labels = _
    exact sound4893 B hB hF
  have h5281 : mixedVector B (Sum.inr 5281) = Sparse.eval nodeValue5281 (mixedVector B) := by
    change mixedMoment B node5281 node5281Labels = _
    exact sound5281 B hB hF
  have h5283 : mixedVector B (Sum.inr 5283) = Sparse.eval nodeValue5283 (mixedVector B) := by
    change mixedMoment B node5283 node5283Labels = _
    exact sound5283 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292_e B hB hF
  simpa only [sourceForm856, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4438, h4439, h4456, h4851, h4852, h4864, h4885, h4887, h4888, h4889, h4893, h5281, h5283, h5292, reducedSource746] using sourceEq856 B hB

theorem rowSound746 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row746 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck746, numericCheck746, reducedZero746 B hB hF, mul_zero]

theorem reducedZero747 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource747 (mixedVector B) = 0 := by
  have h1705 : mixedVector B (Sum.inr 1705) = Sparse.eval nodeValue1705 (mixedVector B) := by
    change mixedMoment B node1705 node1705Labels = _
    exact sound1705 B hB hF
  have h1706 : mixedVector B (Sum.inr 1706) = Sparse.eval nodeValue1706 (mixedVector B) := by
    change mixedMoment B node1706 node1706Labels = _
    exact sound1706 B hB hF
  have h1713 : mixedVector B (Sum.inr 1713) = Sparse.eval nodeValue1713 (mixedVector B) := by
    change mixedMoment B node1713 node1713Labels = _
    exact sound1713 B hB hF
  have h2240 : mixedVector B (Sum.inr 2240) = Sparse.eval nodeValue2240 (mixedVector B) := by
    change mixedMoment B node2240 node2240Labels = _
    exact sound2240 B hB hF
  have h2241 : mixedVector B (Sum.inr 2241) = Sparse.eval nodeValue2241 (mixedVector B) := by
    change mixedMoment B node2241 node2241Labels = _
    exact sound2241 B hB hF
  have h2243 : mixedVector B (Sum.inr 2243) = Sparse.eval nodeValue2243 (mixedVector B) := by
    change mixedMoment B node2243 node2243Labels = _
    exact sound2243 B hB hF
  have h2250 : mixedVector B (Sum.inr 2250) = Sparse.eval nodeValue2250 (mixedVector B) := by
    change mixedMoment B node2250 node2250Labels = _
    exact sound2250 B hB hF
  have h2252 : mixedVector B (Sum.inr 2252) = Sparse.eval nodeValue2252 (mixedVector B) := by
    change mixedMoment B node2252 node2252Labels = _
    exact sound2252 B hB hF
  have h2262 : mixedVector B (Sum.inr 2262) = Sparse.eval nodeValue2262 (mixedVector B) := by
    change mixedMoment B node2262 node2262Labels = _
    exact sound2262 B hB hF
  have h2263 : mixedVector B (Sum.inr 2263) = Sparse.eval nodeValue2263 (mixedVector B) := by
    change mixedMoment B node2263 node2263Labels = _
    exact sound2263 B hB hF
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  have h2750 : mixedVector B (Sum.inr 2750) = Sparse.eval nodeValue2750 (mixedVector B) := by
    change mixedMoment B node2750 node2750Labels = _
    exact sound2750 B hB hF
  have h2752 : mixedVector B (Sum.inr 2752) = Sparse.eval nodeValue2752 (mixedVector B) := by
    change mixedMoment B node2752 node2752Labels = _
    exact sound2752 B hB hF
  have h2766 : mixedVector B (Sum.inr 2766) = Sparse.eval nodeValue2766 (mixedVector B) := by
    change mixedMoment B node2766 node2766Labels = _
    exact sound2766_e B hB hF
  simpa only [sourceForm857, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1705, h1706, h1713, h2240, h2241, h2243, h2250, h2252, h2262, h2263, h2277, h2750, h2752, h2766, reducedSource747] using sourceEq857 B hB

theorem rowSound747 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row747 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck747, numericCheck747, reducedZero747 B hB hF, mul_zero]

theorem reducedZero748 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource748 (mixedVector B) = 0 := by
  have h4248 : mixedVector B (Sum.inr 4248) = Sparse.eval nodeValue4248 (mixedVector B) := by
    change mixedMoment B node4248 node4248Labels = _
    exact sound4248 B hB hF
  have h4249 : mixedVector B (Sum.inr 4249) = Sparse.eval nodeValue4249 (mixedVector B) := by
    change mixedMoment B node4249 node4249Labels = _
    exact sound4249 B hB hF
  have h4801 : mixedVector B (Sum.inr 4801) = Sparse.eval nodeValue4801 (mixedVector B) := by
    change mixedMoment B node4801 node4801Labels = _
    exact sound4801 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4831 : mixedVector B (Sum.inr 4831) = Sparse.eval nodeValue4831 (mixedVector B) := by
    change mixedMoment B node4831 node4831Labels = _
    exact sound4831 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433_e B hB hF
  have h5452 : mixedVector B (Sum.inr 5452) = Sparse.eval nodeValue5452 (mixedVector B) := by
    change mixedMoment B node5452 node5452Labels = _
    exact sound5452_e B hB hF
  simpa only [sourceForm858, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4248, h4249, h4801, h4802, h4831, h4888, h5433, h5452, reducedSource748] using sourceEq858 B hB

theorem rowSound748 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row748 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck748, numericCheck748, reducedZero748 B hB hF, mul_zero]

theorem sourceRowsAt736 : MixedData.sourceRows (736 : Fin 2425) =
    MixedData.row736 := by decide +kernel

theorem sourceRowsAt737 : MixedData.sourceRows (737 : Fin 2425) =
    MixedData.row737 := by decide +kernel

theorem sourceRowsAt738 : MixedData.sourceRows (738 : Fin 2425) =
    MixedData.row738 := by decide +kernel

theorem sourceRowsAt739 : MixedData.sourceRows (739 : Fin 2425) =
    MixedData.row739 := by decide +kernel

theorem sourceRowsAt740 : MixedData.sourceRows (740 : Fin 2425) =
    MixedData.row740 := by decide +kernel

theorem sourceRowsAt741 : MixedData.sourceRows (741 : Fin 2425) =
    MixedData.row741 := by decide +kernel

theorem sourceRowsAt742 : MixedData.sourceRows (742 : Fin 2425) =
    MixedData.row742 := by decide +kernel

theorem sourceRowsAt743 : MixedData.sourceRows (743 : Fin 2425) =
    MixedData.row743 := by decide +kernel

theorem sourceRowsAt744 : MixedData.sourceRows (744 : Fin 2425) =
    MixedData.row744 := by decide +kernel

theorem sourceRowsAt745 : MixedData.sourceRows (745 : Fin 2425) =
    MixedData.row745 := by decide +kernel

theorem sourceRowsAt746 : MixedData.sourceRows (746 : Fin 2425) =
    MixedData.row746 := by decide +kernel

theorem sourceRowsAt747 : MixedData.sourceRows (747 : Fin 2425) =
    MixedData.row747 := by decide +kernel

theorem sourceRowsAt748 : MixedData.sourceRows (748 : Fin 2425) =
    MixedData.row748 := by decide +kernel

theorem sourceRowsAt749 : MixedData.sourceRows (749 : Fin 2425) =
    MixedData.row749 := by decide +kernel

theorem sourceRowsAt750 : MixedData.sourceRows (750 : Fin 2425) =
    MixedData.row750 := by decide +kernel

theorem sourceRowsAt751 : MixedData.sourceRows (751 : Fin 2425) =
    MixedData.row751 := by decide +kernel

theorem chunkSound46_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 46) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 736 ∨ k.val = 737 ∨ k.val = 738 ∨ k.val = 739 ∨ k.val = 740 ∨ k.val = 741 ∨ k.val = 742 ∨ k.val = 743 ∨ k.val = 744 ∨ k.val = 745 ∨ k.val = 746 ∨ k.val = 747 ∨ k.val = 748 ∨ k.val = 749 ∨ k.val = 750 ∨ k.val = 751 := by omega
  rcases heq with h736 | h737 | h738 | h739 | h740 | h741 | h742 | h743 | h744 | h745 | h746 | h747 | h748 | h749 | h750 | h751
  · have he : k = (736 : Fin 2425) := Fin.ext h736
    subst k
    rw [sourceRowsAt736]
    exact rowSound736_e B hB hF
  · have he : k = (737 : Fin 2425) := Fin.ext h737
    subst k
    rw [sourceRowsAt737]
    exact rowSound737_e B hB hF
  · have he : k = (738 : Fin 2425) := Fin.ext h738
    subst k
    rw [sourceRowsAt738]
    exact rowSound738_e B hB hF
  · have he : k = (739 : Fin 2425) := Fin.ext h739
    subst k
    rw [sourceRowsAt739]
    exact rowSound739_e B hB hF
  · have he : k = (740 : Fin 2425) := Fin.ext h740
    subst k
    rw [sourceRowsAt740]
    exact rowSound740_e B hB hF
  · have he : k = (741 : Fin 2425) := Fin.ext h741
    subst k
    rw [sourceRowsAt741]
    exact rowSound741_e B hB hF
  · have he : k = (742 : Fin 2425) := Fin.ext h742
    subst k
    rw [sourceRowsAt742]
    exact rowSound742_e B hB hF
  · have he : k = (743 : Fin 2425) := Fin.ext h743
    subst k
    rw [sourceRowsAt743]
    exact rowSound743_e B hB hF
  · have he : k = (744 : Fin 2425) := Fin.ext h744
    subst k
    rw [sourceRowsAt744]
    exact rowSound744_e B hB hF
  · have he : k = (745 : Fin 2425) := Fin.ext h745
    subst k
    rw [sourceRowsAt745]
    exact rowSound745 B hB hF
  · have he : k = (746 : Fin 2425) := Fin.ext h746
    subst k
    rw [sourceRowsAt746]
    exact rowSound746 B hB hF
  · have he : k = (747 : Fin 2425) := Fin.ext h747
    subst k
    rw [sourceRowsAt747]
    exact rowSound747 B hB hF
  · have he : k = (748 : Fin 2425) := Fin.ext h748
    subst k
    rw [sourceRowsAt748]
    exact rowSound748 B hB hF
  · have he : k = (749 : Fin 2425) := Fin.ext h749
    subst k
    rw [sourceRowsAt749]
    exact rowSound749_e B hB hF
  · have he : k = (750 : Fin 2425) := Fin.ext h750
    subst k
    rw [sourceRowsAt750]
    exact rowSound750_e B hB hF
  · have he : k = (751 : Fin 2425) := Fin.ext h751
    subst k
    rw [sourceRowsAt751]
    exact rowSound751_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound46_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound46_e_oai
