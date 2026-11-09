-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound55_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:23:10.912343+00:00
-- url     : https://prove2.me/submissions/b03faae7-e0dc-438e-bdfd-85e6899da4d2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3937_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3938_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3977_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3981_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3995_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound4003_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5482_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5485_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound881_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound882_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound883_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound884_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound885_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound887_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound888_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound890_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound891_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound894_e

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

theorem IsHadamard.column_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, conj (H k i) * H k j = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.2
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14797 raw14797Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw14797 raw14797Labels = mixedMoment B raw14797step0 raw14797step0Labels := by
      have hz : ∀ j, raw14797 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14797step0 = (fun i j => raw14797 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14797step0 raw14797; decide +kernel
      have hl : raw14797step0Labels = raw14797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14797 raw14797Labels permutation434 hz
    mixedMoment B raw14797step0 raw14797step0Labels = mixedMoment B raw14797step1 raw14797step1Labels := by
      have hz : ∀ j, raw14797step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14797step1 = (fun i j => raw14797step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14797step1 raw14797step0; decide +kernel
      have hl : raw14797step1Labels = raw14797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14797step0 raw14797step0Labels permutation80 hz
    mixedMoment B raw14797step1 raw14797step1Labels = mixedMoment B raw14797step2 raw14797step2Labels := by
      have ha : raw14797step2 = (fun i j => raw14797step1 (permutation31 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14797step2 raw14797step1; decide +kernel
      have hl : raw14797step2Labels = raw14797step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14797step1 raw14797step1Labels permutation31 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15140 raw15140Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw15140 raw15140Labels = mixedMoment B raw15140step0 raw15140step0Labels := by
      have hz : ∀ j, raw15140 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15140step0 = (fun i j => raw15140 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15140step0 raw15140; decide +kernel
      have hl : raw15140step0Labels = raw15140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15140 raw15140Labels permutation346 hz
    mixedMoment B raw15140step0 raw15140step0Labels = mixedMoment B raw15140step1 raw15140step1Labels := by
      have ha : raw15140step1 = (fun i j => raw15140step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15140step1 raw15140step0; decide +kernel
      have hl : raw15140step1Labels = raw15140step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15140step0 raw15140step0Labels permutation151 permutation7
    mixedMoment B raw15140step1 raw15140step1Labels = mixedMoment B raw15140step2 raw15140step2Labels := by
      have ha : raw15140step2 = -raw15140step1 := by apply Matrix.ext; change ∀ i j, raw15140step2 i j = -(raw15140step1 i j); unfold raw15140step2 raw15140step1; decide +kernel
      have hl : raw15140step2Labels = raw15140step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15140step2 raw15140step2Labels = mixedMoment B raw15140step3 raw15140step3Labels := by
      have ha : raw15140step3 = raw15140step2 := by apply Matrix.ext; unfold raw15140step3 raw15140step2; decide +kernel
      have hl : raw15140step2Labels = labelEmbedding1 ∘ raw15140step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15140step2 raw15140step2Labels raw15140step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3981 node3981Labels := by rfl

theorem canonical15151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15151 raw15151Labels = mixedMoment B node3977 node3977Labels := by
  calc
    mixedMoment B raw15151 raw15151Labels = mixedMoment B raw15151step0 raw15151step0Labels := by
      have ha : raw15151step0 = (fun i j => raw15151 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15151step0 raw15151; decide +kernel
      have hl : raw15151step0Labels = raw15151Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15151 raw15151Labels permutation682 permutation7
    mixedMoment B raw15151step0 raw15151step0Labels = mixedMoment B raw15151step1 raw15151step1Labels := by
      have ha : raw15151step1 = -raw15151step0 := by apply Matrix.ext; change ∀ i j, raw15151step1 i j = -(raw15151step0 i j); unfold raw15151step1 raw15151step0; decide +kernel
      have hl : raw15151step1Labels = raw15151step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15151step1 raw15151step1Labels = mixedMoment B raw15151step2 raw15151step2Labels := by
      have ha : raw15151step2 = raw15151step1 := by apply Matrix.ext; unfold raw15151step2 raw15151step1; decide +kernel
      have hl : raw15151step1Labels = labelEmbedding1 ∘ raw15151step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15151step1 raw15151step1Labels raw15151step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3977 node3977Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15715 raw15715Labels = mixedMoment B node3953 node3953Labels := by
  calc
    mixedMoment B raw15715 raw15715Labels = mixedMoment B raw15715step0 raw15715step0Labels := by
      have ha : raw15715step0 = (fun i j => raw15715 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15715step0 raw15715; decide +kernel
      have hl : raw15715step0Labels = raw15715Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15715 raw15715Labels permutation682 permutation7
    mixedMoment B raw15715step0 raw15715step0Labels = mixedMoment B raw15715step1 raw15715step1Labels := by
      have ha : raw15715step1 = -raw15715step0 := by apply Matrix.ext; change ∀ i j, raw15715step1 i j = -(raw15715step0 i j); unfold raw15715step1 raw15715step0; decide +kernel
      have hl : raw15715step1Labels = raw15715step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15715step1 raw15715step1Labels = mixedMoment B raw15715step2 raw15715step2Labels := by
      have ha : raw15715step2 = raw15715step1 := by apply Matrix.ext; unfold raw15715step2 raw15715step1; decide +kernel
      have hl : raw15715step1Labels = labelEmbedding1 ∘ raw15715step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15715step1 raw15715step1Labels raw15715step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3953 node3953Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15744 raw15744Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw15744 raw15744Labels = mixedMoment B raw15744step0 raw15744step0Labels := by
      have hz : ∀ j, raw15744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15744step0 = (fun i j => raw15744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15744step0 raw15744; decide +kernel
      have hl : raw15744step0Labels = raw15744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15744 raw15744Labels permutation346 hz
    mixedMoment B raw15744step0 raw15744step0Labels = mixedMoment B raw15744step1 raw15744step1Labels := by
      have ha : raw15744step1 = (fun i j => raw15744step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15744step1 raw15744step0; decide +kernel
      have hl : raw15744step1Labels = raw15744step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15744step0 raw15744step0Labels permutation44 permutation4
    mixedMoment B raw15744step1 raw15744step1Labels = mixedMoment B raw15744step2 raw15744step2Labels := by
      have ha : raw15744step2 = -raw15744step1 := by apply Matrix.ext; change ∀ i j, raw15744step2 i j = -(raw15744step1 i j); unfold raw15744step2 raw15744step1; decide +kernel
      have hl : raw15744step2Labels = raw15744step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3884 node3884Labels := by rfl

theorem canonical15746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15746 raw15746Labels = mixedMoment B node2869 node2869Labels := by
  calc
    mixedMoment B raw15746 raw15746Labels = mixedMoment B raw15746step0 raw15746step0Labels := by
      have ha : raw15746step0 = (fun i j => raw15746 (permutation572 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15746step0 raw15746; decide +kernel
      have hl : raw15746step0Labels = raw15746Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15746 raw15746Labels permutation572 permutation2
    _ = mixedMoment B node2869 node2869Labels := by rfl

theorem canonical15750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15750 raw15750Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw15750 raw15750Labels = mixedMoment B raw15750step0 raw15750step0Labels := by
      have ha : raw15750step0 = (fun i j => raw15750 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15750step0 raw15750; decide +kernel
      have hl : raw15750step0Labels = raw15750Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15750 raw15750Labels permutation164 permutation4
    mixedMoment B raw15750step0 raw15750step0Labels = mixedMoment B raw15750step1 raw15750step1Labels := by
      have ha : raw15750step1 = -raw15750step0 := by apply Matrix.ext; change ∀ i j, raw15750step1 i j = -(raw15750step0 i j); unfold raw15750step1 raw15750step0; decide +kernel
      have hl : raw15750step1Labels = raw15750step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3805 node3805Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15892 raw15892Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw15892 raw15892Labels = mixedMoment B raw15892step0 raw15892step0Labels := by
      have ha : raw15892step0 = (fun i j => raw15892 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15892step0 raw15892; decide +kernel
      have hl : raw15892step0Labels = raw15892Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15892 raw15892Labels permutation682 permutation7
    mixedMoment B raw15892step0 raw15892step0Labels = mixedMoment B raw15892step1 raw15892step1Labels := by
      have ha : raw15892step1 = -raw15892step0 := by apply Matrix.ext; change ∀ i j, raw15892step1 i j = -(raw15892step0 i j); unfold raw15892step1 raw15892step0; decide +kernel
      have hl : raw15892step1Labels = raw15892step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15892step1 raw15892step1Labels = mixedMoment B raw15892step2 raw15892step2Labels := by
      have ha : raw15892step2 = raw15892step1 := by apply Matrix.ext; unfold raw15892step2 raw15892step1; decide +kernel
      have hl : raw15892step1Labels = labelEmbedding1 ∘ raw15892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15892step1 raw15892step1Labels raw15892step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3800 node3800Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16597 raw16597Labels = mixedMoment B node2882 node2882Labels := by
  calc
    mixedMoment B raw16597 raw16597Labels = mixedMoment B raw16597step0 raw16597step0Labels := by
      have hz : ∀ j, raw16597 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16597step0 = (fun i j => raw16597 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16597step0 raw16597; decide +kernel
      have hl : raw16597step0Labels = raw16597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16597 raw16597Labels permutation346 hz
    mixedMoment B raw16597step0 raw16597step0Labels = mixedMoment B raw16597step1 raw16597step1Labels := by
      have ha : raw16597step1 = (fun i j => raw16597step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16597step1 raw16597step0; decide +kernel
      have hl : raw16597step1Labels = raw16597step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16597step0 raw16597step0Labels permutation126 permutation2
    _ = mixedMoment B node2882 node2882Labels := by rfl

theorem canonical16599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16599 raw16599Labels = mixedMoment B node2871 node2871Labels := by
  calc
    mixedMoment B raw16599 raw16599Labels = mixedMoment B raw16599step0 raw16599step0Labels := by
      have hz : ∀ j, raw16599 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16599step0 = (fun i j => raw16599 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16599step0 raw16599; decide +kernel
      have hl : raw16599step0Labels = raw16599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16599 raw16599Labels permutation346 hz
    mixedMoment B raw16599step0 raw16599step0Labels = mixedMoment B raw16599step1 raw16599step1Labels := by
      have ha : raw16599step1 = (fun i j => raw16599step0 (permutation123 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16599step1 raw16599step0; decide +kernel
      have hl : raw16599step1Labels = raw16599step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16599step0 raw16599step0Labels permutation123 permutation2
    _ = mixedMoment B node2871 node2871Labels := by rfl

theorem canonical16600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16600 raw16600Labels = mixedMoment B node2873 node2873Labels := by
  calc
    mixedMoment B raw16600 raw16600Labels = mixedMoment B raw16600step0 raw16600step0Labels := by
      have hz : ∀ j, raw16600 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16600step0 = (fun i j => raw16600 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16600step0 raw16600; decide +kernel
      have hl : raw16600step0Labels = raw16600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16600 raw16600Labels permutation346 hz
    mixedMoment B raw16600step0 raw16600step0Labels = mixedMoment B raw16600step1 raw16600step1Labels := by
      have ha : raw16600step1 = (fun i j => raw16600step0 (permutation123 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16600step1 raw16600step0; decide +kernel
      have hl : raw16600step1Labels = raw16600step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16600step0 raw16600step0Labels permutation123 permutation2
    _ = mixedMoment B node2873 node2873Labels := by rfl

theorem canonical16601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16601 raw16601Labels = mixedMoment B node3044 node3044Labels := by
  calc
    mixedMoment B raw16601 raw16601Labels = mixedMoment B raw16601step0 raw16601step0Labels := by
      have hz : ∀ j, raw16601 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16601step0 = (fun i j => raw16601 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16601step0 raw16601; decide +kernel
      have hl : raw16601step0Labels = raw16601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16601 raw16601Labels permutation346 hz
    mixedMoment B raw16601step0 raw16601step0Labels = mixedMoment B raw16601step1 raw16601step1Labels := by
      have ha : raw16601step1 = (fun i j => raw16601step0 (permutation123 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16601step1 raw16601step0; decide +kernel
      have hl : raw16601step1Labels = raw16601step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16601step0 raw16601step0Labels permutation123 permutation2
    _ = mixedMoment B node3044 node3044Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16736 raw16736Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw16736 raw16736Labels = mixedMoment B raw16736step0 raw16736step0Labels := by
      have ha : raw16736step0 = (fun i j => raw16736 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16736step0 raw16736; decide +kernel
      have hl : raw16736step0Labels = raw16736Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16736 raw16736Labels permutation265 permutation2
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical16737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16737 raw16737Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw16737 raw16737Labels = mixedMoment B raw16737step0 raw16737step0Labels := by
      have ha : raw16737step0 = (fun i j => raw16737 (permutation685 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16737step0 raw16737; decide +kernel
      have hl : raw16737step0Labels = raw16737Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16737 raw16737Labels permutation685 permutation3
    mixedMoment B raw16737step0 raw16737step0Labels = mixedMoment B raw16737step1 raw16737step1Labels := by
      have ha : raw16737step1 = -raw16737step0 := by apply Matrix.ext; change ∀ i j, raw16737step1 i j = -(raw16737step0 i j); unfold raw16737step1 raw16737step0; decide +kernel
      have hl : raw16737step1Labels = raw16737step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16737step1 raw16737step1Labels = mixedMoment B raw16737step2 raw16737step2Labels := by
      have ha : raw16737step2 = raw16737step1 := by apply Matrix.ext; unfold raw16737step2 raw16737step1; decide +kernel
      have hl : raw16737step1Labels = labelEmbedding6 ∘ raw16737step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16737step1 raw16737step1Labels raw16737step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5480 node5480Labels := by rfl

theorem canonical16738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16738 raw16738Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw16738 raw16738Labels = mixedMoment B raw16738step0 raw16738step0Labels := by
      have ha : raw16738step0 = (fun i j => raw16738 (permutation679 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16738step0 raw16738; decide +kernel
      have hl : raw16738step0Labels = raw16738Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16738 raw16738Labels permutation679 permutation3
    mixedMoment B raw16738step0 raw16738step0Labels = mixedMoment B raw16738step1 raw16738step1Labels := by
      have ha : raw16738step1 = -raw16738step0 := by apply Matrix.ext; change ∀ i j, raw16738step1 i j = -(raw16738step0 i j); unfold raw16738step1 raw16738step0; decide +kernel
      have hl : raw16738step1Labels = raw16738step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16738step1 raw16738step1Labels = mixedMoment B raw16738step2 raw16738step2Labels := by
      have ha : raw16738step2 = raw16738step1 := by apply Matrix.ext; unfold raw16738step2 raw16738step1; decide +kernel
      have hl : raw16738step1Labels = labelEmbedding6 ∘ raw16738step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16738step1 raw16738step1Labels raw16738step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5480 node5480Labels := by rfl

theorem canonical16739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16739 raw16739Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw16739 raw16739Labels = mixedMoment B raw16739step0 raw16739step0Labels := by
      have hz : ∀ j, raw16739 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16739step0 = (fun i j => raw16739 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16739step0 raw16739; decide +kernel
      have hl : raw16739step0Labels = raw16739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16739 raw16739Labels permutation520 hz
    mixedMoment B raw16739step0 raw16739step0Labels = mixedMoment B raw16739step1 raw16739step1Labels := by
      have ha : raw16739step1 = (fun i j => raw16739step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16739step1 raw16739step0; decide +kernel
      have hl : raw16739step1Labels = raw16739step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16739step0 raw16739step0Labels permutation56 permutation7
    mixedMoment B raw16739step1 raw16739step1Labels = mixedMoment B raw16739step2 raw16739step2Labels := by
      have ha : raw16739step2 = -raw16739step1 := by apply Matrix.ext; change ∀ i j, raw16739step2 i j = -(raw16739step1 i j); unfold raw16739step2 raw16739step1; decide +kernel
      have hl : raw16739step2Labels = raw16739step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16739step2 raw16739step2Labels = mixedMoment B raw16739step3 raw16739step3Labels := by
      have ha : raw16739step3 = raw16739step2 := by apply Matrix.ext; unfold raw16739step3 raw16739step2; decide +kernel
      have hl : raw16739step2Labels = labelEmbedding10 ∘ raw16739step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16739step2 raw16739step2Labels raw16739step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

theorem canonical16740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16740 raw16740Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw16740 raw16740Labels = mixedMoment B raw16740step0 raw16740step0Labels := by
      have ha : raw16740step0 = (fun i j => raw16740 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16740step0 raw16740; decide +kernel
      have hl : raw16740step0Labels = raw16740Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16740 raw16740Labels permutation277 permutation7
    mixedMoment B raw16740step0 raw16740step0Labels = mixedMoment B raw16740step1 raw16740step1Labels := by
      have ha : raw16740step1 = -raw16740step0 := by apply Matrix.ext; change ∀ i j, raw16740step1 i j = -(raw16740step0 i j); unfold raw16740step1 raw16740step0; decide +kernel
      have hl : raw16740step1Labels = raw16740step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16740step1 raw16740step1Labels = mixedMoment B raw16740step2 raw16740step2Labels := by
      have ha : raw16740step2 = raw16740step1 := by apply Matrix.ext; unfold raw16740step2 raw16740step1; decide +kernel
      have hl : raw16740step1Labels = labelEmbedding10 ∘ raw16740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16740step1 raw16740step1Labels raw16740step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical16741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16741 raw16741Labels = mixedMoment B node5244 node5244Labels := by
  calc
    mixedMoment B raw16741 raw16741Labels = mixedMoment B raw16741step0 raw16741step0Labels := by
      have ha : raw16741step0 = (fun i j => raw16741 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16741step0 raw16741; decide +kernel
      have hl : raw16741step0Labels = raw16741Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16741 raw16741Labels permutation182 permutation3
    mixedMoment B raw16741step0 raw16741step0Labels = mixedMoment B raw16741step1 raw16741step1Labels := by
      have ha : raw16741step1 = raw16741step0 := by apply Matrix.ext; unfold raw16741step1 raw16741step0; decide +kernel
      have hl : raw16741step0Labels = labelEmbedding6 ∘ raw16741step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16741step0 raw16741step0Labels raw16741step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5244 node5244Labels := by rfl

theorem canonical16742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16742 raw16742Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw16742 raw16742Labels = mixedMoment B raw16742step0 raw16742step0Labels := by
      have ha : raw16742step0 = (fun i j => raw16742 (permutation330 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16742step0 raw16742; decide +kernel
      have hl : raw16742step0Labels = raw16742Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16742 raw16742Labels permutation330 permutation4
    mixedMoment B raw16742step0 raw16742step0Labels = mixedMoment B raw16742step1 raw16742step1Labels := by
      have ha : raw16742step1 = raw16742step0 := by apply Matrix.ext; unfold raw16742step1 raw16742step0; decide +kernel
      have hl : raw16742step0Labels = labelEmbedding7 ∘ raw16742step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16742step0 raw16742step0Labels raw16742step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

theorem canonical16743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16743 raw16743Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw16743 raw16743Labels = mixedMoment B raw16743step0 raw16743step0Labels := by
      have ha : raw16743step0 = (fun i j => raw16743 (permutation329 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16743step0 raw16743; decide +kernel
      have hl : raw16743step0Labels = raw16743Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16743 raw16743Labels permutation329 permutation4
    mixedMoment B raw16743step0 raw16743step0Labels = mixedMoment B raw16743step1 raw16743step1Labels := by
      have ha : raw16743step1 = raw16743step0 := by apply Matrix.ext; unfold raw16743step1 raw16743step0; decide +kernel
      have hl : raw16743step0Labels = labelEmbedding7 ∘ raw16743step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16743step0 raw16743step0Labels raw16743step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

theorem canonical16744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16744 raw16744Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw16744 raw16744Labels = mixedMoment B raw16744step0 raw16744step0Labels := by
      have hz : ∀ j, raw16744 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16744step0 = (fun i j => raw16744 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16744step0 raw16744; decide +kernel
      have hl : raw16744step0Labels = raw16744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16744 raw16744Labels permutation520 hz
    mixedMoment B raw16744step0 raw16744step0Labels = mixedMoment B raw16744step1 raw16744step1Labels := by
      have ha : raw16744step1 = (fun i j => raw16744step0 (permutation74 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16744step1 raw16744step0; decide +kernel
      have hl : raw16744step1Labels = raw16744step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16744step0 raw16744step0Labels permutation74 permutation4
    mixedMoment B raw16744step1 raw16744step1Labels = mixedMoment B raw16744step2 raw16744step2Labels := by
      have ha : raw16744step2 = raw16744step1 := by apply Matrix.ext; unfold raw16744step2 raw16744step1; decide +kernel
      have hl : raw16744step1Labels = labelEmbedding7 ∘ raw16744step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16744step1 raw16744step1Labels raw16744step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

theorem canonical16745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16745 raw16745Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw16745 raw16745Labels = mixedMoment B raw16745step0 raw16745step0Labels := by
      have ha : raw16745step0 = (fun i j => raw16745 (permutation329 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16745step0 raw16745; decide +kernel
      have hl : raw16745step0Labels = raw16745Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16745 raw16745Labels permutation329 permutation4
    mixedMoment B raw16745step0 raw16745step0Labels = mixedMoment B raw16745step1 raw16745step1Labels := by
      have ha : raw16745step1 = raw16745step0 := by apply Matrix.ext; unfold raw16745step1 raw16745step0; decide +kernel
      have hl : raw16745step0Labels = labelEmbedding7 ∘ raw16745step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16745step0 raw16745step0Labels raw16745step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical16746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16746 raw16746Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw16746 raw16746Labels = mixedMoment B raw16746step0 raw16746step0Labels := by
      have ha : raw16746step0 = (fun i j => raw16746 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16746step0 raw16746; decide +kernel
      have hl : raw16746step0Labels = raw16746Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16746 raw16746Labels permutation158 permutation3
    mixedMoment B raw16746step0 raw16746step0Labels = mixedMoment B raw16746step1 raw16746step1Labels := by
      have ha : raw16746step1 = raw16746step0 := by apply Matrix.ext; unfold raw16746step1 raw16746step0; decide +kernel
      have hl : raw16746step0Labels = labelEmbedding6 ∘ raw16746step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16746step0 raw16746step0Labels raw16746step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5185 node5185Labels := by rfl

theorem canonical16747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16747 raw16747Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw16747 raw16747Labels = mixedMoment B raw16747step0 raw16747step0Labels := by
      have ha : raw16747step0 = (fun i j => raw16747 (permutation273 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16747step0 raw16747; decide +kernel
      have hl : raw16747step0Labels = raw16747Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16747 raw16747Labels permutation273 permutation2
    _ = mixedMoment B node5352 node5352Labels := by rfl

theorem canonical16748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16748 raw16748Labels = mixedMoment B node5470 node5470Labels := by
  calc
    mixedMoment B raw16748 raw16748Labels = mixedMoment B raw16748step0 raw16748step0Labels := by
      have ha : raw16748step0 = (fun i j => raw16748 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16748step0 raw16748; decide +kernel
      have hl : raw16748step0Labels = raw16748Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16748 raw16748Labels permutation160 permutation2
    _ = mixedMoment B node5470 node5470Labels := by rfl

theorem canonical16749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16749 raw16749Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw16749 raw16749Labels = mixedMoment B raw16749step0 raw16749step0Labels := by
      have hz : ∀ j, raw16749 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16749step0 = (fun i j => raw16749 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16749step0 raw16749; decide +kernel
      have hl : raw16749step0Labels = raw16749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16749 raw16749Labels permutation520 hz
    mixedMoment B raw16749step0 raw16749step0Labels = mixedMoment B raw16749step1 raw16749step1Labels := by
      have ha : raw16749step1 = (fun i j => raw16749step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16749step1 raw16749step0; decide +kernel
      have hl : raw16749step1Labels = raw16749step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16749step0 raw16749step0Labels permutation34 permutation2
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical16750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16750 raw16750Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw16750 raw16750Labels = mixedMoment B raw16750step0 raw16750step0Labels := by
      have ha : raw16750step0 = (fun i j => raw16750 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16750step0 raw16750; decide +kernel
      have hl : raw16750step0Labels = raw16750Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16750 raw16750Labels permutation160 permutation2
    _ = mixedMoment B node5472 node5472Labels := by rfl

theorem canonical16751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16751 raw16751Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw16751 raw16751Labels = mixedMoment B raw16751step0 raw16751step0Labels := by
      have ha : raw16751step0 = (fun i j => raw16751 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16751step0 raw16751; decide +kernel
      have hl : raw16751step0Labels = raw16751Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16751 raw16751Labels permutation152 permutation3
    mixedMoment B raw16751step0 raw16751step0Labels = mixedMoment B raw16751step1 raw16751step1Labels := by
      have ha : raw16751step1 = raw16751step0 := by apply Matrix.ext; unfold raw16751step1 raw16751step0; decide +kernel
      have hl : raw16751step0Labels = labelEmbedding6 ∘ raw16751step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16751step0 raw16751step0Labels raw16751step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5185 node5185Labels := by rfl

theorem canonical16752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16752 raw16752Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw16752 raw16752Labels = mixedMoment B raw16752step0 raw16752step0Labels := by
      have ha : raw16752step0 = (fun i j => raw16752 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16752step0 raw16752; decide +kernel
      have hl : raw16752step0Labels = raw16752Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16752 raw16752Labels permutation267 permutation2
    _ = mixedMoment B node5352 node5352Labels := by rfl

theorem canonical16753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16753 raw16753Labels = mixedMoment B node5470 node5470Labels := by
  calc
    mixedMoment B raw16753 raw16753Labels = mixedMoment B raw16753step0 raw16753step0Labels := by
      have ha : raw16753step0 = (fun i j => raw16753 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16753step0 raw16753; decide +kernel
      have hl : raw16753step0Labels = raw16753Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16753 raw16753Labels permutation154 permutation2
    _ = mixedMoment B node5470 node5470Labels := by rfl

theorem canonical16754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16754 raw16754Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw16754 raw16754Labels = mixedMoment B raw16754step0 raw16754step0Labels := by
      have hz : ∀ j, raw16754 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16754step0 = (fun i j => raw16754 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16754step0 raw16754; decide +kernel
      have hl : raw16754step0Labels = raw16754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16754 raw16754Labels permutation520 hz
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical16755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16755 raw16755Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw16755 raw16755Labels = mixedMoment B raw16755step0 raw16755step0Labels := by
      have ha : raw16755step0 = (fun i j => raw16755 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16755step0 raw16755; decide +kernel
      have hl : raw16755step0Labels = raw16755Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16755 raw16755Labels permutation154 permutation2
    _ = mixedMoment B node5472 node5472Labels := by rfl

theorem canonical16756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16756 raw16756Labels = mixedMoment B node5181 node5181Labels := by
  calc
    mixedMoment B raw16756 raw16756Labels = mixedMoment B raw16756step0 raw16756step0Labels := by
      have ha : raw16756step0 = (fun i j => raw16756 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16756step0 raw16756; decide +kernel
      have hl : raw16756step0Labels = raw16756Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16756 raw16756Labels permutation153 permutation3
    mixedMoment B raw16756step0 raw16756step0Labels = mixedMoment B raw16756step1 raw16756step1Labels := by
      have ha : raw16756step1 = raw16756step0 := by apply Matrix.ext; unfold raw16756step1 raw16756step0; decide +kernel
      have hl : raw16756step0Labels = labelEmbedding6 ∘ raw16756step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16756step0 raw16756step0Labels raw16756step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5181 node5181Labels := by rfl

theorem canonical16757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16757 raw16757Labels = mixedMoment B node5348 node5348Labels := by
  calc
    mixedMoment B raw16757 raw16757Labels = mixedMoment B raw16757step0 raw16757step0Labels := by
      have ha : raw16757step0 = (fun i j => raw16757 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16757step0 raw16757; decide +kernel
      have hl : raw16757step0Labels = raw16757Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16757 raw16757Labels permutation265 permutation2
    _ = mixedMoment B node5348 node5348Labels := by rfl

theorem canonical16758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16758 raw16758Labels = mixedMoment B node5350 node5350Labels := by
  calc
    mixedMoment B raw16758 raw16758Labels = mixedMoment B raw16758step0 raw16758step0Labels := by
      have ha : raw16758step0 = (fun i j => raw16758 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16758step0 raw16758; decide +kernel
      have hl : raw16758step0Labels = raw16758Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16758 raw16758Labels permutation587 permutation3
    mixedMoment B raw16758step0 raw16758step0Labels = mixedMoment B raw16758step1 raw16758step1Labels := by
      have ha : raw16758step1 = -raw16758step0 := by apply Matrix.ext; change ∀ i j, raw16758step1 i j = -(raw16758step0 i j); unfold raw16758step1 raw16758step0; decide +kernel
      have hl : raw16758step1Labels = raw16758step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16758step1 raw16758step1Labels = mixedMoment B raw16758step2 raw16758step2Labels := by
      have ha : raw16758step2 = raw16758step1 := by apply Matrix.ext; unfold raw16758step2 raw16758step1; decide +kernel
      have hl : raw16758step1Labels = labelEmbedding6 ∘ raw16758step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16758step1 raw16758step1Labels raw16758step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5350 node5350Labels := by rfl

theorem canonical16759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16759 raw16759Labels = mixedMoment B node5350 node5350Labels := by
  calc
    mixedMoment B raw16759 raw16759Labels = mixedMoment B raw16759step0 raw16759step0Labels := by
      have ha : raw16759step0 = (fun i j => raw16759 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16759step0 raw16759; decide +kernel
      have hl : raw16759step0Labels = raw16759Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16759 raw16759Labels permutation582 permutation3
    mixedMoment B raw16759step0 raw16759step0Labels = mixedMoment B raw16759step1 raw16759step1Labels := by
      have ha : raw16759step1 = -raw16759step0 := by apply Matrix.ext; change ∀ i j, raw16759step1 i j = -(raw16759step0 i j); unfold raw16759step1 raw16759step0; decide +kernel
      have hl : raw16759step1Labels = raw16759step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16759step1 raw16759step1Labels = mixedMoment B raw16759step2 raw16759step2Labels := by
      have ha : raw16759step2 = raw16759step1 := by apply Matrix.ext; unfold raw16759step2 raw16759step1; decide +kernel
      have hl : raw16759step1Labels = labelEmbedding6 ∘ raw16759step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16759step1 raw16759step1Labels raw16759step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5350 node5350Labels := by rfl

theorem canonical16760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16760 raw16760Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw16760 raw16760Labels = mixedMoment B raw16760step0 raw16760step0Labels := by
      have ha : raw16760step0 = (fun i j => raw16760 (permutation584 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16760step0 raw16760; decide +kernel
      have hl : raw16760step0Labels = raw16760Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16760 raw16760Labels permutation584 permutation3
    mixedMoment B raw16760step0 raw16760step0Labels = mixedMoment B raw16760step1 raw16760step1Labels := by
      have ha : raw16760step1 = -raw16760step0 := by apply Matrix.ext; change ∀ i j, raw16760step1 i j = -(raw16760step0 i j); unfold raw16760step1 raw16760step0; decide +kernel
      have hl : raw16760step1Labels = raw16760step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16760step1 raw16760step1Labels = mixedMoment B raw16760step2 raw16760step2Labels := by
      have ha : raw16760step2 = raw16760step1 := by apply Matrix.ext; unfold raw16760step2 raw16760step1; decide +kernel
      have hl : raw16760step1Labels = labelEmbedding6 ∘ raw16760step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16760step1 raw16760step1Labels raw16760step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

theorem canonical16761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16761 raw16761Labels = mixedMoment B node5064 node5064Labels := by
  calc
    mixedMoment B raw16761 raw16761Labels = mixedMoment B raw16761step0 raw16761step0Labels := by
      have ha : raw16761step0 = (fun i j => raw16761 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16761step0 raw16761; decide +kernel
      have hl : raw16761step0Labels = raw16761Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16761 raw16761Labels permutation682 permutation3
    mixedMoment B raw16761step0 raw16761step0Labels = mixedMoment B raw16761step1 raw16761step1Labels := by
      have ha : raw16761step1 = -raw16761step0 := by apply Matrix.ext; change ∀ i j, raw16761step1 i j = -(raw16761step0 i j); unfold raw16761step1 raw16761step0; decide +kernel
      have hl : raw16761step1Labels = raw16761step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16761step1 raw16761step1Labels = mixedMoment B raw16761step2 raw16761step2Labels := by
      have ha : raw16761step2 = raw16761step1 := by apply Matrix.ext; unfold raw16761step2 raw16761step1; decide +kernel
      have hl : raw16761step1Labels = labelEmbedding6 ∘ raw16761step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16761step1 raw16761step1Labels raw16761step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5064 node5064Labels := by rfl

theorem canonical16762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16762 raw16762Labels = mixedMoment B node5067 node5067Labels := by
  calc
    mixedMoment B raw16762 raw16762Labels = mixedMoment B raw16762step0 raw16762step0Labels := by
      have ha : raw16762step0 = (fun i j => raw16762 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16762step0 raw16762; decide +kernel
      have hl : raw16762step0Labels = raw16762Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16762 raw16762Labels permutation682 permutation3
    mixedMoment B raw16762step0 raw16762step0Labels = mixedMoment B raw16762step1 raw16762step1Labels := by
      have ha : raw16762step1 = -raw16762step0 := by apply Matrix.ext; change ∀ i j, raw16762step1 i j = -(raw16762step0 i j); unfold raw16762step1 raw16762step0; decide +kernel
      have hl : raw16762step1Labels = raw16762step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16762step1 raw16762step1Labels = mixedMoment B raw16762step2 raw16762step2Labels := by
      have ha : raw16762step2 = raw16762step1 := by apply Matrix.ext; unfold raw16762step2 raw16762step1; decide +kernel
      have hl : raw16762step1Labels = labelEmbedding6 ∘ raw16762step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16762step1 raw16762step1Labels raw16762step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5067 node5067Labels := by rfl

theorem canonical16763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16763 raw16763Labels = mixedMoment B node5071 node5071Labels := by
  calc
    mixedMoment B raw16763 raw16763Labels = mixedMoment B raw16763step0 raw16763step0Labels := by
      have ha : raw16763step0 = (fun i j => raw16763 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16763step0 raw16763; decide +kernel
      have hl : raw16763step0Labels = raw16763Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16763 raw16763Labels permutation686 permutation3
    mixedMoment B raw16763step0 raw16763step0Labels = mixedMoment B raw16763step1 raw16763step1Labels := by
      have ha : raw16763step1 = -raw16763step0 := by apply Matrix.ext; change ∀ i j, raw16763step1 i j = -(raw16763step0 i j); unfold raw16763step1 raw16763step0; decide +kernel
      have hl : raw16763step1Labels = raw16763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16763step1 raw16763step1Labels = mixedMoment B raw16763step2 raw16763step2Labels := by
      have ha : raw16763step2 = raw16763step1 := by apply Matrix.ext; unfold raw16763step2 raw16763step1; decide +kernel
      have hl : raw16763step1Labels = labelEmbedding6 ∘ raw16763step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16763step1 raw16763step1Labels raw16763step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5071 node5071Labels := by rfl

theorem canonical16764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16764 raw16764Labels = mixedMoment B node5071 node5071Labels := by
  calc
    mixedMoment B raw16764 raw16764Labels = mixedMoment B raw16764step0 raw16764step0Labels := by
      have ha : raw16764step0 = (fun i j => raw16764 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16764step0 raw16764; decide +kernel
      have hl : raw16764step0Labels = raw16764Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16764 raw16764Labels permutation680 permutation3
    mixedMoment B raw16764step0 raw16764step0Labels = mixedMoment B raw16764step1 raw16764step1Labels := by
      have ha : raw16764step1 = -raw16764step0 := by apply Matrix.ext; change ∀ i j, raw16764step1 i j = -(raw16764step0 i j); unfold raw16764step1 raw16764step0; decide +kernel
      have hl : raw16764step1Labels = raw16764step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16764step1 raw16764step1Labels = mixedMoment B raw16764step2 raw16764step2Labels := by
      have ha : raw16764step2 = raw16764step1 := by apply Matrix.ext; unfold raw16764step2 raw16764step1; decide +kernel
      have hl : raw16764step1Labels = labelEmbedding6 ∘ raw16764step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16764step1 raw16764step1Labels raw16764step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5071 node5071Labels := by rfl

theorem canonical16765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16765 raw16765Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw16765 raw16765Labels = mixedMoment B raw16765step0 raw16765step0Labels := by
      have hz : ∀ j, raw16765 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16765step0 = (fun i j => raw16765 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16765step0 raw16765; decide +kernel
      have hl : raw16765step0Labels = raw16765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16765 raw16765Labels permutation520 hz
    mixedMoment B raw16765step0 raw16765step0Labels = mixedMoment B raw16765step1 raw16765step1Labels := by
      have ha : raw16765step1 = (fun i j => raw16765step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16765step1 raw16765step0; decide +kernel
      have hl : raw16765step1Labels = raw16765step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16765step0 raw16765step0Labels permutation145 permutation3
    mixedMoment B raw16765step1 raw16765step1Labels = mixedMoment B raw16765step2 raw16765step2Labels := by
      have ha : raw16765step2 = -raw16765step1 := by apply Matrix.ext; change ∀ i j, raw16765step2 i j = -(raw16765step1 i j); unfold raw16765step2 raw16765step1; decide +kernel
      have hl : raw16765step2Labels = raw16765step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16765step2 raw16765step2Labels = mixedMoment B raw16765step3 raw16765step3Labels := by
      have ha : raw16765step3 = raw16765step2 := by apply Matrix.ext; unfold raw16765step3 raw16765step2; decide +kernel
      have hl : raw16765step2Labels = labelEmbedding6 ∘ raw16765step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16765step2 raw16765step2Labels raw16765step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16826 raw16826Labels = mixedMoment B node3953 node3953Labels := by
  calc
    _ = mixedMoment B node3953 node3953Labels := by rfl

theorem canonical16832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16832 raw16832Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw16832 raw16832Labels = mixedMoment B raw16832step0 raw16832step0Labels := by
      have hz : ∀ j, raw16832 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16832step0 = (fun i j => raw16832 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16832step0 raw16832; decide +kernel
      have hl : raw16832step0Labels = raw16832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16832 raw16832Labels permutation520 hz
    mixedMoment B raw16832step0 raw16832step0Labels = mixedMoment B raw16832step1 raw16832step1Labels := by
      have ha : raw16832step1 = (fun i j => raw16832step0 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw16832step1 raw16832step0; decide +kernel
      have hl : raw16832step1Labels = raw16832step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16832step0 raw16832step0Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical16833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16833 raw16833Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw16833 raw16833Labels = mixedMoment B raw16833step0 raw16833step0Labels := by
      have ha : raw16833step0 = (fun i j => raw16833 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16833step0 raw16833; decide +kernel
      have hl : raw16833step0Labels = raw16833Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16833 raw16833Labels permutation265 permutation2
    _ = mixedMoment B node3800 node3800Labels := by rfl

theorem canonical16834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16834 raw16834Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw16834 raw16834Labels = mixedMoment B raw16834step0 raw16834step0Labels := by
      have ha : raw16834step0 = (fun i j => raw16834 (permutation273 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16834step0 raw16834; decide +kernel
      have hl : raw16834step0Labels = raw16834Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16834 raw16834Labels permutation273 permutation2
    _ = mixedMoment B node3690 node3690Labels := by rfl

theorem canonical16835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16835 raw16835Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw16835 raw16835Labels = mixedMoment B raw16835step0 raw16835step0Labels := by
      have ha : raw16835step0 = (fun i j => raw16835 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16835step0 raw16835; decide +kernel
      have hl : raw16835step0Labels = raw16835Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16835 raw16835Labels permutation267 permutation2
    _ = mixedMoment B node3690 node3690Labels := by rfl

theorem canonical16836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16836 raw16836Labels = mixedMoment B node3685 node3685Labels := by
  calc
    mixedMoment B raw16836 raw16836Labels = mixedMoment B raw16836step0 raw16836step0Labels := by
      have ha : raw16836step0 = (fun i j => raw16836 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16836step0 raw16836; decide +kernel
      have hl : raw16836step0Labels = raw16836Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16836 raw16836Labels permutation265 permutation2
    _ = mixedMoment B node3685 node3685Labels := by rfl

theorem canonical16837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16837 raw16837Labels = mixedMoment B node2981 node2981Labels := by
  calc
    mixedMoment B raw16837 raw16837Labels = mixedMoment B raw16837step0 raw16837step0Labels := by
      have ha : raw16837step0 = (fun i j => raw16837 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16837step0 raw16837; decide +kernel
      have hl : raw16837step0Labels = raw16837Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16837 raw16837Labels permutation681 permutation2
    mixedMoment B raw16837step0 raw16837step0Labels = mixedMoment B raw16837step1 raw16837step1Labels := by
      have ha : raw16837step1 = -raw16837step0 := by apply Matrix.ext; change ∀ i j, raw16837step1 i j = -(raw16837step0 i j); unfold raw16837step1 raw16837step0; decide +kernel
      have hl : raw16837step1Labels = raw16837step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2981 node2981Labels := by rfl

theorem canonical16891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16891 raw16891Labels = mixedMoment B node2728 node2728Labels := by
  calc
    mixedMoment B raw16891 raw16891Labels = mixedMoment B raw16891step0 raw16891step0Labels := by
      have ha : raw16891step0 = (fun i j => raw16891 (permutation324 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16891step0 raw16891; decide +kernel
      have hl : raw16891step0Labels = raw16891Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16891 raw16891Labels permutation324 permutation5
    mixedMoment B raw16891step0 raw16891step0Labels = mixedMoment B raw16891step1 raw16891step1Labels := by
      have ha : raw16891step1 = -raw16891step0 := by apply Matrix.ext; change ∀ i j, raw16891step1 i j = -(raw16891step0 i j); unfold raw16891step1 raw16891step0; decide +kernel
      have hl : raw16891step1Labels = raw16891step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16891step1 raw16891step1Labels = mixedMoment B raw16891step2 raw16891step2Labels := by
      have ha : raw16891step2 = raw16891step1 := by apply Matrix.ext; unfold raw16891step2 raw16891step1; decide +kernel
      have hl : raw16891step1Labels = labelEmbedding1 ∘ raw16891step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16891step1 raw16891step1Labels raw16891step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2728 node2728Labels := by rfl

theorem canonical16892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16892 raw16892Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw16892 raw16892Labels = mixedMoment B raw16892step0 raw16892step0Labels := by
      have hz : ∀ j, raw16892 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16892step0 = (fun i j => raw16892 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16892step0 raw16892; decide +kernel
      have hl : raw16892step0Labels = raw16892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16892 raw16892Labels permutation346 hz
    mixedMoment B raw16892step0 raw16892step0Labels = mixedMoment B raw16892step1 raw16892step1Labels := by
      have ha : raw16892step1 = (fun i j => raw16892step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16892step1 raw16892step0; decide +kernel
      have hl : raw16892step1Labels = raw16892step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16892step0 raw16892step0Labels permutation32 permutation7
    mixedMoment B raw16892step1 raw16892step1Labels = mixedMoment B raw16892step2 raw16892step2Labels := by
      have ha : raw16892step2 = raw16892step1 := by apply Matrix.ext; unfold raw16892step2 raw16892step1; decide +kernel
      have hl : raw16892step1Labels = labelEmbedding1 ∘ raw16892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16892step1 raw16892step1Labels raw16892step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

theorem canonical16893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16893 raw16893Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw16893 raw16893Labels = mixedMoment B raw16893step0 raw16893step0Labels := by
      have hz : ∀ j, raw16893 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16893step0 = (fun i j => raw16893 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16893step0 raw16893; decide +kernel
      have hl : raw16893step0Labels = raw16893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16893 raw16893Labels permutation434 hz
    mixedMoment B raw16893step0 raw16893step0Labels = mixedMoment B raw16893step1 raw16893step1Labels := by
      have ha : raw16893step1 = (fun i j => raw16893step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16893step1 raw16893step0; decide +kernel
      have hl : raw16893step1Labels = raw16893step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16893step0 raw16893step0Labels permutation32 permutation7
    mixedMoment B raw16893step1 raw16893step1Labels = mixedMoment B raw16893step2 raw16893step2Labels := by
      have ha : raw16893step2 = raw16893step1 := by apply Matrix.ext; unfold raw16893step2 raw16893step1; decide +kernel
      have hl : raw16893step1Labels = labelEmbedding1 ∘ raw16893step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16893step1 raw16893step1Labels raw16893step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

theorem canonical16894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16894 raw16894Labels = mixedMoment B node3869 node3869Labels := by
  calc
    mixedMoment B raw16894 raw16894Labels = mixedMoment B raw16894step0 raw16894step0Labels := by
      have ha : raw16894step0 = (fun i j => raw16894 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16894step0 raw16894; decide +kernel
      have hl : raw16894step0Labels = raw16894Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16894 raw16894Labels permutation152 permutation7
    mixedMoment B raw16894step0 raw16894step0Labels = mixedMoment B raw16894step1 raw16894step1Labels := by
      have ha : raw16894step1 = raw16894step0 := by apply Matrix.ext; unfold raw16894step1 raw16894step0; decide +kernel
      have hl : raw16894step0Labels = labelEmbedding1 ∘ raw16894step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16894step0 raw16894step0Labels raw16894step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3869 node3869Labels := by rfl

theorem canonical16895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16895 raw16895Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw16895 raw16895Labels = mixedMoment B raw16895step0 raw16895step0Labels := by
      have ha : raw16895step0 = (fun i j => raw16895 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16895step0 raw16895; decide +kernel
      have hl : raw16895step0Labels = raw16895Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16895 raw16895Labels permutation682 permutation7
    mixedMoment B raw16895step0 raw16895step0Labels = mixedMoment B raw16895step1 raw16895step1Labels := by
      have ha : raw16895step1 = -raw16895step0 := by apply Matrix.ext; change ∀ i j, raw16895step1 i j = -(raw16895step0 i j); unfold raw16895step1 raw16895step0; decide +kernel
      have hl : raw16895step1Labels = raw16895step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16895step1 raw16895step1Labels = mixedMoment B raw16895step2 raw16895step2Labels := by
      have ha : raw16895step2 = raw16895step1 := by apply Matrix.ext; unfold raw16895step2 raw16895step1; decide +kernel
      have hl : raw16895step1Labels = labelEmbedding1 ∘ raw16895step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16895step1 raw16895step1Labels raw16895step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3799 node3799Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical132
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16896 raw16896Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw16896 raw16896Labels = mixedMoment B raw16896step0 raw16896step0Labels := by
      have hz : ∀ j, raw16896 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16896step0 = (fun i j => raw16896 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16896step0 raw16896; decide +kernel
      have hl : raw16896step0Labels = raw16896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16896 raw16896Labels permutation434 hz
    mixedMoment B raw16896step0 raw16896step0Labels = mixedMoment B raw16896step1 raw16896step1Labels := by
      have ha : raw16896step1 = (fun i j => raw16896step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16896step1 raw16896step0; decide +kernel
      have hl : raw16896step1Labels = raw16896step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16896step0 raw16896step0Labels permutation151 permutation7
    mixedMoment B raw16896step1 raw16896step1Labels = mixedMoment B raw16896step2 raw16896step2Labels := by
      have ha : raw16896step2 = -raw16896step1 := by apply Matrix.ext; change ∀ i j, raw16896step2 i j = -(raw16896step1 i j); unfold raw16896step2 raw16896step1; decide +kernel
      have hl : raw16896step2Labels = raw16896step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16896step2 raw16896step2Labels = mixedMoment B raw16896step3 raw16896step3Labels := by
      have ha : raw16896step3 = raw16896step2 := by apply Matrix.ext; unfold raw16896step3 raw16896step2; decide +kernel
      have hl : raw16896step2Labels = labelEmbedding1 ∘ raw16896step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16896step2 raw16896step2Labels raw16896step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3981 node3981Labels := by rfl

theorem canonical16897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16897 raw16897Labels = mixedMoment B node3783 node3783Labels := by
  calc
    mixedMoment B raw16897 raw16897Labels = mixedMoment B raw16897step0 raw16897step0Labels := by
      have ha : raw16897step0 = (fun i j => raw16897 (permutation398 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16897step0 raw16897; decide +kernel
      have hl : raw16897step0Labels = raw16897Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16897 raw16897Labels permutation398 permutation5
    mixedMoment B raw16897step0 raw16897step0Labels = mixedMoment B raw16897step1 raw16897step1Labels := by
      have ha : raw16897step1 = raw16897step0 := by apply Matrix.ext; unfold raw16897step1 raw16897step0; decide +kernel
      have hl : raw16897step0Labels = labelEmbedding1 ∘ raw16897step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16897step0 raw16897step0Labels raw16897step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3783 node3783Labels := by rfl

theorem canonical16898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16898 raw16898Labels = mixedMoment B node2613 node2613Labels := by
  calc
    mixedMoment B raw16898 raw16898Labels = mixedMoment B raw16898step0 raw16898step0Labels := by
      have ha : raw16898step0 = (fun i j => raw16898 (permutation282 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16898step0 raw16898; decide +kernel
      have hl : raw16898step0Labels = raw16898Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16898 raw16898Labels permutation282 permutation5
    mixedMoment B raw16898step0 raw16898step0Labels = mixedMoment B raw16898step1 raw16898step1Labels := by
      have ha : raw16898step1 = -raw16898step0 := by apply Matrix.ext; change ∀ i j, raw16898step1 i j = -(raw16898step0 i j); unfold raw16898step1 raw16898step0; decide +kernel
      have hl : raw16898step1Labels = raw16898step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16898step1 raw16898step1Labels = mixedMoment B raw16898step2 raw16898step2Labels := by
      have ha : raw16898step2 = raw16898step1 := by apply Matrix.ext; unfold raw16898step2 raw16898step1; decide +kernel
      have hl : raw16898step1Labels = labelEmbedding1 ∘ raw16898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16898step1 raw16898step1Labels raw16898step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2613 node2613Labels := by rfl

theorem canonical16899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16899 raw16899Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw16899 raw16899Labels = mixedMoment B raw16899step0 raw16899step0Labels := by
      have hz : ∀ j, raw16899 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16899step0 = (fun i j => raw16899 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16899step0 raw16899; decide +kernel
      have hl : raw16899step0Labels = raw16899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16899 raw16899Labels permutation434 hz
    mixedMoment B raw16899step0 raw16899step0Labels = mixedMoment B raw16899step1 raw16899step1Labels := by
      have ha : raw16899step1 = (fun i j => raw16899step0 (permutation102 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16899step1 raw16899step0; decide +kernel
      have hl : raw16899step1Labels = raw16899step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16899step0 raw16899step0Labels permutation102 permutation5
    mixedMoment B raw16899step1 raw16899step1Labels = mixedMoment B raw16899step2 raw16899step2Labels := by
      have ha : raw16899step2 = raw16899step1 := by apply Matrix.ext; unfold raw16899step2 raw16899step1; decide +kernel
      have hl : raw16899step1Labels = labelEmbedding1 ∘ raw16899step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16899step1 raw16899step1Labels raw16899step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3881 node3881Labels := by rfl

theorem canonical16900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16900 raw16900Labels = mixedMoment B node3785 node3785Labels := by
  calc
    mixedMoment B raw16900 raw16900Labels = mixedMoment B raw16900step0 raw16900step0Labels := by
      have ha : raw16900step0 = (fun i j => raw16900 (permutation396 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16900step0 raw16900; decide +kernel
      have hl : raw16900step0Labels = raw16900Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16900 raw16900Labels permutation396 permutation5
    mixedMoment B raw16900step0 raw16900step0Labels = mixedMoment B raw16900step1 raw16900step1Labels := by
      have ha : raw16900step1 = raw16900step0 := by apply Matrix.ext; unfold raw16900step1 raw16900step0; decide +kernel
      have hl : raw16900step0Labels = labelEmbedding1 ∘ raw16900step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16900step0 raw16900step0Labels raw16900step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3785 node3785Labels := by rfl

theorem canonical16901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16901 raw16901Labels = mixedMoment B node3802 node3802Labels := by
  calc
    mixedMoment B raw16901 raw16901Labels = mixedMoment B raw16901step0 raw16901step0Labels := by
      have ha : raw16901step0 = (fun i j => raw16901 (permutation393 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16901step0 raw16901; decide +kernel
      have hl : raw16901step0Labels = raw16901Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16901 raw16901Labels permutation393 permutation5
    mixedMoment B raw16901step0 raw16901step0Labels = mixedMoment B raw16901step1 raw16901step1Labels := by
      have ha : raw16901step1 = raw16901step0 := by apply Matrix.ext; unfold raw16901step1 raw16901step0; decide +kernel
      have hl : raw16901step0Labels = labelEmbedding1 ∘ raw16901step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16901step0 raw16901step0Labels raw16901step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3802 node3802Labels := by rfl

theorem canonical16902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16902 raw16902Labels = mixedMoment B node3783 node3783Labels := by
  calc
    mixedMoment B raw16902 raw16902Labels = mixedMoment B raw16902step0 raw16902step0Labels := by
      have ha : raw16902step0 = (fun i j => raw16902 (permutation483 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16902step0 raw16902; decide +kernel
      have hl : raw16902step0Labels = raw16902Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16902 raw16902Labels permutation483 permutation5
    mixedMoment B raw16902step0 raw16902step0Labels = mixedMoment B raw16902step1 raw16902step1Labels := by
      have ha : raw16902step1 = raw16902step0 := by apply Matrix.ext; unfold raw16902step1 raw16902step0; decide +kernel
      have hl : raw16902step0Labels = labelEmbedding1 ∘ raw16902step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16902step0 raw16902step0Labels raw16902step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3783 node3783Labels := by rfl

theorem canonical16903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16903 raw16903Labels = mixedMoment B node2613 node2613Labels := by
  calc
    mixedMoment B raw16903 raw16903Labels = mixedMoment B raw16903step0 raw16903step0Labels := by
      have ha : raw16903step0 = (fun i j => raw16903 (permutation281 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16903step0 raw16903; decide +kernel
      have hl : raw16903step0Labels = raw16903Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16903 raw16903Labels permutation281 permutation5
    mixedMoment B raw16903step0 raw16903step0Labels = mixedMoment B raw16903step1 raw16903step1Labels := by
      have ha : raw16903step1 = -raw16903step0 := by apply Matrix.ext; change ∀ i j, raw16903step1 i j = -(raw16903step0 i j); unfold raw16903step1 raw16903step0; decide +kernel
      have hl : raw16903step1Labels = raw16903step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16903step1 raw16903step1Labels = mixedMoment B raw16903step2 raw16903step2Labels := by
      have ha : raw16903step2 = raw16903step1 := by apply Matrix.ext; unfold raw16903step2 raw16903step1; decide +kernel
      have hl : raw16903step1Labels = labelEmbedding1 ∘ raw16903step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16903step1 raw16903step1Labels raw16903step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2613 node2613Labels := by rfl

theorem canonical16904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16904 raw16904Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw16904 raw16904Labels = mixedMoment B raw16904step0 raw16904step0Labels := by
      have hz : ∀ j, raw16904 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16904step0 = (fun i j => raw16904 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16904step0 raw16904; decide +kernel
      have hl : raw16904step0Labels = raw16904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16904 raw16904Labels permutation346 hz
    mixedMoment B raw16904step0 raw16904step0Labels = mixedMoment B raw16904step1 raw16904step1Labels := by
      have ha : raw16904step1 = (fun i j => raw16904step0 (permutation102 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16904step1 raw16904step0; decide +kernel
      have hl : raw16904step1Labels = raw16904step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16904step0 raw16904step0Labels permutation102 permutation5
    mixedMoment B raw16904step1 raw16904step1Labels = mixedMoment B raw16904step2 raw16904step2Labels := by
      have ha : raw16904step2 = raw16904step1 := by apply Matrix.ext; unfold raw16904step2 raw16904step1; decide +kernel
      have hl : raw16904step1Labels = labelEmbedding1 ∘ raw16904step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16904step1 raw16904step1Labels raw16904step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3881 node3881Labels := by rfl

theorem canonical16905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16905 raw16905Labels = mixedMoment B node3785 node3785Labels := by
  calc
    mixedMoment B raw16905 raw16905Labels = mixedMoment B raw16905step0 raw16905step0Labels := by
      have ha : raw16905step0 = (fun i j => raw16905 (permutation481 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16905step0 raw16905; decide +kernel
      have hl : raw16905step0Labels = raw16905Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16905 raw16905Labels permutation481 permutation5
    mixedMoment B raw16905step0 raw16905step0Labels = mixedMoment B raw16905step1 raw16905step1Labels := by
      have ha : raw16905step1 = raw16905step0 := by apply Matrix.ext; unfold raw16905step1 raw16905step0; decide +kernel
      have hl : raw16905step0Labels = labelEmbedding1 ∘ raw16905step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16905step0 raw16905step0Labels raw16905step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3785 node3785Labels := by rfl

theorem canonical16906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16906 raw16906Labels = mixedMoment B node3802 node3802Labels := by
  calc
    mixedMoment B raw16906 raw16906Labels = mixedMoment B raw16906step0 raw16906step0Labels := by
      have ha : raw16906step0 = (fun i j => raw16906 (permutation479 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16906step0 raw16906; decide +kernel
      have hl : raw16906step0Labels = raw16906Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16906 raw16906Labels permutation479 permutation5
    mixedMoment B raw16906step0 raw16906step0Labels = mixedMoment B raw16906step1 raw16906step1Labels := by
      have ha : raw16906step1 = raw16906step0 := by apply Matrix.ext; unfold raw16906step1 raw16906step0; decide +kernel
      have hl : raw16906step0Labels = labelEmbedding1 ∘ raw16906step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16906step0 raw16906step0Labels raw16906step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3802 node3802Labels := by rfl

theorem canonical16907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16907 raw16907Labels = mixedMoment B node3938 node3938Labels := by
  calc
    mixedMoment B raw16907 raw16907Labels = mixedMoment B raw16907step0 raw16907step0Labels := by
      have ha : raw16907step0 = (fun i j => raw16907 (permutation287 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16907step0 raw16907; decide +kernel
      have hl : raw16907step0Labels = raw16907Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16907 raw16907Labels permutation287 permutation5
    mixedMoment B raw16907step0 raw16907step0Labels = mixedMoment B raw16907step1 raw16907step1Labels := by
      have ha : raw16907step1 = -raw16907step0 := by apply Matrix.ext; change ∀ i j, raw16907step1 i j = -(raw16907step0 i j); unfold raw16907step1 raw16907step0; decide +kernel
      have hl : raw16907step1Labels = raw16907step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16907step1 raw16907step1Labels = mixedMoment B raw16907step2 raw16907step2Labels := by
      have ha : raw16907step2 = raw16907step1 := by apply Matrix.ext; unfold raw16907step2 raw16907step1; decide +kernel
      have hl : raw16907step1Labels = labelEmbedding1 ∘ raw16907step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16907step1 raw16907step1Labels raw16907step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3938 node3938Labels := by rfl

theorem canonical16908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16908 raw16908Labels = mixedMoment B node2631 node2631Labels := by
  calc
    mixedMoment B raw16908 raw16908Labels = mixedMoment B raw16908step0 raw16908step0Labels := by
      have ha : raw16908step0 = (fun i j => raw16908 (permutation287 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16908step0 raw16908; decide +kernel
      have hl : raw16908step0Labels = raw16908Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16908 raw16908Labels permutation287 permutation5
    mixedMoment B raw16908step0 raw16908step0Labels = mixedMoment B raw16908step1 raw16908step1Labels := by
      have ha : raw16908step1 = -raw16908step0 := by apply Matrix.ext; change ∀ i j, raw16908step1 i j = -(raw16908step0 i j); unfold raw16908step1 raw16908step0; decide +kernel
      have hl : raw16908step1Labels = raw16908step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16908step1 raw16908step1Labels = mixedMoment B raw16908step2 raw16908step2Labels := by
      have ha : raw16908step2 = raw16908step1 := by apply Matrix.ext; unfold raw16908step2 raw16908step1; decide +kernel
      have hl : raw16908step1Labels = labelEmbedding1 ∘ raw16908step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16908step1 raw16908step1Labels raw16908step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2631 node2631Labels := by rfl

theorem canonical16909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16909 raw16909Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw16909 raw16909Labels = mixedMoment B raw16909step0 raw16909step0Labels := by
      have hz : ∀ j, raw16909 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16909step0 = (fun i j => raw16909 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16909step0 raw16909; decide +kernel
      have hl : raw16909step0Labels = raw16909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16909 raw16909Labels permutation346 hz
    mixedMoment B raw16909step0 raw16909step0Labels = mixedMoment B raw16909step1 raw16909step1Labels := by
      have ha : raw16909step1 = (fun i j => raw16909step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16909step1 raw16909step0; decide +kernel
      have hl : raw16909step1Labels = raw16909step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16909step0 raw16909step0Labels permutation151 permutation7
    mixedMoment B raw16909step1 raw16909step1Labels = mixedMoment B raw16909step2 raw16909step2Labels := by
      have ha : raw16909step2 = -raw16909step1 := by apply Matrix.ext; change ∀ i j, raw16909step2 i j = -(raw16909step1 i j); unfold raw16909step2 raw16909step1; decide +kernel
      have hl : raw16909step2Labels = raw16909step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16909step2 raw16909step2Labels = mixedMoment B raw16909step3 raw16909step3Labels := by
      have ha : raw16909step3 = raw16909step2 := by apply Matrix.ext; unfold raw16909step3 raw16909step2; decide +kernel
      have hl : raw16909step2Labels = labelEmbedding1 ∘ raw16909step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16909step2 raw16909step2Labels raw16909step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3995 node3995Labels := by rfl

theorem canonical16910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16910 raw16910Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw16910 raw16910Labels = mixedMoment B raw16910step0 raw16910step0Labels := by
      have hz : ∀ j, raw16910 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16910step0 = (fun i j => raw16910 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16910step0 raw16910; decide +kernel
      have hl : raw16910step0Labels = raw16910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16910 raw16910Labels permutation434 hz
    mixedMoment B raw16910step0 raw16910step0Labels = mixedMoment B raw16910step1 raw16910step1Labels := by
      have ha : raw16910step1 = (fun i j => raw16910step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16910step1 raw16910step0; decide +kernel
      have hl : raw16910step1Labels = raw16910step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16910step0 raw16910step0Labels permutation151 permutation7
    mixedMoment B raw16910step1 raw16910step1Labels = mixedMoment B raw16910step2 raw16910step2Labels := by
      have ha : raw16910step2 = -raw16910step1 := by apply Matrix.ext; change ∀ i j, raw16910step2 i j = -(raw16910step1 i j); unfold raw16910step2 raw16910step1; decide +kernel
      have hl : raw16910step2Labels = raw16910step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16910step2 raw16910step2Labels = mixedMoment B raw16910step3 raw16910step3Labels := by
      have ha : raw16910step3 = raw16910step2 := by apply Matrix.ext; unfold raw16910step3 raw16910step2; decide +kernel
      have hl : raw16910step2Labels = labelEmbedding1 ∘ raw16910step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16910step2 raw16910step2Labels raw16910step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3995 node3995Labels := by rfl

theorem canonical16911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16911 raw16911Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw16911 raw16911Labels = mixedMoment B raw16911step0 raw16911step0Labels := by
      have ha : raw16911step0 = (fun i j => raw16911 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16911step0 raw16911; decide +kernel
      have hl : raw16911step0Labels = raw16911Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16911 raw16911Labels permutation682 permutation7
    mixedMoment B raw16911step0 raw16911step0Labels = mixedMoment B raw16911step1 raw16911step1Labels := by
      have ha : raw16911step1 = -raw16911step0 := by apply Matrix.ext; change ∀ i j, raw16911step1 i j = -(raw16911step0 i j); unfold raw16911step1 raw16911step0; decide +kernel
      have hl : raw16911step1Labels = raw16911step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16911step1 raw16911step1Labels = mixedMoment B raw16911step2 raw16911step2Labels := by
      have ha : raw16911step2 = raw16911step1 := by apply Matrix.ext; unfold raw16911step2 raw16911step1; decide +kernel
      have hl : raw16911step1Labels = labelEmbedding1 ∘ raw16911step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16911step1 raw16911step1Labels raw16911step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3846 node3846Labels := by rfl

theorem canonical16912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16912 raw16912Labels = mixedMoment B node3937 node3937Labels := by
  calc
    mixedMoment B raw16912 raw16912Labels = mixedMoment B raw16912step0 raw16912step0Labels := by
      have ha : raw16912step0 = (fun i j => raw16912 (permutation277 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16912step0 raw16912; decide +kernel
      have hl : raw16912step0Labels = raw16912Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16912 raw16912Labels permutation277 permutation5
    mixedMoment B raw16912step0 raw16912step0Labels = mixedMoment B raw16912step1 raw16912step1Labels := by
      have ha : raw16912step1 = -raw16912step0 := by apply Matrix.ext; change ∀ i j, raw16912step1 i j = -(raw16912step0 i j); unfold raw16912step1 raw16912step0; decide +kernel
      have hl : raw16912step1Labels = raw16912step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16912step1 raw16912step1Labels = mixedMoment B raw16912step2 raw16912step2Labels := by
      have ha : raw16912step2 = raw16912step1 := by apply Matrix.ext; unfold raw16912step2 raw16912step1; decide +kernel
      have hl : raw16912step1Labels = labelEmbedding1 ∘ raw16912step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16912step1 raw16912step1Labels raw16912step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3937 node3937Labels := by rfl

theorem canonical16913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16913 raw16913Labels = mixedMoment B node2617 node2617Labels := by
  calc
    mixedMoment B raw16913 raw16913Labels = mixedMoment B raw16913step0 raw16913step0Labels := by
      have ha : raw16913step0 = (fun i j => raw16913 (permutation277 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16913step0 raw16913; decide +kernel
      have hl : raw16913step0Labels = raw16913Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16913 raw16913Labels permutation277 permutation5
    mixedMoment B raw16913step0 raw16913step0Labels = mixedMoment B raw16913step1 raw16913step1Labels := by
      have ha : raw16913step1 = -raw16913step0 := by apply Matrix.ext; change ∀ i j, raw16913step1 i j = -(raw16913step0 i j); unfold raw16913step1 raw16913step0; decide +kernel
      have hl : raw16913step1Labels = raw16913step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16913step1 raw16913step1Labels = mixedMoment B raw16913step2 raw16913step2Labels := by
      have ha : raw16913step2 = raw16913step1 := by apply Matrix.ext; unfold raw16913step2 raw16913step1; decide +kernel
      have hl : raw16913step1Labels = labelEmbedding1 ∘ raw16913step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16913step1 raw16913step1Labels raw16913step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2617 node2617Labels := by rfl

theorem canonical16914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16914 raw16914Labels = mixedMoment B node4003 node4003Labels := by
  calc
    mixedMoment B raw16914 raw16914Labels = mixedMoment B raw16914step0 raw16914step0Labels := by
      have hz : ∀ j, raw16914 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16914step0 = (fun i j => raw16914 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16914step0 raw16914; decide +kernel
      have hl : raw16914step0Labels = raw16914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16914 raw16914Labels permutation346 hz
    mixedMoment B raw16914step0 raw16914step0Labels = mixedMoment B raw16914step1 raw16914step1Labels := by
      have ha : raw16914step1 = (fun i j => raw16914step0 (permutation58 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16914step1 raw16914step0; decide +kernel
      have hl : raw16914step1Labels = raw16914step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16914step0 raw16914step0Labels permutation58 permutation5
    mixedMoment B raw16914step1 raw16914step1Labels = mixedMoment B raw16914step2 raw16914step2Labels := by
      have ha : raw16914step2 = -raw16914step1 := by apply Matrix.ext; change ∀ i j, raw16914step2 i j = -(raw16914step1 i j); unfold raw16914step2 raw16914step1; decide +kernel
      have hl : raw16914step2Labels = raw16914step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16914step2 raw16914step2Labels = mixedMoment B raw16914step3 raw16914step3Labels := by
      have ha : raw16914step3 = raw16914step2 := by apply Matrix.ext; unfold raw16914step3 raw16914step2; decide +kernel
      have hl : raw16914step2Labels = labelEmbedding1 ∘ raw16914step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16914step2 raw16914step2Labels raw16914step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4003 node4003Labels := by rfl

theorem canonical16915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16915 raw16915Labels = mixedMoment B node4003 node4003Labels := by
  calc
    mixedMoment B raw16915 raw16915Labels = mixedMoment B raw16915step0 raw16915step0Labels := by
      have hz : ∀ j, raw16915 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16915step0 = (fun i j => raw16915 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16915step0 raw16915; decide +kernel
      have hl : raw16915step0Labels = raw16915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16915 raw16915Labels permutation434 hz
    mixedMoment B raw16915step0 raw16915step0Labels = mixedMoment B raw16915step1 raw16915step1Labels := by
      have ha : raw16915step1 = (fun i j => raw16915step0 (permutation58 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16915step1 raw16915step0; decide +kernel
      have hl : raw16915step1Labels = raw16915step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16915step0 raw16915step0Labels permutation58 permutation5
    mixedMoment B raw16915step1 raw16915step1Labels = mixedMoment B raw16915step2 raw16915step2Labels := by
      have ha : raw16915step2 = -raw16915step1 := by apply Matrix.ext; change ∀ i j, raw16915step2 i j = -(raw16915step1 i j); unfold raw16915step2 raw16915step1; decide +kernel
      have hl : raw16915step2Labels = raw16915step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16915step2 raw16915step2Labels = mixedMoment B raw16915step3 raw16915step3Labels := by
      have ha : raw16915step3 = raw16915step2 := by apply Matrix.ext; unfold raw16915step3 raw16915step2; decide +kernel
      have hl : raw16915step2Labels = labelEmbedding1 ∘ raw16915step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16915step2 raw16915step2Labels raw16915step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4003 node4003Labels := by rfl

theorem canonical16916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16916 raw16916Labels = mixedMoment B node3949 node3949Labels := by
  calc
    mixedMoment B raw16916 raw16916Labels = mixedMoment B raw16916step0 raw16916step0Labels := by
      have ha : raw16916step0 = (fun i j => raw16916 (permutation322 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16916step0 raw16916; decide +kernel
      have hl : raw16916step0Labels = raw16916Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16916 raw16916Labels permutation322 permutation5
    mixedMoment B raw16916step0 raw16916step0Labels = mixedMoment B raw16916step1 raw16916step1Labels := by
      have ha : raw16916step1 = -raw16916step0 := by apply Matrix.ext; change ∀ i j, raw16916step1 i j = -(raw16916step0 i j); unfold raw16916step1 raw16916step0; decide +kernel
      have hl : raw16916step1Labels = raw16916step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16916step1 raw16916step1Labels = mixedMoment B raw16916step2 raw16916step2Labels := by
      have ha : raw16916step2 = raw16916step1 := by apply Matrix.ext; unfold raw16916step2 raw16916step1; decide +kernel
      have hl : raw16916step1Labels = labelEmbedding1 ∘ raw16916step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16916step1 raw16916step1Labels raw16916step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3949 node3949Labels := by rfl

theorem canonical16917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16917 raw16917Labels = mixedMoment B node3956 node3956Labels := by
  calc
    mixedMoment B raw16917 raw16917Labels = mixedMoment B raw16917step0 raw16917step0Labels := by
      have ha : raw16917step0 = (fun i j => raw16917 (permutation277 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16917step0 raw16917; decide +kernel
      have hl : raw16917step0Labels = raw16917Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16917 raw16917Labels permutation277 permutation4
    mixedMoment B raw16917step0 raw16917step0Labels = mixedMoment B raw16917step1 raw16917step1Labels := by
      have ha : raw16917step1 = -raw16917step0 := by apply Matrix.ext; change ∀ i j, raw16917step1 i j = -(raw16917step0 i j); unfold raw16917step1 raw16917step0; decide +kernel
      have hl : raw16917step1Labels = raw16917step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3956 node3956Labels := by rfl

theorem canonical16918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16918 raw16918Labels = mixedMoment B node3691 node3691Labels := by
  calc
    mixedMoment B raw16918 raw16918Labels = mixedMoment B raw16918step0 raw16918step0Labels := by
      have ha : raw16918step0 = (fun i j => raw16918 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16918step0 raw16918; decide +kernel
      have hl : raw16918step0Labels = raw16918Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16918 raw16918Labels permutation167 permutation4
    mixedMoment B raw16918step0 raw16918step0Labels = mixedMoment B raw16918step1 raw16918step1Labels := by
      have ha : raw16918step1 = -raw16918step0 := by apply Matrix.ext; change ∀ i j, raw16918step1 i j = -(raw16918step0 i j); unfold raw16918step1 raw16918step0; decide +kernel
      have hl : raw16918step1Labels = raw16918step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3691 node3691Labels := by rfl

theorem canonical16919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16919 raw16919Labels = mixedMoment B node3691 node3691Labels := by
  calc
    mixedMoment B raw16919 raw16919Labels = mixedMoment B raw16919step0 raw16919step0Labels := by
      have ha : raw16919step0 = (fun i j => raw16919 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16919step0 raw16919; decide +kernel
      have hl : raw16919step0Labels = raw16919Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16919 raw16919Labels permutation165 permutation4
    mixedMoment B raw16919step0 raw16919step0Labels = mixedMoment B raw16919step1 raw16919step1Labels := by
      have ha : raw16919step1 = -raw16919step0 := by apply Matrix.ext; change ∀ i j, raw16919step1 i j = -(raw16919step0 i j); unfold raw16919step1 raw16919step0; decide +kernel
      have hl : raw16919step1Labels = raw16919step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3691 node3691Labels := by rfl

theorem canonical16920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16920 raw16920Labels = mixedMoment B node3703 node3703Labels := by
  calc
    mixedMoment B raw16920 raw16920Labels = mixedMoment B raw16920step0 raw16920step0Labels := by
      have ha : raw16920step0 = (fun i j => raw16920 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16920step0 raw16920; decide +kernel
      have hl : raw16920step0Labels = raw16920Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16920 raw16920Labels permutation152 permutation4
    mixedMoment B raw16920step0 raw16920step0Labels = mixedMoment B raw16920step1 raw16920step1Labels := by
      have ha : raw16920step1 = -raw16920step0 := by apply Matrix.ext; change ∀ i j, raw16920step1 i j = -(raw16920step0 i j); unfold raw16920step1 raw16920step0; decide +kernel
      have hl : raw16920step1Labels = raw16920step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3703 node3703Labels := by rfl

theorem canonical16921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16921 raw16921Labels = mixedMoment B node3689 node3689Labels := by
  calc
    mixedMoment B raw16921 raw16921Labels = mixedMoment B raw16921step0 raw16921step0Labels := by
      have ha : raw16921step0 = (fun i j => raw16921 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16921step0 raw16921; decide +kernel
      have hl : raw16921step0Labels = raw16921Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16921 raw16921Labels permutation164 permutation4
    mixedMoment B raw16921step0 raw16921step0Labels = mixedMoment B raw16921step1 raw16921step1Labels := by
      have ha : raw16921step1 = -raw16921step0 := by apply Matrix.ext; change ∀ i j, raw16921step1 i j = -(raw16921step0 i j); unfold raw16921step1 raw16921step0; decide +kernel
      have hl : raw16921step1Labels = raw16921step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3689 node3689Labels := by rfl

theorem canonical17017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17017 raw17017Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw17017 raw17017Labels = mixedMoment B raw17017step0 raw17017step0Labels := by
      have ha : raw17017step0 = (fun i j => raw17017 (permutation439 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17017step0 raw17017; decide +kernel
      have hl : raw17017step0Labels = raw17017Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17017 raw17017Labels permutation439 permutation4
    mixedMoment B raw17017step0 raw17017step0Labels = mixedMoment B raw17017step1 raw17017step1Labels := by
      have ha : raw17017step1 = -raw17017step0 := by apply Matrix.ext; change ∀ i j, raw17017step1 i j = -(raw17017step0 i j); unfold raw17017step1 raw17017step0; decide +kernel
      have hl : raw17017step1Labels = raw17017step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3880 node3880Labels := by rfl

theorem canonical17023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17023 raw17023Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw17023 raw17023Labels = mixedMoment B raw17023step0 raw17023step0Labels := by
      have hz : ∀ j, raw17023 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17023step0 = (fun i j => raw17023 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17023step0 raw17023; decide +kernel
      have hl : raw17023step0Labels = raw17023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17023 raw17023Labels permutation520 hz
    mixedMoment B raw17023step0 raw17023step0Labels = mixedMoment B raw17023step1 raw17023step1Labels := by
      have ha : raw17023step1 = (fun i j => raw17023step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw17023step1 raw17023step0; decide +kernel
      have hl : raw17023step1Labels = raw17023step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17023step0 raw17023step0Labels permutation122 permutation0
    mixedMoment B raw17023step1 raw17023step1Labels = mixedMoment B raw17023step2 raw17023step2Labels := by
      have ha : raw17023step2 = -raw17023step1 := by apply Matrix.ext; change ∀ i j, raw17023step2 i j = -(raw17023step1 i j); unfold raw17023step2 raw17023step1; decide +kernel
      have hl : raw17023step2Labels = raw17023step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical133
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17024 raw17024Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw17024 raw17024Labels = mixedMoment B raw17024step0 raw17024step0Labels := by
      have ha : raw17024step0 = (fun i j => raw17024 (permutation435 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17024step0 raw17024; decide +kernel
      have hl : raw17024step0Labels = raw17024Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17024 raw17024Labels permutation435 permutation4
    mixedMoment B raw17024step0 raw17024step0Labels = mixedMoment B raw17024step1 raw17024step1Labels := by
      have ha : raw17024step1 = -raw17024step0 := by apply Matrix.ext; change ∀ i j, raw17024step1 i j = -(raw17024step0 i j); unfold raw17024step1 raw17024step0; decide +kernel
      have hl : raw17024step1Labels = raw17024step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3909 node3909Labels := by rfl

theorem canonical17025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17025 raw17025Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw17025 raw17025Labels = mixedMoment B raw17025step0 raw17025step0Labels := by
      have ha : raw17025step0 = (fun i j => raw17025 (permutation442 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17025step0 raw17025; decide +kernel
      have hl : raw17025step0Labels = raw17025Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17025 raw17025Labels permutation442 permutation4
    mixedMoment B raw17025step0 raw17025step0Labels = mixedMoment B raw17025step1 raw17025step1Labels := by
      have ha : raw17025step1 = -raw17025step0 := by apply Matrix.ext; change ∀ i j, raw17025step1 i j = -(raw17025step0 i j); unfold raw17025step1 raw17025step0; decide +kernel
      have hl : raw17025step1Labels = raw17025step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3880 node3880Labels := by rfl

theorem canonical17026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17026 raw17026Labels = mixedMoment B node3945 node3945Labels := by
  calc
    mixedMoment B raw17026 raw17026Labels = mixedMoment B raw17026step0 raw17026step0Labels := by
      have ha : raw17026step0 = (fun i j => raw17026 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17026step0 raw17026; decide +kernel
      have hl : raw17026step0Labels = raw17026Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17026 raw17026Labels permutation662 permutation2
    mixedMoment B raw17026step0 raw17026step0Labels = mixedMoment B raw17026step1 raw17026step1Labels := by
      have ha : raw17026step1 = -raw17026step0 := by apply Matrix.ext; change ∀ i j, raw17026step1 i j = -(raw17026step0 i j); unfold raw17026step1 raw17026step0; decide +kernel
      have hl : raw17026step1Labels = raw17026step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3945 node3945Labels := by rfl

theorem canonical17027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17027 raw17027Labels = mixedMoment B node3878 node3878Labels := by
  calc
    mixedMoment B raw17027 raw17027Labels = mixedMoment B raw17027step0 raw17027step0Labels := by
      have ha : raw17027step0 = (fun i j => raw17027 (permutation435 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17027step0 raw17027; decide +kernel
      have hl : raw17027step0Labels = raw17027Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17027 raw17027Labels permutation435 permutation4
    mixedMoment B raw17027step0 raw17027step0Labels = mixedMoment B raw17027step1 raw17027step1Labels := by
      have ha : raw17027step1 = -raw17027step0 := by apply Matrix.ext; change ∀ i j, raw17027step1 i j = -(raw17027step0 i j); unfold raw17027step1 raw17027step0; decide +kernel
      have hl : raw17027step1Labels = raw17027step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3878 node3878Labels := by rfl

theorem canonical17028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17028 raw17028Labels = mixedMoment B node2976 node2976Labels := by
  calc
    mixedMoment B raw17028 raw17028Labels = mixedMoment B raw17028step0 raw17028step0Labels := by
      have ha : raw17028step0 = (fun i j => raw17028 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17028step0 raw17028; decide +kernel
      have hl : raw17028step0Labels = raw17028Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17028 raw17028Labels permutation686 permutation2
    mixedMoment B raw17028step0 raw17028step0Labels = mixedMoment B raw17028step1 raw17028step1Labels := by
      have ha : raw17028step1 = -raw17028step0 := by apply Matrix.ext; change ∀ i j, raw17028step1 i j = -(raw17028step0 i j); unfold raw17028step1 raw17028step0; decide +kernel
      have hl : raw17028step1Labels = raw17028step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2976 node2976Labels := by rfl

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

theorem canonical2394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2394 raw2394Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw2394 raw2394Labels = mixedMoment B raw2394step0 raw2394step0Labels := by
      have ha : raw2394step0 = (fun i j => raw2394 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2394step0 raw2394; decide +kernel
      have hl : raw2394step0Labels = raw2394Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2394 raw2394Labels permutation152 permutation4
    mixedMoment B raw2394step0 raw2394step0Labels = mixedMoment B raw2394step1 raw2394step1Labels := by
      have ha : raw2394step1 = raw2394step0 := by apply Matrix.ext; unfold raw2394step1 raw2394step0; decide +kernel
      have hl : raw2394step0Labels = labelEmbedding7 ∘ raw2394step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2394step0 raw2394step0Labels raw2394step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

theorem canonical2395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2395 raw2395Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw2395 raw2395Labels = mixedMoment B raw2395step0 raw2395step0Labels := by
      have ha : raw2395step0 = (fun i j => raw2395 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2395step0 raw2395; decide +kernel
      have hl : raw2395step0Labels = raw2395Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2395 raw2395Labels permutation152 permutation4
    _ = mixedMoment B node3690 node3690Labels := by rfl

theorem canonical2396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2396 raw2396Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw2396 raw2396Labels = mixedMoment B raw2396step0 raw2396step0Labels := by
      have ha : raw2396step0 = (fun i j => raw2396 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2396step0 raw2396; decide +kernel
      have hl : raw2396step0Labels = raw2396Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2396 raw2396Labels permutation158 permutation6
    mixedMoment B raw2396step0 raw2396step0Labels = mixedMoment B raw2396step1 raw2396step1Labels := by
      have ha : raw2396step1 = -raw2396step0 := by apply Matrix.ext; change ∀ i j, raw2396step1 i j = -(raw2396step0 i j); unfold raw2396step1 raw2396step0; decide +kernel
      have hl : raw2396step1Labels = raw2396step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2396step1 raw2396step1Labels = mixedMoment B raw2396step2 raw2396step2Labels := by
      have ha : raw2396step2 = raw2396step1 := by apply Matrix.ext; unfold raw2396step2 raw2396step1; decide +kernel
      have hl : raw2396step1Labels = labelEmbedding1 ∘ raw2396step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2396step1 raw2396step1Labels raw2396step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

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

theorem canonical2484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2484 raw2484Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw2484 raw2484Labels = mixedMoment B raw2484step0 raw2484step0Labels := by
      have ha : raw2484step0 = (fun i j => raw2484 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2484step0 raw2484; decide +kernel
      have hl : raw2484step0Labels = raw2484Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2484 raw2484Labels permutation152 permutation4
    mixedMoment B raw2484step0 raw2484step0Labels = mixedMoment B raw2484step1 raw2484step1Labels := by
      have ha : raw2484step1 = raw2484step0 := by apply Matrix.ext; unfold raw2484step1 raw2484step0; decide +kernel
      have hl : raw2484step0Labels = labelEmbedding7 ∘ raw2484step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2484step0 raw2484step0Labels raw2484step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

theorem canonical2485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2485 raw2485Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw2485 raw2485Labels = mixedMoment B raw2485step0 raw2485step0Labels := by
      have ha : raw2485step0 = (fun i j => raw2485 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2485step0 raw2485; decide +kernel
      have hl : raw2485step0Labels = raw2485Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2485 raw2485Labels permutation152 permutation4
    _ = mixedMoment B node3800 node3800Labels := by rfl

theorem canonical2486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2486 raw2486Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw2486 raw2486Labels = mixedMoment B raw2486step0 raw2486step0Labels := by
      have ha : raw2486step0 = (fun i j => raw2486 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2486step0 raw2486; decide +kernel
      have hl : raw2486step0Labels = raw2486Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2486 raw2486Labels permutation164 permutation6
    mixedMoment B raw2486step0 raw2486step0Labels = mixedMoment B raw2486step1 raw2486step1Labels := by
      have ha : raw2486step1 = -raw2486step0 := by apply Matrix.ext; change ∀ i j, raw2486step1 i j = -(raw2486step0 i j); unfold raw2486step1 raw2486step0; decide +kernel
      have hl : raw2486step1Labels = raw2486step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2486step1 raw2486step1Labels = mixedMoment B raw2486step2 raw2486step2Labels := by
      have ha : raw2486step2 = raw2486step1 := by apply Matrix.ext; unfold raw2486step2 raw2486step1; decide +kernel
      have hl : raw2486step1Labels = labelEmbedding1 ∘ raw2486step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2486step1 raw2486step1Labels raw2486step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3805 node3805Labels := by rfl

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

theorem canonical2550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2550 raw2550Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw2550 raw2550Labels = mixedMoment B raw2550step0 raw2550step0Labels := by
      have ha : raw2550step0 = (fun i j => raw2550 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2550step0 raw2550; decide +kernel
      have hl : raw2550step0Labels = raw2550Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2550 raw2550Labels permutation32 permutation4
    mixedMoment B raw2550step0 raw2550step0Labels = mixedMoment B raw2550step1 raw2550step1Labels := by
      have ha : raw2550step1 = raw2550step0 := by apply Matrix.ext; unfold raw2550step1 raw2550step0; decide +kernel
      have hl : raw2550step0Labels = labelEmbedding7 ∘ raw2550step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2550step0 raw2550step0Labels raw2550step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

theorem canonical2551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2551 raw2551Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw2551 raw2551Labels = mixedMoment B raw2551step0 raw2551step0Labels := by
      have ha : raw2551step0 = (fun i j => raw2551 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2551step0 raw2551; decide +kernel
      have hl : raw2551step0Labels = raw2551Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2551 raw2551Labels permutation32 permutation4
    _ = mixedMoment B node3885 node3885Labels := by rfl

theorem canonical2552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2552 raw2552Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw2552 raw2552Labels = mixedMoment B raw2552step0 raw2552step0Labels := by
      have ha : raw2552step0 = (fun i j => raw2552 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2552step0 raw2552; decide +kernel
      have hl : raw2552step0Labels = raw2552Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2552 raw2552Labels permutation38 permutation6
    mixedMoment B raw2552step0 raw2552step0Labels = mixedMoment B raw2552step1 raw2552step1Labels := by
      have ha : raw2552step1 = -raw2552step0 := by apply Matrix.ext; change ∀ i j, raw2552step1 i j = -(raw2552step0 i j); unfold raw2552step1 raw2552step0; decide +kernel
      have hl : raw2552step1Labels = raw2552step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2552step1 raw2552step1Labels = mixedMoment B raw2552step2 raw2552step2Labels := by
      have ha : raw2552step2 = raw2552step1 := by apply Matrix.ext; unfold raw2552step2 raw2552step1; decide +kernel
      have hl : raw2552step1Labels = labelEmbedding1 ∘ raw2552step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2552step1 raw2552step1Labels raw2552step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3885 node3885Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2586 raw2586Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw2586 raw2586Labels = mixedMoment B raw2586step0 raw2586step0Labels := by
      have ha : raw2586step0 = (fun i j => raw2586 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2586step0 raw2586; decide +kernel
      have hl : raw2586step0Labels = raw2586Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2586 raw2586Labels permutation152 permutation4
    mixedMoment B raw2586step0 raw2586step0Labels = mixedMoment B raw2586step1 raw2586step1Labels := by
      have ha : raw2586step1 = raw2586step0 := by apply Matrix.ext; unfold raw2586step1 raw2586step0; decide +kernel
      have hl : raw2586step0Labels = labelEmbedding7 ∘ raw2586step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2586step0 raw2586step0Labels raw2586step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5472 node5472Labels := by rfl

theorem canonical2587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2587 raw2587Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw2587 raw2587Labels = mixedMoment B raw2587step0 raw2587step0Labels := by
      have ha : raw2587step0 = (fun i j => raw2587 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2587step0 raw2587; decide +kernel
      have hl : raw2587step0Labels = raw2587Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2587 raw2587Labels permutation152 permutation4
    _ = mixedMoment B node3957 node3957Labels := by rfl

theorem canonical2588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2588 raw2588Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw2588 raw2588Labels = mixedMoment B raw2588step0 raw2588step0Labels := by
      have ha : raw2588step0 = (fun i j => raw2588 (permutation271 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2588step0 raw2588; decide +kernel
      have hl : raw2588step0Labels = raw2588Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2588 raw2588Labels permutation271 permutation6
    mixedMoment B raw2588step0 raw2588step0Labels = mixedMoment B raw2588step1 raw2588step1Labels := by
      have ha : raw2588step1 = -raw2588step0 := by apply Matrix.ext; change ∀ i j, raw2588step1 i j = -(raw2588step0 i j); unfold raw2588step1 raw2588step0; decide +kernel
      have hl : raw2588step1Labels = raw2588step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2588step1 raw2588step1Labels = mixedMoment B raw2588step2 raw2588step2Labels := by
      have ha : raw2588step2 = raw2588step1 := by apply Matrix.ext; unfold raw2588step2 raw2588step1; decide +kernel
      have hl : raw2588step1Labels = labelEmbedding1 ∘ raw2588step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2588step1 raw2588step1Labels raw2588step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3957 node3957Labels := by rfl

theorem canonical2589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2589 raw2589Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw2589 raw2589Labels = mixedMoment B raw2589step0 raw2589step0Labels := by
      have ha : raw2589step0 = (fun i j => raw2589 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2589step0 raw2589; decide +kernel
      have hl : raw2589step0Labels = raw2589Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2589 raw2589Labels permutation32 permutation4
    mixedMoment B raw2589step0 raw2589step0Labels = mixedMoment B raw2589step1 raw2589step1Labels := by
      have ha : raw2589step1 = raw2589step0 := by apply Matrix.ext; unfold raw2589step1 raw2589step0; decide +kernel
      have hl : raw2589step0Labels = labelEmbedding7 ∘ raw2589step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2589step0 raw2589step0Labels raw2589step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical2590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2590 raw2590Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw2590 raw2590Labels = mixedMoment B raw2590step0 raw2590step0Labels := by
      have ha : raw2590step0 = (fun i j => raw2590 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2590step0 raw2590; decide +kernel
      have hl : raw2590step0Labels = raw2590Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2590 raw2590Labels permutation32 permutation4
    _ = mixedMoment B node3958 node3958Labels := by rfl

theorem canonical2591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2591 raw2591Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw2591 raw2591Labels = mixedMoment B raw2591step0 raw2591step0Labels := by
      have ha : raw2591step0 = (fun i j => raw2591 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2591step0 raw2591; decide +kernel
      have hl : raw2591step0Labels = raw2591Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2591 raw2591Labels permutation56 permutation6
    mixedMoment B raw2591step0 raw2591step0Labels = mixedMoment B raw2591step1 raw2591step1Labels := by
      have ha : raw2591step1 = -raw2591step0 := by apply Matrix.ext; change ∀ i j, raw2591step1 i j = -(raw2591step0 i j); unfold raw2591step1 raw2591step0; decide +kernel
      have hl : raw2591step1Labels = raw2591step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2591step1 raw2591step1Labels = mixedMoment B raw2591step2 raw2591step2Labels := by
      have ha : raw2591step2 = raw2591step1 := by apply Matrix.ext; unfold raw2591step2 raw2591step1; decide +kernel
      have hl : raw2591step1Labels = labelEmbedding1 ∘ raw2591step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2591step1 raw2591step1Labels raw2591step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5352 node5352Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3690 node3690Labels + mixedMoment B node3764 node3764Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2394 singletonSmall5352
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5352) = raw2394Labels := by decide +kernel
  rw [hl, canonical2394 B hB] at h
  have hc0 : mixedMoment B raw2394 (Fin.cases (0 : Fin 2) singletonSmall5352) =
      mixedMoment B node3690 node3690Labels := by
    have ha : raw2394 = raw2395 := by apply Matrix.ext; unfold raw2394 raw2395; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5352 = raw2395Labels := by decide +kernel
    rw [ha, hj, canonical2395 B hB]
  have hc1 : mixedMoment B raw2394 (Fin.cases (1 : Fin 2) singletonSmall5352) =
      mixedMoment B node3764 node3764Labels := by
    have ha : raw2394 = raw2396 := by apply Matrix.ext; unfold raw2394 raw2396; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5352 = raw2396Labels := by decide +kernel
    rw [ha, hj, canonical2396 B hB]
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

theorem singleton5405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5405 node5405Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3800 node3800Labels + mixedMoment B node3805 node3805Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2484 singletonSmall5405
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5405) = raw2484Labels := by decide +kernel
  rw [hl, canonical2484 B hB] at h
  have hc0 : mixedMoment B raw2484 (Fin.cases (0 : Fin 2) singletonSmall5405) =
      mixedMoment B node3800 node3800Labels := by
    have ha : raw2484 = raw2485 := by apply Matrix.ext; unfold raw2484 raw2485; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5405 = raw2485Labels := by decide +kernel
    rw [ha, hj, canonical2485 B hB]
  have hc1 : mixedMoment B raw2484 (Fin.cases (1 : Fin 2) singletonSmall5405) =
      mixedMoment B node3805 node3805Labels := by
    have ha : raw2484 = raw2486 := by apply Matrix.ext; unfold raw2484 raw2486; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5405 = raw2486Labels := by decide +kernel
    rw [ha, hj, canonical2486 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5448 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5448 node5448Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3885 node3885Labels + mixedMoment B node3885 node3885Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2550 singletonSmall5448
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5448) = raw2550Labels := by decide +kernel
  rw [hl, canonical2550 B hB] at h
  have hc0 : mixedMoment B raw2550 (Fin.cases (0 : Fin 2) singletonSmall5448) =
      mixedMoment B node3885 node3885Labels := by
    have ha : raw2550 = raw2551 := by apply Matrix.ext; unfold raw2550 raw2551; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5448 = raw2551Labels := by decide +kernel
    rw [ha, hj, canonical2551 B hB]
  have hc1 : mixedMoment B raw2550 (Fin.cases (1 : Fin 2) singletonSmall5448) =
      mixedMoment B node3885 node3885Labels := by
    have ha : raw2550 = raw2552 := by apply Matrix.ext; unfold raw2550 raw2552; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5448 = raw2552Labels := by decide +kernel
    rw [ha, hj, canonical2552 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5472 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5472 node5472Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3957 node3957Labels + mixedMoment B node3957 node3957Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2586 singletonSmall5472
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5472) = raw2586Labels := by decide +kernel
  rw [hl, canonical2586 B hB] at h
  have hc0 : mixedMoment B raw2586 (Fin.cases (0 : Fin 2) singletonSmall5472) =
      mixedMoment B node3957 node3957Labels := by
    have ha : raw2586 = raw2587 := by apply Matrix.ext; unfold raw2586 raw2587; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5472 = raw2587Labels := by decide +kernel
    rw [ha, hj, canonical2587 B hB]
  have hc1 : mixedMoment B raw2586 (Fin.cases (1 : Fin 2) singletonSmall5472) =
      mixedMoment B node3957 node3957Labels := by
    have ha : raw2586 = raw2588 := by apply Matrix.ext; unfold raw2586 raw2588; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5472 = raw2588Labels := by decide +kernel
    rw [ha, hj, canonical2588 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5473 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5473 node5473Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3958 node3958Labels + mixedMoment B node3961 node3961Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2589 singletonSmall5473
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5473) = raw2589Labels := by decide +kernel
  rw [hl, canonical2589 B hB] at h
  have hc0 : mixedMoment B raw2589 (Fin.cases (0 : Fin 2) singletonSmall5473) =
      mixedMoment B node3958 node3958Labels := by
    have ha : raw2589 = raw2590 := by apply Matrix.ext; unfold raw2589 raw2590; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5473 = raw2590Labels := by decide +kernel
    rw [ha, hj, canonical2590 B hB]
  have hc1 : mixedMoment B raw2589 (Fin.cases (1 : Fin 2) singletonSmall5473) =
      mixedMoment B node3961 node3961Labels := by
    have ha : raw2589 = raw2591 := by apply Matrix.ext; unfold raw2589 raw2591; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5473 = raw2591Labels := by decide +kernel
    rw [ha, hj, canonical2591 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound2613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2613 node2613Labels = Sparse.eval nodeValue2613 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2613) = mixedMoment B node2613 node2613Labels := rfl
  simpa [nodeValue2613, Sparse.eval] using hc.symm

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

theorem sound2728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2728 node2728Labels = Sparse.eval nodeValue2728 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2728) = mixedMoment B node2728 node2728Labels := rfl
  simpa [nodeValue2728, Sparse.eval] using hc.symm

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

theorem sound2869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2869 node2869Labels = Sparse.eval nodeValue2869 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2869) = mixedMoment B node2869 node2869Labels := rfl
  simpa [nodeValue2869, Sparse.eval] using hc.symm

theorem sound2871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2871 node2871Labels = Sparse.eval nodeValue2871 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2871) = mixedMoment B node2871 node2871Labels := rfl
  simpa [nodeValue2871, Sparse.eval] using hc.symm

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

theorem sound2882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2882 node2882Labels = Sparse.eval nodeValue2882 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2882) = mixedMoment B node2882 node2882Labels := rfl
  simpa [nodeValue2882, Sparse.eval] using hc.symm

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

theorem sound2976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2976 node2976Labels = Sparse.eval nodeValue2976 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2976) = mixedMoment B node2976 node2976Labels := rfl
  simpa [nodeValue2976, Sparse.eval] using hc.symm

theorem sound2981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2981 node2981Labels = Sparse.eval nodeValue2981 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2981) = mixedMoment B node2981 node2981Labels := rfl
  simpa [nodeValue2981, Sparse.eval] using hc.symm

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

theorem sound3044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3044 node3044Labels = Sparse.eval nodeValue3044 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3044) = mixedMoment B node3044 node3044Labels := rfl
  simpa [nodeValue3044, Sparse.eval] using hc.symm

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

theorem sound3685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3685 node3685Labels = Sparse.eval nodeValue3685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3685) = mixedMoment B node3685 node3685Labels := rfl
  simpa [nodeValue3685, Sparse.eval] using hc.symm

theorem sound3689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3689 node3689Labels = Sparse.eval nodeValue3689 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3689) = mixedMoment B node3689 node3689Labels := rfl
  simpa [nodeValue3689, Sparse.eval] using hc.symm

theorem sound3690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3690 node3690Labels = Sparse.eval nodeValue3690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3690) = mixedMoment B node3690 node3690Labels := rfl
  simpa [nodeValue3690, Sparse.eval] using hc.symm

theorem sound3691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3691 node3691Labels = Sparse.eval nodeValue3691 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3691) = mixedMoment B node3691 node3691Labels := rfl
  simpa [nodeValue3691, Sparse.eval] using hc.symm

theorem sound3703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3703 node3703Labels = Sparse.eval nodeValue3703 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3703) = mixedMoment B node3703 node3703Labels := rfl
  simpa [nodeValue3703, Sparse.eval] using hc.symm

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

theorem sound3764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3764 node3764Labels = Sparse.eval nodeValue3764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3764) = mixedMoment B node3764 node3764Labels := rfl
  simpa [nodeValue3764, Sparse.eval] using hc.symm

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

theorem sound3783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3783 node3783Labels = Sparse.eval nodeValue3783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3783) = mixedMoment B node3783 node3783Labels := rfl
  simpa [nodeValue3783, Sparse.eval] using hc.symm

theorem sound3785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3785 node3785Labels = Sparse.eval nodeValue3785 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3785) = mixedMoment B node3785 node3785Labels := rfl
  simpa [nodeValue3785, Sparse.eval] using hc.symm

theorem sound3799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3799 node3799Labels = Sparse.eval nodeValue3799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3799) = mixedMoment B node3799 node3799Labels := rfl
  simpa [nodeValue3799, Sparse.eval] using hc.symm

theorem sound3800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3800 node3800Labels = Sparse.eval nodeValue3800 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3800) = mixedMoment B node3800 node3800Labels := rfl
  simpa [nodeValue3800, Sparse.eval] using hc.symm

theorem sound3802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3802 node3802Labels = Sparse.eval nodeValue3802 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3802) = mixedMoment B node3802 node3802Labels := rfl
  simpa [nodeValue3802, Sparse.eval] using hc.symm

theorem sound3805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3805 node3805Labels = Sparse.eval nodeValue3805 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3805) = mixedMoment B node3805 node3805Labels := rfl
  simpa [nodeValue3805, Sparse.eval] using hc.symm

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

theorem sound3846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3846 node3846Labels = Sparse.eval nodeValue3846 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3846) = mixedMoment B node3846 node3846Labels := rfl
  simpa [nodeValue3846, Sparse.eval] using hc.symm

theorem sound3849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3849 node3849Labels = Sparse.eval nodeValue3849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3849) = mixedMoment B node3849 node3849Labels := rfl
  simpa [nodeValue3849, Sparse.eval] using hc.symm

theorem sound3869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3869 node3869Labels = Sparse.eval nodeValue3869 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3869) = mixedMoment B node3869 node3869Labels := rfl
  simpa [nodeValue3869, Sparse.eval] using hc.symm

theorem sound3875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3875 node3875Labels = Sparse.eval nodeValue3875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3875) = mixedMoment B node3875 node3875Labels := rfl
  simpa [nodeValue3875, Sparse.eval] using hc.symm

theorem sound3876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3876 node3876Labels = Sparse.eval nodeValue3876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3876) = mixedMoment B node3876 node3876Labels := rfl
  simpa [nodeValue3876, Sparse.eval] using hc.symm

theorem sound3878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3878 node3878Labels = Sparse.eval nodeValue3878 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3878) = mixedMoment B node3878 node3878Labels := rfl
  simpa [nodeValue3878, Sparse.eval] using hc.symm

theorem sound3880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3880 node3880Labels = Sparse.eval nodeValue3880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3880) = mixedMoment B node3880 node3880Labels := rfl
  simpa [nodeValue3880, Sparse.eval] using hc.symm

theorem sound3881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3881 node3881Labels = Sparse.eval nodeValue3881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3881) = mixedMoment B node3881 node3881Labels := rfl
  simpa [nodeValue3881, Sparse.eval] using hc.symm

theorem sound3884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3884 node3884Labels = Sparse.eval nodeValue3884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3884) = mixedMoment B node3884 node3884Labels := rfl
  simpa [nodeValue3884, Sparse.eval] using hc.symm

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

theorem zero3953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3953 node3953Labels = 0 := by
  exact mixedMoment_alpha B hF node3953 node3953Labels 1 permutation200
    (by decide +kernel)

theorem zero3956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3956 node3956Labels = 0 := by
  exact mixedMoment_alpha B hF node3956 node3956Labels 1 permutation203
    (by decide +kernel)

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

theorem sound3909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3909 node3909Labels = Sparse.eval nodeValue3909 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3909) = mixedMoment B node3909 node3909Labels := rfl
  simpa [nodeValue3909, Sparse.eval] using hc.symm

theorem sound3945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3945 node3945Labels = Sparse.eval nodeValue3945 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3945) = mixedMoment B node3945 node3945Labels := rfl
  simpa [nodeValue3945, Sparse.eval] using hc.symm

theorem sound3949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3949 node3949Labels = Sparse.eval nodeValue3949 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3949) = mixedMoment B node3949 node3949Labels := rfl
  simpa [nodeValue3949, Sparse.eval] using hc.symm

theorem sound3953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3953 node3953Labels = Sparse.eval nodeValue3953 (mixedVector B) := by
  simpa only [nodeValue3953, Sparse.eval_nil] using zero3953 B _hB _hF

theorem sound3956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3956 node3956Labels = Sparse.eval nodeValue3956 (mixedVector B) := by
  simpa only [nodeValue3956, Sparse.eval_nil] using zero3956 B _hB _hF

theorem sound3957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3957 node3957Labels = Sparse.eval nodeValue3957 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3957) = mixedMoment B node3957 node3957Labels := rfl
  simpa [nodeValue3957, Sparse.eval] using hc.symm

theorem sound3958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3958 node3958Labels = Sparse.eval nodeValue3958 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3958) = mixedMoment B node3958 node3958Labels := rfl
  simpa [nodeValue3958, Sparse.eval] using hc.symm

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

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

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

theorem sound5064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5064 node5064Labels = Sparse.eval nodeValue5064 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5064) = mixedMoment B node5064 node5064Labels := rfl
  simpa [nodeValue5064, Sparse.eval] using hc.symm

theorem sound5067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5067 node5067Labels = Sparse.eval nodeValue5067 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5067) = mixedMoment B node5067 node5067Labels := rfl
  simpa [nodeValue5067, Sparse.eval] using hc.symm

theorem sound5071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5071 node5071Labels = Sparse.eval nodeValue5071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5071) = mixedMoment B node5071 node5071Labels := rfl
  simpa [nodeValue5071, Sparse.eval] using hc.symm

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

theorem sound5181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5181 node5181Labels = Sparse.eval nodeValue5181 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5181) = mixedMoment B node5181 node5181Labels := rfl
  simpa [nodeValue5181, Sparse.eval] using hc.symm

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

theorem sound5244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5244 node5244Labels = Sparse.eval nodeValue5244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5244) = mixedMoment B node5244 node5244Labels := rfl
  simpa [nodeValue5244, Sparse.eval] using hc.symm

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

theorem sound5282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5282 node5282Labels = Sparse.eval nodeValue5282 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5282) = mixedMoment B node5282 node5282Labels := rfl
  simpa [nodeValue5282, Sparse.eval] using hc.symm

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

theorem sound5348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5348 node5348Labels = Sparse.eval nodeValue5348 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5348) = mixedMoment B node5348 node5348Labels := rfl
  simpa [nodeValue5348, Sparse.eval] using hc.symm

theorem sound5350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5350 node5350Labels = Sparse.eval nodeValue5350 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5350) = mixedMoment B node5350 node5350Labels := rfl
  simpa [nodeValue5350, Sparse.eval] using hc.symm

theorem sound5352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5352 node5352Labels = Sparse.eval nodeValue5352 (mixedVector B) := by
  have h := singleton5352 B _hB
  rw [sound3690 B _hB _hF, sound3764 B _hB _hF] at h
  norm_num [nodeValue5352, nodeValue3690, nodeValue3764, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5405 node5405Labels = Sparse.eval nodeValue5405 (mixedVector B) := by
  have h := singleton5405 B _hB
  rw [sound3800 B _hB _hF, sound3805 B _hB _hF] at h
  norm_num [nodeValue5405, nodeValue3800, nodeValue3805, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5421 node5421Labels = Sparse.eval nodeValue5421 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5421) = mixedMoment B node5421 node5421Labels := rfl
  simpa [nodeValue5421, Sparse.eval] using hc.symm

theorem sound5429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5429 node5429Labels = Sparse.eval nodeValue5429 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5429) = mixedMoment B node5429 node5429Labels := rfl
  simpa [nodeValue5429, Sparse.eval] using hc.symm

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

theorem sound5448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5448 node5448Labels = Sparse.eval nodeValue5448 (mixedVector B) := by
  have h := singleton5448 B _hB
  rw [sound3885 B _hB _hF] at h
  norm_num [nodeValue5448, nodeValue3885, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5470 node5470Labels = Sparse.eval nodeValue5470 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5470) = mixedMoment B node5470 node5470Labels := rfl
  simpa [nodeValue5470, Sparse.eval] using hc.symm

theorem sound5472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5472 node5472Labels = Sparse.eval nodeValue5472 (mixedVector B) := by
  have h := singleton5472 B _hB
  rw [sound3957 B _hB _hF] at h
  norm_num [nodeValue5472, nodeValue3957, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5473 node5473Labels = Sparse.eval nodeValue5473 (mixedVector B) := by
  have h := singleton5473 B _hB
  rw [sound3958 B _hB _hF, sound3961 B _hB _hF] at h
  norm_num [nodeValue5473, nodeValue3958, nodeValue3961, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5480 node5480Labels = Sparse.eval nodeValue5480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5480) = mixedMoment B node5480 node5480Labels := rfl
  simpa [nodeValue5480, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources31
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1018 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1018 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1018 + difference 0 4) (sourceB1018 + difference 4 0) sourceC1018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2882) := by
    have ha : (tripleCharges (sourceA1018 + difference 0 4) (sourceB1018 + difference 4 0) sourceC1018) = raw16597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1018 sourceB1018 sourceC1018 difference raw16597; decide +kernel
    rw [ha]
    exact (canonical16597 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1018 + difference 1 4) (sourceB1018 + difference 4 1) sourceC1018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2871) := by
    have ha : (tripleCharges (sourceA1018 + difference 1 4) (sourceB1018 + difference 4 1) sourceC1018) = raw16599 := by
      apply Matrix.ext; unfold tripleCharges sourceA1018 sourceB1018 sourceC1018 difference raw16599; decide +kernel
    rw [ha]
    exact (canonical16599 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1018 + difference 2 4) (sourceB1018 + difference 4 2) sourceC1018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2869) := by
    have ha : (tripleCharges (sourceA1018 + difference 2 4) (sourceB1018 + difference 4 2) sourceC1018) = raw15746 := by
      apply Matrix.ext; unfold tripleCharges sourceA1018 sourceB1018 sourceC1018 difference raw15746; decide +kernel
    rw [ha]
    exact (canonical15746 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1018 + difference 3 4) (sourceB1018 + difference 4 3) sourceC1018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2873) := by
    have ha : (tripleCharges (sourceA1018 + difference 3 4) (sourceB1018 + difference 4 3) sourceC1018) = raw16600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1018 sourceB1018 sourceC1018 difference raw16600; decide +kernel
    rw [ha]
    exact (canonical16600 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1018 + difference 4 4) (sourceB1018 + difference 4 4) sourceC1018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA1018 + difference 4 4) (sourceB1018 + difference 4 4) sourceC1018) = raw15744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1018 sourceB1018 sourceC1018 difference raw15744; decide +kernel
    rw [ha]
    exact (canonical15744 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1018 + difference 5 4) (sourceB1018 + difference 4 5) sourceC1018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3044) := by
    have ha : (tripleCharges (sourceA1018 + difference 5 4) (sourceB1018 + difference 4 5) sourceC1018) = raw16601 := by
      apply Matrix.ext; unfold tripleCharges sourceA1018 sourceB1018 sourceC1018 difference raw16601; decide +kernel
    rw [ha]
    exact (canonical16601 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1018 + sourceB1018) sourceC1018) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1018 + sourceB1018) sourceC1018) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA1018 sourceB1018 sourceC1018 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1018 sourceB1018 sourceC1018
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1018, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources32
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1025 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1025 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1025 + difference 0 1) (sourceB1025 + difference 1 0) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA1025 + difference 0 1) (sourceB1025 + difference 1 0) sourceC1025) = raw16736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16736; decide +kernel
    rw [ha]
    exact (canonical16736 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1025 + difference 0 2) (sourceB1025 + difference 2 0) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA1025 + difference 0 2) (sourceB1025 + difference 2 0) sourceC1025) = raw16737 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16737; decide +kernel
    rw [ha]
    exact (canonical16737 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1025 + difference 0 3) (sourceB1025 + difference 3 0) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA1025 + difference 0 3) (sourceB1025 + difference 3 0) sourceC1025) = raw16738 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16738; decide +kernel
    rw [ha]
    exact (canonical16738 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1025 + difference 0 4) (sourceB1025 + difference 4 0) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1025 + difference 0 4) (sourceB1025 + difference 4 0) sourceC1025) = raw16739 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16739; decide +kernel
    rw [ha]
    exact (canonical16739 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1025 + difference 0 5) (sourceB1025 + difference 5 0) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1025 + difference 0 5) (sourceB1025 + difference 5 0) sourceC1025) = raw16740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16740; decide +kernel
    rw [ha]
    exact (canonical16740 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1025 + difference 1 0) (sourceB1025 + difference 0 1) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5244) := by
    have ha : (tripleCharges (sourceA1025 + difference 1 0) (sourceB1025 + difference 0 1) sourceC1025) = raw16741 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16741; decide +kernel
    rw [ha]
    exact (canonical16741 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1025 + difference 1 2) (sourceB1025 + difference 2 1) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA1025 + difference 1 2) (sourceB1025 + difference 2 1) sourceC1025) = raw16742 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16742; decide +kernel
    rw [ha]
    exact (canonical16742 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1025 + difference 1 3) (sourceB1025 + difference 3 1) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA1025 + difference 1 3) (sourceB1025 + difference 3 1) sourceC1025) = raw16743 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16743; decide +kernel
    rw [ha]
    exact (canonical16743 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1025 + difference 1 4) (sourceB1025 + difference 4 1) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1025 + difference 1 4) (sourceB1025 + difference 4 1) sourceC1025) = raw16744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16744; decide +kernel
    rw [ha]
    exact (canonical16744 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1025 + difference 1 5) (sourceB1025 + difference 5 1) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1025 + difference 1 5) (sourceB1025 + difference 5 1) sourceC1025) = raw16745 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16745; decide +kernel
    rw [ha]
    exact (canonical16745 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1025 + difference 2 0) (sourceB1025 + difference 0 2) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA1025 + difference 2 0) (sourceB1025 + difference 0 2) sourceC1025) = raw16746 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16746; decide +kernel
    rw [ha]
    exact (canonical16746 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1025 + difference 2 1) (sourceB1025 + difference 1 2) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1025 + difference 2 1) (sourceB1025 + difference 1 2) sourceC1025) = raw16747 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16747; decide +kernel
    rw [ha]
    exact (canonical16747 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1025 + difference 2 3) (sourceB1025 + difference 3 2) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5470) := by
    have ha : (tripleCharges (sourceA1025 + difference 2 3) (sourceB1025 + difference 3 2) sourceC1025) = raw16748 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16748; decide +kernel
    rw [ha]
    exact (canonical16748 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1025 + difference 2 4) (sourceB1025 + difference 4 2) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1025 + difference 2 4) (sourceB1025 + difference 4 2) sourceC1025) = raw16749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16749; decide +kernel
    rw [ha]
    exact (canonical16749 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1025 + difference 2 5) (sourceB1025 + difference 5 2) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA1025 + difference 2 5) (sourceB1025 + difference 5 2) sourceC1025) = raw16750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16750; decide +kernel
    rw [ha]
    exact (canonical16750 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1025 + difference 3 0) (sourceB1025 + difference 0 3) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA1025 + difference 3 0) (sourceB1025 + difference 0 3) sourceC1025) = raw16751 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16751; decide +kernel
    rw [ha]
    exact (canonical16751 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1025 + difference 3 1) (sourceB1025 + difference 1 3) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1025 + difference 3 1) (sourceB1025 + difference 1 3) sourceC1025) = raw16752 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16752; decide +kernel
    rw [ha]
    exact (canonical16752 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1025 + difference 3 2) (sourceB1025 + difference 2 3) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5470) := by
    have ha : (tripleCharges (sourceA1025 + difference 3 2) (sourceB1025 + difference 2 3) sourceC1025) = raw16753 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16753; decide +kernel
    rw [ha]
    exact (canonical16753 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1025 + difference 3 4) (sourceB1025 + difference 4 3) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1025 + difference 3 4) (sourceB1025 + difference 4 3) sourceC1025) = raw16754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16754; decide +kernel
    rw [ha]
    exact (canonical16754 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1025 + difference 3 5) (sourceB1025 + difference 5 3) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA1025 + difference 3 5) (sourceB1025 + difference 5 3) sourceC1025) = raw16755 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16755; decide +kernel
    rw [ha]
    exact (canonical16755 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1025 + difference 4 0) (sourceB1025 + difference 0 4) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5181) := by
    have ha : (tripleCharges (sourceA1025 + difference 4 0) (sourceB1025 + difference 0 4) sourceC1025) = raw16756 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16756; decide +kernel
    rw [ha]
    exact (canonical16756 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1025 + difference 4 1) (sourceB1025 + difference 1 4) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5348) := by
    have ha : (tripleCharges (sourceA1025 + difference 4 1) (sourceB1025 + difference 1 4) sourceC1025) = raw16757 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16757; decide +kernel
    rw [ha]
    exact (canonical16757 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1025 + difference 4 2) (sourceB1025 + difference 2 4) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5350) := by
    have ha : (tripleCharges (sourceA1025 + difference 4 2) (sourceB1025 + difference 2 4) sourceC1025) = raw16758 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16758; decide +kernel
    rw [ha]
    exact (canonical16758 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1025 + difference 4 3) (sourceB1025 + difference 3 4) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5350) := by
    have ha : (tripleCharges (sourceA1025 + difference 4 3) (sourceB1025 + difference 3 4) sourceC1025) = raw16759 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16759; decide +kernel
    rw [ha]
    exact (canonical16759 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1025 + difference 4 5) (sourceB1025 + difference 5 4) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1025 + difference 4 5) (sourceB1025 + difference 5 4) sourceC1025) = raw16760 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16760; decide +kernel
    rw [ha]
    exact (canonical16760 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1025 + difference 5 0) (sourceB1025 + difference 0 5) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5064) := by
    have ha : (tripleCharges (sourceA1025 + difference 5 0) (sourceB1025 + difference 0 5) sourceC1025) = raw16761 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16761; decide +kernel
    rw [ha]
    exact (canonical16761 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1025 + difference 5 1) (sourceB1025 + difference 1 5) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5067) := by
    have ha : (tripleCharges (sourceA1025 + difference 5 1) (sourceB1025 + difference 1 5) sourceC1025) = raw16762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16762; decide +kernel
    rw [ha]
    exact (canonical16762 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1025 + difference 5 2) (sourceB1025 + difference 2 5) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5071) := by
    have ha : (tripleCharges (sourceA1025 + difference 5 2) (sourceB1025 + difference 2 5) sourceC1025) = raw16763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16763; decide +kernel
    rw [ha]
    exact (canonical16763 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1025 + difference 5 3) (sourceB1025 + difference 3 5) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5071) := by
    have ha : (tripleCharges (sourceA1025 + difference 5 3) (sourceB1025 + difference 3 5) sourceC1025) = raw16764 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16764; decide +kernel
    rw [ha]
    exact (canonical16764 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1025 + difference 5 4) (sourceB1025 + difference 4 5) sourceC1025) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA1025 + difference 5 4) (sourceB1025 + difference 4 5) sourceC1025) = raw16765 := by
      apply Matrix.ext; unfold tripleCharges sourceA1025 sourceB1025 sourceC1025 difference raw16765; decide +kernel
    rw [ha]
    exact (canonical16765 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1025 sourceB1025 sourceC1025
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1025, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1029 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1029 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1029 + difference 0 1) (sourceB1029 + difference 1 0) sourceC1029) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA1029 + difference 0 1) (sourceB1029 + difference 1 0) sourceC1029) = raw16833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1029 sourceB1029 sourceC1029 difference raw16833; decide +kernel
    rw [ha]
    exact (canonical16833 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1029 + difference 1 1) (sourceB1029 + difference 1 1) sourceC1029) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3953) := by
    have ha : (tripleCharges (sourceA1029 + difference 1 1) (sourceB1029 + difference 1 1) sourceC1029) = raw16826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1029 sourceB1029 sourceC1029 difference raw16826; decide +kernel
    rw [ha]
    exact (canonical16826 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1029 + difference 2 1) (sourceB1029 + difference 1 2) sourceC1029) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA1029 + difference 2 1) (sourceB1029 + difference 1 2) sourceC1029) = raw16834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1029 sourceB1029 sourceC1029 difference raw16834; decide +kernel
    rw [ha]
    exact (canonical16834 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1029 + difference 3 1) (sourceB1029 + difference 1 3) sourceC1029) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA1029 + difference 3 1) (sourceB1029 + difference 1 3) sourceC1029) = raw16835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1029 sourceB1029 sourceC1029 difference raw16835; decide +kernel
    rw [ha]
    exact (canonical16835 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1029 + difference 4 1) (sourceB1029 + difference 1 4) sourceC1029) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3685) := by
    have ha : (tripleCharges (sourceA1029 + difference 4 1) (sourceB1029 + difference 1 4) sourceC1029) = raw16836 := by
      apply Matrix.ext; unfold tripleCharges sourceA1029 sourceB1029 sourceC1029 difference raw16836; decide +kernel
    rw [ha]
    exact (canonical16836 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1029 + difference 5 1) (sourceB1029 + difference 1 5) sourceC1029) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2981) := by
    have ha : (tripleCharges (sourceA1029 + difference 5 1) (sourceB1029 + difference 1 5) sourceC1029) = raw16837 := by
      apply Matrix.ext; unfold tripleCharges sourceA1029 sourceB1029 sourceC1029 difference raw16837; decide +kernel
    rw [ha]
    exact (canonical16837 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1029 + sourceB1029) sourceC1029) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1029 + sourceB1029) sourceC1029) = raw16832 := by
      apply Matrix.ext; unfold doubleCharges sourceA1029 sourceB1029 sourceC1029 raw16832; decide +kernel
    rw [ha]
    exact (canonical16832 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1029 sourceB1029 sourceC1029
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1029, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1032 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1032 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1032 + difference 0 1) (sourceB1032 + difference 1 0) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2728) := by
    have ha : (tripleCharges (sourceA1032 + difference 0 1) (sourceB1032 + difference 1 0) sourceC1032) = raw16891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16891; decide +kernel
    rw [ha]
    exact (canonical16891 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1032 + difference 0 2) (sourceB1032 + difference 2 0) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA1032 + difference 0 2) (sourceB1032 + difference 2 0) sourceC1032) = raw16892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16892; decide +kernel
    rw [ha]
    exact (canonical16892 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1032 + difference 0 3) (sourceB1032 + difference 3 0) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA1032 + difference 0 3) (sourceB1032 + difference 3 0) sourceC1032) = raw16893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16893; decide +kernel
    rw [ha]
    exact (canonical16893 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1032 + difference 0 4) (sourceB1032 + difference 4 0) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3869) := by
    have ha : (tripleCharges (sourceA1032 + difference 0 4) (sourceB1032 + difference 4 0) sourceC1032) = raw16894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16894; decide +kernel
    rw [ha]
    exact (canonical16894 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1032 + difference 0 5) (sourceB1032 + difference 5 0) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA1032 + difference 0 5) (sourceB1032 + difference 5 0) sourceC1032) = raw16895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16895; decide +kernel
    rw [ha]
    exact (canonical16895 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1032 + difference 1 0) (sourceB1032 + difference 0 1) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3977) := by
    have ha : (tripleCharges (sourceA1032 + difference 1 0) (sourceB1032 + difference 0 1) sourceC1032) = raw15151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw15151; decide +kernel
    rw [ha]
    exact (canonical15151 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1032 + difference 1 2) (sourceB1032 + difference 2 1) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1032 + difference 1 2) (sourceB1032 + difference 2 1) sourceC1032) = raw15140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw15140; decide +kernel
    rw [ha]
    exact (canonical15140 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1032 + difference 1 3) (sourceB1032 + difference 3 1) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1032 + difference 1 3) (sourceB1032 + difference 3 1) sourceC1032) = raw16896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16896; decide +kernel
    rw [ha]
    exact (canonical16896 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1032 + difference 1 4) (sourceB1032 + difference 4 1) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3953) := by
    have ha : (tripleCharges (sourceA1032 + difference 1 4) (sourceB1032 + difference 4 1) sourceC1032) = raw15715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw15715; decide +kernel
    rw [ha]
    exact (canonical15715 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1032 + difference 1 5) (sourceB1032 + difference 5 1) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA1032 + difference 1 5) (sourceB1032 + difference 5 1) sourceC1032) = raw15892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw15892; decide +kernel
    rw [ha]
    exact (canonical15892 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1032 + difference 2 0) (sourceB1032 + difference 0 2) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3783) := by
    have ha : (tripleCharges (sourceA1032 + difference 2 0) (sourceB1032 + difference 0 2) sourceC1032) = raw16897 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16897; decide +kernel
    rw [ha]
    exact (canonical16897 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1032 + difference 2 1) (sourceB1032 + difference 1 2) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2613) := by
    have ha : (tripleCharges (sourceA1032 + difference 2 1) (sourceB1032 + difference 1 2) sourceC1032) = raw16898 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16898; decide +kernel
    rw [ha]
    exact (canonical16898 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1032 + difference 2 3) (sourceB1032 + difference 3 2) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA1032 + difference 2 3) (sourceB1032 + difference 3 2) sourceC1032) = raw16899 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16899; decide +kernel
    rw [ha]
    exact (canonical16899 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1032 + difference 2 4) (sourceB1032 + difference 4 2) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3785) := by
    have ha : (tripleCharges (sourceA1032 + difference 2 4) (sourceB1032 + difference 4 2) sourceC1032) = raw16900 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16900; decide +kernel
    rw [ha]
    exact (canonical16900 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1032 + difference 2 5) (sourceB1032 + difference 5 2) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3802) := by
    have ha : (tripleCharges (sourceA1032 + difference 2 5) (sourceB1032 + difference 5 2) sourceC1032) = raw16901 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16901; decide +kernel
    rw [ha]
    exact (canonical16901 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1032 + difference 3 0) (sourceB1032 + difference 0 3) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3783) := by
    have ha : (tripleCharges (sourceA1032 + difference 3 0) (sourceB1032 + difference 0 3) sourceC1032) = raw16902 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16902; decide +kernel
    rw [ha]
    exact (canonical16902 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1032 + difference 3 1) (sourceB1032 + difference 1 3) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2613) := by
    have ha : (tripleCharges (sourceA1032 + difference 3 1) (sourceB1032 + difference 1 3) sourceC1032) = raw16903 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16903; decide +kernel
    rw [ha]
    exact (canonical16903 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1032 + difference 3 2) (sourceB1032 + difference 2 3) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA1032 + difference 3 2) (sourceB1032 + difference 2 3) sourceC1032) = raw16904 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16904; decide +kernel
    rw [ha]
    exact (canonical16904 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1032 + difference 3 4) (sourceB1032 + difference 4 3) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3785) := by
    have ha : (tripleCharges (sourceA1032 + difference 3 4) (sourceB1032 + difference 4 3) sourceC1032) = raw16905 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16905; decide +kernel
    rw [ha]
    exact (canonical16905 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1032 + difference 3 5) (sourceB1032 + difference 5 3) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3802) := by
    have ha : (tripleCharges (sourceA1032 + difference 3 5) (sourceB1032 + difference 5 3) sourceC1032) = raw16906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16906; decide +kernel
    rw [ha]
    exact (canonical16906 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1032 + difference 4 0) (sourceB1032 + difference 0 4) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3938) := by
    have ha : (tripleCharges (sourceA1032 + difference 4 0) (sourceB1032 + difference 0 4) sourceC1032) = raw16907 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16907; decide +kernel
    rw [ha]
    exact (canonical16907 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1032 + difference 4 1) (sourceB1032 + difference 1 4) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2631) := by
    have ha : (tripleCharges (sourceA1032 + difference 4 1) (sourceB1032 + difference 1 4) sourceC1032) = raw16908 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16908; decide +kernel
    rw [ha]
    exact (canonical16908 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1032 + difference 4 2) (sourceB1032 + difference 2 4) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA1032 + difference 4 2) (sourceB1032 + difference 2 4) sourceC1032) = raw16909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16909; decide +kernel
    rw [ha]
    exact (canonical16909 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1032 + difference 4 3) (sourceB1032 + difference 3 4) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA1032 + difference 4 3) (sourceB1032 + difference 3 4) sourceC1032) = raw16910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16910; decide +kernel
    rw [ha]
    exact (canonical16910 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1032 + difference 4 5) (sourceB1032 + difference 5 4) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA1032 + difference 4 5) (sourceB1032 + difference 5 4) sourceC1032) = raw16911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16911; decide +kernel
    rw [ha]
    exact (canonical16911 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1032 + difference 5 0) (sourceB1032 + difference 0 5) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3937) := by
    have ha : (tripleCharges (sourceA1032 + difference 5 0) (sourceB1032 + difference 0 5) sourceC1032) = raw16912 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16912; decide +kernel
    rw [ha]
    exact (canonical16912 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1032 + difference 5 1) (sourceB1032 + difference 1 5) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2617) := by
    have ha : (tripleCharges (sourceA1032 + difference 5 1) (sourceB1032 + difference 1 5) sourceC1032) = raw16913 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16913; decide +kernel
    rw [ha]
    exact (canonical16913 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1032 + difference 5 2) (sourceB1032 + difference 2 5) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4003) := by
    have ha : (tripleCharges (sourceA1032 + difference 5 2) (sourceB1032 + difference 2 5) sourceC1032) = raw16914 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16914; decide +kernel
    rw [ha]
    exact (canonical16914 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1032 + difference 5 3) (sourceB1032 + difference 3 5) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4003) := by
    have ha : (tripleCharges (sourceA1032 + difference 5 3) (sourceB1032 + difference 3 5) sourceC1032) = raw16915 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16915; decide +kernel
    rw [ha]
    exact (canonical16915 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1032 + difference 5 4) (sourceB1032 + difference 4 5) sourceC1032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3949) := by
    have ha : (tripleCharges (sourceA1032 + difference 5 4) (sourceB1032 + difference 4 5) sourceC1032) = raw16916 := by
      apply Matrix.ext; unfold tripleCharges sourceA1032 sourceB1032 sourceC1032 difference raw16916; decide +kernel
    rw [ha]
    exact (canonical16916 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1032 sourceB1032 sourceC1032
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1032, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1033 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1033 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1033 + difference 0 0) (sourceB1033 + difference 0 0) sourceC1033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3956) := by
    have ha : (tripleCharges (sourceA1033 + difference 0 0) (sourceB1033 + difference 0 0) sourceC1033) = raw16917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1033 sourceB1033 sourceC1033 difference raw16917; decide +kernel
    rw [ha]
    exact (canonical16917 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1033 + difference 1 0) (sourceB1033 + difference 0 1) sourceC1033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA1033 + difference 1 0) (sourceB1033 + difference 0 1) sourceC1033) = raw15750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1033 sourceB1033 sourceC1033 difference raw15750; decide +kernel
    rw [ha]
    exact (canonical15750 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1033 + difference 2 0) (sourceB1033 + difference 0 2) sourceC1033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3691) := by
    have ha : (tripleCharges (sourceA1033 + difference 2 0) (sourceB1033 + difference 0 2) sourceC1033) = raw16918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1033 sourceB1033 sourceC1033 difference raw16918; decide +kernel
    rw [ha]
    exact (canonical16918 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1033 + difference 3 0) (sourceB1033 + difference 0 3) sourceC1033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3691) := by
    have ha : (tripleCharges (sourceA1033 + difference 3 0) (sourceB1033 + difference 0 3) sourceC1033) = raw16919 := by
      apply Matrix.ext; unfold tripleCharges sourceA1033 sourceB1033 sourceC1033 difference raw16919; decide +kernel
    rw [ha]
    exact (canonical16919 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1033 + difference 4 0) (sourceB1033 + difference 0 4) sourceC1033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3703) := by
    have ha : (tripleCharges (sourceA1033 + difference 4 0) (sourceB1033 + difference 0 4) sourceC1033) = raw16920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1033 sourceB1033 sourceC1033 difference raw16920; decide +kernel
    rw [ha]
    exact (canonical16920 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1033 + difference 5 0) (sourceB1033 + difference 0 5) sourceC1033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3689) := by
    have ha : (tripleCharges (sourceA1033 + difference 5 0) (sourceB1033 + difference 0 5) sourceC1033) = raw16921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1033 sourceB1033 sourceC1033 difference raw16921; decide +kernel
    rw [ha]
    exact (canonical16921 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1033 + sourceB1033) sourceC1033) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1033 + sourceB1033) sourceC1033) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA1033 sourceB1033 sourceC1033 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1033 sourceB1033 sourceC1033
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1033, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1039 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1039 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1039 + difference 0 2) (sourceB1039 + difference 2 0) sourceC1039) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3909) := by
    have ha : (tripleCharges (sourceA1039 + difference 0 2) (sourceB1039 + difference 2 0) sourceC1039) = raw17024 := by
      apply Matrix.ext; unfold tripleCharges sourceA1039 sourceB1039 sourceC1039 difference raw17024; decide +kernel
    rw [ha]
    exact (canonical17024 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1039 + difference 1 2) (sourceB1039 + difference 2 1) sourceC1039) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA1039 + difference 1 2) (sourceB1039 + difference 2 1) sourceC1039) = raw17025 := by
      apply Matrix.ext; unfold tripleCharges sourceA1039 sourceB1039 sourceC1039 difference raw17025; decide +kernel
    rw [ha]
    exact (canonical17025 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1039 + difference 2 2) (sourceB1039 + difference 2 2) sourceC1039) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA1039 + difference 2 2) (sourceB1039 + difference 2 2) sourceC1039) = raw17017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1039 sourceB1039 sourceC1039 difference raw17017; decide +kernel
    rw [ha]
    exact (canonical17017 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1039 + difference 3 2) (sourceB1039 + difference 2 3) sourceC1039) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3945) := by
    have ha : (tripleCharges (sourceA1039 + difference 3 2) (sourceB1039 + difference 2 3) sourceC1039) = raw17026 := by
      apply Matrix.ext; unfold tripleCharges sourceA1039 sourceB1039 sourceC1039 difference raw17026; decide +kernel
    rw [ha]
    exact (canonical17026 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1039 + difference 4 2) (sourceB1039 + difference 2 4) sourceC1039) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3878) := by
    have ha : (tripleCharges (sourceA1039 + difference 4 2) (sourceB1039 + difference 2 4) sourceC1039) = raw17027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1039 sourceB1039 sourceC1039 difference raw17027; decide +kernel
    rw [ha]
    exact (canonical17027 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1039 + difference 5 2) (sourceB1039 + difference 2 5) sourceC1039) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2976) := by
    have ha : (tripleCharges (sourceA1039 + difference 5 2) (sourceB1039 + difference 2 5) sourceC1039) = raw17028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1039 sourceB1039 sourceC1039 difference raw17028; decide +kernel
    rw [ha]
    exact (canonical17028 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1039 + sourceB1039) sourceC1039) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1039 + sourceB1039) sourceC1039) = raw17023 := by
      apply Matrix.ext; unfold doubleCharges sourceA1039 sourceB1039 sourceC1039 raw17023; decide +kernel
    rw [ha]
    exact (canonical17023 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1039 sourceB1039 sourceC1039
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1039, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck880 : Integer.Sparse.reindex keyMap MixedData.row880 = numericRow880 := by decide +kernel

theorem numericCheck880 (x : Master → ℝ) : Integer.Sparse.eval numericRow880 x =
    (1 : ℝ) * reducedSource880 x := by
  norm_num [numericRow880, reducedSource880, Integer.Sparse.eval, Sparse.eval, nodeValue2869, nodeValue2871, nodeValue2873, nodeValue2882, nodeValue3044, nodeValue3884, nodeValue4092]

theorem reindexCheck886 : Integer.Sparse.reindex keyMap MixedData.row886 = numericRow886 := by decide +kernel

theorem numericCheck886 (x : Master → ℝ) : Integer.Sparse.eval numericRow886 x =
    (1440 : ℝ) * reducedSource886 x := by
  norm_num [numericRow886, reducedSource886, Integer.Sparse.eval, Sparse.eval, nodeValue5064, nodeValue5067, nodeValue5071, nodeValue5181, nodeValue5185, nodeValue5244, nodeValue5282, nodeValue5348, nodeValue5350, nodeValue5352, nodeValue5405, nodeValue5421, nodeValue5429, nodeValue5431, nodeValue5448, nodeValue5470, nodeValue5472, nodeValue5473, nodeValue5480, nodeValue5482, nodeValue5485]
  ring

theorem reindexCheck889 : Integer.Sparse.reindex keyMap MixedData.row889 = numericRow889 := by decide +kernel

theorem numericCheck889 (x : Master → ℝ) : Integer.Sparse.eval numericRow889 x =
    (1 : ℝ) * reducedSource889 x := by
  norm_num [numericRow889, reducedSource889, Integer.Sparse.eval, Sparse.eval, nodeValue2981, nodeValue3685, nodeValue3690, nodeValue3800, nodeValue3953, nodeValue4091]

theorem reindexCheck892 : Integer.Sparse.reindex keyMap MixedData.row892 = numericRow892 := by decide +kernel

theorem numericCheck892 (x : Master → ℝ) : Integer.Sparse.eval numericRow892 x =
    (25920 : ℝ) * reducedSource892 x := by
  norm_num [numericRow892, reducedSource892, Integer.Sparse.eval, Sparse.eval, nodeValue2613, nodeValue2617, nodeValue2631, nodeValue2728, nodeValue3783, nodeValue3785, nodeValue3799, nodeValue3800, nodeValue3802, nodeValue3846, nodeValue3869, nodeValue3876, nodeValue3881, nodeValue3937, nodeValue3938, nodeValue3949, nodeValue3953, nodeValue3977, nodeValue3981, nodeValue3995, nodeValue4003]
  ring

theorem reindexCheck893 : Integer.Sparse.reindex keyMap MixedData.row893 = numericRow893 := by decide +kernel

theorem numericCheck893 (x : Master → ℝ) : Integer.Sparse.eval numericRow893 x =
    (1 : ℝ) * reducedSource893 x := by
  norm_num [numericRow893, reducedSource893, Integer.Sparse.eval, Sparse.eval, nodeValue3689, nodeValue3691, nodeValue3703, nodeValue3805, nodeValue3956, nodeValue4092]

theorem reindexCheck895 : Integer.Sparse.reindex keyMap MixedData.row895 = numericRow895 := by decide +kernel

theorem numericCheck895 (x : Master → ℝ) : Integer.Sparse.eval numericRow895 x =
    (1 : ℝ) * reducedSource895 x := by
  norm_num [numericRow895, reducedSource895, Integer.Sparse.eval, Sparse.eval, nodeValue2976, nodeValue3878, nodeValue3880, nodeValue3909, nodeValue3945, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero880 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource880 (mixedVector B) = 0 := by
  have h2869 : mixedVector B (Sum.inr 2869) = Sparse.eval nodeValue2869 (mixedVector B) := by
    change mixedMoment B node2869 node2869Labels = _
    exact sound2869 B hB hF
  have h2871 : mixedVector B (Sum.inr 2871) = Sparse.eval nodeValue2871 (mixedVector B) := by
    change mixedMoment B node2871 node2871Labels = _
    exact sound2871 B hB hF
  have h2873 : mixedVector B (Sum.inr 2873) = Sparse.eval nodeValue2873 (mixedVector B) := by
    change mixedMoment B node2873 node2873Labels = _
    exact sound2873 B hB hF
  have h2882 : mixedVector B (Sum.inr 2882) = Sparse.eval nodeValue2882 (mixedVector B) := by
    change mixedMoment B node2882 node2882Labels = _
    exact sound2882 B hB hF
  have h3044 : mixedVector B (Sum.inr 3044) = Sparse.eval nodeValue3044 (mixedVector B) := by
    change mixedMoment B node3044 node3044Labels = _
    exact sound3044 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1018, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2869, h2871, h2873, h2882, h3044, h3884, h4092, reducedSource880] using sourceEq1018 B hB

theorem rowSound880 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row880 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck880, numericCheck880, reducedZero880 B hB hF, mul_zero]

theorem reducedZero886 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource886 (mixedVector B) = 0 := by
  have h5064 : mixedVector B (Sum.inr 5064) = Sparse.eval nodeValue5064 (mixedVector B) := by
    change mixedMoment B node5064 node5064Labels = _
    exact sound5064 B hB hF
  have h5067 : mixedVector B (Sum.inr 5067) = Sparse.eval nodeValue5067 (mixedVector B) := by
    change mixedMoment B node5067 node5067Labels = _
    exact sound5067 B hB hF
  have h5071 : mixedVector B (Sum.inr 5071) = Sparse.eval nodeValue5071 (mixedVector B) := by
    change mixedMoment B node5071 node5071Labels = _
    exact sound5071 B hB hF
  have h5181 : mixedVector B (Sum.inr 5181) = Sparse.eval nodeValue5181 (mixedVector B) := by
    change mixedMoment B node5181 node5181Labels = _
    exact sound5181 B hB hF
  have h5185 : mixedVector B (Sum.inr 5185) = Sparse.eval nodeValue5185 (mixedVector B) := by
    change mixedMoment B node5185 node5185Labels = _
    exact sound5185 B hB hF
  have h5244 : mixedVector B (Sum.inr 5244) = Sparse.eval nodeValue5244 (mixedVector B) := by
    change mixedMoment B node5244 node5244Labels = _
    exact sound5244 B hB hF
  have h5282 : mixedVector B (Sum.inr 5282) = Sparse.eval nodeValue5282 (mixedVector B) := by
    change mixedMoment B node5282 node5282Labels = _
    exact sound5282 B hB hF
  have h5348 : mixedVector B (Sum.inr 5348) = Sparse.eval nodeValue5348 (mixedVector B) := by
    change mixedMoment B node5348 node5348Labels = _
    exact sound5348 B hB hF
  have h5350 : mixedVector B (Sum.inr 5350) = Sparse.eval nodeValue5350 (mixedVector B) := by
    change mixedMoment B node5350 node5350Labels = _
    exact sound5350 B hB hF
  have h5352 : mixedVector B (Sum.inr 5352) = Sparse.eval nodeValue5352 (mixedVector B) := by
    change mixedMoment B node5352 node5352Labels = _
    exact sound5352 B hB hF
  have h5405 : mixedVector B (Sum.inr 5405) = Sparse.eval nodeValue5405 (mixedVector B) := by
    change mixedMoment B node5405 node5405Labels = _
    exact sound5405 B hB hF
  have h5421 : mixedVector B (Sum.inr 5421) = Sparse.eval nodeValue5421 (mixedVector B) := by
    change mixedMoment B node5421 node5421Labels = _
    exact sound5421 B hB hF
  have h5429 : mixedVector B (Sum.inr 5429) = Sparse.eval nodeValue5429 (mixedVector B) := by
    change mixedMoment B node5429 node5429Labels = _
    exact sound5429 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5448 : mixedVector B (Sum.inr 5448) = Sparse.eval nodeValue5448 (mixedVector B) := by
    change mixedMoment B node5448 node5448Labels = _
    exact sound5448 B hB hF
  have h5470 : mixedVector B (Sum.inr 5470) = Sparse.eval nodeValue5470 (mixedVector B) := by
    change mixedMoment B node5470 node5470Labels = _
    exact sound5470 B hB hF
  have h5472 : mixedVector B (Sum.inr 5472) = Sparse.eval nodeValue5472 (mixedVector B) := by
    change mixedMoment B node5472 node5472Labels = _
    exact sound5472 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  have h5480 : mixedVector B (Sum.inr 5480) = Sparse.eval nodeValue5480 (mixedVector B) := by
    change mixedMoment B node5480 node5480Labels = _
    exact sound5480 B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482_e B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485_e B hB hF
  simpa only [sourceForm1025, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5064, h5067, h5071, h5181, h5185, h5244, h5282, h5348, h5350, h5352, h5405, h5421, h5429, h5431, h5448, h5470, h5472, h5473, h5480, h5482, h5485, reducedSource886] using sourceEq1025 B hB

theorem rowSound886 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row886 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck886, numericCheck886, reducedZero886 B hB hF, mul_zero]

theorem reducedZero889 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource889 (mixedVector B) = 0 := by
  have h2981 : mixedVector B (Sum.inr 2981) = Sparse.eval nodeValue2981 (mixedVector B) := by
    change mixedMoment B node2981 node2981Labels = _
    exact sound2981 B hB hF
  have h3685 : mixedVector B (Sum.inr 3685) = Sparse.eval nodeValue3685 (mixedVector B) := by
    change mixedMoment B node3685 node3685Labels = _
    exact sound3685 B hB hF
  have h3690 : mixedVector B (Sum.inr 3690) = Sparse.eval nodeValue3690 (mixedVector B) := by
    change mixedMoment B node3690 node3690Labels = _
    exact sound3690 B hB hF
  have h3800 : mixedVector B (Sum.inr 3800) = Sparse.eval nodeValue3800 (mixedVector B) := by
    change mixedMoment B node3800 node3800Labels = _
    exact sound3800 B hB hF
  have h3953 : mixedVector B (Sum.inr 3953) = Sparse.eval nodeValue3953 (mixedVector B) := by
    change mixedMoment B node3953 node3953Labels = _
    exact sound3953 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1029, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2981, h3685, h3690, h3800, h3953, h4091, reducedSource889] using sourceEq1029 B hB

theorem rowSound889 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row889 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck889, numericCheck889, reducedZero889 B hB hF, mul_zero]

theorem reducedZero892 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource892 (mixedVector B) = 0 := by
  have h2613 : mixedVector B (Sum.inr 2613) = Sparse.eval nodeValue2613 (mixedVector B) := by
    change mixedMoment B node2613 node2613Labels = _
    exact sound2613 B hB hF
  have h2617 : mixedVector B (Sum.inr 2617) = Sparse.eval nodeValue2617 (mixedVector B) := by
    change mixedMoment B node2617 node2617Labels = _
    exact sound2617 B hB hF
  have h2631 : mixedVector B (Sum.inr 2631) = Sparse.eval nodeValue2631 (mixedVector B) := by
    change mixedMoment B node2631 node2631Labels = _
    exact sound2631 B hB hF
  have h2728 : mixedVector B (Sum.inr 2728) = Sparse.eval nodeValue2728 (mixedVector B) := by
    change mixedMoment B node2728 node2728Labels = _
    exact sound2728 B hB hF
  have h3783 : mixedVector B (Sum.inr 3783) = Sparse.eval nodeValue3783 (mixedVector B) := by
    change mixedMoment B node3783 node3783Labels = _
    exact sound3783 B hB hF
  have h3785 : mixedVector B (Sum.inr 3785) = Sparse.eval nodeValue3785 (mixedVector B) := by
    change mixedMoment B node3785 node3785Labels = _
    exact sound3785 B hB hF
  have h3799 : mixedVector B (Sum.inr 3799) = Sparse.eval nodeValue3799 (mixedVector B) := by
    change mixedMoment B node3799 node3799Labels = _
    exact sound3799 B hB hF
  have h3800 : mixedVector B (Sum.inr 3800) = Sparse.eval nodeValue3800 (mixedVector B) := by
    change mixedMoment B node3800 node3800Labels = _
    exact sound3800 B hB hF
  have h3802 : mixedVector B (Sum.inr 3802) = Sparse.eval nodeValue3802 (mixedVector B) := by
    change mixedMoment B node3802 node3802Labels = _
    exact sound3802 B hB hF
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h3869 : mixedVector B (Sum.inr 3869) = Sparse.eval nodeValue3869 (mixedVector B) := by
    change mixedMoment B node3869 node3869Labels = _
    exact sound3869 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h3881 : mixedVector B (Sum.inr 3881) = Sparse.eval nodeValue3881 (mixedVector B) := by
    change mixedMoment B node3881 node3881Labels = _
    exact sound3881 B hB hF
  have h3937 : mixedVector B (Sum.inr 3937) = Sparse.eval nodeValue3937 (mixedVector B) := by
    change mixedMoment B node3937 node3937Labels = _
    exact sound3937_e B hB hF
  have h3938 : mixedVector B (Sum.inr 3938) = Sparse.eval nodeValue3938 (mixedVector B) := by
    change mixedMoment B node3938 node3938Labels = _
    exact sound3938_e B hB hF
  have h3949 : mixedVector B (Sum.inr 3949) = Sparse.eval nodeValue3949 (mixedVector B) := by
    change mixedMoment B node3949 node3949Labels = _
    exact sound3949 B hB hF
  have h3953 : mixedVector B (Sum.inr 3953) = Sparse.eval nodeValue3953 (mixedVector B) := by
    change mixedMoment B node3953 node3953Labels = _
    exact sound3953 B hB hF
  have h3977 : mixedVector B (Sum.inr 3977) = Sparse.eval nodeValue3977 (mixedVector B) := by
    change mixedMoment B node3977 node3977Labels = _
    exact sound3977_e B hB hF
  have h3981 : mixedVector B (Sum.inr 3981) = Sparse.eval nodeValue3981 (mixedVector B) := by
    change mixedMoment B node3981 node3981Labels = _
    exact sound3981_e B hB hF
  have h3995 : mixedVector B (Sum.inr 3995) = Sparse.eval nodeValue3995 (mixedVector B) := by
    change mixedMoment B node3995 node3995Labels = _
    exact sound3995_e B hB hF
  have h4003 : mixedVector B (Sum.inr 4003) = Sparse.eval nodeValue4003 (mixedVector B) := by
    change mixedMoment B node4003 node4003Labels = _
    exact sound4003_e B hB hF
  simpa only [sourceForm1032, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2613, h2617, h2631, h2728, h3783, h3785, h3799, h3800, h3802, h3846, h3869, h3876, h3881, h3937, h3938, h3949, h3953, h3977, h3981, h3995, h4003, reducedSource892] using sourceEq1032 B hB

theorem rowSound892 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row892 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck892, numericCheck892, reducedZero892 B hB hF, mul_zero]

theorem reducedZero893 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource893 (mixedVector B) = 0 := by
  have h3689 : mixedVector B (Sum.inr 3689) = Sparse.eval nodeValue3689 (mixedVector B) := by
    change mixedMoment B node3689 node3689Labels = _
    exact sound3689 B hB hF
  have h3691 : mixedVector B (Sum.inr 3691) = Sparse.eval nodeValue3691 (mixedVector B) := by
    change mixedMoment B node3691 node3691Labels = _
    exact sound3691 B hB hF
  have h3703 : mixedVector B (Sum.inr 3703) = Sparse.eval nodeValue3703 (mixedVector B) := by
    change mixedMoment B node3703 node3703Labels = _
    exact sound3703 B hB hF
  have h3805 : mixedVector B (Sum.inr 3805) = Sparse.eval nodeValue3805 (mixedVector B) := by
    change mixedMoment B node3805 node3805Labels = _
    exact sound3805 B hB hF
  have h3956 : mixedVector B (Sum.inr 3956) = Sparse.eval nodeValue3956 (mixedVector B) := by
    change mixedMoment B node3956 node3956Labels = _
    exact sound3956 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1033, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3689, h3691, h3703, h3805, h3956, h4092, reducedSource893] using sourceEq1033 B hB

theorem rowSound893 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row893 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck893, numericCheck893, reducedZero893 B hB hF, mul_zero]

theorem reducedZero895 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource895 (mixedVector B) = 0 := by
  have h2976 : mixedVector B (Sum.inr 2976) = Sparse.eval nodeValue2976 (mixedVector B) := by
    change mixedMoment B node2976 node2976Labels = _
    exact sound2976 B hB hF
  have h3878 : mixedVector B (Sum.inr 3878) = Sparse.eval nodeValue3878 (mixedVector B) := by
    change mixedMoment B node3878 node3878Labels = _
    exact sound3878 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h3909 : mixedVector B (Sum.inr 3909) = Sparse.eval nodeValue3909 (mixedVector B) := by
    change mixedMoment B node3909 node3909Labels = _
    exact sound3909 B hB hF
  have h3945 : mixedVector B (Sum.inr 3945) = Sparse.eval nodeValue3945 (mixedVector B) := by
    change mixedMoment B node3945 node3945Labels = _
    exact sound3945 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1039, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2976, h3878, h3880, h3909, h3945, h4091, reducedSource895] using sourceEq1039 B hB

theorem rowSound895 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row895 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck895, numericCheck895, reducedZero895 B hB hF, mul_zero]

theorem sourceRowsAt880 : MixedData.sourceRows (880 : Fin 2425) =
    MixedData.row880 := by decide +kernel

theorem sourceRowsAt881 : MixedData.sourceRows (881 : Fin 2425) =
    MixedData.row881 := by decide +kernel

theorem sourceRowsAt882 : MixedData.sourceRows (882 : Fin 2425) =
    MixedData.row882 := by decide +kernel

theorem sourceRowsAt883 : MixedData.sourceRows (883 : Fin 2425) =
    MixedData.row883 := by decide +kernel

theorem sourceRowsAt884 : MixedData.sourceRows (884 : Fin 2425) =
    MixedData.row884 := by decide +kernel

theorem sourceRowsAt885 : MixedData.sourceRows (885 : Fin 2425) =
    MixedData.row885 := by decide +kernel

theorem sourceRowsAt886 : MixedData.sourceRows (886 : Fin 2425) =
    MixedData.row886 := by decide +kernel

theorem sourceRowsAt887 : MixedData.sourceRows (887 : Fin 2425) =
    MixedData.row887 := by decide +kernel

theorem sourceRowsAt888 : MixedData.sourceRows (888 : Fin 2425) =
    MixedData.row888 := by decide +kernel

theorem sourceRowsAt889 : MixedData.sourceRows (889 : Fin 2425) =
    MixedData.row889 := by decide +kernel

theorem sourceRowsAt890 : MixedData.sourceRows (890 : Fin 2425) =
    MixedData.row890 := by decide +kernel

theorem sourceRowsAt891 : MixedData.sourceRows (891 : Fin 2425) =
    MixedData.row891 := by decide +kernel

theorem sourceRowsAt892 : MixedData.sourceRows (892 : Fin 2425) =
    MixedData.row892 := by decide +kernel

theorem sourceRowsAt893 : MixedData.sourceRows (893 : Fin 2425) =
    MixedData.row893 := by decide +kernel

theorem sourceRowsAt894 : MixedData.sourceRows (894 : Fin 2425) =
    MixedData.row894 := by decide +kernel

theorem sourceRowsAt895 : MixedData.sourceRows (895 : Fin 2425) =
    MixedData.row895 := by decide +kernel

theorem chunkSound55_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 55) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 880 ∨ k.val = 881 ∨ k.val = 882 ∨ k.val = 883 ∨ k.val = 884 ∨ k.val = 885 ∨ k.val = 886 ∨ k.val = 887 ∨ k.val = 888 ∨ k.val = 889 ∨ k.val = 890 ∨ k.val = 891 ∨ k.val = 892 ∨ k.val = 893 ∨ k.val = 894 ∨ k.val = 895 := by omega
  rcases heq with h880 | h881 | h882 | h883 | h884 | h885 | h886 | h887 | h888 | h889 | h890 | h891 | h892 | h893 | h894 | h895
  · have he : k = (880 : Fin 2425) := Fin.ext h880
    subst k
    rw [sourceRowsAt880]
    exact rowSound880 B hB hF
  · have he : k = (881 : Fin 2425) := Fin.ext h881
    subst k
    rw [sourceRowsAt881]
    exact rowSound881_e B hB hF
  · have he : k = (882 : Fin 2425) := Fin.ext h882
    subst k
    rw [sourceRowsAt882]
    exact rowSound882_e B hB hF
  · have he : k = (883 : Fin 2425) := Fin.ext h883
    subst k
    rw [sourceRowsAt883]
    exact rowSound883_e B hB hF
  · have he : k = (884 : Fin 2425) := Fin.ext h884
    subst k
    rw [sourceRowsAt884]
    exact rowSound884_e B hB hF
  · have he : k = (885 : Fin 2425) := Fin.ext h885
    subst k
    rw [sourceRowsAt885]
    exact rowSound885_e B hB hF
  · have he : k = (886 : Fin 2425) := Fin.ext h886
    subst k
    rw [sourceRowsAt886]
    exact rowSound886 B hB hF
  · have he : k = (887 : Fin 2425) := Fin.ext h887
    subst k
    rw [sourceRowsAt887]
    exact rowSound887_e B hB hF
  · have he : k = (888 : Fin 2425) := Fin.ext h888
    subst k
    rw [sourceRowsAt888]
    exact rowSound888_e B hB hF
  · have he : k = (889 : Fin 2425) := Fin.ext h889
    subst k
    rw [sourceRowsAt889]
    exact rowSound889 B hB hF
  · have he : k = (890 : Fin 2425) := Fin.ext h890
    subst k
    rw [sourceRowsAt890]
    exact rowSound890_e B hB hF
  · have he : k = (891 : Fin 2425) := Fin.ext h891
    subst k
    rw [sourceRowsAt891]
    exact rowSound891_e B hB hF
  · have he : k = (892 : Fin 2425) := Fin.ext h892
    subst k
    rw [sourceRowsAt892]
    exact rowSound892 B hB hF
  · have he : k = (893 : Fin 2425) := Fin.ext h893
    subst k
    rw [sourceRowsAt893]
    exact rowSound893 B hB hF
  · have he : k = (894 : Fin 2425) := Fin.ext h894
    subst k
    rw [sourceRowsAt894]
    exact rowSound894_e B hB hF
  · have he : k = (895 : Fin 2425) := Fin.ext h895
    subst k
    rw [sourceRowsAt895]
    exact rowSound895 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound55_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound55_e_oai
