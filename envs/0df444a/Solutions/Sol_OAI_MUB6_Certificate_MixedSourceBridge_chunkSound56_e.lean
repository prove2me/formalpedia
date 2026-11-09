-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:23:44.881202+00:00
-- url     : https://prove2.me/submissions/46243a9d-18a1-4b11-8518-3b5e7d867dfa

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3847_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3852_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3977_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3981_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5433_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5439_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5482_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5483_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5485_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound897_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound898_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound899_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound900_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound902_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound903_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound905_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound906_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound908_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound909_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound910_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound911_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15113 raw15113Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw15113 raw15113Labels = mixedMoment B raw15113step0 raw15113step0Labels := by
      have hz : ∀ j, raw15113 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15113step0 = (fun i j => raw15113 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15113step0 raw15113; decide +kernel
      have hl : raw15113step0Labels = raw15113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15113 raw15113Labels permutation346 hz
    mixedMoment B raw15113step0 raw15113step0Labels = mixedMoment B raw15113step1 raw15113step1Labels := by
      have ha : raw15113step1 = (fun i j => raw15113step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15113step1 raw15113step0; decide +kernel
      have hl : raw15113step1Labels = raw15113step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15113step0 raw15113step0Labels permutation32 permutation6
    mixedMoment B raw15113step1 raw15113step1Labels = mixedMoment B raw15113step2 raw15113step2Labels := by
      have ha : raw15113step2 = raw15113step1 := by apply Matrix.ext; unfold raw15113step2 raw15113step1; decide +kernel
      have hl : raw15113step1Labels = labelEmbedding9 ∘ raw15113step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15113step1 raw15113step1Labels raw15113step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5483 node5483Labels := by rfl

theorem canonical15114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15114 raw15114Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw15114 raw15114Labels = mixedMoment B raw15114step0 raw15114step0Labels := by
      have ha : raw15114step0 = (fun i j => raw15114 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15114step0 raw15114; decide +kernel
      have hl : raw15114step0Labels = raw15114Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15114 raw15114Labels permutation158 permutation7
    mixedMoment B raw15114step0 raw15114step0Labels = mixedMoment B raw15114step1 raw15114step1Labels := by
      have ha : raw15114step1 = raw15114step0 := by apply Matrix.ext; unfold raw15114step1 raw15114step0; decide +kernel
      have hl : raw15114step0Labels = labelEmbedding10 ∘ raw15114step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15114step0 raw15114step0Labels raw15114step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

theorem canonical15129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15129 raw15129Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw15129 raw15129Labels = mixedMoment B raw15129step0 raw15129step0Labels := by
      have hz : ∀ j, raw15129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15129step0 = (fun i j => raw15129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15129step0 raw15129; decide +kernel
      have hl : raw15129step0Labels = raw15129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15129 raw15129Labels permutation346 hz
    mixedMoment B raw15129step0 raw15129step0Labels = mixedMoment B raw15129step1 raw15129step1Labels := by
      have ha : raw15129step1 = (fun i j => raw15129step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15129step1 raw15129step0; decide +kernel
      have hl : raw15129step1Labels = raw15129step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15129step0 raw15129step0Labels permutation35 permutation4
    mixedMoment B raw15129step1 raw15129step1Labels = mixedMoment B raw15129step2 raw15129step2Labels := by
      have ha : raw15129step2 = -raw15129step1 := by apply Matrix.ext; change ∀ i j, raw15129step2 i j = -(raw15129step1 i j); unfold raw15129step2 raw15129step1; decide +kernel
      have hl : raw15129step2Labels = raw15129step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15129step2 raw15129step2Labels = mixedMoment B raw15129step3 raw15129step3Labels := by
      have ha : raw15129step3 = raw15129step2 := by apply Matrix.ext; unfold raw15129step3 raw15129step2; decide +kernel
      have hl : raw15129step2Labels = labelEmbedding7 ∘ raw15129step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15129step2 raw15129step2Labels raw15129step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical15130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15130 raw15130Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw15130 raw15130Labels = mixedMoment B raw15130step0 raw15130step0Labels := by
      have ha : raw15130step0 = (fun i j => raw15130 (permutation179 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15130step0 raw15130; decide +kernel
      have hl : raw15130step0Labels = raw15130Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15130 raw15130Labels permutation179 permutation4
    mixedMoment B raw15130step0 raw15130step0Labels = mixedMoment B raw15130step1 raw15130step1Labels := by
      have ha : raw15130step1 = -raw15130step0 := by apply Matrix.ext; change ∀ i j, raw15130step1 i j = -(raw15130step0 i j); unfold raw15130step1 raw15130step0; decide +kernel
      have hl : raw15130step1Labels = raw15130step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15130step1 raw15130step1Labels = mixedMoment B raw15130step2 raw15130step2Labels := by
      have ha : raw15130step2 = raw15130step1 := by apply Matrix.ext; unfold raw15130step2 raw15130step1; decide +kernel
      have hl : raw15130step1Labels = labelEmbedding7 ∘ raw15130step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15130step1 raw15130step1Labels raw15130step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

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

theorem canonical15144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15144 raw15144Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw15144 raw15144Labels = mixedMoment B raw15144step0 raw15144step0Labels := by
      have hz : ∀ j, raw15144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15144step0 = (fun i j => raw15144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15144step0 raw15144; decide +kernel
      have hl : raw15144step0Labels = raw15144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15144 raw15144Labels permutation346 hz
    mixedMoment B raw15144step0 raw15144step0Labels = mixedMoment B raw15144step1 raw15144step1Labels := by
      have ha : raw15144step1 = (fun i j => raw15144step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15144step1 raw15144step0; decide +kernel
      have hl : raw15144step1Labels = raw15144step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15144step0 raw15144step0Labels permutation151 permutation7
    mixedMoment B raw15144step1 raw15144step1Labels = mixedMoment B raw15144step2 raw15144step2Labels := by
      have ha : raw15144step2 = -raw15144step1 := by apply Matrix.ext; change ∀ i j, raw15144step2 i j = -(raw15144step1 i j); unfold raw15144step2 raw15144step1; decide +kernel
      have hl : raw15144step2Labels = raw15144step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15144step2 raw15144step2Labels = mixedMoment B raw15144step3 raw15144step3Labels := by
      have ha : raw15144step3 = raw15144step2 := by apply Matrix.ext; unfold raw15144step3 raw15144step2; decide +kernel
      have hl : raw15144step2Labels = labelEmbedding1 ∘ raw15144step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15144step2 raw15144step2Labels raw15144step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3808 node3808Labels := by rfl

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

theorem canonical15154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15154 raw15154Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw15154 raw15154Labels = mixedMoment B raw15154step0 raw15154step0Labels := by
      have ha : raw15154step0 = (fun i j => raw15154 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15154step0 raw15154; decide +kernel
      have hl : raw15154step0Labels = raw15154Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15154 raw15154Labels permutation682 permutation7
    mixedMoment B raw15154step0 raw15154step0Labels = mixedMoment B raw15154step1 raw15154step1Labels := by
      have ha : raw15154step1 = -raw15154step0 := by apply Matrix.ext; change ∀ i j, raw15154step1 i j = -(raw15154step0 i j); unfold raw15154step1 raw15154step0; decide +kernel
      have hl : raw15154step1Labels = raw15154step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15154step1 raw15154step1Labels = mixedMoment B raw15154step2 raw15154step2Labels := by
      have ha : raw15154step2 = raw15154step1 := by apply Matrix.ext; unfold raw15154step2 raw15154step1; decide +kernel
      have hl : raw15154step1Labels = labelEmbedding1 ∘ raw15154step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15154step1 raw15154step1Labels raw15154step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3801 node3801Labels := by rfl

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

theorem canonical15718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15718 raw15718Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw15718 raw15718Labels = mixedMoment B raw15718step0 raw15718step0Labels := by
      have ha : raw15718step0 = (fun i j => raw15718 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15718step0 raw15718; decide +kernel
      have hl : raw15718step0Labels = raw15718Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15718 raw15718Labels permutation682 permutation7
    mixedMoment B raw15718step0 raw15718step0Labels = mixedMoment B raw15718step1 raw15718step1Labels := by
      have ha : raw15718step1 = -raw15718step0 := by apply Matrix.ext; change ∀ i j, raw15718step1 i j = -(raw15718step0 i j); unfold raw15718step1 raw15718step0; decide +kernel
      have hl : raw15718step1Labels = raw15718step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15718step1 raw15718step1Labels = mixedMoment B raw15718step2 raw15718step2Labels := by
      have ha : raw15718step2 = raw15718step1 := by apply Matrix.ext; unfold raw15718step2 raw15718step1; decide +kernel
      have hl : raw15718step1Labels = labelEmbedding1 ∘ raw15718step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15718step1 raw15718step1Labels raw15718step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3758 node3758Labels := by rfl

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

theorem canonical15893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15893 raw15893Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw15893 raw15893Labels = mixedMoment B raw15893step0 raw15893step0Labels := by
      have hz : ∀ j, raw15893 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15893step0 = (fun i j => raw15893 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15893step0 raw15893; decide +kernel
      have hl : raw15893step0Labels = raw15893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15893 raw15893Labels permutation434 hz
    mixedMoment B raw15893step0 raw15893step0Labels = mixedMoment B raw15893step1 raw15893step1Labels := by
      have ha : raw15893step1 = (fun i j => raw15893step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15893step1 raw15893step0; decide +kernel
      have hl : raw15893step1Labels = raw15893step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15893step0 raw15893step0Labels permutation151 permutation7
    mixedMoment B raw15893step1 raw15893step1Labels = mixedMoment B raw15893step2 raw15893step2Labels := by
      have ha : raw15893step2 = -raw15893step1 := by apply Matrix.ext; change ∀ i j, raw15893step2 i j = -(raw15893step1 i j); unfold raw15893step2 raw15893step1; decide +kernel
      have hl : raw15893step2Labels = raw15893step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15893step2 raw15893step2Labels = mixedMoment B raw15893step3 raw15893step3Labels := by
      have ha : raw15893step3 = raw15893step2 := by apply Matrix.ext; unfold raw15893step3 raw15893step2; decide +kernel
      have hl : raw15893step2Labels = labelEmbedding1 ∘ raw15893step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15893step2 raw15893step2Labels raw15893step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3808 node3808Labels := by rfl

theorem canonical15894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15894 raw15894Labels = mixedMoment B node3460 node3460Labels := by
  calc
    mixedMoment B raw15894 raw15894Labels = mixedMoment B raw15894step0 raw15894step0Labels := by
      have ha : raw15894step0 = (fun i j => raw15894 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15894step0 raw15894; decide +kernel
      have hl : raw15894step0Labels = raw15894Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15894 raw15894Labels permutation682 permutation7
    mixedMoment B raw15894step0 raw15894step0Labels = mixedMoment B raw15894step1 raw15894step1Labels := by
      have ha : raw15894step1 = -raw15894step0 := by apply Matrix.ext; change ∀ i j, raw15894step1 i j = -(raw15894step0 i j); unfold raw15894step1 raw15894step0; decide +kernel
      have hl : raw15894step1Labels = raw15894step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15894step1 raw15894step1Labels = mixedMoment B raw15894step2 raw15894step2Labels := by
      have ha : raw15894step2 = raw15894step1 := by apply Matrix.ext; unfold raw15894step2 raw15894step1; decide +kernel
      have hl : raw15894step1Labels = labelEmbedding1 ∘ raw15894step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15894step1 raw15894step1Labels raw15894step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3460 node3460Labels := by rfl

theorem canonical15899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15899 raw15899Labels = mixedMoment B node3803 node3803Labels := by
  calc
    mixedMoment B raw15899 raw15899Labels = mixedMoment B raw15899step0 raw15899step0Labels := by
      have ha : raw15899step0 = (fun i j => raw15899 (permutation394 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15899step0 raw15899; decide +kernel
      have hl : raw15899step0Labels = raw15899Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15899 raw15899Labels permutation394 permutation5
    mixedMoment B raw15899step0 raw15899step0Labels = mixedMoment B raw15899step1 raw15899step1Labels := by
      have ha : raw15899step1 = raw15899step0 := by apply Matrix.ext; unfold raw15899step1 raw15899step0; decide +kernel
      have hl : raw15899step0Labels = labelEmbedding1 ∘ raw15899step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15899step0 raw15899step0Labels raw15899step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3803 node3803Labels := by rfl

theorem canonical15903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15903 raw15903Labels = mixedMoment B node3803 node3803Labels := by
  calc
    mixedMoment B raw15903 raw15903Labels = mixedMoment B raw15903step0 raw15903step0Labels := by
      have ha : raw15903step0 = (fun i j => raw15903 (permutation480 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15903step0 raw15903; decide +kernel
      have hl : raw15903step0Labels = raw15903Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15903 raw15903Labels permutation480 permutation5
    mixedMoment B raw15903step0 raw15903step0Labels = mixedMoment B raw15903step1 raw15903step1Labels := by
      have ha : raw15903step1 = raw15903step0 := by apply Matrix.ext; unfold raw15903step1 raw15903step0; decide +kernel
      have hl : raw15903step0Labels = labelEmbedding1 ∘ raw15903step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15903step0 raw15903step0Labels raw15903step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3803 node3803Labels := by rfl

theorem canonical15906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15906 raw15906Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw15906 raw15906Labels = mixedMoment B raw15906step0 raw15906step0Labels := by
      have ha : raw15906step0 = (fun i j => raw15906 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15906step0 raw15906; decide +kernel
      have hl : raw15906step0Labels = raw15906Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15906 raw15906Labels permutation682 permutation7
    mixedMoment B raw15906step0 raw15906step0Labels = mixedMoment B raw15906step1 raw15906step1Labels := by
      have ha : raw15906step1 = -raw15906step0 := by apply Matrix.ext; change ∀ i j, raw15906step1 i j = -(raw15906step0 i j); unfold raw15906step1 raw15906step0; decide +kernel
      have hl : raw15906step1Labels = raw15906step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15906step1 raw15906step1Labels = mixedMoment B raw15906step2 raw15906step2Labels := by
      have ha : raw15906step2 = raw15906step1 := by apply Matrix.ext; unfold raw15906step2 raw15906step1; decide +kernel
      have hl : raw15906step1Labels = labelEmbedding1 ∘ raw15906step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15906step1 raw15906step1Labels raw15906step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3847 node3847Labels := by rfl

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

theorem canonical16851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16851 raw16851Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw16851 raw16851Labels = mixedMoment B raw16851step0 raw16851step0Labels := by
      have hz : ∀ j, raw16851 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16851step0 = (fun i j => raw16851 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16851step0 raw16851; decide +kernel
      have hl : raw16851step0Labels = raw16851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16851 raw16851Labels permutation346 hz
    mixedMoment B raw16851step0 raw16851step0Labels = mixedMoment B raw16851step1 raw16851step1Labels := by
      have ha : raw16851step1 = (fun i j => raw16851step0 (permutation102 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16851step1 raw16851step0; decide +kernel
      have hl : raw16851step1Labels = raw16851step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16851step0 raw16851step0Labels permutation102 permutation5
    mixedMoment B raw16851step1 raw16851step1Labels = mixedMoment B raw16851step2 raw16851step2Labels := by
      have ha : raw16851step2 = raw16851step1 := by apply Matrix.ext; unfold raw16851step2 raw16851step1; decide +kernel
      have hl : raw16851step1Labels = labelEmbedding8 ∘ raw16851step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16851step1 raw16851step1Labels raw16851step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

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

theorem canonical17029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17029 raw17029Labels = mixedMoment B node5382 node5382Labels := by
  calc
    mixedMoment B raw17029 raw17029Labels = mixedMoment B raw17029step0 raw17029step0Labels := by
      have ha : raw17029step0 = (fun i j => raw17029 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17029step0 raw17029; decide +kernel
      have hl : raw17029step0Labels = raw17029Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17029 raw17029Labels permutation200 permutation2
    mixedMoment B raw17029step0 raw17029step0Labels = mixedMoment B raw17029step1 raw17029step1Labels := by
      have ha : raw17029step1 = -raw17029step0 := by apply Matrix.ext; change ∀ i j, raw17029step1 i j = -(raw17029step0 i j); unfold raw17029step1 raw17029step0; decide +kernel
      have hl : raw17029step1Labels = raw17029step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5382 node5382Labels := by rfl

theorem canonical17030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17030 raw17030Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw17030 raw17030Labels = mixedMoment B raw17030step0 raw17030step0Labels := by
      have ha : raw17030step0 = (fun i j => raw17030 (permutation203 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17030step0 raw17030; decide +kernel
      have hl : raw17030step0Labels = raw17030Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17030 raw17030Labels permutation203 permutation2
    mixedMoment B raw17030step0 raw17030step0Labels = mixedMoment B raw17030step1 raw17030step1Labels := by
      have ha : raw17030step1 = -raw17030step0 := by apply Matrix.ext; change ∀ i j, raw17030step1 i j = -(raw17030step0 i j); unfold raw17030step1 raw17030step0; decide +kernel
      have hl : raw17030step1Labels = raw17030step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5381 node5381Labels := by rfl

theorem canonical17031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17031 raw17031Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17031 raw17031Labels = mixedMoment B raw17031step0 raw17031step0Labels := by
      have ha : raw17031step0 = (fun i j => raw17031 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17031step0 raw17031; decide +kernel
      have hl : raw17031step0Labels = raw17031Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17031 raw17031Labels permutation158 permutation7
    mixedMoment B raw17031step0 raw17031step0Labels = mixedMoment B raw17031step1 raw17031step1Labels := by
      have ha : raw17031step1 = raw17031step0 := by apply Matrix.ext; unfold raw17031step1 raw17031step0; decide +kernel
      have hl : raw17031step0Labels = labelEmbedding10 ∘ raw17031step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17031step0 raw17031step0Labels raw17031step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical17032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17032 raw17032Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw17032 raw17032Labels = mixedMoment B raw17032step0 raw17032step0Labels := by
      have ha : raw17032step0 = (fun i j => raw17032 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17032step0 raw17032; decide +kernel
      have hl : raw17032step0Labels = raw17032Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17032 raw17032Labels permutation201 permutation2
    mixedMoment B raw17032step0 raw17032step0Labels = mixedMoment B raw17032step1 raw17032step1Labels := by
      have ha : raw17032step1 = -raw17032step0 := by apply Matrix.ext; change ∀ i j, raw17032step1 i j = -(raw17032step0 i j); unfold raw17032step1 raw17032step0; decide +kernel
      have hl : raw17032step1Labels = raw17032step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5379 node5379Labels := by rfl

theorem canonical17033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17033 raw17033Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw17033 raw17033Labels = mixedMoment B raw17033step0 raw17033step0Labels := by
      have ha : raw17033step0 = (fun i j => raw17033 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17033step0 raw17033; decide +kernel
      have hl : raw17033step0Labels = raw17033Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17033 raw17033Labels permutation200 permutation2
    mixedMoment B raw17033step0 raw17033step0Labels = mixedMoment B raw17033step1 raw17033step1Labels := by
      have ha : raw17033step1 = -raw17033step0 := by apply Matrix.ext; change ∀ i j, raw17033step1 i j = -(raw17033step0 i j); unfold raw17033step1 raw17033step0; decide +kernel
      have hl : raw17033step1Labels = raw17033step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical17034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17034 raw17034Labels = mixedMoment B node5420 node5420Labels := by
  calc
    mixedMoment B raw17034 raw17034Labels = mixedMoment B raw17034step0 raw17034step0Labels := by
      have ha : raw17034step0 = (fun i j => raw17034 (permutation409 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17034step0 raw17034; decide +kernel
      have hl : raw17034step0Labels = raw17034Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17034 raw17034Labels permutation409 permutation3
    mixedMoment B raw17034step0 raw17034step0Labels = mixedMoment B raw17034step1 raw17034step1Labels := by
      have ha : raw17034step1 = raw17034step0 := by apply Matrix.ext; unfold raw17034step1 raw17034step0; decide +kernel
      have hl : raw17034step0Labels = labelEmbedding6 ∘ raw17034step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17034step0 raw17034step0Labels raw17034step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5420 node5420Labels := by rfl

theorem canonical17035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17035 raw17035Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw17035 raw17035Labels = mixedMoment B raw17035step0 raw17035step0Labels := by
      have ha : raw17035step0 = (fun i j => raw17035 (permutation455 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17035step0 raw17035; decide +kernel
      have hl : raw17035step0Labels = raw17035Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17035 raw17035Labels permutation455 permutation3
    mixedMoment B raw17035step0 raw17035step0Labels = mixedMoment B raw17035step1 raw17035step1Labels := by
      have ha : raw17035step1 = -raw17035step0 := by apply Matrix.ext; change ∀ i j, raw17035step1 i j = -(raw17035step0 i j); unfold raw17035step1 raw17035step0; decide +kernel
      have hl : raw17035step1Labels = raw17035step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17035step1 raw17035step1Labels = mixedMoment B raw17035step2 raw17035step2Labels := by
      have ha : raw17035step2 = raw17035step1 := by apply Matrix.ext; unfold raw17035step2 raw17035step1; decide +kernel
      have hl : raw17035step1Labels = labelEmbedding6 ∘ raw17035step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17035step1 raw17035step1Labels raw17035step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

theorem canonical17036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17036 raw17036Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw17036 raw17036Labels = mixedMoment B raw17036step0 raw17036step0Labels := by
      have ha : raw17036step0 = (fun i j => raw17036 (permutation679 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17036step0 raw17036; decide +kernel
      have hl : raw17036step0Labels = raw17036Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17036 raw17036Labels permutation679 permutation2
    _ = mixedMoment B node5397 node5397Labels := by rfl

theorem canonical17037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17037 raw17037Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw17037 raw17037Labels = mixedMoment B raw17037step0 raw17037step0Labels := by
      have hz : ∀ j, raw17037 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17037step0 = (fun i j => raw17037 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17037step0 raw17037; decide +kernel
      have hl : raw17037step0Labels = raw17037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17037 raw17037Labels permutation346 hz
    mixedMoment B raw17037step0 raw17037step0Labels = mixedMoment B raw17037step1 raw17037step1Labels := by
      have ha : raw17037step1 = (fun i j => raw17037step0 (permutation81 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17037step1 raw17037step0; decide +kernel
      have hl : raw17037step1Labels = raw17037step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17037step0 raw17037step0Labels permutation81 permutation3
    mixedMoment B raw17037step1 raw17037step1Labels = mixedMoment B raw17037step2 raw17037step2Labels := by
      have ha : raw17037step2 = -raw17037step1 := by apply Matrix.ext; change ∀ i j, raw17037step2 i j = -(raw17037step1 i j); unfold raw17037step2 raw17037step1; decide +kernel
      have hl : raw17037step2Labels = raw17037step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17037step2 raw17037step2Labels = mixedMoment B raw17037step3 raw17037step3Labels := by
      have ha : raw17037step3 = raw17037step2 := by apply Matrix.ext; unfold raw17037step3 raw17037step2; decide +kernel
      have hl : raw17037step2Labels = labelEmbedding6 ∘ raw17037step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17037step2 raw17037step2Labels raw17037step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

theorem canonical17038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17038 raw17038Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw17038 raw17038Labels = mixedMoment B raw17038step0 raw17038step0Labels := by
      have hz : ∀ j, raw17038 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17038step0 = (fun i j => raw17038 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17038step0 raw17038; decide +kernel
      have hl : raw17038step0Labels = raw17038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17038 raw17038Labels permutation346 hz
    mixedMoment B raw17038step0 raw17038step0Labels = mixedMoment B raw17038step1 raw17038step1Labels := by
      have ha : raw17038step1 = (fun i j => raw17038step0 (permutation148 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17038step1 raw17038step0; decide +kernel
      have hl : raw17038step1Labels = raw17038step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17038step0 raw17038step0Labels permutation148 permutation2
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical17039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17039 raw17039Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw17039 raw17039Labels = mixedMoment B raw17039step0 raw17039step0Labels := by
      have ha : raw17039step0 = (fun i j => raw17039 (permutation517 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17039step0 raw17039; decide +kernel
      have hl : raw17039step0Labels = raw17039Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17039 raw17039Labels permutation517 permutation5
    mixedMoment B raw17039step0 raw17039step0Labels = mixedMoment B raw17039step1 raw17039step1Labels := by
      have ha : raw17039step1 = raw17039step0 := by apply Matrix.ext; unfold raw17039step1 raw17039step0; decide +kernel
      have hl : raw17039step0Labels = labelEmbedding8 ∘ raw17039step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17039step0 raw17039step0Labels raw17039step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4852 node4852Labels := by rfl

theorem canonical17040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17040 raw17040Labels = mixedMoment B node4849 node4849Labels := by
  calc
    mixedMoment B raw17040 raw17040Labels = mixedMoment B raw17040step0 raw17040step0Labels := by
      have ha : raw17040step0 = (fun i j => raw17040 (permutation515 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17040step0 raw17040; decide +kernel
      have hl : raw17040step0Labels = raw17040Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17040 raw17040Labels permutation515 permutation5
    mixedMoment B raw17040step0 raw17040step0Labels = mixedMoment B raw17040step1 raw17040step1Labels := by
      have ha : raw17040step1 = raw17040step0 := by apply Matrix.ext; unfold raw17040step1 raw17040step0; decide +kernel
      have hl : raw17040step0Labels = labelEmbedding8 ∘ raw17040step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17040step0 raw17040step0Labels raw17040step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4849 node4849Labels := by rfl

theorem canonical17041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17041 raw17041Labels = mixedMoment B node4848 node4848Labels := by
  calc
    mixedMoment B raw17041 raw17041Labels = mixedMoment B raw17041step0 raw17041step0Labels := by
      have ha : raw17041step0 = (fun i j => raw17041 (permutation439 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17041step0 raw17041; decide +kernel
      have hl : raw17041step0Labels = raw17041Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17041 raw17041Labels permutation439 permutation3
    mixedMoment B raw17041step0 raw17041step0Labels = mixedMoment B raw17041step1 raw17041step1Labels := by
      have ha : raw17041step1 = -raw17041step0 := by apply Matrix.ext; change ∀ i j, raw17041step1 i j = -(raw17041step0 i j); unfold raw17041step1 raw17041step0; decide +kernel
      have hl : raw17041step1Labels = raw17041step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17041step1 raw17041step1Labels = mixedMoment B raw17041step2 raw17041step2Labels := by
      have ha : raw17041step2 = raw17041step1 := by apply Matrix.ext; unfold raw17041step2 raw17041step1; decide +kernel
      have hl : raw17041step1Labels = labelEmbedding6 ∘ raw17041step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17041step1 raw17041step1Labels raw17041step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4848 node4848Labels := by rfl

theorem canonical17042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17042 raw17042Labels = mixedMoment B node4849 node4849Labels := by
  calc
    mixedMoment B raw17042 raw17042Labels = mixedMoment B raw17042step0 raw17042step0Labels := by
      have ha : raw17042step0 = (fun i j => raw17042 (permutation438 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17042step0 raw17042; decide +kernel
      have hl : raw17042step0Labels = raw17042Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17042 raw17042Labels permutation438 permutation3
    mixedMoment B raw17042step0 raw17042step0Labels = mixedMoment B raw17042step1 raw17042step1Labels := by
      have ha : raw17042step1 = -raw17042step0 := by apply Matrix.ext; change ∀ i j, raw17042step1 i j = -(raw17042step0 i j); unfold raw17042step1 raw17042step0; decide +kernel
      have hl : raw17042step1Labels = raw17042step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17042step1 raw17042step1Labels = mixedMoment B raw17042step2 raw17042step2Labels := by
      have ha : raw17042step2 = raw17042step1 := by apply Matrix.ext; unfold raw17042step2 raw17042step1; decide +kernel
      have hl : raw17042step1Labels = labelEmbedding6 ∘ raw17042step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17042step1 raw17042step1Labels raw17042step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4849 node4849Labels := by rfl

theorem canonical17043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17043 raw17043Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw17043 raw17043Labels = mixedMoment B raw17043step0 raw17043step0Labels := by
      have ha : raw17043step0 = (fun i j => raw17043 (permutation436 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17043step0 raw17043; decide +kernel
      have hl : raw17043step0Labels = raw17043Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17043 raw17043Labels permutation436 permutation3
    mixedMoment B raw17043step0 raw17043step0Labels = mixedMoment B raw17043step1 raw17043step1Labels := by
      have ha : raw17043step1 = -raw17043step0 := by apply Matrix.ext; change ∀ i j, raw17043step1 i j = -(raw17043step0 i j); unfold raw17043step1 raw17043step0; decide +kernel
      have hl : raw17043step1Labels = raw17043step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17043step1 raw17043step1Labels = mixedMoment B raw17043step2 raw17043step2Labels := by
      have ha : raw17043step2 = raw17043step1 := by apply Matrix.ext; unfold raw17043step2 raw17043step1; decide +kernel
      have hl : raw17043step1Labels = labelEmbedding6 ∘ raw17043step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17043step1 raw17043step1Labels raw17043step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4852 node4852Labels := by rfl

theorem canonical17044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17044 raw17044Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw17044 raw17044Labels = mixedMoment B raw17044step0 raw17044step0Labels := by
      have ha : raw17044step0 = (fun i j => raw17044 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17044step0 raw17044; decide +kernel
      have hl : raw17044step0Labels = raw17044Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17044 raw17044Labels permutation155 permutation4
    mixedMoment B raw17044step0 raw17044step0Labels = mixedMoment B raw17044step1 raw17044step1Labels := by
      have ha : raw17044step1 = -raw17044step0 := by apply Matrix.ext; change ∀ i j, raw17044step1 i j = -(raw17044step0 i j); unfold raw17044step1 raw17044step0; decide +kernel
      have hl : raw17044step1Labels = raw17044step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17044step1 raw17044step1Labels = mixedMoment B raw17044step2 raw17044step2Labels := by
      have ha : raw17044step2 = raw17044step1 := by apply Matrix.ext; unfold raw17044step2 raw17044step1; decide +kernel
      have hl : raw17044step1Labels = labelEmbedding7 ∘ raw17044step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17044step1 raw17044step1Labels raw17044step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

theorem canonical17045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17045 raw17045Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw17045 raw17045Labels = mixedMoment B raw17045step0 raw17045step0Labels := by
      have ha : raw17045step0 = (fun i j => raw17045 (permutation500 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17045step0 raw17045; decide +kernel
      have hl : raw17045step0Labels = raw17045Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17045 raw17045Labels permutation500 permutation5
    mixedMoment B raw17045step0 raw17045step0Labels = mixedMoment B raw17045step1 raw17045step1Labels := by
      have ha : raw17045step1 = raw17045step0 := by apply Matrix.ext; unfold raw17045step1 raw17045step0; decide +kernel
      have hl : raw17045step0Labels = labelEmbedding8 ∘ raw17045step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17045step0 raw17045step0Labels raw17045step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

theorem canonical17046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17046 raw17046Labels = mixedMoment B node5420 node5420Labels := by
  calc
    mixedMoment B raw17046 raw17046Labels = mixedMoment B raw17046step0 raw17046step0Labels := by
      have ha : raw17046step0 = (fun i j => raw17046 (permutation499 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17046step0 raw17046; decide +kernel
      have hl : raw17046step0Labels = raw17046Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17046 raw17046Labels permutation499 permutation5
    mixedMoment B raw17046step0 raw17046step0Labels = mixedMoment B raw17046step1 raw17046step1Labels := by
      have ha : raw17046step1 = raw17046step0 := by apply Matrix.ext; unfold raw17046step1 raw17046step0; decide +kernel
      have hl : raw17046step0Labels = labelEmbedding8 ∘ raw17046step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17046step0 raw17046step0Labels raw17046step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5420 node5420Labels := by rfl

theorem canonical17047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17047 raw17047Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw17047 raw17047Labels = mixedMoment B raw17047step0 raw17047step0Labels := by
      have ha : raw17047step0 = (fun i j => raw17047 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17047step0 raw17047; decide +kernel
      have hl : raw17047step0Labels = raw17047Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17047 raw17047Labels permutation152 permutation6
    mixedMoment B raw17047step0 raw17047step0Labels = mixedMoment B raw17047step1 raw17047step1Labels := by
      have ha : raw17047step1 = raw17047step0 := by apply Matrix.ext; unfold raw17047step1 raw17047step0; decide +kernel
      have hl : raw17047step0Labels = labelEmbedding9 ∘ raw17047step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17047step0 raw17047step0Labels raw17047step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

theorem canonical17048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17048 raw17048Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw17048 raw17048Labels = mixedMoment B raw17048step0 raw17048step0Labels := by
      have ha : raw17048step0 = (fun i j => raw17048 (permutation643 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17048step0 raw17048; decide +kernel
      have hl : raw17048step0Labels = raw17048Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17048 raw17048Labels permutation643 permutation2
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical17049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17049 raw17049Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw17049 raw17049Labels = mixedMoment B raw17049step0 raw17049step0Labels := by
      have ha : raw17049step0 = (fun i j => raw17049 (permutation664 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17049step0 raw17049; decide +kernel
      have hl : raw17049step0Labels = raw17049Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17049 raw17049Labels permutation664 permutation4
    mixedMoment B raw17049step0 raw17049step0Labels = mixedMoment B raw17049step1 raw17049step1Labels := by
      have ha : raw17049step1 = raw17049step0 := by apply Matrix.ext; unfold raw17049step1 raw17049step0; decide +kernel
      have hl : raw17049step0Labels = labelEmbedding7 ∘ raw17049step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17049step0 raw17049step0Labels raw17049step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical17050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17050 raw17050Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw17050 raw17050Labels = mixedMoment B raw17050step0 raw17050step0Labels := by
      have ha : raw17050step0 = (fun i j => raw17050 (permutation663 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17050step0 raw17050; decide +kernel
      have hl : raw17050step0Labels = raw17050Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17050 raw17050Labels permutation663 permutation4
    mixedMoment B raw17050step0 raw17050step0Labels = mixedMoment B raw17050step1 raw17050step1Labels := by
      have ha : raw17050step1 = raw17050step0 := by apply Matrix.ext; unfold raw17050step1 raw17050step0; decide +kernel
      have hl : raw17050step0Labels = labelEmbedding7 ∘ raw17050step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17050step0 raw17050step0Labels raw17050step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

theorem canonical17051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17051 raw17051Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw17051 raw17051Labels = mixedMoment B raw17051step0 raw17051step0Labels := by
      have ha : raw17051step0 = (fun i j => raw17051 (permutation661 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17051step0 raw17051; decide +kernel
      have hl : raw17051step0Labels = raw17051Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17051 raw17051Labels permutation661 permutation4
    mixedMoment B raw17051step0 raw17051step0Labels = mixedMoment B raw17051step1 raw17051step1Labels := by
      have ha : raw17051step1 = raw17051step0 := by apply Matrix.ext; unfold raw17051step1 raw17051step0; decide +kernel
      have hl : raw17051step0Labels = labelEmbedding7 ∘ raw17051step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17051step0 raw17051step0Labels raw17051step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

theorem canonical17052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17052 raw17052Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17052 raw17052Labels = mixedMoment B raw17052step0 raw17052step0Labels := by
      have ha : raw17052step0 = (fun i j => raw17052 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17052step0 raw17052; decide +kernel
      have hl : raw17052step0Labels = raw17052Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17052 raw17052Labels permutation688 permutation6
    mixedMoment B raw17052step0 raw17052step0Labels = mixedMoment B raw17052step1 raw17052step1Labels := by
      have ha : raw17052step1 = -raw17052step0 := by apply Matrix.ext; change ∀ i j, raw17052step1 i j = -(raw17052step0 i j); unfold raw17052step1 raw17052step0; decide +kernel
      have hl : raw17052step1Labels = raw17052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17052step1 raw17052step1Labels = mixedMoment B raw17052step2 raw17052step2Labels := by
      have ha : raw17052step2 = raw17052step1 := by apply Matrix.ext; unfold raw17052step2 raw17052step1; decide +kernel
      have hl : raw17052step1Labels = labelEmbedding9 ∘ raw17052step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17052step1 raw17052step1Labels raw17052step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical17053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17053 raw17053Labels = mixedMoment B node5382 node5382Labels := by
  calc
    mixedMoment B raw17053 raw17053Labels = mixedMoment B raw17053step0 raw17053step0Labels := by
      have ha : raw17053step0 = (fun i j => raw17053 (permutation664 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17053step0 raw17053; decide +kernel
      have hl : raw17053step0Labels = raw17053Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17053 raw17053Labels permutation664 permutation4
    mixedMoment B raw17053step0 raw17053step0Labels = mixedMoment B raw17053step1 raw17053step1Labels := by
      have ha : raw17053step1 = raw17053step0 := by apply Matrix.ext; unfold raw17053step1 raw17053step0; decide +kernel
      have hl : raw17053step0Labels = labelEmbedding7 ∘ raw17053step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17053step0 raw17053step0Labels raw17053step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5382 node5382Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical134
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17179 raw17179Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw17179 raw17179Labels = mixedMoment B raw17179step0 raw17179step0Labels := by
      have ha : raw17179step0 = (fun i j => raw17179 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17179step0 raw17179; decide +kernel
      have hl : raw17179step0Labels = raw17179Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17179 raw17179Labels permutation681 permutation2
    mixedMoment B raw17179step0 raw17179step0Labels = mixedMoment B raw17179step1 raw17179step1Labels := by
      have ha : raw17179step1 = -raw17179step0 := by apply Matrix.ext; change ∀ i j, raw17179step1 i j = -(raw17179step0 i j); unfold raw17179step1 raw17179step0; decide +kernel
      have hl : raw17179step1Labels = raw17179step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical17180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17180 raw17180Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw17180 raw17180Labels = mixedMoment B raw17180step0 raw17180step0Labels := by
      have ha : raw17180step0 = (fun i j => raw17180 (permutation685 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17180step0 raw17180; decide +kernel
      have hl : raw17180step0Labels = raw17180Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17180 raw17180Labels permutation685 permutation2
    mixedMoment B raw17180step0 raw17180step0Labels = mixedMoment B raw17180step1 raw17180step1Labels := by
      have ha : raw17180step1 = -raw17180step0 := by apply Matrix.ext; change ∀ i j, raw17180step1 i j = -(raw17180step0 i j); unfold raw17180step1 raw17180step0; decide +kernel
      have hl : raw17180step1Labels = raw17180step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5408 node5408Labels := by rfl

theorem canonical17181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17181 raw17181Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw17181 raw17181Labels = mixedMoment B raw17181step0 raw17181step0Labels := by
      have ha : raw17181step0 = (fun i j => raw17181 (permutation679 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17181step0 raw17181; decide +kernel
      have hl : raw17181step0Labels = raw17181Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17181 raw17181Labels permutation679 permutation2
    mixedMoment B raw17181step0 raw17181step0Labels = mixedMoment B raw17181step1 raw17181step1Labels := by
      have ha : raw17181step1 = -raw17181step0 := by apply Matrix.ext; change ∀ i j, raw17181step1 i j = -(raw17181step0 i j); unfold raw17181step1 raw17181step0; decide +kernel
      have hl : raw17181step1Labels = raw17181step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5408 node5408Labels := by rfl

theorem canonical17182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17182 raw17182Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw17182 raw17182Labels = mixedMoment B raw17182step0 raw17182step0Labels := by
      have ha : raw17182step0 = (fun i j => raw17182 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17182step0 raw17182; decide +kernel
      have hl : raw17182step0Labels = raw17182Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17182 raw17182Labels permutation674 permutation7
    mixedMoment B raw17182step0 raw17182step0Labels = mixedMoment B raw17182step1 raw17182step1Labels := by
      have ha : raw17182step1 = raw17182step0 := by apply Matrix.ext; unfold raw17182step1 raw17182step0; decide +kernel
      have hl : raw17182step0Labels = labelEmbedding10 ∘ raw17182step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17182step0 raw17182step0Labels raw17182step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical17183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17183 raw17183Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw17183 raw17183Labels = mixedMoment B raw17183step0 raw17183step0Labels := by
      have ha : raw17183step0 = (fun i j => raw17183 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17183step0 raw17183; decide +kernel
      have hl : raw17183step0Labels = raw17183Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17183 raw17183Labels permutation674 permutation7
    mixedMoment B raw17183step0 raw17183step0Labels = mixedMoment B raw17183step1 raw17183step1Labels := by
      have ha : raw17183step1 = raw17183step0 := by apply Matrix.ext; unfold raw17183step1 raw17183step0; decide +kernel
      have hl : raw17183step0Labels = labelEmbedding10 ∘ raw17183step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17183step0 raw17183step0Labels raw17183step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

theorem canonical17184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17184 raw17184Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw17184 raw17184Labels = mixedMoment B raw17184step0 raw17184step0Labels := by
      have hz : ∀ j, raw17184 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw17184step0 = (fun i j => raw17184 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw17184step0 raw17184; decide +kernel
      have hl : raw17184step0Labels = raw17184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17184 raw17184Labels permutation265 hz
    mixedMoment B raw17184step0 raw17184step0Labels = mixedMoment B raw17184step1 raw17184step1Labels := by
      have ha : raw17184step1 = (fun i j => raw17184step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17184step1 raw17184step0; decide +kernel
      have hl : raw17184step1Labels = raw17184step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17184step0 raw17184step0Labels permutation32 permutation3
    mixedMoment B raw17184step1 raw17184step1Labels = mixedMoment B raw17184step2 raw17184step2Labels := by
      have ha : raw17184step2 = raw17184step1 := by apply Matrix.ext; unfold raw17184step2 raw17184step1; decide +kernel
      have hl : raw17184step1Labels = labelEmbedding6 ∘ raw17184step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17184step1 raw17184step1Labels raw17184step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical17185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17185 raw17185Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw17185 raw17185Labels = mixedMoment B raw17185step0 raw17185step0Labels := by
      have ha : raw17185step0 = (fun i j => raw17185 (permutation273 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17185step0 raw17185; decide +kernel
      have hl : raw17185step0Labels = raw17185Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17185 raw17185Labels permutation273 permutation3
    mixedMoment B raw17185step0 raw17185step0Labels = mixedMoment B raw17185step1 raw17185step1Labels := by
      have ha : raw17185step1 = raw17185step0 := by apply Matrix.ext; unfold raw17185step1 raw17185step0; decide +kernel
      have hl : raw17185step0Labels = labelEmbedding6 ∘ raw17185step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17185step0 raw17185step0Labels raw17185step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

theorem canonical17186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17186 raw17186Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw17186 raw17186Labels = mixedMoment B raw17186step0 raw17186step0Labels := by
      have ha : raw17186step0 = (fun i j => raw17186 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17186step0 raw17186; decide +kernel
      have hl : raw17186step0Labels = raw17186Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17186 raw17186Labels permutation680 permutation2
    mixedMoment B raw17186step0 raw17186step0Labels = mixedMoment B raw17186step1 raw17186step1Labels := by
      have ha : raw17186step1 = -raw17186step0 := by apply Matrix.ext; change ∀ i j, raw17186step1 i j = -(raw17186step0 i j); unfold raw17186step1 raw17186step0; decide +kernel
      have hl : raw17186step1Labels = raw17186step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5401 node5401Labels := by rfl

theorem canonical17187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17187 raw17187Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw17187 raw17187Labels = mixedMoment B raw17187step0 raw17187step0Labels := by
      have ha : raw17187step0 = (fun i j => raw17187 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17187step0 raw17187; decide +kernel
      have hl : raw17187step0Labels = raw17187Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17187 raw17187Labels permutation674 permutation7
    mixedMoment B raw17187step0 raw17187step0Labels = mixedMoment B raw17187step1 raw17187step1Labels := by
      have ha : raw17187step1 = raw17187step0 := by apply Matrix.ext; unfold raw17187step1 raw17187step0; decide +kernel
      have hl : raw17187step0Labels = labelEmbedding10 ∘ raw17187step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17187step0 raw17187step0Labels raw17187step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical17188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17188 raw17188Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw17188 raw17188Labels = mixedMoment B raw17188step0 raw17188step0Labels := by
      have ha : raw17188step0 = (fun i j => raw17188 (permutation163 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17188step0 raw17188; decide +kernel
      have hl : raw17188step0Labels = raw17188Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17188 raw17188Labels permutation163 permutation3
    mixedMoment B raw17188step0 raw17188step0Labels = mixedMoment B raw17188step1 raw17188step1Labels := by
      have ha : raw17188step1 = raw17188step0 := by apply Matrix.ext; unfold raw17188step1 raw17188step0; decide +kernel
      have hl : raw17188step0Labels = labelEmbedding6 ∘ raw17188step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17188step0 raw17188step0Labels raw17188step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5480 node5480Labels := by rfl

theorem canonical17189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17189 raw17189Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw17189 raw17189Labels = mixedMoment B raw17189step0 raw17189step0Labels := by
      have ha : raw17189step0 = (fun i j => raw17189 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17189step0 raw17189; decide +kernel
      have hl : raw17189step0Labels = raw17189Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17189 raw17189Labels permutation267 permutation3
    mixedMoment B raw17189step0 raw17189step0Labels = mixedMoment B raw17189step1 raw17189step1Labels := by
      have ha : raw17189step1 = raw17189step0 := by apply Matrix.ext; unfold raw17189step1 raw17189step0; decide +kernel
      have hl : raw17189step0Labels = labelEmbedding6 ∘ raw17189step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17189step0 raw17189step0Labels raw17189step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

theorem canonical17190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17190 raw17190Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw17190 raw17190Labels = mixedMoment B raw17190step0 raw17190step0Labels := by
      have ha : raw17190step0 = (fun i j => raw17190 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17190step0 raw17190; decide +kernel
      have hl : raw17190step0Labels = raw17190Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17190 raw17190Labels permutation686 permutation2
    mixedMoment B raw17190step0 raw17190step0Labels = mixedMoment B raw17190step1 raw17190step1Labels := by
      have ha : raw17190step1 = -raw17190step0 := by apply Matrix.ext; change ∀ i j, raw17190step1 i j = -(raw17190step0 i j); unfold raw17190step1 raw17190step0; decide +kernel
      have hl : raw17190step1Labels = raw17190step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5401 node5401Labels := by rfl

theorem canonical17191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17191 raw17191Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw17191 raw17191Labels = mixedMoment B raw17191step0 raw17191step0Labels := by
      have ha : raw17191step0 = (fun i j => raw17191 (permutation676 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17191step0 raw17191; decide +kernel
      have hl : raw17191step0Labels = raw17191Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17191 raw17191Labels permutation676 permutation7
    mixedMoment B raw17191step0 raw17191step0Labels = mixedMoment B raw17191step1 raw17191step1Labels := by
      have ha : raw17191step1 = raw17191step0 := by apply Matrix.ext; unfold raw17191step1 raw17191step0; decide +kernel
      have hl : raw17191step0Labels = labelEmbedding10 ∘ raw17191step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17191step0 raw17191step0Labels raw17191step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical17192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17192 raw17192Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw17192 raw17192Labels = mixedMoment B raw17192step0 raw17192step0Labels := by
      have ha : raw17192step0 = (fun i j => raw17192 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17192step0 raw17192; decide +kernel
      have hl : raw17192step0Labels = raw17192Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17192 raw17192Labels permutation157 permutation3
    mixedMoment B raw17192step0 raw17192step0Labels = mixedMoment B raw17192step1 raw17192step1Labels := by
      have ha : raw17192step1 = raw17192step0 := by apply Matrix.ext; unfold raw17192step1 raw17192step0; decide +kernel
      have hl : raw17192step0Labels = labelEmbedding6 ∘ raw17192step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17192step0 raw17192step0Labels raw17192step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5480 node5480Labels := by rfl

theorem canonical17193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17193 raw17193Labels = mixedMoment B node5348 node5348Labels := by
  calc
    mixedMoment B raw17193 raw17193Labels = mixedMoment B raw17193step0 raw17193step0Labels := by
      have ha : raw17193step0 = (fun i j => raw17193 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17193step0 raw17193; decide +kernel
      have hl : raw17193step0Labels = raw17193Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17193 raw17193Labels permutation682 permutation2
    mixedMoment B raw17193step0 raw17193step0Labels = mixedMoment B raw17193step1 raw17193step1Labels := by
      have ha : raw17193step1 = -raw17193step0 := by apply Matrix.ext; change ∀ i j, raw17193step1 i j = -(raw17193step0 i j); unfold raw17193step1 raw17193step0; decide +kernel
      have hl : raw17193step1Labels = raw17193step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5348 node5348Labels := by rfl

theorem canonical17194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17194 raw17194Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw17194 raw17194Labels = mixedMoment B raw17194step0 raw17194step0Labels := by
      have ha : raw17194step0 = (fun i j => raw17194 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17194step0 raw17194; decide +kernel
      have hl : raw17194step0Labels = raw17194Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17194 raw17194Labels permutation686 permutation2
    mixedMoment B raw17194step0 raw17194step0Labels = mixedMoment B raw17194step1 raw17194step1Labels := by
      have ha : raw17194step1 = -raw17194step0 := by apply Matrix.ext; change ∀ i j, raw17194step1 i j = -(raw17194step0 i j); unfold raw17194step1 raw17194step0; decide +kernel
      have hl : raw17194step1Labels = raw17194step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5352 node5352Labels := by rfl

theorem canonical17195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17195 raw17195Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw17195 raw17195Labels = mixedMoment B raw17195step0 raw17195step0Labels := by
      have ha : raw17195step0 = (fun i j => raw17195 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17195step0 raw17195; decide +kernel
      have hl : raw17195step0Labels = raw17195Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17195 raw17195Labels permutation680 permutation2
    mixedMoment B raw17195step0 raw17195step0Labels = mixedMoment B raw17195step1 raw17195step1Labels := by
      have ha : raw17195step1 = -raw17195step0 := by apply Matrix.ext; change ∀ i j, raw17195step1 i j = -(raw17195step0 i j); unfold raw17195step1 raw17195step0; decide +kernel
      have hl : raw17195step1Labels = raw17195step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5352 node5352Labels := by rfl

theorem canonical17196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17196 raw17196Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw17196 raw17196Labels = mixedMoment B raw17196step0 raw17196step0Labels := by
      have ha : raw17196step0 = (fun i j => raw17196 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17196step0 raw17196; decide +kernel
      have hl : raw17196step0Labels = raw17196Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17196 raw17196Labels permutation584 permutation2
    mixedMoment B raw17196step0 raw17196step0Labels = mixedMoment B raw17196step1 raw17196step1Labels := by
      have ha : raw17196step1 = -raw17196step0 := by apply Matrix.ext; change ∀ i j, raw17196step1 i j = -(raw17196step0 i j); unfold raw17196step1 raw17196step0; decide +kernel
      have hl : raw17196step1Labels = raw17196step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5471 node5471Labels := by rfl

theorem canonical17197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17197 raw17197Labels = mixedMoment B node5067 node5067Labels := by
  calc
    mixedMoment B raw17197 raw17197Labels = mixedMoment B raw17197step0 raw17197step0Labels := by
      have ha : raw17197step0 = (fun i j => raw17197 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17197step0 raw17197; decide +kernel
      have hl : raw17197step0Labels = raw17197Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17197 raw17197Labels permutation682 permutation2
    mixedMoment B raw17197step0 raw17197step0Labels = mixedMoment B raw17197step1 raw17197step1Labels := by
      have ha : raw17197step1 = -raw17197step0 := by apply Matrix.ext; change ∀ i j, raw17197step1 i j = -(raw17197step0 i j); unfold raw17197step1 raw17197step0; decide +kernel
      have hl : raw17197step1Labels = raw17197step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5067 node5067Labels := by rfl

theorem canonical17198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17198 raw17198Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw17198 raw17198Labels = mixedMoment B raw17198step0 raw17198step0Labels := by
      have ha : raw17198step0 = (fun i j => raw17198 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17198step0 raw17198; decide +kernel
      have hl : raw17198step0Labels = raw17198Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17198 raw17198Labels permutation686 permutation2
    mixedMoment B raw17198step0 raw17198step0Labels = mixedMoment B raw17198step1 raw17198step1Labels := by
      have ha : raw17198step1 = -raw17198step0 := by apply Matrix.ext; change ∀ i j, raw17198step1 i j = -(raw17198step0 i j); unfold raw17198step1 raw17198step0; decide +kernel
      have hl : raw17198step1Labels = raw17198step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5073 node5073Labels := by rfl

theorem canonical17199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17199 raw17199Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw17199 raw17199Labels = mixedMoment B raw17199step0 raw17199step0Labels := by
      have ha : raw17199step0 = (fun i j => raw17199 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17199step0 raw17199; decide +kernel
      have hl : raw17199step0Labels = raw17199Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17199 raw17199Labels permutation680 permutation2
    mixedMoment B raw17199step0 raw17199step0Labels = mixedMoment B raw17199step1 raw17199step1Labels := by
      have ha : raw17199step1 = -raw17199step0 := by apply Matrix.ext; change ∀ i j, raw17199step1 i j = -(raw17199step0 i j); unfold raw17199step1 raw17199step0; decide +kernel
      have hl : raw17199step1Labels = raw17199step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5073 node5073Labels := by rfl

theorem canonical17200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17200 raw17200Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw17200 raw17200Labels = mixedMoment B raw17200step0 raw17200step0Labels := by
      have ha : raw17200step0 = (fun i j => raw17200 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17200step0 raw17200; decide +kernel
      have hl : raw17200step0Labels = raw17200Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17200 raw17200Labels permutation682 permutation2
    mixedMoment B raw17200step0 raw17200step0Labels = mixedMoment B raw17200step1 raw17200step1Labels := by
      have ha : raw17200step1 = -raw17200step0 := by apply Matrix.ext; change ∀ i j, raw17200step1 i j = -(raw17200step0 i j); unfold raw17200step1 raw17200step0; decide +kernel
      have hl : raw17200step1Labels = raw17200step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5250 node5250Labels := by rfl

theorem canonical17233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17233 raw17233Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw17233 raw17233Labels = mixedMoment B raw17233step0 raw17233step0Labels := by
      have hz : ∀ j, raw17233 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17233step0 = (fun i j => raw17233 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17233step0 raw17233; decide +kernel
      have hl : raw17233step0Labels = raw17233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17233 raw17233Labels permutation346 hz
    mixedMoment B raw17233step0 raw17233step0Labels = mixedMoment B raw17233step1 raw17233step1Labels := by
      have ha : raw17233step1 = (fun i j => raw17233step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17233step1 raw17233step0; decide +kernel
      have hl : raw17233step1Labels = raw17233step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17233step0 raw17233step0Labels permutation151 permutation7
    mixedMoment B raw17233step1 raw17233step1Labels = mixedMoment B raw17233step2 raw17233step2Labels := by
      have ha : raw17233step2 = -raw17233step1 := by apply Matrix.ext; change ∀ i j, raw17233step2 i j = -(raw17233step1 i j); unfold raw17233step2 raw17233step1; decide +kernel
      have hl : raw17233step2Labels = raw17233step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17233step2 raw17233step2Labels = mixedMoment B raw17233step3 raw17233step3Labels := by
      have ha : raw17233step3 = raw17233step2 := by apply Matrix.ext; unfold raw17233step3 raw17233step2; decide +kernel
      have hl : raw17233step2Labels = labelEmbedding1 ∘ raw17233step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17233step2 raw17233step2Labels raw17233step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

theorem canonical17234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17234 raw17234Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw17234 raw17234Labels = mixedMoment B raw17234step0 raw17234step0Labels := by
      have hz : ∀ j, raw17234 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17234step0 = (fun i j => raw17234 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17234step0 raw17234; decide +kernel
      have hl : raw17234step0Labels = raw17234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17234 raw17234Labels permutation434 hz
    mixedMoment B raw17234step0 raw17234step0Labels = mixedMoment B raw17234step1 raw17234step1Labels := by
      have ha : raw17234step1 = (fun i j => raw17234step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17234step1 raw17234step0; decide +kernel
      have hl : raw17234step1Labels = raw17234step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17234step0 raw17234step0Labels permutation151 permutation7
    mixedMoment B raw17234step1 raw17234step1Labels = mixedMoment B raw17234step2 raw17234step2Labels := by
      have ha : raw17234step2 = -raw17234step1 := by apply Matrix.ext; change ∀ i j, raw17234step2 i j = -(raw17234step1 i j); unfold raw17234step2 raw17234step1; decide +kernel
      have hl : raw17234step2Labels = raw17234step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17234step2 raw17234step2Labels = mixedMoment B raw17234step3 raw17234step3Labels := by
      have ha : raw17234step3 = raw17234step2 := by apply Matrix.ext; unfold raw17234step3 raw17234step2; decide +kernel
      have hl : raw17234step2Labels = labelEmbedding1 ∘ raw17234step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17234step2 raw17234step2Labels raw17234step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

theorem canonical17235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17235 raw17235Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw17235 raw17235Labels = mixedMoment B raw17235step0 raw17235step0Labels := by
      have ha : raw17235step0 = (fun i j => raw17235 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17235step0 raw17235; decide +kernel
      have hl : raw17235step0Labels = raw17235Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17235 raw17235Labels permutation682 permutation7
    mixedMoment B raw17235step0 raw17235step0Labels = mixedMoment B raw17235step1 raw17235step1Labels := by
      have ha : raw17235step1 = -raw17235step0 := by apply Matrix.ext; change ∀ i j, raw17235step1 i j = -(raw17235step0 i j); unfold raw17235step1 raw17235step0; decide +kernel
      have hl : raw17235step1Labels = raw17235step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17235step1 raw17235step1Labels = mixedMoment B raw17235step2 raw17235step2Labels := by
      have ha : raw17235step2 = raw17235step1 := by apply Matrix.ext; unfold raw17235step2 raw17235step1; decide +kernel
      have hl : raw17235step1Labels = labelEmbedding1 ∘ raw17235step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17235step1 raw17235step1Labels raw17235step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3757 node3757Labels := by rfl

theorem canonical17236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17236 raw17236Labels = mixedMoment B node3459 node3459Labels := by
  calc
    mixedMoment B raw17236 raw17236Labels = mixedMoment B raw17236step0 raw17236step0Labels := by
      have ha : raw17236step0 = (fun i j => raw17236 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17236step0 raw17236; decide +kernel
      have hl : raw17236step0Labels = raw17236Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17236 raw17236Labels permutation682 permutation7
    mixedMoment B raw17236step0 raw17236step0Labels = mixedMoment B raw17236step1 raw17236step1Labels := by
      have ha : raw17236step1 = -raw17236step0 := by apply Matrix.ext; change ∀ i j, raw17236step1 i j = -(raw17236step0 i j); unfold raw17236step1 raw17236step0; decide +kernel
      have hl : raw17236step1Labels = raw17236step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17236step1 raw17236step1Labels = mixedMoment B raw17236step2 raw17236step2Labels := by
      have ha : raw17236step2 = raw17236step1 := by apply Matrix.ext; unfold raw17236step2 raw17236step1; decide +kernel
      have hl : raw17236step1Labels = labelEmbedding1 ∘ raw17236step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17236step1 raw17236step1Labels raw17236step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3459 node3459Labels := by rfl

theorem canonical17237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17237 raw17237Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw17237 raw17237Labels = mixedMoment B raw17237step0 raw17237step0Labels := by
      have hz : ∀ j, raw17237 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17237step0 = (fun i j => raw17237 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17237step0 raw17237; decide +kernel
      have hl : raw17237step0Labels = raw17237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17237 raw17237Labels permutation434 hz
    mixedMoment B raw17237step0 raw17237step0Labels = mixedMoment B raw17237step1 raw17237step1Labels := by
      have ha : raw17237step1 = (fun i j => raw17237step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17237step1 raw17237step0; decide +kernel
      have hl : raw17237step1Labels = raw17237step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17237step0 raw17237step0Labels permutation151 permutation7
    mixedMoment B raw17237step1 raw17237step1Labels = mixedMoment B raw17237step2 raw17237step2Labels := by
      have ha : raw17237step2 = -raw17237step1 := by apply Matrix.ext; change ∀ i j, raw17237step2 i j = -(raw17237step1 i j); unfold raw17237step2 raw17237step1; decide +kernel
      have hl : raw17237step2Labels = raw17237step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17237step2 raw17237step2Labels = mixedMoment B raw17237step3 raw17237step3Labels := by
      have ha : raw17237step3 = raw17237step2 := by apply Matrix.ext; unfold raw17237step3 raw17237step2; decide +kernel
      have hl : raw17237step2Labels = labelEmbedding1 ∘ raw17237step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17237step2 raw17237step2Labels raw17237step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

theorem canonical17238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17238 raw17238Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw17238 raw17238Labels = mixedMoment B raw17238step0 raw17238step0Labels := by
      have ha : raw17238step0 = (fun i j => raw17238 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17238step0 raw17238; decide +kernel
      have hl : raw17238step0Labels = raw17238Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17238 raw17238Labels permutation688 permutation7
    mixedMoment B raw17238step0 raw17238step0Labels = mixedMoment B raw17238step1 raw17238step1Labels := by
      have ha : raw17238step1 = -raw17238step0 := by apply Matrix.ext; change ∀ i j, raw17238step1 i j = -(raw17238step0 i j); unfold raw17238step1 raw17238step0; decide +kernel
      have hl : raw17238step1Labels = raw17238step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17238step1 raw17238step1Labels = mixedMoment B raw17238step2 raw17238step2Labels := by
      have ha : raw17238step2 = raw17238step1 := by apply Matrix.ext; unfold raw17238step2 raw17238step1; decide +kernel
      have hl : raw17238step1Labels = labelEmbedding1 ∘ raw17238step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17238step1 raw17238step1Labels raw17238step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

theorem canonical17239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17239 raw17239Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw17239 raw17239Labels = mixedMoment B raw17239step0 raw17239step0Labels := by
      have ha : raw17239step0 = (fun i j => raw17239 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17239step0 raw17239; decide +kernel
      have hl : raw17239step0Labels = raw17239Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17239 raw17239Labels permutation688 permutation7
    mixedMoment B raw17239step0 raw17239step0Labels = mixedMoment B raw17239step1 raw17239step1Labels := by
      have ha : raw17239step1 = -raw17239step0 := by apply Matrix.ext; change ∀ i j, raw17239step1 i j = -(raw17239step0 i j); unfold raw17239step1 raw17239step0; decide +kernel
      have hl : raw17239step1Labels = raw17239step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17239step1 raw17239step1Labels = mixedMoment B raw17239step2 raw17239step2Labels := by
      have ha : raw17239step2 = raw17239step1 := by apply Matrix.ext; unfold raw17239step2 raw17239step1; decide +kernel
      have hl : raw17239step1Labels = labelEmbedding1 ∘ raw17239step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17239step1 raw17239step1Labels raw17239step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

theorem canonical17240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17240 raw17240Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw17240 raw17240Labels = mixedMoment B raw17240step0 raw17240step0Labels := by
      have hz : ∀ j, raw17240 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17240step0 = (fun i j => raw17240 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17240step0 raw17240; decide +kernel
      have hl : raw17240step0Labels = raw17240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17240 raw17240Labels permutation346 hz
    mixedMoment B raw17240step0 raw17240step0Labels = mixedMoment B raw17240step1 raw17240step1Labels := by
      have ha : raw17240step1 = (fun i j => raw17240step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17240step1 raw17240step0; decide +kernel
      have hl : raw17240step1Labels = raw17240step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17240step0 raw17240step0Labels permutation151 permutation7
    mixedMoment B raw17240step1 raw17240step1Labels = mixedMoment B raw17240step2 raw17240step2Labels := by
      have ha : raw17240step2 = -raw17240step1 := by apply Matrix.ext; change ∀ i j, raw17240step2 i j = -(raw17240step1 i j); unfold raw17240step2 raw17240step1; decide +kernel
      have hl : raw17240step2Labels = raw17240step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17240step2 raw17240step2Labels = mixedMoment B raw17240step3 raw17240step3Labels := by
      have ha : raw17240step3 = raw17240step2 := by apply Matrix.ext; unfold raw17240step3 raw17240step2; decide +kernel
      have hl : raw17240step2Labels = labelEmbedding1 ∘ raw17240step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17240step2 raw17240step2Labels raw17240step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

theorem canonical17241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17241 raw17241Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw17241 raw17241Labels = mixedMoment B raw17241step0 raw17241step0Labels := by
      have ha : raw17241step0 = (fun i j => raw17241 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17241step0 raw17241; decide +kernel
      have hl : raw17241step0Labels = raw17241Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17241 raw17241Labels permutation682 permutation7
    mixedMoment B raw17241step0 raw17241step0Labels = mixedMoment B raw17241step1 raw17241step1Labels := by
      have ha : raw17241step1 = -raw17241step0 := by apply Matrix.ext; change ∀ i j, raw17241step1 i j = -(raw17241step0 i j); unfold raw17241step1 raw17241step0; decide +kernel
      have hl : raw17241step1Labels = raw17241step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17241step1 raw17241step1Labels = mixedMoment B raw17241step2 raw17241step2Labels := by
      have ha : raw17241step2 = raw17241step1 := by apply Matrix.ext; unfold raw17241step2 raw17241step1; decide +kernel
      have hl : raw17241step1Labels = labelEmbedding1 ∘ raw17241step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17241step1 raw17241step1Labels raw17241step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

theorem canonical17242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17242 raw17242Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw17242 raw17242Labels = mixedMoment B raw17242step0 raw17242step0Labels := by
      have ha : raw17242step0 = (fun i j => raw17242 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17242step0 raw17242; decide +kernel
      have hl : raw17242step0Labels = raw17242Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17242 raw17242Labels permutation682 permutation7
    mixedMoment B raw17242step0 raw17242step0Labels = mixedMoment B raw17242step1 raw17242step1Labels := by
      have ha : raw17242step1 = -raw17242step0 := by apply Matrix.ext; change ∀ i j, raw17242step1 i j = -(raw17242step0 i j); unfold raw17242step1 raw17242step0; decide +kernel
      have hl : raw17242step1Labels = raw17242step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17242step1 raw17242step1Labels = mixedMoment B raw17242step2 raw17242step2Labels := by
      have ha : raw17242step2 = raw17242step1 := by apply Matrix.ext; unfold raw17242step2 raw17242step1; decide +kernel
      have hl : raw17242step1Labels = labelEmbedding1 ∘ raw17242step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17242step1 raw17242step1Labels raw17242step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

theorem canonical17243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17243 raw17243Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw17243 raw17243Labels = mixedMoment B raw17243step0 raw17243step0Labels := by
      have hz : ∀ j, raw17243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17243step0 = (fun i j => raw17243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17243step0 raw17243; decide +kernel
      have hl : raw17243step0Labels = raw17243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17243 raw17243Labels permutation346 hz
    mixedMoment B raw17243step0 raw17243step0Labels = mixedMoment B raw17243step1 raw17243step1Labels := by
      have ha : raw17243step1 = (fun i j => raw17243step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17243step1 raw17243step0; decide +kernel
      have hl : raw17243step1Labels = raw17243step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17243step0 raw17243step0Labels permutation151 permutation7
    mixedMoment B raw17243step1 raw17243step1Labels = mixedMoment B raw17243step2 raw17243step2Labels := by
      have ha : raw17243step2 = -raw17243step1 := by apply Matrix.ext; change ∀ i j, raw17243step2 i j = -(raw17243step1 i j); unfold raw17243step2 raw17243step1; decide +kernel
      have hl : raw17243step2Labels = raw17243step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17243step2 raw17243step2Labels = mixedMoment B raw17243step3 raw17243step3Labels := by
      have ha : raw17243step3 = raw17243step2 := by apply Matrix.ext; unfold raw17243step3 raw17243step2; decide +kernel
      have hl : raw17243step2Labels = labelEmbedding1 ∘ raw17243step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17243step2 raw17243step2Labels raw17243step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

theorem canonical17244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17244 raw17244Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw17244 raw17244Labels = mixedMoment B raw17244step0 raw17244step0Labels := by
      have hz : ∀ j, raw17244 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17244step0 = (fun i j => raw17244 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17244step0 raw17244; decide +kernel
      have hl : raw17244step0Labels = raw17244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17244 raw17244Labels permutation434 hz
    mixedMoment B raw17244step0 raw17244step0Labels = mixedMoment B raw17244step1 raw17244step1Labels := by
      have ha : raw17244step1 = (fun i j => raw17244step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17244step1 raw17244step0; decide +kernel
      have hl : raw17244step1Labels = raw17244step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17244step0 raw17244step0Labels permutation151 permutation7
    mixedMoment B raw17244step1 raw17244step1Labels = mixedMoment B raw17244step2 raw17244step2Labels := by
      have ha : raw17244step2 = -raw17244step1 := by apply Matrix.ext; change ∀ i j, raw17244step2 i j = -(raw17244step1 i j); unfold raw17244step2 raw17244step1; decide +kernel
      have hl : raw17244step2Labels = raw17244step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17244step2 raw17244step2Labels = mixedMoment B raw17244step3 raw17244step3Labels := by
      have ha : raw17244step3 = raw17244step2 := by apply Matrix.ext; unfold raw17244step3 raw17244step2; decide +kernel
      have hl : raw17244step2Labels = labelEmbedding1 ∘ raw17244step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17244step2 raw17244step2Labels raw17244step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

theorem canonical17245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17245 raw17245Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw17245 raw17245Labels = mixedMoment B raw17245step0 raw17245step0Labels := by
      have ha : raw17245step0 = (fun i j => raw17245 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17245step0 raw17245; decide +kernel
      have hl : raw17245step0Labels = raw17245Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17245 raw17245Labels permutation682 permutation7
    mixedMoment B raw17245step0 raw17245step0Labels = mixedMoment B raw17245step1 raw17245step1Labels := by
      have ha : raw17245step1 = -raw17245step0 := by apply Matrix.ext; change ∀ i j, raw17245step1 i j = -(raw17245step0 i j); unfold raw17245step1 raw17245step0; decide +kernel
      have hl : raw17245step1Labels = raw17245step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17245step1 raw17245step1Labels = mixedMoment B raw17245step2 raw17245step2Labels := by
      have ha : raw17245step2 = raw17245step1 := by apply Matrix.ext; unfold raw17245step2 raw17245step1; decide +kernel
      have hl : raw17245step1Labels = labelEmbedding1 ∘ raw17245step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17245step1 raw17245step1Labels raw17245step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3525 node3525Labels := by rfl

theorem canonical17246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17246 raw17246Labels = mixedMoment B node3976 node3976Labels := by
  calc
    mixedMoment B raw17246 raw17246Labels = mixedMoment B raw17246step0 raw17246step0Labels := by
      have ha : raw17246step0 = (fun i j => raw17246 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17246step0 raw17246; decide +kernel
      have hl : raw17246step0Labels = raw17246Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17246 raw17246Labels permutation682 permutation7
    mixedMoment B raw17246step0 raw17246step0Labels = mixedMoment B raw17246step1 raw17246step1Labels := by
      have ha : raw17246step1 = -raw17246step0 := by apply Matrix.ext; change ∀ i j, raw17246step1 i j = -(raw17246step0 i j); unfold raw17246step1 raw17246step0; decide +kernel
      have hl : raw17246step1Labels = raw17246step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17246step1 raw17246step1Labels = mixedMoment B raw17246step2 raw17246step2Labels := by
      have ha : raw17246step2 = raw17246step1 := by apply Matrix.ext; unfold raw17246step2 raw17246step1; decide +kernel
      have hl : raw17246step1Labels = labelEmbedding1 ∘ raw17246step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17246step1 raw17246step1Labels raw17246step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3976 node3976Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical135
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17307 raw17307Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw17307 raw17307Labels = mixedMoment B raw17307step0 raw17307step0Labels := by
      have hz : ∀ j, raw17307 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17307step0 = (fun i j => raw17307 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17307step0 raw17307; decide +kernel
      have hl : raw17307step0Labels = raw17307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17307 raw17307Labels permutation434 hz
    mixedMoment B raw17307step0 raw17307step0Labels = mixedMoment B raw17307step1 raw17307step1Labels := by
      have ha : raw17307step1 = (fun i j => raw17307step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17307step1 raw17307step0; decide +kernel
      have hl : raw17307step1Labels = raw17307step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17307step0 raw17307step0Labels permutation150 permutation2
    mixedMoment B raw17307step1 raw17307step1Labels = mixedMoment B raw17307step2 raw17307step2Labels := by
      have ha : raw17307step2 = -raw17307step1 := by apply Matrix.ext; change ∀ i j, raw17307step2 i j = -(raw17307step1 i j); unfold raw17307step2 raw17307step1; decide +kernel
      have hl : raw17307step2Labels = raw17307step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

theorem canonical17308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17308 raw17308Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw17308 raw17308Labels = mixedMoment B raw17308step0 raw17308step0Labels := by
      have hz : ∀ j, raw17308 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17308step0 = (fun i j => raw17308 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17308step0 raw17308; decide +kernel
      have hl : raw17308step0Labels = raw17308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17308 raw17308Labels permutation434 hz
    mixedMoment B raw17308step0 raw17308step0Labels = mixedMoment B raw17308step1 raw17308step1Labels := by
      have ha : raw17308step1 = (fun i j => raw17308step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17308step1 raw17308step0; decide +kernel
      have hl : raw17308step1Labels = raw17308step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17308step0 raw17308step0Labels permutation151 permutation2
    mixedMoment B raw17308step1 raw17308step1Labels = mixedMoment B raw17308step2 raw17308step2Labels := by
      have ha : raw17308step2 = -raw17308step1 := by apply Matrix.ext; change ∀ i j, raw17308step2 i j = -(raw17308step1 i j); unfold raw17308step2 raw17308step1; decide +kernel
      have hl : raw17308step2Labels = raw17308step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

theorem canonical17309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17309 raw17309Labels = mixedMoment B node3790 node3790Labels := by
  calc
    mixedMoment B raw17309 raw17309Labels = mixedMoment B raw17309step0 raw17309step0Labels := by
      have hz : ∀ j, raw17309 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17309step0 = (fun i j => raw17309 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17309step0 raw17309; decide +kernel
      have hl : raw17309step0Labels = raw17309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17309 raw17309Labels permutation434 hz
    mixedMoment B raw17309step0 raw17309step0Labels = mixedMoment B raw17309step1 raw17309step1Labels := by
      have ha : raw17309step1 = (fun i j => raw17309step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17309step1 raw17309step0; decide +kernel
      have hl : raw17309step1Labels = raw17309step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17309step0 raw17309step0Labels permutation144 permutation2
    mixedMoment B raw17309step1 raw17309step1Labels = mixedMoment B raw17309step2 raw17309step2Labels := by
      have ha : raw17309step2 = -raw17309step1 := by apply Matrix.ext; change ∀ i j, raw17309step2 i j = -(raw17309step1 i j); unfold raw17309step2 raw17309step1; decide +kernel
      have hl : raw17309step2Labels = raw17309step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3790 node3790Labels := by rfl

theorem canonical17310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17310 raw17310Labels = mixedMoment B node3825 node3825Labels := by
  calc
    mixedMoment B raw17310 raw17310Labels = mixedMoment B raw17310step0 raw17310step0Labels := by
      have ha : raw17310step0 = (fun i j => raw17310 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17310step0 raw17310; decide +kernel
      have hl : raw17310step0Labels = raw17310Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17310 raw17310Labels permutation663 permutation2
    mixedMoment B raw17310step0 raw17310step0Labels = mixedMoment B raw17310step1 raw17310step1Labels := by
      have ha : raw17310step1 = -raw17310step0 := by apply Matrix.ext; change ∀ i j, raw17310step1 i j = -(raw17310step0 i j); unfold raw17310step1 raw17310step0; decide +kernel
      have hl : raw17310step1Labels = raw17310step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3825 node3825Labels := by rfl

theorem canonical17311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17311 raw17311Labels = mixedMoment B node3115 node3115Labels := by
  calc
    mixedMoment B raw17311 raw17311Labels = mixedMoment B raw17311step0 raw17311step0Labels := by
      have hz : ∀ j, raw17311 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17311step0 = (fun i j => raw17311 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17311step0 raw17311; decide +kernel
      have hl : raw17311step0Labels = raw17311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17311 raw17311Labels permutation434 hz
    mixedMoment B raw17311step0 raw17311step0Labels = mixedMoment B raw17311step1 raw17311step1Labels := by
      have ha : raw17311step1 = (fun i j => raw17311step0 (permutation122 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17311step1 raw17311step0; decide +kernel
      have hl : raw17311step1Labels = raw17311step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17311step0 raw17311step0Labels permutation122 permutation4
    _ = mixedMoment B node3115 node3115Labels := by rfl

theorem canonical17312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17312 raw17312Labels = mixedMoment B node2621 node2621Labels := by
  calc
    mixedMoment B raw17312 raw17312Labels = mixedMoment B raw17312step0 raw17312step0Labels := by
      have hz : ∀ j, raw17312 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17312step0 = (fun i j => raw17312 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17312step0 raw17312; decide +kernel
      have hl : raw17312step0Labels = raw17312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17312 raw17312Labels permutation434 hz
    mixedMoment B raw17312step0 raw17312step0Labels = mixedMoment B raw17312step1 raw17312step1Labels := by
      have ha : raw17312step1 = (fun i j => raw17312step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17312step1 raw17312step0; decide +kernel
      have hl : raw17312step1Labels = raw17312step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17312step0 raw17312step0Labels permutation150 permutation2
    mixedMoment B raw17312step1 raw17312step1Labels = mixedMoment B raw17312step2 raw17312step2Labels := by
      have ha : raw17312step2 = -raw17312step1 := by apply Matrix.ext; change ∀ i j, raw17312step2 i j = -(raw17312step1 i j); unfold raw17312step2 raw17312step1; decide +kernel
      have hl : raw17312step2Labels = raw17312step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2621 node2621Labels := by rfl

theorem canonical17313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17313 raw17313Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw17313 raw17313Labels = mixedMoment B raw17313step0 raw17313step0Labels := by
      have hz : ∀ j, raw17313 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17313step0 = (fun i j => raw17313 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17313step0 raw17313; decide +kernel
      have hl : raw17313step0Labels = raw17313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17313 raw17313Labels permutation434 hz
    mixedMoment B raw17313step0 raw17313step0Labels = mixedMoment B raw17313step1 raw17313step1Labels := by
      have ha : raw17313step1 = (fun i j => raw17313step0 (permutation140 i) (permutation0 j)) := by apply Matrix.ext; unfold raw17313step1 raw17313step0; decide +kernel
      have hl : raw17313step1Labels = raw17313step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17313step0 raw17313step0Labels permutation140 permutation0
    mixedMoment B raw17313step1 raw17313step1Labels = mixedMoment B raw17313step2 raw17313step2Labels := by
      have ha : raw17313step2 = -raw17313step1 := by apply Matrix.ext; change ∀ i j, raw17313step2 i j = -(raw17313step1 i j); unfold raw17313step2 raw17313step1; decide +kernel
      have hl : raw17313step2Labels = raw17313step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

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

theorem canonical2430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2430 raw2430Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw2430 raw2430Labels = mixedMoment B raw2430step0 raw2430step0Labels := by
      have ha : raw2430step0 = (fun i j => raw2430 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2430step0 raw2430; decide +kernel
      have hl : raw2430step0Labels = raw2430Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2430 raw2430Labels permutation152 permutation4
    mixedMoment B raw2430step0 raw2430step0Labels = mixedMoment B raw2430step1 raw2430step1Labels := by
      have ha : raw2430step1 = raw2430step0 := by apply Matrix.ext; unfold raw2430step1 raw2430step0; decide +kernel
      have hl : raw2430step0Labels = labelEmbedding7 ∘ raw2430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2430step0 raw2430step0Labels raw2430step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical2431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2431 raw2431Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw2431 raw2431Labels = mixedMoment B raw2431step0 raw2431step0Labels := by
      have ha : raw2431step0 = (fun i j => raw2431 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2431step0 raw2431; decide +kernel
      have hl : raw2431step0Labels = raw2431Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2431 raw2431Labels permutation152 permutation4
    _ = mixedMoment B node3719 node3719Labels := by rfl

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

theorem canonical2432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2432 raw2432Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw2432 raw2432Labels = mixedMoment B raw2432step0 raw2432step0Labels := by
      have ha : raw2432step0 = (fun i j => raw2432 (permutation686 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2432step0 raw2432; decide +kernel
      have hl : raw2432step0Labels = raw2432Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2432 raw2432Labels permutation686 permutation6
    mixedMoment B raw2432step0 raw2432step0Labels = mixedMoment B raw2432step1 raw2432step1Labels := by
      have ha : raw2432step1 = raw2432step0 := by apply Matrix.ext; unfold raw2432step1 raw2432step0; decide +kernel
      have hl : raw2432step0Labels = labelEmbedding1 ∘ raw2432step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2432step0 raw2432step0Labels raw2432step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

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

theorem canonical2475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2475 raw2475Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw2475 raw2475Labels = mixedMoment B raw2475step0 raw2475step0Labels := by
      have ha : raw2475step0 = (fun i j => raw2475 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2475step0 raw2475; decide +kernel
      have hl : raw2475step0Labels = raw2475Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2475 raw2475Labels permutation152 permutation4
    mixedMoment B raw2475step0 raw2475step0Labels = mixedMoment B raw2475step1 raw2475step1Labels := by
      have ha : raw2475step1 = raw2475step0 := by apply Matrix.ext; unfold raw2475step1 raw2475step0; decide +kernel
      have hl : raw2475step0Labels = labelEmbedding7 ∘ raw2475step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2475step0 raw2475step0Labels raw2475step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

theorem canonical2476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2476 raw2476Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw2476 raw2476Labels = mixedMoment B raw2476step0 raw2476step0Labels := by
      have ha : raw2476step0 = (fun i j => raw2476 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2476step0 raw2476; decide +kernel
      have hl : raw2476step0Labels = raw2476Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2476 raw2476Labels permutation152 permutation4
    _ = mixedMoment B node3787 node3787Labels := by rfl

theorem canonical2477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2477 raw2477Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw2477 raw2477Labels = mixedMoment B raw2477step0 raw2477step0Labels := by
      have ha : raw2477step0 = (fun i j => raw2477 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2477step0 raw2477; decide +kernel
      have hl : raw2477step0Labels = raw2477Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2477 raw2477Labels permutation158 permutation6
    mixedMoment B raw2477step0 raw2477step0Labels = mixedMoment B raw2477step1 raw2477step1Labels := by
      have ha : raw2477step1 = -raw2477step0 := by apply Matrix.ext; change ∀ i j, raw2477step1 i j = -(raw2477step0 i j); unfold raw2477step1 raw2477step0; decide +kernel
      have hl : raw2477step1Labels = raw2477step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2477step1 raw2477step1Labels = mixedMoment B raw2477step2 raw2477step2Labels := by
      have ha : raw2477step2 = raw2477step1 := by apply Matrix.ext; unfold raw2477step2 raw2477step1; decide +kernel
      have hl : raw2477step1Labels = labelEmbedding1 ∘ raw2477step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2477step1 raw2477step1Labels raw2477step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

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

theorem canonical2514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2514 raw2514Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw2514 raw2514Labels = mixedMoment B raw2514step0 raw2514step0Labels := by
      have ha : raw2514step0 = (fun i j => raw2514 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2514step0 raw2514; decide +kernel
      have hl : raw2514step0Labels = raw2514Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2514 raw2514Labels permutation152 permutation4
    mixedMoment B raw2514step0 raw2514step0Labels = mixedMoment B raw2514step1 raw2514step1Labels := by
      have ha : raw2514step1 = raw2514step0 := by apply Matrix.ext; unfold raw2514step1 raw2514step0; decide +kernel
      have hl : raw2514step0Labels = labelEmbedding7 ∘ raw2514step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2514step0 raw2514step0Labels raw2514step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical2515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2515 raw2515Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw2515 raw2515Labels = mixedMoment B raw2515step0 raw2515step0Labels := by
      have ha : raw2515step0 = (fun i j => raw2515 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2515step0 raw2515; decide +kernel
      have hl : raw2515step0Labels = raw2515Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2515 raw2515Labels permutation152 permutation4
    _ = mixedMoment B node3838 node3838Labels := by rfl

theorem canonical2516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2516 raw2516Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw2516 raw2516Labels = mixedMoment B raw2516step0 raw2516step0Labels := by
      have ha : raw2516step0 = (fun i j => raw2516 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2516step0 raw2516; decide +kernel
      have hl : raw2516step0Labels = raw2516Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2516 raw2516Labels permutation176 permutation6
    mixedMoment B raw2516step0 raw2516step0Labels = mixedMoment B raw2516step1 raw2516step1Labels := by
      have ha : raw2516step1 = -raw2516step0 := by apply Matrix.ext; change ∀ i j, raw2516step1 i j = -(raw2516step0 i j); unfold raw2516step1 raw2516step0; decide +kernel
      have hl : raw2516step1Labels = raw2516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2516step1 raw2516step1Labels = mixedMoment B raw2516step2 raw2516step2Labels := by
      have ha : raw2516step2 = raw2516step1 := by apply Matrix.ext; unfold raw2516step2 raw2516step1; decide +kernel
      have hl : raw2516step1Labels = labelEmbedding1 ∘ raw2516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2516step1 raw2516step1Labels raw2516step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9129 raw9129Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw9129 raw9129Labels = mixedMoment B raw9129step0 raw9129step0Labels := by
      have hz : ∀ j, raw9129 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9129step0 = (fun i j => raw9129 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9129step0 raw9129; decide +kernel
      have hl : raw9129step0Labels = raw9129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9129 raw9129Labels permutation265 hz
    mixedMoment B raw9129step0 raw9129step0Labels = mixedMoment B raw9129step1 raw9129step1Labels := by
      have ha : raw9129step1 = (fun i j => raw9129step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9129step1 raw9129step0; decide +kernel
      have hl : raw9129step1Labels = raw9129step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9129step0 raw9129step0Labels permutation151 permutation2
    mixedMoment B raw9129step1 raw9129step1Labels = mixedMoment B raw9129step2 raw9129step2Labels := by
      have ha : raw9129step2 = -raw9129step1 := by apply Matrix.ext; change ∀ i j, raw9129step2 i j = -(raw9129step1 i j); unfold raw9129step2 raw9129step1; decide +kernel
      have hl : raw9129step2Labels = raw9129step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5410 node5410Labels := by rfl

theorem canonical9130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9130 raw9130Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw9130 raw9130Labels = mixedMoment B raw9130step0 raw9130step0Labels := by
      have hz : ∀ j, raw9130 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9130step0 = (fun i j => raw9130 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9130step0 raw9130; decide +kernel
      have hl : raw9130step0Labels = raw9130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9130 raw9130Labels permutation265 hz
    mixedMoment B raw9130step0 raw9130step0Labels = mixedMoment B raw9130step1 raw9130step1Labels := by
      have ha : raw9130step1 = (fun i j => raw9130step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9130step1 raw9130step0; decide +kernel
      have hl : raw9130step1Labels = raw9130step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9130step0 raw9130step0Labels permutation149 permutation2
    mixedMoment B raw9130step1 raw9130step1Labels = mixedMoment B raw9130step2 raw9130step2Labels := by
      have ha : raw9130step2 = -raw9130step1 := by apply Matrix.ext; change ∀ i j, raw9130step2 i j = -(raw9130step1 i j); unfold raw9130step2 raw9130step1; decide +kernel
      have hl : raw9130step2Labels = raw9130step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5410 node5410Labels := by rfl

theorem canonical9131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9131 raw9131Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw9131 raw9131Labels = mixedMoment B raw9131step0 raw9131step0Labels := by
      have hz : ∀ j, raw9131 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9131step0 = (fun i j => raw9131 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9131step0 raw9131; decide +kernel
      have hl : raw9131step0Labels = raw9131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9131 raw9131Labels permutation265 hz
    mixedMoment B raw9131step0 raw9131step0Labels = mixedMoment B raw9131step1 raw9131step1Labels := by
      have ha : raw9131step1 = (fun i j => raw9131step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9131step1 raw9131step0; decide +kernel
      have hl : raw9131step1Labels = raw9131step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9131step0 raw9131step0Labels permutation149 permutation7
    mixedMoment B raw9131step1 raw9131step1Labels = mixedMoment B raw9131step2 raw9131step2Labels := by
      have ha : raw9131step2 = raw9131step1 := by apply Matrix.ext; unfold raw9131step2 raw9131step1; decide +kernel
      have hl : raw9131step1Labels = labelEmbedding10 ∘ raw9131step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9131step1 raw9131step1Labels raw9131step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical9132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9132 raw9132Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw9132 raw9132Labels = mixedMoment B raw9132step0 raw9132step0Labels := by
      have hz : ∀ j, raw9132 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9132step0 = (fun i j => raw9132 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9132step0 raw9132; decide +kernel
      have hl : raw9132step0Labels = raw9132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9132 raw9132Labels permutation265 hz
    mixedMoment B raw9132step0 raw9132step0Labels = mixedMoment B raw9132step1 raw9132step1Labels := by
      have ha : raw9132step1 = (fun i j => raw9132step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9132step1 raw9132step0; decide +kernel
      have hl : raw9132step1Labels = raw9132step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9132step0 raw9132step0Labels permutation149 permutation7
    mixedMoment B raw9132step1 raw9132step1Labels = mixedMoment B raw9132step2 raw9132step2Labels := by
      have ha : raw9132step2 = raw9132step1 := by apply Matrix.ext; unfold raw9132step2 raw9132step1; decide +kernel
      have hl : raw9132step1Labels = labelEmbedding10 ∘ raw9132step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9132step1 raw9132step1Labels raw9132step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

theorem canonical9139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9139 raw9139Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw9139 raw9139Labels = mixedMoment B raw9139step0 raw9139step0Labels := by
      have ha : raw9139step0 = (fun i j => raw9139 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9139step0 raw9139; decide +kernel
      have hl : raw9139step0Labels = raw9139Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9139 raw9139Labels permutation160 permutation3
    mixedMoment B raw9139step0 raw9139step0Labels = mixedMoment B raw9139step1 raw9139step1Labels := by
      have ha : raw9139step1 = raw9139step0 := by apply Matrix.ext; unfold raw9139step1 raw9139step0; decide +kernel
      have hl : raw9139step0Labels = labelEmbedding6 ∘ raw9139step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9139step0 raw9139step0Labels raw9139step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5074 node5074Labels := by rfl

theorem canonical9144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9144 raw9144Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw9144 raw9144Labels = mixedMoment B raw9144step0 raw9144step0Labels := by
      have ha : raw9144step0 = (fun i j => raw9144 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9144step0 raw9144; decide +kernel
      have hl : raw9144step0Labels = raw9144Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9144 raw9144Labels permutation154 permutation3
    mixedMoment B raw9144step0 raw9144step0Labels = mixedMoment B raw9144step1 raw9144step1Labels := by
      have ha : raw9144step1 = raw9144step0 := by apply Matrix.ext; unfold raw9144step1 raw9144step0; decide +kernel
      have hl : raw9144step0Labels = labelEmbedding6 ∘ raw9144step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9144step0 raw9144step0Labels raw9144step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5074 node5074Labels := by rfl

theorem canonical9149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9149 raw9149Labels = mixedMoment B node5067 node5067Labels := by
  calc
    mixedMoment B raw9149 raw9149Labels = mixedMoment B raw9149step0 raw9149step0Labels := by
      have ha : raw9149step0 = (fun i j => raw9149 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9149step0 raw9149; decide +kernel
      have hl : raw9149step0Labels = raw9149Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9149 raw9149Labels permutation153 permutation3
    mixedMoment B raw9149step0 raw9149step0Labels = mixedMoment B raw9149step1 raw9149step1Labels := by
      have ha : raw9149step1 = raw9149step0 := by apply Matrix.ext; unfold raw9149step1 raw9149step0; decide +kernel
      have hl : raw9149step0Labels = labelEmbedding6 ∘ raw9149step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9149step0 raw9149step0Labels raw9149step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5067 node5067Labels := by rfl

theorem canonical9154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9154 raw9154Labels = mixedMoment B node5065 node5065Labels := by
  calc
    mixedMoment B raw9154 raw9154Labels = mixedMoment B raw9154step0 raw9154step0Labels := by
      have ha : raw9154step0 = (fun i j => raw9154 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9154step0 raw9154; decide +kernel
      have hl : raw9154step0Labels = raw9154Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9154 raw9154Labels permutation682 permutation2
    mixedMoment B raw9154step0 raw9154step0Labels = mixedMoment B raw9154step1 raw9154step1Labels := by
      have ha : raw9154step1 = -raw9154step0 := by apply Matrix.ext; change ∀ i j, raw9154step1 i j = -(raw9154step0 i j); unfold raw9154step1 raw9154step0; decide +kernel
      have hl : raw9154step1Labels = raw9154step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5065 node5065Labels := by rfl

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

theorem singleton5378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5378 node5378Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3719 node3719Labels + mixedMoment B node3795 node3795Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2430 singletonSmall5378
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5378) = raw2430Labels := by decide +kernel
  rw [hl, canonical2430 B hB] at h
  have hc0 : mixedMoment B raw2430 (Fin.cases (0 : Fin 2) singletonSmall5378) =
      mixedMoment B node3719 node3719Labels := by
    have ha : raw2430 = raw2431 := by apply Matrix.ext; unfold raw2430 raw2431; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5378 = raw2431Labels := by decide +kernel
    rw [ha, hj, canonical2431 B hB]
  have hc1 : mixedMoment B raw2430 (Fin.cases (1 : Fin 2) singletonSmall5378) =
      mixedMoment B node3795 node3795Labels := by
    have ha : raw2430 = raw2432 := by apply Matrix.ext; unfold raw2430 raw2432; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5378 = raw2432Labels := by decide +kernel
    rw [ha, hj, canonical2432 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5401 node5401Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3787 node3787Labels + mixedMoment B node3804 node3804Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2475 singletonSmall5401
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5401) = raw2475Labels := by decide +kernel
  rw [hl, canonical2475 B hB] at h
  have hc0 : mixedMoment B raw2475 (Fin.cases (0 : Fin 2) singletonSmall5401) =
      mixedMoment B node3787 node3787Labels := by
    have ha : raw2475 = raw2476 := by apply Matrix.ext; unfold raw2475 raw2476; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5401 = raw2476Labels := by decide +kernel
    rw [ha, hj, canonical2476 B hB]
  have hc1 : mixedMoment B raw2475 (Fin.cases (1 : Fin 2) singletonSmall5401) =
      mixedMoment B node3804 node3804Labels := by
    have ha : raw2475 = raw2477 := by apply Matrix.ext; unfold raw2475 raw2477; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5401 = raw2477Labels := by decide +kernel
    rw [ha, hj, canonical2477 B hB]
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

theorem singleton5424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5424 node5424Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3838 node3838Labels + mixedMoment B node3843 node3843Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2514 singletonSmall5424
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5424) = raw2514Labels := by decide +kernel
  rw [hl, canonical2514 B hB] at h
  have hc0 : mixedMoment B raw2514 (Fin.cases (0 : Fin 2) singletonSmall5424) =
      mixedMoment B node3838 node3838Labels := by
    have ha : raw2514 = raw2515 := by apply Matrix.ext; unfold raw2514 raw2515; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5424 = raw2515Labels := by decide +kernel
    rw [ha, hj, canonical2515 B hB]
  have hc1 : mixedMoment B raw2514 (Fin.cases (1 : Fin 2) singletonSmall5424) =
      mixedMoment B node3843 node3843Labels := by
    have ha : raw2514 = raw2516 := by apply Matrix.ext; unfold raw2514 raw2516; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5424 = raw2516Labels := by decide +kernel
    rw [ha, hj, canonical2516 B hB]
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

theorem zero5471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5471 node5471Labels = 0 := by
  exact mixedMoment_alpha B hF node5471 node5471Labels 1 permutation200
    (by decide +kernel)

theorem zero5477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5477 node5477Labels = 0 := by
  exact mixedMoment_alpha B hF node5477 node5477Labels 2 permutation152
    (by decide +kernel)

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

theorem sound2621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2621 node2621Labels = Sparse.eval nodeValue2621 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2621) = mixedMoment B node2621 node2621Labels := rfl
  simpa [nodeValue2621, Sparse.eval] using hc.symm

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

theorem sound3077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3077 node3077Labels = Sparse.eval nodeValue3077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3077) = mixedMoment B node3077 node3077Labels := rfl
  simpa [nodeValue3077, Sparse.eval] using hc.symm

theorem sound3115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3115 node3115Labels = Sparse.eval nodeValue3115 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3115) = mixedMoment B node3115 node3115Labels := rfl
  simpa [nodeValue3115, Sparse.eval] using hc.symm

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

theorem sound3459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3459 node3459Labels = Sparse.eval nodeValue3459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3459) = mixedMoment B node3459 node3459Labels := rfl
  simpa [nodeValue3459, Sparse.eval] using hc.symm

theorem sound3460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3460 node3460Labels = Sparse.eval nodeValue3460 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3460) = mixedMoment B node3460 node3460Labels := rfl
  simpa [nodeValue3460, Sparse.eval] using hc.symm

theorem sound3463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3463 node3463Labels = Sparse.eval nodeValue3463 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3463) = mixedMoment B node3463 node3463Labels := rfl
  simpa [nodeValue3463, Sparse.eval] using hc.symm

theorem sound3467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3467 node3467Labels = Sparse.eval nodeValue3467 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3467) = mixedMoment B node3467 node3467Labels := rfl
  simpa [nodeValue3467, Sparse.eval] using hc.symm

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

theorem sound3625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3625 node3625Labels = Sparse.eval nodeValue3625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3625) = mixedMoment B node3625 node3625Labels := rfl
  simpa [nodeValue3625, Sparse.eval] using hc.symm

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

theorem sound3690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3690 node3690Labels = Sparse.eval nodeValue3690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3690) = mixedMoment B node3690 node3690Labels := rfl
  simpa [nodeValue3690, Sparse.eval] using hc.symm

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

theorem sound3719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3719 node3719Labels = Sparse.eval nodeValue3719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3719) = mixedMoment B node3719 node3719Labels := rfl
  simpa [nodeValue3719, Sparse.eval] using hc.symm

theorem sound3757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3757 node3757Labels = Sparse.eval nodeValue3757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3757) = mixedMoment B node3757 node3757Labels := rfl
  simpa [nodeValue3757, Sparse.eval] using hc.symm

theorem sound3758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3758 node3758Labels = Sparse.eval nodeValue3758 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3758) = mixedMoment B node3758 node3758Labels := rfl
  simpa [nodeValue3758, Sparse.eval] using hc.symm

theorem sound3761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3761 node3761Labels = Sparse.eval nodeValue3761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3761) = mixedMoment B node3761 node3761Labels := rfl
  simpa [nodeValue3761, Sparse.eval] using hc.symm

theorem sound3764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3764 node3764Labels = Sparse.eval nodeValue3764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3764) = mixedMoment B node3764 node3764Labels := rfl
  simpa [nodeValue3764, Sparse.eval] using hc.symm

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

theorem zero3807 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = 0 := by
  exact mixedMoment_order_one B hB node3807 node3807Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3808 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3808 node3808Labels = 0 := by
  exact mixedMoment_order_one B hB node3808 node3808Labels 1
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

theorem sound3782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3782 node3782Labels = Sparse.eval nodeValue3782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3782) = mixedMoment B node3782 node3782Labels := rfl
  simpa [nodeValue3782, Sparse.eval] using hc.symm

theorem sound3787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3787 node3787Labels = Sparse.eval nodeValue3787 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3787) = mixedMoment B node3787 node3787Labels := rfl
  simpa [nodeValue3787, Sparse.eval] using hc.symm

theorem sound3790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3790 node3790Labels = Sparse.eval nodeValue3790 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3790) = mixedMoment B node3790 node3790Labels := rfl
  simpa [nodeValue3790, Sparse.eval] using hc.symm

theorem sound3795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3795 node3795Labels = Sparse.eval nodeValue3795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3795) = mixedMoment B node3795 node3795Labels := rfl
  simpa [nodeValue3795, Sparse.eval] using hc.symm

theorem sound3796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3796 node3796Labels = Sparse.eval nodeValue3796 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3796) = mixedMoment B node3796 node3796Labels := rfl
  simpa [nodeValue3796, Sparse.eval] using hc.symm

theorem sound3799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3799 node3799Labels = Sparse.eval nodeValue3799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3799) = mixedMoment B node3799 node3799Labels := rfl
  simpa [nodeValue3799, Sparse.eval] using hc.symm

theorem sound3801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3801 node3801Labels = Sparse.eval nodeValue3801 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3801) = mixedMoment B node3801 node3801Labels := rfl
  simpa [nodeValue3801, Sparse.eval] using hc.symm

theorem sound3802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3802 node3802Labels = Sparse.eval nodeValue3802 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3802) = mixedMoment B node3802 node3802Labels := rfl
  simpa [nodeValue3802, Sparse.eval] using hc.symm

theorem sound3803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3803 node3803Labels = Sparse.eval nodeValue3803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3803) = mixedMoment B node3803 node3803Labels := rfl
  simpa [nodeValue3803, Sparse.eval] using hc.symm

theorem sound3804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3804 node3804Labels = Sparse.eval nodeValue3804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3804) = mixedMoment B node3804 node3804Labels := rfl
  simpa [nodeValue3804, Sparse.eval] using hc.symm

theorem sound3807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3807 node3807Labels = Sparse.eval nodeValue3807 (mixedVector B) := by
  simpa only [nodeValue3807, Sparse.eval_nil] using zero3807 B _hB _hF

theorem sound3808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3808 node3808Labels = Sparse.eval nodeValue3808 (mixedVector B) := by
  simpa only [nodeValue3808, Sparse.eval_nil] using zero3808 B _hB _hF

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

theorem sound3825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3825 node3825Labels = Sparse.eval nodeValue3825 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3825) = mixedMoment B node3825 node3825Labels := rfl
  simpa [nodeValue3825, Sparse.eval] using hc.symm

theorem sound3838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3838 node3838Labels = Sparse.eval nodeValue3838 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3838) = mixedMoment B node3838 node3838Labels := rfl
  simpa [nodeValue3838, Sparse.eval] using hc.symm

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

theorem sound3843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3843 node3843Labels = Sparse.eval nodeValue3843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3843) = mixedMoment B node3843 node3843Labels := rfl
  simpa [nodeValue3843, Sparse.eval] using hc.symm

theorem sound3846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3846 node3846Labels = Sparse.eval nodeValue3846 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3846) = mixedMoment B node3846 node3846Labels := rfl
  simpa [nodeValue3846, Sparse.eval] using hc.symm

theorem sound3876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3876 node3876Labels = Sparse.eval nodeValue3876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3876) = mixedMoment B node3876 node3876Labels := rfl
  simpa [nodeValue3876, Sparse.eval] using hc.symm

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

theorem sound3953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3953 node3953Labels = Sparse.eval nodeValue3953 (mixedVector B) := by
  simpa only [nodeValue3953, Sparse.eval_nil] using zero3953 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3976 node3976Labels = 0 := by
  exact mixedMoment_alpha B hF node3976 node3976Labels 2 permutation160
    (by decide +kernel)

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

theorem sound3976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3976 node3976Labels = Sparse.eval nodeValue3976 (mixedVector B) := by
  simpa only [nodeValue3976, Sparse.eval_nil] using zero3976 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4848 node4848Labels = Sparse.eval nodeValue4848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4848) = mixedMoment B node4848 node4848Labels := rfl
  simpa [nodeValue4848, Sparse.eval] using hc.symm

theorem sound4849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4849 node4849Labels = Sparse.eval nodeValue4849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4849) = mixedMoment B node4849 node4849Labels := rfl
  simpa [nodeValue4849, Sparse.eval] using hc.symm

theorem sound4852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4852 node4852Labels = Sparse.eval nodeValue4852 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4852) = mixedMoment B node4852 node4852Labels := rfl
  simpa [nodeValue4852, Sparse.eval] using hc.symm

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

theorem sound5065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5065 node5065Labels = Sparse.eval nodeValue5065 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5065) = mixedMoment B node5065 node5065Labels := rfl
  simpa [nodeValue5065, Sparse.eval] using hc.symm

theorem sound5067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5067 node5067Labels = Sparse.eval nodeValue5067 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5067) = mixedMoment B node5067 node5067Labels := rfl
  simpa [nodeValue5067, Sparse.eval] using hc.symm

theorem sound5073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5073 node5073Labels = Sparse.eval nodeValue5073 (mixedVector B) := by
  have h := singleton5073 B _hB
  rw [sound2480 B _hB _hF, sound3467 B _hB _hF] at h
  norm_num [nodeValue5073, nodeValue2480, nodeValue3467, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5074 node5074Labels = Sparse.eval nodeValue5074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5074) = mixedMoment B node5074 node5074Labels := rfl
  simpa [nodeValue5074, Sparse.eval] using hc.symm

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

theorem sound5284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5284 node5284Labels = Sparse.eval nodeValue5284 (mixedVector B) := by
  have h := singleton5284 B _hB
  rw [sound3077 B _hB _hF, sound3625 B _hB _hF] at h
  norm_num [nodeValue5284, nodeValue3077, nodeValue3625, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5352 node5352Labels = Sparse.eval nodeValue5352 (mixedVector B) := by
  have h := singleton5352 B _hB
  rw [sound3690 B _hB _hF, sound3764 B _hB _hF] at h
  norm_num [nodeValue5352, nodeValue3690, nodeValue3764, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5353 node5353Labels = Sparse.eval nodeValue5353 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5353) = mixedMoment B node5353 node5353Labels := rfl
  simpa [nodeValue5353, Sparse.eval] using hc.symm

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

theorem sound5378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5378 node5378Labels = Sparse.eval nodeValue5378 (mixedVector B) := by
  have h := singleton5378 B _hB
  rw [sound3719 B _hB _hF, sound3795 B _hB _hF] at h
  norm_num [nodeValue5378, nodeValue3719, nodeValue3795, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5379 node5379Labels = Sparse.eval nodeValue5379 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5379) = mixedMoment B node5379 node5379Labels := rfl
  simpa [nodeValue5379, Sparse.eval] using hc.symm

theorem sound5381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5381 node5381Labels = Sparse.eval nodeValue5381 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5381) = mixedMoment B node5381 node5381Labels := rfl
  simpa [nodeValue5381, Sparse.eval] using hc.symm

theorem sound5382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5382 node5382Labels = Sparse.eval nodeValue5382 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5382) = mixedMoment B node5382 node5382Labels := rfl
  simpa [nodeValue5382, Sparse.eval] using hc.symm

theorem sound5397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5397 node5397Labels = Sparse.eval nodeValue5397 (mixedVector B) := by
  have h := singleton5397 B _hB
  rw [sound3782 B _hB _hF, sound3796 B _hB _hF] at h
  norm_num [nodeValue5397, nodeValue3782, nodeValue3796, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5401 node5401Labels = Sparse.eval nodeValue5401 (mixedVector B) := by
  have h := singleton5401 B _hB
  rw [sound3787 B _hB _hF, sound3804 B _hB _hF] at h
  norm_num [nodeValue5401, nodeValue3787, nodeValue3804, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5406 node5406Labels = Sparse.eval nodeValue5406 (mixedVector B) := by
  have h := singleton5406 B _hB
  rw [sound3801 B _hB _hF, sound3812 B _hB _hF] at h
  norm_num [nodeValue5406, nodeValue3801, nodeValue3812, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5408 node5408Labels = Sparse.eval nodeValue5408 (mixedVector B) := by
  simpa only [nodeValue5408, Sparse.eval_nil] using zero5408 B _hB _hF

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

theorem sound5420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5420 node5420Labels = Sparse.eval nodeValue5420 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5420) = mixedMoment B node5420 node5420Labels := rfl
  simpa [nodeValue5420, Sparse.eval] using hc.symm

theorem sound5421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5421 node5421Labels = Sparse.eval nodeValue5421 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5421) = mixedMoment B node5421 node5421Labels := rfl
  simpa [nodeValue5421, Sparse.eval] using hc.symm

theorem sound5424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5424 node5424Labels = Sparse.eval nodeValue5424 (mixedVector B) := by
  have h := singleton5424 B _hB
  rw [sound3838 B _hB _hF, sound3843 B _hB _hF] at h
  norm_num [nodeValue5424, nodeValue3838, nodeValue3843, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5425 node5425Labels = Sparse.eval nodeValue5425 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5425) = mixedMoment B node5425 node5425Labels := rfl
  simpa [nodeValue5425, Sparse.eval] using hc.symm

theorem sound5430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5430 node5430Labels = Sparse.eval nodeValue5430 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5430) = mixedMoment B node5430 node5430Labels := rfl
  simpa [nodeValue5430, Sparse.eval] using hc.symm

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

theorem sound5446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5446 node5446Labels = Sparse.eval nodeValue5446 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5446) = mixedMoment B node5446 node5446Labels := rfl
  simpa [nodeValue5446, Sparse.eval] using hc.symm

theorem sound5471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5471 node5471Labels = Sparse.eval nodeValue5471 (mixedVector B) := by
  simpa only [nodeValue5471, Sparse.eval_nil] using zero5471 B _hB _hF

theorem sound5477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5477 node5477Labels = Sparse.eval nodeValue5477 (mixedVector B) := by
  simpa only [nodeValue5477, Sparse.eval_nil] using zero5477 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources32
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1040 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1040 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1040 + difference 0 1) (sourceB1040 + difference 1 0) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5382) := by
    have ha : (tripleCharges (sourceA1040 + difference 0 1) (sourceB1040 + difference 1 0) sourceC1040) = raw17029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17029; decide +kernel
    rw [ha]
    exact (canonical17029 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1040 + difference 0 2) (sourceB1040 + difference 2 0) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA1040 + difference 0 2) (sourceB1040 + difference 2 0) sourceC1040) = raw17030 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17030; decide +kernel
    rw [ha]
    exact (canonical17030 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1040 + difference 0 3) (sourceB1040 + difference 3 0) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1040 + difference 0 3) (sourceB1040 + difference 3 0) sourceC1040) = raw17031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17031; decide +kernel
    rw [ha]
    exact (canonical17031 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1040 + difference 0 4) (sourceB1040 + difference 4 0) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA1040 + difference 0 4) (sourceB1040 + difference 4 0) sourceC1040) = raw17032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17032; decide +kernel
    rw [ha]
    exact (canonical17032 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1040 + difference 0 5) (sourceB1040 + difference 5 0) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1040 + difference 0 5) (sourceB1040 + difference 5 0) sourceC1040) = raw17033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17033; decide +kernel
    rw [ha]
    exact (canonical17033 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1040 + difference 1 0) (sourceB1040 + difference 0 1) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1040 + difference 1 0) (sourceB1040 + difference 0 1) sourceC1040) = raw15130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw15130; decide +kernel
    rw [ha]
    exact (canonical15130 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1040 + difference 1 2) (sourceB1040 + difference 2 1) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5420) := by
    have ha : (tripleCharges (sourceA1040 + difference 1 2) (sourceB1040 + difference 2 1) sourceC1040) = raw17034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17034; decide +kernel
    rw [ha]
    exact (canonical17034 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1040 + difference 1 3) (sourceB1040 + difference 3 1) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1040 + difference 1 3) (sourceB1040 + difference 3 1) sourceC1040) = raw15114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw15114; decide +kernel
    rw [ha]
    exact (canonical15114 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1040 + difference 1 4) (sourceB1040 + difference 4 1) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA1040 + difference 1 4) (sourceB1040 + difference 4 1) sourceC1040) = raw17035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17035; decide +kernel
    rw [ha]
    exact (canonical17035 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1040 + difference 1 5) (sourceB1040 + difference 5 1) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1040 + difference 1 5) (sourceB1040 + difference 5 1) sourceC1040) = raw17036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17036; decide +kernel
    rw [ha]
    exact (canonical17036 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1040 + difference 2 0) (sourceB1040 + difference 0 2) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1040 + difference 2 0) (sourceB1040 + difference 0 2) sourceC1040) = raw15129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw15129; decide +kernel
    rw [ha]
    exact (canonical15129 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1040 + difference 2 1) (sourceB1040 + difference 1 2) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1040 + difference 2 1) (sourceB1040 + difference 1 2) sourceC1040) = raw16851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw16851; decide +kernel
    rw [ha]
    exact (canonical16851 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1040 + difference 2 3) (sourceB1040 + difference 3 2) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA1040 + difference 2 3) (sourceB1040 + difference 3 2) sourceC1040) = raw15113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw15113; decide +kernel
    rw [ha]
    exact (canonical15113 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1040 + difference 2 4) (sourceB1040 + difference 4 2) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1040 + difference 2 4) (sourceB1040 + difference 4 2) sourceC1040) = raw17037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17037; decide +kernel
    rw [ha]
    exact (canonical17037 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1040 + difference 2 5) (sourceB1040 + difference 5 2) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA1040 + difference 2 5) (sourceB1040 + difference 5 2) sourceC1040) = raw17038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17038; decide +kernel
    rw [ha]
    exact (canonical17038 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1040 + difference 3 0) (sourceB1040 + difference 0 3) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA1040 + difference 3 0) (sourceB1040 + difference 0 3) sourceC1040) = raw17039 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17039; decide +kernel
    rw [ha]
    exact (canonical17039 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1040 + difference 3 1) (sourceB1040 + difference 1 3) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4849) := by
    have ha : (tripleCharges (sourceA1040 + difference 3 1) (sourceB1040 + difference 1 3) sourceC1040) = raw17040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17040; decide +kernel
    rw [ha]
    exact (canonical17040 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1040 + difference 3 2) (sourceB1040 + difference 2 3) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4848) := by
    have ha : (tripleCharges (sourceA1040 + difference 3 2) (sourceB1040 + difference 2 3) sourceC1040) = raw17041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17041; decide +kernel
    rw [ha]
    exact (canonical17041 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1040 + difference 3 4) (sourceB1040 + difference 4 3) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4849) := by
    have ha : (tripleCharges (sourceA1040 + difference 3 4) (sourceB1040 + difference 4 3) sourceC1040) = raw17042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17042; decide +kernel
    rw [ha]
    exact (canonical17042 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1040 + difference 3 5) (sourceB1040 + difference 5 3) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA1040 + difference 3 5) (sourceB1040 + difference 5 3) sourceC1040) = raw17043 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17043; decide +kernel
    rw [ha]
    exact (canonical17043 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1040 + difference 4 0) (sourceB1040 + difference 0 4) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1040 + difference 4 0) (sourceB1040 + difference 0 4) sourceC1040) = raw17044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17044; decide +kernel
    rw [ha]
    exact (canonical17044 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1040 + difference 4 1) (sourceB1040 + difference 1 4) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA1040 + difference 4 1) (sourceB1040 + difference 1 4) sourceC1040) = raw17045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17045; decide +kernel
    rw [ha]
    exact (canonical17045 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1040 + difference 4 2) (sourceB1040 + difference 2 4) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5420) := by
    have ha : (tripleCharges (sourceA1040 + difference 4 2) (sourceB1040 + difference 2 4) sourceC1040) = raw17046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17046; decide +kernel
    rw [ha]
    exact (canonical17046 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1040 + difference 4 3) (sourceB1040 + difference 3 4) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA1040 + difference 4 3) (sourceB1040 + difference 3 4) sourceC1040) = raw17047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17047; decide +kernel
    rw [ha]
    exact (canonical17047 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1040 + difference 4 5) (sourceB1040 + difference 5 4) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1040 + difference 4 5) (sourceB1040 + difference 5 4) sourceC1040) = raw17048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17048; decide +kernel
    rw [ha]
    exact (canonical17048 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1040 + difference 5 0) (sourceB1040 + difference 0 5) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1040 + difference 5 0) (sourceB1040 + difference 0 5) sourceC1040) = raw17049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17049; decide +kernel
    rw [ha]
    exact (canonical17049 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1040 + difference 5 1) (sourceB1040 + difference 1 5) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA1040 + difference 5 1) (sourceB1040 + difference 1 5) sourceC1040) = raw17050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17050; decide +kernel
    rw [ha]
    exact (canonical17050 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1040 + difference 5 2) (sourceB1040 + difference 2 5) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA1040 + difference 5 2) (sourceB1040 + difference 2 5) sourceC1040) = raw17051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17051; decide +kernel
    rw [ha]
    exact (canonical17051 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1040 + difference 5 3) (sourceB1040 + difference 3 5) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1040 + difference 5 3) (sourceB1040 + difference 3 5) sourceC1040) = raw17052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17052; decide +kernel
    rw [ha]
    exact (canonical17052 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1040 + difference 5 4) (sourceB1040 + difference 4 5) sourceC1040) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5382) := by
    have ha : (tripleCharges (sourceA1040 + difference 5 4) (sourceB1040 + difference 4 5) sourceC1040) = raw17053 := by
      apply Matrix.ext; unfold tripleCharges sourceA1040 sourceB1040 sourceC1040 difference raw17053; decide +kernel
    rw [ha]
    exact (canonical17053 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1040 sourceB1040 sourceC1040
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1040, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1048 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1048 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1048 + difference 0 1) (sourceB1048 + difference 1 0) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1048 + difference 0 1) (sourceB1048 + difference 1 0) sourceC1048) = raw17179 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17179; decide +kernel
    rw [ha]
    exact (canonical17179 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1048 + difference 0 2) (sourceB1048 + difference 2 0) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5408) := by
    have ha : (tripleCharges (sourceA1048 + difference 0 2) (sourceB1048 + difference 2 0) sourceC1048) = raw17180 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17180; decide +kernel
    rw [ha]
    exact (canonical17180 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1048 + difference 0 3) (sourceB1048 + difference 3 0) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5408) := by
    have ha : (tripleCharges (sourceA1048 + difference 0 3) (sourceB1048 + difference 3 0) sourceC1048) = raw17181 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17181; decide +kernel
    rw [ha]
    exact (canonical17181 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1048 + difference 0 4) (sourceB1048 + difference 4 0) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1048 + difference 0 4) (sourceB1048 + difference 4 0) sourceC1048) = raw17182 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17182; decide +kernel
    rw [ha]
    exact (canonical17182 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1048 + difference 0 5) (sourceB1048 + difference 5 0) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA1048 + difference 0 5) (sourceB1048 + difference 5 0) sourceC1048) = raw17183 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17183; decide +kernel
    rw [ha]
    exact (canonical17183 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1048 + difference 1 0) (sourceB1048 + difference 0 1) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA1048 + difference 1 0) (sourceB1048 + difference 0 1) sourceC1048) = raw17184 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17184; decide +kernel
    rw [ha]
    exact (canonical17184 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1048 + difference 1 2) (sourceB1048 + difference 2 1) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1048 + difference 1 2) (sourceB1048 + difference 2 1) sourceC1048) = raw9129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw9129; decide +kernel
    rw [ha]
    exact (canonical9129 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1048 + difference 1 3) (sourceB1048 + difference 3 1) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1048 + difference 1 3) (sourceB1048 + difference 3 1) sourceC1048) = raw9130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw9130; decide +kernel
    rw [ha]
    exact (canonical9130 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1048 + difference 1 4) (sourceB1048 + difference 4 1) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1048 + difference 1 4) (sourceB1048 + difference 4 1) sourceC1048) = raw9131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw9131; decide +kernel
    rw [ha]
    exact (canonical9131 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1048 + difference 1 5) (sourceB1048 + difference 5 1) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1048 + difference 1 5) (sourceB1048 + difference 5 1) sourceC1048) = raw9132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw9132; decide +kernel
    rw [ha]
    exact (canonical9132 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1048 + difference 2 0) (sourceB1048 + difference 0 2) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA1048 + difference 2 0) (sourceB1048 + difference 0 2) sourceC1048) = raw9139 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw9139; decide +kernel
    rw [ha]
    exact (canonical9139 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1048 + difference 2 1) (sourceB1048 + difference 1 2) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA1048 + difference 2 1) (sourceB1048 + difference 1 2) sourceC1048) = raw17185 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17185; decide +kernel
    rw [ha]
    exact (canonical17185 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1048 + difference 2 3) (sourceB1048 + difference 3 2) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1048 + difference 2 3) (sourceB1048 + difference 3 2) sourceC1048) = raw17186 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17186; decide +kernel
    rw [ha]
    exact (canonical17186 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1048 + difference 2 4) (sourceB1048 + difference 4 2) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1048 + difference 2 4) (sourceB1048 + difference 4 2) sourceC1048) = raw17187 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17187; decide +kernel
    rw [ha]
    exact (canonical17187 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1048 + difference 2 5) (sourceB1048 + difference 5 2) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA1048 + difference 2 5) (sourceB1048 + difference 5 2) sourceC1048) = raw17188 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17188; decide +kernel
    rw [ha]
    exact (canonical17188 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1048 + difference 3 0) (sourceB1048 + difference 0 3) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA1048 + difference 3 0) (sourceB1048 + difference 0 3) sourceC1048) = raw9144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw9144; decide +kernel
    rw [ha]
    exact (canonical9144 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1048 + difference 3 1) (sourceB1048 + difference 1 3) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA1048 + difference 3 1) (sourceB1048 + difference 1 3) sourceC1048) = raw17189 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17189; decide +kernel
    rw [ha]
    exact (canonical17189 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1048 + difference 3 2) (sourceB1048 + difference 2 3) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1048 + difference 3 2) (sourceB1048 + difference 2 3) sourceC1048) = raw17190 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17190; decide +kernel
    rw [ha]
    exact (canonical17190 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1048 + difference 3 4) (sourceB1048 + difference 4 3) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1048 + difference 3 4) (sourceB1048 + difference 4 3) sourceC1048) = raw17191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17191; decide +kernel
    rw [ha]
    exact (canonical17191 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1048 + difference 3 5) (sourceB1048 + difference 5 3) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA1048 + difference 3 5) (sourceB1048 + difference 5 3) sourceC1048) = raw17192 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17192; decide +kernel
    rw [ha]
    exact (canonical17192 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1048 + difference 4 0) (sourceB1048 + difference 0 4) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5067) := by
    have ha : (tripleCharges (sourceA1048 + difference 4 0) (sourceB1048 + difference 0 4) sourceC1048) = raw9149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw9149; decide +kernel
    rw [ha]
    exact (canonical9149 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1048 + difference 4 1) (sourceB1048 + difference 1 4) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5348) := by
    have ha : (tripleCharges (sourceA1048 + difference 4 1) (sourceB1048 + difference 1 4) sourceC1048) = raw17193 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17193; decide +kernel
    rw [ha]
    exact (canonical17193 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1048 + difference 4 2) (sourceB1048 + difference 2 4) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1048 + difference 4 2) (sourceB1048 + difference 2 4) sourceC1048) = raw17194 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17194; decide +kernel
    rw [ha]
    exact (canonical17194 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1048 + difference 4 3) (sourceB1048 + difference 3 4) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA1048 + difference 4 3) (sourceB1048 + difference 3 4) sourceC1048) = raw17195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17195; decide +kernel
    rw [ha]
    exact (canonical17195 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1048 + difference 4 5) (sourceB1048 + difference 5 4) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA1048 + difference 4 5) (sourceB1048 + difference 5 4) sourceC1048) = raw17196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17196; decide +kernel
    rw [ha]
    exact (canonical17196 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1048 + difference 5 0) (sourceB1048 + difference 0 5) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5065) := by
    have ha : (tripleCharges (sourceA1048 + difference 5 0) (sourceB1048 + difference 0 5) sourceC1048) = raw9154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw9154; decide +kernel
    rw [ha]
    exact (canonical9154 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1048 + difference 5 1) (sourceB1048 + difference 1 5) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5067) := by
    have ha : (tripleCharges (sourceA1048 + difference 5 1) (sourceB1048 + difference 1 5) sourceC1048) = raw17197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17197; decide +kernel
    rw [ha]
    exact (canonical17197 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1048 + difference 5 2) (sourceB1048 + difference 2 5) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA1048 + difference 5 2) (sourceB1048 + difference 2 5) sourceC1048) = raw17198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17198; decide +kernel
    rw [ha]
    exact (canonical17198 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1048 + difference 5 3) (sourceB1048 + difference 3 5) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA1048 + difference 5 3) (sourceB1048 + difference 3 5) sourceC1048) = raw17199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17199; decide +kernel
    rw [ha]
    exact (canonical17199 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1048 + difference 5 4) (sourceB1048 + difference 4 5) sourceC1048) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA1048 + difference 5 4) (sourceB1048 + difference 4 5) sourceC1048) = raw17200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1048 sourceB1048 sourceC1048 difference raw17200; decide +kernel
    rw [ha]
    exact (canonical17200 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1048 sourceB1048 sourceC1048
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1048, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1051 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1051 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1051 + difference 0 1) (sourceB1051 + difference 1 0) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA1051 + difference 0 1) (sourceB1051 + difference 1 0) sourceC1051) = raw16895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw16895; decide +kernel
    rw [ha]
    exact (canonical16895 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1051 + difference 0 2) (sourceB1051 + difference 2 0) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA1051 + difference 0 2) (sourceB1051 + difference 2 0) sourceC1051) = raw17233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17233; decide +kernel
    rw [ha]
    exact (canonical17233 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1051 + difference 0 3) (sourceB1051 + difference 3 0) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA1051 + difference 0 3) (sourceB1051 + difference 3 0) sourceC1051) = raw17234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17234; decide +kernel
    rw [ha]
    exact (canonical17234 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1051 + difference 0 4) (sourceB1051 + difference 4 0) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3757) := by
    have ha : (tripleCharges (sourceA1051 + difference 0 4) (sourceB1051 + difference 4 0) sourceC1051) = raw17235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17235; decide +kernel
    rw [ha]
    exact (canonical17235 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1051 + difference 0 5) (sourceB1051 + difference 5 0) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3459) := by
    have ha : (tripleCharges (sourceA1051 + difference 0 5) (sourceB1051 + difference 5 0) sourceC1051) = raw17236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17236; decide +kernel
    rw [ha]
    exact (canonical17236 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1051 + difference 1 0) (sourceB1051 + difference 0 1) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA1051 + difference 1 0) (sourceB1051 + difference 0 1) sourceC1051) = raw15154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15154; decide +kernel
    rw [ha]
    exact (canonical15154 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1051 + difference 1 2) (sourceB1051 + difference 2 1) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA1051 + difference 1 2) (sourceB1051 + difference 2 1) sourceC1051) = raw15144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15144; decide +kernel
    rw [ha]
    exact (canonical15144 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1051 + difference 1 3) (sourceB1051 + difference 3 1) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA1051 + difference 1 3) (sourceB1051 + difference 3 1) sourceC1051) = raw15893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15893; decide +kernel
    rw [ha]
    exact (canonical15893 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1051 + difference 1 4) (sourceB1051 + difference 4 1) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3758) := by
    have ha : (tripleCharges (sourceA1051 + difference 1 4) (sourceB1051 + difference 4 1) sourceC1051) = raw15718 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15718; decide +kernel
    rw [ha]
    exact (canonical15718 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1051 + difference 1 5) (sourceB1051 + difference 5 1) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3460) := by
    have ha : (tripleCharges (sourceA1051 + difference 1 5) (sourceB1051 + difference 5 1) sourceC1051) = raw15894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15894; decide +kernel
    rw [ha]
    exact (canonical15894 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1051 + difference 2 0) (sourceB1051 + difference 0 2) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA1051 + difference 2 0) (sourceB1051 + difference 0 2) sourceC1051) = raw15899 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15899; decide +kernel
    rw [ha]
    exact (canonical15899 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1051 + difference 2 1) (sourceB1051 + difference 1 2) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3802) := by
    have ha : (tripleCharges (sourceA1051 + difference 2 1) (sourceB1051 + difference 1 2) sourceC1051) = raw16901 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw16901; decide +kernel
    rw [ha]
    exact (canonical16901 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1051 + difference 2 3) (sourceB1051 + difference 3 2) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA1051 + difference 2 3) (sourceB1051 + difference 3 2) sourceC1051) = raw17237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17237; decide +kernel
    rw [ha]
    exact (canonical17237 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1051 + difference 2 4) (sourceB1051 + difference 4 2) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA1051 + difference 2 4) (sourceB1051 + difference 4 2) sourceC1051) = raw17238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17238; decide +kernel
    rw [ha]
    exact (canonical17238 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1051 + difference 2 5) (sourceB1051 + difference 5 2) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA1051 + difference 2 5) (sourceB1051 + difference 5 2) sourceC1051) = raw17239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17239; decide +kernel
    rw [ha]
    exact (canonical17239 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1051 + difference 3 0) (sourceB1051 + difference 0 3) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA1051 + difference 3 0) (sourceB1051 + difference 0 3) sourceC1051) = raw15903 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15903; decide +kernel
    rw [ha]
    exact (canonical15903 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1051 + difference 3 1) (sourceB1051 + difference 1 3) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3802) := by
    have ha : (tripleCharges (sourceA1051 + difference 3 1) (sourceB1051 + difference 1 3) sourceC1051) = raw16906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw16906; decide +kernel
    rw [ha]
    exact (canonical16906 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1051 + difference 3 2) (sourceB1051 + difference 2 3) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA1051 + difference 3 2) (sourceB1051 + difference 2 3) sourceC1051) = raw17240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17240; decide +kernel
    rw [ha]
    exact (canonical17240 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1051 + difference 3 4) (sourceB1051 + difference 4 3) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA1051 + difference 3 4) (sourceB1051 + difference 4 3) sourceC1051) = raw17241 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17241; decide +kernel
    rw [ha]
    exact (canonical17241 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1051 + difference 3 5) (sourceB1051 + difference 5 3) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA1051 + difference 3 5) (sourceB1051 + difference 5 3) sourceC1051) = raw17242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17242; decide +kernel
    rw [ha]
    exact (canonical17242 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1051 + difference 4 0) (sourceB1051 + difference 0 4) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA1051 + difference 4 0) (sourceB1051 + difference 0 4) sourceC1051) = raw15906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15906; decide +kernel
    rw [ha]
    exact (canonical15906 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1051 + difference 4 1) (sourceB1051 + difference 1 4) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA1051 + difference 4 1) (sourceB1051 + difference 1 4) sourceC1051) = raw16911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw16911; decide +kernel
    rw [ha]
    exact (canonical16911 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1051 + difference 4 2) (sourceB1051 + difference 2 4) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA1051 + difference 4 2) (sourceB1051 + difference 2 4) sourceC1051) = raw17243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17243; decide +kernel
    rw [ha]
    exact (canonical17243 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1051 + difference 4 3) (sourceB1051 + difference 3 4) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA1051 + difference 4 3) (sourceB1051 + difference 3 4) sourceC1051) = raw17244 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17244; decide +kernel
    rw [ha]
    exact (canonical17244 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1051 + difference 4 5) (sourceB1051 + difference 5 4) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA1051 + difference 4 5) (sourceB1051 + difference 5 4) sourceC1051) = raw17245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17245; decide +kernel
    rw [ha]
    exact (canonical17245 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1051 + difference 5 0) (sourceB1051 + difference 0 5) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3977) := by
    have ha : (tripleCharges (sourceA1051 + difference 5 0) (sourceB1051 + difference 0 5) sourceC1051) = raw15151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15151; decide +kernel
    rw [ha]
    exact (canonical15151 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1051 + difference 5 1) (sourceB1051 + difference 1 5) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3976) := by
    have ha : (tripleCharges (sourceA1051 + difference 5 1) (sourceB1051 + difference 1 5) sourceC1051) = raw17246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw17246; decide +kernel
    rw [ha]
    exact (canonical17246 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1051 + difference 5 2) (sourceB1051 + difference 2 5) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1051 + difference 5 2) (sourceB1051 + difference 2 5) sourceC1051) = raw15140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15140; decide +kernel
    rw [ha]
    exact (canonical15140 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1051 + difference 5 3) (sourceB1051 + difference 3 5) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA1051 + difference 5 3) (sourceB1051 + difference 3 5) sourceC1051) = raw16896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw16896; decide +kernel
    rw [ha]
    exact (canonical16896 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1051 + difference 5 4) (sourceB1051 + difference 4 5) sourceC1051) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3953) := by
    have ha : (tripleCharges (sourceA1051 + difference 5 4) (sourceB1051 + difference 4 5) sourceC1051) = raw15715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1051 sourceB1051 sourceC1051 difference raw15715; decide +kernel
    rw [ha]
    exact (canonical15715 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1051 sourceB1051 sourceC1051
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1051, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1054 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1054 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1054 + difference 0 1) (sourceB1054 + difference 1 0) sourceC1054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA1054 + difference 0 1) (sourceB1054 + difference 1 0) sourceC1054) = raw17307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1054 sourceB1054 sourceC1054 difference raw17307; decide +kernel
    rw [ha]
    exact (canonical17307 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1054 + difference 1 1) (sourceB1054 + difference 1 1) sourceC1054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA1054 + difference 1 1) (sourceB1054 + difference 1 1) sourceC1054) = raw17308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1054 sourceB1054 sourceC1054 difference raw17308; decide +kernel
    rw [ha]
    exact (canonical17308 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1054 + difference 2 1) (sourceB1054 + difference 1 2) sourceC1054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3790) := by
    have ha : (tripleCharges (sourceA1054 + difference 2 1) (sourceB1054 + difference 1 2) sourceC1054) = raw17309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1054 sourceB1054 sourceC1054 difference raw17309; decide +kernel
    rw [ha]
    exact (canonical17309 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1054 + difference 3 1) (sourceB1054 + difference 1 3) sourceC1054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3825) := by
    have ha : (tripleCharges (sourceA1054 + difference 3 1) (sourceB1054 + difference 1 3) sourceC1054) = raw17310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1054 sourceB1054 sourceC1054 difference raw17310; decide +kernel
    rw [ha]
    exact (canonical17310 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1054 + difference 4 1) (sourceB1054 + difference 1 4) sourceC1054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3115) := by
    have ha : (tripleCharges (sourceA1054 + difference 4 1) (sourceB1054 + difference 1 4) sourceC1054) = raw17311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1054 sourceB1054 sourceC1054 difference raw17311; decide +kernel
    rw [ha]
    exact (canonical17311 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1054 + difference 5 1) (sourceB1054 + difference 1 5) sourceC1054) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2621) := by
    have ha : (tripleCharges (sourceA1054 + difference 5 1) (sourceB1054 + difference 1 5) sourceC1054) = raw17312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1054 sourceB1054 sourceC1054 difference raw17312; decide +kernel
    rw [ha]
    exact (canonical17312 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1054 + sourceB1054) sourceC1054) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1054 + sourceB1054) sourceC1054) = raw17313 := by
      apply Matrix.ext; unfold doubleCharges sourceA1054 sourceB1054 sourceC1054 raw17313; decide +kernel
    rw [ha]
    exact (canonical17313 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1054 sourceB1054 sourceC1054
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1054, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck896 : Integer.Sparse.reindex keyMap MixedData.row896 = numericRow896 := by decide +kernel

theorem numericCheck896 (x : Master → ℝ) : Integer.Sparse.eval numericRow896 x =
    (2880 : ℝ) * reducedSource896 x := by
  norm_num [numericRow896, reducedSource896, Integer.Sparse.eval, Sparse.eval, nodeValue4848, nodeValue4849, nodeValue4852, nodeValue5378, nodeValue5379, nodeValue5381, nodeValue5382, nodeValue5397, nodeValue5411, nodeValue5420, nodeValue5421, nodeValue5424, nodeValue5425, nodeValue5446, nodeValue5477, nodeValue5483]
  ring

theorem reindexCheck901 : Integer.Sparse.reindex keyMap MixedData.row901 = numericRow901 := by decide +kernel

theorem numericCheck901 (x : Master → ℝ) : Integer.Sparse.eval numericRow901 x =
    (8640 : ℝ) * reducedSource901 x := by
  norm_num [numericRow901, reducedSource901, Integer.Sparse.eval, Sparse.eval, nodeValue5065, nodeValue5067, nodeValue5073, nodeValue5074, nodeValue5250, nodeValue5284, nodeValue5348, nodeValue5352, nodeValue5353, nodeValue5401, nodeValue5406, nodeValue5408, nodeValue5410, nodeValue5430, nodeValue5433, nodeValue5439, nodeValue5471, nodeValue5480, nodeValue5482, nodeValue5485]
  ring

theorem reindexCheck904 : Integer.Sparse.reindex keyMap MixedData.row904 = numericRow904 := by decide +kernel

theorem numericCheck904 (x : Master → ℝ) : Integer.Sparse.eval numericRow904 x =
    (2160 : ℝ) * reducedSource904 x := by
  norm_num [numericRow904, reducedSource904, Integer.Sparse.eval, Sparse.eval, nodeValue3459, nodeValue3460, nodeValue3463, nodeValue3525, nodeValue3757, nodeValue3758, nodeValue3761, nodeValue3799, nodeValue3801, nodeValue3802, nodeValue3803, nodeValue3807, nodeValue3808, nodeValue3813, nodeValue3846, nodeValue3847, nodeValue3852, nodeValue3953, nodeValue3976, nodeValue3977, nodeValue3981]
  ring

theorem reindexCheck907 : Integer.Sparse.reindex keyMap MixedData.row907 = numericRow907 := by decide +kernel

theorem numericCheck907 (x : Master → ℝ) : Integer.Sparse.eval numericRow907 x =
    (1 : ℝ) * reducedSource907 x := by
  norm_num [numericRow907, reducedSource907, Integer.Sparse.eval, Sparse.eval, nodeValue2621, nodeValue3115, nodeValue3790, nodeValue3825, nodeValue3876, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero896 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource896 (mixedVector B) = 0 := by
  have h4848 : mixedVector B (Sum.inr 4848) = Sparse.eval nodeValue4848 (mixedVector B) := by
    change mixedMoment B node4848 node4848Labels = _
    exact sound4848 B hB hF
  have h4849 : mixedVector B (Sum.inr 4849) = Sparse.eval nodeValue4849 (mixedVector B) := by
    change mixedMoment B node4849 node4849Labels = _
    exact sound4849 B hB hF
  have h4852 : mixedVector B (Sum.inr 4852) = Sparse.eval nodeValue4852 (mixedVector B) := by
    change mixedMoment B node4852 node4852Labels = _
    exact sound4852 B hB hF
  have h5378 : mixedVector B (Sum.inr 5378) = Sparse.eval nodeValue5378 (mixedVector B) := by
    change mixedMoment B node5378 node5378Labels = _
    exact sound5378 B hB hF
  have h5379 : mixedVector B (Sum.inr 5379) = Sparse.eval nodeValue5379 (mixedVector B) := by
    change mixedMoment B node5379 node5379Labels = _
    exact sound5379 B hB hF
  have h5381 : mixedVector B (Sum.inr 5381) = Sparse.eval nodeValue5381 (mixedVector B) := by
    change mixedMoment B node5381 node5381Labels = _
    exact sound5381 B hB hF
  have h5382 : mixedVector B (Sum.inr 5382) = Sparse.eval nodeValue5382 (mixedVector B) := by
    change mixedMoment B node5382 node5382Labels = _
    exact sound5382 B hB hF
  have h5397 : mixedVector B (Sum.inr 5397) = Sparse.eval nodeValue5397 (mixedVector B) := by
    change mixedMoment B node5397 node5397Labels = _
    exact sound5397 B hB hF
  have h5411 : mixedVector B (Sum.inr 5411) = Sparse.eval nodeValue5411 (mixedVector B) := by
    change mixedMoment B node5411 node5411Labels = _
    exact sound5411 B hB hF
  have h5420 : mixedVector B (Sum.inr 5420) = Sparse.eval nodeValue5420 (mixedVector B) := by
    change mixedMoment B node5420 node5420Labels = _
    exact sound5420 B hB hF
  have h5421 : mixedVector B (Sum.inr 5421) = Sparse.eval nodeValue5421 (mixedVector B) := by
    change mixedMoment B node5421 node5421Labels = _
    exact sound5421 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5425 : mixedVector B (Sum.inr 5425) = Sparse.eval nodeValue5425 (mixedVector B) := by
    change mixedMoment B node5425 node5425Labels = _
    exact sound5425 B hB hF
  have h5446 : mixedVector B (Sum.inr 5446) = Sparse.eval nodeValue5446 (mixedVector B) := by
    change mixedMoment B node5446 node5446Labels = _
    exact sound5446 B hB hF
  have h5477 : mixedVector B (Sum.inr 5477) = Sparse.eval nodeValue5477 (mixedVector B) := by
    change mixedMoment B node5477 node5477Labels = _
    exact sound5477 B hB hF
  have h5483 : mixedVector B (Sum.inr 5483) = Sparse.eval nodeValue5483 (mixedVector B) := by
    change mixedMoment B node5483 node5483Labels = _
    exact sound5483_e B hB hF
  simpa only [sourceForm1040, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4848, h4849, h4852, h5378, h5379, h5381, h5382, h5397, h5411, h5420, h5421, h5424, h5425, h5446, h5477, h5483, reducedSource896] using sourceEq1040 B hB

theorem rowSound896 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row896 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck896, numericCheck896, reducedZero896 B hB hF, mul_zero]

theorem reducedZero901 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource901 (mixedVector B) = 0 := by
  have h5065 : mixedVector B (Sum.inr 5065) = Sparse.eval nodeValue5065 (mixedVector B) := by
    change mixedMoment B node5065 node5065Labels = _
    exact sound5065 B hB hF
  have h5067 : mixedVector B (Sum.inr 5067) = Sparse.eval nodeValue5067 (mixedVector B) := by
    change mixedMoment B node5067 node5067Labels = _
    exact sound5067 B hB hF
  have h5073 : mixedVector B (Sum.inr 5073) = Sparse.eval nodeValue5073 (mixedVector B) := by
    change mixedMoment B node5073 node5073Labels = _
    exact sound5073 B hB hF
  have h5074 : mixedVector B (Sum.inr 5074) = Sparse.eval nodeValue5074 (mixedVector B) := by
    change mixedMoment B node5074 node5074Labels = _
    exact sound5074 B hB hF
  have h5250 : mixedVector B (Sum.inr 5250) = Sparse.eval nodeValue5250 (mixedVector B) := by
    change mixedMoment B node5250 node5250Labels = _
    exact sound5250 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5348 : mixedVector B (Sum.inr 5348) = Sparse.eval nodeValue5348 (mixedVector B) := by
    change mixedMoment B node5348 node5348Labels = _
    exact sound5348 B hB hF
  have h5352 : mixedVector B (Sum.inr 5352) = Sparse.eval nodeValue5352 (mixedVector B) := by
    change mixedMoment B node5352 node5352Labels = _
    exact sound5352 B hB hF
  have h5353 : mixedVector B (Sum.inr 5353) = Sparse.eval nodeValue5353 (mixedVector B) := by
    change mixedMoment B node5353 node5353Labels = _
    exact sound5353 B hB hF
  have h5401 : mixedVector B (Sum.inr 5401) = Sparse.eval nodeValue5401 (mixedVector B) := by
    change mixedMoment B node5401 node5401Labels = _
    exact sound5401 B hB hF
  have h5406 : mixedVector B (Sum.inr 5406) = Sparse.eval nodeValue5406 (mixedVector B) := by
    change mixedMoment B node5406 node5406Labels = _
    exact sound5406 B hB hF
  have h5408 : mixedVector B (Sum.inr 5408) = Sparse.eval nodeValue5408 (mixedVector B) := by
    change mixedMoment B node5408 node5408Labels = _
    exact sound5408 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  have h5430 : mixedVector B (Sum.inr 5430) = Sparse.eval nodeValue5430 (mixedVector B) := by
    change mixedMoment B node5430 node5430Labels = _
    exact sound5430 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433_e B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439_e B hB hF
  have h5471 : mixedVector B (Sum.inr 5471) = Sparse.eval nodeValue5471 (mixedVector B) := by
    change mixedMoment B node5471 node5471Labels = _
    exact sound5471 B hB hF
  have h5480 : mixedVector B (Sum.inr 5480) = Sparse.eval nodeValue5480 (mixedVector B) := by
    change mixedMoment B node5480 node5480Labels = _
    exact sound5480 B hB hF
  have h5482 : mixedVector B (Sum.inr 5482) = Sparse.eval nodeValue5482 (mixedVector B) := by
    change mixedMoment B node5482 node5482Labels = _
    exact sound5482_e B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485_e B hB hF
  simpa only [sourceForm1048, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5065, h5067, h5073, h5074, h5250, h5284, h5348, h5352, h5353, h5401, h5406, h5408, h5410, h5430, h5433, h5439, h5471, h5480, h5482, h5485, reducedSource901] using sourceEq1048 B hB

theorem rowSound901 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row901 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck901, numericCheck901, reducedZero901 B hB hF, mul_zero]

theorem reducedZero904 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource904 (mixedVector B) = 0 := by
  have h3459 : mixedVector B (Sum.inr 3459) = Sparse.eval nodeValue3459 (mixedVector B) := by
    change mixedMoment B node3459 node3459Labels = _
    exact sound3459 B hB hF
  have h3460 : mixedVector B (Sum.inr 3460) = Sparse.eval nodeValue3460 (mixedVector B) := by
    change mixedMoment B node3460 node3460Labels = _
    exact sound3460 B hB hF
  have h3463 : mixedVector B (Sum.inr 3463) = Sparse.eval nodeValue3463 (mixedVector B) := by
    change mixedMoment B node3463 node3463Labels = _
    exact sound3463 B hB hF
  have h3525 : mixedVector B (Sum.inr 3525) = Sparse.eval nodeValue3525 (mixedVector B) := by
    change mixedMoment B node3525 node3525Labels = _
    exact sound3525 B hB hF
  have h3757 : mixedVector B (Sum.inr 3757) = Sparse.eval nodeValue3757 (mixedVector B) := by
    change mixedMoment B node3757 node3757Labels = _
    exact sound3757 B hB hF
  have h3758 : mixedVector B (Sum.inr 3758) = Sparse.eval nodeValue3758 (mixedVector B) := by
    change mixedMoment B node3758 node3758Labels = _
    exact sound3758 B hB hF
  have h3761 : mixedVector B (Sum.inr 3761) = Sparse.eval nodeValue3761 (mixedVector B) := by
    change mixedMoment B node3761 node3761Labels = _
    exact sound3761 B hB hF
  have h3799 : mixedVector B (Sum.inr 3799) = Sparse.eval nodeValue3799 (mixedVector B) := by
    change mixedMoment B node3799 node3799Labels = _
    exact sound3799 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h3802 : mixedVector B (Sum.inr 3802) = Sparse.eval nodeValue3802 (mixedVector B) := by
    change mixedMoment B node3802 node3802Labels = _
    exact sound3802 B hB hF
  have h3803 : mixedVector B (Sum.inr 3803) = Sparse.eval nodeValue3803 (mixedVector B) := by
    change mixedMoment B node3803 node3803Labels = _
    exact sound3803 B hB hF
  have h3807 : mixedVector B (Sum.inr 3807) = Sparse.eval nodeValue3807 (mixedVector B) := by
    change mixedMoment B node3807 node3807Labels = _
    exact sound3807 B hB hF
  have h3808 : mixedVector B (Sum.inr 3808) = Sparse.eval nodeValue3808 (mixedVector B) := by
    change mixedMoment B node3808 node3808Labels = _
    exact sound3808 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h3847 : mixedVector B (Sum.inr 3847) = Sparse.eval nodeValue3847 (mixedVector B) := by
    change mixedMoment B node3847 node3847Labels = _
    exact sound3847_e B hB hF
  have h3852 : mixedVector B (Sum.inr 3852) = Sparse.eval nodeValue3852 (mixedVector B) := by
    change mixedMoment B node3852 node3852Labels = _
    exact sound3852_e B hB hF
  have h3953 : mixedVector B (Sum.inr 3953) = Sparse.eval nodeValue3953 (mixedVector B) := by
    change mixedMoment B node3953 node3953Labels = _
    exact sound3953 B hB hF
  have h3976 : mixedVector B (Sum.inr 3976) = Sparse.eval nodeValue3976 (mixedVector B) := by
    change mixedMoment B node3976 node3976Labels = _
    exact sound3976 B hB hF
  have h3977 : mixedVector B (Sum.inr 3977) = Sparse.eval nodeValue3977 (mixedVector B) := by
    change mixedMoment B node3977 node3977Labels = _
    exact sound3977_e B hB hF
  have h3981 : mixedVector B (Sum.inr 3981) = Sparse.eval nodeValue3981 (mixedVector B) := by
    change mixedMoment B node3981 node3981Labels = _
    exact sound3981_e B hB hF
  simpa only [sourceForm1051, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3459, h3460, h3463, h3525, h3757, h3758, h3761, h3799, h3801, h3802, h3803, h3807, h3808, h3813, h3846, h3847, h3852, h3953, h3976, h3977, h3981, reducedSource904] using sourceEq1051 B hB

theorem rowSound904 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row904 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck904, numericCheck904, reducedZero904 B hB hF, mul_zero]

theorem reducedZero907 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource907 (mixedVector B) = 0 := by
  have h2621 : mixedVector B (Sum.inr 2621) = Sparse.eval nodeValue2621 (mixedVector B) := by
    change mixedMoment B node2621 node2621Labels = _
    exact sound2621 B hB hF
  have h3115 : mixedVector B (Sum.inr 3115) = Sparse.eval nodeValue3115 (mixedVector B) := by
    change mixedMoment B node3115 node3115Labels = _
    exact sound3115 B hB hF
  have h3790 : mixedVector B (Sum.inr 3790) = Sparse.eval nodeValue3790 (mixedVector B) := by
    change mixedMoment B node3790 node3790Labels = _
    exact sound3790 B hB hF
  have h3825 : mixedVector B (Sum.inr 3825) = Sparse.eval nodeValue3825 (mixedVector B) := by
    change mixedMoment B node3825 node3825Labels = _
    exact sound3825 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1054, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2621, h3115, h3790, h3825, h3876, h4091, reducedSource907] using sourceEq1054 B hB

theorem rowSound907 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row907 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck907, numericCheck907, reducedZero907 B hB hF, mul_zero]

theorem sourceRowsAt896 : MixedData.sourceRows (896 : Fin 2425) =
    MixedData.row896 := by decide +kernel

theorem sourceRowsAt897 : MixedData.sourceRows (897 : Fin 2425) =
    MixedData.row897 := by decide +kernel

theorem sourceRowsAt898 : MixedData.sourceRows (898 : Fin 2425) =
    MixedData.row898 := by decide +kernel

theorem sourceRowsAt899 : MixedData.sourceRows (899 : Fin 2425) =
    MixedData.row899 := by decide +kernel

theorem sourceRowsAt900 : MixedData.sourceRows (900 : Fin 2425) =
    MixedData.row900 := by decide +kernel

theorem sourceRowsAt901 : MixedData.sourceRows (901 : Fin 2425) =
    MixedData.row901 := by decide +kernel

theorem sourceRowsAt902 : MixedData.sourceRows (902 : Fin 2425) =
    MixedData.row902 := by decide +kernel

theorem sourceRowsAt903 : MixedData.sourceRows (903 : Fin 2425) =
    MixedData.row903 := by decide +kernel

theorem sourceRowsAt904 : MixedData.sourceRows (904 : Fin 2425) =
    MixedData.row904 := by decide +kernel

theorem sourceRowsAt905 : MixedData.sourceRows (905 : Fin 2425) =
    MixedData.row905 := by decide +kernel

theorem sourceRowsAt906 : MixedData.sourceRows (906 : Fin 2425) =
    MixedData.row906 := by decide +kernel

theorem sourceRowsAt907 : MixedData.sourceRows (907 : Fin 2425) =
    MixedData.row907 := by decide +kernel

theorem sourceRowsAt908 : MixedData.sourceRows (908 : Fin 2425) =
    MixedData.row908 := by decide +kernel

theorem sourceRowsAt909 : MixedData.sourceRows (909 : Fin 2425) =
    MixedData.row909 := by decide +kernel

theorem sourceRowsAt910 : MixedData.sourceRows (910 : Fin 2425) =
    MixedData.row910 := by decide +kernel

theorem sourceRowsAt911 : MixedData.sourceRows (911 : Fin 2425) =
    MixedData.row911 := by decide +kernel

theorem chunkSound56_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 56) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 896 ∨ k.val = 897 ∨ k.val = 898 ∨ k.val = 899 ∨ k.val = 900 ∨ k.val = 901 ∨ k.val = 902 ∨ k.val = 903 ∨ k.val = 904 ∨ k.val = 905 ∨ k.val = 906 ∨ k.val = 907 ∨ k.val = 908 ∨ k.val = 909 ∨ k.val = 910 ∨ k.val = 911 := by omega
  rcases heq with h896 | h897 | h898 | h899 | h900 | h901 | h902 | h903 | h904 | h905 | h906 | h907 | h908 | h909 | h910 | h911
  · have he : k = (896 : Fin 2425) := Fin.ext h896
    subst k
    rw [sourceRowsAt896]
    exact rowSound896 B hB hF
  · have he : k = (897 : Fin 2425) := Fin.ext h897
    subst k
    rw [sourceRowsAt897]
    exact rowSound897_e B hB hF
  · have he : k = (898 : Fin 2425) := Fin.ext h898
    subst k
    rw [sourceRowsAt898]
    exact rowSound898_e B hB hF
  · have he : k = (899 : Fin 2425) := Fin.ext h899
    subst k
    rw [sourceRowsAt899]
    exact rowSound899_e B hB hF
  · have he : k = (900 : Fin 2425) := Fin.ext h900
    subst k
    rw [sourceRowsAt900]
    exact rowSound900_e B hB hF
  · have he : k = (901 : Fin 2425) := Fin.ext h901
    subst k
    rw [sourceRowsAt901]
    exact rowSound901 B hB hF
  · have he : k = (902 : Fin 2425) := Fin.ext h902
    subst k
    rw [sourceRowsAt902]
    exact rowSound902_e B hB hF
  · have he : k = (903 : Fin 2425) := Fin.ext h903
    subst k
    rw [sourceRowsAt903]
    exact rowSound903_e B hB hF
  · have he : k = (904 : Fin 2425) := Fin.ext h904
    subst k
    rw [sourceRowsAt904]
    exact rowSound904 B hB hF
  · have he : k = (905 : Fin 2425) := Fin.ext h905
    subst k
    rw [sourceRowsAt905]
    exact rowSound905_e B hB hF
  · have he : k = (906 : Fin 2425) := Fin.ext h906
    subst k
    rw [sourceRowsAt906]
    exact rowSound906_e B hB hF
  · have he : k = (907 : Fin 2425) := Fin.ext h907
    subst k
    rw [sourceRowsAt907]
    exact rowSound907 B hB hF
  · have he : k = (908 : Fin 2425) := Fin.ext h908
    subst k
    rw [sourceRowsAt908]
    exact rowSound908_e B hB hF
  · have he : k = (909 : Fin 2425) := Fin.ext h909
    subst k
    rw [sourceRowsAt909]
    exact rowSound909_e B hB hF
  · have he : k = (910 : Fin 2425) := Fin.ext h910
    subst k
    rw [sourceRowsAt910]
    exact rowSound910_e B hB hF
  · have he : k = (911 : Fin 2425) := Fin.ext h911
    subst k
    rw [sourceRowsAt911]
    exact rowSound911_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56_e_oai
