-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:24:15.409417+00:00
-- url     : https://prove2.me/submissions/81605778-2028-473f-bd75-6fc851bc012e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5387_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5435_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5439_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5450_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5490_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound928_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound929_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound930_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound931_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound932_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound933_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound935_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound936_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound937_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound938_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound939_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound940_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound941_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound942_e

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

theorem canonical1719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1719 raw1719Labels = mixedMoment B node4787 node4787Labels := by
  calc
    mixedMoment B raw1719 raw1719Labels = mixedMoment B raw1719step0 raw1719step0Labels := by
      have ha : raw1719step0 = (fun i j => raw1719 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1719step0 raw1719; decide +kernel
      have hl : raw1719step0Labels = raw1719Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1719 raw1719Labels permutation152 permutation4
    mixedMoment B raw1719step0 raw1719step0Labels = mixedMoment B raw1719step1 raw1719step1Labels := by
      have ha : raw1719step1 = raw1719step0 := by apply Matrix.ext; unfold raw1719step1 raw1719step0; decide +kernel
      have hl : raw1719step0Labels = labelEmbedding7 ∘ raw1719step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1719step0 raw1719step0Labels raw1719step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4787 node4787Labels := by rfl

theorem canonical1720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1720 raw1720Labels = mixedMoment B node2000 node2000Labels := by
  calc
    mixedMoment B raw1720 raw1720Labels = mixedMoment B raw1720step0 raw1720step0Labels := by
      have ha : raw1720step0 = (fun i j => raw1720 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1720step0 raw1720; decide +kernel
      have hl : raw1720step0Labels = raw1720Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1720 raw1720Labels permutation152 permutation4
    _ = mixedMoment B node2000 node2000Labels := by rfl

theorem canonical1721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1721 raw1721Labels = mixedMoment B node2000 node2000Labels := by
  calc
    mixedMoment B raw1721 raw1721Labels = mixedMoment B raw1721step0 raw1721step0Labels := by
      have ha : raw1721step0 = (fun i j => raw1721 (permutation177 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1721step0 raw1721; decide +kernel
      have hl : raw1721step0Labels = raw1721Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1721 raw1721Labels permutation177 permutation6
    mixedMoment B raw1721step0 raw1721step0Labels = mixedMoment B raw1721step1 raw1721step1Labels := by
      have ha : raw1721step1 = -raw1721step0 := by apply Matrix.ext; change ∀ i j, raw1721step1 i j = -(raw1721step0 i j); unfold raw1721step1 raw1721step0; decide +kernel
      have hl : raw1721step1Labels = raw1721step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1721step1 raw1721step1Labels = mixedMoment B raw1721step2 raw1721step2Labels := by
      have ha : raw1721step2 = raw1721step1 := by apply Matrix.ext; unfold raw1721step2 raw1721step1; decide +kernel
      have hl : raw1721step1Labels = labelEmbedding1 ∘ raw1721step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1721step1 raw1721step1Labels raw1721step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2000 node2000Labels := by rfl

theorem canonical1722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1722 raw1722Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw1722 raw1722Labels = mixedMoment B raw1722step0 raw1722step0Labels := by
      have ha : raw1722step0 = (fun i j => raw1722 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1722step0 raw1722; decide +kernel
      have hl : raw1722step0Labels = raw1722Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1722 raw1722Labels permutation32 permutation4
    mixedMoment B raw1722step0 raw1722step0Labels = mixedMoment B raw1722step1 raw1722step1Labels := by
      have ha : raw1722step1 = raw1722step0 := by apply Matrix.ext; unfold raw1722step1 raw1722step0; decide +kernel
      have hl : raw1722step0Labels = labelEmbedding7 ∘ raw1722step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1722step0 raw1722step0Labels raw1722step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

theorem canonical1723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1723 raw1723Labels = mixedMoment B node2003 node2003Labels := by
  calc
    mixedMoment B raw1723 raw1723Labels = mixedMoment B raw1723step0 raw1723step0Labels := by
      have ha : raw1723step0 = (fun i j => raw1723 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1723step0 raw1723; decide +kernel
      have hl : raw1723step0Labels = raw1723Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1723 raw1723Labels permutation32 permutation4
    _ = mixedMoment B node2003 node2003Labels := by rfl

theorem canonical1724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1724 raw1724Labels = mixedMoment B node2006 node2006Labels := by
  calc
    mixedMoment B raw1724 raw1724Labels = mixedMoment B raw1724step0 raw1724step0Labels := by
      have ha : raw1724step0 = (fun i j => raw1724 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1724step0 raw1724; decide +kernel
      have hl : raw1724step0Labels = raw1724Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1724 raw1724Labels permutation38 permutation6
    mixedMoment B raw1724step0 raw1724step0Labels = mixedMoment B raw1724step1 raw1724step1Labels := by
      have ha : raw1724step1 = -raw1724step0 := by apply Matrix.ext; change ∀ i j, raw1724step1 i j = -(raw1724step0 i j); unfold raw1724step1 raw1724step0; decide +kernel
      have hl : raw1724step1Labels = raw1724step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1724step1 raw1724step1Labels = mixedMoment B raw1724step2 raw1724step2Labels := by
      have ha : raw1724step2 = raw1724step1 := by apply Matrix.ext; unfold raw1724step2 raw1724step1; decide +kernel
      have hl : raw1724step1Labels = labelEmbedding1 ∘ raw1724step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1724step1 raw1724step1Labels raw1724step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2006 node2006Labels := by rfl

theorem canonical1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1725 raw1725Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw1725 raw1725Labels = mixedMoment B raw1725step0 raw1725step0Labels := by
      have ha : raw1725step0 = (fun i j => raw1725 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1725step0 raw1725; decide +kernel
      have hl : raw1725step0Labels = raw1725Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1725 raw1725Labels permutation152 permutation4
    mixedMoment B raw1725step0 raw1725step0Labels = mixedMoment B raw1725step1 raw1725step1Labels := by
      have ha : raw1725step1 = raw1725step0 := by apply Matrix.ext; unfold raw1725step1 raw1725step0; decide +kernel
      have hl : raw1725step0Labels = labelEmbedding7 ∘ raw1725step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1725step0 raw1725step0Labels raw1725step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical1726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1726 raw1726Labels = mixedMoment B node2016 node2016Labels := by
  calc
    mixedMoment B raw1726 raw1726Labels = mixedMoment B raw1726step0 raw1726step0Labels := by
      have ha : raw1726step0 = (fun i j => raw1726 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1726step0 raw1726; decide +kernel
      have hl : raw1726step0Labels = raw1726Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1726 raw1726Labels permutation152 permutation4
    _ = mixedMoment B node2016 node2016Labels := by rfl

theorem canonical1727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1727 raw1727Labels = mixedMoment B node2075 node2075Labels := by
  calc
    mixedMoment B raw1727 raw1727Labels = mixedMoment B raw1727step0 raw1727step0Labels := by
      have ha : raw1727step0 = (fun i j => raw1727 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1727step0 raw1727; decide +kernel
      have hl : raw1727step0Labels = raw1727Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1727 raw1727Labels permutation200 permutation6
    mixedMoment B raw1727step0 raw1727step0Labels = mixedMoment B raw1727step1 raw1727step1Labels := by
      have ha : raw1727step1 = -raw1727step0 := by apply Matrix.ext; change ∀ i j, raw1727step1 i j = -(raw1727step0 i j); unfold raw1727step1 raw1727step0; decide +kernel
      have hl : raw1727step1Labels = raw1727step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1727step1 raw1727step1Labels = mixedMoment B raw1727step2 raw1727step2Labels := by
      have ha : raw1727step2 = raw1727step1 := by apply Matrix.ext; unfold raw1727step2 raw1727step1; decide +kernel
      have hl : raw1727step1Labels = labelEmbedding1 ∘ raw1727step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1727step1 raw1727step1Labels raw1727step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2075 node2075Labels := by rfl

theorem canonical1728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1728 raw1728Labels = mixedMoment B node4800 node4800Labels := by
  calc
    mixedMoment B raw1728 raw1728Labels = mixedMoment B raw1728step0 raw1728step0Labels := by
      have ha : raw1728step0 = (fun i j => raw1728 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1728step0 raw1728; decide +kernel
      have hl : raw1728step0Labels = raw1728Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1728 raw1728Labels permutation32 permutation4
    mixedMoment B raw1728step0 raw1728step0Labels = mixedMoment B raw1728step1 raw1728step1Labels := by
      have ha : raw1728step1 = raw1728step0 := by apply Matrix.ext; unfold raw1728step1 raw1728step0; decide +kernel
      have hl : raw1728step0Labels = labelEmbedding7 ∘ raw1728step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1728step0 raw1728step0Labels raw1728step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4800 node4800Labels := by rfl

theorem canonical1729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1729 raw1729Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw1729 raw1729Labels = mixedMoment B raw1729step0 raw1729step0Labels := by
      have ha : raw1729step0 = (fun i j => raw1729 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1729step0 raw1729; decide +kernel
      have hl : raw1729step0Labels = raw1729Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1729 raw1729Labels permutation32 permutation4
    _ = mixedMoment B node2018 node2018Labels := by rfl

theorem canonical1730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1730 raw1730Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw1730 raw1730Labels = mixedMoment B raw1730step0 raw1730step0Labels := by
      have ha : raw1730step0 = (fun i j => raw1730 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1730step0 raw1730; decide +kernel
      have hl : raw1730step0Labels = raw1730Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1730 raw1730Labels permutation143 permutation6
    mixedMoment B raw1730step0 raw1730step0Labels = mixedMoment B raw1730step1 raw1730step1Labels := by
      have ha : raw1730step1 = raw1730step0 := by apply Matrix.ext; unfold raw1730step1 raw1730step0; decide +kernel
      have hl : raw1730step0Labels = labelEmbedding1 ∘ raw1730step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1730step0 raw1730step0Labels raw1730step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2018 node2018Labels := by rfl

theorem canonical1746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1746 raw1746Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw1746 raw1746Labels = mixedMoment B raw1746step0 raw1746step0Labels := by
      have ha : raw1746step0 = (fun i j => raw1746 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1746step0 raw1746; decide +kernel
      have hl : raw1746step0Labels = raw1746Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1746 raw1746Labels permutation32 permutation4
    mixedMoment B raw1746step0 raw1746step0Labels = mixedMoment B raw1746step1 raw1746step1Labels := by
      have ha : raw1746step1 = raw1746step0 := by apply Matrix.ext; unfold raw1746step1 raw1746step0; decide +kernel
      have hl : raw1746step0Labels = labelEmbedding7 ∘ raw1746step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1746step0 raw1746step0Labels raw1746step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

theorem canonical1747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1747 raw1747Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw1747 raw1747Labels = mixedMoment B raw1747step0 raw1747step0Labels := by
      have ha : raw1747step0 = (fun i j => raw1747 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1747step0 raw1747; decide +kernel
      have hl : raw1747step0Labels = raw1747Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1747 raw1747Labels permutation32 permutation4
    _ = mixedMoment B node2028 node2028Labels := by rfl

theorem canonical1748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1748 raw1748Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw1748 raw1748Labels = mixedMoment B raw1748step0 raw1748step0Labels := by
      have ha : raw1748step0 = (fun i j => raw1748 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1748step0 raw1748; decide +kernel
      have hl : raw1748step0Labels = raw1748Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1748 raw1748Labels permutation34 permutation6
    mixedMoment B raw1748step0 raw1748step0Labels = mixedMoment B raw1748step1 raw1748step1Labels := by
      have ha : raw1748step1 = -raw1748step0 := by apply Matrix.ext; change ∀ i j, raw1748step1 i j = -(raw1748step0 i j); unfold raw1748step1 raw1748step0; decide +kernel
      have hl : raw1748step1Labels = raw1748step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1748step1 raw1748step1Labels = mixedMoment B raw1748step2 raw1748step2Labels := by
      have ha : raw1748step2 = raw1748step1 := by apply Matrix.ext; unfold raw1748step2 raw1748step1; decide +kernel
      have hl : raw1748step1Labels = labelEmbedding1 ∘ raw1748step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1748step1 raw1748step1Labels raw1748step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical1758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1758 raw1758Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw1758 raw1758Labels = mixedMoment B raw1758step0 raw1758step0Labels := by
      have ha : raw1758step0 = (fun i j => raw1758 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1758step0 raw1758; decide +kernel
      have hl : raw1758step0Labels = raw1758Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1758 raw1758Labels permutation32 permutation4
    mixedMoment B raw1758step0 raw1758step0Labels = mixedMoment B raw1758step1 raw1758step1Labels := by
      have ha : raw1758step1 = raw1758step0 := by apply Matrix.ext; unfold raw1758step1 raw1758step0; decide +kernel
      have hl : raw1758step0Labels = labelEmbedding7 ∘ raw1758step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1758step0 raw1758step0Labels raw1758step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

theorem canonical1759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1759 raw1759Labels = mixedMoment B node2048 node2048Labels := by
  calc
    mixedMoment B raw1759 raw1759Labels = mixedMoment B raw1759step0 raw1759step0Labels := by
      have ha : raw1759step0 = (fun i j => raw1759 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1759step0 raw1759; decide +kernel
      have hl : raw1759step0Labels = raw1759Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1759 raw1759Labels permutation32 permutation4
    _ = mixedMoment B node2048 node2048Labels := by rfl

theorem canonical1760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1760 raw1760Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw1760 raw1760Labels = mixedMoment B raw1760step0 raw1760step0Labels := by
      have ha : raw1760step0 = (fun i j => raw1760 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1760step0 raw1760; decide +kernel
      have hl : raw1760step0Labels = raw1760Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1760 raw1760Labels permutation38 permutation6
    mixedMoment B raw1760step0 raw1760step0Labels = mixedMoment B raw1760step1 raw1760step1Labels := by
      have ha : raw1760step1 = -raw1760step0 := by apply Matrix.ext; change ∀ i j, raw1760step1 i j = -(raw1760step0 i j); unfold raw1760step1 raw1760step0; decide +kernel
      have hl : raw1760step1Labels = raw1760step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1760step1 raw1760step1Labels = mixedMoment B raw1760step2 raw1760step2Labels := by
      have ha : raw1760step2 = raw1760step1 := by apply Matrix.ext; unfold raw1760step2 raw1760step1; decide +kernel
      have hl : raw1760step1Labels = labelEmbedding1 ∘ raw1760step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1760step1 raw1760step1Labels raw1760step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2082 node2082Labels := by rfl

theorem canonical1767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1767 raw1767Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw1767 raw1767Labels = mixedMoment B raw1767step0 raw1767step0Labels := by
      have ha : raw1767step0 = (fun i j => raw1767 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1767step0 raw1767; decide +kernel
      have hl : raw1767step0Labels = raw1767Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1767 raw1767Labels permutation32 permutation4
    mixedMoment B raw1767step0 raw1767step0Labels = mixedMoment B raw1767step1 raw1767step1Labels := by
      have ha : raw1767step1 = raw1767step0 := by apply Matrix.ext; unfold raw1767step1 raw1767step0; decide +kernel
      have hl : raw1767step0Labels = labelEmbedding7 ∘ raw1767step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1767step0 raw1767step0Labels raw1767step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical1768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1768 raw1768Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw1768 raw1768Labels = mixedMoment B raw1768step0 raw1768step0Labels := by
      have ha : raw1768step0 = (fun i j => raw1768 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1768step0 raw1768; decide +kernel
      have hl : raw1768step0Labels = raw1768Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1768 raw1768Labels permutation32 permutation4
    _ = mixedMoment B node2054 node2054Labels := by rfl

theorem canonical1769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1769 raw1769Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw1769 raw1769Labels = mixedMoment B raw1769step0 raw1769step0Labels := by
      have ha : raw1769step0 = (fun i j => raw1769 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1769step0 raw1769; decide +kernel
      have hl : raw1769step0Labels = raw1769Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1769 raw1769Labels permutation33 permutation6
    mixedMoment B raw1769step0 raw1769step0Labels = mixedMoment B raw1769step1 raw1769step1Labels := by
      have ha : raw1769step1 = -raw1769step0 := by apply Matrix.ext; change ∀ i j, raw1769step1 i j = -(raw1769step0 i j); unfold raw1769step1 raw1769step0; decide +kernel
      have hl : raw1769step1Labels = raw1769step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1769step1 raw1769step1Labels = mixedMoment B raw1769step2 raw1769step2Labels := by
      have ha : raw1769step2 = raw1769step1 := by apply Matrix.ext; unfold raw1769step2 raw1769step1; decide +kernel
      have hl : raw1769step1Labels = labelEmbedding1 ∘ raw1769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1769step1 raw1769step1Labels raw1769step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

theorem canonical1791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1791 raw1791Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw1791 raw1791Labels = mixedMoment B raw1791step0 raw1791step0Labels := by
      have ha : raw1791step0 = (fun i j => raw1791 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1791step0 raw1791; decide +kernel
      have hl : raw1791step0Labels = raw1791Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1791 raw1791Labels permutation32 permutation4
    mixedMoment B raw1791step0 raw1791step0Labels = mixedMoment B raw1791step1 raw1791step1Labels := by
      have ha : raw1791step1 = raw1791step0 := by apply Matrix.ext; unfold raw1791step1 raw1791step0; decide +kernel
      have hl : raw1791step0Labels = labelEmbedding7 ∘ raw1791step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1791step0 raw1791step0Labels raw1791step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

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

theorem canonical1792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1792 raw1792Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw1792 raw1792Labels = mixedMoment B raw1792step0 raw1792step0Labels := by
      have ha : raw1792step0 = (fun i j => raw1792 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1792step0 raw1792; decide +kernel
      have hl : raw1792step0Labels = raw1792Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1792 raw1792Labels permutation32 permutation4
    _ = mixedMoment B node2106 node2106Labels := by rfl

theorem canonical1793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1793 raw1793Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw1793 raw1793Labels = mixedMoment B raw1793step0 raw1793step0Labels := by
      have ha : raw1793step0 = (fun i j => raw1793 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1793step0 raw1793; decide +kernel
      have hl : raw1793step0Labels = raw1793Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1793 raw1793Labels permutation40 permutation6
    mixedMoment B raw1793step0 raw1793step0Labels = mixedMoment B raw1793step1 raw1793step1Labels := by
      have ha : raw1793step1 = -raw1793step0 := by apply Matrix.ext; change ∀ i j, raw1793step1 i j = -(raw1793step0 i j); unfold raw1793step1 raw1793step0; decide +kernel
      have hl : raw1793step1Labels = raw1793step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1793step1 raw1793step1Labels = mixedMoment B raw1793step2 raw1793step2Labels := by
      have ha : raw1793step2 = raw1793step1 := by apply Matrix.ext; unfold raw1793step2 raw1793step1; decide +kernel
      have hl : raw1793step1Labels = labelEmbedding1 ∘ raw1793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1793step1 raw1793step1Labels raw1793step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical140
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17948 raw17948Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw17948 raw17948Labels = mixedMoment B raw17948step0 raw17948step0Labels := by
      have hz : ∀ j, raw17948 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17948step0 = (fun i j => raw17948 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17948step0 raw17948; decide +kernel
      have hl : raw17948step0Labels = raw17948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17948 raw17948Labels permutation434 hz
    mixedMoment B raw17948step0 raw17948step0Labels = mixedMoment B raw17948step1 raw17948step1Labels := by
      have ha : raw17948step1 = (fun i j => raw17948step0 (permutation58 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17948step1 raw17948step0; decide +kernel
      have hl : raw17948step1Labels = raw17948step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17948step0 raw17948step0Labels permutation58 permutation5
    mixedMoment B raw17948step1 raw17948step1Labels = mixedMoment B raw17948step2 raw17948step2Labels := by
      have ha : raw17948step2 = -raw17948step1 := by apply Matrix.ext; change ∀ i j, raw17948step2 i j = -(raw17948step1 i j); unfold raw17948step2 raw17948step1; decide +kernel
      have hl : raw17948step2Labels = raw17948step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17948step2 raw17948step2Labels = mixedMoment B raw17948step3 raw17948step3Labels := by
      have ha : raw17948step3 = raw17948step2 := by apply Matrix.ext; unfold raw17948step3 raw17948step2; decide +kernel
      have hl : raw17948step2Labels = labelEmbedding8 ∘ raw17948step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17948step2 raw17948step2Labels raw17948step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical17949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17949 raw17949Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw17949 raw17949Labels = mixedMoment B raw17949step0 raw17949step0Labels := by
      have hz : ∀ j, raw17949 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17949step0 = (fun i j => raw17949 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17949step0 raw17949; decide +kernel
      have hl : raw17949step0Labels = raw17949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17949 raw17949Labels permutation434 hz
    mixedMoment B raw17949step0 raw17949step0Labels = mixedMoment B raw17949step1 raw17949step1Labels := by
      have ha : raw17949step1 = (fun i j => raw17949step0 (permutation147 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17949step1 raw17949step0; decide +kernel
      have hl : raw17949step1Labels = raw17949step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17949step0 raw17949step0Labels permutation147 permutation3
    mixedMoment B raw17949step1 raw17949step1Labels = mixedMoment B raw17949step2 raw17949step2Labels := by
      have ha : raw17949step2 = -raw17949step1 := by apply Matrix.ext; change ∀ i j, raw17949step2 i j = -(raw17949step1 i j); unfold raw17949step2 raw17949step1; decide +kernel
      have hl : raw17949step2Labels = raw17949step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17949step2 raw17949step2Labels = mixedMoment B raw17949step3 raw17949step3Labels := by
      have ha : raw17949step3 = raw17949step2 := by apply Matrix.ext; unfold raw17949step3 raw17949step2; decide +kernel
      have hl : raw17949step2Labels = labelEmbedding6 ∘ raw17949step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17949step2 raw17949step2Labels raw17949step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical17950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17950 raw17950Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17950 raw17950Labels = mixedMoment B raw17950step0 raw17950step0Labels := by
      have ha : raw17950step0 = (fun i j => raw17950 (permutation642 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17950step0 raw17950; decide +kernel
      have hl : raw17950step0Labels = raw17950Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17950 raw17950Labels permutation642 permutation5
    mixedMoment B raw17950step0 raw17950step0Labels = mixedMoment B raw17950step1 raw17950step1Labels := by
      have ha : raw17950step1 = raw17950step0 := by apply Matrix.ext; unfold raw17950step1 raw17950step0; decide +kernel
      have hl : raw17950step0Labels = labelEmbedding8 ∘ raw17950step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17950step0 raw17950step0Labels raw17950step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical17951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17951 raw17951Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw17951 raw17951Labels = mixedMoment B raw17951step0 raw17951step0Labels := by
      have hz : ∀ j, raw17951 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17951step0 = (fun i j => raw17951 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17951step0 raw17951; decide +kernel
      have hl : raw17951step0Labels = raw17951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17951 raw17951Labels permutation434 hz
    mixedMoment B raw17951step0 raw17951step0Labels = mixedMoment B raw17951step1 raw17951step1Labels := by
      have ha : raw17951step1 = (fun i j => raw17951step0 (permutation141 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17951step1 raw17951step0; decide +kernel
      have hl : raw17951step1Labels = raw17951step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17951step0 raw17951step0Labels permutation141 permutation5
    mixedMoment B raw17951step1 raw17951step1Labels = mixedMoment B raw17951step2 raw17951step2Labels := by
      have ha : raw17951step2 = raw17951step1 := by apply Matrix.ext; unfold raw17951step2 raw17951step1; decide +kernel
      have hl : raw17951step1Labels = labelEmbedding8 ∘ raw17951step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17951step1 raw17951step1Labels raw17951step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical17952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17952 raw17952Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw17952 raw17952Labels = mixedMoment B raw17952step0 raw17952step0Labels := by
      have hz : ∀ j, raw17952 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17952step0 = (fun i j => raw17952 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17952step0 raw17952; decide +kernel
      have hl : raw17952step0Labels = raw17952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17952 raw17952Labels permutation434 hz
    mixedMoment B raw17952step0 raw17952step0Labels = mixedMoment B raw17952step1 raw17952step1Labels := by
      have ha : raw17952step1 = (fun i j => raw17952step0 (permutation69 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17952step1 raw17952step0; decide +kernel
      have hl : raw17952step1Labels = raw17952step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17952step0 raw17952step0Labels permutation69 permutation4
    mixedMoment B raw17952step1 raw17952step1Labels = mixedMoment B raw17952step2 raw17952step2Labels := by
      have ha : raw17952step2 = -raw17952step1 := by apply Matrix.ext; change ∀ i j, raw17952step2 i j = -(raw17952step1 i j); unfold raw17952step2 raw17952step1; decide +kernel
      have hl : raw17952step2Labels = raw17952step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17952step2 raw17952step2Labels = mixedMoment B raw17952step3 raw17952step3Labels := by
      have ha : raw17952step3 = raw17952step2 := by apply Matrix.ext; unfold raw17952step3 raw17952step2; decide +kernel
      have hl : raw17952step2Labels = labelEmbedding7 ∘ raw17952step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17952step2 raw17952step2Labels raw17952step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical17953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17953 raw17953Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw17953 raw17953Labels = mixedMoment B raw17953step0 raw17953step0Labels := by
      have hz : ∀ j, raw17953 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17953step0 = (fun i j => raw17953 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17953step0 raw17953; decide +kernel
      have hl : raw17953step0Labels = raw17953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17953 raw17953Labels permutation434 hz
    mixedMoment B raw17953step0 raw17953step0Labels = mixedMoment B raw17953step1 raw17953step1Labels := by
      have ha : raw17953step1 = (fun i j => raw17953step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17953step1 raw17953step0; decide +kernel
      have hl : raw17953step1Labels = raw17953step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17953step0 raw17953step0Labels permutation32 permutation3
    mixedMoment B raw17953step1 raw17953step1Labels = mixedMoment B raw17953step2 raw17953step2Labels := by
      have ha : raw17953step2 = raw17953step1 := by apply Matrix.ext; unfold raw17953step2 raw17953step1; decide +kernel
      have hl : raw17953step1Labels = labelEmbedding6 ∘ raw17953step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17953step1 raw17953step1Labels raw17953step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical17954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17954 raw17954Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw17954 raw17954Labels = mixedMoment B raw17954step0 raw17954step0Labels := by
      have hz : ∀ j, raw17954 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17954step0 = (fun i j => raw17954 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17954step0 raw17954; decide +kernel
      have hl : raw17954step0Labels = raw17954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17954 raw17954Labels permutation434 hz
    mixedMoment B raw17954step0 raw17954step0Labels = mixedMoment B raw17954step1 raw17954step1Labels := by
      have ha : raw17954step1 = (fun i j => raw17954step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17954step1 raw17954step0; decide +kernel
      have hl : raw17954step1Labels = raw17954step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17954step0 raw17954step0Labels permutation149 permutation3
    mixedMoment B raw17954step1 raw17954step1Labels = mixedMoment B raw17954step2 raw17954step2Labels := by
      have ha : raw17954step2 = -raw17954step1 := by apply Matrix.ext; change ∀ i j, raw17954step2 i j = -(raw17954step1 i j); unfold raw17954step2 raw17954step1; decide +kernel
      have hl : raw17954step2Labels = raw17954step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17954step2 raw17954step2Labels = mixedMoment B raw17954step3 raw17954step3Labels := by
      have ha : raw17954step3 = raw17954step2 := by apply Matrix.ext; unfold raw17954step3 raw17954step2; decide +kernel
      have hl : raw17954step2Labels = labelEmbedding6 ∘ raw17954step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17954step2 raw17954step2Labels raw17954step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical17955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17955 raw17955Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17955 raw17955Labels = mixedMoment B raw17955step0 raw17955step0Labels := by
      have ha : raw17955step0 = (fun i j => raw17955 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17955step0 raw17955; decide +kernel
      have hl : raw17955step0Labels = raw17955Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17955 raw17955Labels permutation680 permutation3
    mixedMoment B raw17955step0 raw17955step0Labels = mixedMoment B raw17955step1 raw17955step1Labels := by
      have ha : raw17955step1 = -raw17955step0 := by apply Matrix.ext; change ∀ i j, raw17955step1 i j = -(raw17955step0 i j); unfold raw17955step1 raw17955step0; decide +kernel
      have hl : raw17955step1Labels = raw17955step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17955step1 raw17955step1Labels = mixedMoment B raw17955step2 raw17955step2Labels := by
      have ha : raw17955step2 = raw17955step1 := by apply Matrix.ext; unfold raw17955step2 raw17955step1; decide +kernel
      have hl : raw17955step1Labels = labelEmbedding6 ∘ raw17955step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17955step1 raw17955step1Labels raw17955step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

theorem canonical17956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17956 raw17956Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw17956 raw17956Labels = mixedMoment B raw17956step0 raw17956step0Labels := by
      have hz : ∀ j, raw17956 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17956step0 = (fun i j => raw17956 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17956step0 raw17956; decide +kernel
      have hl : raw17956step0Labels = raw17956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17956 raw17956Labels permutation434 hz
    mixedMoment B raw17956step0 raw17956step0Labels = mixedMoment B raw17956step1 raw17956step1Labels := by
      have ha : raw17956step1 = (fun i j => raw17956step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17956step1 raw17956step0; decide +kernel
      have hl : raw17956step1Labels = raw17956step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17956step0 raw17956step0Labels permutation143 permutation5
    mixedMoment B raw17956step1 raw17956step1Labels = mixedMoment B raw17956step2 raw17956step2Labels := by
      have ha : raw17956step2 = raw17956step1 := by apply Matrix.ext; unfold raw17956step2 raw17956step1; decide +kernel
      have hl : raw17956step1Labels = labelEmbedding8 ∘ raw17956step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17956step1 raw17956step1Labels raw17956step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical17957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17957 raw17957Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw17957 raw17957Labels = mixedMoment B raw17957step0 raw17957step0Labels := by
      have hz : ∀ j, raw17957 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17957step0 = (fun i j => raw17957 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17957step0 raw17957; decide +kernel
      have hl : raw17957step0Labels = raw17957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17957 raw17957Labels permutation434 hz
    mixedMoment B raw17957step0 raw17957step0Labels = mixedMoment B raw17957step1 raw17957step1Labels := by
      have ha : raw17957step1 = (fun i j => raw17957step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17957step1 raw17957step0; decide +kernel
      have hl : raw17957step1Labels = raw17957step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17957step0 raw17957step0Labels permutation39 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical17958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17958 raw17958Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw17958 raw17958Labels = mixedMoment B raw17958step0 raw17958step0Labels := by
      have hz : ∀ j, raw17958 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17958step0 = (fun i j => raw17958 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17958step0 raw17958; decide +kernel
      have hl : raw17958step0Labels = raw17958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17958 raw17958Labels permutation434 hz
    mixedMoment B raw17958step0 raw17958step0Labels = mixedMoment B raw17958step1 raw17958step1Labels := by
      have ha : raw17958step1 = (fun i j => raw17958step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17958step1 raw17958step0; decide +kernel
      have hl : raw17958step1Labels = raw17958step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17958step0 raw17958step0Labels permutation34 permutation3
    mixedMoment B raw17958step1 raw17958step1Labels = mixedMoment B raw17958step2 raw17958step2Labels := by
      have ha : raw17958step2 = raw17958step1 := by apply Matrix.ext; unfold raw17958step2 raw17958step1; decide +kernel
      have hl : raw17958step1Labels = labelEmbedding6 ∘ raw17958step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17958step1 raw17958step1Labels raw17958step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

theorem canonical17959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17959 raw17959Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw17959 raw17959Labels = mixedMoment B raw17959step0 raw17959step0Labels := by
      have hz : ∀ j, raw17959 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17959step0 = (fun i j => raw17959 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17959step0 raw17959; decide +kernel
      have hl : raw17959step0Labels = raw17959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17959 raw17959Labels permutation434 hz
    mixedMoment B raw17959step0 raw17959step0Labels = mixedMoment B raw17959step1 raw17959step1Labels := by
      have ha : raw17959step1 = (fun i j => raw17959step0 (permutation58 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17959step1 raw17959step0; decide +kernel
      have hl : raw17959step1Labels = raw17959step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17959step0 raw17959step0Labels permutation58 permutation5
    mixedMoment B raw17959step1 raw17959step1Labels = mixedMoment B raw17959step2 raw17959step2Labels := by
      have ha : raw17959step2 = -raw17959step1 := by apply Matrix.ext; change ∀ i j, raw17959step2 i j = -(raw17959step1 i j); unfold raw17959step2 raw17959step1; decide +kernel
      have hl : raw17959step2Labels = raw17959step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17959step2 raw17959step2Labels = mixedMoment B raw17959step3 raw17959step3Labels := by
      have ha : raw17959step3 = raw17959step2 := by apply Matrix.ext; unfold raw17959step3 raw17959step2; decide +kernel
      have hl : raw17959step2Labels = labelEmbedding8 ∘ raw17959step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17959step2 raw17959step2Labels raw17959step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

theorem canonical17960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17960 raw17960Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw17960 raw17960Labels = mixedMoment B raw17960step0 raw17960step0Labels := by
      have ha : raw17960step0 = (fun i j => raw17960 (permutation645 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17960step0 raw17960; decide +kernel
      have hl : raw17960step0Labels = raw17960Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17960 raw17960Labels permutation645 permutation5
    mixedMoment B raw17960step0 raw17960step0Labels = mixedMoment B raw17960step1 raw17960step1Labels := by
      have ha : raw17960step1 = raw17960step0 := by apply Matrix.ext; unfold raw17960step1 raw17960step0; decide +kernel
      have hl : raw17960step0Labels = labelEmbedding8 ∘ raw17960step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17960step0 raw17960step0Labels raw17960step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

theorem canonical17961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17961 raw17961Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw17961 raw17961Labels = mixedMoment B raw17961step0 raw17961step0Labels := by
      have hz : ∀ j, raw17961 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17961step0 = (fun i j => raw17961 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17961step0 raw17961; decide +kernel
      have hl : raw17961step0Labels = raw17961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17961 raw17961Labels permutation434 hz
    mixedMoment B raw17961step0 raw17961step0Labels = mixedMoment B raw17961step1 raw17961step1Labels := by
      have ha : raw17961step1 = (fun i j => raw17961step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17961step1 raw17961step0; decide +kernel
      have hl : raw17961step1Labels = raw17961step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17961step0 raw17961step0Labels permutation144 permutation5
    mixedMoment B raw17961step1 raw17961step1Labels = mixedMoment B raw17961step2 raw17961step2Labels := by
      have ha : raw17961step2 = raw17961step1 := by apply Matrix.ext; unfold raw17961step2 raw17961step1; decide +kernel
      have hl : raw17961step1Labels = labelEmbedding8 ∘ raw17961step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17961step1 raw17961step1Labels raw17961step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

theorem canonical17962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17962 raw17962Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw17962 raw17962Labels = mixedMoment B raw17962step0 raw17962step0Labels := by
      have hz : ∀ j, raw17962 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17962step0 = (fun i j => raw17962 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17962step0 raw17962; decide +kernel
      have hl : raw17962step0Labels = raw17962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17962 raw17962Labels permutation434 hz
    mixedMoment B raw17962step0 raw17962step0Labels = mixedMoment B raw17962step1 raw17962step1Labels := by
      have ha : raw17962step1 = (fun i j => raw17962step0 (permutation59 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17962step1 raw17962step0; decide +kernel
      have hl : raw17962step1Labels = raw17962step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17962step0 raw17962step0Labels permutation59 permutation5
    mixedMoment B raw17962step1 raw17962step1Labels = mixedMoment B raw17962step2 raw17962step2Labels := by
      have ha : raw17962step2 = -raw17962step1 := by apply Matrix.ext; change ∀ i j, raw17962step2 i j = -(raw17962step1 i j); unfold raw17962step2 raw17962step1; decide +kernel
      have hl : raw17962step2Labels = raw17962step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17962step2 raw17962step2Labels = mixedMoment B raw17962step3 raw17962step3Labels := by
      have ha : raw17962step3 = raw17962step2 := by apply Matrix.ext; unfold raw17962step3 raw17962step2; decide +kernel
      have hl : raw17962step2Labels = labelEmbedding8 ∘ raw17962step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17962step2 raw17962step2Labels raw17962step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical17963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17963 raw17963Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw17963 raw17963Labels = mixedMoment B raw17963step0 raw17963step0Labels := by
      have ha : raw17963step0 = (fun i j => raw17963 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17963step0 raw17963; decide +kernel
      have hl : raw17963step0Labels = raw17963Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17963 raw17963Labels permutation154 permutation3
    mixedMoment B raw17963step0 raw17963step0Labels = mixedMoment B raw17963step1 raw17963step1Labels := by
      have ha : raw17963step1 = raw17963step0 := by apply Matrix.ext; unfold raw17963step1 raw17963step0; decide +kernel
      have hl : raw17963step0Labels = labelEmbedding6 ∘ raw17963step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17963step0 raw17963step0Labels raw17963step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

theorem canonical17964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17964 raw17964Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw17964 raw17964Labels = mixedMoment B raw17964step0 raw17964step0Labels := by
      have ha : raw17964step0 = (fun i j => raw17964 (permutation277 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17964step0 raw17964; decide +kernel
      have hl : raw17964step0Labels = raw17964Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17964 raw17964Labels permutation277 permutation5
    mixedMoment B raw17964step0 raw17964step0Labels = mixedMoment B raw17964step1 raw17964step1Labels := by
      have ha : raw17964step1 = -raw17964step0 := by apply Matrix.ext; change ∀ i j, raw17964step1 i j = -(raw17964step0 i j); unfold raw17964step1 raw17964step0; decide +kernel
      have hl : raw17964step1Labels = raw17964step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17964step1 raw17964step1Labels = mixedMoment B raw17964step2 raw17964step2Labels := by
      have ha : raw17964step2 = raw17964step1 := by apply Matrix.ext; unfold raw17964step2 raw17964step1; decide +kernel
      have hl : raw17964step1Labels = labelEmbedding8 ∘ raw17964step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17964step1 raw17964step1Labels raw17964step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

theorem canonical17965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17965 raw17965Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw17965 raw17965Labels = mixedMoment B raw17965step0 raw17965step0Labels := by
      have ha : raw17965step0 = (fun i j => raw17965 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17965step0 raw17965; decide +kernel
      have hl : raw17965step0Labels = raw17965Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17965 raw17965Labels permutation664 permutation3
    mixedMoment B raw17965step0 raw17965step0Labels = mixedMoment B raw17965step1 raw17965step1Labels := by
      have ha : raw17965step1 = -raw17965step0 := by apply Matrix.ext; change ∀ i j, raw17965step1 i j = -(raw17965step0 i j); unfold raw17965step1 raw17965step0; decide +kernel
      have hl : raw17965step1Labels = raw17965step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17965step1 raw17965step1Labels = mixedMoment B raw17965step2 raw17965step2Labels := by
      have ha : raw17965step2 = raw17965step1 := by apply Matrix.ext; unfold raw17965step2 raw17965step1; decide +kernel
      have hl : raw17965step1Labels = labelEmbedding6 ∘ raw17965step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17965step1 raw17965step1Labels raw17965step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

theorem canonical17966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17966 raw17966Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw17966 raw17966Labels = mixedMoment B raw17966step0 raw17966step0Labels := by
      have ha : raw17966step0 = (fun i j => raw17966 (permutation657 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17966step0 raw17966; decide +kernel
      have hl : raw17966step0Labels = raw17966Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17966 raw17966Labels permutation657 permutation5
    mixedMoment B raw17966step0 raw17966step0Labels = mixedMoment B raw17966step1 raw17966step1Labels := by
      have ha : raw17966step1 = raw17966step0 := by apply Matrix.ext; unfold raw17966step1 raw17966step0; decide +kernel
      have hl : raw17966step0Labels = labelEmbedding8 ∘ raw17966step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17966step0 raw17966step0Labels raw17966step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

theorem canonical17967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17967 raw17967Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw17967 raw17967Labels = mixedMoment B raw17967step0 raw17967step0Labels := by
      have ha : raw17967step0 = (fun i j => raw17967 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17967step0 raw17967; decide +kernel
      have hl : raw17967step0Labels = raw17967Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17967 raw17967Labels permutation154 permutation3
    mixedMoment B raw17967step0 raw17967step0Labels = mixedMoment B raw17967step1 raw17967step1Labels := by
      have ha : raw17967step1 = raw17967step0 := by apply Matrix.ext; unfold raw17967step1 raw17967step0; decide +kernel
      have hl : raw17967step0Labels = labelEmbedding6 ∘ raw17967step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17967step0 raw17967step0Labels raw17967step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5472 node5472Labels := by rfl

theorem canonical17968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17968 raw17968Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw17968 raw17968Labels = mixedMoment B raw17968step0 raw17968step0Labels := by
      have hz : ∀ j, raw17968 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17968step0 = (fun i j => raw17968 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17968step0 raw17968; decide +kernel
      have hl : raw17968step0Labels = raw17968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17968 raw17968Labels permutation434 hz
    mixedMoment B raw17968step0 raw17968step0Labels = mixedMoment B raw17968step1 raw17968step1Labels := by
      have ha : raw17968step1 = (fun i j => raw17968step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17968step1 raw17968step0; decide +kernel
      have hl : raw17968step1Labels = raw17968step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17968step0 raw17968step0Labels permutation32 permutation3
    mixedMoment B raw17968step1 raw17968step1Labels = mixedMoment B raw17968step2 raw17968step2Labels := by
      have ha : raw17968step2 = raw17968step1 := by apply Matrix.ext; unfold raw17968step2 raw17968step1; decide +kernel
      have hl : raw17968step1Labels = labelEmbedding6 ∘ raw17968step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17968step1 raw17968step1Labels raw17968step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

theorem canonical17969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17969 raw17969Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw17969 raw17969Labels = mixedMoment B raw17969step0 raw17969step0Labels := by
      have hz : ∀ j, raw17969 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17969step0 = (fun i j => raw17969 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17969step0 raw17969; decide +kernel
      have hl : raw17969step0Labels = raw17969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17969 raw17969Labels permutation434 hz
    mixedMoment B raw17969step0 raw17969step0Labels = mixedMoment B raw17969step1 raw17969step1Labels := by
      have ha : raw17969step1 = (fun i j => raw17969step0 (permutation56 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17969step1 raw17969step0; decide +kernel
      have hl : raw17969step1Labels = raw17969step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17969step0 raw17969step0Labels permutation56 permutation5
    mixedMoment B raw17969step1 raw17969step1Labels = mixedMoment B raw17969step2 raw17969step2Labels := by
      have ha : raw17969step2 = -raw17969step1 := by apply Matrix.ext; change ∀ i j, raw17969step2 i j = -(raw17969step1 i j); unfold raw17969step2 raw17969step1; decide +kernel
      have hl : raw17969step2Labels = raw17969step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17969step2 raw17969step2Labels = mixedMoment B raw17969step3 raw17969step3Labels := by
      have ha : raw17969step3 = raw17969step2 := by apply Matrix.ext; unfold raw17969step3 raw17969step2; decide +kernel
      have hl : raw17969step2Labels = labelEmbedding8 ∘ raw17969step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17969step2 raw17969step2Labels raw17969step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

theorem canonical17970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17970 raw17970Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw17970 raw17970Labels = mixedMoment B raw17970step0 raw17970step0Labels := by
      have hz : ∀ j, raw17970 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17970step0 = (fun i j => raw17970 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17970step0 raw17970; decide +kernel
      have hl : raw17970step0Labels = raw17970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17970 raw17970Labels permutation434 hz
    mixedMoment B raw17970step0 raw17970step0Labels = mixedMoment B raw17970step1 raw17970step1Labels := by
      have ha : raw17970step1 = (fun i j => raw17970step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17970step1 raw17970step0; decide +kernel
      have hl : raw17970step1Labels = raw17970step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17970step0 raw17970step0Labels permutation151 permutation3
    mixedMoment B raw17970step1 raw17970step1Labels = mixedMoment B raw17970step2 raw17970step2Labels := by
      have ha : raw17970step2 = -raw17970step1 := by apply Matrix.ext; change ∀ i j, raw17970step2 i j = -(raw17970step1 i j); unfold raw17970step2 raw17970step1; decide +kernel
      have hl : raw17970step2Labels = raw17970step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17970step2 raw17970step2Labels = mixedMoment B raw17970step3 raw17970step3Labels := by
      have ha : raw17970step3 = raw17970step2 := by apply Matrix.ext; unfold raw17970step3 raw17970step2; decide +kernel
      have hl : raw17970step2Labels = labelEmbedding6 ∘ raw17970step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17970step2 raw17970step2Labels raw17970step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

theorem canonical17971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17971 raw17971Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw17971 raw17971Labels = mixedMoment B raw17971step0 raw17971step0Labels := by
      have ha : raw17971step0 = (fun i j => raw17971 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17971step0 raw17971; decide +kernel
      have hl : raw17971step0Labels = raw17971Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17971 raw17971Labels permutation682 permutation3
    mixedMoment B raw17971step0 raw17971step0Labels = mixedMoment B raw17971step1 raw17971step1Labels := by
      have ha : raw17971step1 = -raw17971step0 := by apply Matrix.ext; change ∀ i j, raw17971step1 i j = -(raw17971step0 i j); unfold raw17971step1 raw17971step0; decide +kernel
      have hl : raw17971step1Labels = raw17971step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17971step1 raw17971step1Labels = mixedMoment B raw17971step2 raw17971step2Labels := by
      have ha : raw17971step2 = raw17971step1 := by apply Matrix.ext; unfold raw17971step2 raw17971step1; decide +kernel
      have hl : raw17971step1Labels = labelEmbedding6 ∘ raw17971step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17971step1 raw17971step1Labels raw17971step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

theorem canonical17972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17972 raw17972Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw17972 raw17972Labels = mixedMoment B raw17972step0 raw17972step0Labels := by
      have hz : ∀ j, raw17972 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17972step0 = (fun i j => raw17972 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17972step0 raw17972; decide +kernel
      have hl : raw17972step0Labels = raw17972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17972 raw17972Labels permutation434 hz
    mixedMoment B raw17972step0 raw17972step0Labels = mixedMoment B raw17972step1 raw17972step1Labels := by
      have ha : raw17972step1 = (fun i j => raw17972step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17972step1 raw17972step0; decide +kernel
      have hl : raw17972step1Labels = raw17972step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17972step0 raw17972step0Labels permutation33 permutation3
    mixedMoment B raw17972step1 raw17972step1Labels = mixedMoment B raw17972step2 raw17972step2Labels := by
      have ha : raw17972step2 = raw17972step1 := by apply Matrix.ext; unfold raw17972step2 raw17972step1; decide +kernel
      have hl : raw17972step1Labels = labelEmbedding6 ∘ raw17972step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17972step1 raw17972step1Labels raw17972step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical17973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17973 raw17973Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw17973 raw17973Labels = mixedMoment B raw17973step0 raw17973step0Labels := by
      have hz : ∀ j, raw17973 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17973step0 = (fun i j => raw17973 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17973step0 raw17973; decide +kernel
      have hl : raw17973step0Labels = raw17973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17973 raw17973Labels permutation434 hz
    mixedMoment B raw17973step0 raw17973step0Labels = mixedMoment B raw17973step1 raw17973step1Labels := by
      have ha : raw17973step1 = (fun i j => raw17973step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17973step1 raw17973step0; decide +kernel
      have hl : raw17973step1Labels = raw17973step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17973step0 raw17973step0Labels permutation151 permutation3
    mixedMoment B raw17973step1 raw17973step1Labels = mixedMoment B raw17973step2 raw17973step2Labels := by
      have ha : raw17973step2 = -raw17973step1 := by apply Matrix.ext; change ∀ i j, raw17973step2 i j = -(raw17973step1 i j); unfold raw17973step2 raw17973step1; decide +kernel
      have hl : raw17973step2Labels = raw17973step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17973step2 raw17973step2Labels = mixedMoment B raw17973step3 raw17973step3Labels := by
      have ha : raw17973step3 = raw17973step2 := by apply Matrix.ext; unfold raw17973step3 raw17973step2; decide +kernel
      have hl : raw17973step2Labels = labelEmbedding6 ∘ raw17973step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17973step2 raw17973step2Labels raw17973step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

theorem canonical17974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17974 raw17974Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw17974 raw17974Labels = mixedMoment B raw17974step0 raw17974step0Labels := by
      have hz : ∀ j, raw17974 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17974step0 = (fun i j => raw17974 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17974step0 raw17974; decide +kernel
      have hl : raw17974step0Labels = raw17974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17974 raw17974Labels permutation434 hz
    mixedMoment B raw17974step0 raw17974step0Labels = mixedMoment B raw17974step1 raw17974step1Labels := by
      have ha : raw17974step1 = (fun i j => raw17974step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17974step1 raw17974step0; decide +kernel
      have hl : raw17974step1Labels = raw17974step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17974step0 raw17974step0Labels permutation144 permutation5
    mixedMoment B raw17974step1 raw17974step1Labels = mixedMoment B raw17974step2 raw17974step2Labels := by
      have ha : raw17974step2 = raw17974step1 := by apply Matrix.ext; unfold raw17974step2 raw17974step1; decide +kernel
      have hl : raw17974step1Labels = labelEmbedding8 ∘ raw17974step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17974step1 raw17974step1Labels raw17974step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

theorem canonical17975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17975 raw17975Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw17975 raw17975Labels = mixedMoment B raw17975step0 raw17975step0Labels := by
      have hz : ∀ j, raw17975 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17975step0 = (fun i j => raw17975 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17975step0 raw17975; decide +kernel
      have hl : raw17975step0Labels = raw17975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17975 raw17975Labels permutation434 hz
    mixedMoment B raw17975step0 raw17975step0Labels = mixedMoment B raw17975step1 raw17975step1Labels := by
      have ha : raw17975step1 = (fun i j => raw17975step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17975step1 raw17975step0; decide +kernel
      have hl : raw17975step1Labels = raw17975step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17975step0 raw17975step0Labels permutation151 permutation3
    mixedMoment B raw17975step1 raw17975step1Labels = mixedMoment B raw17975step2 raw17975step2Labels := by
      have ha : raw17975step2 = -raw17975step1 := by apply Matrix.ext; change ∀ i j, raw17975step2 i j = -(raw17975step1 i j); unfold raw17975step2 raw17975step1; decide +kernel
      have hl : raw17975step2Labels = raw17975step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17975step2 raw17975step2Labels = mixedMoment B raw17975step3 raw17975step3Labels := by
      have ha : raw17975step3 = raw17975step2 := by apply Matrix.ext; unfold raw17975step3 raw17975step2; decide +kernel
      have hl : raw17975step2Labels = labelEmbedding6 ∘ raw17975step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17975step2 raw17975step2Labels raw17975step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical17976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17976 raw17976Labels = mixedMoment B node4787 node4787Labels := by
  calc
    mixedMoment B raw17976 raw17976Labels = mixedMoment B raw17976step0 raw17976step0Labels := by
      have ha : raw17976step0 = (fun i j => raw17976 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17976step0 raw17976; decide +kernel
      have hl : raw17976step0Labels = raw17976Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17976 raw17976Labels permutation682 permutation3
    mixedMoment B raw17976step0 raw17976step0Labels = mixedMoment B raw17976step1 raw17976step1Labels := by
      have ha : raw17976step1 = -raw17976step0 := by apply Matrix.ext; change ∀ i j, raw17976step1 i j = -(raw17976step0 i j); unfold raw17976step1 raw17976step0; decide +kernel
      have hl : raw17976step1Labels = raw17976step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17976step1 raw17976step1Labels = mixedMoment B raw17976step2 raw17976step2Labels := by
      have ha : raw17976step2 = raw17976step1 := by apply Matrix.ext; unfold raw17976step2 raw17976step1; decide +kernel
      have hl : raw17976step1Labels = labelEmbedding6 ∘ raw17976step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17976step1 raw17976step1Labels raw17976step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4787 node4787Labels := by rfl

theorem canonical17977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17977 raw17977Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw17977 raw17977Labels = mixedMoment B raw17977step0 raw17977step0Labels := by
      have hz : ∀ j, raw17977 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17977step0 = (fun i j => raw17977 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17977step0 raw17977; decide +kernel
      have hl : raw17977step0Labels = raw17977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17977 raw17977Labels permutation434 hz
    mixedMoment B raw17977step0 raw17977step0Labels = mixedMoment B raw17977step1 raw17977step1Labels := by
      have ha : raw17977step1 = (fun i j => raw17977step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17977step1 raw17977step0; decide +kernel
      have hl : raw17977step1Labels = raw17977step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17977step0 raw17977step0Labels permutation144 permutation5
    mixedMoment B raw17977step1 raw17977step1Labels = mixedMoment B raw17977step2 raw17977step2Labels := by
      have ha : raw17977step2 = raw17977step1 := by apply Matrix.ext; unfold raw17977step2 raw17977step1; decide +kernel
      have hl : raw17977step1Labels = labelEmbedding8 ∘ raw17977step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17977step1 raw17977step1Labels raw17977step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical142
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18182 raw18182Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw18182 raw18182Labels = mixedMoment B raw18182step0 raw18182step0Labels := by
      have hz : ∀ j, raw18182 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18182step0 = (fun i j => raw18182 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18182step0 raw18182; decide +kernel
      have hl : raw18182step0Labels = raw18182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18182 raw18182Labels permutation346 hz
    mixedMoment B raw18182step0 raw18182step0Labels = mixedMoment B raw18182step1 raw18182step1Labels := by
      have ha : raw18182step1 = (fun i j => raw18182step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18182step1 raw18182step0; decide +kernel
      have hl : raw18182step1Labels = raw18182step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18182step0 raw18182step0Labels permutation56 permutation2
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical18183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18183 raw18183Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw18183 raw18183Labels = mixedMoment B raw18183step0 raw18183step0Labels := by
      have ha : raw18183step0 = (fun i j => raw18183 (permutation685 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18183step0 raw18183; decide +kernel
      have hl : raw18183step0Labels = raw18183Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18183 raw18183Labels permutation685 permutation3
    mixedMoment B raw18183step0 raw18183step0Labels = mixedMoment B raw18183step1 raw18183step1Labels := by
      have ha : raw18183step1 = -raw18183step0 := by apply Matrix.ext; change ∀ i j, raw18183step1 i j = -(raw18183step0 i j); unfold raw18183step1 raw18183step0; decide +kernel
      have hl : raw18183step1Labels = raw18183step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18183step1 raw18183step1Labels = mixedMoment B raw18183step2 raw18183step2Labels := by
      have ha : raw18183step2 = raw18183step1 := by apply Matrix.ext; unfold raw18183step2 raw18183step1; decide +kernel
      have hl : raw18183step1Labels = labelEmbedding6 ∘ raw18183step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18183step1 raw18183step1Labels raw18183step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical18184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18184 raw18184Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw18184 raw18184Labels = mixedMoment B raw18184step0 raw18184step0Labels := by
      have hz : ∀ j, raw18184 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18184step0 = (fun i j => raw18184 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18184step0 raw18184; decide +kernel
      have hl : raw18184step0Labels = raw18184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18184 raw18184Labels permutation346 hz
    mixedMoment B raw18184step0 raw18184step0Labels = mixedMoment B raw18184step1 raw18184step1Labels := by
      have ha : raw18184step1 = (fun i j => raw18184step0 (permutation148 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18184step1 raw18184step0; decide +kernel
      have hl : raw18184step1Labels = raw18184step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18184step0 raw18184step0Labels permutation148 permutation3
    mixedMoment B raw18184step1 raw18184step1Labels = mixedMoment B raw18184step2 raw18184step2Labels := by
      have ha : raw18184step2 = -raw18184step1 := by apply Matrix.ext; change ∀ i j, raw18184step2 i j = -(raw18184step1 i j); unfold raw18184step2 raw18184step1; decide +kernel
      have hl : raw18184step2Labels = raw18184step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18184step2 raw18184step2Labels = mixedMoment B raw18184step3 raw18184step3Labels := by
      have ha : raw18184step3 = raw18184step2 := by apply Matrix.ext; unfold raw18184step3 raw18184step2; decide +kernel
      have hl : raw18184step2Labels = labelEmbedding6 ∘ raw18184step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18184step2 raw18184step2Labels raw18184step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical18185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18185 raw18185Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18185 raw18185Labels = mixedMoment B raw18185step0 raw18185step0Labels := by
      have hz : ∀ j, raw18185 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18185step0 = (fun i j => raw18185 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18185step0 raw18185; decide +kernel
      have hl : raw18185step0Labels = raw18185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18185 raw18185Labels permutation346 hz
    mixedMoment B raw18185step0 raw18185step0Labels = mixedMoment B raw18185step1 raw18185step1Labels := by
      have ha : raw18185step1 = (fun i j => raw18185step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18185step1 raw18185step0; decide +kernel
      have hl : raw18185step1Labels = raw18185step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18185step0 raw18185step0Labels permutation137 permutation5
    mixedMoment B raw18185step1 raw18185step1Labels = mixedMoment B raw18185step2 raw18185step2Labels := by
      have ha : raw18185step2 = raw18185step1 := by apply Matrix.ext; unfold raw18185step2 raw18185step1; decide +kernel
      have hl : raw18185step1Labels = labelEmbedding8 ∘ raw18185step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18185step1 raw18185step1Labels raw18185step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical18186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18186 raw18186Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw18186 raw18186Labels = mixedMoment B raw18186step0 raw18186step0Labels := by
      have hz : ∀ j, raw18186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18186step0 = (fun i j => raw18186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18186step0 raw18186; decide +kernel
      have hl : raw18186step0Labels = raw18186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18186 raw18186Labels permutation346 hz
    mixedMoment B raw18186step0 raw18186step0Labels = mixedMoment B raw18186step1 raw18186step1Labels := by
      have ha : raw18186step1 = (fun i j => raw18186step0 (permutation75 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18186step1 raw18186step0; decide +kernel
      have hl : raw18186step1Labels = raw18186step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18186step0 raw18186step0Labels permutation75 permutation6
    mixedMoment B raw18186step1 raw18186step1Labels = mixedMoment B raw18186step2 raw18186step2Labels := by
      have ha : raw18186step2 = -raw18186step1 := by apply Matrix.ext; change ∀ i j, raw18186step2 i j = -(raw18186step1 i j); unfold raw18186step2 raw18186step1; decide +kernel
      have hl : raw18186step2Labels = raw18186step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18186step2 raw18186step2Labels = mixedMoment B raw18186step3 raw18186step3Labels := by
      have ha : raw18186step3 = raw18186step2 := by apply Matrix.ext; unfold raw18186step3 raw18186step2; decide +kernel
      have hl : raw18186step2Labels = labelEmbedding9 ∘ raw18186step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18186step2 raw18186step2Labels raw18186step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical18187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18187 raw18187Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw18187 raw18187Labels = mixedMoment B raw18187step0 raw18187step0Labels := by
      have hz : ∀ j, raw18187 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18187step0 = (fun i j => raw18187 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18187step0 raw18187; decide +kernel
      have hl : raw18187step0Labels = raw18187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18187 raw18187Labels permutation346 hz
    mixedMoment B raw18187step0 raw18187step0Labels = mixedMoment B raw18187step1 raw18187step1Labels := by
      have ha : raw18187step1 = (fun i j => raw18187step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18187step1 raw18187step0; decide +kernel
      have hl : raw18187step1Labels = raw18187step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18187step0 raw18187step0Labels permutation40 permutation5
    mixedMoment B raw18187step1 raw18187step1Labels = mixedMoment B raw18187step2 raw18187step2Labels := by
      have ha : raw18187step2 = -raw18187step1 := by apply Matrix.ext; change ∀ i j, raw18187step2 i j = -(raw18187step1 i j); unfold raw18187step2 raw18187step1; decide +kernel
      have hl : raw18187step2Labels = raw18187step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18187step2 raw18187step2Labels = mixedMoment B raw18187step3 raw18187step3Labels := by
      have ha : raw18187step3 = raw18187step2 := by apply Matrix.ext; unfold raw18187step3 raw18187step2; decide +kernel
      have hl : raw18187step2Labels = labelEmbedding8 ∘ raw18187step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18187step2 raw18187step2Labels raw18187step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

theorem canonical18188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18188 raw18188Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw18188 raw18188Labels = mixedMoment B raw18188step0 raw18188step0Labels := by
      have ha : raw18188step0 = (fun i j => raw18188 (permutation622 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18188step0 raw18188; decide +kernel
      have hl : raw18188step0Labels = raw18188Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18188 raw18188Labels permutation622 permutation5
    mixedMoment B raw18188step0 raw18188step0Labels = mixedMoment B raw18188step1 raw18188step1Labels := by
      have ha : raw18188step1 = raw18188step0 := by apply Matrix.ext; unfold raw18188step1 raw18188step0; decide +kernel
      have hl : raw18188step0Labels = labelEmbedding8 ∘ raw18188step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18188step0 raw18188step0Labels raw18188step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical18189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18189 raw18189Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw18189 raw18189Labels = mixedMoment B raw18189step0 raw18189step0Labels := by
      have hz : ∀ j, raw18189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18189step0 = (fun i j => raw18189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18189step0 raw18189; decide +kernel
      have hl : raw18189step0Labels = raw18189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18189 raw18189Labels permutation346 hz
    mixedMoment B raw18189step0 raw18189step0Labels = mixedMoment B raw18189step1 raw18189step1Labels := by
      have ha : raw18189step1 = (fun i j => raw18189step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18189step1 raw18189step0; decide +kernel
      have hl : raw18189step1Labels = raw18189step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18189step0 raw18189step0Labels permutation40 permutation5
    mixedMoment B raw18189step1 raw18189step1Labels = mixedMoment B raw18189step2 raw18189step2Labels := by
      have ha : raw18189step2 = -raw18189step1 := by apply Matrix.ext; change ∀ i j, raw18189step2 i j = -(raw18189step1 i j); unfold raw18189step2 raw18189step1; decide +kernel
      have hl : raw18189step2Labels = raw18189step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18189step2 raw18189step2Labels = mixedMoment B raw18189step3 raw18189step3Labels := by
      have ha : raw18189step3 = raw18189step2 := by apply Matrix.ext; unfold raw18189step3 raw18189step2; decide +kernel
      have hl : raw18189step2Labels = labelEmbedding8 ∘ raw18189step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18189step2 raw18189step2Labels raw18189step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical18190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18190 raw18190Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw18190 raw18190Labels = mixedMoment B raw18190step0 raw18190step0Labels := by
      have hz : ∀ j, raw18190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18190step0 = (fun i j => raw18190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18190step0 raw18190; decide +kernel
      have hl : raw18190step0Labels = raw18190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18190 raw18190Labels permutation346 hz
    mixedMoment B raw18190step0 raw18190step0Labels = mixedMoment B raw18190step1 raw18190step1Labels := by
      have ha : raw18190step1 = (fun i j => raw18190step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18190step1 raw18190step0; decide +kernel
      have hl : raw18190step1Labels = raw18190step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18190step0 raw18190step0Labels permutation137 permutation5
    mixedMoment B raw18190step1 raw18190step1Labels = mixedMoment B raw18190step2 raw18190step2Labels := by
      have ha : raw18190step2 = raw18190step1 := by apply Matrix.ext; unfold raw18190step2 raw18190step1; decide +kernel
      have hl : raw18190step1Labels = labelEmbedding8 ∘ raw18190step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18190step1 raw18190step1Labels raw18190step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5387 node5387Labels := by rfl

theorem canonical18191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18191 raw18191Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw18191 raw18191Labels = mixedMoment B raw18191step0 raw18191step0Labels := by
      have hz : ∀ j, raw18191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18191step0 = (fun i j => raw18191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18191step0 raw18191; decide +kernel
      have hl : raw18191step0Labels = raw18191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18191 raw18191Labels permutation346 hz
    mixedMoment B raw18191step0 raw18191step0Labels = mixedMoment B raw18191step1 raw18191step1Labels := by
      have ha : raw18191step1 = (fun i j => raw18191step0 (permutation79 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18191step1 raw18191step0; decide +kernel
      have hl : raw18191step1Labels = raw18191step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18191step0 raw18191step0Labels permutation79 permutation4
    mixedMoment B raw18191step1 raw18191step1Labels = mixedMoment B raw18191step2 raw18191step2Labels := by
      have ha : raw18191step2 = raw18191step1 := by apply Matrix.ext; unfold raw18191step2 raw18191step1; decide +kernel
      have hl : raw18191step1Labels = labelEmbedding7 ∘ raw18191step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18191step1 raw18191step1Labels raw18191step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical18192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18192 raw18192Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw18192 raw18192Labels = mixedMoment B raw18192step0 raw18192step0Labels := by
      have ha : raw18192step0 = (fun i j => raw18192 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18192step0 raw18192; decide +kernel
      have hl : raw18192step0Labels = raw18192Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18192 raw18192Labels permutation212 permutation5
    mixedMoment B raw18192step0 raw18192step0Labels = mixedMoment B raw18192step1 raw18192step1Labels := by
      have ha : raw18192step1 = -raw18192step0 := by apply Matrix.ext; change ∀ i j, raw18192step1 i j = -(raw18192step0 i j); unfold raw18192step1 raw18192step0; decide +kernel
      have hl : raw18192step1Labels = raw18192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18192step1 raw18192step1Labels = mixedMoment B raw18192step2 raw18192step2Labels := by
      have ha : raw18192step2 = raw18192step1 := by apply Matrix.ext; unfold raw18192step2 raw18192step1; decide +kernel
      have hl : raw18192step1Labels = labelEmbedding8 ∘ raw18192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18192step1 raw18192step1Labels raw18192step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical18193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18193 raw18193Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw18193 raw18193Labels = mixedMoment B raw18193step0 raw18193step0Labels := by
      have ha : raw18193step0 = (fun i j => raw18193 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18193step0 raw18193; decide +kernel
      have hl : raw18193step0Labels = raw18193Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18193 raw18193Labels permutation160 permutation3
    mixedMoment B raw18193step0 raw18193step0Labels = mixedMoment B raw18193step1 raw18193step1Labels := by
      have ha : raw18193step1 = raw18193step0 := by apply Matrix.ext; unfold raw18193step1 raw18193step0; decide +kernel
      have hl : raw18193step0Labels = labelEmbedding6 ∘ raw18193step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18193step0 raw18193step0Labels raw18193step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical18194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18194 raw18194Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw18194 raw18194Labels = mixedMoment B raw18194step0 raw18194step0Labels := by
      have ha : raw18194step0 = (fun i j => raw18194 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18194step0 raw18194; decide +kernel
      have hl : raw18194step0Labels = raw18194Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18194 raw18194Labels permutation212 permutation5
    mixedMoment B raw18194step0 raw18194step0Labels = mixedMoment B raw18194step1 raw18194step1Labels := by
      have ha : raw18194step1 = -raw18194step0 := by apply Matrix.ext; change ∀ i j, raw18194step1 i j = -(raw18194step0 i j); unfold raw18194step1 raw18194step0; decide +kernel
      have hl : raw18194step1Labels = raw18194step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18194step1 raw18194step1Labels = mixedMoment B raw18194step2 raw18194step2Labels := by
      have ha : raw18194step2 = raw18194step1 := by apply Matrix.ext; unfold raw18194step2 raw18194step1; decide +kernel
      have hl : raw18194step1Labels = labelEmbedding8 ∘ raw18194step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18194step1 raw18194step1Labels raw18194step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

theorem canonical18195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18195 raw18195Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw18195 raw18195Labels = mixedMoment B raw18195step0 raw18195step0Labels := by
      have ha : raw18195step0 = (fun i j => raw18195 (permutation632 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18195step0 raw18195; decide +kernel
      have hl : raw18195step0Labels = raw18195Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18195 raw18195Labels permutation632 permutation5
    mixedMoment B raw18195step0 raw18195step0Labels = mixedMoment B raw18195step1 raw18195step1Labels := by
      have ha : raw18195step1 = raw18195step0 := by apply Matrix.ext; unfold raw18195step1 raw18195step0; decide +kernel
      have hl : raw18195step0Labels = labelEmbedding8 ∘ raw18195step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18195step0 raw18195step0Labels raw18195step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5400 node5400Labels := by rfl

theorem canonical18196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18196 raw18196Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw18196 raw18196Labels = mixedMoment B raw18196step0 raw18196step0Labels := by
      have ha : raw18196step0 = (fun i j => raw18196 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18196step0 raw18196; decide +kernel
      have hl : raw18196step0Labels = raw18196Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18196 raw18196Labels permutation212 permutation5
    mixedMoment B raw18196step0 raw18196step0Labels = mixedMoment B raw18196step1 raw18196step1Labels := by
      have ha : raw18196step1 = -raw18196step0 := by apply Matrix.ext; change ∀ i j, raw18196step1 i j = -(raw18196step0 i j); unfold raw18196step1 raw18196step0; decide +kernel
      have hl : raw18196step1Labels = raw18196step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18196step1 raw18196step1Labels = mixedMoment B raw18196step2 raw18196step2Labels := by
      have ha : raw18196step2 = raw18196step1 := by apply Matrix.ext; unfold raw18196step2 raw18196step1; decide +kernel
      have hl : raw18196step1Labels = labelEmbedding8 ∘ raw18196step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18196step1 raw18196step1Labels raw18196step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical18197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18197 raw18197Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw18197 raw18197Labels = mixedMoment B raw18197step0 raw18197step0Labels := by
      have hz : ∀ j, raw18197 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18197step0 = (fun i j => raw18197 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18197step0 raw18197; decide +kernel
      have hl : raw18197step0Labels = raw18197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18197 raw18197Labels permutation346 hz
    mixedMoment B raw18197step0 raw18197step0Labels = mixedMoment B raw18197step1 raw18197step1Labels := by
      have ha : raw18197step1 = (fun i j => raw18197step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18197step1 raw18197step0; decide +kernel
      have hl : raw18197step1Labels = raw18197step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18197step0 raw18197step0Labels permutation32 permutation3
    mixedMoment B raw18197step1 raw18197step1Labels = mixedMoment B raw18197step2 raw18197step2Labels := by
      have ha : raw18197step2 = raw18197step1 := by apply Matrix.ext; unfold raw18197step2 raw18197step1; decide +kernel
      have hl : raw18197step1Labels = labelEmbedding6 ∘ raw18197step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18197step1 raw18197step1Labels raw18197step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

theorem canonical18198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18198 raw18198Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw18198 raw18198Labels = mixedMoment B raw18198step0 raw18198step0Labels := by
      have hz : ∀ j, raw18198 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18198step0 = (fun i j => raw18198 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18198step0 raw18198; decide +kernel
      have hl : raw18198step0Labels = raw18198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18198 raw18198Labels permutation346 hz
    mixedMoment B raw18198step0 raw18198step0Labels = mixedMoment B raw18198step1 raw18198step1Labels := by
      have ha : raw18198step1 = (fun i j => raw18198step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18198step1 raw18198step0; decide +kernel
      have hl : raw18198step1Labels = raw18198step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18198step0 raw18198step0Labels permutation32 permutation3
    mixedMoment B raw18198step1 raw18198step1Labels = mixedMoment B raw18198step2 raw18198step2Labels := by
      have ha : raw18198step2 = raw18198step1 := by apply Matrix.ext; unfold raw18198step2 raw18198step1; decide +kernel
      have hl : raw18198step1Labels = labelEmbedding6 ∘ raw18198step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18198step1 raw18198step1Labels raw18198step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5387 node5387Labels := by rfl

theorem canonical18199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18199 raw18199Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw18199 raw18199Labels = mixedMoment B raw18199step0 raw18199step0Labels := by
      have ha : raw18199step0 = (fun i j => raw18199 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18199step0 raw18199; decide +kernel
      have hl : raw18199step0Labels = raw18199Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18199 raw18199Labels permutation176 permutation3
    mixedMoment B raw18199step0 raw18199step0Labels = mixedMoment B raw18199step1 raw18199step1Labels := by
      have ha : raw18199step1 = raw18199step0 := by apply Matrix.ext; unfold raw18199step1 raw18199step0; decide +kernel
      have hl : raw18199step0Labels = labelEmbedding6 ∘ raw18199step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18199step0 raw18199step0Labels raw18199step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5400 node5400Labels := by rfl

theorem canonical18200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18200 raw18200Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw18200 raw18200Labels = mixedMoment B raw18200step0 raw18200step0Labels := by
      have hz : ∀ j, raw18200 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18200step0 = (fun i j => raw18200 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18200step0 raw18200; decide +kernel
      have hl : raw18200step0Labels = raw18200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18200 raw18200Labels permutation346 hz
    mixedMoment B raw18200step0 raw18200step0Labels = mixedMoment B raw18200step1 raw18200step1Labels := by
      have ha : raw18200step1 = (fun i j => raw18200step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18200step1 raw18200step0; decide +kernel
      have hl : raw18200step1Labels = raw18200step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18200step0 raw18200step0Labels permutation145 permutation3
    mixedMoment B raw18200step1 raw18200step1Labels = mixedMoment B raw18200step2 raw18200step2Labels := by
      have ha : raw18200step2 = -raw18200step1 := by apply Matrix.ext; change ∀ i j, raw18200step2 i j = -(raw18200step1 i j); unfold raw18200step2 raw18200step1; decide +kernel
      have hl : raw18200step2Labels = raw18200step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18200step2 raw18200step2Labels = mixedMoment B raw18200step3 raw18200step3Labels := by
      have ha : raw18200step3 = raw18200step2 := by apply Matrix.ext; unfold raw18200step3 raw18200step2; decide +kernel
      have hl : raw18200step2Labels = labelEmbedding6 ∘ raw18200step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18200step2 raw18200step2Labels raw18200step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

theorem canonical18201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18201 raw18201Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18201 raw18201Labels = mixedMoment B raw18201step0 raw18201step0Labels := by
      have hz : ∀ j, raw18201 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18201step0 = (fun i j => raw18201 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18201step0 raw18201; decide +kernel
      have hl : raw18201step0Labels = raw18201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18201 raw18201Labels permutation346 hz
    mixedMoment B raw18201step0 raw18201step0Labels = mixedMoment B raw18201step1 raw18201step1Labels := by
      have ha : raw18201step1 = (fun i j => raw18201step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18201step1 raw18201step0; decide +kernel
      have hl : raw18201step1Labels = raw18201step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18201step0 raw18201step0Labels permutation32 permutation3
    mixedMoment B raw18201step1 raw18201step1Labels = mixedMoment B raw18201step2 raw18201step2Labels := by
      have ha : raw18201step2 = raw18201step1 := by apply Matrix.ext; unfold raw18201step2 raw18201step1; decide +kernel
      have hl : raw18201step1Labels = labelEmbedding6 ∘ raw18201step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18201step1 raw18201step1Labels raw18201step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical18202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18202 raw18202Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw18202 raw18202Labels = mixedMoment B raw18202step0 raw18202step0Labels := by
      have hz : ∀ j, raw18202 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18202step0 = (fun i j => raw18202 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18202step0 raw18202; decide +kernel
      have hl : raw18202step0Labels = raw18202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18202 raw18202Labels permutation346 hz
    mixedMoment B raw18202step0 raw18202step0Labels = mixedMoment B raw18202step1 raw18202step1Labels := by
      have ha : raw18202step1 = (fun i j => raw18202step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18202step1 raw18202step0; decide +kernel
      have hl : raw18202step1Labels = raw18202step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18202step0 raw18202step0Labels permutation38 permutation5
    mixedMoment B raw18202step1 raw18202step1Labels = mixedMoment B raw18202step2 raw18202step2Labels := by
      have ha : raw18202step2 = -raw18202step1 := by apply Matrix.ext; change ∀ i j, raw18202step2 i j = -(raw18202step1 i j); unfold raw18202step2 raw18202step1; decide +kernel
      have hl : raw18202step2Labels = raw18202step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18202step2 raw18202step2Labels = mixedMoment B raw18202step3 raw18202step3Labels := by
      have ha : raw18202step3 = raw18202step2 := by apply Matrix.ext; unfold raw18202step3 raw18202step2; decide +kernel
      have hl : raw18202step2Labels = labelEmbedding8 ∘ raw18202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18202step2 raw18202step2Labels raw18202step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

theorem canonical18203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18203 raw18203Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw18203 raw18203Labels = mixedMoment B raw18203step0 raw18203step0Labels := by
      have hz : ∀ j, raw18203 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18203step0 = (fun i j => raw18203 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18203step0 raw18203; decide +kernel
      have hl : raw18203step0Labels = raw18203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18203 raw18203Labels permutation346 hz
    mixedMoment B raw18203step0 raw18203step0Labels = mixedMoment B raw18203step1 raw18203step1Labels := by
      have ha : raw18203step1 = (fun i j => raw18203step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18203step1 raw18203step0; decide +kernel
      have hl : raw18203step1Labels = raw18203step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18203step0 raw18203step0Labels permutation151 permutation3
    mixedMoment B raw18203step1 raw18203step1Labels = mixedMoment B raw18203step2 raw18203step2Labels := by
      have ha : raw18203step2 = -raw18203step1 := by apply Matrix.ext; change ∀ i j, raw18203step2 i j = -(raw18203step1 i j); unfold raw18203step2 raw18203step1; decide +kernel
      have hl : raw18203step2Labels = raw18203step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18203step2 raw18203step2Labels = mixedMoment B raw18203step3 raw18203step3Labels := by
      have ha : raw18203step3 = raw18203step2 := by apply Matrix.ext; unfold raw18203step3 raw18203step2; decide +kernel
      have hl : raw18203step2Labels = labelEmbedding6 ∘ raw18203step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18203step2 raw18203step2Labels raw18203step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical18204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18204 raw18204Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw18204 raw18204Labels = mixedMoment B raw18204step0 raw18204step0Labels := by
      have ha : raw18204step0 = (fun i j => raw18204 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18204step0 raw18204; decide +kernel
      have hl : raw18204step0Labels = raw18204Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18204 raw18204Labels permutation686 permutation3
    mixedMoment B raw18204step0 raw18204step0Labels = mixedMoment B raw18204step1 raw18204step1Labels := by
      have ha : raw18204step1 = -raw18204step0 := by apply Matrix.ext; change ∀ i j, raw18204step1 i j = -(raw18204step0 i j); unfold raw18204step1 raw18204step0; decide +kernel
      have hl : raw18204step1Labels = raw18204step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18204step1 raw18204step1Labels = mixedMoment B raw18204step2 raw18204step2Labels := by
      have ha : raw18204step2 = raw18204step1 := by apply Matrix.ext; unfold raw18204step2 raw18204step1; decide +kernel
      have hl : raw18204step1Labels = labelEmbedding6 ∘ raw18204step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18204step1 raw18204step1Labels raw18204step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

theorem canonical18205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18205 raw18205Labels = mixedMoment B node5364 node5364Labels := by
  calc
    mixedMoment B raw18205 raw18205Labels = mixedMoment B raw18205step0 raw18205step0Labels := by
      have hz : ∀ j, raw18205 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18205step0 = (fun i j => raw18205 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18205step0 raw18205; decide +kernel
      have hl : raw18205step0Labels = raw18205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18205 raw18205Labels permutation346 hz
    mixedMoment B raw18205step0 raw18205step0Labels = mixedMoment B raw18205step1 raw18205step1Labels := by
      have ha : raw18205step1 = (fun i j => raw18205step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18205step1 raw18205step0; decide +kernel
      have hl : raw18205step1Labels = raw18205step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18205step0 raw18205step0Labels permutation149 permutation3
    mixedMoment B raw18205step1 raw18205step1Labels = mixedMoment B raw18205step2 raw18205step2Labels := by
      have ha : raw18205step2 = -raw18205step1 := by apply Matrix.ext; change ∀ i j, raw18205step2 i j = -(raw18205step1 i j); unfold raw18205step2 raw18205step1; decide +kernel
      have hl : raw18205step2Labels = raw18205step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18205step2 raw18205step2Labels = mixedMoment B raw18205step3 raw18205step3Labels := by
      have ha : raw18205step3 = raw18205step2 := by apply Matrix.ext; unfold raw18205step3 raw18205step2; decide +kernel
      have hl : raw18205step2Labels = labelEmbedding6 ∘ raw18205step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18205step2 raw18205step2Labels raw18205step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5364 node5364Labels := by rfl

theorem canonical18206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18206 raw18206Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw18206 raw18206Labels = mixedMoment B raw18206step0 raw18206step0Labels := by
      have hz : ∀ j, raw18206 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18206step0 = (fun i j => raw18206 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18206step0 raw18206; decide +kernel
      have hl : raw18206step0Labels = raw18206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18206 raw18206Labels permutation346 hz
    mixedMoment B raw18206step0 raw18206step0Labels = mixedMoment B raw18206step1 raw18206step1Labels := by
      have ha : raw18206step1 = (fun i j => raw18206step0 (permutation39 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18206step1 raw18206step0; decide +kernel
      have hl : raw18206step1Labels = raw18206step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18206step0 raw18206step0Labels permutation39 permutation5
    mixedMoment B raw18206step1 raw18206step1Labels = mixedMoment B raw18206step2 raw18206step2Labels := by
      have ha : raw18206step2 = -raw18206step1 := by apply Matrix.ext; change ∀ i j, raw18206step2 i j = -(raw18206step1 i j); unfold raw18206step2 raw18206step1; decide +kernel
      have hl : raw18206step2Labels = raw18206step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18206step2 raw18206step2Labels = mixedMoment B raw18206step3 raw18206step3Labels := by
      have ha : raw18206step3 = raw18206step2 := by apply Matrix.ext; unfold raw18206step3 raw18206step2; decide +kernel
      have hl : raw18206step2Labels = labelEmbedding8 ∘ raw18206step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18206step2 raw18206step2Labels raw18206step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical18207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18207 raw18207Labels = mixedMoment B node4800 node4800Labels := by
  calc
    mixedMoment B raw18207 raw18207Labels = mixedMoment B raw18207step0 raw18207step0Labels := by
      have hz : ∀ j, raw18207 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18207step0 = (fun i j => raw18207 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18207step0 raw18207; decide +kernel
      have hl : raw18207step0Labels = raw18207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18207 raw18207Labels permutation346 hz
    mixedMoment B raw18207step0 raw18207step0Labels = mixedMoment B raw18207step1 raw18207step1Labels := by
      have ha : raw18207step1 = (fun i j => raw18207step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18207step1 raw18207step0; decide +kernel
      have hl : raw18207step1Labels = raw18207step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18207step0 raw18207step0Labels permutation151 permutation3
    mixedMoment B raw18207step1 raw18207step1Labels = mixedMoment B raw18207step2 raw18207step2Labels := by
      have ha : raw18207step2 = -raw18207step1 := by apply Matrix.ext; change ∀ i j, raw18207step2 i j = -(raw18207step1 i j); unfold raw18207step2 raw18207step1; decide +kernel
      have hl : raw18207step2Labels = raw18207step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18207step2 raw18207step2Labels = mixedMoment B raw18207step3 raw18207step3Labels := by
      have ha : raw18207step3 = raw18207step2 := by apply Matrix.ext; unfold raw18207step3 raw18207step2; decide +kernel
      have hl : raw18207step2Labels = labelEmbedding6 ∘ raw18207step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18207step2 raw18207step2Labels raw18207step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4800 node4800Labels := by rfl

theorem canonical18208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18208 raw18208Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw18208 raw18208Labels = mixedMoment B raw18208step0 raw18208step0Labels := by
      have hz : ∀ j, raw18208 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18208step0 = (fun i j => raw18208 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18208step0 raw18208; decide +kernel
      have hl : raw18208step0Labels = raw18208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18208 raw18208Labels permutation346 hz
    mixedMoment B raw18208step0 raw18208step0Labels = mixedMoment B raw18208step1 raw18208step1Labels := by
      have ha : raw18208step1 = (fun i j => raw18208step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18208step1 raw18208step0; decide +kernel
      have hl : raw18208step1Labels = raw18208step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18208step0 raw18208step0Labels permutation151 permutation3
    mixedMoment B raw18208step1 raw18208step1Labels = mixedMoment B raw18208step2 raw18208step2Labels := by
      have ha : raw18208step2 = -raw18208step1 := by apply Matrix.ext; change ∀ i j, raw18208step2 i j = -(raw18208step1 i j); unfold raw18208step2 raw18208step1; decide +kernel
      have hl : raw18208step2Labels = raw18208step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18208step2 raw18208step2Labels = mixedMoment B raw18208step3 raw18208step3Labels := by
      have ha : raw18208step3 = raw18208step2 := by apply Matrix.ext; unfold raw18208step3 raw18208step2; decide +kernel
      have hl : raw18208step2Labels = labelEmbedding6 ∘ raw18208step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18208step2 raw18208step2Labels raw18208step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

theorem canonical18209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18209 raw18209Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw18209 raw18209Labels = mixedMoment B raw18209step0 raw18209step0Labels := by
      have ha : raw18209step0 = (fun i j => raw18209 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18209step0 raw18209; decide +kernel
      have hl : raw18209step0Labels = raw18209Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18209 raw18209Labels permutation686 permutation3
    mixedMoment B raw18209step0 raw18209step0Labels = mixedMoment B raw18209step1 raw18209step1Labels := by
      have ha : raw18209step1 = -raw18209step0 := by apply Matrix.ext; change ∀ i j, raw18209step1 i j = -(raw18209step0 i j); unfold raw18209step1 raw18209step0; decide +kernel
      have hl : raw18209step1Labels = raw18209step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18209step1 raw18209step1Labels = mixedMoment B raw18209step2 raw18209step2Labels := by
      have ha : raw18209step2 = raw18209step1 := by apply Matrix.ext; unfold raw18209step2 raw18209step1; decide +kernel
      have hl : raw18209step1Labels = labelEmbedding6 ∘ raw18209step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18209step1 raw18209step1Labels raw18209step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical18210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18210 raw18210Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw18210 raw18210Labels = mixedMoment B raw18210step0 raw18210step0Labels := by
      have hz : ∀ j, raw18210 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18210step0 = (fun i j => raw18210 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18210step0 raw18210; decide +kernel
      have hl : raw18210step0Labels = raw18210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18210 raw18210Labels permutation346 hz
    mixedMoment B raw18210step0 raw18210step0Labels = mixedMoment B raw18210step1 raw18210step1Labels := by
      have ha : raw18210step1 = (fun i j => raw18210step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18210step1 raw18210step0; decide +kernel
      have hl : raw18210step1Labels = raw18210step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18210step0 raw18210step0Labels permutation149 permutation3
    mixedMoment B raw18210step1 raw18210step1Labels = mixedMoment B raw18210step2 raw18210step2Labels := by
      have ha : raw18210step2 = -raw18210step1 := by apply Matrix.ext; change ∀ i j, raw18210step2 i j = -(raw18210step1 i j); unfold raw18210step2 raw18210step1; decide +kernel
      have hl : raw18210step2Labels = raw18210step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18210step2 raw18210step2Labels = mixedMoment B raw18210step3 raw18210step3Labels := by
      have ha : raw18210step3 = raw18210step2 := by apply Matrix.ext; unfold raw18210step3 raw18210step2; decide +kernel
      have hl : raw18210step2Labels = labelEmbedding6 ∘ raw18210step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18210step2 raw18210step2Labels raw18210step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

theorem canonical18211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18211 raw18211Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw18211 raw18211Labels = mixedMoment B raw18211step0 raw18211step0Labels := by
      have hz : ∀ j, raw18211 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18211step0 = (fun i j => raw18211 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18211step0 raw18211; decide +kernel
      have hl : raw18211step0Labels = raw18211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18211 raw18211Labels permutation346 hz
    mixedMoment B raw18211step0 raw18211step0Labels = mixedMoment B raw18211step1 raw18211step1Labels := by
      have ha : raw18211step1 = (fun i j => raw18211step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18211step1 raw18211step0; decide +kernel
      have hl : raw18211step1Labels = raw18211step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18211step0 raw18211step0Labels permutation137 permutation5
    mixedMoment B raw18211step1 raw18211step1Labels = mixedMoment B raw18211step2 raw18211step2Labels := by
      have ha : raw18211step2 = raw18211step1 := by apply Matrix.ext; unfold raw18211step2 raw18211step1; decide +kernel
      have hl : raw18211step1Labels = labelEmbedding8 ∘ raw18211step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18211step1 raw18211step1Labels raw18211step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2007 raw2007Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw2007 raw2007Labels = mixedMoment B raw2007step0 raw2007step0Labels := by
      have ha : raw2007step0 = (fun i j => raw2007 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2007step0 raw2007; decide +kernel
      have hl : raw2007step0Labels = raw2007Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2007 raw2007Labels permutation152 permutation4
    mixedMoment B raw2007step0 raw2007step0Labels = mixedMoment B raw2007step1 raw2007step1Labels := by
      have ha : raw2007step1 = raw2007step0 := by apply Matrix.ext; unfold raw2007step1 raw2007step0; decide +kernel
      have hl : raw2007step0Labels = labelEmbedding7 ∘ raw2007step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2007step0 raw2007step0Labels raw2007step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

theorem canonical2008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2008 raw2008Labels = mixedMoment B node2382 node2382Labels := by
  calc
    mixedMoment B raw2008 raw2008Labels = mixedMoment B raw2008step0 raw2008step0Labels := by
      have ha : raw2008step0 = (fun i j => raw2008 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2008step0 raw2008; decide +kernel
      have hl : raw2008step0Labels = raw2008Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2008 raw2008Labels permutation152 permutation4
    _ = mixedMoment B node2382 node2382Labels := by rfl

theorem canonical2009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2009 raw2009Labels = mixedMoment B node3340 node3340Labels := by
  calc
    mixedMoment B raw2009 raw2009Labels = mixedMoment B raw2009step0 raw2009step0Labels := by
      have ha : raw2009step0 = (fun i j => raw2009 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2009step0 raw2009; decide +kernel
      have hl : raw2009step0Labels = raw2009Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2009 raw2009Labels permutation158 permutation6
    mixedMoment B raw2009step0 raw2009step0Labels = mixedMoment B raw2009step1 raw2009step1Labels := by
      have ha : raw2009step1 = -raw2009step0 := by apply Matrix.ext; change ∀ i j, raw2009step1 i j = -(raw2009step0 i j); unfold raw2009step1 raw2009step0; decide +kernel
      have hl : raw2009step1Labels = raw2009step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2009step1 raw2009step1Labels = mixedMoment B raw2009step2 raw2009step2Labels := by
      have ha : raw2009step2 = raw2009step1 := by apply Matrix.ext; unfold raw2009step2 raw2009step1; decide +kernel
      have hl : raw2009step1Labels = labelEmbedding1 ∘ raw2009step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2009step1 raw2009step1Labels raw2009step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3340 node3340Labels := by rfl

theorem canonical2016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2016 raw2016Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw2016 raw2016Labels = mixedMoment B raw2016step0 raw2016step0Labels := by
      have ha : raw2016step0 = (fun i j => raw2016 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2016step0 raw2016; decide +kernel
      have hl : raw2016step0Labels = raw2016Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2016 raw2016Labels permutation32 permutation4
    mixedMoment B raw2016step0 raw2016step0Labels = mixedMoment B raw2016step1 raw2016step1Labels := by
      have ha : raw2016step1 = raw2016step0 := by apply Matrix.ext; unfold raw2016step1 raw2016step0; decide +kernel
      have hl : raw2016step0Labels = labelEmbedding7 ∘ raw2016step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2016step0 raw2016step0Labels raw2016step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

theorem canonical2017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2017 raw2017Labels = mixedMoment B node2388 node2388Labels := by
  calc
    mixedMoment B raw2017 raw2017Labels = mixedMoment B raw2017step0 raw2017step0Labels := by
      have ha : raw2017step0 = (fun i j => raw2017 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2017step0 raw2017; decide +kernel
      have hl : raw2017step0Labels = raw2017Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2017 raw2017Labels permutation32 permutation4
    _ = mixedMoment B node2388 node2388Labels := by rfl

theorem canonical2018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2018 raw2018Labels = mixedMoment B node3354 node3354Labels := by
  calc
    mixedMoment B raw2018 raw2018Labels = mixedMoment B raw2018step0 raw2018step0Labels := by
      have ha : raw2018step0 = (fun i j => raw2018 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2018step0 raw2018; decide +kernel
      have hl : raw2018step0Labels = raw2018Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2018 raw2018Labels permutation32 permutation6
    mixedMoment B raw2018step0 raw2018step0Labels = mixedMoment B raw2018step1 raw2018step1Labels := by
      have ha : raw2018step1 = -raw2018step0 := by apply Matrix.ext; change ∀ i j, raw2018step1 i j = -(raw2018step0 i j); unfold raw2018step1 raw2018step0; decide +kernel
      have hl : raw2018step1Labels = raw2018step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2018step1 raw2018step1Labels = mixedMoment B raw2018step2 raw2018step2Labels := by
      have ha : raw2018step2 = raw2018step1 := by apply Matrix.ext; unfold raw2018step2 raw2018step1; decide +kernel
      have hl : raw2018step1Labels = labelEmbedding1 ∘ raw2018step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2018step1 raw2018step1Labels raw2018step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3354 node3354Labels := by rfl

theorem canonical2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2025 raw2025Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw2025 raw2025Labels = mixedMoment B raw2025step0 raw2025step0Labels := by
      have ha : raw2025step0 = (fun i j => raw2025 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2025step0 raw2025; decide +kernel
      have hl : raw2025step0Labels = raw2025Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2025 raw2025Labels permutation32 permutation4
    mixedMoment B raw2025step0 raw2025step0Labels = mixedMoment B raw2025step1 raw2025step1Labels := by
      have ha : raw2025step1 = raw2025step0 := by apply Matrix.ext; unfold raw2025step1 raw2025step0; decide +kernel
      have hl : raw2025step0Labels = labelEmbedding7 ∘ raw2025step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2025step0 raw2025step0Labels raw2025step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

theorem canonical2026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2026 raw2026Labels = mixedMoment B node2400 node2400Labels := by
  calc
    mixedMoment B raw2026 raw2026Labels = mixedMoment B raw2026step0 raw2026step0Labels := by
      have ha : raw2026step0 = (fun i j => raw2026 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2026step0 raw2026; decide +kernel
      have hl : raw2026step0Labels = raw2026Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2026 raw2026Labels permutation32 permutation4
    _ = mixedMoment B node2400 node2400Labels := by rfl

theorem canonical2027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2027 raw2027Labels = mixedMoment B node3344 node3344Labels := by
  calc
    mixedMoment B raw2027 raw2027Labels = mixedMoment B raw2027step0 raw2027step0Labels := by
      have ha : raw2027step0 = (fun i j => raw2027 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2027step0 raw2027; decide +kernel
      have hl : raw2027step0Labels = raw2027Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2027 raw2027Labels permutation32 permutation6
    mixedMoment B raw2027step0 raw2027step0Labels = mixedMoment B raw2027step1 raw2027step1Labels := by
      have ha : raw2027step1 = -raw2027step0 := by apply Matrix.ext; change ∀ i j, raw2027step1 i j = -(raw2027step0 i j); unfold raw2027step1 raw2027step0; decide +kernel
      have hl : raw2027step1Labels = raw2027step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2027step1 raw2027step1Labels = mixedMoment B raw2027step2 raw2027step2Labels := by
      have ha : raw2027step2 = raw2027step1 := by apply Matrix.ext; unfold raw2027step2 raw2027step1; decide +kernel
      have hl : raw2027step1Labels = labelEmbedding1 ∘ raw2027step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2027step1 raw2027step1Labels raw2027step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3344 node3344Labels := by rfl

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

theorem canonical2271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2271 raw2271Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw2271 raw2271Labels = mixedMoment B raw2271step0 raw2271step0Labels := by
      have ha : raw2271step0 = (fun i j => raw2271 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2271step0 raw2271; decide +kernel
      have hl : raw2271step0Labels = raw2271Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2271 raw2271Labels permutation32 permutation4
    mixedMoment B raw2271step0 raw2271step0Labels = mixedMoment B raw2271step1 raw2271step1Labels := by
      have ha : raw2271step1 = raw2271step0 := by apply Matrix.ext; unfold raw2271step1 raw2271step0; decide +kernel
      have hl : raw2271step0Labels = labelEmbedding7 ∘ raw2271step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2271step0 raw2271step0Labels raw2271step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical2272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2272 raw2272Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw2272 raw2272Labels = mixedMoment B raw2272step0 raw2272step0Labels := by
      have ha : raw2272step0 = (fun i j => raw2272 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2272step0 raw2272; decide +kernel
      have hl : raw2272step0Labels = raw2272Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2272 raw2272Labels permutation32 permutation4
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical2273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2273 raw2273Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw2273 raw2273Labels = mixedMoment B raw2273step0 raw2273step0Labels := by
      have ha : raw2273step0 = (fun i j => raw2273 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2273step0 raw2273; decide +kernel
      have hl : raw2273step0Labels = raw2273Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2273 raw2273Labels permutation34 permutation6
    mixedMoment B raw2273step0 raw2273step0Labels = mixedMoment B raw2273step1 raw2273step1Labels := by
      have ha : raw2273step1 = -raw2273step0 := by apply Matrix.ext; change ∀ i j, raw2273step1 i j = -(raw2273step0 i j); unfold raw2273step1 raw2273step0; decide +kernel
      have hl : raw2273step1Labels = raw2273step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2273step1 raw2273step1Labels = mixedMoment B raw2273step2 raw2273step2Labels := by
      have ha : raw2273step2 = raw2273step1 := by apply Matrix.ext; unfold raw2273step2 raw2273step1; decide +kernel
      have hl : raw2273step1Labels = labelEmbedding1 ∘ raw2273step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2273step1 raw2273step1Labels raw2273step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

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

theorem canonical2385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2385 raw2385Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw2385 raw2385Labels = mixedMoment B raw2385step0 raw2385step0Labels := by
      have ha : raw2385step0 = (fun i j => raw2385 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2385step0 raw2385; decide +kernel
      have hl : raw2385step0Labels = raw2385Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2385 raw2385Labels permutation152 permutation4
    mixedMoment B raw2385step0 raw2385step0Labels = mixedMoment B raw2385step1 raw2385step1Labels := by
      have ha : raw2385step1 = raw2385step0 := by apply Matrix.ext; unfold raw2385step1 raw2385step0; decide +kernel
      have hl : raw2385step0Labels = labelEmbedding7 ∘ raw2385step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2385step0 raw2385step0Labels raw2385step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

theorem canonical2386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2386 raw2386Labels = mixedMoment B node3683 node3683Labels := by
  calc
    mixedMoment B raw2386 raw2386Labels = mixedMoment B raw2386step0 raw2386step0Labels := by
      have ha : raw2386step0 = (fun i j => raw2386 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2386step0 raw2386; decide +kernel
      have hl : raw2386step0Labels = raw2386Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2386 raw2386Labels permutation152 permutation4
    _ = mixedMoment B node3683 node3683Labels := by rfl

theorem canonical2387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2387 raw2387Labels = mixedMoment B node3746 node3746Labels := by
  calc
    mixedMoment B raw2387 raw2387Labels = mixedMoment B raw2387step0 raw2387step0Labels := by
      have ha : raw2387step0 = (fun i j => raw2387 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2387step0 raw2387; decide +kernel
      have hl : raw2387step0Labels = raw2387Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2387 raw2387Labels permutation153 permutation6
    mixedMoment B raw2387step0 raw2387step0Labels = mixedMoment B raw2387step1 raw2387step1Labels := by
      have ha : raw2387step1 = -raw2387step0 := by apply Matrix.ext; change ∀ i j, raw2387step1 i j = -(raw2387step0 i j); unfold raw2387step1 raw2387step0; decide +kernel
      have hl : raw2387step1Labels = raw2387step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2387step1 raw2387step1Labels = mixedMoment B raw2387step2 raw2387step2Labels := by
      have ha : raw2387step2 = raw2387step1 := by apply Matrix.ext; unfold raw2387step2 raw2387step1; decide +kernel
      have hl : raw2387step1Labels = labelEmbedding1 ∘ raw2387step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2387step1 raw2387step1Labels raw2387step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3746 node3746Labels := by rfl

theorem canonical2388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2388 raw2388Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw2388 raw2388Labels = mixedMoment B raw2388step0 raw2388step0Labels := by
      have ha : raw2388step0 = (fun i j => raw2388 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2388step0 raw2388; decide +kernel
      have hl : raw2388step0Labels = raw2388Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2388 raw2388Labels permutation152 permutation4
    mixedMoment B raw2388step0 raw2388step0Labels = mixedMoment B raw2388step1 raw2388step1Labels := by
      have ha : raw2388step1 = raw2388step0 := by apply Matrix.ext; unfold raw2388step1 raw2388step0; decide +kernel
      have hl : raw2388step0Labels = labelEmbedding7 ∘ raw2388step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2388step0 raw2388step0Labels raw2388step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

theorem canonical2389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2389 raw2389Labels = mixedMoment B node3687 node3687Labels := by
  calc
    mixedMoment B raw2389 raw2389Labels = mixedMoment B raw2389step0 raw2389step0Labels := by
      have ha : raw2389step0 = (fun i j => raw2389 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2389step0 raw2389; decide +kernel
      have hl : raw2389step0Labels = raw2389Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2389 raw2389Labels permutation152 permutation4
    _ = mixedMoment B node3687 node3687Labels := by rfl

theorem canonical2390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2390 raw2390Labels = mixedMoment B node3749 node3749Labels := by
  calc
    mixedMoment B raw2390 raw2390Labels = mixedMoment B raw2390step0 raw2390step0Labels := by
      have ha : raw2390step0 = (fun i j => raw2390 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2390step0 raw2390; decide +kernel
      have hl : raw2390step0Labels = raw2390Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2390 raw2390Labels permutation158 permutation6
    mixedMoment B raw2390step0 raw2390step0Labels = mixedMoment B raw2390step1 raw2390step1Labels := by
      have ha : raw2390step1 = -raw2390step0 := by apply Matrix.ext; change ∀ i j, raw2390step1 i j = -(raw2390step0 i j); unfold raw2390step1 raw2390step0; decide +kernel
      have hl : raw2390step1Labels = raw2390step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2390step1 raw2390step1Labels = mixedMoment B raw2390step2 raw2390step2Labels := by
      have ha : raw2390step2 = raw2390step1 := by apply Matrix.ext; unfold raw2390step2 raw2390step1; decide +kernel
      have hl : raw2390step1Labels = labelEmbedding1 ∘ raw2390step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2390step1 raw2390step1Labels raw2390step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3749 node3749Labels := by rfl

theorem canonical2400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2400 raw2400Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw2400 raw2400Labels = mixedMoment B raw2400step0 raw2400step0Labels := by
      have ha : raw2400step0 = (fun i j => raw2400 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2400step0 raw2400; decide +kernel
      have hl : raw2400step0Labels = raw2400Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2400 raw2400Labels permutation32 permutation4
    mixedMoment B raw2400step0 raw2400step0Labels = mixedMoment B raw2400step1 raw2400step1Labels := by
      have ha : raw2400step1 = raw2400step0 := by apply Matrix.ext; unfold raw2400step1 raw2400step0; decide +kernel
      have hl : raw2400step0Labels = labelEmbedding7 ∘ raw2400step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2400step0 raw2400step0Labels raw2400step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

theorem canonical2401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2401 raw2401Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw2401 raw2401Labels = mixedMoment B raw2401step0 raw2401step0Labels := by
      have ha : raw2401step0 = (fun i j => raw2401 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2401step0 raw2401; decide +kernel
      have hl : raw2401step0Labels = raw2401Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2401 raw2401Labels permutation32 permutation4
    _ = mixedMoment B node3693 node3693Labels := by rfl

theorem canonical2402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2402 raw2402Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw2402 raw2402Labels = mixedMoment B raw2402step0 raw2402step0Labels := by
      have ha : raw2402step0 = (fun i j => raw2402 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2402step0 raw2402; decide +kernel
      have hl : raw2402step0Labels = raw2402Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2402 raw2402Labels permutation34 permutation6
    mixedMoment B raw2402step0 raw2402step0Labels = mixedMoment B raw2402step1 raw2402step1Labels := by
      have ha : raw2402step1 = -raw2402step0 := by apply Matrix.ext; change ∀ i j, raw2402step1 i j = -(raw2402step0 i j); unfold raw2402step1 raw2402step0; decide +kernel
      have hl : raw2402step1Labels = raw2402step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2402step1 raw2402step1Labels = mixedMoment B raw2402step2 raw2402step2Labels := by
      have ha : raw2402step2 = raw2402step1 := by apply Matrix.ext; unfold raw2402step2 raw2402step1; decide +kernel
      have hl : raw2402step1Labels = labelEmbedding1 ∘ raw2402step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2402step1 raw2402step1Labels raw2402step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

theorem canonical2409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2409 raw2409Labels = mixedMoment B node5364 node5364Labels := by
  calc
    mixedMoment B raw2409 raw2409Labels = mixedMoment B raw2409step0 raw2409step0Labels := by
      have ha : raw2409step0 = (fun i j => raw2409 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2409step0 raw2409; decide +kernel
      have hl : raw2409step0Labels = raw2409Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2409 raw2409Labels permutation32 permutation4
    mixedMoment B raw2409step0 raw2409step0Labels = mixedMoment B raw2409step1 raw2409step1Labels := by
      have ha : raw2409step1 = raw2409step0 := by apply Matrix.ext; unfold raw2409step1 raw2409step0; decide +kernel
      have hl : raw2409step0Labels = labelEmbedding7 ∘ raw2409step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2409step0 raw2409step0Labels raw2409step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5364 node5364Labels := by rfl

theorem canonical2410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2410 raw2410Labels = mixedMoment B node3702 node3702Labels := by
  calc
    mixedMoment B raw2410 raw2410Labels = mixedMoment B raw2410step0 raw2410step0Labels := by
      have ha : raw2410step0 = (fun i j => raw2410 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2410step0 raw2410; decide +kernel
      have hl : raw2410step0Labels = raw2410Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2410 raw2410Labels permutation32 permutation4
    _ = mixedMoment B node3702 node3702Labels := by rfl

theorem canonical2411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2411 raw2411Labels = mixedMoment B node3702 node3702Labels := by
  calc
    mixedMoment B raw2411 raw2411Labels = mixedMoment B raw2411step0 raw2411step0Labels := by
      have ha : raw2411step0 = (fun i j => raw2411 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2411step0 raw2411; decide +kernel
      have hl : raw2411step0Labels = raw2411Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2411 raw2411Labels permutation151 permutation6
    mixedMoment B raw2411step0 raw2411step0Labels = mixedMoment B raw2411step1 raw2411step1Labels := by
      have ha : raw2411step1 = raw2411step0 := by apply Matrix.ext; unfold raw2411step1 raw2411step0; decide +kernel
      have hl : raw2411step0Labels = labelEmbedding1 ∘ raw2411step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2411step0 raw2411step0Labels raw2411step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3702 node3702Labels := by rfl

theorem canonical2415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2415 raw2415Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw2415 raw2415Labels = mixedMoment B raw2415step0 raw2415step0Labels := by
      have ha : raw2415step0 = (fun i j => raw2415 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2415step0 raw2415; decide +kernel
      have hl : raw2415step0Labels = raw2415Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2415 raw2415Labels permutation32 permutation4
    mixedMoment B raw2415step0 raw2415step0Labels = mixedMoment B raw2415step1 raw2415step1Labels := by
      have ha : raw2415step1 = raw2415step0 := by apply Matrix.ext; unfold raw2415step1 raw2415step0; decide +kernel
      have hl : raw2415step0Labels = labelEmbedding7 ∘ raw2415step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2415step0 raw2415step0Labels raw2415step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

theorem canonical2416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2416 raw2416Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw2416 raw2416Labels = mixedMoment B raw2416step0 raw2416step0Labels := by
      have ha : raw2416step0 = (fun i j => raw2416 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2416step0 raw2416; decide +kernel
      have hl : raw2416step0Labels = raw2416Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2416 raw2416Labels permutation32 permutation4
    _ = mixedMoment B node3705 node3705Labels := by rfl

theorem canonical2417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2417 raw2417Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw2417 raw2417Labels = mixedMoment B raw2417step0 raw2417step0Labels := by
      have ha : raw2417step0 = (fun i j => raw2417 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2417step0 raw2417; decide +kernel
      have hl : raw2417step0Labels = raw2417Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2417 raw2417Labels permutation33 permutation6
    mixedMoment B raw2417step0 raw2417step0Labels = mixedMoment B raw2417step1 raw2417step1Labels := by
      have ha : raw2417step1 = -raw2417step0 := by apply Matrix.ext; change ∀ i j, raw2417step1 i j = -(raw2417step0 i j); unfold raw2417step1 raw2417step0; decide +kernel
      have hl : raw2417step1Labels = raw2417step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2417step1 raw2417step1Labels = mixedMoment B raw2417step2 raw2417step2Labels := by
      have ha : raw2417step2 = raw2417step1 := by apply Matrix.ext; unfold raw2417step2 raw2417step1; decide +kernel
      have hl : raw2417step1Labels = labelEmbedding1 ∘ raw2417step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2417step1 raw2417step1Labels raw2417step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3767 node3767Labels := by rfl

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

theorem canonical2463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2463 raw2463Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw2463 raw2463Labels = mixedMoment B raw2463step0 raw2463step0Labels := by
      have ha : raw2463step0 = (fun i j => raw2463 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2463step0 raw2463; decide +kernel
      have hl : raw2463step0Labels = raw2463Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2463 raw2463Labels permutation152 permutation4
    mixedMoment B raw2463step0 raw2463step0Labels = mixedMoment B raw2463step1 raw2463step1Labels := by
      have ha : raw2463step1 = raw2463step0 := by apply Matrix.ext; unfold raw2463step1 raw2463step0; decide +kernel
      have hl : raw2463step0Labels = labelEmbedding7 ∘ raw2463step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2463step0 raw2463step0Labels raw2463step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

theorem canonical2464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2464 raw2464Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw2464 raw2464Labels = mixedMoment B raw2464step0 raw2464step0Labels := by
      have ha : raw2464step0 = (fun i j => raw2464 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2464step0 raw2464; decide +kernel
      have hl : raw2464step0Labels = raw2464Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2464 raw2464Labels permutation152 permutation4
    _ = mixedMoment B node3781 node3781Labels := by rfl

theorem canonical2465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2465 raw2465Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw2465 raw2465Labels = mixedMoment B raw2465step0 raw2465step0Labels := by
      have ha : raw2465step0 = (fun i j => raw2465 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2465step0 raw2465; decide +kernel
      have hl : raw2465step0Labels = raw2465Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2465 raw2465Labels permutation153 permutation6
    mixedMoment B raw2465step0 raw2465step0Labels = mixedMoment B raw2465step1 raw2465step1Labels := by
      have ha : raw2465step1 = -raw2465step0 := by apply Matrix.ext; change ∀ i j, raw2465step1 i j = -(raw2465step0 i j); unfold raw2465step1 raw2465step0; decide +kernel
      have hl : raw2465step1Labels = raw2465step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2465step1 raw2465step1Labels = mixedMoment B raw2465step2 raw2465step2Labels := by
      have ha : raw2465step2 = raw2465step1 := by apply Matrix.ext; unfold raw2465step2 raw2465step1; decide +kernel
      have hl : raw2465step1Labels = labelEmbedding1 ∘ raw2465step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2465step1 raw2465step1Labels raw2465step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3794 node3794Labels := by rfl

theorem canonical2472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2472 raw2472Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw2472 raw2472Labels = mixedMoment B raw2472step0 raw2472step0Labels := by
      have ha : raw2472step0 = (fun i j => raw2472 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2472step0 raw2472; decide +kernel
      have hl : raw2472step0Labels = raw2472Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2472 raw2472Labels permutation152 permutation4
    mixedMoment B raw2472step0 raw2472step0Labels = mixedMoment B raw2472step1 raw2472step1Labels := by
      have ha : raw2472step1 = raw2472step0 := by apply Matrix.ext; unfold raw2472step1 raw2472step0; decide +kernel
      have hl : raw2472step0Labels = labelEmbedding7 ∘ raw2472step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2472step0 raw2472step0Labels raw2472step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5400 node5400Labels := by rfl

theorem canonical2473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2473 raw2473Labels = mixedMoment B node3786 node3786Labels := by
  calc
    mixedMoment B raw2473 raw2473Labels = mixedMoment B raw2473step0 raw2473step0Labels := by
      have ha : raw2473step0 = (fun i j => raw2473 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2473step0 raw2473; decide +kernel
      have hl : raw2473step0Labels = raw2473Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2473 raw2473Labels permutation152 permutation4
    _ = mixedMoment B node3786 node3786Labels := by rfl

theorem canonical2474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2474 raw2474Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw2474 raw2474Labels = mixedMoment B raw2474step0 raw2474step0Labels := by
      have ha : raw2474step0 = (fun i j => raw2474 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2474step0 raw2474; decide +kernel
      have hl : raw2474step0Labels = raw2474Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2474 raw2474Labels permutation160 permutation6
    mixedMoment B raw2474step0 raw2474step0Labels = mixedMoment B raw2474step1 raw2474step1Labels := by
      have ha : raw2474step1 = -raw2474step0 := by apply Matrix.ext; change ∀ i j, raw2474step1 i j = -(raw2474step0 i j); unfold raw2474step1 raw2474step0; decide +kernel
      have hl : raw2474step1Labels = raw2474step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2474step1 raw2474step1Labels = mixedMoment B raw2474step2 raw2474step2Labels := by
      have ha : raw2474step2 = raw2474step1 := by apply Matrix.ext; unfold raw2474step2 raw2474step1; decide +kernel
      have hl : raw2474step1Labels = labelEmbedding1 ∘ raw2474step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2474step1 raw2474step1Labels raw2474step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3799 node3799Labels := by rfl

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

theorem canonical2523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2523 raw2523Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw2523 raw2523Labels = mixedMoment B raw2523step0 raw2523step0Labels := by
      have ha : raw2523step0 = (fun i j => raw2523 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2523step0 raw2523; decide +kernel
      have hl : raw2523step0Labels = raw2523Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2523 raw2523Labels permutation32 permutation4
    mixedMoment B raw2523step0 raw2523step0Labels = mixedMoment B raw2523step1 raw2523step1Labels := by
      have ha : raw2523step1 = raw2523step0 := by apply Matrix.ext; unfold raw2523step1 raw2523step0; decide +kernel
      have hl : raw2523step0Labels = labelEmbedding7 ∘ raw2523step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2523step0 raw2523step0Labels raw2523step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

theorem canonical2524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2524 raw2524Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw2524 raw2524Labels = mixedMoment B raw2524step0 raw2524step0Labels := by
      have ha : raw2524step0 = (fun i j => raw2524 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2524step0 raw2524; decide +kernel
      have hl : raw2524step0Labels = raw2524Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2524 raw2524Labels permutation32 permutation4
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical2525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2525 raw2525Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw2525 raw2525Labels = mixedMoment B raw2525step0 raw2525step0Labels := by
      have ha : raw2525step0 = (fun i j => raw2525 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2525step0 raw2525; decide +kernel
      have hl : raw2525step0Labels = raw2525Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2525 raw2525Labels permutation143 permutation6
    mixedMoment B raw2525step0 raw2525step0Labels = mixedMoment B raw2525step1 raw2525step1Labels := by
      have ha : raw2525step1 = raw2525step0 := by apply Matrix.ext; unfold raw2525step1 raw2525step0; decide +kernel
      have hl : raw2525step0Labels = labelEmbedding1 ∘ raw2525step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2525step0 raw2525step0Labels raw2525step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical2538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2538 raw2538Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw2538 raw2538Labels = mixedMoment B raw2538step0 raw2538step0Labels := by
      have ha : raw2538step0 = (fun i j => raw2538 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2538step0 raw2538; decide +kernel
      have hl : raw2538step0Labels = raw2538Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2538 raw2538Labels permutation32 permutation4
    mixedMoment B raw2538step0 raw2538step0Labels = mixedMoment B raw2538step1 raw2538step1Labels := by
      have ha : raw2538step1 = raw2538step0 := by apply Matrix.ext; unfold raw2538step1 raw2538step0; decide +kernel
      have hl : raw2538step0Labels = labelEmbedding7 ∘ raw2538step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2538step0 raw2538step0Labels raw2538step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical2539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2539 raw2539Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw2539 raw2539Labels = mixedMoment B raw2539step0 raw2539step0Labels := by
      have ha : raw2539step0 = (fun i j => raw2539 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2539step0 raw2539; decide +kernel
      have hl : raw2539step0Labels = raw2539Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2539 raw2539Labels permutation32 permutation4
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical2540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2540 raw2540Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw2540 raw2540Labels = mixedMoment B raw2540step0 raw2540step0Labels := by
      have ha : raw2540step0 = (fun i j => raw2540 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2540step0 raw2540; decide +kernel
      have hl : raw2540step0Labels = raw2540Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2540 raw2540Labels permutation38 permutation6
    mixedMoment B raw2540step0 raw2540step0Labels = mixedMoment B raw2540step1 raw2540step1Labels := by
      have ha : raw2540step1 = -raw2540step0 := by apply Matrix.ext; change ∀ i j, raw2540step1 i j = -(raw2540step0 i j); unfold raw2540step1 raw2540step0; decide +kernel
      have hl : raw2540step1Labels = raw2540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2540step1 raw2540step1Labels = mixedMoment B raw2540step2 raw2540step2Labels := by
      have ha : raw2540step2 = raw2540step1 := by apply Matrix.ext; unfold raw2540step2 raw2540step1; decide +kernel
      have hl : raw2540step1Labels = labelEmbedding1 ∘ raw2540step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2540step1 raw2540step1Labels raw2540step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4787 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4787 node4787Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2000 node2000Labels + mixedMoment B node2000 node2000Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1719 singletonSmall4787
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4787) = raw1719Labels := by decide +kernel
  rw [hl, canonical1719 B hB] at h
  have hc0 : mixedMoment B raw1719 (Fin.cases (0 : Fin 2) singletonSmall4787) =
      mixedMoment B node2000 node2000Labels := by
    have ha : raw1719 = raw1720 := by apply Matrix.ext; unfold raw1719 raw1720; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4787 = raw1720Labels := by decide +kernel
    rw [ha, hj, canonical1720 B hB]
  have hc1 : mixedMoment B raw1719 (Fin.cases (1 : Fin 2) singletonSmall4787) =
      mixedMoment B node2000 node2000Labels := by
    have ha : raw1719 = raw1721 := by apply Matrix.ext; unfold raw1719 raw1721; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4787 = raw1721Labels := by decide +kernel
    rw [ha, hj, canonical1721 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4788 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4788 node4788Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2003 node2003Labels + mixedMoment B node2006 node2006Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1722 singletonSmall4788
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4788) = raw1722Labels := by decide +kernel
  rw [hl, canonical1722 B hB] at h
  have hc0 : mixedMoment B raw1722 (Fin.cases (0 : Fin 2) singletonSmall4788) =
      mixedMoment B node2003 node2003Labels := by
    have ha : raw1722 = raw1723 := by apply Matrix.ext; unfold raw1722 raw1723; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4788 = raw1723Labels := by decide +kernel
    rw [ha, hj, canonical1723 B hB]
  have hc1 : mixedMoment B raw1722 (Fin.cases (1 : Fin 2) singletonSmall4788) =
      mixedMoment B node2006 node2006Labels := by
    have ha : raw1722 = raw1724 := by apply Matrix.ext; unfold raw1722 raw1724; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4788 = raw1724Labels := by decide +kernel
    rw [ha, hj, canonical1724 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4798 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4798 node4798Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2016 node2016Labels + mixedMoment B node2075 node2075Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1725 singletonSmall4798
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4798) = raw1725Labels := by decide +kernel
  rw [hl, canonical1725 B hB] at h
  have hc0 : mixedMoment B raw1725 (Fin.cases (0 : Fin 2) singletonSmall4798) =
      mixedMoment B node2016 node2016Labels := by
    have ha : raw1725 = raw1726 := by apply Matrix.ext; unfold raw1725 raw1726; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4798 = raw1726Labels := by decide +kernel
    rw [ha, hj, canonical1726 B hB]
  have hc1 : mixedMoment B raw1725 (Fin.cases (1 : Fin 2) singletonSmall4798) =
      mixedMoment B node2075 node2075Labels := by
    have ha : raw1725 = raw1727 := by apply Matrix.ext; unfold raw1725 raw1727; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4798 = raw1727Labels := by decide +kernel
    rw [ha, hj, canonical1727 B hB]
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

theorem singleton4800 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4800 node4800Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2018 node2018Labels + mixedMoment B node2018 node2018Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1728 singletonSmall4800
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4800) = raw1728Labels := by decide +kernel
  rw [hl, canonical1728 B hB] at h
  have hc0 : mixedMoment B raw1728 (Fin.cases (0 : Fin 2) singletonSmall4800) =
      mixedMoment B node2018 node2018Labels := by
    have ha : raw1728 = raw1729 := by apply Matrix.ext; unfold raw1728 raw1729; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4800 = raw1729Labels := by decide +kernel
    rw [ha, hj, canonical1729 B hB]
  have hc1 : mixedMoment B raw1728 (Fin.cases (1 : Fin 2) singletonSmall4800) =
      mixedMoment B node2018 node2018Labels := by
    have ha : raw1728 = raw1730 := by apply Matrix.ext; unfold raw1728 raw1730; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4800 = raw1730Labels := by decide +kernel
    rw [ha, hj, canonical1730 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4810 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4810 node4810Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2028 node2028Labels + mixedMoment B node2215 node2215Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1746 singletonSmall4810
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4810) = raw1746Labels := by decide +kernel
  rw [hl, canonical1746 B hB] at h
  have hc0 : mixedMoment B raw1746 (Fin.cases (0 : Fin 2) singletonSmall4810) =
      mixedMoment B node2028 node2028Labels := by
    have ha : raw1746 = raw1747 := by apply Matrix.ext; unfold raw1746 raw1747; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4810 = raw1747Labels := by decide +kernel
    rw [ha, hj, canonical1747 B hB]
  have hc1 : mixedMoment B raw1746 (Fin.cases (1 : Fin 2) singletonSmall4810) =
      mixedMoment B node2215 node2215Labels := by
    have ha : raw1746 = raw1748 := by apply Matrix.ext; unfold raw1746 raw1748; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4810 = raw1748Labels := by decide +kernel
    rw [ha, hj, canonical1748 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4828 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4828 node4828Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2048 node2048Labels + mixedMoment B node2082 node2082Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1758 singletonSmall4828
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4828) = raw1758Labels := by decide +kernel
  rw [hl, canonical1758 B hB] at h
  have hc0 : mixedMoment B raw1758 (Fin.cases (0 : Fin 2) singletonSmall4828) =
      mixedMoment B node2048 node2048Labels := by
    have ha : raw1758 = raw1759 := by apply Matrix.ext; unfold raw1758 raw1759; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4828 = raw1759Labels := by decide +kernel
    rw [ha, hj, canonical1759 B hB]
  have hc1 : mixedMoment B raw1758 (Fin.cases (1 : Fin 2) singletonSmall4828) =
      mixedMoment B node2082 node2082Labels := by
    have ha : raw1758 = raw1760 := by apply Matrix.ext; unfold raw1758 raw1760; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4828 = raw1760Labels := by decide +kernel
    rw [ha, hj, canonical1760 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4835 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4835 node4835Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2054 node2054Labels + mixedMoment B node2206 node2206Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1767 singletonSmall4835
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4835) = raw1767Labels := by decide +kernel
  rw [hl, canonical1767 B hB] at h
  have hc0 : mixedMoment B raw1767 (Fin.cases (0 : Fin 2) singletonSmall4835) =
      mixedMoment B node2054 node2054Labels := by
    have ha : raw1767 = raw1768 := by apply Matrix.ext; unfold raw1767 raw1768; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4835 = raw1768Labels := by decide +kernel
    rw [ha, hj, canonical1768 B hB]
  have hc1 : mixedMoment B raw1767 (Fin.cases (1 : Fin 2) singletonSmall4835) =
      mixedMoment B node2206 node2206Labels := by
    have ha : raw1767 = raw1769 := by apply Matrix.ext; unfold raw1767 raw1769; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4835 = raw1769Labels := by decide +kernel
    rw [ha, hj, canonical1769 B hB]
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

theorem singleton4865 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4865 node4865Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2106 node2106Labels + mixedMoment B node2242 node2242Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1791 singletonSmall4865
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4865) = raw1791Labels := by decide +kernel
  rw [hl, canonical1791 B hB] at h
  have hc0 : mixedMoment B raw1791 (Fin.cases (0 : Fin 2) singletonSmall4865) =
      mixedMoment B node2106 node2106Labels := by
    have ha : raw1791 = raw1792 := by apply Matrix.ext; unfold raw1791 raw1792; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4865 = raw1792Labels := by decide +kernel
    rw [ha, hj, canonical1792 B hB]
  have hc1 : mixedMoment B raw1791 (Fin.cases (1 : Fin 2) singletonSmall4865) =
      mixedMoment B node2242 node2242Labels := by
    have ha : raw1791 = raw1793 := by apply Matrix.ext; unfold raw1791 raw1793; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4865 = raw1793Labels := by decide +kernel
    rw [ha, hj, canonical1793 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4996 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4996 node4996Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2382 node2382Labels + mixedMoment B node3340 node3340Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2007 singletonSmall4996
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4996) = raw2007Labels := by decide +kernel
  rw [hl, canonical2007 B hB] at h
  have hc0 : mixedMoment B raw2007 (Fin.cases (0 : Fin 2) singletonSmall4996) =
      mixedMoment B node2382 node2382Labels := by
    have ha : raw2007 = raw2008 := by apply Matrix.ext; unfold raw2007 raw2008; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4996 = raw2008Labels := by decide +kernel
    rw [ha, hj, canonical2008 B hB]
  have hc1 : mixedMoment B raw2007 (Fin.cases (1 : Fin 2) singletonSmall4996) =
      mixedMoment B node3340 node3340Labels := by
    have ha : raw2007 = raw2009 := by apply Matrix.ext; unfold raw2007 raw2009; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4996 = raw2009Labels := by decide +kernel
    rw [ha, hj, canonical2009 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5003 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5003 node5003Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2388 node2388Labels + mixedMoment B node3354 node3354Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2016 singletonSmall5003
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5003) = raw2016Labels := by decide +kernel
  rw [hl, canonical2016 B hB] at h
  have hc0 : mixedMoment B raw2016 (Fin.cases (0 : Fin 2) singletonSmall5003) =
      mixedMoment B node2388 node2388Labels := by
    have ha : raw2016 = raw2017 := by apply Matrix.ext; unfold raw2016 raw2017; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5003 = raw2017Labels := by decide +kernel
    rw [ha, hj, canonical2017 B hB]
  have hc1 : mixedMoment B raw2016 (Fin.cases (1 : Fin 2) singletonSmall5003) =
      mixedMoment B node3354 node3354Labels := by
    have ha : raw2016 = raw2018 := by apply Matrix.ext; unfold raw2016 raw2018; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5003 = raw2018Labels := by decide +kernel
    rw [ha, hj, canonical2018 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5015 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5015 node5015Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2400 node2400Labels + mixedMoment B node3344 node3344Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2025 singletonSmall5015
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5015) = raw2025Labels := by decide +kernel
  rw [hl, canonical2025 B hB] at h
  have hc0 : mixedMoment B raw2025 (Fin.cases (0 : Fin 2) singletonSmall5015) =
      mixedMoment B node2400 node2400Labels := by
    have ha : raw2025 = raw2026 := by apply Matrix.ext; unfold raw2025 raw2026; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5015 = raw2026Labels := by decide +kernel
    rw [ha, hj, canonical2026 B hB]
  have hc1 : mixedMoment B raw2025 (Fin.cases (1 : Fin 2) singletonSmall5015) =
      mixedMoment B node3344 node3344Labels := by
    have ha : raw2025 = raw2027 := by apply Matrix.ext; unfold raw2025 raw2027; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5015 = raw2027Labels := by decide +kernel
    rw [ha, hj, canonical2027 B hB]
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

theorem singleton5258 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5258 node5258Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2722 node2722Labels + mixedMoment B node3533 node3533Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2271 singletonSmall5258
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5258) = raw2271Labels := by decide +kernel
  rw [hl, canonical2271 B hB] at h
  have hc0 : mixedMoment B raw2271 (Fin.cases (0 : Fin 2) singletonSmall5258) =
      mixedMoment B node2722 node2722Labels := by
    have ha : raw2271 = raw2272 := by apply Matrix.ext; unfold raw2271 raw2272; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5258 = raw2272Labels := by decide +kernel
    rw [ha, hj, canonical2272 B hB]
  have hc1 : mixedMoment B raw2271 (Fin.cases (1 : Fin 2) singletonSmall5258) =
      mixedMoment B node3533 node3533Labels := by
    have ha : raw2271 = raw2273 := by apply Matrix.ext; unfold raw2271 raw2273; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5258 = raw2273Labels := by decide +kernel
    rw [ha, hj, canonical2273 B hB]
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

theorem singleton5346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5346 node5346Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3683 node3683Labels + mixedMoment B node3746 node3746Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2385 singletonSmall5346
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5346) = raw2385Labels := by decide +kernel
  rw [hl, canonical2385 B hB] at h
  have hc0 : mixedMoment B raw2385 (Fin.cases (0 : Fin 2) singletonSmall5346) =
      mixedMoment B node3683 node3683Labels := by
    have ha : raw2385 = raw2386 := by apply Matrix.ext; unfold raw2385 raw2386; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5346 = raw2386Labels := by decide +kernel
    rw [ha, hj, canonical2386 B hB]
  have hc1 : mixedMoment B raw2385 (Fin.cases (1 : Fin 2) singletonSmall5346) =
      mixedMoment B node3746 node3746Labels := by
    have ha : raw2385 = raw2387 := by apply Matrix.ext; unfold raw2385 raw2387; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5346 = raw2387Labels := by decide +kernel
    rw [ha, hj, canonical2387 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5349 node5349Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3687 node3687Labels + mixedMoment B node3749 node3749Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2388 singletonSmall5349
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5349) = raw2388Labels := by decide +kernel
  rw [hl, canonical2388 B hB] at h
  have hc0 : mixedMoment B raw2388 (Fin.cases (0 : Fin 2) singletonSmall5349) =
      mixedMoment B node3687 node3687Labels := by
    have ha : raw2388 = raw2389 := by apply Matrix.ext; unfold raw2388 raw2389; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5349 = raw2389Labels := by decide +kernel
    rw [ha, hj, canonical2389 B hB]
  have hc1 : mixedMoment B raw2388 (Fin.cases (1 : Fin 2) singletonSmall5349) =
      mixedMoment B node3749 node3749Labels := by
    have ha : raw2388 = raw2390 := by apply Matrix.ext; unfold raw2388 raw2390; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5349 = raw2390Labels := by decide +kernel
    rw [ha, hj, canonical2390 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5355 node5355Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3693 node3693Labels + mixedMoment B node3770 node3770Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2400 singletonSmall5355
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5355) = raw2400Labels := by decide +kernel
  rw [hl, canonical2400 B hB] at h
  have hc0 : mixedMoment B raw2400 (Fin.cases (0 : Fin 2) singletonSmall5355) =
      mixedMoment B node3693 node3693Labels := by
    have ha : raw2400 = raw2401 := by apply Matrix.ext; unfold raw2400 raw2401; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5355 = raw2401Labels := by decide +kernel
    rw [ha, hj, canonical2401 B hB]
  have hc1 : mixedMoment B raw2400 (Fin.cases (1 : Fin 2) singletonSmall5355) =
      mixedMoment B node3770 node3770Labels := by
    have ha : raw2400 = raw2402 := by apply Matrix.ext; unfold raw2400 raw2402; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5355 = raw2402Labels := by decide +kernel
    rw [ha, hj, canonical2402 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5364 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5364 node5364Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3702 node3702Labels + mixedMoment B node3702 node3702Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2409 singletonSmall5364
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5364) = raw2409Labels := by decide +kernel
  rw [hl, canonical2409 B hB] at h
  have hc0 : mixedMoment B raw2409 (Fin.cases (0 : Fin 2) singletonSmall5364) =
      mixedMoment B node3702 node3702Labels := by
    have ha : raw2409 = raw2410 := by apply Matrix.ext; unfold raw2409 raw2410; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5364 = raw2410Labels := by decide +kernel
    rw [ha, hj, canonical2410 B hB]
  have hc1 : mixedMoment B raw2409 (Fin.cases (1 : Fin 2) singletonSmall5364) =
      mixedMoment B node3702 node3702Labels := by
    have ha : raw2409 = raw2411 := by apply Matrix.ext; unfold raw2409 raw2411; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5364 = raw2411Labels := by decide +kernel
    rw [ha, hj, canonical2411 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5368 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5368 node5368Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3705 node3705Labels + mixedMoment B node3767 node3767Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2415 singletonSmall5368
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5368) = raw2415Labels := by decide +kernel
  rw [hl, canonical2415 B hB] at h
  have hc0 : mixedMoment B raw2415 (Fin.cases (0 : Fin 2) singletonSmall5368) =
      mixedMoment B node3705 node3705Labels := by
    have ha : raw2415 = raw2416 := by apply Matrix.ext; unfold raw2415 raw2416; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5368 = raw2416Labels := by decide +kernel
    rw [ha, hj, canonical2416 B hB]
  have hc1 : mixedMoment B raw2415 (Fin.cases (1 : Fin 2) singletonSmall5368) =
      mixedMoment B node3767 node3767Labels := by
    have ha : raw2415 = raw2417 := by apply Matrix.ext; unfold raw2415 raw2417; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5368 = raw2417Labels := by decide +kernel
    rw [ha, hj, canonical2417 B hB]
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

theorem singleton5395 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5395 node5395Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3781 node3781Labels + mixedMoment B node3794 node3794Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2463 singletonSmall5395
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5395) = raw2463Labels := by decide +kernel
  rw [hl, canonical2463 B hB] at h
  have hc0 : mixedMoment B raw2463 (Fin.cases (0 : Fin 2) singletonSmall5395) =
      mixedMoment B node3781 node3781Labels := by
    have ha : raw2463 = raw2464 := by apply Matrix.ext; unfold raw2463 raw2464; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5395 = raw2464Labels := by decide +kernel
    rw [ha, hj, canonical2464 B hB]
  have hc1 : mixedMoment B raw2463 (Fin.cases (1 : Fin 2) singletonSmall5395) =
      mixedMoment B node3794 node3794Labels := by
    have ha : raw2463 = raw2465 := by apply Matrix.ext; unfold raw2463 raw2465; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5395 = raw2465Labels := by decide +kernel
    rw [ha, hj, canonical2465 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5400 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5400 node5400Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3786 node3786Labels + mixedMoment B node3799 node3799Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2472 singletonSmall5400
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5400) = raw2472Labels := by decide +kernel
  rw [hl, canonical2472 B hB] at h
  have hc0 : mixedMoment B raw2472 (Fin.cases (0 : Fin 2) singletonSmall5400) =
      mixedMoment B node3786 node3786Labels := by
    have ha : raw2472 = raw2473 := by apply Matrix.ext; unfold raw2472 raw2473; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5400 = raw2473Labels := by decide +kernel
    rw [ha, hj, canonical2473 B hB]
  have hc1 : mixedMoment B raw2472 (Fin.cases (1 : Fin 2) singletonSmall5400) =
      mixedMoment B node3799 node3799Labels := by
    have ha : raw2472 = raw2474 := by apply Matrix.ext; unfold raw2472 raw2474; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5400 = raw2474Labels := by decide +kernel
    rw [ha, hj, canonical2474 B hB]
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

theorem singleton5432 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5432 node5432Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3850 node3850Labels + mixedMoment B node3850 node3850Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2523 singletonSmall5432
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5432) = raw2523Labels := by decide +kernel
  rw [hl, canonical2523 B hB] at h
  have hc0 : mixedMoment B raw2523 (Fin.cases (0 : Fin 2) singletonSmall5432) =
      mixedMoment B node3850 node3850Labels := by
    have ha : raw2523 = raw2524 := by apply Matrix.ext; unfold raw2523 raw2524; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5432 = raw2524Labels := by decide +kernel
    rw [ha, hj, canonical2524 B hB]
  have hc1 : mixedMoment B raw2523 (Fin.cases (1 : Fin 2) singletonSmall5432) =
      mixedMoment B node3850 node3850Labels := by
    have ha : raw2523 = raw2525 := by apply Matrix.ext; unfold raw2523 raw2525; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5432 = raw2525Labels := by decide +kernel
    rw [ha, hj, canonical2525 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5438 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5438 node5438Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3857 node3857Labels + mixedMoment B node3876 node3876Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2538 singletonSmall5438
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5438) = raw2538Labels := by decide +kernel
  rw [hl, canonical2538 B hB] at h
  have hc0 : mixedMoment B raw2538 (Fin.cases (0 : Fin 2) singletonSmall5438) =
      mixedMoment B node3857 node3857Labels := by
    have ha : raw2538 = raw2539 := by apply Matrix.ext; unfold raw2538 raw2539; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5438 = raw2539Labels := by decide +kernel
    rw [ha, hj, canonical2539 B hB]
  have hc1 : mixedMoment B raw2538 (Fin.cases (1 : Fin 2) singletonSmall5438) =
      mixedMoment B node3876 node3876Labels := by
    have ha : raw2538 = raw2540 := by apply Matrix.ext; unfold raw2538 raw2540; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5438 = raw2540Labels := by decide +kernel
    rw [ha, hj, canonical2540 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2000 node2000Labels = Sparse.eval nodeValue2000 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2000) = mixedMoment B node2000 node2000Labels := rfl
  simpa [nodeValue2000, Sparse.eval] using hc.symm

theorem sound2003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2003 node2003Labels = Sparse.eval nodeValue2003 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2003) = mixedMoment B node2003 node2003Labels := rfl
  simpa [nodeValue2003, Sparse.eval] using hc.symm

theorem sound2006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2006 node2006Labels = Sparse.eval nodeValue2006 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2006) = mixedMoment B node2006 node2006Labels := rfl
  simpa [nodeValue2006, Sparse.eval] using hc.symm

theorem sound2016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2016 node2016Labels = Sparse.eval nodeValue2016 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2016) = mixedMoment B node2016 node2016Labels := rfl
  simpa [nodeValue2016, Sparse.eval] using hc.symm

theorem sound2018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2018 node2018Labels = Sparse.eval nodeValue2018 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2018) = mixedMoment B node2018 node2018Labels := rfl
  simpa [nodeValue2018, Sparse.eval] using hc.symm

theorem sound2028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2028 node2028Labels = Sparse.eval nodeValue2028 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2028) = mixedMoment B node2028 node2028Labels := rfl
  simpa [nodeValue2028, Sparse.eval] using hc.symm

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

theorem sound2048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2048 node2048Labels = Sparse.eval nodeValue2048 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2048) = mixedMoment B node2048 node2048Labels := rfl
  simpa [nodeValue2048, Sparse.eval] using hc.symm

theorem sound2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2054 node2054Labels = Sparse.eval nodeValue2054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2054) = mixedMoment B node2054 node2054Labels := rfl
  simpa [nodeValue2054, Sparse.eval] using hc.symm

theorem sound2075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2075 node2075Labels = Sparse.eval nodeValue2075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2075) = mixedMoment B node2075 node2075Labels := rfl
  simpa [nodeValue2075, Sparse.eval] using hc.symm

theorem sound2082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2082 node2082Labels = Sparse.eval nodeValue2082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2082) = mixedMoment B node2082 node2082Labels := rfl
  simpa [nodeValue2082, Sparse.eval] using hc.symm

theorem sound2106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2106 node2106Labels = Sparse.eval nodeValue2106 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2106) = mixedMoment B node2106 node2106Labels := rfl
  simpa [nodeValue2106, Sparse.eval] using hc.symm

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

theorem sound2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2206 node2206Labels = Sparse.eval nodeValue2206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2206) = mixedMoment B node2206 node2206Labels := rfl
  simpa [nodeValue2206, Sparse.eval] using hc.symm

theorem sound2215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2215 node2215Labels = Sparse.eval nodeValue2215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2215) = mixedMoment B node2215 node2215Labels := rfl
  simpa [nodeValue2215, Sparse.eval] using hc.symm

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2382 node2382Labels = Sparse.eval nodeValue2382 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2382) = mixedMoment B node2382 node2382Labels := rfl
  simpa [nodeValue2382, Sparse.eval] using hc.symm

theorem sound2388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2388 node2388Labels = Sparse.eval nodeValue2388 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2388) = mixedMoment B node2388 node2388Labels := rfl
  simpa [nodeValue2388, Sparse.eval] using hc.symm

theorem sound2400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2400 node2400Labels = Sparse.eval nodeValue2400 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2400) = mixedMoment B node2400 node2400Labels := rfl
  simpa [nodeValue2400, Sparse.eval] using hc.symm

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

theorem sound2722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2722 node2722Labels = Sparse.eval nodeValue2722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2722) = mixedMoment B node2722 node2722Labels := rfl
  simpa [nodeValue2722, Sparse.eval] using hc.symm

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

theorem sound3340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3340 node3340Labels = Sparse.eval nodeValue3340 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3340) = mixedMoment B node3340 node3340Labels := rfl
  simpa [nodeValue3340, Sparse.eval] using hc.symm

theorem sound3344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3344 node3344Labels = Sparse.eval nodeValue3344 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3344) = mixedMoment B node3344 node3344Labels := rfl
  simpa [nodeValue3344, Sparse.eval] using hc.symm

theorem sound3354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3354 node3354Labels = Sparse.eval nodeValue3354 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3354) = mixedMoment B node3354 node3354Labels := rfl
  simpa [nodeValue3354, Sparse.eval] using hc.symm

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

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

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

theorem sound3683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3683 node3683Labels = Sparse.eval nodeValue3683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3683) = mixedMoment B node3683 node3683Labels := rfl
  simpa [nodeValue3683, Sparse.eval] using hc.symm

theorem sound3687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3687 node3687Labels = Sparse.eval nodeValue3687 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3687) = mixedMoment B node3687 node3687Labels := rfl
  simpa [nodeValue3687, Sparse.eval] using hc.symm

theorem sound3693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3693 node3693Labels = Sparse.eval nodeValue3693 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3693) = mixedMoment B node3693 node3693Labels := rfl
  simpa [nodeValue3693, Sparse.eval] using hc.symm

theorem sound3702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3702 node3702Labels = Sparse.eval nodeValue3702 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3702) = mixedMoment B node3702 node3702Labels := rfl
  simpa [nodeValue3702, Sparse.eval] using hc.symm

theorem sound3705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3705 node3705Labels = Sparse.eval nodeValue3705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3705) = mixedMoment B node3705 node3705Labels := rfl
  simpa [nodeValue3705, Sparse.eval] using hc.symm

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

theorem sound3746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3746 node3746Labels = Sparse.eval nodeValue3746 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3746) = mixedMoment B node3746 node3746Labels := rfl
  simpa [nodeValue3746, Sparse.eval] using hc.symm

theorem sound3749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3749 node3749Labels = Sparse.eval nodeValue3749 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3749) = mixedMoment B node3749 node3749Labels := rfl
  simpa [nodeValue3749, Sparse.eval] using hc.symm

theorem sound3767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3767 node3767Labels = Sparse.eval nodeValue3767 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3767) = mixedMoment B node3767 node3767Labels := rfl
  simpa [nodeValue3767, Sparse.eval] using hc.symm

theorem sound3770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3770 node3770Labels = Sparse.eval nodeValue3770 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3770) = mixedMoment B node3770 node3770Labels := rfl
  simpa [nodeValue3770, Sparse.eval] using hc.symm

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

theorem sound3781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3781 node3781Labels = Sparse.eval nodeValue3781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3781) = mixedMoment B node3781 node3781Labels := rfl
  simpa [nodeValue3781, Sparse.eval] using hc.symm

theorem sound3786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3786 node3786Labels = Sparse.eval nodeValue3786 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3786) = mixedMoment B node3786 node3786Labels := rfl
  simpa [nodeValue3786, Sparse.eval] using hc.symm

theorem sound3794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3794 node3794Labels = Sparse.eval nodeValue3794 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3794) = mixedMoment B node3794 node3794Labels := rfl
  simpa [nodeValue3794, Sparse.eval] using hc.symm

theorem sound3795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3795 node3795Labels = Sparse.eval nodeValue3795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3795) = mixedMoment B node3795 node3795Labels := rfl
  simpa [nodeValue3795, Sparse.eval] using hc.symm

theorem sound3799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3799 node3799Labels = Sparse.eval nodeValue3799 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3799) = mixedMoment B node3799 node3799Labels := rfl
  simpa [nodeValue3799, Sparse.eval] using hc.symm

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

theorem sound3849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3849 node3849Labels = Sparse.eval nodeValue3849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3849) = mixedMoment B node3849 node3849Labels := rfl
  simpa [nodeValue3849, Sparse.eval] using hc.symm

theorem sound3850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3850 node3850Labels = Sparse.eval nodeValue3850 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3850) = mixedMoment B node3850 node3850Labels := rfl
  simpa [nodeValue3850, Sparse.eval] using hc.symm

theorem sound3857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3857 node3857Labels = Sparse.eval nodeValue3857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3857) = mixedMoment B node3857 node3857Labels := rfl
  simpa [nodeValue3857, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4787 node4787Labels = Sparse.eval nodeValue4787 (mixedVector B) := by
  have h := singleton4787 B _hB
  rw [sound2000 B _hB _hF] at h
  norm_num [nodeValue4787, nodeValue2000, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4788 node4788Labels = Sparse.eval nodeValue4788 (mixedVector B) := by
  have h := singleton4788 B _hB
  rw [sound2003 B _hB _hF, sound2006 B _hB _hF] at h
  norm_num [nodeValue4788, nodeValue2003, nodeValue2006, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4798 node4798Labels = Sparse.eval nodeValue4798 (mixedVector B) := by
  have h := singleton4798 B _hB
  rw [sound2016 B _hB _hF, sound2075 B _hB _hF] at h
  norm_num [nodeValue4798, nodeValue2016, nodeValue2075, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4800 node4800Labels = Sparse.eval nodeValue4800 (mixedVector B) := by
  have h := singleton4800 B _hB
  rw [sound2018 B _hB _hF] at h
  norm_num [nodeValue4800, nodeValue2018, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4810 node4810Labels = Sparse.eval nodeValue4810 (mixedVector B) := by
  have h := singleton4810 B _hB
  rw [sound2028 B _hB _hF, sound2215 B _hB _hF] at h
  norm_num [nodeValue4810, nodeValue2028, nodeValue2215, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4828 node4828Labels = Sparse.eval nodeValue4828 (mixedVector B) := by
  have h := singleton4828 B _hB
  rw [sound2048 B _hB _hF, sound2082 B _hB _hF] at h
  norm_num [nodeValue4828, nodeValue2048, nodeValue2082, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4835 node4835Labels = Sparse.eval nodeValue4835 (mixedVector B) := by
  have h := singleton4835 B _hB
  rw [sound2054 B _hB _hF, sound2206 B _hB _hF] at h
  norm_num [nodeValue4835, nodeValue2054, nodeValue2206, Sparse.eval] at h ⊢
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

theorem sound4865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4865 node4865Labels = Sparse.eval nodeValue4865 (mixedVector B) := by
  have h := singleton4865 B _hB
  rw [sound2106 B _hB _hF, sound2242 B _hB _hF] at h
  norm_num [nodeValue4865, nodeValue2106, nodeValue2242, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4996 node4996Labels = Sparse.eval nodeValue4996 (mixedVector B) := by
  have h := singleton4996 B _hB
  rw [sound2382 B _hB _hF, sound3340 B _hB _hF] at h
  norm_num [nodeValue4996, nodeValue2382, nodeValue3340, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5003 node5003Labels = Sparse.eval nodeValue5003 (mixedVector B) := by
  have h := singleton5003 B _hB
  rw [sound2388 B _hB _hF, sound3354 B _hB _hF] at h
  norm_num [nodeValue5003, nodeValue2388, nodeValue3354, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5015 node5015Labels = Sparse.eval nodeValue5015 (mixedVector B) := by
  have h := singleton5015 B _hB
  rw [sound2400 B _hB _hF, sound3344 B _hB _hF] at h
  norm_num [nodeValue5015, nodeValue2400, nodeValue3344, Sparse.eval] at h ⊢
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

theorem sound5258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5258 node5258Labels = Sparse.eval nodeValue5258 (mixedVector B) := by
  have h := singleton5258 B _hB
  rw [sound2722 B _hB _hF, sound3533 B _hB _hF] at h
  norm_num [nodeValue5258, nodeValue2722, nodeValue3533, Sparse.eval] at h ⊢
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

theorem sound5346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5346 node5346Labels = Sparse.eval nodeValue5346 (mixedVector B) := by
  have h := singleton5346 B _hB
  rw [sound3683 B _hB _hF, sound3746 B _hB _hF] at h
  norm_num [nodeValue5346, nodeValue3683, nodeValue3746, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5349 node5349Labels = Sparse.eval nodeValue5349 (mixedVector B) := by
  have h := singleton5349 B _hB
  rw [sound3687 B _hB _hF, sound3749 B _hB _hF] at h
  norm_num [nodeValue5349, nodeValue3687, nodeValue3749, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5355 node5355Labels = Sparse.eval nodeValue5355 (mixedVector B) := by
  have h := singleton5355 B _hB
  rw [sound3693 B _hB _hF, sound3770 B _hB _hF] at h
  norm_num [nodeValue5355, nodeValue3693, nodeValue3770, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5364 node5364Labels = Sparse.eval nodeValue5364 (mixedVector B) := by
  have h := singleton5364 B _hB
  rw [sound3702 B _hB _hF] at h
  norm_num [nodeValue5364, nodeValue3702, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5368 node5368Labels = Sparse.eval nodeValue5368 (mixedVector B) := by
  have h := singleton5368 B _hB
  rw [sound3705 B _hB _hF, sound3767 B _hB _hF] at h
  norm_num [nodeValue5368, nodeValue3705, nodeValue3767, Sparse.eval] at h ⊢
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

theorem sound5378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5378 node5378Labels = Sparse.eval nodeValue5378 (mixedVector B) := by
  have h := singleton5378 B _hB
  rw [sound3719 B _hB _hF, sound3795 B _hB _hF] at h
  norm_num [nodeValue5378, nodeValue3719, nodeValue3795, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5395 node5395Labels = Sparse.eval nodeValue5395 (mixedVector B) := by
  have h := singleton5395 B _hB
  rw [sound3781 B _hB _hF, sound3794 B _hB _hF] at h
  norm_num [nodeValue5395, nodeValue3781, nodeValue3794, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5400 node5400Labels = Sparse.eval nodeValue5400 (mixedVector B) := by
  have h := singleton5400 B _hB
  rw [sound3786 B _hB _hF, sound3799 B _hB _hF] at h
  norm_num [nodeValue5400, nodeValue3786, nodeValue3799, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5424 node5424Labels = Sparse.eval nodeValue5424 (mixedVector B) := by
  have h := singleton5424 B _hB
  rw [sound3838 B _hB _hF, sound3843 B _hB _hF] at h
  norm_num [nodeValue5424, nodeValue3838, nodeValue3843, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5431 node5431Labels = Sparse.eval nodeValue5431 (mixedVector B) := by
  have h := singleton5431 B _hB
  rw [sound3849 B _hB _hF, sound3875 B _hB _hF] at h
  norm_num [nodeValue5431, nodeValue3849, nodeValue3875, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5432 node5432Labels = Sparse.eval nodeValue5432 (mixedVector B) := by
  have h := singleton5432 B _hB
  rw [sound3850 B _hB _hF] at h
  norm_num [nodeValue5432, nodeValue3850, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5438 node5438Labels = Sparse.eval nodeValue5438 (mixedVector B) := by
  have h := singleton5438 B _hB
  rw [sound3857 B _hB _hF, sound3876 B _hB _hF] at h
  norm_num [nodeValue5438, nodeValue3857, nodeValue3876, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources33
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1081 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1081 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1081 + difference 0 1) (sourceB1081 + difference 1 0) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA1081 + difference 0 1) (sourceB1081 + difference 1 0) sourceC1081) = raw17948 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17948; decide +kernel
    rw [ha]
    exact (canonical17948 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1081 + difference 0 2) (sourceB1081 + difference 2 0) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1081 + difference 0 2) (sourceB1081 + difference 2 0) sourceC1081) = raw17949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17949; decide +kernel
    rw [ha]
    exact (canonical17949 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1081 + difference 0 3) (sourceB1081 + difference 3 0) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1081 + difference 0 3) (sourceB1081 + difference 3 0) sourceC1081) = raw17950 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17950; decide +kernel
    rw [ha]
    exact (canonical17950 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1081 + difference 0 4) (sourceB1081 + difference 4 0) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1081 + difference 0 4) (sourceB1081 + difference 4 0) sourceC1081) = raw17951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17951; decide +kernel
    rw [ha]
    exact (canonical17951 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1081 + difference 0 5) (sourceB1081 + difference 5 0) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1081 + difference 0 5) (sourceB1081 + difference 5 0) sourceC1081) = raw17952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17952; decide +kernel
    rw [ha]
    exact (canonical17952 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1081 + difference 1 0) (sourceB1081 + difference 0 1) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA1081 + difference 1 0) (sourceB1081 + difference 0 1) sourceC1081) = raw17953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17953; decide +kernel
    rw [ha]
    exact (canonical17953 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1081 + difference 1 2) (sourceB1081 + difference 2 1) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1081 + difference 1 2) (sourceB1081 + difference 2 1) sourceC1081) = raw17954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17954; decide +kernel
    rw [ha]
    exact (canonical17954 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1081 + difference 1 3) (sourceB1081 + difference 3 1) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA1081 + difference 1 3) (sourceB1081 + difference 3 1) sourceC1081) = raw17955 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17955; decide +kernel
    rw [ha]
    exact (canonical17955 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1081 + difference 1 4) (sourceB1081 + difference 4 1) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1081 + difference 1 4) (sourceB1081 + difference 4 1) sourceC1081) = raw17956 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17956; decide +kernel
    rw [ha]
    exact (canonical17956 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1081 + difference 1 5) (sourceB1081 + difference 5 1) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1081 + difference 1 5) (sourceB1081 + difference 5 1) sourceC1081) = raw17957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17957; decide +kernel
    rw [ha]
    exact (canonical17957 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1081 + difference 2 0) (sourceB1081 + difference 0 2) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA1081 + difference 2 0) (sourceB1081 + difference 0 2) sourceC1081) = raw17958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17958; decide +kernel
    rw [ha]
    exact (canonical17958 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1081 + difference 2 1) (sourceB1081 + difference 1 2) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA1081 + difference 2 1) (sourceB1081 + difference 1 2) sourceC1081) = raw17959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17959; decide +kernel
    rw [ha]
    exact (canonical17959 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1081 + difference 2 3) (sourceB1081 + difference 3 2) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA1081 + difference 2 3) (sourceB1081 + difference 3 2) sourceC1081) = raw17960 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17960; decide +kernel
    rw [ha]
    exact (canonical17960 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1081 + difference 2 4) (sourceB1081 + difference 4 2) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA1081 + difference 2 4) (sourceB1081 + difference 4 2) sourceC1081) = raw17961 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17961; decide +kernel
    rw [ha]
    exact (canonical17961 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1081 + difference 2 5) (sourceB1081 + difference 5 2) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1081 + difference 2 5) (sourceB1081 + difference 5 2) sourceC1081) = raw17962 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17962; decide +kernel
    rw [ha]
    exact (canonical17962 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1081 + difference 3 0) (sourceB1081 + difference 0 3) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA1081 + difference 3 0) (sourceB1081 + difference 0 3) sourceC1081) = raw17963 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17963; decide +kernel
    rw [ha]
    exact (canonical17963 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1081 + difference 3 1) (sourceB1081 + difference 1 3) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA1081 + difference 3 1) (sourceB1081 + difference 1 3) sourceC1081) = raw17964 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17964; decide +kernel
    rw [ha]
    exact (canonical17964 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1081 + difference 3 2) (sourceB1081 + difference 2 3) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1081 + difference 3 2) (sourceB1081 + difference 2 3) sourceC1081) = raw17965 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17965; decide +kernel
    rw [ha]
    exact (canonical17965 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1081 + difference 3 4) (sourceB1081 + difference 4 3) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA1081 + difference 3 4) (sourceB1081 + difference 4 3) sourceC1081) = raw17966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17966; decide +kernel
    rw [ha]
    exact (canonical17966 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1081 + difference 3 5) (sourceB1081 + difference 5 3) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA1081 + difference 3 5) (sourceB1081 + difference 5 3) sourceC1081) = raw17967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17967; decide +kernel
    rw [ha]
    exact (canonical17967 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1081 + difference 4 0) (sourceB1081 + difference 0 4) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA1081 + difference 4 0) (sourceB1081 + difference 0 4) sourceC1081) = raw17968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17968; decide +kernel
    rw [ha]
    exact (canonical17968 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1081 + difference 4 1) (sourceB1081 + difference 1 4) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA1081 + difference 4 1) (sourceB1081 + difference 1 4) sourceC1081) = raw17969 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17969; decide +kernel
    rw [ha]
    exact (canonical17969 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1081 + difference 4 2) (sourceB1081 + difference 2 4) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA1081 + difference 4 2) (sourceB1081 + difference 2 4) sourceC1081) = raw17970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17970; decide +kernel
    rw [ha]
    exact (canonical17970 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1081 + difference 4 3) (sourceB1081 + difference 3 4) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA1081 + difference 4 3) (sourceB1081 + difference 3 4) sourceC1081) = raw17971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17971; decide +kernel
    rw [ha]
    exact (canonical17971 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1081 + difference 4 5) (sourceB1081 + difference 5 4) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1081 + difference 4 5) (sourceB1081 + difference 5 4) sourceC1081) = raw17972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17972; decide +kernel
    rw [ha]
    exact (canonical17972 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1081 + difference 5 0) (sourceB1081 + difference 0 5) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA1081 + difference 5 0) (sourceB1081 + difference 0 5) sourceC1081) = raw17973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17973; decide +kernel
    rw [ha]
    exact (canonical17973 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1081 + difference 5 1) (sourceB1081 + difference 1 5) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA1081 + difference 5 1) (sourceB1081 + difference 1 5) sourceC1081) = raw17974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17974; decide +kernel
    rw [ha]
    exact (canonical17974 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1081 + difference 5 2) (sourceB1081 + difference 2 5) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA1081 + difference 5 2) (sourceB1081 + difference 2 5) sourceC1081) = raw17975 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17975; decide +kernel
    rw [ha]
    exact (canonical17975 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1081 + difference 5 3) (sourceB1081 + difference 3 5) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4787) := by
    have ha : (tripleCharges (sourceA1081 + difference 5 3) (sourceB1081 + difference 3 5) sourceC1081) = raw17976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17976; decide +kernel
    rw [ha]
    exact (canonical17976 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1081 + difference 5 4) (sourceB1081 + difference 4 5) sourceC1081) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA1081 + difference 5 4) (sourceB1081 + difference 4 5) sourceC1081) = raw17977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1081 sourceB1081 sourceC1081 difference raw17977; decide +kernel
    rw [ha]
    exact (canonical17977 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1081 sourceB1081 sourceC1081
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1081, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources34
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1090 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1090 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1090 + difference 0 1) (sourceB1090 + difference 1 0) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1090 + difference 0 1) (sourceB1090 + difference 1 0) sourceC1090) = raw18182 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18182; decide +kernel
    rw [ha]
    exact (canonical18182 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1090 + difference 0 2) (sourceB1090 + difference 2 0) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1090 + difference 0 2) (sourceB1090 + difference 2 0) sourceC1090) = raw18183 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18183; decide +kernel
    rw [ha]
    exact (canonical18183 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1090 + difference 0 3) (sourceB1090 + difference 3 0) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1090 + difference 0 3) (sourceB1090 + difference 3 0) sourceC1090) = raw18184 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18184; decide +kernel
    rw [ha]
    exact (canonical18184 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1090 + difference 0 4) (sourceB1090 + difference 4 0) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1090 + difference 0 4) (sourceB1090 + difference 4 0) sourceC1090) = raw18185 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18185; decide +kernel
    rw [ha]
    exact (canonical18185 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1090 + difference 0 5) (sourceB1090 + difference 5 0) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1090 + difference 0 5) (sourceB1090 + difference 5 0) sourceC1090) = raw18186 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18186; decide +kernel
    rw [ha]
    exact (canonical18186 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1090 + difference 1 0) (sourceB1090 + difference 0 1) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA1090 + difference 1 0) (sourceB1090 + difference 0 1) sourceC1090) = raw18187 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18187; decide +kernel
    rw [ha]
    exact (canonical18187 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1090 + difference 1 2) (sourceB1090 + difference 2 1) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1090 + difference 1 2) (sourceB1090 + difference 2 1) sourceC1090) = raw18188 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18188; decide +kernel
    rw [ha]
    exact (canonical18188 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1090 + difference 1 3) (sourceB1090 + difference 3 1) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA1090 + difference 1 3) (sourceB1090 + difference 3 1) sourceC1090) = raw18189 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18189; decide +kernel
    rw [ha]
    exact (canonical18189 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1090 + difference 1 4) (sourceB1090 + difference 4 1) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA1090 + difference 1 4) (sourceB1090 + difference 4 1) sourceC1090) = raw18190 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18190; decide +kernel
    rw [ha]
    exact (canonical18190 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1090 + difference 1 5) (sourceB1090 + difference 5 1) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1090 + difference 1 5) (sourceB1090 + difference 5 1) sourceC1090) = raw18191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18191; decide +kernel
    rw [ha]
    exact (canonical18191 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1090 + difference 2 0) (sourceB1090 + difference 0 2) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA1090 + difference 2 0) (sourceB1090 + difference 0 2) sourceC1090) = raw18192 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18192; decide +kernel
    rw [ha]
    exact (canonical18192 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1090 + difference 2 1) (sourceB1090 + difference 1 2) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1090 + difference 2 1) (sourceB1090 + difference 1 2) sourceC1090) = raw18193 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18193; decide +kernel
    rw [ha]
    exact (canonical18193 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1090 + difference 2 3) (sourceB1090 + difference 3 2) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA1090 + difference 2 3) (sourceB1090 + difference 3 2) sourceC1090) = raw18194 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18194; decide +kernel
    rw [ha]
    exact (canonical18194 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1090 + difference 2 4) (sourceB1090 + difference 4 2) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA1090 + difference 2 4) (sourceB1090 + difference 4 2) sourceC1090) = raw18195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18195; decide +kernel
    rw [ha]
    exact (canonical18195 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1090 + difference 2 5) (sourceB1090 + difference 5 2) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1090 + difference 2 5) (sourceB1090 + difference 5 2) sourceC1090) = raw18196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18196; decide +kernel
    rw [ha]
    exact (canonical18196 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1090 + difference 3 0) (sourceB1090 + difference 0 3) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA1090 + difference 3 0) (sourceB1090 + difference 0 3) sourceC1090) = raw18197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18197; decide +kernel
    rw [ha]
    exact (canonical18197 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1090 + difference 3 1) (sourceB1090 + difference 1 3) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA1090 + difference 3 1) (sourceB1090 + difference 1 3) sourceC1090) = raw18198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18198; decide +kernel
    rw [ha]
    exact (canonical18198 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1090 + difference 3 2) (sourceB1090 + difference 2 3) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA1090 + difference 3 2) (sourceB1090 + difference 2 3) sourceC1090) = raw18199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18199; decide +kernel
    rw [ha]
    exact (canonical18199 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1090 + difference 3 4) (sourceB1090 + difference 4 3) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA1090 + difference 3 4) (sourceB1090 + difference 4 3) sourceC1090) = raw18200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18200; decide +kernel
    rw [ha]
    exact (canonical18200 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1090 + difference 3 5) (sourceB1090 + difference 5 3) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1090 + difference 3 5) (sourceB1090 + difference 5 3) sourceC1090) = raw18201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18201; decide +kernel
    rw [ha]
    exact (canonical18201 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1090 + difference 4 0) (sourceB1090 + difference 0 4) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA1090 + difference 4 0) (sourceB1090 + difference 0 4) sourceC1090) = raw18202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18202; decide +kernel
    rw [ha]
    exact (canonical18202 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1090 + difference 4 1) (sourceB1090 + difference 1 4) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA1090 + difference 4 1) (sourceB1090 + difference 1 4) sourceC1090) = raw18203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18203; decide +kernel
    rw [ha]
    exact (canonical18203 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1090 + difference 4 2) (sourceB1090 + difference 2 4) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA1090 + difference 4 2) (sourceB1090 + difference 2 4) sourceC1090) = raw18204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18204; decide +kernel
    rw [ha]
    exact (canonical18204 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1090 + difference 4 3) (sourceB1090 + difference 3 4) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5364) := by
    have ha : (tripleCharges (sourceA1090 + difference 4 3) (sourceB1090 + difference 3 4) sourceC1090) = raw18205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18205; decide +kernel
    rw [ha]
    exact (canonical18205 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1090 + difference 4 5) (sourceB1090 + difference 5 4) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1090 + difference 4 5) (sourceB1090 + difference 5 4) sourceC1090) = raw18206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18206; decide +kernel
    rw [ha]
    exact (canonical18206 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1090 + difference 5 0) (sourceB1090 + difference 0 5) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4800) := by
    have ha : (tripleCharges (sourceA1090 + difference 5 0) (sourceB1090 + difference 0 5) sourceC1090) = raw18207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18207; decide +kernel
    rw [ha]
    exact (canonical18207 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1090 + difference 5 1) (sourceB1090 + difference 1 5) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA1090 + difference 5 1) (sourceB1090 + difference 1 5) sourceC1090) = raw18208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18208; decide +kernel
    rw [ha]
    exact (canonical18208 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1090 + difference 5 2) (sourceB1090 + difference 2 5) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA1090 + difference 5 2) (sourceB1090 + difference 2 5) sourceC1090) = raw18209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18209; decide +kernel
    rw [ha]
    exact (canonical18209 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1090 + difference 5 3) (sourceB1090 + difference 3 5) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA1090 + difference 5 3) (sourceB1090 + difference 3 5) sourceC1090) = raw18210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18210; decide +kernel
    rw [ha]
    exact (canonical18210 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1090 + difference 5 4) (sourceB1090 + difference 4 5) sourceC1090) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA1090 + difference 5 4) (sourceB1090 + difference 4 5) sourceC1090) = raw18211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1090 sourceB1090 sourceC1090 difference raw18211; decide +kernel
    rw [ha]
    exact (canonical18211 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1090 sourceB1090 sourceC1090
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1090, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck934 : Integer.Sparse.reindex keyMap MixedData.row934 = numericRow934 := by decide +kernel

theorem numericCheck934 (x : Master → ℝ) : Integer.Sparse.eval numericRow934 x =
    (8640 : ℝ) * reducedSource934 x := by
  norm_num [numericRow934, reducedSource934, Integer.Sparse.eval, Sparse.eval, nodeValue4787, nodeValue4788, nodeValue4835, nodeValue4996, nodeValue5003, nodeValue5015, nodeValue5258, nodeValue5346, nodeValue5368, nodeValue5395, nodeValue5424, nodeValue5434, nodeValue5439, nodeValue5472, nodeValue5473, nodeValue5490]
  ring

theorem reindexCheck943 : Integer.Sparse.reindex keyMap MixedData.row943 = numericRow943 := by decide +kernel

theorem numericCheck943 (x : Master → ℝ) : Integer.Sparse.eval numericRow943 x =
    (25920 : ℝ) * reducedSource943 x := by
  norm_num [numericRow943, reducedSource943, Integer.Sparse.eval, Sparse.eval, nodeValue4798, nodeValue4800, nodeValue4810, nodeValue4828, nodeValue4865, nodeValue5349, nodeValue5355, nodeValue5364, nodeValue5378, nodeValue5387, nodeValue5400, nodeValue5431, nodeValue5432, nodeValue5435, nodeValue5438, nodeValue5450, nodeValue5490]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero934 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource934 (mixedVector B) = 0 := by
  have h4787 : mixedVector B (Sum.inr 4787) = Sparse.eval nodeValue4787 (mixedVector B) := by
    change mixedMoment B node4787 node4787Labels = _
    exact sound4787 B hB hF
  have h4788 : mixedVector B (Sum.inr 4788) = Sparse.eval nodeValue4788 (mixedVector B) := by
    change mixedMoment B node4788 node4788Labels = _
    exact sound4788 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4996 : mixedVector B (Sum.inr 4996) = Sparse.eval nodeValue4996 (mixedVector B) := by
    change mixedMoment B node4996 node4996Labels = _
    exact sound4996 B hB hF
  have h5003 : mixedVector B (Sum.inr 5003) = Sparse.eval nodeValue5003 (mixedVector B) := by
    change mixedMoment B node5003 node5003Labels = _
    exact sound5003 B hB hF
  have h5015 : mixedVector B (Sum.inr 5015) = Sparse.eval nodeValue5015 (mixedVector B) := by
    change mixedMoment B node5015 node5015Labels = _
    exact sound5015 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5346 : mixedVector B (Sum.inr 5346) = Sparse.eval nodeValue5346 (mixedVector B) := by
    change mixedMoment B node5346 node5346Labels = _
    exact sound5346 B hB hF
  have h5368 : mixedVector B (Sum.inr 5368) = Sparse.eval nodeValue5368 (mixedVector B) := by
    change mixedMoment B node5368 node5368Labels = _
    exact sound5368 B hB hF
  have h5395 : mixedVector B (Sum.inr 5395) = Sparse.eval nodeValue5395 (mixedVector B) := by
    change mixedMoment B node5395 node5395Labels = _
    exact sound5395 B hB hF
  have h5424 : mixedVector B (Sum.inr 5424) = Sparse.eval nodeValue5424 (mixedVector B) := by
    change mixedMoment B node5424 node5424Labels = _
    exact sound5424 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439_e B hB hF
  have h5472 : mixedVector B (Sum.inr 5472) = Sparse.eval nodeValue5472 (mixedVector B) := by
    change mixedMoment B node5472 node5472Labels = _
    exact sound5472 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490_e B hB hF
  simpa only [sourceForm1081, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4787, h4788, h4835, h4996, h5003, h5015, h5258, h5346, h5368, h5395, h5424, h5434, h5439, h5472, h5473, h5490, reducedSource934] using sourceEq1081 B hB

theorem rowSound934 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row934 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck934, numericCheck934, reducedZero934 B hB hF, mul_zero]

theorem reducedZero943 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource943 (mixedVector B) = 0 := by
  have h4798 : mixedVector B (Sum.inr 4798) = Sparse.eval nodeValue4798 (mixedVector B) := by
    change mixedMoment B node4798 node4798Labels = _
    exact sound4798 B hB hF
  have h4800 : mixedVector B (Sum.inr 4800) = Sparse.eval nodeValue4800 (mixedVector B) := by
    change mixedMoment B node4800 node4800Labels = _
    exact sound4800 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4828 : mixedVector B (Sum.inr 4828) = Sparse.eval nodeValue4828 (mixedVector B) := by
    change mixedMoment B node4828 node4828Labels = _
    exact sound4828 B hB hF
  have h4865 : mixedVector B (Sum.inr 4865) = Sparse.eval nodeValue4865 (mixedVector B) := by
    change mixedMoment B node4865 node4865Labels = _
    exact sound4865 B hB hF
  have h5349 : mixedVector B (Sum.inr 5349) = Sparse.eval nodeValue5349 (mixedVector B) := by
    change mixedMoment B node5349 node5349Labels = _
    exact sound5349 B hB hF
  have h5355 : mixedVector B (Sum.inr 5355) = Sparse.eval nodeValue5355 (mixedVector B) := by
    change mixedMoment B node5355 node5355Labels = _
    exact sound5355 B hB hF
  have h5364 : mixedVector B (Sum.inr 5364) = Sparse.eval nodeValue5364 (mixedVector B) := by
    change mixedMoment B node5364 node5364Labels = _
    exact sound5364 B hB hF
  have h5378 : mixedVector B (Sum.inr 5378) = Sparse.eval nodeValue5378 (mixedVector B) := by
    change mixedMoment B node5378 node5378Labels = _
    exact sound5378 B hB hF
  have h5387 : mixedVector B (Sum.inr 5387) = Sparse.eval nodeValue5387 (mixedVector B) := by
    change mixedMoment B node5387 node5387Labels = _
    exact sound5387_e B hB hF
  have h5400 : mixedVector B (Sum.inr 5400) = Sparse.eval nodeValue5400 (mixedVector B) := by
    change mixedMoment B node5400 node5400Labels = _
    exact sound5400 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5432 : mixedVector B (Sum.inr 5432) = Sparse.eval nodeValue5432 (mixedVector B) := by
    change mixedMoment B node5432 node5432Labels = _
    exact sound5432 B hB hF
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435_e B hB hF
  have h5438 : mixedVector B (Sum.inr 5438) = Sparse.eval nodeValue5438 (mixedVector B) := by
    change mixedMoment B node5438 node5438Labels = _
    exact sound5438 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450_e B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490_e B hB hF
  simpa only [sourceForm1090, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4798, h4800, h4810, h4828, h4865, h5349, h5355, h5364, h5378, h5387, h5400, h5431, h5432, h5435, h5438, h5450, h5490, reducedSource943] using sourceEq1090 B hB

theorem rowSound943 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row943 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck943, numericCheck943, reducedZero943 B hB hF, mul_zero]

theorem sourceRowsAt928 : MixedData.sourceRows (928 : Fin 2425) =
    MixedData.row928 := by decide +kernel

theorem sourceRowsAt929 : MixedData.sourceRows (929 : Fin 2425) =
    MixedData.row929 := by decide +kernel

theorem sourceRowsAt930 : MixedData.sourceRows (930 : Fin 2425) =
    MixedData.row930 := by decide +kernel

theorem sourceRowsAt931 : MixedData.sourceRows (931 : Fin 2425) =
    MixedData.row931 := by decide +kernel

theorem sourceRowsAt932 : MixedData.sourceRows (932 : Fin 2425) =
    MixedData.row932 := by decide +kernel

theorem sourceRowsAt933 : MixedData.sourceRows (933 : Fin 2425) =
    MixedData.row933 := by decide +kernel

theorem sourceRowsAt934 : MixedData.sourceRows (934 : Fin 2425) =
    MixedData.row934 := by decide +kernel

theorem sourceRowsAt935 : MixedData.sourceRows (935 : Fin 2425) =
    MixedData.row935 := by decide +kernel

theorem sourceRowsAt936 : MixedData.sourceRows (936 : Fin 2425) =
    MixedData.row936 := by decide +kernel

theorem sourceRowsAt937 : MixedData.sourceRows (937 : Fin 2425) =
    MixedData.row937 := by decide +kernel

theorem sourceRowsAt938 : MixedData.sourceRows (938 : Fin 2425) =
    MixedData.row938 := by decide +kernel

theorem sourceRowsAt939 : MixedData.sourceRows (939 : Fin 2425) =
    MixedData.row939 := by decide +kernel

theorem sourceRowsAt940 : MixedData.sourceRows (940 : Fin 2425) =
    MixedData.row940 := by decide +kernel

theorem sourceRowsAt941 : MixedData.sourceRows (941 : Fin 2425) =
    MixedData.row941 := by decide +kernel

theorem sourceRowsAt942 : MixedData.sourceRows (942 : Fin 2425) =
    MixedData.row942 := by decide +kernel

theorem sourceRowsAt943 : MixedData.sourceRows (943 : Fin 2425) =
    MixedData.row943 := by decide +kernel

theorem chunkSound58_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 58) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 928 ∨ k.val = 929 ∨ k.val = 930 ∨ k.val = 931 ∨ k.val = 932 ∨ k.val = 933 ∨ k.val = 934 ∨ k.val = 935 ∨ k.val = 936 ∨ k.val = 937 ∨ k.val = 938 ∨ k.val = 939 ∨ k.val = 940 ∨ k.val = 941 ∨ k.val = 942 ∨ k.val = 943 := by omega
  rcases heq with h928 | h929 | h930 | h931 | h932 | h933 | h934 | h935 | h936 | h937 | h938 | h939 | h940 | h941 | h942 | h943
  · have he : k = (928 : Fin 2425) := Fin.ext h928
    subst k
    rw [sourceRowsAt928]
    exact rowSound928_e B hB hF
  · have he : k = (929 : Fin 2425) := Fin.ext h929
    subst k
    rw [sourceRowsAt929]
    exact rowSound929_e B hB hF
  · have he : k = (930 : Fin 2425) := Fin.ext h930
    subst k
    rw [sourceRowsAt930]
    exact rowSound930_e B hB hF
  · have he : k = (931 : Fin 2425) := Fin.ext h931
    subst k
    rw [sourceRowsAt931]
    exact rowSound931_e B hB hF
  · have he : k = (932 : Fin 2425) := Fin.ext h932
    subst k
    rw [sourceRowsAt932]
    exact rowSound932_e B hB hF
  · have he : k = (933 : Fin 2425) := Fin.ext h933
    subst k
    rw [sourceRowsAt933]
    exact rowSound933_e B hB hF
  · have he : k = (934 : Fin 2425) := Fin.ext h934
    subst k
    rw [sourceRowsAt934]
    exact rowSound934 B hB hF
  · have he : k = (935 : Fin 2425) := Fin.ext h935
    subst k
    rw [sourceRowsAt935]
    exact rowSound935_e B hB hF
  · have he : k = (936 : Fin 2425) := Fin.ext h936
    subst k
    rw [sourceRowsAt936]
    exact rowSound936_e B hB hF
  · have he : k = (937 : Fin 2425) := Fin.ext h937
    subst k
    rw [sourceRowsAt937]
    exact rowSound937_e B hB hF
  · have he : k = (938 : Fin 2425) := Fin.ext h938
    subst k
    rw [sourceRowsAt938]
    exact rowSound938_e B hB hF
  · have he : k = (939 : Fin 2425) := Fin.ext h939
    subst k
    rw [sourceRowsAt939]
    exact rowSound939_e B hB hF
  · have he : k = (940 : Fin 2425) := Fin.ext h940
    subst k
    rw [sourceRowsAt940]
    exact rowSound940_e B hB hF
  · have he : k = (941 : Fin 2425) := Fin.ext h941
    subst k
    rw [sourceRowsAt941]
    exact rowSound941_e B hB hF
  · have he : k = (942 : Fin 2425) := Fin.ext h942
    subst k
    rw [sourceRowsAt942]
    exact rowSound942_e B hB hF
  · have he : k = (943 : Fin 2425) := Fin.ext h943
    subst k
    rw [sourceRowsAt943]
    exact rowSound943 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58_e_oai
