-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:41:22.494658+00:00
-- url     : https://prove2.me/submissions/750c3bfd-a7bf-4526-8005-f326544f4d69

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5168_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5169_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_reducedZero1909_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1904_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1905_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1906_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1907_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1908_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1910_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1911_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1912_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1914_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1915_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1916_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1917_e

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

theorem canonical1770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1770 raw1770Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw1770 raw1770Labels = mixedMoment B raw1770step0 raw1770step0Labels := by
      have ha : raw1770step0 = (fun i j => raw1770 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1770step0 raw1770; decide +kernel
      have hl : raw1770step0Labels = raw1770Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1770 raw1770Labels permutation32 permutation4
    mixedMoment B raw1770step0 raw1770step0Labels = mixedMoment B raw1770step1 raw1770step1Labels := by
      have ha : raw1770step1 = raw1770step0 := by apply Matrix.ext; unfold raw1770step1 raw1770step0; decide +kernel
      have hl : raw1770step0Labels = labelEmbedding7 ∘ raw1770step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1770step0 raw1770step0Labels raw1770step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

theorem canonical1771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1771 raw1771Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw1771 raw1771Labels = mixedMoment B raw1771step0 raw1771step0Labels := by
      have ha : raw1771step0 = (fun i j => raw1771 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1771step0 raw1771; decide +kernel
      have hl : raw1771step0Labels = raw1771Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1771 raw1771Labels permutation32 permutation4
    _ = mixedMoment B node2058 node2058Labels := by rfl

theorem canonical1772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1772 raw1772Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw1772 raw1772Labels = mixedMoment B raw1772step0 raw1772step0Labels := by
      have ha : raw1772step0 = (fun i j => raw1772 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1772step0 raw1772; decide +kernel
      have hl : raw1772step0Labels = raw1772Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1772 raw1772Labels permutation36 permutation6
    mixedMoment B raw1772step0 raw1772step0Labels = mixedMoment B raw1772step1 raw1772step1Labels := by
      have ha : raw1772step1 = -raw1772step0 := by apply Matrix.ext; change ∀ i j, raw1772step1 i j = -(raw1772step0 i j); unfold raw1772step1 raw1772step0; decide +kernel
      have hl : raw1772step1Labels = raw1772step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1772step1 raw1772step1Labels = mixedMoment B raw1772step2 raw1772step2Labels := by
      have ha : raw1772step2 = raw1772step1 := by apply Matrix.ext; unfold raw1772step2 raw1772step1; decide +kernel
      have hl : raw1772step1Labels = labelEmbedding1 ∘ raw1772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1772step1 raw1772step1Labels raw1772step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

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

theorem canonical1800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1800 raw1800Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw1800 raw1800Labels = mixedMoment B raw1800step0 raw1800step0Labels := by
      have ha : raw1800step0 = (fun i j => raw1800 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1800step0 raw1800; decide +kernel
      have hl : raw1800step0Labels = raw1800Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1800 raw1800Labels permutation32 permutation4
    mixedMoment B raw1800step0 raw1800step0Labels = mixedMoment B raw1800step1 raw1800step1Labels := by
      have ha : raw1800step1 = raw1800step0 := by apply Matrix.ext; unfold raw1800step1 raw1800step0; decide +kernel
      have hl : raw1800step0Labels = labelEmbedding7 ∘ raw1800step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1800step0 raw1800step0Labels raw1800step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical1801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1801 raw1801Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw1801 raw1801Labels = mixedMoment B raw1801step0 raw1801step0Labels := by
      have ha : raw1801step0 = (fun i j => raw1801 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1801step0 raw1801; decide +kernel
      have hl : raw1801step0Labels = raw1801Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1801 raw1801Labels permutation32 permutation4
    _ = mixedMoment B node2110 node2110Labels := by rfl

theorem canonical1802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1802 raw1802Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw1802 raw1802Labels = mixedMoment B raw1802step0 raw1802step0Labels := by
      have ha : raw1802step0 = (fun i j => raw1802 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1802step0 raw1802; decide +kernel
      have hl : raw1802step0Labels = raw1802Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1802 raw1802Labels permutation50 permutation6
    mixedMoment B raw1802step0 raw1802step0Labels = mixedMoment B raw1802step1 raw1802step1Labels := by
      have ha : raw1802step1 = -raw1802step0 := by apply Matrix.ext; change ∀ i j, raw1802step1 i j = -(raw1802step0 i j); unfold raw1802step1 raw1802step0; decide +kernel
      have hl : raw1802step1Labels = raw1802step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1802step1 raw1802step1Labels = mixedMoment B raw1802step2 raw1802step2Labels := by
      have ha : raw1802step2 = raw1802step1 := by apply Matrix.ext; unfold raw1802step2 raw1802step1; decide +kernel
      have hl : raw1802step1Labels = labelEmbedding1 ∘ raw1802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1802step1 raw1802step1Labels raw1802step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2275 node2275Labels := by rfl

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

theorem canonical2091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2091 raw2091Labels = mixedMoment B node5072 node5072Labels := by
  calc
    mixedMoment B raw2091 raw2091Labels = mixedMoment B raw2091step0 raw2091step0Labels := by
      have ha : raw2091step0 = (fun i j => raw2091 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2091step0 raw2091; decide +kernel
      have hl : raw2091step0Labels = raw2091Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2091 raw2091Labels permutation152 permutation4
    mixedMoment B raw2091step0 raw2091step0Labels = mixedMoment B raw2091step1 raw2091step1Labels := by
      have ha : raw2091step1 = raw2091step0 := by apply Matrix.ext; unfold raw2091step1 raw2091step0; decide +kernel
      have hl : raw2091step0Labels = labelEmbedding7 ∘ raw2091step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2091step0 raw2091step0Labels raw2091step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5072 node5072Labels := by rfl

theorem canonical2092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2092 raw2092Labels = mixedMoment B node2479 node2479Labels := by
  calc
    mixedMoment B raw2092 raw2092Labels = mixedMoment B raw2092step0 raw2092step0Labels := by
      have ha : raw2092step0 = (fun i j => raw2092 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2092step0 raw2092; decide +kernel
      have hl : raw2092step0Labels = raw2092Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2092 raw2092Labels permutation152 permutation4
    _ = mixedMoment B node2479 node2479Labels := by rfl

theorem canonical2093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2093 raw2093Labels = mixedMoment B node3459 node3459Labels := by
  calc
    mixedMoment B raw2093 raw2093Labels = mixedMoment B raw2093step0 raw2093step0Labels := by
      have ha : raw2093step0 = (fun i j => raw2093 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2093step0 raw2093; decide +kernel
      have hl : raw2093step0Labels = raw2093Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2093 raw2093Labels permutation160 permutation6
    mixedMoment B raw2093step0 raw2093step0Labels = mixedMoment B raw2093step1 raw2093step1Labels := by
      have ha : raw2093step1 = -raw2093step0 := by apply Matrix.ext; change ∀ i j, raw2093step1 i j = -(raw2093step0 i j); unfold raw2093step1 raw2093step0; decide +kernel
      have hl : raw2093step1Labels = raw2093step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2093step1 raw2093step1Labels = mixedMoment B raw2093step2 raw2093step2Labels := by
      have ha : raw2093step2 = raw2093step1 := by apply Matrix.ext; unfold raw2093step2 raw2093step1; decide +kernel
      have hl : raw2093step1Labels = labelEmbedding1 ∘ raw2093step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2093step1 raw2093step1Labels raw2093step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3459 node3459Labels := by rfl

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

theorem canonical2124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2124 raw2124Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw2124 raw2124Labels = mixedMoment B raw2124step0 raw2124step0Labels := by
      have ha : raw2124step0 = (fun i j => raw2124 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2124step0 raw2124; decide +kernel
      have hl : raw2124step0Labels = raw2124Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2124 raw2124Labels permutation32 permutation4
    mixedMoment B raw2124step0 raw2124step0Labels = mixedMoment B raw2124step1 raw2124step1Labels := by
      have ha : raw2124step1 = raw2124step0 := by apply Matrix.ext; unfold raw2124step1 raw2124step0; decide +kernel
      have hl : raw2124step0Labels = labelEmbedding7 ∘ raw2124step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2124step0 raw2124step0Labels raw2124step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5099 node5099Labels := by rfl

theorem canonical2125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2125 raw2125Labels = mixedMoment B node2509 node2509Labels := by
  calc
    mixedMoment B raw2125 raw2125Labels = mixedMoment B raw2125step0 raw2125step0Labels := by
      have ha : raw2125step0 = (fun i j => raw2125 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2125step0 raw2125; decide +kernel
      have hl : raw2125step0Labels = raw2125Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2125 raw2125Labels permutation32 permutation4
    _ = mixedMoment B node2509 node2509Labels := by rfl

theorem canonical2126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2126 raw2126Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw2126 raw2126Labels = mixedMoment B raw2126step0 raw2126step0Labels := by
      have ha : raw2126step0 = (fun i j => raw2126 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2126step0 raw2126; decide +kernel
      have hl : raw2126step0Labels = raw2126Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2126 raw2126Labels permutation145 permutation6
    mixedMoment B raw2126step0 raw2126step0Labels = mixedMoment B raw2126step1 raw2126step1Labels := by
      have ha : raw2126step1 = raw2126step0 := by apply Matrix.ext; unfold raw2126step1 raw2126step0; decide +kernel
      have hl : raw2126step0Labels = labelEmbedding1 ∘ raw2126step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2126step0 raw2126step0Labels raw2126step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

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

theorem canonical2166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2166 raw2166Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw2166 raw2166Labels = mixedMoment B raw2166step0 raw2166step0Labels := by
      have ha : raw2166step0 = (fun i j => raw2166 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2166step0 raw2166; decide +kernel
      have hl : raw2166step0Labels = raw2166Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2166 raw2166Labels permutation152 permutation4
    mixedMoment B raw2166step0 raw2166step0Labels = mixedMoment B raw2166step1 raw2166step1Labels := by
      have ha : raw2166step1 = raw2166step0 := by apply Matrix.ext; unfold raw2166step1 raw2166step0; decide +kernel
      have hl : raw2166step0Labels = labelEmbedding7 ∘ raw2166step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2166step0 raw2166step0Labels raw2166step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5137 node5137Labels := by rfl

theorem canonical2167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2167 raw2167Labels = mixedMoment B node2556 node2556Labels := by
  calc
    mixedMoment B raw2167 raw2167Labels = mixedMoment B raw2167step0 raw2167step0Labels := by
      have ha : raw2167step0 = (fun i j => raw2167 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2167step0 raw2167; decide +kernel
      have hl : raw2167step0Labels = raw2167Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2167 raw2167Labels permutation152 permutation4
    _ = mixedMoment B node2556 node2556Labels := by rfl

theorem canonical2168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2168 raw2168Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw2168 raw2168Labels = mixedMoment B raw2168step0 raw2168step0Labels := by
      have ha : raw2168step0 = (fun i j => raw2168 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2168step0 raw2168; decide +kernel
      have hl : raw2168step0Labels = raw2168Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2168 raw2168Labels permutation176 permutation6
    mixedMoment B raw2168step0 raw2168step0Labels = mixedMoment B raw2168step1 raw2168step1Labels := by
      have ha : raw2168step1 = -raw2168step0 := by apply Matrix.ext; change ∀ i j, raw2168step1 i j = -(raw2168step0 i j); unfold raw2168step1 raw2168step0; decide +kernel
      have hl : raw2168step1Labels = raw2168step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2168step1 raw2168step1Labels = mixedMoment B raw2168step2 raw2168step2Labels := by
      have ha : raw2168step2 = raw2168step1 := by apply Matrix.ext; unfold raw2168step2 raw2168step1; decide +kernel
      have hl : raw2168step1Labels = labelEmbedding1 ∘ raw2168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2168step1 raw2168step1Labels raw2168step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

theorem canonical2175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2175 raw2175Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw2175 raw2175Labels = mixedMoment B raw2175step0 raw2175step0Labels := by
      have ha : raw2175step0 = (fun i j => raw2175 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2175step0 raw2175; decide +kernel
      have hl : raw2175step0Labels = raw2175Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2175 raw2175Labels permutation152 permutation5
    mixedMoment B raw2175step0 raw2175step0Labels = mixedMoment B raw2175step1 raw2175step1Labels := by
      have ha : raw2175step1 = raw2175step0 := by apply Matrix.ext; unfold raw2175step1 raw2175step0; decide +kernel
      have hl : raw2175step0Labels = labelEmbedding8 ∘ raw2175step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2175step0 raw2175step0Labels raw2175step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

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

theorem canonical2176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2176 raw2176Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw2176 raw2176Labels = mixedMoment B raw2176step0 raw2176step0Labels := by
      have ha : raw2176step0 = (fun i j => raw2176 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2176step0 raw2176; decide +kernel
      have hl : raw2176step0Labels = raw2176Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2176 raw2176Labels permutation154 permutation4
    _ = mixedMoment B node2924 node2924Labels := by rfl

theorem canonical2177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2177 raw2177Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw2177 raw2177Labels = mixedMoment B raw2177step0 raw2177step0Labels := by
      have ha : raw2177step0 = (fun i j => raw2177 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2177step0 raw2177; decide +kernel
      have hl : raw2177step0Labels = raw2177Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2177 raw2177Labels permutation162 permutation3
    mixedMoment B raw2177step0 raw2177step0Labels = mixedMoment B raw2177step1 raw2177step1Labels := by
      have ha : raw2177step1 = -raw2177step0 := by apply Matrix.ext; change ∀ i j, raw2177step1 i j = -(raw2177step0 i j); unfold raw2177step1 raw2177step0; decide +kernel
      have hl : raw2177step1Labels = raw2177step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2177step1 raw2177step1Labels = mixedMoment B raw2177step2 raw2177step2Labels := by
      have ha : raw2177step2 = raw2177step1 := by apply Matrix.ext; unfold raw2177step2 raw2177step1; decide +kernel
      have hl : raw2177step1Labels = labelEmbedding1 ∘ raw2177step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2177step1 raw2177step1Labels raw2177step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

theorem canonical2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2202 raw2202Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw2202 raw2202Labels = mixedMoment B raw2202step0 raw2202step0Labels := by
      have ha : raw2202step0 = (fun i j => raw2202 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2202step0 raw2202; decide +kernel
      have hl : raw2202step0Labels = raw2202Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2202 raw2202Labels permutation32 permutation5
    mixedMoment B raw2202step0 raw2202step0Labels = mixedMoment B raw2202step1 raw2202step1Labels := by
      have ha : raw2202step1 = raw2202step0 := by apply Matrix.ext; unfold raw2202step1 raw2202step0; decide +kernel
      have hl : raw2202step0Labels = labelEmbedding8 ∘ raw2202step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2202step0 raw2202step0Labels raw2202step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

theorem canonical2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2203 raw2203Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw2203 raw2203Labels = mixedMoment B raw2203step0 raw2203step0Labels := by
      have ha : raw2203step0 = (fun i j => raw2203 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2203step0 raw2203; decide +kernel
      have hl : raw2203step0Labels = raw2203Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2203 raw2203Labels permutation34 permutation4
    _ = mixedMoment B node2954 node2954Labels := by rfl

theorem canonical2204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2204 raw2204Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw2204 raw2204Labels = mixedMoment B raw2204step0 raw2204step0Labels := by
      have ha : raw2204step0 = (fun i j => raw2204 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2204step0 raw2204; decide +kernel
      have hl : raw2204step0Labels = raw2204Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2204 raw2204Labels permutation33 permutation3
    mixedMoment B raw2204step0 raw2204step0Labels = mixedMoment B raw2204step1 raw2204step1Labels := by
      have ha : raw2204step1 = -raw2204step0 := by apply Matrix.ext; change ∀ i j, raw2204step1 i j = -(raw2204step0 i j); unfold raw2204step1 raw2204step0; decide +kernel
      have hl : raw2204step1Labels = raw2204step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2204step1 raw2204step1Labels = mixedMoment B raw2204step2 raw2204step2Labels := by
      have ha : raw2204step2 = raw2204step1 := by apply Matrix.ext; unfold raw2204step2 raw2204step1; decide +kernel
      have hl : raw2204step1Labels = labelEmbedding1 ∘ raw2204step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2204step1 raw2204step1Labels raw2204step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

theorem canonical2232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2232 raw2232Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw2232 raw2232Labels = mixedMoment B raw2232step0 raw2232step0Labels := by
      have ha : raw2232step0 = (fun i j => raw2232 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2232step0 raw2232; decide +kernel
      have hl : raw2232step0Labels = raw2232Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2232 raw2232Labels permutation32 permutation5
    mixedMoment B raw2232step0 raw2232step0Labels = mixedMoment B raw2232step1 raw2232step1Labels := by
      have ha : raw2232step1 = raw2232step0 := by apply Matrix.ext; unfold raw2232step1 raw2232step0; decide +kernel
      have hl : raw2232step0Labels = labelEmbedding8 ∘ raw2232step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2232step0 raw2232step0Labels raw2232step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

theorem canonical2233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2233 raw2233Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw2233 raw2233Labels = mixedMoment B raw2233step0 raw2233step0Labels := by
      have ha : raw2233step0 = (fun i j => raw2233 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2233step0 raw2233; decide +kernel
      have hl : raw2233step0Labels = raw2233Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2233 raw2233Labels permutation34 permutation4
    _ = mixedMoment B node2881 node2881Labels := by rfl

theorem canonical2234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2234 raw2234Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw2234 raw2234Labels = mixedMoment B raw2234step0 raw2234step0Labels := by
      have ha : raw2234step0 = (fun i j => raw2234 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2234step0 raw2234; decide +kernel
      have hl : raw2234step0Labels = raw2234Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2234 raw2234Labels permutation42 permutation3
    mixedMoment B raw2234step0 raw2234step0Labels = mixedMoment B raw2234step1 raw2234step1Labels := by
      have ha : raw2234step1 = -raw2234step0 := by apply Matrix.ext; change ∀ i j, raw2234step1 i j = -(raw2234step0 i j); unfold raw2234step1 raw2234step0; decide +kernel
      have hl : raw2234step1Labels = raw2234step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2234step1 raw2234step1Labels = mixedMoment B raw2234step2 raw2234step2Labels := by
      have ha : raw2234step2 = raw2234step1 := by apply Matrix.ext; unfold raw2234step2 raw2234step1; decide +kernel
      have hl : raw2234step1Labels = labelEmbedding1 ∘ raw2234step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2234step1 raw2234step1Labels raw2234step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3624 node3624Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical251
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32154 raw32154Labels = mixedMoment B node3815 node3815Labels := by
  calc
    mixedMoment B raw32154 raw32154Labels = mixedMoment B raw32154step0 raw32154step0Labels := by
      have hz : ∀ j, raw32154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32154step0 = (fun i j => raw32154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32154step0 raw32154; decide +kernel
      have hl : raw32154step0Labels = raw32154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32154 raw32154Labels permutation346 hz
    mixedMoment B raw32154step0 raw32154step0Labels = mixedMoment B raw32154step1 raw32154step1Labels := by
      have ha : raw32154step1 = (fun i j => raw32154step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32154step1 raw32154step0; decide +kernel
      have hl : raw32154step1Labels = raw32154step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32154step0 raw32154step0Labels permutation144 permutation7
    mixedMoment B raw32154step1 raw32154step1Labels = mixedMoment B raw32154step2 raw32154step2Labels := by
      have ha : raw32154step2 = raw32154step1 := by apply Matrix.ext; unfold raw32154step2 raw32154step1; decide +kernel
      have hl : raw32154step1Labels = labelEmbedding1 ∘ raw32154step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32154step1 raw32154step1Labels raw32154step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3815 node3815Labels := by rfl

theorem canonical32155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32155 raw32155Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw32155 raw32155Labels = mixedMoment B raw32155step0 raw32155step0Labels := by
      have ha : raw32155step0 = (fun i j => raw32155 (permutation658 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32155step0 raw32155; decide +kernel
      have hl : raw32155step0Labels = raw32155Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32155 raw32155Labels permutation658 permutation7
    mixedMoment B raw32155step0 raw32155step0Labels = mixedMoment B raw32155step1 raw32155step1Labels := by
      have ha : raw32155step1 = raw32155step0 := by apply Matrix.ext; unfold raw32155step1 raw32155step0; decide +kernel
      have hl : raw32155step0Labels = labelEmbedding1 ∘ raw32155step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32155step0 raw32155step0Labels raw32155step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

theorem canonical32156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32156 raw32156Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw32156 raw32156Labels = mixedMoment B raw32156step0 raw32156step0Labels := by
      have hz : ∀ j, raw32156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32156step0 = (fun i j => raw32156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32156step0 raw32156; decide +kernel
      have hl : raw32156step0Labels = raw32156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32156 raw32156Labels permutation346 hz
    mixedMoment B raw32156step0 raw32156step0Labels = mixedMoment B raw32156step1 raw32156step1Labels := by
      have ha : raw32156step1 = (fun i j => raw32156step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32156step1 raw32156step0; decide +kernel
      have hl : raw32156step1Labels = raw32156step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32156step0 raw32156step0Labels permutation145 permutation7
    mixedMoment B raw32156step1 raw32156step1Labels = mixedMoment B raw32156step2 raw32156step2Labels := by
      have ha : raw32156step2 = raw32156step1 := by apply Matrix.ext; unfold raw32156step2 raw32156step1; decide +kernel
      have hl : raw32156step1Labels = labelEmbedding1 ∘ raw32156step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32156step1 raw32156step1Labels raw32156step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical32157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32157 raw32157Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw32157 raw32157Labels = mixedMoment B raw32157step0 raw32157step0Labels := by
      have hz : ∀ j, raw32157 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32157step0 = (fun i j => raw32157 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32157step0 raw32157; decide +kernel
      have hl : raw32157step0Labels = raw32157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32157 raw32157Labels permutation346 hz
    mixedMoment B raw32157step0 raw32157step0Labels = mixedMoment B raw32157step1 raw32157step1Labels := by
      have ha : raw32157step1 = (fun i j => raw32157step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32157step1 raw32157step0; decide +kernel
      have hl : raw32157step1Labels = raw32157step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32157step0 raw32157step0Labels permutation145 permutation7
    mixedMoment B raw32157step1 raw32157step1Labels = mixedMoment B raw32157step2 raw32157step2Labels := by
      have ha : raw32157step2 = raw32157step1 := by apply Matrix.ext; unfold raw32157step2 raw32157step1; decide +kernel
      have hl : raw32157step1Labels = labelEmbedding1 ∘ raw32157step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32157step1 raw32157step1Labels raw32157step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

theorem canonical32158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32158 raw32158Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw32158 raw32158Labels = mixedMoment B raw32158step0 raw32158step0Labels := by
      have hz : ∀ j, raw32158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32158step0 = (fun i j => raw32158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32158step0 raw32158; decide +kernel
      have hl : raw32158step0Labels = raw32158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32158 raw32158Labels permutation346 hz
    mixedMoment B raw32158step0 raw32158step0Labels = mixedMoment B raw32158step1 raw32158step1Labels := by
      have ha : raw32158step1 = (fun i j => raw32158step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32158step1 raw32158step0; decide +kernel
      have hl : raw32158step1Labels = raw32158step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32158step0 raw32158step0Labels permutation145 permutation7
    mixedMoment B raw32158step1 raw32158step1Labels = mixedMoment B raw32158step2 raw32158step2Labels := by
      have ha : raw32158step2 = raw32158step1 := by apply Matrix.ext; unfold raw32158step2 raw32158step1; decide +kernel
      have hl : raw32158step1Labels = labelEmbedding1 ∘ raw32158step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32158step1 raw32158step1Labels raw32158step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3983 node3983Labels := by rfl

theorem canonical32159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32159 raw32159Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw32159 raw32159Labels = mixedMoment B raw32159step0 raw32159step0Labels := by
      have hz : ∀ j, raw32159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32159step0 = (fun i j => raw32159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32159step0 raw32159; decide +kernel
      have hl : raw32159step0Labels = raw32159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32159 raw32159Labels permutation346 hz
    mixedMoment B raw32159step0 raw32159step0Labels = mixedMoment B raw32159step1 raw32159step1Labels := by
      have ha : raw32159step1 = (fun i j => raw32159step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32159step1 raw32159step0; decide +kernel
      have hl : raw32159step1Labels = raw32159step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32159step0 raw32159step0Labels permutation42 permutation5
    mixedMoment B raw32159step1 raw32159step1Labels = mixedMoment B raw32159step2 raw32159step2Labels := by
      have ha : raw32159step2 = -raw32159step1 := by apply Matrix.ext; change ∀ i j, raw32159step2 i j = -(raw32159step1 i j); unfold raw32159step2 raw32159step1; decide +kernel
      have hl : raw32159step2Labels = raw32159step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32159step2 raw32159step2Labels = mixedMoment B raw32159step3 raw32159step3Labels := by
      have ha : raw32159step3 = raw32159step2 := by apply Matrix.ext; unfold raw32159step3 raw32159step2; decide +kernel
      have hl : raw32159step2Labels = labelEmbedding1 ∘ raw32159step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32159step2 raw32159step2Labels raw32159step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

theorem canonical32160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32160 raw32160Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw32160 raw32160Labels = mixedMoment B raw32160step0 raw32160step0Labels := by
      have ha : raw32160step0 = (fun i j => raw32160 (permutation186 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32160step0 raw32160; decide +kernel
      have hl : raw32160step0Labels = raw32160Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32160 raw32160Labels permutation186 permutation5
    mixedMoment B raw32160step0 raw32160step0Labels = mixedMoment B raw32160step1 raw32160step1Labels := by
      have ha : raw32160step1 = -raw32160step0 := by apply Matrix.ext; change ∀ i j, raw32160step1 i j = -(raw32160step0 i j); unfold raw32160step1 raw32160step0; decide +kernel
      have hl : raw32160step1Labels = raw32160step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32160step1 raw32160step1Labels = mixedMoment B raw32160step2 raw32160step2Labels := by
      have ha : raw32160step2 = raw32160step1 := by apply Matrix.ext; unfold raw32160step2 raw32160step1; decide +kernel
      have hl : raw32160step1Labels = labelEmbedding1 ∘ raw32160step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32160step1 raw32160step1Labels raw32160step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

theorem canonical32161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32161 raw32161Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw32161 raw32161Labels = mixedMoment B raw32161step0 raw32161step0Labels := by
      have hz : ∀ j, raw32161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32161step0 = (fun i j => raw32161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32161step0 raw32161; decide +kernel
      have hl : raw32161step0Labels = raw32161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32161 raw32161Labels permutation346 hz
    mixedMoment B raw32161step0 raw32161step0Labels = mixedMoment B raw32161step1 raw32161step1Labels := by
      have ha : raw32161step1 = (fun i j => raw32161step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32161step1 raw32161step0; decide +kernel
      have hl : raw32161step1Labels = raw32161step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32161step0 raw32161step0Labels permutation42 permutation5
    mixedMoment B raw32161step1 raw32161step1Labels = mixedMoment B raw32161step2 raw32161step2Labels := by
      have ha : raw32161step2 = -raw32161step1 := by apply Matrix.ext; change ∀ i j, raw32161step2 i j = -(raw32161step1 i j); unfold raw32161step2 raw32161step1; decide +kernel
      have hl : raw32161step2Labels = raw32161step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32161step2 raw32161step2Labels = mixedMoment B raw32161step3 raw32161step3Labels := by
      have ha : raw32161step3 = raw32161step2 := by apply Matrix.ext; unfold raw32161step3 raw32161step2; decide +kernel
      have hl : raw32161step2Labels = labelEmbedding1 ∘ raw32161step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32161step2 raw32161step2Labels raw32161step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

theorem canonical32162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32162 raw32162Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw32162 raw32162Labels = mixedMoment B raw32162step0 raw32162step0Labels := by
      have hz : ∀ j, raw32162 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32162step0 = (fun i j => raw32162 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32162step0 raw32162; decide +kernel
      have hl : raw32162step0Labels = raw32162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32162 raw32162Labels permutation346 hz
    mixedMoment B raw32162step0 raw32162step0Labels = mixedMoment B raw32162step1 raw32162step1Labels := by
      have ha : raw32162step1 = (fun i j => raw32162step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32162step1 raw32162step0; decide +kernel
      have hl : raw32162step1Labels = raw32162step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32162step0 raw32162step0Labels permutation42 permutation5
    mixedMoment B raw32162step1 raw32162step1Labels = mixedMoment B raw32162step2 raw32162step2Labels := by
      have ha : raw32162step2 = -raw32162step1 := by apply Matrix.ext; change ∀ i j, raw32162step2 i j = -(raw32162step1 i j); unfold raw32162step2 raw32162step1; decide +kernel
      have hl : raw32162step2Labels = raw32162step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32162step2 raw32162step2Labels = mixedMoment B raw32162step3 raw32162step3Labels := by
      have ha : raw32162step3 = raw32162step2 := by apply Matrix.ext; unfold raw32162step3 raw32162step2; decide +kernel
      have hl : raw32162step2Labels = labelEmbedding1 ∘ raw32162step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32162step2 raw32162step2Labels raw32162step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

theorem canonical32163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32163 raw32163Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw32163 raw32163Labels = mixedMoment B raw32163step0 raw32163step0Labels := by
      have hz : ∀ j, raw32163 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32163step0 = (fun i j => raw32163 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32163step0 raw32163; decide +kernel
      have hl : raw32163step0Labels = raw32163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32163 raw32163Labels permutation346 hz
    mixedMoment B raw32163step0 raw32163step0Labels = mixedMoment B raw32163step1 raw32163step1Labels := by
      have ha : raw32163step1 = (fun i j => raw32163step0 (permutation52 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32163step1 raw32163step0; decide +kernel
      have hl : raw32163step1Labels = raw32163step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32163step0 raw32163step0Labels permutation52 permutation5
    mixedMoment B raw32163step1 raw32163step1Labels = mixedMoment B raw32163step2 raw32163step2Labels := by
      have ha : raw32163step2 = -raw32163step1 := by apply Matrix.ext; change ∀ i j, raw32163step2 i j = -(raw32163step1 i j); unfold raw32163step2 raw32163step1; decide +kernel
      have hl : raw32163step2Labels = raw32163step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32163step2 raw32163step2Labels = mixedMoment B raw32163step3 raw32163step3Labels := by
      have ha : raw32163step3 = raw32163step2 := by apply Matrix.ext; unfold raw32163step3 raw32163step2; decide +kernel
      have hl : raw32163step2Labels = labelEmbedding1 ∘ raw32163step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32163step2 raw32163step2Labels raw32163step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical32164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32164 raw32164Labels = mixedMoment B node1668 node1668Labels := by
  calc
    mixedMoment B raw32164 raw32164Labels = mixedMoment B raw32164step0 raw32164step0Labels := by
      have ha : raw32164step0 = (fun i j => raw32164 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32164step0 raw32164; decide +kernel
      have hl : raw32164step0Labels = raw32164Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32164 raw32164Labels permutation162 permutation5
    mixedMoment B raw32164step0 raw32164step0Labels = mixedMoment B raw32164step1 raw32164step1Labels := by
      have ha : raw32164step1 = -raw32164step0 := by apply Matrix.ext; change ∀ i j, raw32164step1 i j = -(raw32164step0 i j); unfold raw32164step1 raw32164step0; decide +kernel
      have hl : raw32164step1Labels = raw32164step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32164step1 raw32164step1Labels = mixedMoment B raw32164step2 raw32164step2Labels := by
      have ha : raw32164step2 = raw32164step1 := by apply Matrix.ext; unfold raw32164step2 raw32164step1; decide +kernel
      have hl : raw32164step1Labels = labelEmbedding1 ∘ raw32164step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32164step1 raw32164step1Labels raw32164step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1668 node1668Labels := by rfl

theorem canonical32165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32165 raw32165Labels = mixedMoment B node3407 node3407Labels := by
  calc
    mixedMoment B raw32165 raw32165Labels = mixedMoment B raw32165step0 raw32165step0Labels := by
      have ha : raw32165step0 = (fun i j => raw32165 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32165step0 raw32165; decide +kernel
      have hl : raw32165step0Labels = raw32165Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32165 raw32165Labels permutation162 permutation5
    mixedMoment B raw32165step0 raw32165step0Labels = mixedMoment B raw32165step1 raw32165step1Labels := by
      have ha : raw32165step1 = -raw32165step0 := by apply Matrix.ext; change ∀ i j, raw32165step1 i j = -(raw32165step0 i j); unfold raw32165step1 raw32165step0; decide +kernel
      have hl : raw32165step1Labels = raw32165step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32165step1 raw32165step1Labels = mixedMoment B raw32165step2 raw32165step2Labels := by
      have ha : raw32165step2 = raw32165step1 := by apply Matrix.ext; unfold raw32165step2 raw32165step1; decide +kernel
      have hl : raw32165step1Labels = labelEmbedding1 ∘ raw32165step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32165step1 raw32165step1Labels raw32165step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3407 node3407Labels := by rfl

theorem canonical32166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32166 raw32166Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw32166 raw32166Labels = mixedMoment B raw32166step0 raw32166step0Labels := by
      have ha : raw32166step0 = (fun i j => raw32166 (permutation204 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32166step0 raw32166; decide +kernel
      have hl : raw32166step0Labels = raw32166Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32166 raw32166Labels permutation204 permutation5
    mixedMoment B raw32166step0 raw32166step0Labels = mixedMoment B raw32166step1 raw32166step1Labels := by
      have ha : raw32166step1 = -raw32166step0 := by apply Matrix.ext; change ∀ i j, raw32166step1 i j = -(raw32166step0 i j); unfold raw32166step1 raw32166step0; decide +kernel
      have hl : raw32166step1Labels = raw32166step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32166step1 raw32166step1Labels = mixedMoment B raw32166step2 raw32166step2Labels := by
      have ha : raw32166step2 = raw32166step1 := by apply Matrix.ext; unfold raw32166step2 raw32166step1; decide +kernel
      have hl : raw32166step1Labels = labelEmbedding1 ∘ raw32166step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32166step1 raw32166step1Labels raw32166step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

theorem canonical32167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32167 raw32167Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw32167 raw32167Labels = mixedMoment B raw32167step0 raw32167step0Labels := by
      have ha : raw32167step0 = (fun i j => raw32167 (permutation163 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32167step0 raw32167; decide +kernel
      have hl : raw32167step0Labels = raw32167Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32167 raw32167Labels permutation163 permutation5
    mixedMoment B raw32167step0 raw32167step0Labels = mixedMoment B raw32167step1 raw32167step1Labels := by
      have ha : raw32167step1 = -raw32167step0 := by apply Matrix.ext; change ∀ i j, raw32167step1 i j = -(raw32167step0 i j); unfold raw32167step1 raw32167step0; decide +kernel
      have hl : raw32167step1Labels = raw32167step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32167step1 raw32167step1Labels = mixedMoment B raw32167step2 raw32167step2Labels := by
      have ha : raw32167step2 = raw32167step1 := by apply Matrix.ext; unfold raw32167step2 raw32167step1; decide +kernel
      have hl : raw32167step1Labels = labelEmbedding1 ∘ raw32167step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32167step1 raw32167step1Labels raw32167step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

theorem canonical32168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32168 raw32168Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw32168 raw32168Labels = mixedMoment B raw32168step0 raw32168step0Labels := by
      have ha : raw32168step0 = (fun i j => raw32168 (permutation248 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32168step0 raw32168; decide +kernel
      have hl : raw32168step0Labels = raw32168Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32168 raw32168Labels permutation248 permutation5
    mixedMoment B raw32168step0 raw32168step0Labels = mixedMoment B raw32168step1 raw32168step1Labels := by
      have ha : raw32168step1 = -raw32168step0 := by apply Matrix.ext; change ∀ i j, raw32168step1 i j = -(raw32168step0 i j); unfold raw32168step1 raw32168step0; decide +kernel
      have hl : raw32168step1Labels = raw32168step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32168step1 raw32168step1Labels = mixedMoment B raw32168step2 raw32168step2Labels := by
      have ha : raw32168step2 = raw32168step1 := by apply Matrix.ext; unfold raw32168step2 raw32168step1; decide +kernel
      have hl : raw32168step1Labels = labelEmbedding1 ∘ raw32168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32168step1 raw32168step1Labels raw32168step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

theorem canonical32169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32169 raw32169Labels = mixedMoment B node1682 node1682Labels := by
  calc
    mixedMoment B raw32169 raw32169Labels = mixedMoment B raw32169step0 raw32169step0Labels := by
      have hz : ∀ j, raw32169 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32169step0 = (fun i j => raw32169 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32169step0 raw32169; decide +kernel
      have hl : raw32169step0Labels = raw32169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32169 raw32169Labels permutation346 hz
    mixedMoment B raw32169step0 raw32169step0Labels = mixedMoment B raw32169step1 raw32169step1Labels := by
      have ha : raw32169step1 = (fun i j => raw32169step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32169step1 raw32169step0; decide +kernel
      have hl : raw32169step1Labels = raw32169step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32169step0 raw32169step0Labels permutation36 permutation5
    mixedMoment B raw32169step1 raw32169step1Labels = mixedMoment B raw32169step2 raw32169step2Labels := by
      have ha : raw32169step2 = -raw32169step1 := by apply Matrix.ext; change ∀ i j, raw32169step2 i j = -(raw32169step1 i j); unfold raw32169step2 raw32169step1; decide +kernel
      have hl : raw32169step2Labels = raw32169step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32169step2 raw32169step2Labels = mixedMoment B raw32169step3 raw32169step3Labels := by
      have ha : raw32169step3 = raw32169step2 := by apply Matrix.ext; unfold raw32169step3 raw32169step2; decide +kernel
      have hl : raw32169step2Labels = labelEmbedding1 ∘ raw32169step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32169step2 raw32169step2Labels raw32169step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1682 node1682Labels := by rfl

theorem canonical32170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32170 raw32170Labels = mixedMoment B node3418 node3418Labels := by
  calc
    mixedMoment B raw32170 raw32170Labels = mixedMoment B raw32170step0 raw32170step0Labels := by
      have hz : ∀ j, raw32170 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32170step0 = (fun i j => raw32170 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32170step0 raw32170; decide +kernel
      have hl : raw32170step0Labels = raw32170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32170 raw32170Labels permutation346 hz
    mixedMoment B raw32170step0 raw32170step0Labels = mixedMoment B raw32170step1 raw32170step1Labels := by
      have ha : raw32170step1 = (fun i j => raw32170step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32170step1 raw32170step0; decide +kernel
      have hl : raw32170step1Labels = raw32170step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32170step0 raw32170step0Labels permutation36 permutation5
    mixedMoment B raw32170step1 raw32170step1Labels = mixedMoment B raw32170step2 raw32170step2Labels := by
      have ha : raw32170step2 = -raw32170step1 := by apply Matrix.ext; change ∀ i j, raw32170step2 i j = -(raw32170step1 i j); unfold raw32170step2 raw32170step1; decide +kernel
      have hl : raw32170step2Labels = raw32170step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32170step2 raw32170step2Labels = mixedMoment B raw32170step3 raw32170step3Labels := by
      have ha : raw32170step3 = raw32170step2 := by apply Matrix.ext; unfold raw32170step3 raw32170step2; decide +kernel
      have hl : raw32170step2Labels = labelEmbedding1 ∘ raw32170step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32170step2 raw32170step2Labels raw32170step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3418 node3418Labels := by rfl

theorem canonical32171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32171 raw32171Labels = mixedMoment B node3454 node3454Labels := by
  calc
    mixedMoment B raw32171 raw32171Labels = mixedMoment B raw32171step0 raw32171step0Labels := by
      have ha : raw32171step0 = (fun i j => raw32171 (permutation180 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32171step0 raw32171; decide +kernel
      have hl : raw32171step0Labels = raw32171Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32171 raw32171Labels permutation180 permutation5
    mixedMoment B raw32171step0 raw32171step0Labels = mixedMoment B raw32171step1 raw32171step1Labels := by
      have ha : raw32171step1 = -raw32171step0 := by apply Matrix.ext; change ∀ i j, raw32171step1 i j = -(raw32171step0 i j); unfold raw32171step1 raw32171step0; decide +kernel
      have hl : raw32171step1Labels = raw32171step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32171step1 raw32171step1Labels = mixedMoment B raw32171step2 raw32171step2Labels := by
      have ha : raw32171step2 = raw32171step1 := by apply Matrix.ext; unfold raw32171step2 raw32171step1; decide +kernel
      have hl : raw32171step1Labels = labelEmbedding1 ∘ raw32171step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32171step1 raw32171step1Labels raw32171step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3454 node3454Labels := by rfl

theorem canonical32172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32172 raw32172Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw32172 raw32172Labels = mixedMoment B raw32172step0 raw32172step0Labels := by
      have hz : ∀ j, raw32172 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32172step0 = (fun i j => raw32172 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32172step0 raw32172; decide +kernel
      have hl : raw32172step0Labels = raw32172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32172 raw32172Labels permutation346 hz
    mixedMoment B raw32172step0 raw32172step0Labels = mixedMoment B raw32172step1 raw32172step1Labels := by
      have ha : raw32172step1 = (fun i j => raw32172step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32172step1 raw32172step0; decide +kernel
      have hl : raw32172step1Labels = raw32172step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32172step0 raw32172step0Labels permutation37 permutation5
    mixedMoment B raw32172step1 raw32172step1Labels = mixedMoment B raw32172step2 raw32172step2Labels := by
      have ha : raw32172step2 = -raw32172step1 := by apply Matrix.ext; change ∀ i j, raw32172step2 i j = -(raw32172step1 i j); unfold raw32172step2 raw32172step1; decide +kernel
      have hl : raw32172step2Labels = raw32172step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32172step2 raw32172step2Labels = mixedMoment B raw32172step3 raw32172step3Labels := by
      have ha : raw32172step3 = raw32172step2 := by apply Matrix.ext; unfold raw32172step3 raw32172step2; decide +kernel
      have hl : raw32172step2Labels = labelEmbedding1 ∘ raw32172step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32172step2 raw32172step2Labels raw32172step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

theorem canonical32173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32173 raw32173Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw32173 raw32173Labels = mixedMoment B raw32173step0 raw32173step0Labels := by
      have hz : ∀ j, raw32173 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32173step0 = (fun i j => raw32173 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32173step0 raw32173; decide +kernel
      have hl : raw32173step0Labels = raw32173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32173 raw32173Labels permutation346 hz
    mixedMoment B raw32173step0 raw32173step0Labels = mixedMoment B raw32173step1 raw32173step1Labels := by
      have ha : raw32173step1 = (fun i j => raw32173step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32173step1 raw32173step0; decide +kernel
      have hl : raw32173step1Labels = raw32173step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32173step0 raw32173step0Labels permutation50 permutation5
    mixedMoment B raw32173step1 raw32173step1Labels = mixedMoment B raw32173step2 raw32173step2Labels := by
      have ha : raw32173step2 = -raw32173step1 := by apply Matrix.ext; change ∀ i j, raw32173step2 i j = -(raw32173step1 i j); unfold raw32173step2 raw32173step1; decide +kernel
      have hl : raw32173step2Labels = raw32173step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32173step2 raw32173step2Labels = mixedMoment B raw32173step3 raw32173step3Labels := by
      have ha : raw32173step3 = raw32173step2 := by apply Matrix.ext; unfold raw32173step3 raw32173step2; decide +kernel
      have hl : raw32173step2Labels = labelEmbedding1 ∘ raw32173step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32173step2 raw32173step2Labels raw32173step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

theorem canonical32174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32174 raw32174Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw32174 raw32174Labels = mixedMoment B raw32174step0 raw32174step0Labels := by
      have hz : ∀ j, raw32174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32174step0 = (fun i j => raw32174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32174step0 raw32174; decide +kernel
      have hl : raw32174step0Labels = raw32174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32174 raw32174Labels permutation346 hz
    mixedMoment B raw32174step0 raw32174step0Labels = mixedMoment B raw32174step1 raw32174step1Labels := by
      have ha : raw32174step1 = (fun i j => raw32174step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32174step1 raw32174step0; decide +kernel
      have hl : raw32174step1Labels = raw32174step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32174step0 raw32174step0Labels permutation33 permutation5
    mixedMoment B raw32174step1 raw32174step1Labels = mixedMoment B raw32174step2 raw32174step2Labels := by
      have ha : raw32174step2 = -raw32174step1 := by apply Matrix.ext; change ∀ i j, raw32174step2 i j = -(raw32174step1 i j); unfold raw32174step2 raw32174step1; decide +kernel
      have hl : raw32174step2Labels = raw32174step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32174step2 raw32174step2Labels = mixedMoment B raw32174step3 raw32174step3Labels := by
      have ha : raw32174step3 = raw32174step2 := by apply Matrix.ext; unfold raw32174step3 raw32174step2; decide +kernel
      have hl : raw32174step2Labels = labelEmbedding1 ∘ raw32174step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32174step2 raw32174step2Labels raw32174step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

theorem canonical32175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32175 raw32175Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw32175 raw32175Labels = mixedMoment B raw32175step0 raw32175step0Labels := by
      have hz : ∀ j, raw32175 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32175step0 = (fun i j => raw32175 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32175step0 raw32175; decide +kernel
      have hl : raw32175step0Labels = raw32175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32175 raw32175Labels permutation346 hz
    mixedMoment B raw32175step0 raw32175step0Labels = mixedMoment B raw32175step1 raw32175step1Labels := by
      have ha : raw32175step1 = (fun i j => raw32175step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32175step1 raw32175step0; decide +kernel
      have hl : raw32175step1Labels = raw32175step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32175step0 raw32175step0Labels permutation127 permutation5
    mixedMoment B raw32175step1 raw32175step1Labels = mixedMoment B raw32175step2 raw32175step2Labels := by
      have ha : raw32175step2 = raw32175step1 := by apply Matrix.ext; unfold raw32175step2 raw32175step1; decide +kernel
      have hl : raw32175step1Labels = labelEmbedding1 ∘ raw32175step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32175step1 raw32175step1Labels raw32175step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

theorem canonical32176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32176 raw32176Labels = mixedMoment B node2652 node2652Labels := by
  calc
    mixedMoment B raw32176 raw32176Labels = mixedMoment B raw32176step0 raw32176step0Labels := by
      have ha : raw32176step0 = (fun i j => raw32176 (permutation587 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32176step0 raw32176; decide +kernel
      have hl : raw32176step0Labels = raw32176Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32176 raw32176Labels permutation587 permutation5
    mixedMoment B raw32176step0 raw32176step0Labels = mixedMoment B raw32176step1 raw32176step1Labels := by
      have ha : raw32176step1 = raw32176step0 := by apply Matrix.ext; unfold raw32176step1 raw32176step0; decide +kernel
      have hl : raw32176step0Labels = labelEmbedding1 ∘ raw32176step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32176step0 raw32176step0Labels raw32176step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2652 node2652Labels := by rfl

theorem canonical32177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32177 raw32177Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw32177 raw32177Labels = mixedMoment B raw32177step0 raw32177step0Labels := by
      have hz : ∀ j, raw32177 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32177step0 = (fun i j => raw32177 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32177step0 raw32177; decide +kernel
      have hl : raw32177step0Labels = raw32177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32177 raw32177Labels permutation346 hz
    mixedMoment B raw32177step0 raw32177step0Labels = mixedMoment B raw32177step1 raw32177step1Labels := by
      have ha : raw32177step1 = (fun i j => raw32177step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32177step1 raw32177step0; decide +kernel
      have hl : raw32177step1Labels = raw32177step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32177step0 raw32177step0Labels permutation125 permutation5
    mixedMoment B raw32177step1 raw32177step1Labels = mixedMoment B raw32177step2 raw32177step2Labels := by
      have ha : raw32177step2 = raw32177step1 := by apply Matrix.ext; unfold raw32177step2 raw32177step1; decide +kernel
      have hl : raw32177step1Labels = labelEmbedding1 ∘ raw32177step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32177step1 raw32177step1Labels raw32177step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

theorem canonical32178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32178 raw32178Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw32178 raw32178Labels = mixedMoment B raw32178step0 raw32178step0Labels := by
      have hz : ∀ j, raw32178 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32178step0 = (fun i j => raw32178 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32178step0 raw32178; decide +kernel
      have hl : raw32178step0Labels = raw32178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32178 raw32178Labels permutation346 hz
    mixedMoment B raw32178step0 raw32178step0Labels = mixedMoment B raw32178step1 raw32178step1Labels := by
      have ha : raw32178step1 = (fun i j => raw32178step0 (permutation119 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32178step1 raw32178step0; decide +kernel
      have hl : raw32178step1Labels = raw32178step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32178step0 raw32178step0Labels permutation119 permutation5
    mixedMoment B raw32178step1 raw32178step1Labels = mixedMoment B raw32178step2 raw32178step2Labels := by
      have ha : raw32178step2 = raw32178step1 := by apply Matrix.ext; unfold raw32178step2 raw32178step1; decide +kernel
      have hl : raw32178step1Labels = labelEmbedding1 ∘ raw32178step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32178step1 raw32178step1Labels raw32178step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

theorem canonical32179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32179 raw32179Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw32179 raw32179Labels = mixedMoment B raw32179step0 raw32179step0Labels := by
      have hz : ∀ j, raw32179 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32179step0 = (fun i j => raw32179 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32179step0 raw32179; decide +kernel
      have hl : raw32179step0Labels = raw32179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32179 raw32179Labels permutation346 hz
    mixedMoment B raw32179step0 raw32179step0Labels = mixedMoment B raw32179step1 raw32179step1Labels := by
      have ha : raw32179step1 = (fun i j => raw32179step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32179step1 raw32179step0; decide +kernel
      have hl : raw32179step1Labels = raw32179step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32179step0 raw32179step0Labels permutation33 permutation5
    mixedMoment B raw32179step1 raw32179step1Labels = mixedMoment B raw32179step2 raw32179step2Labels := by
      have ha : raw32179step2 = -raw32179step1 := by apply Matrix.ext; change ∀ i j, raw32179step2 i j = -(raw32179step1 i j); unfold raw32179step2 raw32179step1; decide +kernel
      have hl : raw32179step2Labels = raw32179step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32179step2 raw32179step2Labels = mixedMoment B raw32179step3 raw32179step3Labels := by
      have ha : raw32179step3 = raw32179step2 := by apply Matrix.ext; unfold raw32179step3 raw32179step2; decide +kernel
      have hl : raw32179step2Labels = labelEmbedding1 ∘ raw32179step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32179step2 raw32179step2Labels raw32179step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

theorem canonical32180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32180 raw32180Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw32180 raw32180Labels = mixedMoment B raw32180step0 raw32180step0Labels := by
      have hz : ∀ j, raw32180 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32180step0 = (fun i j => raw32180 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32180step0 raw32180; decide +kernel
      have hl : raw32180step0Labels = raw32180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32180 raw32180Labels permutation346 hz
    mixedMoment B raw32180step0 raw32180step0Labels = mixedMoment B raw32180step1 raw32180step1Labels := by
      have ha : raw32180step1 = (fun i j => raw32180step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32180step1 raw32180step0; decide +kernel
      have hl : raw32180step1Labels = raw32180step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32180step0 raw32180step0Labels permutation33 permutation5
    mixedMoment B raw32180step1 raw32180step1Labels = mixedMoment B raw32180step2 raw32180step2Labels := by
      have ha : raw32180step2 = -raw32180step1 := by apply Matrix.ext; change ∀ i j, raw32180step2 i j = -(raw32180step1 i j); unfold raw32180step2 raw32180step1; decide +kernel
      have hl : raw32180step2Labels = raw32180step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32180step2 raw32180step2Labels = mixedMoment B raw32180step3 raw32180step3Labels := by
      have ha : raw32180step3 = raw32180step2 := by apply Matrix.ext; unfold raw32180step3 raw32180step2; decide +kernel
      have hl : raw32180step2Labels = labelEmbedding1 ∘ raw32180step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32180step2 raw32180step2Labels raw32180step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

theorem canonical32181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32181 raw32181Labels = mixedMoment B node3451 node3451Labels := by
  calc
    mixedMoment B raw32181 raw32181Labels = mixedMoment B raw32181step0 raw32181step0Labels := by
      have ha : raw32181step0 = (fun i j => raw32181 (permutation177 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32181step0 raw32181; decide +kernel
      have hl : raw32181step0Labels = raw32181Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32181 raw32181Labels permutation177 permutation5
    mixedMoment B raw32181step0 raw32181step0Labels = mixedMoment B raw32181step1 raw32181step1Labels := by
      have ha : raw32181step1 = -raw32181step0 := by apply Matrix.ext; change ∀ i j, raw32181step1 i j = -(raw32181step0 i j); unfold raw32181step1 raw32181step0; decide +kernel
      have hl : raw32181step1Labels = raw32181step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32181step1 raw32181step1Labels = mixedMoment B raw32181step2 raw32181step2Labels := by
      have ha : raw32181step2 = raw32181step1 := by apply Matrix.ext; unfold raw32181step2 raw32181step1; decide +kernel
      have hl : raw32181step1Labels = labelEmbedding1 ∘ raw32181step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32181step1 raw32181step1Labels raw32181step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3451 node3451Labels := by rfl

theorem canonical32182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32182 raw32182Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw32182 raw32182Labels = mixedMoment B raw32182step0 raw32182step0Labels := by
      have hz : ∀ j, raw32182 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32182step0 = (fun i j => raw32182 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32182step0 raw32182; decide +kernel
      have hl : raw32182step0Labels = raw32182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32182 raw32182Labels permutation346 hz
    mixedMoment B raw32182step0 raw32182step0Labels = mixedMoment B raw32182step1 raw32182step1Labels := by
      have ha : raw32182step1 = (fun i j => raw32182step0 (permutation39 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32182step1 raw32182step0; decide +kernel
      have hl : raw32182step1Labels = raw32182step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32182step0 raw32182step0Labels permutation39 permutation5
    mixedMoment B raw32182step1 raw32182step1Labels = mixedMoment B raw32182step2 raw32182step2Labels := by
      have ha : raw32182step2 = -raw32182step1 := by apply Matrix.ext; change ∀ i j, raw32182step2 i j = -(raw32182step1 i j); unfold raw32182step2 raw32182step1; decide +kernel
      have hl : raw32182step2Labels = raw32182step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32182step2 raw32182step2Labels = mixedMoment B raw32182step3 raw32182step3Labels := by
      have ha : raw32182step3 = raw32182step2 := by apply Matrix.ext; unfold raw32182step3 raw32182step2; decide +kernel
      have hl : raw32182step2Labels = labelEmbedding1 ∘ raw32182step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32182step2 raw32182step2Labels raw32182step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

theorem canonical32183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32183 raw32183Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw32183 raw32183Labels = mixedMoment B raw32183step0 raw32183step0Labels := by
      have hz : ∀ j, raw32183 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32183step0 = (fun i j => raw32183 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32183step0 raw32183; decide +kernel
      have hl : raw32183step0Labels = raw32183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32183 raw32183Labels permutation346 hz
    mixedMoment B raw32183step0 raw32183step0Labels = mixedMoment B raw32183step1 raw32183step1Labels := by
      have ha : raw32183step1 = (fun i j => raw32183step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32183step1 raw32183step0; decide +kernel
      have hl : raw32183step1Labels = raw32183step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32183step0 raw32183step0Labels permutation145 permutation7
    mixedMoment B raw32183step1 raw32183step1Labels = mixedMoment B raw32183step2 raw32183step2Labels := by
      have ha : raw32183step2 = raw32183step1 := by apply Matrix.ext; unfold raw32183step2 raw32183step1; decide +kernel
      have hl : raw32183step1Labels = labelEmbedding1 ∘ raw32183step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32183step1 raw32183step1Labels raw32183step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

theorem canonical32225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32225 raw32225Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw32225 raw32225Labels = mixedMoment B raw32225step0 raw32225step0Labels := by
      have hz : ∀ j, raw32225 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32225step0 = (fun i j => raw32225 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32225step0 raw32225; decide +kernel
      have hl : raw32225step0Labels = raw32225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32225 raw32225Labels permutation346 hz
    mixedMoment B raw32225step0 raw32225step0Labels = mixedMoment B raw32225step1 raw32225step1Labels := by
      have ha : raw32225step1 = (fun i j => raw32225step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32225step1 raw32225step0; decide +kernel
      have hl : raw32225step1Labels = raw32225step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32225step0 raw32225step0Labels permutation32 permutation7
    mixedMoment B raw32225step1 raw32225step1Labels = mixedMoment B raw32225step2 raw32225step2Labels := by
      have ha : raw32225step2 = raw32225step1 := by apply Matrix.ext; unfold raw32225step2 raw32225step1; decide +kernel
      have hl : raw32225step1Labels = labelEmbedding10 ∘ raw32225step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32225step1 raw32225step1Labels raw32225step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5168 node5168Labels := by rfl

theorem canonical32226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32226 raw32226Labels = mixedMoment B node5072 node5072Labels := by
  calc
    mixedMoment B raw32226 raw32226Labels = mixedMoment B raw32226step0 raw32226step0Labels := by
      have ha : raw32226step0 = (fun i j => raw32226 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32226step0 raw32226; decide +kernel
      have hl : raw32226step0Labels = raw32226Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32226 raw32226Labels permutation152 permutation7
    mixedMoment B raw32226step0 raw32226step0Labels = mixedMoment B raw32226step1 raw32226step1Labels := by
      have ha : raw32226step1 = raw32226step0 := by apply Matrix.ext; unfold raw32226step1 raw32226step0; decide +kernel
      have hl : raw32226step0Labels = labelEmbedding10 ∘ raw32226step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32226step0 raw32226step0Labels raw32226step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5072 node5072Labels := by rfl

theorem canonical32227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32227 raw32227Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw32227 raw32227Labels = mixedMoment B raw32227step0 raw32227step0Labels := by
      have hz : ∀ j, raw32227 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32227step0 = (fun i j => raw32227 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32227step0 raw32227; decide +kernel
      have hl : raw32227step0Labels = raw32227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32227 raw32227Labels permutation346 hz
    mixedMoment B raw32227step0 raw32227step0Labels = mixedMoment B raw32227step1 raw32227step1Labels := by
      have ha : raw32227step1 = (fun i j => raw32227step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32227step1 raw32227step0; decide +kernel
      have hl : raw32227step1Labels = raw32227step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32227step0 raw32227step0Labels permutation34 permutation7
    mixedMoment B raw32227step1 raw32227step1Labels = mixedMoment B raw32227step2 raw32227step2Labels := by
      have ha : raw32227step2 = raw32227step1 := by apply Matrix.ext; unfold raw32227step2 raw32227step1; decide +kernel
      have hl : raw32227step1Labels = labelEmbedding10 ∘ raw32227step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32227step1 raw32227step1Labels raw32227step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5101 node5101Labels := by rfl

theorem canonical32228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32228 raw32228Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw32228 raw32228Labels = mixedMoment B raw32228step0 raw32228step0Labels := by
      have hz : ∀ j, raw32228 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32228step0 = (fun i j => raw32228 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32228step0 raw32228; decide +kernel
      have hl : raw32228step0Labels = raw32228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32228 raw32228Labels permutation346 hz
    mixedMoment B raw32228step0 raw32228step0Labels = mixedMoment B raw32228step1 raw32228step1Labels := by
      have ha : raw32228step1 = (fun i j => raw32228step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32228step1 raw32228step0; decide +kernel
      have hl : raw32228step1Labels = raw32228step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32228step0 raw32228step0Labels permutation32 permutation7
    mixedMoment B raw32228step1 raw32228step1Labels = mixedMoment B raw32228step2 raw32228step2Labels := by
      have ha : raw32228step2 = raw32228step1 := by apply Matrix.ext; unfold raw32228step2 raw32228step1; decide +kernel
      have hl : raw32228step1Labels = labelEmbedding10 ∘ raw32228step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32228step1 raw32228step1Labels raw32228step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5101 node5101Labels := by rfl

theorem canonical32229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32229 raw32229Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw32229 raw32229Labels = mixedMoment B raw32229step0 raw32229step0Labels := by
      have hz : ∀ j, raw32229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32229step0 = (fun i j => raw32229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32229step0 raw32229; decide +kernel
      have hl : raw32229step0Labels = raw32229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32229 raw32229Labels permutation346 hz
    mixedMoment B raw32229step0 raw32229step0Labels = mixedMoment B raw32229step1 raw32229step1Labels := by
      have ha : raw32229step1 = (fun i j => raw32229step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32229step1 raw32229step0; decide +kernel
      have hl : raw32229step1Labels = raw32229step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32229step0 raw32229step0Labels permutation32 permutation7
    mixedMoment B raw32229step1 raw32229step1Labels = mixedMoment B raw32229step2 raw32229step2Labels := by
      have ha : raw32229step2 = raw32229step1 := by apply Matrix.ext; unfold raw32229step2 raw32229step1; decide +kernel
      have hl : raw32229step1Labels = labelEmbedding10 ∘ raw32229step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32229step1 raw32229step1Labels raw32229step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5099 node5099Labels := by rfl

theorem canonical32230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32230 raw32230Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw32230 raw32230Labels = mixedMoment B raw32230step0 raw32230step0Labels := by
      have hz : ∀ j, raw32230 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32230step0 = (fun i j => raw32230 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32230step0 raw32230; decide +kernel
      have hl : raw32230step0Labels = raw32230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32230 raw32230Labels permutation346 hz
    mixedMoment B raw32230step0 raw32230step0Labels = mixedMoment B raw32230step1 raw32230step1Labels := by
      have ha : raw32230step1 = (fun i j => raw32230step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32230step1 raw32230step0; decide +kernel
      have hl : raw32230step1Labels = raw32230step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32230step0 raw32230step0Labels permutation32 permutation6
    mixedMoment B raw32230step1 raw32230step1Labels = mixedMoment B raw32230step2 raw32230step2Labels := by
      have ha : raw32230step2 = raw32230step1 := by apply Matrix.ext; unfold raw32230step2 raw32230step1; decide +kernel
      have hl : raw32230step1Labels = labelEmbedding9 ∘ raw32230step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32230step1 raw32230step1Labels raw32230step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

theorem canonical32231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32231 raw32231Labels = mixedMoment B node5187 node5187Labels := by
  calc
    mixedMoment B raw32231 raw32231Labels = mixedMoment B raw32231step0 raw32231step0Labels := by
      have ha : raw32231step0 = (fun i j => raw32231 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32231step0 raw32231; decide +kernel
      have hl : raw32231step0Labels = raw32231Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32231 raw32231Labels permutation152 permutation6
    mixedMoment B raw32231step0 raw32231step0Labels = mixedMoment B raw32231step1 raw32231step1Labels := by
      have ha : raw32231step1 = raw32231step0 := by apply Matrix.ext; unfold raw32231step1 raw32231step0; decide +kernel
      have hl : raw32231step0Labels = labelEmbedding9 ∘ raw32231step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32231step0 raw32231step0Labels raw32231step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5187 node5187Labels := by rfl

theorem canonical32232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32232 raw32232Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw32232 raw32232Labels = mixedMoment B raw32232step0 raw32232step0Labels := by
      have hz : ∀ j, raw32232 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32232step0 = (fun i j => raw32232 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32232step0 raw32232; decide +kernel
      have hl : raw32232step0Labels = raw32232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32232 raw32232Labels permutation346 hz
    mixedMoment B raw32232step0 raw32232step0Labels = mixedMoment B raw32232step1 raw32232step1Labels := by
      have ha : raw32232step1 = (fun i j => raw32232step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32232step1 raw32232step0; decide +kernel
      have hl : raw32232step1Labels = raw32232step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32232step0 raw32232step0Labels permutation32 permutation6
    mixedMoment B raw32232step1 raw32232step1Labels = mixedMoment B raw32232step2 raw32232step2Labels := by
      have ha : raw32232step2 = raw32232step1 := by apply Matrix.ext; unfold raw32232step2 raw32232step1; decide +kernel
      have hl : raw32232step1Labels = labelEmbedding9 ∘ raw32232step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32232step1 raw32232step1Labels raw32232step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

theorem canonical32233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32233 raw32233Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw32233 raw32233Labels = mixedMoment B raw32233step0 raw32233step0Labels := by
      have hz : ∀ j, raw32233 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32233step0 = (fun i j => raw32233 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32233step0 raw32233; decide +kernel
      have hl : raw32233step0Labels = raw32233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32233 raw32233Labels permutation346 hz
    mixedMoment B raw32233step0 raw32233step0Labels = mixedMoment B raw32233step1 raw32233step1Labels := by
      have ha : raw32233step1 = (fun i j => raw32233step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32233step1 raw32233step0; decide +kernel
      have hl : raw32233step1Labels = raw32233step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32233step0 raw32233step0Labels permutation34 permutation6
    mixedMoment B raw32233step1 raw32233step1Labels = mixedMoment B raw32233step2 raw32233step2Labels := by
      have ha : raw32233step2 = raw32233step1 := by apply Matrix.ext; unfold raw32233step2 raw32233step1; decide +kernel
      have hl : raw32233step1Labels = labelEmbedding9 ∘ raw32233step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32233step1 raw32233step1Labels raw32233step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

theorem canonical32234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32234 raw32234Labels = mixedMoment B node5205 node5205Labels := by
  calc
    mixedMoment B raw32234 raw32234Labels = mixedMoment B raw32234step0 raw32234step0Labels := by
      have hz : ∀ j, raw32234 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32234step0 = (fun i j => raw32234 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32234step0 raw32234; decide +kernel
      have hl : raw32234step0Labels = raw32234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32234 raw32234Labels permutation346 hz
    mixedMoment B raw32234step0 raw32234step0Labels = mixedMoment B raw32234step1 raw32234step1Labels := by
      have ha : raw32234step1 = (fun i j => raw32234step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32234step1 raw32234step0; decide +kernel
      have hl : raw32234step1Labels = raw32234step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32234step0 raw32234step0Labels permutation32 permutation6
    mixedMoment B raw32234step1 raw32234step1Labels = mixedMoment B raw32234step2 raw32234step2Labels := by
      have ha : raw32234step2 = raw32234step1 := by apply Matrix.ext; unfold raw32234step2 raw32234step1; decide +kernel
      have hl : raw32234step1Labels = labelEmbedding9 ∘ raw32234step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32234step1 raw32234step1Labels raw32234step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5205 node5205Labels := by rfl

theorem canonical32235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32235 raw32235Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw32235 raw32235Labels = mixedMoment B raw32235step0 raw32235step0Labels := by
      have ha : raw32235step0 = (fun i j => raw32235 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32235step0 raw32235; decide +kernel
      have hl : raw32235step0Labels = raw32235Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32235 raw32235Labels permutation152 permutation6
    mixedMoment B raw32235step0 raw32235step0Labels = mixedMoment B raw32235step1 raw32235step1Labels := by
      have ha : raw32235step1 = raw32235step0 := by apply Matrix.ext; unfold raw32235step1 raw32235step0; decide +kernel
      have hl : raw32235step0Labels = labelEmbedding9 ∘ raw32235step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32235step0 raw32235step0Labels raw32235step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical32236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32236 raw32236Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw32236 raw32236Labels = mixedMoment B raw32236step0 raw32236step0Labels := by
      have ha : raw32236step0 = (fun i j => raw32236 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32236step0 raw32236; decide +kernel
      have hl : raw32236step0Labels = raw32236Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32236 raw32236Labels permutation152 permutation6
    mixedMoment B raw32236step0 raw32236step0Labels = mixedMoment B raw32236step1 raw32236step1Labels := by
      have ha : raw32236step1 = raw32236step0 := by apply Matrix.ext; unfold raw32236step1 raw32236step0; decide +kernel
      have hl : raw32236step0Labels = labelEmbedding9 ∘ raw32236step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32236step0 raw32236step0Labels raw32236step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5076 node5076Labels := by rfl

theorem canonical32237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32237 raw32237Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw32237 raw32237Labels = mixedMoment B raw32237step0 raw32237step0Labels := by
      have ha : raw32237step0 = (fun i j => raw32237 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32237step0 raw32237; decide +kernel
      have hl : raw32237step0Labels = raw32237Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32237 raw32237Labels permutation152 permutation6
    mixedMoment B raw32237step0 raw32237step0Labels = mixedMoment B raw32237step1 raw32237step1Labels := by
      have ha : raw32237step1 = raw32237step0 := by apply Matrix.ext; unfold raw32237step1 raw32237step0; decide +kernel
      have hl : raw32237step0Labels = labelEmbedding9 ∘ raw32237step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32237step0 raw32237step0Labels raw32237step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

theorem canonical32238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32238 raw32238Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw32238 raw32238Labels = mixedMoment B raw32238step0 raw32238step0Labels := by
      have ha : raw32238step0 = (fun i j => raw32238 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32238step0 raw32238; decide +kernel
      have hl : raw32238step0Labels = raw32238Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32238 raw32238Labels permutation154 permutation6
    mixedMoment B raw32238step0 raw32238step0Labels = mixedMoment B raw32238step1 raw32238step1Labels := by
      have ha : raw32238step1 = raw32238step0 := by apply Matrix.ext; unfold raw32238step1 raw32238step0; decide +kernel
      have hl : raw32238step0Labels = labelEmbedding9 ∘ raw32238step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32238step0 raw32238step0Labels raw32238step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

theorem canonical32239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32239 raw32239Labels = mixedMoment B node5150 node5150Labels := by
  calc
    mixedMoment B raw32239 raw32239Labels = mixedMoment B raw32239step0 raw32239step0Labels := by
      have ha : raw32239step0 = (fun i j => raw32239 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32239step0 raw32239; decide +kernel
      have hl : raw32239step0Labels = raw32239Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32239 raw32239Labels permutation152 permutation6
    mixedMoment B raw32239step0 raw32239step0Labels = mixedMoment B raw32239step1 raw32239step1Labels := by
      have ha : raw32239step1 = raw32239step0 := by apply Matrix.ext; unfold raw32239step1 raw32239step0; decide +kernel
      have hl : raw32239step0Labels = labelEmbedding9 ∘ raw32239step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32239step0 raw32239step0Labels raw32239step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5150 node5150Labels := by rfl

theorem canonical32240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32240 raw32240Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw32240 raw32240Labels = mixedMoment B raw32240step0 raw32240step0Labels := by
      have hz : ∀ j, raw32240 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32240step0 = (fun i j => raw32240 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32240step0 raw32240; decide +kernel
      have hl : raw32240step0Labels = raw32240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32240 raw32240Labels permutation346 hz
    mixedMoment B raw32240step0 raw32240step0Labels = mixedMoment B raw32240step1 raw32240step1Labels := by
      have ha : raw32240step1 = (fun i j => raw32240step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32240step1 raw32240step0; decide +kernel
      have hl : raw32240step1Labels = raw32240step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32240step0 raw32240step0Labels permutation34 permutation6
    mixedMoment B raw32240step1 raw32240step1Labels = mixedMoment B raw32240step2 raw32240step2Labels := by
      have ha : raw32240step2 = raw32240step1 := by apply Matrix.ext; unfold raw32240step2 raw32240step1; decide +kernel
      have hl : raw32240step1Labels = labelEmbedding9 ∘ raw32240step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32240step1 raw32240step1Labels raw32240step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

theorem canonical32241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32241 raw32241Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw32241 raw32241Labels = mixedMoment B raw32241step0 raw32241step0Labels := by
      have hz : ∀ j, raw32241 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32241step0 = (fun i j => raw32241 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32241step0 raw32241; decide +kernel
      have hl : raw32241step0Labels = raw32241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32241 raw32241Labels permutation346 hz
    mixedMoment B raw32241step0 raw32241step0Labels = mixedMoment B raw32241step1 raw32241step1Labels := by
      have ha : raw32241step1 = (fun i j => raw32241step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32241step1 raw32241step0; decide +kernel
      have hl : raw32241step1Labels = raw32241step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32241step0 raw32241step0Labels permutation34 permutation6
    mixedMoment B raw32241step1 raw32241step1Labels = mixedMoment B raw32241step2 raw32241step2Labels := by
      have ha : raw32241step2 = raw32241step1 := by apply Matrix.ext; unfold raw32241step2 raw32241step1; decide +kernel
      have hl : raw32241step1Labels = labelEmbedding9 ∘ raw32241step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32241step1 raw32241step1Labels raw32241step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

theorem canonical32242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32242 raw32242Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw32242 raw32242Labels = mixedMoment B raw32242step0 raw32242step0Labels := by
      have ha : raw32242step0 = (fun i j => raw32242 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32242step0 raw32242; decide +kernel
      have hl : raw32242step0Labels = raw32242Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32242 raw32242Labels permutation154 permutation6
    mixedMoment B raw32242step0 raw32242step0Labels = mixedMoment B raw32242step1 raw32242step1Labels := by
      have ha : raw32242step1 = raw32242step0 := by apply Matrix.ext; unfold raw32242step1 raw32242step0; decide +kernel
      have hl : raw32242step0Labels = labelEmbedding9 ∘ raw32242step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32242step0 raw32242step0Labels raw32242step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

theorem canonical32243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32243 raw32243Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw32243 raw32243Labels = mixedMoment B raw32243step0 raw32243step0Labels := by
      have hz : ∀ j, raw32243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32243step0 = (fun i j => raw32243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32243step0 raw32243; decide +kernel
      have hl : raw32243step0Labels = raw32243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32243 raw32243Labels permutation346 hz
    mixedMoment B raw32243step0 raw32243step0Labels = mixedMoment B raw32243step1 raw32243step1Labels := by
      have ha : raw32243step1 = (fun i j => raw32243step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32243step1 raw32243step0; decide +kernel
      have hl : raw32243step1Labels = raw32243step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32243step0 raw32243step0Labels permutation34 permutation6
    mixedMoment B raw32243step1 raw32243step1Labels = mixedMoment B raw32243step2 raw32243step2Labels := by
      have ha : raw32243step2 = raw32243step1 := by apply Matrix.ext; unfold raw32243step2 raw32243step1; decide +kernel
      have hl : raw32243step1Labels = labelEmbedding9 ∘ raw32243step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32243step1 raw32243step1Labels raw32243step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

theorem canonical32244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32244 raw32244Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw32244 raw32244Labels = mixedMoment B raw32244step0 raw32244step0Labels := by
      have hz : ∀ j, raw32244 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32244step0 = (fun i j => raw32244 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32244step0 raw32244; decide +kernel
      have hl : raw32244step0Labels = raw32244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32244 raw32244Labels permutation346 hz
    mixedMoment B raw32244step0 raw32244step0Labels = mixedMoment B raw32244step1 raw32244step1Labels := by
      have ha : raw32244step1 = (fun i j => raw32244step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32244step1 raw32244step0; decide +kernel
      have hl : raw32244step1Labels = raw32244step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32244step0 raw32244step0Labels permutation34 permutation6
    mixedMoment B raw32244step1 raw32244step1Labels = mixedMoment B raw32244step2 raw32244step2Labels := by
      have ha : raw32244step2 = raw32244step1 := by apply Matrix.ext; unfold raw32244step2 raw32244step1; decide +kernel
      have hl : raw32244step1Labels = labelEmbedding9 ∘ raw32244step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32244step1 raw32244step1Labels raw32244step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

theorem canonical32245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32245 raw32245Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw32245 raw32245Labels = mixedMoment B raw32245step0 raw32245step0Labels := by
      have hz : ∀ j, raw32245 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32245step0 = (fun i j => raw32245 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32245step0 raw32245; decide +kernel
      have hl : raw32245step0Labels = raw32245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32245 raw32245Labels permutation346 hz
    mixedMoment B raw32245step0 raw32245step0Labels = mixedMoment B raw32245step1 raw32245step1Labels := by
      have ha : raw32245step1 = (fun i j => raw32245step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32245step1 raw32245step0; decide +kernel
      have hl : raw32245step1Labels = raw32245step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32245step0 raw32245step0Labels permutation32 permutation6
    mixedMoment B raw32245step1 raw32245step1Labels = mixedMoment B raw32245step2 raw32245step2Labels := by
      have ha : raw32245step2 = raw32245step1 := by apply Matrix.ext; unfold raw32245step2 raw32245step1; decide +kernel
      have hl : raw32245step1Labels = labelEmbedding9 ∘ raw32245step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32245step1 raw32245step1Labels raw32245step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

theorem canonical32246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32246 raw32246Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw32246 raw32246Labels = mixedMoment B raw32246step0 raw32246step0Labels := by
      have hz : ∀ j, raw32246 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32246step0 = (fun i j => raw32246 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32246step0 raw32246; decide +kernel
      have hl : raw32246step0Labels = raw32246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32246 raw32246Labels permutation346 hz
    mixedMoment B raw32246step0 raw32246step0Labels = mixedMoment B raw32246step1 raw32246step1Labels := by
      have ha : raw32246step1 = (fun i j => raw32246step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32246step1 raw32246step0; decide +kernel
      have hl : raw32246step1Labels = raw32246step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32246step0 raw32246step0Labels permutation32 permutation6
    mixedMoment B raw32246step1 raw32246step1Labels = mixedMoment B raw32246step2 raw32246step2Labels := by
      have ha : raw32246step2 = raw32246step1 := by apply Matrix.ext; unfold raw32246step2 raw32246step1; decide +kernel
      have hl : raw32246step1Labels = labelEmbedding9 ∘ raw32246step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32246step1 raw32246step1Labels raw32246step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

theorem canonical32247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32247 raw32247Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw32247 raw32247Labels = mixedMoment B raw32247step0 raw32247step0Labels := by
      have ha : raw32247step0 = (fun i j => raw32247 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32247step0 raw32247; decide +kernel
      have hl : raw32247step0Labels = raw32247Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32247 raw32247Labels permutation152 permutation6
    mixedMoment B raw32247step0 raw32247step0Labels = mixedMoment B raw32247step1 raw32247step1Labels := by
      have ha : raw32247step1 = raw32247step0 := by apply Matrix.ext; unfold raw32247step1 raw32247step0; decide +kernel
      have hl : raw32247step0Labels = labelEmbedding9 ∘ raw32247step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32247step0 raw32247step0Labels raw32247step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

theorem canonical32248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32248 raw32248Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw32248 raw32248Labels = mixedMoment B raw32248step0 raw32248step0Labels := by
      have hz : ∀ j, raw32248 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32248step0 = (fun i j => raw32248 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32248step0 raw32248; decide +kernel
      have hl : raw32248step0Labels = raw32248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32248 raw32248Labels permutation346 hz
    mixedMoment B raw32248step0 raw32248step0Labels = mixedMoment B raw32248step1 raw32248step1Labels := by
      have ha : raw32248step1 = (fun i j => raw32248step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32248step1 raw32248step0; decide +kernel
      have hl : raw32248step1Labels = raw32248step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32248step0 raw32248step0Labels permutation32 permutation6
    mixedMoment B raw32248step1 raw32248step1Labels = mixedMoment B raw32248step2 raw32248step2Labels := by
      have ha : raw32248step2 = raw32248step1 := by apply Matrix.ext; unfold raw32248step2 raw32248step1; decide +kernel
      have hl : raw32248step1Labels = labelEmbedding9 ∘ raw32248step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32248step1 raw32248step1Labels raw32248step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

theorem canonical32249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32249 raw32249Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw32249 raw32249Labels = mixedMoment B raw32249step0 raw32249step0Labels := by
      have hz : ∀ j, raw32249 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32249step0 = (fun i j => raw32249 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32249step0 raw32249; decide +kernel
      have hl : raw32249step0Labels = raw32249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32249 raw32249Labels permutation346 hz
    mixedMoment B raw32249step0 raw32249step0Labels = mixedMoment B raw32249step1 raw32249step1Labels := by
      have ha : raw32249step1 = (fun i j => raw32249step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32249step1 raw32249step0; decide +kernel
      have hl : raw32249step1Labels = raw32249step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32249step0 raw32249step0Labels permutation32 permutation6
    mixedMoment B raw32249step1 raw32249step1Labels = mixedMoment B raw32249step2 raw32249step2Labels := by
      have ha : raw32249step2 = raw32249step1 := by apply Matrix.ext; unfold raw32249step2 raw32249step1; decide +kernel
      have hl : raw32249step1Labels = labelEmbedding9 ∘ raw32249step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32249step1 raw32249step1Labels raw32249step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

theorem canonical32250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32250 raw32250Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw32250 raw32250Labels = mixedMoment B raw32250step0 raw32250step0Labels := by
      have hz : ∀ j, raw32250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32250step0 = (fun i j => raw32250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32250step0 raw32250; decide +kernel
      have hl : raw32250step0Labels = raw32250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32250 raw32250Labels permutation346 hz
    mixedMoment B raw32250step0 raw32250step0Labels = mixedMoment B raw32250step1 raw32250step1Labels := by
      have ha : raw32250step1 = (fun i j => raw32250step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32250step1 raw32250step0; decide +kernel
      have hl : raw32250step1Labels = raw32250step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32250step0 raw32250step0Labels permutation32 permutation6
    mixedMoment B raw32250step1 raw32250step1Labels = mixedMoment B raw32250step2 raw32250step2Labels := by
      have ha : raw32250step2 = raw32250step1 := by apply Matrix.ext; unfold raw32250step2 raw32250step1; decide +kernel
      have hl : raw32250step1Labels = labelEmbedding9 ∘ raw32250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32250step1 raw32250step1Labels raw32250step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4838 node4838Labels := by rfl

theorem canonical32251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32251 raw32251Labels = mixedMoment B node5104 node5104Labels := by
  calc
    mixedMoment B raw32251 raw32251Labels = mixedMoment B raw32251step0 raw32251step0Labels := by
      have hz : ∀ j, raw32251 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32251step0 = (fun i j => raw32251 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32251step0 raw32251; decide +kernel
      have hl : raw32251step0Labels = raw32251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32251 raw32251Labels permutation346 hz
    mixedMoment B raw32251step0 raw32251step0Labels = mixedMoment B raw32251step1 raw32251step1Labels := by
      have ha : raw32251step1 = (fun i j => raw32251step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32251step1 raw32251step0; decide +kernel
      have hl : raw32251step1Labels = raw32251step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32251step0 raw32251step0Labels permutation32 permutation6
    mixedMoment B raw32251step1 raw32251step1Labels = mixedMoment B raw32251step2 raw32251step2Labels := by
      have ha : raw32251step2 = raw32251step1 := by apply Matrix.ext; unfold raw32251step2 raw32251step1; decide +kernel
      have hl : raw32251step1Labels = labelEmbedding9 ∘ raw32251step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32251step1 raw32251step1Labels raw32251step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5104 node5104Labels := by rfl

theorem canonical32252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32252 raw32252Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw32252 raw32252Labels = mixedMoment B raw32252step0 raw32252step0Labels := by
      have ha : raw32252step0 = (fun i j => raw32252 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32252step0 raw32252; decide +kernel
      have hl : raw32252step0Labels = raw32252Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32252 raw32252Labels permutation152 permutation6
    mixedMoment B raw32252step0 raw32252step0Labels = mixedMoment B raw32252step1 raw32252step1Labels := by
      have ha : raw32252step1 = raw32252step0 := by apply Matrix.ext; unfold raw32252step1 raw32252step0; decide +kernel
      have hl : raw32252step0Labels = labelEmbedding9 ∘ raw32252step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32252step0 raw32252step0Labels raw32252step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5137 node5137Labels := by rfl

theorem canonical32253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32253 raw32253Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw32253 raw32253Labels = mixedMoment B raw32253step0 raw32253step0Labels := by
      have hz : ∀ j, raw32253 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32253step0 = (fun i j => raw32253 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32253step0 raw32253; decide +kernel
      have hl : raw32253step0Labels = raw32253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32253 raw32253Labels permutation346 hz
    mixedMoment B raw32253step0 raw32253step0Labels = mixedMoment B raw32253step1 raw32253step1Labels := by
      have ha : raw32253step1 = (fun i j => raw32253step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32253step1 raw32253step0; decide +kernel
      have hl : raw32253step1Labels = raw32253step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32253step0 raw32253step0Labels permutation32 permutation6
    mixedMoment B raw32253step1 raw32253step1Labels = mixedMoment B raw32253step2 raw32253step2Labels := by
      have ha : raw32253step2 = raw32253step1 := by apply Matrix.ext; unfold raw32253step2 raw32253step1; decide +kernel
      have hl : raw32253step1Labels = labelEmbedding9 ∘ raw32253step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32253step1 raw32253step1Labels raw32253step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

theorem canonical32254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32254 raw32254Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw32254 raw32254Labels = mixedMoment B raw32254step0 raw32254step0Labels := by
      have hz : ∀ j, raw32254 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32254step0 = (fun i j => raw32254 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32254step0 raw32254; decide +kernel
      have hl : raw32254step0Labels = raw32254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32254 raw32254Labels permutation346 hz
    mixedMoment B raw32254step0 raw32254step0Labels = mixedMoment B raw32254step1 raw32254step1Labels := by
      have ha : raw32254step1 = (fun i j => raw32254step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32254step1 raw32254step0; decide +kernel
      have hl : raw32254step1Labels = raw32254step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32254step0 raw32254step0Labels permutation34 permutation6
    mixedMoment B raw32254step1 raw32254step1Labels = mixedMoment B raw32254step2 raw32254step2Labels := by
      have ha : raw32254step2 = raw32254step1 := by apply Matrix.ext; unfold raw32254step2 raw32254step1; decide +kernel
      have hl : raw32254step1Labels = labelEmbedding9 ∘ raw32254step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32254step1 raw32254step1Labels raw32254step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

theorem canonical32255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32255 raw32255Labels = mixedMoment B node1156 node1156Labels := by
  calc
    mixedMoment B raw32255 raw32255Labels = mixedMoment B raw32255step0 raw32255step0Labels := by
      have ha : raw32255step0 = (fun i j => raw32255 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32255step0 raw32255; decide +kernel
      have hl : raw32255step0Labels = raw32255Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32255 raw32255Labels permutation160 permutation2
    _ = mixedMoment B node1156 node1156Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical252
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32256 raw32256Labels = mixedMoment B node2353 node2353Labels := by
  calc
    mixedMoment B raw32256 raw32256Labels = mixedMoment B raw32256step0 raw32256step0Labels := by
      have ha : raw32256step0 = (fun i j => raw32256 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32256step0 raw32256; decide +kernel
      have hl : raw32256step0Labels = raw32256Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32256 raw32256Labels permutation160 permutation2
    _ = mixedMoment B node2353 node2353Labels := by rfl

theorem canonical32257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32257 raw32257Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw32257 raw32257Labels = mixedMoment B raw32257step0 raw32257step0Labels := by
      have ha : raw32257step0 = (fun i j => raw32257 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32257step0 raw32257; decide +kernel
      have hl : raw32257step0Labels = raw32257Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32257 raw32257Labels permutation160 permutation2
    _ = mixedMoment B node2553 node2553Labels := by rfl

theorem canonical32258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32258 raw32258Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw32258 raw32258Labels = mixedMoment B raw32258step0 raw32258step0Labels := by
      have hz : ∀ j, raw32258 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32258step0 = (fun i j => raw32258 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32258step0 raw32258; decide +kernel
      have hl : raw32258step0Labels = raw32258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32258 raw32258Labels permutation520 hz
    mixedMoment B raw32258step0 raw32258step0Labels = mixedMoment B raw32258step1 raw32258step1Labels := by
      have ha : raw32258step1 = (fun i j => raw32258step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32258step1 raw32258step0; decide +kernel
      have hl : raw32258step1Labels = raw32258step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32258step0 raw32258step0Labels permutation34 permutation2
    _ = mixedMoment B node2590 node2590Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical96
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12326 raw12326Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw12326 raw12326Labels = mixedMoment B raw12326step0 raw12326step0Labels := by
      have hz : ∀ j, raw12326 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12326step0 = (fun i j => raw12326 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12326step0 raw12326; decide +kernel
      have hl : raw12326step0Labels = raw12326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12326 raw12326Labels permutation520 hz
    mixedMoment B raw12326step0 raw12326step0Labels = mixedMoment B raw12326step1 raw12326step1Labels := by
      have hz : ∀ j, raw12326step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12326step1 = (fun i j => raw12326step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12326step1 raw12326step0; decide +kernel
      have hl : raw12326step1Labels = raw12326step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12326step0 raw12326step0Labels permutation56 hz
    mixedMoment B raw12326step1 raw12326step1Labels = mixedMoment B raw12326step2 raw12326step2Labels := by
      have ha : raw12326step2 = (fun i j => raw12326step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw12326step2 raw12326step1; decide +kernel
      have hl : raw12326step2Labels = raw12326step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12326step1 raw12326step1Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical12332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12332 raw12332Labels = mixedMoment B node2587 node2587Labels := by
  calc
    mixedMoment B raw12332 raw12332Labels = mixedMoment B raw12332step0 raw12332step0Labels := by
      have ha : raw12332step0 = (fun i j => raw12332 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12332step0 raw12332; decide +kernel
      have hl : raw12332step0Labels = raw12332Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12332 raw12332Labels permutation160 permutation2
    _ = mixedMoment B node2587 node2587Labels := by rfl

theorem canonical12335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12335 raw12335Labels = mixedMoment B node2566 node2566Labels := by
  calc
    _ = mixedMoment B node2566 node2566Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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

theorem singleton4839 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4839 node4839Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2058 node2058Labels + mixedMoment B node2216 node2216Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1770 singletonSmall4839
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4839) = raw1770Labels := by decide +kernel
  rw [hl, canonical1770 B hB] at h
  have hc0 : mixedMoment B raw1770 (Fin.cases (0 : Fin 2) singletonSmall4839) =
      mixedMoment B node2058 node2058Labels := by
    have ha : raw1770 = raw1771 := by apply Matrix.ext; unfold raw1770 raw1771; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4839 = raw1771Labels := by decide +kernel
    rw [ha, hj, canonical1771 B hB]
  have hc1 : mixedMoment B raw1770 (Fin.cases (1 : Fin 2) singletonSmall4839) =
      mixedMoment B node2216 node2216Labels := by
    have ha : raw1770 = raw1772 := by apply Matrix.ext; unfold raw1770 raw1772; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4839 = raw1772Labels := by decide +kernel
    rw [ha, hj, canonical1772 B hB]
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

theorem singleton4869 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4869 node4869Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2110 node2110Labels + mixedMoment B node2275 node2275Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1800 singletonSmall4869
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4869) = raw1800Labels := by decide +kernel
  rw [hl, canonical1800 B hB] at h
  have hc0 : mixedMoment B raw1800 (Fin.cases (0 : Fin 2) singletonSmall4869) =
      mixedMoment B node2110 node2110Labels := by
    have ha : raw1800 = raw1801 := by apply Matrix.ext; unfold raw1800 raw1801; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4869 = raw1801Labels := by decide +kernel
    rw [ha, hj, canonical1801 B hB]
  have hc1 : mixedMoment B raw1800 (Fin.cases (1 : Fin 2) singletonSmall4869) =
      mixedMoment B node2275 node2275Labels := by
    have ha : raw1800 = raw1802 := by apply Matrix.ext; unfold raw1800 raw1802; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4869 = raw1802Labels := by decide +kernel
    rw [ha, hj, canonical1802 B hB]
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

theorem singleton5072 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5072 node5072Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2479 node2479Labels + mixedMoment B node3459 node3459Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2091 singletonSmall5072
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5072) = raw2091Labels := by decide +kernel
  rw [hl, canonical2091 B hB] at h
  have hc0 : mixedMoment B raw2091 (Fin.cases (0 : Fin 2) singletonSmall5072) =
      mixedMoment B node2479 node2479Labels := by
    have ha : raw2091 = raw2092 := by apply Matrix.ext; unfold raw2091 raw2092; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5072 = raw2092Labels := by decide +kernel
    rw [ha, hj, canonical2092 B hB]
  have hc1 : mixedMoment B raw2091 (Fin.cases (1 : Fin 2) singletonSmall5072) =
      mixedMoment B node3459 node3459Labels := by
    have ha : raw2091 = raw2093 := by apply Matrix.ext; unfold raw2091 raw2093; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5072 = raw2093Labels := by decide +kernel
    rw [ha, hj, canonical2093 B hB]
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

theorem singleton5099 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5099 node5099Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2509 node2509Labels + mixedMoment B node2704 node2704Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2124 singletonSmall5099
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5099) = raw2124Labels := by decide +kernel
  rw [hl, canonical2124 B hB] at h
  have hc0 : mixedMoment B raw2124 (Fin.cases (0 : Fin 2) singletonSmall5099) =
      mixedMoment B node2509 node2509Labels := by
    have ha : raw2124 = raw2125 := by apply Matrix.ext; unfold raw2124 raw2125; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5099 = raw2125Labels := by decide +kernel
    rw [ha, hj, canonical2125 B hB]
  have hc1 : mixedMoment B raw2124 (Fin.cases (1 : Fin 2) singletonSmall5099) =
      mixedMoment B node2704 node2704Labels := by
    have ha : raw2124 = raw2126 := by apply Matrix.ext; unfold raw2124 raw2126; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5099 = raw2126Labels := by decide +kernel
    rw [ha, hj, canonical2126 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5137 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5137 node5137Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2556 node2556Labels + mixedMoment B node3521 node3521Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2166 singletonSmall5137
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5137) = raw2166Labels := by decide +kernel
  rw [hl, canonical2166 B hB] at h
  have hc0 : mixedMoment B raw2166 (Fin.cases (0 : Fin 2) singletonSmall5137) =
      mixedMoment B node2556 node2556Labels := by
    have ha : raw2166 = raw2167 := by apply Matrix.ext; unfold raw2166 raw2167; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5137 = raw2167Labels := by decide +kernel
    rw [ha, hj, canonical2167 B hB]
  have hc1 : mixedMoment B raw2166 (Fin.cases (1 : Fin 2) singletonSmall5137) =
      mixedMoment B node3521 node3521Labels := by
    have ha : raw2166 = raw2168 := by apply Matrix.ext; unfold raw2166 raw2168; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5137 = raw2168Labels := by decide +kernel
    rw [ha, hj, canonical2168 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5149 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5149 node5149Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2924 node2924Labels + mixedMoment B node3605 node3605Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2175 singletonSmall5149
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5149) = raw2175Labels := by decide +kernel
  rw [hl, canonical2175 B hB] at h
  have hc0 : mixedMoment B raw2175 (Fin.cases (0 : Fin 2) singletonSmall5149) =
      mixedMoment B node2924 node2924Labels := by
    have ha : raw2175 = raw2176 := by apply Matrix.ext; unfold raw2175 raw2176; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5149 = raw2176Labels := by decide +kernel
    rw [ha, hj, canonical2176 B hB]
  have hc1 : mixedMoment B raw2175 (Fin.cases (1 : Fin 2) singletonSmall5149) =
      mixedMoment B node3605 node3605Labels := by
    have ha : raw2175 = raw2177 := by apply Matrix.ext; unfold raw2175 raw2177; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5149 = raw2177Labels := by decide +kernel
    rw [ha, hj, canonical2177 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5170 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5170 node5170Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2954 node2954Labels + mixedMoment B node3606 node3606Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2202 singletonSmall5170
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5170) = raw2202Labels := by decide +kernel
  rw [hl, canonical2202 B hB] at h
  have hc0 : mixedMoment B raw2202 (Fin.cases (0 : Fin 2) singletonSmall5170) =
      mixedMoment B node2954 node2954Labels := by
    have ha : raw2202 = raw2203 := by apply Matrix.ext; unfold raw2202 raw2203; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5170 = raw2203Labels := by decide +kernel
    rw [ha, hj, canonical2203 B hB]
  have hc1 : mixedMoment B raw2202 (Fin.cases (1 : Fin 2) singletonSmall5170) =
      mixedMoment B node3606 node3606Labels := by
    have ha : raw2202 = raw2204 := by apply Matrix.ext; unfold raw2202 raw2204; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5170 = raw2204Labels := by decide +kernel
    rw [ha, hj, canonical2204 B hB]
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

theorem singleton5204 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5204 node5204Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2881 node2881Labels + mixedMoment B node3624 node3624Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2232 singletonSmall5204
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5204) = raw2232Labels := by decide +kernel
  rw [hl, canonical2232 B hB] at h
  have hc0 : mixedMoment B raw2232 (Fin.cases (0 : Fin 2) singletonSmall5204) =
      mixedMoment B node2881 node2881Labels := by
    have ha : raw2232 = raw2233 := by apply Matrix.ext; unfold raw2232 raw2233; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5204 = raw2233Labels := by decide +kernel
    rw [ha, hj, canonical2233 B hB]
  have hc1 : mixedMoment B raw2232 (Fin.cases (1 : Fin 2) singletonSmall5204) =
      mixedMoment B node3624 node3624Labels := by
    have ha : raw2232 = raw2234 := by apply Matrix.ext; unfold raw2232 raw2234; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5204 = raw2234Labels := by decide +kernel
    rw [ha, hj, canonical2234 B hB]
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

theorem sound1156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1156 node1156Labels = Sparse.eval nodeValue1156 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1156) = mixedMoment B node1156 node1156Labels := rfl
  simpa [nodeValue1156, Sparse.eval] using hc.symm

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

theorem sound1668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1668 node1668Labels = Sparse.eval nodeValue1668 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1668) = mixedMoment B node1668 node1668Labels := rfl
  simpa [nodeValue1668, Sparse.eval] using hc.symm

theorem sound1669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1669 node1669Labels = Sparse.eval nodeValue1669 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1669) = mixedMoment B node1669 node1669Labels := rfl
  simpa [nodeValue1669, Sparse.eval] using hc.symm

theorem sound1676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1676 node1676Labels = Sparse.eval nodeValue1676 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1676) = mixedMoment B node1676 node1676Labels := rfl
  simpa [nodeValue1676, Sparse.eval] using hc.symm

theorem sound1682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1682 node1682Labels = Sparse.eval nodeValue1682 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1682) = mixedMoment B node1682 node1682Labels := rfl
  simpa [nodeValue1682, Sparse.eval] using hc.symm

theorem sound1714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1714 node1714Labels = Sparse.eval nodeValue1714 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1714) = mixedMoment B node1714 node1714Labels := rfl
  simpa [nodeValue1714, Sparse.eval] using hc.symm

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

theorem sound2023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2023 node2023Labels = Sparse.eval nodeValue2023 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2023) = mixedMoment B node2023 node2023Labels := rfl
  simpa [nodeValue2023, Sparse.eval] using hc.symm

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

theorem sound2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2058 node2058Labels = Sparse.eval nodeValue2058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2058) = mixedMoment B node2058 node2058Labels := rfl
  simpa [nodeValue2058, Sparse.eval] using hc.symm

theorem sound2110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2110 node2110Labels = Sparse.eval nodeValue2110 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2110) = mixedMoment B node2110 node2110Labels := rfl
  simpa [nodeValue2110, Sparse.eval] using hc.symm

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

theorem sound2214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2214 node2214Labels = Sparse.eval nodeValue2214 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2214) = mixedMoment B node2214 node2214Labels := rfl
  simpa [nodeValue2214, Sparse.eval] using hc.symm

theorem sound2216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2216 node2216Labels = Sparse.eval nodeValue2216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2216) = mixedMoment B node2216 node2216Labels := rfl
  simpa [nodeValue2216, Sparse.eval] using hc.symm

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

theorem sound2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2275 node2275Labels = Sparse.eval nodeValue2275 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2275) = mixedMoment B node2275 node2275Labels := rfl
  simpa [nodeValue2275, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2353 node2353Labels = Sparse.eval nodeValue2353 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2353) = mixedMoment B node2353 node2353Labels := rfl
  simpa [nodeValue2353, Sparse.eval] using hc.symm

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

theorem sound2479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2479 node2479Labels = Sparse.eval nodeValue2479 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2479) = mixedMoment B node2479 node2479Labels := rfl
  simpa [nodeValue2479, Sparse.eval] using hc.symm

theorem sound2483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2483 node2483Labels = Sparse.eval nodeValue2483 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2483) = mixedMoment B node2483 node2483Labels := rfl
  simpa [nodeValue2483, Sparse.eval] using hc.symm

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

theorem sound2509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2509 node2509Labels = Sparse.eval nodeValue2509 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2509) = mixedMoment B node2509 node2509Labels := rfl
  simpa [nodeValue2509, Sparse.eval] using hc.symm

theorem sound2515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2515 node2515Labels = Sparse.eval nodeValue2515 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2515) = mixedMoment B node2515 node2515Labels := rfl
  simpa [nodeValue2515, Sparse.eval] using hc.symm

theorem sound2553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2553 node2553Labels = Sparse.eval nodeValue2553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2553) = mixedMoment B node2553 node2553Labels := rfl
  simpa [nodeValue2553, Sparse.eval] using hc.symm

theorem sound2556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2556 node2556Labels = Sparse.eval nodeValue2556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2556) = mixedMoment B node2556 node2556Labels := rfl
  simpa [nodeValue2556, Sparse.eval] using hc.symm

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

theorem sound2566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2566 node2566Labels = Sparse.eval nodeValue2566 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2566) = mixedMoment B node2566 node2566Labels := rfl
  simpa [nodeValue2566, Sparse.eval] using hc.symm

theorem sound2587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2587 node2587Labels = Sparse.eval nodeValue2587 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2587) = mixedMoment B node2587 node2587Labels := rfl
  simpa [nodeValue2587, Sparse.eval] using hc.symm

theorem sound2590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2590 node2590Labels = Sparse.eval nodeValue2590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2590) = mixedMoment B node2590 node2590Labels := rfl
  simpa [nodeValue2590, Sparse.eval] using hc.symm

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

theorem sound2652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2652 node2652Labels = Sparse.eval nodeValue2652 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2652) = mixedMoment B node2652 node2652Labels := rfl
  simpa [nodeValue2652, Sparse.eval] using hc.symm

theorem sound2658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2658 node2658Labels = Sparse.eval nodeValue2658 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2658) = mixedMoment B node2658 node2658Labels := rfl
  simpa [nodeValue2658, Sparse.eval] using hc.symm

theorem sound2670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2670 node2670Labels = Sparse.eval nodeValue2670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2670) = mixedMoment B node2670 node2670Labels := rfl
  simpa [nodeValue2670, Sparse.eval] using hc.symm

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

theorem sound2704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2704 node2704Labels = Sparse.eval nodeValue2704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2704) = mixedMoment B node2704 node2704Labels := rfl
  simpa [nodeValue2704, Sparse.eval] using hc.symm

theorem sound2719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2719 node2719Labels = Sparse.eval nodeValue2719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2719) = mixedMoment B node2719 node2719Labels := rfl
  simpa [nodeValue2719, Sparse.eval] using hc.symm

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

theorem sound2881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2881 node2881Labels = Sparse.eval nodeValue2881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2881) = mixedMoment B node2881 node2881Labels := rfl
  simpa [nodeValue2881, Sparse.eval] using hc.symm

theorem sound2924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2924 node2924Labels = Sparse.eval nodeValue2924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2924) = mixedMoment B node2924 node2924Labels := rfl
  simpa [nodeValue2924, Sparse.eval] using hc.symm

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

theorem sound2954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2954 node2954Labels = Sparse.eval nodeValue2954 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2954) = mixedMoment B node2954 node2954Labels := rfl
  simpa [nodeValue2954, Sparse.eval] using hc.symm

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

theorem sound3407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3407 node3407Labels = Sparse.eval nodeValue3407 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3407) = mixedMoment B node3407 node3407Labels := rfl
  simpa [nodeValue3407, Sparse.eval] using hc.symm

theorem sound3413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3413 node3413Labels = Sparse.eval nodeValue3413 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3413) = mixedMoment B node3413 node3413Labels := rfl
  simpa [nodeValue3413, Sparse.eval] using hc.symm

theorem sound3418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3418 node3418Labels = Sparse.eval nodeValue3418 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3418) = mixedMoment B node3418 node3418Labels := rfl
  simpa [nodeValue3418, Sparse.eval] using hc.symm

theorem sound3451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3451 node3451Labels = Sparse.eval nodeValue3451 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3451) = mixedMoment B node3451 node3451Labels := rfl
  simpa [nodeValue3451, Sparse.eval] using hc.symm

theorem sound3454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3454 node3454Labels = Sparse.eval nodeValue3454 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3454) = mixedMoment B node3454 node3454Labels := rfl
  simpa [nodeValue3454, Sparse.eval] using hc.symm

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

theorem sound3463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3463 node3463Labels = Sparse.eval nodeValue3463 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3463) = mixedMoment B node3463 node3463Labels := rfl
  simpa [nodeValue3463, Sparse.eval] using hc.symm

theorem sound3477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3477 node3477Labels = Sparse.eval nodeValue3477 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3477) = mixedMoment B node3477 node3477Labels := rfl
  simpa [nodeValue3477, Sparse.eval] using hc.symm

theorem sound3479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3479 node3479Labels = Sparse.eval nodeValue3479 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3479) = mixedMoment B node3479 node3479Labels := rfl
  simpa [nodeValue3479, Sparse.eval] using hc.symm

theorem sound3481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3481 node3481Labels = Sparse.eval nodeValue3481 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3481) = mixedMoment B node3481 node3481Labels := rfl
  simpa [nodeValue3481, Sparse.eval] using hc.symm

theorem sound3517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3517 node3517Labels = Sparse.eval nodeValue3517 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3517) = mixedMoment B node3517 node3517Labels := rfl
  simpa [nodeValue3517, Sparse.eval] using hc.symm

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

theorem sound3521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3521 node3521Labels = Sparse.eval nodeValue3521 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3521) = mixedMoment B node3521 node3521Labels := rfl
  simpa [nodeValue3521, Sparse.eval] using hc.symm

theorem sound3523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3523 node3523Labels = Sparse.eval nodeValue3523 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3523) = mixedMoment B node3523 node3523Labels := rfl
  simpa [nodeValue3523, Sparse.eval] using hc.symm

theorem sound3540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3540 node3540Labels = Sparse.eval nodeValue3540 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3540) = mixedMoment B node3540 node3540Labels := rfl
  simpa [nodeValue3540, Sparse.eval] using hc.symm

theorem sound3558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3558 node3558Labels = Sparse.eval nodeValue3558 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3558) = mixedMoment B node3558 node3558Labels := rfl
  simpa [nodeValue3558, Sparse.eval] using hc.symm

theorem sound3565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3565 node3565Labels = Sparse.eval nodeValue3565 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3565) = mixedMoment B node3565 node3565Labels := rfl
  simpa [nodeValue3565, Sparse.eval] using hc.symm

theorem sound3572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3572 node3572Labels = Sparse.eval nodeValue3572 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3572) = mixedMoment B node3572 node3572Labels := rfl
  simpa [nodeValue3572, Sparse.eval] using hc.symm

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

theorem sound3605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3605 node3605Labels = Sparse.eval nodeValue3605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3605) = mixedMoment B node3605 node3605Labels := rfl
  simpa [nodeValue3605, Sparse.eval] using hc.symm

theorem sound3606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3606 node3606Labels = Sparse.eval nodeValue3606 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3606) = mixedMoment B node3606 node3606Labels := rfl
  simpa [nodeValue3606, Sparse.eval] using hc.symm

theorem sound3612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3612 node3612Labels = Sparse.eval nodeValue3612 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3612) = mixedMoment B node3612 node3612Labels := rfl
  simpa [nodeValue3612, Sparse.eval] using hc.symm

theorem sound3624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3624 node3624Labels = Sparse.eval nodeValue3624 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3624) = mixedMoment B node3624 node3624Labels := rfl
  simpa [nodeValue3624, Sparse.eval] using hc.symm

theorem sound3625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3625 node3625Labels = Sparse.eval nodeValue3625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3625) = mixedMoment B node3625 node3625Labels := rfl
  simpa [nodeValue3625, Sparse.eval] using hc.symm

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

theorem zero3816 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3816 node3816Labels = 0 := by
  exact mixedMoment_order_one B hB node3816 node3816Labels 1
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

theorem sound3804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3804 node3804Labels = Sparse.eval nodeValue3804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3804) = mixedMoment B node3804 node3804Labels := rfl
  simpa [nodeValue3804, Sparse.eval] using hc.symm

theorem sound3815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3815 node3815Labels = Sparse.eval nodeValue3815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3815) = mixedMoment B node3815 node3815Labels := rfl
  simpa [nodeValue3815, Sparse.eval] using hc.symm

theorem sound3816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3816 node3816Labels = Sparse.eval nodeValue3816 (mixedVector B) := by
  simpa only [nodeValue3816, Sparse.eval_nil] using zero3816 B _hB _hF

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

theorem sound3857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3857 node3857Labels = Sparse.eval nodeValue3857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3857) = mixedMoment B node3857 node3857Labels := rfl
  simpa [nodeValue3857, Sparse.eval] using hc.symm

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

theorem sound3983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3983 node3983Labels = Sparse.eval nodeValue3983 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3983) = mixedMoment B node3983 node3983Labels := rfl
  simpa [nodeValue3983, Sparse.eval] using hc.symm

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

theorem sound4805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4805 node4805Labels = Sparse.eval nodeValue4805 (mixedVector B) := by
  have h := singleton4805 B _hB
  rw [sound2023 B _hB _hF, sound2214 B _hB _hF] at h
  norm_num [nodeValue4805, nodeValue2023, nodeValue2214, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4838 node4838Labels = Sparse.eval nodeValue4838 (mixedVector B) := by
  simpa only [nodeValue4838, Sparse.eval_nil] using zero4838 B _hB _hF

theorem sound4839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4839 node4839Labels = Sparse.eval nodeValue4839 (mixedVector B) := by
  have h := singleton4839 B _hB
  rw [sound2058 B _hB _hF, sound2216 B _hB _hF] at h
  norm_num [nodeValue4839, nodeValue2058, nodeValue2216, Sparse.eval] at h ⊢
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

theorem sound4869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4869 node4869Labels = Sparse.eval nodeValue4869 (mixedVector B) := by
  have h := singleton4869 B _hB
  rw [sound2110 B _hB _hF, sound2275 B _hB _hF] at h
  norm_num [nodeValue4869, nodeValue2110, nodeValue2275, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem zero5101 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5101 node5101Labels = 0 := by
  exact mixedMoment_order_one B hB node5101 node5101Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5104 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5104 node5104Labels = 0 := by
  exact mixedMoment_order_one B hB node5104 node5104Labels 1
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

theorem sound5072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5072 node5072Labels = Sparse.eval nodeValue5072 (mixedVector B) := by
  have h := singleton5072 B _hB
  rw [sound2479 B _hB _hF, sound3459 B _hB _hF] at h
  norm_num [nodeValue5072, nodeValue2479, nodeValue3459, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5076 node5076Labels = Sparse.eval nodeValue5076 (mixedVector B) := by
  have h := singleton5076 B _hB
  rw [sound2483 B _hB _hF, sound3477 B _hB _hF] at h
  norm_num [nodeValue5076, nodeValue2483, nodeValue3477, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5099 node5099Labels = Sparse.eval nodeValue5099 (mixedVector B) := by
  have h := singleton5099 B _hB
  rw [sound2509 B _hB _hF, sound2704 B _hB _hF] at h
  norm_num [nodeValue5099, nodeValue2509, nodeValue2704, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5101 node5101Labels = Sparse.eval nodeValue5101 (mixedVector B) := by
  simpa only [nodeValue5101, Sparse.eval_nil] using zero5101 B _hB _hF

theorem sound5104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5104 node5104Labels = Sparse.eval nodeValue5104 (mixedVector B) := by
  simpa only [nodeValue5104, Sparse.eval_nil] using zero5104 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5137 node5137Labels = Sparse.eval nodeValue5137 (mixedVector B) := by
  have h := singleton5137 B _hB
  rw [sound2556 B _hB _hF, sound3521 B _hB _hF] at h
  norm_num [nodeValue5137, nodeValue2556, nodeValue3521, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5138 node5138Labels = Sparse.eval nodeValue5138 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5138) = mixedMoment B node5138 node5138Labels := rfl
  simpa [nodeValue5138, Sparse.eval] using hc.symm

theorem sound5149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5149 node5149Labels = Sparse.eval nodeValue5149 (mixedVector B) := by
  have h := singleton5149 B _hB
  rw [sound2924 B _hB _hF, sound3605 B _hB _hF] at h
  norm_num [nodeValue5149, nodeValue2924, nodeValue3605, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5150 node5150Labels = Sparse.eval nodeValue5150 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5150) = mixedMoment B node5150 node5150Labels := rfl
  simpa [nodeValue5150, Sparse.eval] using hc.symm

theorem sound5170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5170 node5170Labels = Sparse.eval nodeValue5170 (mixedVector B) := by
  have h := singleton5170 B _hB
  rw [sound2954 B _hB _hF, sound3606 B _hB _hF] at h
  norm_num [nodeValue5170, nodeValue2954, nodeValue3606, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5173 node5173Labels = Sparse.eval nodeValue5173 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5173) = mixedMoment B node5173 node5173Labels := rfl
  simpa [nodeValue5173, Sparse.eval] using hc.symm

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

theorem sound5187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5187 node5187Labels = Sparse.eval nodeValue5187 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5187) = mixedMoment B node5187 node5187Labels := rfl
  simpa [nodeValue5187, Sparse.eval] using hc.symm

theorem sound5204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5204 node5204Labels = Sparse.eval nodeValue5204 (mixedVector B) := by
  have h := singleton5204 B _hB
  rw [sound2881 B _hB _hF, sound3624 B _hB _hF] at h
  norm_num [nodeValue5204, nodeValue2881, nodeValue3624, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5205 node5205Labels = Sparse.eval nodeValue5205 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5205) = mixedMoment B node5205 node5205Labels := rfl
  simpa [nodeValue5205, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources73
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2349 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2349 + difference 0 1) (sourceB2349 + difference 1 0) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3815) := by
    have ha : (tripleCharges (sourceA2349 + difference 0 1) (sourceB2349 + difference 1 0) sourceC2349) = raw32154 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32154; decide +kernel
    rw [ha]
    exact (canonical32154 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2349 + difference 0 2) (sourceB2349 + difference 2 0) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA2349 + difference 0 2) (sourceB2349 + difference 2 0) sourceC2349) = raw32155 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32155; decide +kernel
    rw [ha]
    exact (canonical32155 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2349 + difference 0 3) (sourceB2349 + difference 3 0) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA2349 + difference 0 3) (sourceB2349 + difference 3 0) sourceC2349) = raw32156 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32156; decide +kernel
    rw [ha]
    exact (canonical32156 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2349 + difference 0 4) (sourceB2349 + difference 4 0) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2349 + difference 0 4) (sourceB2349 + difference 4 0) sourceC2349) = raw32157 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32157; decide +kernel
    rw [ha]
    exact (canonical32157 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2349 + difference 0 5) (sourceB2349 + difference 5 0) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA2349 + difference 0 5) (sourceB2349 + difference 5 0) sourceC2349) = raw32158 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32158; decide +kernel
    rw [ha]
    exact (canonical32158 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2349 + difference 1 0) (sourceB2349 + difference 0 1) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA2349 + difference 1 0) (sourceB2349 + difference 0 1) sourceC2349) = raw32159 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32159; decide +kernel
    rw [ha]
    exact (canonical32159 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2349 + difference 1 2) (sourceB2349 + difference 2 1) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA2349 + difference 1 2) (sourceB2349 + difference 2 1) sourceC2349) = raw32160 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32160; decide +kernel
    rw [ha]
    exact (canonical32160 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2349 + difference 1 3) (sourceB2349 + difference 3 1) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA2349 + difference 1 3) (sourceB2349 + difference 3 1) sourceC2349) = raw32161 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32161; decide +kernel
    rw [ha]
    exact (canonical32161 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2349 + difference 1 4) (sourceB2349 + difference 4 1) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA2349 + difference 1 4) (sourceB2349 + difference 4 1) sourceC2349) = raw32162 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32162; decide +kernel
    rw [ha]
    exact (canonical32162 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2349 + difference 1 5) (sourceB2349 + difference 5 1) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA2349 + difference 1 5) (sourceB2349 + difference 5 1) sourceC2349) = raw32163 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32163; decide +kernel
    rw [ha]
    exact (canonical32163 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2349 + difference 2 0) (sourceB2349 + difference 0 2) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1668) := by
    have ha : (tripleCharges (sourceA2349 + difference 2 0) (sourceB2349 + difference 0 2) sourceC2349) = raw32164 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32164; decide +kernel
    rw [ha]
    exact (canonical32164 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2349 + difference 2 1) (sourceB2349 + difference 1 2) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3407) := by
    have ha : (tripleCharges (sourceA2349 + difference 2 1) (sourceB2349 + difference 1 2) sourceC2349) = raw32165 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32165; decide +kernel
    rw [ha]
    exact (canonical32165 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2349 + difference 2 3) (sourceB2349 + difference 3 2) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA2349 + difference 2 3) (sourceB2349 + difference 3 2) sourceC2349) = raw32166 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32166; decide +kernel
    rw [ha]
    exact (canonical32166 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2349 + difference 2 4) (sourceB2349 + difference 4 2) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA2349 + difference 2 4) (sourceB2349 + difference 4 2) sourceC2349) = raw32167 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32167; decide +kernel
    rw [ha]
    exact (canonical32167 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2349 + difference 2 5) (sourceB2349 + difference 5 2) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA2349 + difference 2 5) (sourceB2349 + difference 5 2) sourceC2349) = raw32168 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32168; decide +kernel
    rw [ha]
    exact (canonical32168 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2349 + difference 3 0) (sourceB2349 + difference 0 3) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1682) := by
    have ha : (tripleCharges (sourceA2349 + difference 3 0) (sourceB2349 + difference 0 3) sourceC2349) = raw32169 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32169; decide +kernel
    rw [ha]
    exact (canonical32169 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2349 + difference 3 1) (sourceB2349 + difference 1 3) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3418) := by
    have ha : (tripleCharges (sourceA2349 + difference 3 1) (sourceB2349 + difference 1 3) sourceC2349) = raw32170 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32170; decide +kernel
    rw [ha]
    exact (canonical32170 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2349 + difference 3 2) (sourceB2349 + difference 2 3) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3454) := by
    have ha : (tripleCharges (sourceA2349 + difference 3 2) (sourceB2349 + difference 2 3) sourceC2349) = raw32171 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32171; decide +kernel
    rw [ha]
    exact (canonical32171 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2349 + difference 3 4) (sourceB2349 + difference 4 3) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2349 + difference 3 4) (sourceB2349 + difference 4 3) sourceC2349) = raw32172 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32172; decide +kernel
    rw [ha]
    exact (canonical32172 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2349 + difference 3 5) (sourceB2349 + difference 5 3) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA2349 + difference 3 5) (sourceB2349 + difference 5 3) sourceC2349) = raw32173 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32173; decide +kernel
    rw [ha]
    exact (canonical32173 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2349 + difference 4 0) (sourceB2349 + difference 0 4) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA2349 + difference 4 0) (sourceB2349 + difference 0 4) sourceC2349) = raw32174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32174; decide +kernel
    rw [ha]
    exact (canonical32174 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2349 + difference 4 1) (sourceB2349 + difference 1 4) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2349 + difference 4 1) (sourceB2349 + difference 1 4) sourceC2349) = raw32175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32175; decide +kernel
    rw [ha]
    exact (canonical32175 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2349 + difference 4 2) (sourceB2349 + difference 2 4) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2652) := by
    have ha : (tripleCharges (sourceA2349 + difference 4 2) (sourceB2349 + difference 2 4) sourceC2349) = raw32176 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32176; decide +kernel
    rw [ha]
    exact (canonical32176 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2349 + difference 4 3) (sourceB2349 + difference 3 4) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA2349 + difference 4 3) (sourceB2349 + difference 3 4) sourceC2349) = raw32177 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32177; decide +kernel
    rw [ha]
    exact (canonical32177 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2349 + difference 4 5) (sourceB2349 + difference 5 4) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA2349 + difference 4 5) (sourceB2349 + difference 5 4) sourceC2349) = raw32178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32178; decide +kernel
    rw [ha]
    exact (canonical32178 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2349 + difference 5 0) (sourceB2349 + difference 0 5) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA2349 + difference 5 0) (sourceB2349 + difference 0 5) sourceC2349) = raw32179 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32179; decide +kernel
    rw [ha]
    exact (canonical32179 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2349 + difference 5 1) (sourceB2349 + difference 1 5) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA2349 + difference 5 1) (sourceB2349 + difference 1 5) sourceC2349) = raw32180 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32180; decide +kernel
    rw [ha]
    exact (canonical32180 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2349 + difference 5 2) (sourceB2349 + difference 2 5) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3451) := by
    have ha : (tripleCharges (sourceA2349 + difference 5 2) (sourceB2349 + difference 2 5) sourceC2349) = raw32181 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32181; decide +kernel
    rw [ha]
    exact (canonical32181 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2349 + difference 5 3) (sourceB2349 + difference 3 5) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA2349 + difference 5 3) (sourceB2349 + difference 3 5) sourceC2349) = raw32182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32182; decide +kernel
    rw [ha]
    exact (canonical32182 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2349 + difference 5 4) (sourceB2349 + difference 4 5) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA2349 + difference 5 4) (sourceB2349 + difference 4 5) sourceC2349) = raw32183 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32183; decide +kernel
    rw [ha]
    exact (canonical32183 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2349 sourceB2349 sourceC2349
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2349, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2354 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2354 + difference 0 1) (sourceB2354 + difference 1 0) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2354 + difference 0 1) (sourceB2354 + difference 1 0) sourceC2354) = raw32225 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32225; decide +kernel
    rw [ha]
    exact (canonical32225 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2354 + difference 0 2) (sourceB2354 + difference 2 0) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA2354 + difference 0 2) (sourceB2354 + difference 2 0) sourceC2354) = raw32226 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32226; decide +kernel
    rw [ha]
    exact (canonical32226 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2354 + difference 0 3) (sourceB2354 + difference 3 0) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2354 + difference 0 3) (sourceB2354 + difference 3 0) sourceC2354) = raw32227 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32227; decide +kernel
    rw [ha]
    exact (canonical32227 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2354 + difference 0 4) (sourceB2354 + difference 4 0) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2354 + difference 0 4) (sourceB2354 + difference 4 0) sourceC2354) = raw32228 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32228; decide +kernel
    rw [ha]
    exact (canonical32228 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2354 + difference 0 5) (sourceB2354 + difference 5 0) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA2354 + difference 0 5) (sourceB2354 + difference 5 0) sourceC2354) = raw32229 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32229; decide +kernel
    rw [ha]
    exact (canonical32229 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2354 + difference 1 0) (sourceB2354 + difference 0 1) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA2354 + difference 1 0) (sourceB2354 + difference 0 1) sourceC2354) = raw32230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32230; decide +kernel
    rw [ha]
    exact (canonical32230 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2354 + difference 1 2) (sourceB2354 + difference 2 1) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5187) := by
    have ha : (tripleCharges (sourceA2354 + difference 1 2) (sourceB2354 + difference 2 1) sourceC2354) = raw32231 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32231; decide +kernel
    rw [ha]
    exact (canonical32231 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2354 + difference 1 3) (sourceB2354 + difference 3 1) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2354 + difference 1 3) (sourceB2354 + difference 3 1) sourceC2354) = raw32232 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32232; decide +kernel
    rw [ha]
    exact (canonical32232 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2354 + difference 1 4) (sourceB2354 + difference 4 1) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2354 + difference 1 4) (sourceB2354 + difference 4 1) sourceC2354) = raw32233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32233; decide +kernel
    rw [ha]
    exact (canonical32233 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2354 + difference 1 5) (sourceB2354 + difference 5 1) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5205) := by
    have ha : (tripleCharges (sourceA2354 + difference 1 5) (sourceB2354 + difference 5 1) sourceC2354) = raw32234 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32234; decide +kernel
    rw [ha]
    exact (canonical32234 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2354 + difference 2 0) (sourceB2354 + difference 0 2) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2354 + difference 2 0) (sourceB2354 + difference 0 2) sourceC2354) = raw32235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32235; decide +kernel
    rw [ha]
    exact (canonical32235 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2354 + difference 2 1) (sourceB2354 + difference 1 2) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA2354 + difference 2 1) (sourceB2354 + difference 1 2) sourceC2354) = raw32236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32236; decide +kernel
    rw [ha]
    exact (canonical32236 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2354 + difference 2 3) (sourceB2354 + difference 3 2) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2354 + difference 2 3) (sourceB2354 + difference 3 2) sourceC2354) = raw32237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32237; decide +kernel
    rw [ha]
    exact (canonical32237 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2354 + difference 2 4) (sourceB2354 + difference 4 2) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2354 + difference 2 4) (sourceB2354 + difference 4 2) sourceC2354) = raw32238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32238; decide +kernel
    rw [ha]
    exact (canonical32238 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2354 + difference 2 5) (sourceB2354 + difference 5 2) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5150) := by
    have ha : (tripleCharges (sourceA2354 + difference 2 5) (sourceB2354 + difference 5 2) sourceC2354) = raw32239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32239; decide +kernel
    rw [ha]
    exact (canonical32239 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2354 + difference 3 0) (sourceB2354 + difference 0 3) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2354 + difference 3 0) (sourceB2354 + difference 0 3) sourceC2354) = raw32240 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32240; decide +kernel
    rw [ha]
    exact (canonical32240 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2354 + difference 3 1) (sourceB2354 + difference 1 3) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA2354 + difference 3 1) (sourceB2354 + difference 1 3) sourceC2354) = raw32241 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32241; decide +kernel
    rw [ha]
    exact (canonical32241 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2354 + difference 3 2) (sourceB2354 + difference 2 3) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA2354 + difference 3 2) (sourceB2354 + difference 2 3) sourceC2354) = raw32242 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32242; decide +kernel
    rw [ha]
    exact (canonical32242 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2354 + difference 3 4) (sourceB2354 + difference 4 3) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2354 + difference 3 4) (sourceB2354 + difference 4 3) sourceC2354) = raw32243 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32243; decide +kernel
    rw [ha]
    exact (canonical32243 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2354 + difference 3 5) (sourceB2354 + difference 5 3) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA2354 + difference 3 5) (sourceB2354 + difference 5 3) sourceC2354) = raw32244 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32244; decide +kernel
    rw [ha]
    exact (canonical32244 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2354 + difference 4 0) (sourceB2354 + difference 0 4) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2354 + difference 4 0) (sourceB2354 + difference 0 4) sourceC2354) = raw32245 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32245; decide +kernel
    rw [ha]
    exact (canonical32245 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2354 + difference 4 1) (sourceB2354 + difference 1 4) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA2354 + difference 4 1) (sourceB2354 + difference 1 4) sourceC2354) = raw32246 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32246; decide +kernel
    rw [ha]
    exact (canonical32246 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2354 + difference 4 2) (sourceB2354 + difference 2 4) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA2354 + difference 4 2) (sourceB2354 + difference 2 4) sourceC2354) = raw32247 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32247; decide +kernel
    rw [ha]
    exact (canonical32247 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2354 + difference 4 3) (sourceB2354 + difference 3 4) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2354 + difference 4 3) (sourceB2354 + difference 3 4) sourceC2354) = raw32248 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32248; decide +kernel
    rw [ha]
    exact (canonical32248 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2354 + difference 4 5) (sourceB2354 + difference 5 4) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA2354 + difference 4 5) (sourceB2354 + difference 5 4) sourceC2354) = raw32249 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32249; decide +kernel
    rw [ha]
    exact (canonical32249 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2354 + difference 5 0) (sourceB2354 + difference 0 5) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2354 + difference 5 0) (sourceB2354 + difference 0 5) sourceC2354) = raw32250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32250; decide +kernel
    rw [ha]
    exact (canonical32250 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2354 + difference 5 1) (sourceB2354 + difference 1 5) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA2354 + difference 5 1) (sourceB2354 + difference 1 5) sourceC2354) = raw32251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32251; decide +kernel
    rw [ha]
    exact (canonical32251 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2354 + difference 5 2) (sourceB2354 + difference 2 5) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2354 + difference 5 2) (sourceB2354 + difference 2 5) sourceC2354) = raw32252 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32252; decide +kernel
    rw [ha]
    exact (canonical32252 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2354 + difference 5 3) (sourceB2354 + difference 3 5) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2354 + difference 5 3) (sourceB2354 + difference 3 5) sourceC2354) = raw32253 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32253; decide +kernel
    rw [ha]
    exact (canonical32253 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2354 + difference 5 4) (sourceB2354 + difference 4 5) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2354 + difference 5 4) (sourceB2354 + difference 4 5) sourceC2354) = raw32254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32254; decide +kernel
    rw [ha]
    exact (canonical32254 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2354 sourceB2354 sourceC2354
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2354, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2355 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2355 + difference 2 0) (sourceB2355 + difference 0 2) sourceC2355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1156) := by
    have ha : (tripleCharges (sourceA2355 + difference 2 0) (sourceB2355 + difference 0 2) sourceC2355) = raw32255 := by
      apply Matrix.ext; unfold tripleCharges sourceA2355 sourceB2355 sourceC2355 difference raw32255; decide +kernel
    rw [ha]
    exact (canonical32255 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2355 + difference 2 1) (sourceB2355 + difference 1 2) sourceC2355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2353) := by
    have ha : (tripleCharges (sourceA2355 + difference 2 1) (sourceB2355 + difference 1 2) sourceC2355) = raw32256 := by
      apply Matrix.ext; unfold tripleCharges sourceA2355 sourceB2355 sourceC2355 difference raw32256; decide +kernel
    rw [ha]
    exact (canonical32256 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2355 + difference 2 2) (sourceB2355 + difference 2 2) sourceC2355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2566) := by
    have ha : (tripleCharges (sourceA2355 + difference 2 2) (sourceB2355 + difference 2 2) sourceC2355) = raw12335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2355 sourceB2355 sourceC2355 difference raw12335; decide +kernel
    rw [ha]
    exact (canonical12335 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2355 + difference 2 3) (sourceB2355 + difference 3 2) sourceC2355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA2355 + difference 2 3) (sourceB2355 + difference 3 2) sourceC2355) = raw32257 := by
      apply Matrix.ext; unfold tripleCharges sourceA2355 sourceB2355 sourceC2355 difference raw32257; decide +kernel
    rw [ha]
    exact (canonical32257 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2355 + difference 2 4) (sourceB2355 + difference 4 2) sourceC2355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA2355 + difference 2 4) (sourceB2355 + difference 4 2) sourceC2355) = raw32258 := by
      apply Matrix.ext; unfold tripleCharges sourceA2355 sourceB2355 sourceC2355 difference raw32258; decide +kernel
    rw [ha]
    exact (canonical32258 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2355 + difference 2 5) (sourceB2355 + difference 5 2) sourceC2355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2587) := by
    have ha : (tripleCharges (sourceA2355 + difference 2 5) (sourceB2355 + difference 5 2) sourceC2355) = raw12332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2355 sourceB2355 sourceC2355 difference raw12332; decide +kernel
    rw [ha]
    exact (canonical12332 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2355 + sourceB2355) sourceC2355) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2355 + sourceB2355) sourceC2355) = raw12326 := by
      apply Matrix.ext; unfold doubleCharges sourceA2355 sourceB2355 sourceC2355 raw12326; decide +kernel
    rw [ha]
    exact (canonical12326 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2355 sourceB2355 sourceC2355
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2355, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1909 : Integer.Sparse.reindex keyMap MixedData.row1909 = numericRow1909 := by decide +kernel

theorem numericCheck1909 (x : Master → ℝ) : Integer.Sparse.eval numericRow1909 x =
    (1080 : ℝ) * reducedSource1909 x := by
  norm_num [numericRow1909, reducedSource1909, Integer.Sparse.eval, Sparse.eval, nodeValue1129, nodeValue1131, nodeValue1134, nodeValue1139, nodeValue1301, nodeValue2429, nodeValue2434, nodeValue2485, nodeValue2601, nodeValue2809, nodeValue2813, nodeValue2818, nodeValue2893, nodeValue2897, nodeValue2927, nodeValue2931, nodeValue2958, nodeValue2959, nodeValue2960, nodeValue2969, nodeValue3102, nodeValue3122, nodeValue3123, nodeValue3737, nodeValue3967, nodeValue3982, nodeValue4001, nodeValue4036]
  ring

theorem reindexCheck1913 : Integer.Sparse.reindex keyMap MixedData.row1913 = numericRow1913 := by decide +kernel

theorem numericCheck1913 (x : Master → ℝ) : Integer.Sparse.eval numericRow1913 x =
    (1 : ℝ) * reducedSource1913 x := by
  norm_num [numericRow1913, reducedSource1913, Integer.Sparse.eval, Sparse.eval, nodeValue1668, nodeValue1669, nodeValue1676, nodeValue1682, nodeValue1714, nodeValue2652, nodeValue2658, nodeValue2670, nodeValue2719, nodeValue3407, nodeValue3413, nodeValue3418, nodeValue3451, nodeValue3454, nodeValue3463, nodeValue3481, nodeValue3517, nodeValue3523, nodeValue3540, nodeValue3558, nodeValue3565, nodeValue3572, nodeValue3605, nodeValue3612, nodeValue3625, nodeValue3804, nodeValue3815, nodeValue3816, nodeValue3857, nodeValue3983]

theorem reindexCheck1918 : Integer.Sparse.reindex keyMap MixedData.row1918 = numericRow1918 := by decide +kernel

theorem numericCheck1918 (x : Master → ℝ) : Integer.Sparse.eval numericRow1918 x =
    (17280 : ℝ) * reducedSource1918 x := by
  norm_num [numericRow1918, reducedSource1918, Integer.Sparse.eval, Sparse.eval, nodeValue4805, nodeValue4838, nodeValue4839, nodeValue4869, nodeValue5072, nodeValue5076, nodeValue5099, nodeValue5101, nodeValue5104, nodeValue5105, nodeValue5137, nodeValue5138, nodeValue5149, nodeValue5150, nodeValue5168, nodeValue5169, nodeValue5170, nodeValue5173, nodeValue5187, nodeValue5204, nodeValue5205]
  ring

theorem reindexCheck1919 : Integer.Sparse.reindex keyMap MixedData.row1919 = numericRow1919 := by decide +kernel

theorem numericCheck1919 (x : Master → ℝ) : Integer.Sparse.eval numericRow1919 x =
    (1 : ℝ) * reducedSource1919 x := by
  norm_num [numericRow1919, reducedSource1919, Integer.Sparse.eval, Sparse.eval, nodeValue1156, nodeValue2353, nodeValue2553, nodeValue2566, nodeValue2587, nodeValue2590, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem rowSound1909 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1909 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1909, numericCheck1909, reducedZero1909_e B hB hF, mul_zero]

theorem reducedZero1913 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1913 (mixedVector B) = 0 := by
  have h1668 : mixedVector B (Sum.inr 1668) = Sparse.eval nodeValue1668 (mixedVector B) := by
    change mixedMoment B node1668 node1668Labels = _
    exact sound1668 B hB hF
  have h1669 : mixedVector B (Sum.inr 1669) = Sparse.eval nodeValue1669 (mixedVector B) := by
    change mixedMoment B node1669 node1669Labels = _
    exact sound1669 B hB hF
  have h1676 : mixedVector B (Sum.inr 1676) = Sparse.eval nodeValue1676 (mixedVector B) := by
    change mixedMoment B node1676 node1676Labels = _
    exact sound1676 B hB hF
  have h1682 : mixedVector B (Sum.inr 1682) = Sparse.eval nodeValue1682 (mixedVector B) := by
    change mixedMoment B node1682 node1682Labels = _
    exact sound1682 B hB hF
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h2652 : mixedVector B (Sum.inr 2652) = Sparse.eval nodeValue2652 (mixedVector B) := by
    change mixedMoment B node2652 node2652Labels = _
    exact sound2652 B hB hF
  have h2658 : mixedVector B (Sum.inr 2658) = Sparse.eval nodeValue2658 (mixedVector B) := by
    change mixedMoment B node2658 node2658Labels = _
    exact sound2658 B hB hF
  have h2670 : mixedVector B (Sum.inr 2670) = Sparse.eval nodeValue2670 (mixedVector B) := by
    change mixedMoment B node2670 node2670Labels = _
    exact sound2670 B hB hF
  have h2719 : mixedVector B (Sum.inr 2719) = Sparse.eval nodeValue2719 (mixedVector B) := by
    change mixedMoment B node2719 node2719Labels = _
    exact sound2719 B hB hF
  have h3407 : mixedVector B (Sum.inr 3407) = Sparse.eval nodeValue3407 (mixedVector B) := by
    change mixedMoment B node3407 node3407Labels = _
    exact sound3407 B hB hF
  have h3413 : mixedVector B (Sum.inr 3413) = Sparse.eval nodeValue3413 (mixedVector B) := by
    change mixedMoment B node3413 node3413Labels = _
    exact sound3413 B hB hF
  have h3418 : mixedVector B (Sum.inr 3418) = Sparse.eval nodeValue3418 (mixedVector B) := by
    change mixedMoment B node3418 node3418Labels = _
    exact sound3418 B hB hF
  have h3451 : mixedVector B (Sum.inr 3451) = Sparse.eval nodeValue3451 (mixedVector B) := by
    change mixedMoment B node3451 node3451Labels = _
    exact sound3451 B hB hF
  have h3454 : mixedVector B (Sum.inr 3454) = Sparse.eval nodeValue3454 (mixedVector B) := by
    change mixedMoment B node3454 node3454Labels = _
    exact sound3454 B hB hF
  have h3463 : mixedVector B (Sum.inr 3463) = Sparse.eval nodeValue3463 (mixedVector B) := by
    change mixedMoment B node3463 node3463Labels = _
    exact sound3463 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h3517 : mixedVector B (Sum.inr 3517) = Sparse.eval nodeValue3517 (mixedVector B) := by
    change mixedMoment B node3517 node3517Labels = _
    exact sound3517 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3558 : mixedVector B (Sum.inr 3558) = Sparse.eval nodeValue3558 (mixedVector B) := by
    change mixedMoment B node3558 node3558Labels = _
    exact sound3558 B hB hF
  have h3565 : mixedVector B (Sum.inr 3565) = Sparse.eval nodeValue3565 (mixedVector B) := by
    change mixedMoment B node3565 node3565Labels = _
    exact sound3565 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h3605 : mixedVector B (Sum.inr 3605) = Sparse.eval nodeValue3605 (mixedVector B) := by
    change mixedMoment B node3605 node3605Labels = _
    exact sound3605 B hB hF
  have h3612 : mixedVector B (Sum.inr 3612) = Sparse.eval nodeValue3612 (mixedVector B) := by
    change mixedMoment B node3612 node3612Labels = _
    exact sound3612 B hB hF
  have h3625 : mixedVector B (Sum.inr 3625) = Sparse.eval nodeValue3625 (mixedVector B) := by
    change mixedMoment B node3625 node3625Labels = _
    exact sound3625 B hB hF
  have h3804 : mixedVector B (Sum.inr 3804) = Sparse.eval nodeValue3804 (mixedVector B) := by
    change mixedMoment B node3804 node3804Labels = _
    exact sound3804 B hB hF
  have h3815 : mixedVector B (Sum.inr 3815) = Sparse.eval nodeValue3815 (mixedVector B) := by
    change mixedMoment B node3815 node3815Labels = _
    exact sound3815 B hB hF
  have h3816 : mixedVector B (Sum.inr 3816) = Sparse.eval nodeValue3816 (mixedVector B) := by
    change mixedMoment B node3816 node3816Labels = _
    exact sound3816 B hB hF
  have h3857 : mixedVector B (Sum.inr 3857) = Sparse.eval nodeValue3857 (mixedVector B) := by
    change mixedMoment B node3857 node3857Labels = _
    exact sound3857 B hB hF
  have h3983 : mixedVector B (Sum.inr 3983) = Sparse.eval nodeValue3983 (mixedVector B) := by
    change mixedMoment B node3983 node3983Labels = _
    exact sound3983 B hB hF
  simpa only [sourceForm2349, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1668, h1669, h1676, h1682, h1714, h2652, h2658, h2670, h2719, h3407, h3413, h3418, h3451, h3454, h3463, h3481, h3517, h3523, h3540, h3558, h3565, h3572, h3605, h3612, h3625, h3804, h3815, h3816, h3857, h3983, reducedSource1913] using sourceEq2349 B hB

theorem rowSound1913 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1913 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1913, numericCheck1913, reducedZero1913 B hB hF, mul_zero]

theorem reducedZero1918 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1918 (mixedVector B) = 0 := by
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4838 : mixedVector B (Sum.inr 4838) = Sparse.eval nodeValue4838 (mixedVector B) := by
    change mixedMoment B node4838 node4838Labels = _
    exact sound4838 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4869 : mixedVector B (Sum.inr 4869) = Sparse.eval nodeValue4869 (mixedVector B) := by
    change mixedMoment B node4869 node4869Labels = _
    exact sound4869 B hB hF
  have h5072 : mixedVector B (Sum.inr 5072) = Sparse.eval nodeValue5072 (mixedVector B) := by
    change mixedMoment B node5072 node5072Labels = _
    exact sound5072 B hB hF
  have h5076 : mixedVector B (Sum.inr 5076) = Sparse.eval nodeValue5076 (mixedVector B) := by
    change mixedMoment B node5076 node5076Labels = _
    exact sound5076 B hB hF
  have h5099 : mixedVector B (Sum.inr 5099) = Sparse.eval nodeValue5099 (mixedVector B) := by
    change mixedMoment B node5099 node5099Labels = _
    exact sound5099 B hB hF
  have h5101 : mixedVector B (Sum.inr 5101) = Sparse.eval nodeValue5101 (mixedVector B) := by
    change mixedMoment B node5101 node5101Labels = _
    exact sound5101 B hB hF
  have h5104 : mixedVector B (Sum.inr 5104) = Sparse.eval nodeValue5104 (mixedVector B) := by
    change mixedMoment B node5104 node5104Labels = _
    exact sound5104 B hB hF
  have h5105 : mixedVector B (Sum.inr 5105) = Sparse.eval nodeValue5105 (mixedVector B) := by
    change mixedMoment B node5105 node5105Labels = _
    exact sound5105 B hB hF
  have h5137 : mixedVector B (Sum.inr 5137) = Sparse.eval nodeValue5137 (mixedVector B) := by
    change mixedMoment B node5137 node5137Labels = _
    exact sound5137 B hB hF
  have h5138 : mixedVector B (Sum.inr 5138) = Sparse.eval nodeValue5138 (mixedVector B) := by
    change mixedMoment B node5138 node5138Labels = _
    exact sound5138 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5150 : mixedVector B (Sum.inr 5150) = Sparse.eval nodeValue5150 (mixedVector B) := by
    change mixedMoment B node5150 node5150Labels = _
    exact sound5150 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168_e B hB hF
  have h5169 : mixedVector B (Sum.inr 5169) = Sparse.eval nodeValue5169 (mixedVector B) := by
    change mixedMoment B node5169 node5169Labels = _
    exact sound5169_e B hB hF
  have h5170 : mixedVector B (Sum.inr 5170) = Sparse.eval nodeValue5170 (mixedVector B) := by
    change mixedMoment B node5170 node5170Labels = _
    exact sound5170 B hB hF
  have h5173 : mixedVector B (Sum.inr 5173) = Sparse.eval nodeValue5173 (mixedVector B) := by
    change mixedMoment B node5173 node5173Labels = _
    exact sound5173 B hB hF
  have h5187 : mixedVector B (Sum.inr 5187) = Sparse.eval nodeValue5187 (mixedVector B) := by
    change mixedMoment B node5187 node5187Labels = _
    exact sound5187 B hB hF
  have h5204 : mixedVector B (Sum.inr 5204) = Sparse.eval nodeValue5204 (mixedVector B) := by
    change mixedMoment B node5204 node5204Labels = _
    exact sound5204 B hB hF
  have h5205 : mixedVector B (Sum.inr 5205) = Sparse.eval nodeValue5205 (mixedVector B) := by
    change mixedMoment B node5205 node5205Labels = _
    exact sound5205 B hB hF
  simpa only [sourceForm2354, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4805, h4838, h4839, h4869, h5072, h5076, h5099, h5101, h5104, h5105, h5137, h5138, h5149, h5150, h5168, h5169, h5170, h5173, h5187, h5204, h5205, reducedSource1918] using sourceEq2354 B hB

theorem rowSound1918 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1918 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1918, numericCheck1918, reducedZero1918 B hB hF, mul_zero]

theorem reducedZero1919 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1919 (mixedVector B) = 0 := by
  have h1156 : mixedVector B (Sum.inr 1156) = Sparse.eval nodeValue1156 (mixedVector B) := by
    change mixedMoment B node1156 node1156Labels = _
    exact sound1156 B hB hF
  have h2353 : mixedVector B (Sum.inr 2353) = Sparse.eval nodeValue2353 (mixedVector B) := by
    change mixedMoment B node2353 node2353Labels = _
    exact sound2353 B hB hF
  have h2553 : mixedVector B (Sum.inr 2553) = Sparse.eval nodeValue2553 (mixedVector B) := by
    change mixedMoment B node2553 node2553Labels = _
    exact sound2553 B hB hF
  have h2566 : mixedVector B (Sum.inr 2566) = Sparse.eval nodeValue2566 (mixedVector B) := by
    change mixedMoment B node2566 node2566Labels = _
    exact sound2566 B hB hF
  have h2587 : mixedVector B (Sum.inr 2587) = Sparse.eval nodeValue2587 (mixedVector B) := by
    change mixedMoment B node2587 node2587Labels = _
    exact sound2587 B hB hF
  have h2590 : mixedVector B (Sum.inr 2590) = Sparse.eval nodeValue2590 (mixedVector B) := by
    change mixedMoment B node2590 node2590Labels = _
    exact sound2590 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2355, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1156, h2353, h2553, h2566, h2587, h2590, h4092, reducedSource1919] using sourceEq2355 B hB

theorem rowSound1919 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1919 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1919, numericCheck1919, reducedZero1919 B hB hF, mul_zero]

theorem sourceRowsAt1904 : MixedData.sourceRows (1904 : Fin 2425) =
    MixedData.row1904 := by decide +kernel

theorem sourceRowsAt1905 : MixedData.sourceRows (1905 : Fin 2425) =
    MixedData.row1905 := by decide +kernel

theorem sourceRowsAt1906 : MixedData.sourceRows (1906 : Fin 2425) =
    MixedData.row1906 := by decide +kernel

theorem sourceRowsAt1907 : MixedData.sourceRows (1907 : Fin 2425) =
    MixedData.row1907 := by decide +kernel

theorem sourceRowsAt1908 : MixedData.sourceRows (1908 : Fin 2425) =
    MixedData.row1908 := by decide +kernel

theorem sourceRowsAt1909 : MixedData.sourceRows (1909 : Fin 2425) =
    MixedData.row1909 := by decide +kernel

theorem sourceRowsAt1910 : MixedData.sourceRows (1910 : Fin 2425) =
    MixedData.row1910 := by decide +kernel

theorem sourceRowsAt1911 : MixedData.sourceRows (1911 : Fin 2425) =
    MixedData.row1911 := by decide +kernel

theorem sourceRowsAt1912 : MixedData.sourceRows (1912 : Fin 2425) =
    MixedData.row1912 := by decide +kernel

theorem sourceRowsAt1913 : MixedData.sourceRows (1913 : Fin 2425) =
    MixedData.row1913 := by decide +kernel

theorem sourceRowsAt1914 : MixedData.sourceRows (1914 : Fin 2425) =
    MixedData.row1914 := by decide +kernel

theorem sourceRowsAt1915 : MixedData.sourceRows (1915 : Fin 2425) =
    MixedData.row1915 := by decide +kernel

theorem sourceRowsAt1916 : MixedData.sourceRows (1916 : Fin 2425) =
    MixedData.row1916 := by decide +kernel

theorem sourceRowsAt1917 : MixedData.sourceRows (1917 : Fin 2425) =
    MixedData.row1917 := by decide +kernel

theorem sourceRowsAt1918 : MixedData.sourceRows (1918 : Fin 2425) =
    MixedData.row1918 := by decide +kernel

theorem sourceRowsAt1919 : MixedData.sourceRows (1919 : Fin 2425) =
    MixedData.row1919 := by decide +kernel

theorem chunkSound119_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 119) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1904 ∨ k.val = 1905 ∨ k.val = 1906 ∨ k.val = 1907 ∨ k.val = 1908 ∨ k.val = 1909 ∨ k.val = 1910 ∨ k.val = 1911 ∨ k.val = 1912 ∨ k.val = 1913 ∨ k.val = 1914 ∨ k.val = 1915 ∨ k.val = 1916 ∨ k.val = 1917 ∨ k.val = 1918 ∨ k.val = 1919 := by omega
  rcases heq with h1904 | h1905 | h1906 | h1907 | h1908 | h1909 | h1910 | h1911 | h1912 | h1913 | h1914 | h1915 | h1916 | h1917 | h1918 | h1919
  · have he : k = (1904 : Fin 2425) := Fin.ext h1904
    subst k
    rw [sourceRowsAt1904]
    exact rowSound1904_e B hB hF
  · have he : k = (1905 : Fin 2425) := Fin.ext h1905
    subst k
    rw [sourceRowsAt1905]
    exact rowSound1905_e B hB hF
  · have he : k = (1906 : Fin 2425) := Fin.ext h1906
    subst k
    rw [sourceRowsAt1906]
    exact rowSound1906_e B hB hF
  · have he : k = (1907 : Fin 2425) := Fin.ext h1907
    subst k
    rw [sourceRowsAt1907]
    exact rowSound1907_e B hB hF
  · have he : k = (1908 : Fin 2425) := Fin.ext h1908
    subst k
    rw [sourceRowsAt1908]
    exact rowSound1908_e B hB hF
  · have he : k = (1909 : Fin 2425) := Fin.ext h1909
    subst k
    rw [sourceRowsAt1909]
    exact rowSound1909 B hB hF
  · have he : k = (1910 : Fin 2425) := Fin.ext h1910
    subst k
    rw [sourceRowsAt1910]
    exact rowSound1910_e B hB hF
  · have he : k = (1911 : Fin 2425) := Fin.ext h1911
    subst k
    rw [sourceRowsAt1911]
    exact rowSound1911_e B hB hF
  · have he : k = (1912 : Fin 2425) := Fin.ext h1912
    subst k
    rw [sourceRowsAt1912]
    exact rowSound1912_e B hB hF
  · have he : k = (1913 : Fin 2425) := Fin.ext h1913
    subst k
    rw [sourceRowsAt1913]
    exact rowSound1913 B hB hF
  · have he : k = (1914 : Fin 2425) := Fin.ext h1914
    subst k
    rw [sourceRowsAt1914]
    exact rowSound1914_e B hB hF
  · have he : k = (1915 : Fin 2425) := Fin.ext h1915
    subst k
    rw [sourceRowsAt1915]
    exact rowSound1915_e B hB hF
  · have he : k = (1916 : Fin 2425) := Fin.ext h1916
    subst k
    rw [sourceRowsAt1916]
    exact rowSound1916_e B hB hF
  · have he : k = (1917 : Fin 2425) := Fin.ext h1917
    subst k
    rw [sourceRowsAt1917]
    exact rowSound1917_e B hB hF
  · have he : k = (1918 : Fin 2425) := Fin.ext h1918
    subst k
    rw [sourceRowsAt1918]
    exact rowSound1918 B hB hF
  · have he : k = (1919 : Fin 2425) := Fin.ext h1919
    subst k
    rw [sourceRowsAt1919]
    exact rowSound1919 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119_e_oai
