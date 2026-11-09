-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound38_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:13:10.779904+00:00
-- url     : https://prove2.me/submissions/21f90e62-eaf8-4eff-bf83-4e2da95981d8

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3087_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3100_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3203_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3223_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5292_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_reducedZero621_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound608_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound612_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound613_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound614_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11664 raw11664Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw11664 raw11664Labels = mixedMoment B raw11664step0 raw11664step0Labels := by
      have ha : raw11664step0 = (fun i j => raw11664 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11664step0 raw11664; decide +kernel
      have hl : raw11664step0Labels = raw11664Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11664 raw11664Labels permutation180 permutation7
    mixedMoment B raw11664step0 raw11664step0Labels = mixedMoment B raw11664step1 raw11664step1Labels := by
      have ha : raw11664step1 = raw11664step0 := by apply Matrix.ext; unfold raw11664step1 raw11664step0; decide +kernel
      have hl : raw11664step0Labels = labelEmbedding10 ∘ raw11664step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11664step0 raw11664step0Labels raw11664step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

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

theorem canonical11670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11670 raw11670Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw11670 raw11670Labels = mixedMoment B raw11670step0 raw11670step0Labels := by
      have ha : raw11670step0 = (fun i j => raw11670 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11670step0 raw11670; decide +kernel
      have hl : raw11670step0Labels = raw11670Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11670 raw11670Labels permutation160 permutation4
    mixedMoment B raw11670step0 raw11670step0Labels = mixedMoment B raw11670step1 raw11670step1Labels := by
      have ha : raw11670step1 = -raw11670step0 := by apply Matrix.ext; change ∀ i j, raw11670step1 i j = -(raw11670step0 i j); unfold raw11670step1 raw11670step0; decide +kernel
      have hl : raw11670step1Labels = raw11670step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11670step1 raw11670step1Labels = mixedMoment B raw11670step2 raw11670step2Labels := by
      have ha : raw11670step2 = raw11670step1 := by apply Matrix.ext; unfold raw11670step2 raw11670step1; decide +kernel
      have hl : raw11670step1Labels = labelEmbedding7 ∘ raw11670step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11670step1 raw11670step1Labels raw11670step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4795 node4795Labels := by rfl

theorem canonical11671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11671 raw11671Labels = mixedMoment B node5230 node5230Labels := by
  calc
    mixedMoment B raw11671 raw11671Labels = mixedMoment B raw11671step0 raw11671step0Labels := by
      have ha : raw11671step0 = (fun i j => raw11671 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11671step0 raw11671; decide +kernel
      have hl : raw11671step0Labels = raw11671Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11671 raw11671Labels permutation152 permutation6
    mixedMoment B raw11671step0 raw11671step0Labels = mixedMoment B raw11671step1 raw11671step1Labels := by
      have ha : raw11671step1 = raw11671step0 := by apply Matrix.ext; unfold raw11671step1 raw11671step0; decide +kernel
      have hl : raw11671step0Labels = labelEmbedding9 ∘ raw11671step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11671step0 raw11671step0Labels raw11671step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5230 node5230Labels := by rfl

theorem canonical11672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11672 raw11672Labels = mixedMoment B node5262 node5262Labels := by
  calc
    mixedMoment B raw11672 raw11672Labels = mixedMoment B raw11672step0 raw11672step0Labels := by
      have ha : raw11672step0 = (fun i j => raw11672 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11672step0 raw11672; decide +kernel
      have hl : raw11672step0Labels = raw11672Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11672 raw11672Labels permutation152 permutation6
    mixedMoment B raw11672step0 raw11672step0Labels = mixedMoment B raw11672step1 raw11672step1Labels := by
      have ha : raw11672step1 = raw11672step0 := by apply Matrix.ext; unfold raw11672step1 raw11672step0; decide +kernel
      have hl : raw11672step0Labels = labelEmbedding9 ∘ raw11672step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11672step0 raw11672step0Labels raw11672step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5262 node5262Labels := by rfl

theorem canonical11673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11673 raw11673Labels = mixedMoment B node5262 node5262Labels := by
  calc
    mixedMoment B raw11673 raw11673Labels = mixedMoment B raw11673step0 raw11673step0Labels := by
      have ha : raw11673step0 = (fun i j => raw11673 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11673step0 raw11673; decide +kernel
      have hl : raw11673step0Labels = raw11673Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11673 raw11673Labels permutation154 permutation6
    mixedMoment B raw11673step0 raw11673step0Labels = mixedMoment B raw11673step1 raw11673step1Labels := by
      have ha : raw11673step1 = raw11673step0 := by apply Matrix.ext; unfold raw11673step1 raw11673step0; decide +kernel
      have hl : raw11673step0Labels = labelEmbedding9 ∘ raw11673step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11673step0 raw11673step0Labels raw11673step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5262 node5262Labels := by rfl

theorem canonical11679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11679 raw11679Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw11679 raw11679Labels = mixedMoment B raw11679step0 raw11679step0Labels := by
      have ha : raw11679step0 = (fun i j => raw11679 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11679step0 raw11679; decide +kernel
      have hl : raw11679step0Labels = raw11679Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11679 raw11679Labels permutation154 permutation6
    mixedMoment B raw11679step0 raw11679step0Labels = mixedMoment B raw11679step1 raw11679step1Labels := by
      have ha : raw11679step1 = raw11679step0 := by apply Matrix.ext; unfold raw11679step1 raw11679step0; decide +kernel
      have hl : raw11679step0Labels = labelEmbedding9 ∘ raw11679step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11679step0 raw11679step0Labels raw11679step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical11684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11684 raw11684Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw11684 raw11684Labels = mixedMoment B raw11684step0 raw11684step0Labels := by
      have ha : raw11684step0 = (fun i j => raw11684 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11684step0 raw11684; decide +kernel
      have hl : raw11684step0Labels = raw11684Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11684 raw11684Labels permutation152 permutation6
    mixedMoment B raw11684step0 raw11684step0Labels = mixedMoment B raw11684step1 raw11684step1Labels := by
      have ha : raw11684step1 = raw11684step0 := by apply Matrix.ext; unfold raw11684step1 raw11684step0; decide +kernel
      have hl : raw11684step0Labels = labelEmbedding9 ∘ raw11684step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11684step0 raw11684step0Labels raw11684step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11862 raw11862Labels = mixedMoment B node2730 node2730Labels := by
  calc
    _ = mixedMoment B node2730 node2730Labels := by rfl

theorem canonical11863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11863 raw11863Labels = mixedMoment B node3812 node3812Labels := by
  calc
    _ = mixedMoment B node3812 node3812Labels := by rfl

theorem canonical11864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11864 raw11864Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw11864 raw11864Labels = mixedMoment B raw11864step0 raw11864step0Labels := by
      have ha : raw11864step0 = (fun i j => raw11864 (permutation416 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11864step0 raw11864; decide +kernel
      have hl : raw11864step0Labels = raw11864Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11864 raw11864Labels permutation416 permutation4
    mixedMoment B raw11864step0 raw11864step0Labels = mixedMoment B raw11864step1 raw11864step1Labels := by
      have ha : raw11864step1 = -raw11864step0 := by apply Matrix.ext; change ∀ i j, raw11864step1 i j = -(raw11864step0 i j); unfold raw11864step1 raw11864step0; decide +kernel
      have hl : raw11864step1Labels = raw11864step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2730 node2730Labels := by rfl

theorem canonical11865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11865 raw11865Labels = mixedMoment B node3906 node3906Labels := by
  calc
    mixedMoment B raw11865 raw11865Labels = mixedMoment B raw11865step0 raw11865step0Labels := by
      have hz : ∀ j, raw11865 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11865step0 = (fun i j => raw11865 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11865step0 raw11865; decide +kernel
      have hl : raw11865step0Labels = raw11865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11865 raw11865Labels permutation434 hz
    _ = mixedMoment B node3906 node3906Labels := by rfl

theorem canonical11866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11866 raw11866Labels = mixedMoment B node3906 node3906Labels := by
  calc
    mixedMoment B raw11866 raw11866Labels = mixedMoment B raw11866step0 raw11866step0Labels := by
      have hz : ∀ j, raw11866 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11866step0 = (fun i j => raw11866 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11866step0 raw11866; decide +kernel
      have hl : raw11866step0Labels = raw11866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11866 raw11866Labels permutation520 hz
    _ = mixedMoment B node3906 node3906Labels := by rfl

theorem canonical11867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11867 raw11867Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw11867 raw11867Labels = mixedMoment B raw11867step0 raw11867step0Labels := by
      have ha : raw11867step0 = (fun i j => raw11867 (permutation416 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11867step0 raw11867; decide +kernel
      have hl : raw11867step0Labels = raw11867Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11867 raw11867Labels permutation416 permutation4
    mixedMoment B raw11867step0 raw11867step0Labels = mixedMoment B raw11867step1 raw11867step1Labels := by
      have ha : raw11867step1 = -raw11867step0 := by apply Matrix.ext; change ∀ i j, raw11867step1 i j = -(raw11867step0 i j); unfold raw11867step1 raw11867step0; decide +kernel
      have hl : raw11867step1Labels = raw11867step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3812 node3812Labels := by rfl

theorem canonical11868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11868 raw11868Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw11868 raw11868Labels = mixedMoment B raw11868step0 raw11868step0Labels := by
      have hz : ∀ j, raw11868 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11868step0 = (fun i j => raw11868 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11868step0 raw11868; decide +kernel
      have hl : raw11868step0Labels = raw11868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11868 raw11868Labels permutation520 hz
    mixedMoment B raw11868step0 raw11868step0Labels = mixedMoment B raw11868step1 raw11868step1Labels := by
      have hz : ∀ j, raw11868step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11868step1 = (fun i j => raw11868step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11868step1 raw11868step0; decide +kernel
      have hl : raw11868step1Labels = raw11868step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11868step0 raw11868step0Labels permutation104 hz
    mixedMoment B raw11868step1 raw11868step1Labels = mixedMoment B raw11868step2 raw11868step2Labels := by
      have ha : raw11868step2 = (fun i j => raw11868step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw11868step2 raw11868step1; decide +kernel
      have hl : raw11868step2Labels = raw11868step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11868step1 raw11868step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical11869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11869 raw11869Labels = mixedMoment B node1276 node1276Labels := by
  calc
    mixedMoment B raw11869 raw11869Labels = mixedMoment B raw11869step0 raw11869step0Labels := by
      have ha : raw11869step0 = (fun i j => raw11869 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11869step0 raw11869; decide +kernel
      have hl : raw11869step0Labels = raw11869Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11869 raw11869Labels permutation176 permutation2
    _ = mixedMoment B node1276 node1276Labels := by rfl

theorem canonical11874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11874 raw11874Labels = mixedMoment B node2645 node2645Labels := by
  calc
    mixedMoment B raw11874 raw11874Labels = mixedMoment B raw11874step0 raw11874step0Labels := by
      have ha : raw11874step0 = (fun i j => raw11874 (permutation364 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11874step0 raw11874; decide +kernel
      have hl : raw11874step0Labels = raw11874Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11874 raw11874Labels permutation364 permutation4
    mixedMoment B raw11874step0 raw11874step0Labels = mixedMoment B raw11874step1 raw11874step1Labels := by
      have ha : raw11874step1 = -raw11874step0 := by apply Matrix.ext; change ∀ i j, raw11874step1 i j = -(raw11874step0 i j); unfold raw11874step1 raw11874step0; decide +kernel
      have hl : raw11874step1Labels = raw11874step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2645 node2645Labels := by rfl

theorem canonical11875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11875 raw11875Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw11875 raw11875Labels = mixedMoment B raw11875step0 raw11875step0Labels := by
      have hz : ∀ j, raw11875 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11875step0 = (fun i j => raw11875 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11875step0 raw11875; decide +kernel
      have hl : raw11875step0Labels = raw11875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11875 raw11875Labels permutation434 hz
    mixedMoment B raw11875step0 raw11875step0Labels = mixedMoment B raw11875step1 raw11875step1Labels := by
      have ha : raw11875step1 = (fun i j => raw11875step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11875step1 raw11875step0; decide +kernel
      have hl : raw11875step1Labels = raw11875step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11875step0 raw11875step0Labels permutation38 permutation2
    _ = mixedMoment B node2773 node2773Labels := by rfl

theorem canonical11876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11876 raw11876Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw11876 raw11876Labels = mixedMoment B raw11876step0 raw11876step0Labels := by
      have hz : ∀ j, raw11876 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11876step0 = (fun i j => raw11876 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11876step0 raw11876; decide +kernel
      have hl : raw11876step0Labels = raw11876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11876 raw11876Labels permutation520 hz
    mixedMoment B raw11876step0 raw11876step0Labels = mixedMoment B raw11876step1 raw11876step1Labels := by
      have ha : raw11876step1 = (fun i j => raw11876step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11876step1 raw11876step0; decide +kernel
      have hl : raw11876step1Labels = raw11876step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11876step0 raw11876step0Labels permutation38 permutation2
    _ = mixedMoment B node2773 node2773Labels := by rfl

theorem canonical11877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11877 raw11877Labels = mixedMoment B node2757 node2757Labels := by
  calc
    mixedMoment B raw11877 raw11877Labels = mixedMoment B raw11877step0 raw11877step0Labels := by
      have ha : raw11877step0 = (fun i j => raw11877 (permutation252 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11877step0 raw11877; decide +kernel
      have hl : raw11877step0Labels = raw11877Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11877 raw11877Labels permutation252 permutation2
    _ = mixedMoment B node2757 node2757Labels := by rfl

theorem canonical11878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11878 raw11878Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw11878 raw11878Labels = mixedMoment B raw11878step0 raw11878step0Labels := by
      have ha : raw11878step0 = (fun i j => raw11878 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11878step0 raw11878; decide +kernel
      have hl : raw11878step0Labels = raw11878Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11878 raw11878Labels permutation161 permutation2
    _ = mixedMoment B node2508 node2508Labels := by rfl

theorem canonical11879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11879 raw11879Labels = mixedMoment B node2494 node2494Labels := by
  calc
    mixedMoment B raw11879 raw11879Labels = mixedMoment B raw11879step0 raw11879step0Labels := by
      have ha : raw11879step0 = (fun i j => raw11879 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11879step0 raw11879; decide +kernel
      have hl : raw11879step0Labels = raw11879Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11879 raw11879Labels permutation155 permutation2
    _ = mixedMoment B node2494 node2494Labels := by rfl

theorem canonical11880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11880 raw11880Labels = mixedMoment B node2494 node2494Labels := by
  calc
    mixedMoment B raw11880 raw11880Labels = mixedMoment B raw11880step0 raw11880step0Labels := by
      have ha : raw11880step0 = (fun i j => raw11880 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11880step0 raw11880; decide +kernel
      have hl : raw11880step0Labels = raw11880Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11880 raw11880Labels permutation153 permutation2
    _ = mixedMoment B node2494 node2494Labels := by rfl

theorem canonical11881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11881 raw11881Labels = mixedMoment B node2493 node2493Labels := by
  calc
    _ = mixedMoment B node2493 node2493Labels := by rfl

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

theorem canonical11972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11972 raw11972Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw11972 raw11972Labels = mixedMoment B raw11972step0 raw11972step0Labels := by
      have ha : raw11972step0 = (fun i j => raw11972 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11972step0 raw11972; decide +kernel
      have hl : raw11972step0Labels = raw11972Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11972 raw11972Labels permutation180 permutation2
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical11973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11973 raw11973Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw11973 raw11973Labels = mixedMoment B raw11973step0 raw11973step0Labels := by
      have ha : raw11973step0 = (fun i j => raw11973 (permutation426 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11973step0 raw11973; decide +kernel
      have hl : raw11973step0Labels = raw11973Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11973 raw11973Labels permutation426 permutation4
    _ = mixedMoment B node3846 node3846Labels := by rfl

theorem canonical11974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11974 raw11974Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw11974 raw11974Labels = mixedMoment B raw11974step0 raw11974step0Labels := by
      have ha : raw11974step0 = (fun i j => raw11974 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11974step0 raw11974; decide +kernel
      have hl : raw11974step0Labels = raw11974Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11974 raw11974Labels permutation180 permutation2
    _ = mixedMoment B node3957 node3957Labels := by rfl

theorem canonical11975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11975 raw11975Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw11975 raw11975Labels = mixedMoment B raw11975step0 raw11975step0Labels := by
      have ha : raw11975step0 = (fun i j => raw11975 (permutation428 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11975step0 raw11975; decide +kernel
      have hl : raw11975step0Labels = raw11975Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11975 raw11975Labels permutation428 permutation4
    _ = mixedMoment B node3849 node3849Labels := by rfl

theorem canonical11976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11976 raw11976Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw11976 raw11976Labels = mixedMoment B raw11976step0 raw11976step0Labels := by
      have ha : raw11976step0 = (fun i j => raw11976 (permutation424 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11976step0 raw11976; decide +kernel
      have hl : raw11976step0Labels = raw11976Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11976 raw11976Labels permutation424 permutation4
    _ = mixedMoment B node3849 node3849Labels := by rfl

theorem canonical11977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11977 raw11977Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw11977 raw11977Labels = mixedMoment B raw11977step0 raw11977step0Labels := by
      have hz : ∀ j, raw11977 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11977step0 = (fun i j => raw11977 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11977step0 raw11977; decide +kernel
      have hl : raw11977step0Labels = raw11977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11977 raw11977Labels permutation590 hz
    mixedMoment B raw11977step0 raw11977step0Labels = mixedMoment B raw11977step1 raw11977step1Labels := by
      have ha : raw11977step1 = (fun i j => raw11977step0 (permutation96 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11977step1 raw11977step0; decide +kernel
      have hl : raw11977step1Labels = raw11977step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11977step0 raw11977step0Labels permutation96 permutation4
    _ = mixedMoment B node3910 node3910Labels := by rfl

theorem canonical11978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11978 raw11978Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw11978 raw11978Labels = mixedMoment B raw11978step0 raw11978step0Labels := by
      have hz : ∀ j, raw11978 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11978step0 = (fun i j => raw11978 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11978step0 raw11978; decide +kernel
      have hl : raw11978step0Labels = raw11978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11978 raw11978Labels permutation590 hz
    mixedMoment B raw11978step0 raw11978step0Labels = mixedMoment B raw11978step1 raw11978step1Labels := by
      have ha : raw11978step1 = (fun i j => raw11978step0 (permutation80 i) (permutation0 j)) := by apply Matrix.ext; unfold raw11978step1 raw11978step0; decide +kernel
      have hl : raw11978step1Labels = raw11978step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11978step0 raw11978step0Labels permutation80 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical11979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11979 raw11979Labels = mixedMoment B node1366 node1366Labels := by
  calc
    mixedMoment B raw11979 raw11979Labels = mixedMoment B raw11979step0 raw11979step0Labels := by
      have ha : raw11979step0 = (fun i j => raw11979 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11979step0 raw11979; decide +kernel
      have hl : raw11979step0Labels = raw11979Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11979 raw11979Labels permutation194 permutation2
    _ = mixedMoment B node1366 node1366Labels := by rfl

theorem canonical11980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11980 raw11980Labels = mixedMoment B node1421 node1421Labels := by
  calc
    mixedMoment B raw11980 raw11980Labels = mixedMoment B raw11980step0 raw11980step0Labels := by
      have ha : raw11980step0 = (fun i j => raw11980 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11980step0 raw11980; decide +kernel
      have hl : raw11980step0Labels = raw11980Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11980 raw11980Labels permutation156 permutation2
    _ = mixedMoment B node1421 node1421Labels := by rfl

theorem canonical11981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11981 raw11981Labels = mixedMoment B node1358 node1358Labels := by
  calc
    mixedMoment B raw11981 raw11981Labels = mixedMoment B raw11981step0 raw11981step0Labels := by
      have ha : raw11981step0 = (fun i j => raw11981 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11981step0 raw11981; decide +kernel
      have hl : raw11981step0Labels = raw11981Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11981 raw11981Labels permutation181 permutation2
    _ = mixedMoment B node1358 node1358Labels := by rfl

theorem canonical11982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11982 raw11982Labels = mixedMoment B node1358 node1358Labels := by
  calc
    mixedMoment B raw11982 raw11982Labels = mixedMoment B raw11982step0 raw11982step0Labels := by
      have ha : raw11982step0 = (fun i j => raw11982 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11982step0 raw11982; decide +kernel
      have hl : raw11982step0Labels = raw11982Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11982 raw11982Labels permutation180 permutation2
    _ = mixedMoment B node1358 node1358Labels := by rfl

theorem canonical11983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11983 raw11983Labels = mixedMoment B node1360 node1360Labels := by
  calc
    mixedMoment B raw11983 raw11983Labels = mixedMoment B raw11983step0 raw11983step0Labels := by
      have ha : raw11983step0 = (fun i j => raw11983 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11983step0 raw11983; decide +kernel
      have hl : raw11983step0Labels = raw11983Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11983 raw11983Labels permutation176 permutation2
    _ = mixedMoment B node1360 node1360Labels := by rfl

theorem canonical11984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11984 raw11984Labels = mixedMoment B node2880 node2880Labels := by
  calc
    mixedMoment B raw11984 raw11984Labels = mixedMoment B raw11984step0 raw11984step0Labels := by
      have ha : raw11984step0 = (fun i j => raw11984 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11984step0 raw11984; decide +kernel
      have hl : raw11984step0Labels = raw11984Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11984 raw11984Labels permutation194 permutation2
    _ = mixedMoment B node2880 node2880Labels := by rfl

theorem canonical11985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11985 raw11985Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw11985 raw11985Labels = mixedMoment B raw11985step0 raw11985step0Labels := by
      have ha : raw11985step0 = (fun i j => raw11985 (permutation186 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11985step0 raw11985; decide +kernel
      have hl : raw11985step0Labels = raw11985Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11985 raw11985Labels permutation186 permutation2
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical11986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11986 raw11986Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw11986 raw11986Labels = mixedMoment B raw11986step0 raw11986step0Labels := by
      have ha : raw11986step0 = (fun i j => raw11986 (permutation192 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11986step0 raw11986; decide +kernel
      have hl : raw11986step0Labels = raw11986Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11986 raw11986Labels permutation192 permutation2
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical11987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11987 raw11987Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw11987 raw11987Labels = mixedMoment B raw11987step0 raw11987step0Labels := by
      have hz : ∀ j, raw11987 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11987step0 = (fun i j => raw11987 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11987step0 raw11987; decide +kernel
      have hl : raw11987step0Labels = raw11987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11987 raw11987Labels permutation590 hz
    mixedMoment B raw11987step0 raw11987step0Labels = mixedMoment B raw11987step1 raw11987step1Labels := by
      have ha : raw11987step1 = (fun i j => raw11987step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11987step1 raw11987step0; decide +kernel
      have hl : raw11987step1Labels = raw11987step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11987step0 raw11987step0Labels permutation38 permutation2
    _ = mixedMoment B node3053 node3053Labels := by rfl

theorem canonical11992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11992 raw11992Labels = mixedMoment B node2862 node2862Labels := by
  calc
    mixedMoment B raw11992 raw11992Labels = mixedMoment B raw11992step0 raw11992step0Labels := by
      have ha : raw11992step0 = (fun i j => raw11992 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11992step0 raw11992; decide +kernel
      have hl : raw11992step0Labels = raw11992Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11992 raw11992Labels permutation181 permutation2
    _ = mixedMoment B node2862 node2862Labels := by rfl

theorem canonical11993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11993 raw11993Labels = mixedMoment B node2862 node2862Labels := by
  calc
    mixedMoment B raw11993 raw11993Labels = mixedMoment B raw11993step0 raw11993step0Labels := by
      have ha : raw11993step0 = (fun i j => raw11993 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11993step0 raw11993; decide +kernel
      have hl : raw11993step0Labels = raw11993Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11993 raw11993Labels permutation180 permutation2
    _ = mixedMoment B node2862 node2862Labels := by rfl

theorem canonical11994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11994 raw11994Labels = mixedMoment B node2864 node2864Labels := by
  calc
    mixedMoment B raw11994 raw11994Labels = mixedMoment B raw11994step0 raw11994step0Labels := by
      have ha : raw11994step0 = (fun i j => raw11994 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11994step0 raw11994; decide +kernel
      have hl : raw11994step0Labels = raw11994Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11994 raw11994Labels permutation176 permutation2
    _ = mixedMoment B node2864 node2864Labels := by rfl

theorem canonical11995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11995 raw11995Labels = mixedMoment B node2573 node2573Labels := by
  calc
    mixedMoment B raw11995 raw11995Labels = mixedMoment B raw11995step0 raw11995step0Labels := by
      have ha : raw11995step0 = (fun i j => raw11995 (permutation431 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11995step0 raw11995; decide +kernel
      have hl : raw11995step0Labels = raw11995Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11995 raw11995Labels permutation431 permutation4
    _ = mixedMoment B node2573 node2573Labels := by rfl

theorem canonical11996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11996 raw11996Labels = mixedMoment B node3029 node3029Labels := by
  calc
    mixedMoment B raw11996 raw11996Labels = mixedMoment B raw11996step0 raw11996step0Labels := by
      have ha : raw11996step0 = (fun i j => raw11996 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11996step0 raw11996; decide +kernel
      have hl : raw11996step0Labels = raw11996Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11996 raw11996Labels permutation177 permutation2
    _ = mixedMoment B node3029 node3029Labels := by rfl

theorem canonical11997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11997 raw11997Labels = mixedMoment B node3030 node3030Labels := by
  calc
    mixedMoment B raw11997 raw11997Labels = mixedMoment B raw11997step0 raw11997step0Labels := by
      have ha : raw11997step0 = (fun i j => raw11997 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11997step0 raw11997; decide +kernel
      have hl : raw11997step0Labels = raw11997Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11997 raw11997Labels permutation176 permutation2
    _ = mixedMoment B node3030 node3030Labels := by rfl

theorem canonical11998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11998 raw11998Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw11998 raw11998Labels = mixedMoment B raw11998step0 raw11998step0Labels := by
      have ha : raw11998step0 = (fun i j => raw11998 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11998step0 raw11998; decide +kernel
      have hl : raw11998step0Labels = raw11998Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11998 raw11998Labels permutation180 permutation7
    mixedMoment B raw11998step0 raw11998step0Labels = mixedMoment B raw11998step1 raw11998step1Labels := by
      have ha : raw11998step1 = raw11998step0 := by apply Matrix.ext; unfold raw11998step1 raw11998step0; decide +kernel
      have hl : raw11998step0Labels = labelEmbedding10 ∘ raw11998step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11998step0 raw11998step0Labels raw11998step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

theorem canonical11999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11999 raw11999Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw11999 raw11999Labels = mixedMoment B raw11999step0 raw11999step0Labels := by
      have ha : raw11999step0 = (fun i j => raw11999 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11999step0 raw11999; decide +kernel
      have hl : raw11999step0Labels = raw11999Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11999 raw11999Labels permutation181 permutation7
    mixedMoment B raw11999step0 raw11999step0Labels = mixedMoment B raw11999step1 raw11999step1Labels := by
      have ha : raw11999step1 = raw11999step0 := by apply Matrix.ext; unfold raw11999step1 raw11999step0; decide +kernel
      have hl : raw11999step0Labels = labelEmbedding10 ∘ raw11999step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11999step0 raw11999step0Labels raw11999step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

theorem canonical12000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12000 raw12000Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw12000 raw12000Labels = mixedMoment B raw12000step0 raw12000step0Labels := by
      have ha : raw12000step0 = (fun i j => raw12000 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12000step0 raw12000; decide +kernel
      have hl : raw12000step0Labels = raw12000Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12000 raw12000Labels permutation180 permutation7
    mixedMoment B raw12000step0 raw12000step0Labels = mixedMoment B raw12000step1 raw12000step1Labels := by
      have ha : raw12000step1 = raw12000step0 := by apply Matrix.ext; unfold raw12000step1 raw12000step0; decide +kernel
      have hl : raw12000step0Labels = labelEmbedding10 ∘ raw12000step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12000step0 raw12000step0Labels raw12000step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

theorem canonical12001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12001 raw12001Labels = mixedMoment B node5227 node5227Labels := by
  calc
    mixedMoment B raw12001 raw12001Labels = mixedMoment B raw12001step0 raw12001step0Labels := by
      have ha : raw12001step0 = (fun i j => raw12001 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12001step0 raw12001; decide +kernel
      have hl : raw12001step0Labels = raw12001Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12001 raw12001Labels permutation176 permutation7
    mixedMoment B raw12001step0 raw12001step0Labels = mixedMoment B raw12001step1 raw12001step1Labels := by
      have ha : raw12001step1 = raw12001step0 := by apply Matrix.ext; unfold raw12001step1 raw12001step0; decide +kernel
      have hl : raw12001step0Labels = labelEmbedding10 ∘ raw12001step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12001step0 raw12001step0Labels raw12001step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5227 node5227Labels := by rfl

theorem canonical12002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12002 raw12002Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw12002 raw12002Labels = mixedMoment B raw12002step0 raw12002step0Labels := by
      have hz : ∀ j, raw12002 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12002step0 = (fun i j => raw12002 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12002step0 raw12002; decide +kernel
      have hl : raw12002step0Labels = raw12002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12002 raw12002Labels permutation265 hz
    mixedMoment B raw12002step0 raw12002step0Labels = mixedMoment B raw12002step1 raw12002step1Labels := by
      have ha : raw12002step1 = (fun i j => raw12002step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12002step1 raw12002step0; decide +kernel
      have hl : raw12002step1Labels = raw12002step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12002step0 raw12002step0Labels permutation41 permutation4
    mixedMoment B raw12002step1 raw12002step1Labels = mixedMoment B raw12002step2 raw12002step2Labels := by
      have ha : raw12002step2 = -raw12002step1 := by apply Matrix.ext; change ∀ i j, raw12002step2 i j = -(raw12002step1 i j); unfold raw12002step2 raw12002step1; decide +kernel
      have hl : raw12002step2Labels = raw12002step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12002step2 raw12002step2Labels = mixedMoment B raw12002step3 raw12002step3Labels := by
      have ha : raw12002step3 = raw12002step2 := by apply Matrix.ext; unfold raw12002step3 raw12002step2; decide +kernel
      have hl : raw12002step2Labels = labelEmbedding7 ∘ raw12002step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12002step2 raw12002step2Labels raw12002step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical12003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12003 raw12003Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw12003 raw12003Labels = mixedMoment B raw12003step0 raw12003step0Labels := by
      have hz : ∀ j, raw12003 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12003step0 = (fun i j => raw12003 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12003step0 raw12003; decide +kernel
      have hl : raw12003step0Labels = raw12003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12003 raw12003Labels permutation265 hz
    mixedMoment B raw12003step0 raw12003step0Labels = mixedMoment B raw12003step1 raw12003step1Labels := by
      have ha : raw12003step1 = (fun i j => raw12003step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12003step1 raw12003step0; decide +kernel
      have hl : raw12003step1Labels = raw12003step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12003step0 raw12003step0Labels permutation32 permutation6
    mixedMoment B raw12003step1 raw12003step1Labels = mixedMoment B raw12003step2 raw12003step2Labels := by
      have ha : raw12003step2 = raw12003step1 := by apply Matrix.ext; unfold raw12003step2 raw12003step1; decide +kernel
      have hl : raw12003step1Labels = labelEmbedding9 ∘ raw12003step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12003step1 raw12003step1Labels raw12003step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

theorem canonical12004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12004 raw12004Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw12004 raw12004Labels = mixedMoment B raw12004step0 raw12004step0Labels := by
      have hz : ∀ j, raw12004 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12004step0 = (fun i j => raw12004 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12004step0 raw12004; decide +kernel
      have hl : raw12004step0Labels = raw12004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12004 raw12004Labels permutation265 hz
    mixedMoment B raw12004step0 raw12004step0Labels = mixedMoment B raw12004step1 raw12004step1Labels := by
      have ha : raw12004step1 = (fun i j => raw12004step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12004step1 raw12004step0; decide +kernel
      have hl : raw12004step1Labels = raw12004step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12004step0 raw12004step0Labels permutation34 permutation6
    mixedMoment B raw12004step1 raw12004step1Labels = mixedMoment B raw12004step2 raw12004step2Labels := by
      have ha : raw12004step2 = raw12004step1 := by apply Matrix.ext; unfold raw12004step2 raw12004step1; decide +kernel
      have hl : raw12004step1Labels = labelEmbedding9 ∘ raw12004step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12004step1 raw12004step1Labels raw12004step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

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

theorem canonical12006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12006 raw12006Labels = mixedMoment B node4793 node4793Labels := by
  calc
    mixedMoment B raw12006 raw12006Labels = mixedMoment B raw12006step0 raw12006step0Labels := by
      have ha : raw12006step0 = (fun i j => raw12006 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12006step0 raw12006; decide +kernel
      have hl : raw12006step0Labels = raw12006Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12006 raw12006Labels permutation161 permutation4
    mixedMoment B raw12006step0 raw12006step0Labels = mixedMoment B raw12006step1 raw12006step1Labels := by
      have ha : raw12006step1 = -raw12006step0 := by apply Matrix.ext; change ∀ i j, raw12006step1 i j = -(raw12006step0 i j); unfold raw12006step1 raw12006step0; decide +kernel
      have hl : raw12006step1Labels = raw12006step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12006step1 raw12006step1Labels = mixedMoment B raw12006step2 raw12006step2Labels := by
      have ha : raw12006step2 = raw12006step1 := by apply Matrix.ext; unfold raw12006step2 raw12006step1; decide +kernel
      have hl : raw12006step1Labels = labelEmbedding7 ∘ raw12006step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12006step1 raw12006step1Labels raw12006step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4793 node4793Labels := by rfl

theorem canonical12007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12007 raw12007Labels = mixedMoment B node4794 node4794Labels := by
  calc
    mixedMoment B raw12007 raw12007Labels = mixedMoment B raw12007step0 raw12007step0Labels := by
      have ha : raw12007step0 = (fun i j => raw12007 (permutation426 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12007step0 raw12007; decide +kernel
      have hl : raw12007step0Labels = raw12007Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12007 raw12007Labels permutation426 permutation5
    mixedMoment B raw12007step0 raw12007step0Labels = mixedMoment B raw12007step1 raw12007step1Labels := by
      have ha : raw12007step1 = raw12007step0 := by apply Matrix.ext; unfold raw12007step1 raw12007step0; decide +kernel
      have hl : raw12007step0Labels = labelEmbedding8 ∘ raw12007step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12007step0 raw12007step0Labels raw12007step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4794 node4794Labels := by rfl

theorem canonical12008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12008 raw12008Labels = mixedMoment B node4806 node4806Labels := by
  calc
    mixedMoment B raw12008 raw12008Labels = mixedMoment B raw12008step0 raw12008step0Labels := by
      have ha : raw12008step0 = (fun i j => raw12008 (permutation431 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12008step0 raw12008; decide +kernel
      have hl : raw12008step0Labels = raw12008Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12008 raw12008Labels permutation431 permutation5
    mixedMoment B raw12008step0 raw12008step0Labels = mixedMoment B raw12008step1 raw12008step1Labels := by
      have ha : raw12008step1 = raw12008step0 := by apply Matrix.ext; unfold raw12008step1 raw12008step0; decide +kernel
      have hl : raw12008step0Labels = labelEmbedding8 ∘ raw12008step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12008step0 raw12008step0Labels raw12008step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4806 node4806Labels := by rfl

theorem canonical12009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12009 raw12009Labels = mixedMoment B node4806 node4806Labels := by
  calc
    mixedMoment B raw12009 raw12009Labels = mixedMoment B raw12009step0 raw12009step0Labels := by
      have ha : raw12009step0 = (fun i j => raw12009 (permutation425 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12009step0 raw12009; decide +kernel
      have hl : raw12009step0Labels = raw12009Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12009 raw12009Labels permutation425 permutation5
    mixedMoment B raw12009step0 raw12009step0Labels = mixedMoment B raw12009step1 raw12009step1Labels := by
      have ha : raw12009step1 = raw12009step0 := by apply Matrix.ext; unfold raw12009step1 raw12009step0; decide +kernel
      have hl : raw12009step0Labels = labelEmbedding8 ∘ raw12009step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12009step0 raw12009step0Labels raw12009step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4806 node4806Labels := by rfl

theorem canonical12010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12010 raw12010Labels = mixedMoment B node4878 node4878Labels := by
  calc
    mixedMoment B raw12010 raw12010Labels = mixedMoment B raw12010step0 raw12010step0Labels := by
      have ha : raw12010step0 = (fun i j => raw12010 (permutation355 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12010step0 raw12010; decide +kernel
      have hl : raw12010step0Labels = raw12010Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12010 raw12010Labels permutation355 permutation3
    mixedMoment B raw12010step0 raw12010step0Labels = mixedMoment B raw12010step1 raw12010step1Labels := by
      have ha : raw12010step1 = -raw12010step0 := by apply Matrix.ext; change ∀ i j, raw12010step1 i j = -(raw12010step0 i j); unfold raw12010step1 raw12010step0; decide +kernel
      have hl : raw12010step1Labels = raw12010step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12010step1 raw12010step1Labels = mixedMoment B raw12010step2 raw12010step2Labels := by
      have ha : raw12010step2 = raw12010step1 := by apply Matrix.ext; unfold raw12010step2 raw12010step1; decide +kernel
      have hl : raw12010step1Labels = labelEmbedding6 ∘ raw12010step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12010step1 raw12010step1Labels raw12010step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4878 node4878Labels := by rfl

theorem canonical12011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12011 raw12011Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw12011 raw12011Labels = mixedMoment B raw12011step0 raw12011step0Labels := by
      have ha : raw12011step0 = (fun i j => raw12011 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12011step0 raw12011; decide +kernel
      have hl : raw12011step0Labels = raw12011Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12011 raw12011Labels permutation167 permutation4
    mixedMoment B raw12011step0 raw12011step0Labels = mixedMoment B raw12011step1 raw12011step1Labels := by
      have ha : raw12011step1 = -raw12011step0 := by apply Matrix.ext; change ∀ i j, raw12011step1 i j = -(raw12011step0 i j); unfold raw12011step1 raw12011step0; decide +kernel
      have hl : raw12011step1Labels = raw12011step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12011step1 raw12011step1Labels = mixedMoment B raw12011step2 raw12011step2Labels := by
      have ha : raw12011step2 = raw12011step1 := by apply Matrix.ext; unfold raw12011step2 raw12011step1; decide +kernel
      have hl : raw12011step1Labels = labelEmbedding7 ∘ raw12011step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12011step1 raw12011step1Labels raw12011step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical12012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12012 raw12012Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw12012 raw12012Labels = mixedMoment B raw12012step0 raw12012step0Labels := by
      have ha : raw12012step0 = (fun i j => raw12012 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12012step0 raw12012; decide +kernel
      have hl : raw12012step0Labels = raw12012Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12012 raw12012Labels permutation154 permutation6
    mixedMoment B raw12012step0 raw12012step0Labels = mixedMoment B raw12012step1 raw12012step1Labels := by
      have ha : raw12012step1 = raw12012step0 := by apply Matrix.ext; unfold raw12012step1 raw12012step0; decide +kernel
      have hl : raw12012step0Labels = labelEmbedding9 ∘ raw12012step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12012step0 raw12012step0Labels raw12012step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

theorem canonical12013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12013 raw12013Labels = mixedMoment B node5263 node5263Labels := by
  calc
    mixedMoment B raw12013 raw12013Labels = mixedMoment B raw12013step0 raw12013step0Labels := by
      have ha : raw12013step0 = (fun i j => raw12013 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12013step0 raw12013; decide +kernel
      have hl : raw12013step0Labels = raw12013Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12013 raw12013Labels permutation154 permutation6
    mixedMoment B raw12013step0 raw12013step0Labels = mixedMoment B raw12013step1 raw12013step1Labels := by
      have ha : raw12013step1 = raw12013step0 := by apply Matrix.ext; unfold raw12013step1 raw12013step0; decide +kernel
      have hl : raw12013step0Labels = labelEmbedding9 ∘ raw12013step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12013step0 raw12013step0Labels raw12013step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5263 node5263Labels := by rfl

theorem canonical12014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12014 raw12014Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw12014 raw12014Labels = mixedMoment B raw12014step0 raw12014step0Labels := by
      have ha : raw12014step0 = (fun i j => raw12014 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12014step0 raw12014; decide +kernel
      have hl : raw12014step0Labels = raw12014Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12014 raw12014Labels permutation155 permutation6
    mixedMoment B raw12014step0 raw12014step0Labels = mixedMoment B raw12014step1 raw12014step1Labels := by
      have ha : raw12014step1 = raw12014step0 := by apply Matrix.ext; unfold raw12014step1 raw12014step0; decide +kernel
      have hl : raw12014step0Labels = labelEmbedding9 ∘ raw12014step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12014step0 raw12014step0Labels raw12014step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical12015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12015 raw12015Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw12015 raw12015Labels = mixedMoment B raw12015step0 raw12015step0Labels := by
      have ha : raw12015step0 = (fun i j => raw12015 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12015step0 raw12015; decide +kernel
      have hl : raw12015step0Labels = raw12015Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12015 raw12015Labels permutation161 permutation4
    mixedMoment B raw12015step0 raw12015step0Labels = mixedMoment B raw12015step1 raw12015step1Labels := by
      have ha : raw12015step1 = -raw12015step0 := by apply Matrix.ext; change ∀ i j, raw12015step1 i j = -(raw12015step0 i j); unfold raw12015step1 raw12015step0; decide +kernel
      have hl : raw12015step1Labels = raw12015step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12015step1 raw12015step1Labels = mixedMoment B raw12015step2 raw12015step2Labels := by
      have ha : raw12015step2 = raw12015step1 := by apply Matrix.ext; unfold raw12015step2 raw12015step1; decide +kernel
      have hl : raw12015step1Labels = labelEmbedding7 ∘ raw12015step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12015step1 raw12015step1Labels raw12015step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical12016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12016 raw12016Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw12016 raw12016Labels = mixedMoment B raw12016step0 raw12016step0Labels := by
      have ha : raw12016step0 = (fun i j => raw12016 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12016step0 raw12016; decide +kernel
      have hl : raw12016step0Labels = raw12016Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12016 raw12016Labels permutation152 permutation6
    mixedMoment B raw12016step0 raw12016step0Labels = mixedMoment B raw12016step1 raw12016step1Labels := by
      have ha : raw12016step1 = raw12016step0 := by apply Matrix.ext; unfold raw12016step1 raw12016step0; decide +kernel
      have hl : raw12016step0Labels = labelEmbedding9 ∘ raw12016step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12016step0 raw12016step0Labels raw12016step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

theorem canonical12017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12017 raw12017Labels = mixedMoment B node5263 node5263Labels := by
  calc
    mixedMoment B raw12017 raw12017Labels = mixedMoment B raw12017step0 raw12017step0Labels := by
      have ha : raw12017step0 = (fun i j => raw12017 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12017step0 raw12017; decide +kernel
      have hl : raw12017step0Labels = raw12017Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12017 raw12017Labels permutation152 permutation6
    mixedMoment B raw12017step0 raw12017step0Labels = mixedMoment B raw12017step1 raw12017step1Labels := by
      have ha : raw12017step1 = raw12017step0 := by apply Matrix.ext; unfold raw12017step1 raw12017step0; decide +kernel
      have hl : raw12017step0Labels = labelEmbedding9 ∘ raw12017step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12017step0 raw12017step0Labels raw12017step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5263 node5263Labels := by rfl

theorem canonical12018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12018 raw12018Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw12018 raw12018Labels = mixedMoment B raw12018step0 raw12018step0Labels := by
      have ha : raw12018step0 = (fun i j => raw12018 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12018step0 raw12018; decide +kernel
      have hl : raw12018step0Labels = raw12018Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12018 raw12018Labels permutation153 permutation6
    mixedMoment B raw12018step0 raw12018step0Labels = mixedMoment B raw12018step1 raw12018step1Labels := by
      have ha : raw12018step1 = raw12018step0 := by apply Matrix.ext; unfold raw12018step1 raw12018step0; decide +kernel
      have hl : raw12018step0Labels = labelEmbedding9 ∘ raw12018step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12018step0 raw12018step0Labels raw12018step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical12019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12019 raw12019Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw12019 raw12019Labels = mixedMoment B raw12019step0 raw12019step0Labels := by
      have ha : raw12019step0 = (fun i j => raw12019 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12019step0 raw12019; decide +kernel
      have hl : raw12019step0Labels = raw12019Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12019 raw12019Labels permutation152 permutation6
    mixedMoment B raw12019step0 raw12019step0Labels = mixedMoment B raw12019step1 raw12019step1Labels := by
      have ha : raw12019step1 = raw12019step0 := by apply Matrix.ext; unfold raw12019step1 raw12019step0; decide +kernel
      have hl : raw12019step0Labels = labelEmbedding9 ∘ raw12019step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12019step0 raw12019step0Labels raw12019step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5256 node5256Labels := by rfl

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

theorem canonical12042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12042 raw12042Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw12042 raw12042Labels = mixedMoment B raw12042step0 raw12042step0Labels := by
      have ha : raw12042step0 = (fun i j => raw12042 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12042step0 raw12042; decide +kernel
      have hl : raw12042step0Labels = raw12042Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12042 raw12042Labels permutation180 permutation7
    mixedMoment B raw12042step0 raw12042step0Labels = mixedMoment B raw12042step1 raw12042step1Labels := by
      have ha : raw12042step1 = raw12042step0 := by apply Matrix.ext; unfold raw12042step1 raw12042step0; decide +kernel
      have hl : raw12042step0Labels = labelEmbedding1 ∘ raw12042step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12042step0 raw12042step0Labels raw12042step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2676 node2676Labels := by rfl

theorem canonical12043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12043 raw12043Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw12043 raw12043Labels = mixedMoment B raw12043step0 raw12043step0Labels := by
      have ha : raw12043step0 = (fun i j => raw12043 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12043step0 raw12043; decide +kernel
      have hl : raw12043step0Labels = raw12043Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12043 raw12043Labels permutation181 permutation7
    mixedMoment B raw12043step0 raw12043step0Labels = mixedMoment B raw12043step1 raw12043step1Labels := by
      have ha : raw12043step1 = raw12043step0 := by apply Matrix.ext; unfold raw12043step1 raw12043step0; decide +kernel
      have hl : raw12043step0Labels = labelEmbedding1 ∘ raw12043step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12043step0 raw12043step0Labels raw12043step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

theorem canonical12044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12044 raw12044Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw12044 raw12044Labels = mixedMoment B raw12044step0 raw12044step0Labels := by
      have ha : raw12044step0 = (fun i j => raw12044 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12044step0 raw12044; decide +kernel
      have hl : raw12044step0Labels = raw12044Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12044 raw12044Labels permutation180 permutation7
    mixedMoment B raw12044step0 raw12044step0Labels = mixedMoment B raw12044step1 raw12044step1Labels := by
      have ha : raw12044step1 = raw12044step0 := by apply Matrix.ext; unfold raw12044step1 raw12044step0; decide +kernel
      have hl : raw12044step0Labels = labelEmbedding1 ∘ raw12044step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12044step0 raw12044step0Labels raw12044step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

theorem canonical12045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12045 raw12045Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw12045 raw12045Labels = mixedMoment B raw12045step0 raw12045step0Labels := by
      have ha : raw12045step0 = (fun i j => raw12045 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12045step0 raw12045; decide +kernel
      have hl : raw12045step0Labels = raw12045Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12045 raw12045Labels permutation176 permutation7
    mixedMoment B raw12045step0 raw12045step0Labels = mixedMoment B raw12045step1 raw12045step1Labels := by
      have ha : raw12045step1 = raw12045step0 := by apply Matrix.ext; unfold raw12045step1 raw12045step0; decide +kernel
      have hl : raw12045step0Labels = labelEmbedding1 ∘ raw12045step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12045step0 raw12045step0Labels raw12045step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2671 node2671Labels := by rfl

theorem canonical12046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12046 raw12046Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw12046 raw12046Labels = mixedMoment B raw12046step0 raw12046step0Labels := by
      have hz : ∀ j, raw12046 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12046step0 = (fun i j => raw12046 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12046step0 raw12046; decide +kernel
      have hl : raw12046step0Labels = raw12046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12046 raw12046Labels permutation265 hz
    mixedMoment B raw12046step0 raw12046step0Labels = mixedMoment B raw12046step1 raw12046step1Labels := by
      have ha : raw12046step1 = (fun i j => raw12046step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12046step1 raw12046step0; decide +kernel
      have hl : raw12046step1Labels = raw12046step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12046step0 raw12046step0Labels permutation36 permutation7
    mixedMoment B raw12046step1 raw12046step1Labels = mixedMoment B raw12046step2 raw12046step2Labels := by
      have ha : raw12046step2 = raw12046step1 := by apply Matrix.ext; unfold raw12046step2 raw12046step1; decide +kernel
      have hl : raw12046step1Labels = labelEmbedding1 ∘ raw12046step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12046step1 raw12046step1Labels raw12046step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

theorem canonical12047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12047 raw12047Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw12047 raw12047Labels = mixedMoment B raw12047step0 raw12047step0Labels := by
      have hz : ∀ j, raw12047 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12047step0 = (fun i j => raw12047 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12047step0 raw12047; decide +kernel
      have hl : raw12047step0Labels = raw12047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12047 raw12047Labels permutation265 hz
    mixedMoment B raw12047step0 raw12047step0Labels = mixedMoment B raw12047step1 raw12047step1Labels := by
      have ha : raw12047step1 = (fun i j => raw12047step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12047step1 raw12047step0; decide +kernel
      have hl : raw12047step1Labels = raw12047step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12047step0 raw12047step0Labels permutation37 permutation7
    mixedMoment B raw12047step1 raw12047step1Labels = mixedMoment B raw12047step2 raw12047step2Labels := by
      have ha : raw12047step2 = raw12047step1 := by apply Matrix.ext; unfold raw12047step2 raw12047step1; decide +kernel
      have hl : raw12047step1Labels = labelEmbedding1 ∘ raw12047step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12047step1 raw12047step1Labels raw12047step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical12048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12048 raw12048Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw12048 raw12048Labels = mixedMoment B raw12048step0 raw12048step0Labels := by
      have hz : ∀ j, raw12048 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12048step0 = (fun i j => raw12048 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12048step0 raw12048; decide +kernel
      have hl : raw12048step0Labels = raw12048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12048 raw12048Labels permutation265 hz
    mixedMoment B raw12048step0 raw12048step0Labels = mixedMoment B raw12048step1 raw12048step1Labels := by
      have ha : raw12048step1 = (fun i j => raw12048step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12048step1 raw12048step0; decide +kernel
      have hl : raw12048step1Labels = raw12048step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12048step0 raw12048step0Labels permutation36 permutation7
    mixedMoment B raw12048step1 raw12048step1Labels = mixedMoment B raw12048step2 raw12048step2Labels := by
      have ha : raw12048step2 = raw12048step1 := by apply Matrix.ext; unfold raw12048step2 raw12048step1; decide +kernel
      have hl : raw12048step1Labels = labelEmbedding1 ∘ raw12048step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12048step1 raw12048step1Labels raw12048step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

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

theorem canonical12050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12050 raw12050Labels = mixedMoment B node2010 node2010Labels := by
  calc
    mixedMoment B raw12050 raw12050Labels = mixedMoment B raw12050step0 raw12050step0Labels := by
      have ha : raw12050step0 = (fun i j => raw12050 (permutation427 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12050step0 raw12050; decide +kernel
      have hl : raw12050step0Labels = raw12050Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12050 raw12050Labels permutation427 permutation5
    mixedMoment B raw12050step0 raw12050step0Labels = mixedMoment B raw12050step1 raw12050step1Labels := by
      have ha : raw12050step1 = raw12050step0 := by apply Matrix.ext; unfold raw12050step1 raw12050step0; decide +kernel
      have hl : raw12050step0Labels = labelEmbedding1 ∘ raw12050step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12050step0 raw12050step0Labels raw12050step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2010 node2010Labels := by rfl

theorem canonical12051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12051 raw12051Labels = mixedMoment B node2011 node2011Labels := by
  calc
    mixedMoment B raw12051 raw12051Labels = mixedMoment B raw12051step0 raw12051step0Labels := by
      have ha : raw12051step0 = (fun i j => raw12051 (permutation426 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12051step0 raw12051; decide +kernel
      have hl : raw12051step0Labels = raw12051Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12051 raw12051Labels permutation426 permutation5
    mixedMoment B raw12051step0 raw12051step0Labels = mixedMoment B raw12051step1 raw12051step1Labels := by
      have ha : raw12051step1 = raw12051step0 := by apply Matrix.ext; unfold raw12051step1 raw12051step0; decide +kernel
      have hl : raw12051step0Labels = labelEmbedding1 ∘ raw12051step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12051step0 raw12051step0Labels raw12051step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2011 node2011Labels := by rfl

theorem canonical12052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12052 raw12052Labels = mixedMoment B node2024 node2024Labels := by
  calc
    mixedMoment B raw12052 raw12052Labels = mixedMoment B raw12052step0 raw12052step0Labels := by
      have ha : raw12052step0 = (fun i j => raw12052 (permutation431 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12052step0 raw12052; decide +kernel
      have hl : raw12052step0Labels = raw12052Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12052 raw12052Labels permutation431 permutation5
    mixedMoment B raw12052step0 raw12052step0Labels = mixedMoment B raw12052step1 raw12052step1Labels := by
      have ha : raw12052step1 = raw12052step0 := by apply Matrix.ext; unfold raw12052step1 raw12052step0; decide +kernel
      have hl : raw12052step0Labels = labelEmbedding1 ∘ raw12052step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12052step0 raw12052step0Labels raw12052step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2024 node2024Labels := by rfl

theorem canonical12053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12053 raw12053Labels = mixedMoment B node2024 node2024Labels := by
  calc
    mixedMoment B raw12053 raw12053Labels = mixedMoment B raw12053step0 raw12053step0Labels := by
      have ha : raw12053step0 = (fun i j => raw12053 (permutation425 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12053step0 raw12053; decide +kernel
      have hl : raw12053step0Labels = raw12053Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12053 raw12053Labels permutation425 permutation5
    mixedMoment B raw12053step0 raw12053step0Labels = mixedMoment B raw12053step1 raw12053step1Labels := by
      have ha : raw12053step1 = raw12053step0 := by apply Matrix.ext; unfold raw12053step1 raw12053step0; decide +kernel
      have hl : raw12053step0Labels = labelEmbedding1 ∘ raw12053step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12053step0 raw12053step0Labels raw12053step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2024 node2024Labels := by rfl

theorem canonical12054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12054 raw12054Labels = mixedMoment B node2234 node2234Labels := by
  calc
    mixedMoment B raw12054 raw12054Labels = mixedMoment B raw12054step0 raw12054step0Labels := by
      have ha : raw12054step0 = (fun i j => raw12054 (permutation394 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12054step0 raw12054; decide +kernel
      have hl : raw12054step0Labels = raw12054Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12054 raw12054Labels permutation394 permutation5
    mixedMoment B raw12054step0 raw12054step0Labels = mixedMoment B raw12054step1 raw12054step1Labels := by
      have ha : raw12054step1 = raw12054step0 := by apply Matrix.ext; unfold raw12054step1 raw12054step0; decide +kernel
      have hl : raw12054step0Labels = labelEmbedding1 ∘ raw12054step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12054step0 raw12054step0Labels raw12054step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2234 node2234Labels := by rfl

theorem canonical12055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12055 raw12055Labels = mixedMoment B node3203 node3203Labels := by
  calc
    mixedMoment B raw12055 raw12055Labels = mixedMoment B raw12055step0 raw12055step0Labels := by
      have ha : raw12055step0 = (fun i j => raw12055 (permutation167 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12055step0 raw12055; decide +kernel
      have hl : raw12055step0Labels = raw12055Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12055 raw12055Labels permutation167 permutation5
    mixedMoment B raw12055step0 raw12055step0Labels = mixedMoment B raw12055step1 raw12055step1Labels := by
      have ha : raw12055step1 = -raw12055step0 := by apply Matrix.ext; change ∀ i j, raw12055step1 i j = -(raw12055step0 i j); unfold raw12055step1 raw12055step0; decide +kernel
      have hl : raw12055step1Labels = raw12055step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12055step1 raw12055step1Labels = mixedMoment B raw12055step2 raw12055step2Labels := by
      have ha : raw12055step2 = raw12055step1 := by apply Matrix.ext; unfold raw12055step2 raw12055step1; decide +kernel
      have hl : raw12055step1Labels = labelEmbedding1 ∘ raw12055step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12055step1 raw12055step1Labels raw12055step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3203 node3203Labels := by rfl

theorem canonical12056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12056 raw12056Labels = mixedMoment B node3043 node3043Labels := by
  calc
    mixedMoment B raw12056 raw12056Labels = mixedMoment B raw12056step0 raw12056step0Labels := by
      have ha : raw12056step0 = (fun i j => raw12056 (permutation177 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12056step0 raw12056; decide +kernel
      have hl : raw12056step0Labels = raw12056Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12056 raw12056Labels permutation177 permutation7
    mixedMoment B raw12056step0 raw12056step0Labels = mixedMoment B raw12056step1 raw12056step1Labels := by
      have ha : raw12056step1 = raw12056step0 := by apply Matrix.ext; unfold raw12056step1 raw12056step0; decide +kernel
      have hl : raw12056step0Labels = labelEmbedding1 ∘ raw12056step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12056step0 raw12056step0Labels raw12056step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3043 node3043Labels := by rfl

theorem canonical12057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12057 raw12057Labels = mixedMoment B node3036 node3036Labels := by
  calc
    mixedMoment B raw12057 raw12057Labels = mixedMoment B raw12057step0 raw12057step0Labels := by
      have ha : raw12057step0 = (fun i j => raw12057 (permutation177 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12057step0 raw12057; decide +kernel
      have hl : raw12057step0Labels = raw12057Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12057 raw12057Labels permutation177 permutation7
    mixedMoment B raw12057step0 raw12057step0Labels = mixedMoment B raw12057step1 raw12057step1Labels := by
      have ha : raw12057step1 = raw12057step0 := by apply Matrix.ext; unfold raw12057step1 raw12057step0; decide +kernel
      have hl : raw12057step0Labels = labelEmbedding1 ∘ raw12057step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12057step0 raw12057step0Labels raw12057step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3036 node3036Labels := by rfl

theorem canonical12058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12058 raw12058Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw12058 raw12058Labels = mixedMoment B raw12058step0 raw12058step0Labels := by
      have ha : raw12058step0 = (fun i j => raw12058 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12058step0 raw12058; decide +kernel
      have hl : raw12058step0Labels = raw12058Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12058 raw12058Labels permutation176 permutation7
    mixedMoment B raw12058step0 raw12058step0Labels = mixedMoment B raw12058step1 raw12058step1Labels := by
      have ha : raw12058step1 = raw12058step0 := by apply Matrix.ext; unfold raw12058step1 raw12058step0; decide +kernel
      have hl : raw12058step0Labels = labelEmbedding1 ∘ raw12058step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12058step0 raw12058step0Labels raw12058step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical12059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12059 raw12059Labels = mixedMoment B node3203 node3203Labels := by
  calc
    mixedMoment B raw12059 raw12059Labels = mixedMoment B raw12059step0 raw12059step0Labels := by
      have ha : raw12059step0 = (fun i j => raw12059 (permutation161 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12059step0 raw12059; decide +kernel
      have hl : raw12059step0Labels = raw12059Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12059 raw12059Labels permutation161 permutation5
    mixedMoment B raw12059step0 raw12059step0Labels = mixedMoment B raw12059step1 raw12059step1Labels := by
      have ha : raw12059step1 = -raw12059step0 := by apply Matrix.ext; change ∀ i j, raw12059step1 i j = -(raw12059step0 i j); unfold raw12059step1 raw12059step0; decide +kernel
      have hl : raw12059step1Labels = raw12059step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12059step1 raw12059step1Labels = mixedMoment B raw12059step2 raw12059step2Labels := by
      have ha : raw12059step2 = raw12059step1 := by apply Matrix.ext; unfold raw12059step2 raw12059step1; decide +kernel
      have hl : raw12059step1Labels = labelEmbedding1 ∘ raw12059step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12059step1 raw12059step1Labels raw12059step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3203 node3203Labels := by rfl

theorem canonical12060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12060 raw12060Labels = mixedMoment B node3043 node3043Labels := by
  calc
    mixedMoment B raw12060 raw12060Labels = mixedMoment B raw12060step0 raw12060step0Labels := by
      have ha : raw12060step0 = (fun i j => raw12060 (permutation179 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12060step0 raw12060; decide +kernel
      have hl : raw12060step0Labels = raw12060Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12060 raw12060Labels permutation179 permutation7
    mixedMoment B raw12060step0 raw12060step0Labels = mixedMoment B raw12060step1 raw12060step1Labels := by
      have ha : raw12060step1 = raw12060step0 := by apply Matrix.ext; unfold raw12060step1 raw12060step0; decide +kernel
      have hl : raw12060step0Labels = labelEmbedding1 ∘ raw12060step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12060step0 raw12060step0Labels raw12060step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3043 node3043Labels := by rfl

theorem canonical12061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12061 raw12061Labels = mixedMoment B node3036 node3036Labels := by
  calc
    mixedMoment B raw12061 raw12061Labels = mixedMoment B raw12061step0 raw12061step0Labels := by
      have ha : raw12061step0 = (fun i j => raw12061 (permutation179 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12061step0 raw12061; decide +kernel
      have hl : raw12061step0Labels = raw12061Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12061 raw12061Labels permutation179 permutation7
    mixedMoment B raw12061step0 raw12061step0Labels = mixedMoment B raw12061step1 raw12061step1Labels := by
      have ha : raw12061step1 = raw12061step0 := by apply Matrix.ext; unfold raw12061step1 raw12061step0; decide +kernel
      have hl : raw12061step0Labels = labelEmbedding1 ∘ raw12061step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12061step0 raw12061step0Labels raw12061step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3036 node3036Labels := by rfl

theorem canonical12062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12062 raw12062Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw12062 raw12062Labels = mixedMoment B raw12062step0 raw12062step0Labels := by
      have ha : raw12062step0 = (fun i j => raw12062 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12062step0 raw12062; decide +kernel
      have hl : raw12062step0Labels = raw12062Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12062 raw12062Labels permutation178 permutation7
    mixedMoment B raw12062step0 raw12062step0Labels = mixedMoment B raw12062step1 raw12062step1Labels := by
      have ha : raw12062step1 = raw12062step0 := by apply Matrix.ext; unfold raw12062step1 raw12062step0; decide +kernel
      have hl : raw12062step0Labels = labelEmbedding1 ∘ raw12062step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12062step0 raw12062step0Labels raw12062step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical12063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12063 raw12063Labels = mixedMoment B node3085 node3085Labels := by
  calc
    mixedMoment B raw12063 raw12063Labels = mixedMoment B raw12063step0 raw12063step0Labels := by
      have ha : raw12063step0 = (fun i j => raw12063 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12063step0 raw12063; decide +kernel
      have hl : raw12063step0Labels = raw12063Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12063 raw12063Labels permutation180 permutation7
    mixedMoment B raw12063step0 raw12063step0Labels = mixedMoment B raw12063step1 raw12063step1Labels := by
      have ha : raw12063step1 = raw12063step0 := by apply Matrix.ext; unfold raw12063step1 raw12063step0; decide +kernel
      have hl : raw12063step0Labels = labelEmbedding1 ∘ raw12063step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12063step0 raw12063step0Labels raw12063step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3085 node3085Labels := by rfl

theorem canonical12064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12064 raw12064Labels = mixedMoment B node3378 node3378Labels := by
  calc
    mixedMoment B raw12064 raw12064Labels = mixedMoment B raw12064step0 raw12064step0Labels := by
      have ha : raw12064step0 = (fun i j => raw12064 (permutation197 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12064step0 raw12064; decide +kernel
      have hl : raw12064step0Labels = raw12064Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12064 raw12064Labels permutation197 permutation2
    mixedMoment B raw12064step0 raw12064step0Labels = mixedMoment B raw12064step1 raw12064step1Labels := by
      have ha : raw12064step1 = -raw12064step0 := by apply Matrix.ext; change ∀ i j, raw12064step1 i j = -(raw12064step0 i j); unfold raw12064step1 raw12064step0; decide +kernel
      have hl : raw12064step1Labels = raw12064step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3378 node3378Labels := by rfl

theorem canonical12065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12065 raw12065Labels = mixedMoment B node3376 node3376Labels := by
  calc
    mixedMoment B raw12065 raw12065Labels = mixedMoment B raw12065step0 raw12065step0Labels := by
      have ha : raw12065step0 = (fun i j => raw12065 (permutation195 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12065step0 raw12065; decide +kernel
      have hl : raw12065step0Labels = raw12065Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12065 raw12065Labels permutation195 permutation2
    mixedMoment B raw12065step0 raw12065step0Labels = mixedMoment B raw12065step1 raw12065step1Labels := by
      have ha : raw12065step1 = -raw12065step0 := by apply Matrix.ext; change ∀ i j, raw12065step1 i j = -(raw12065step0 i j); unfold raw12065step1 raw12065step0; decide +kernel
      have hl : raw12065step1Labels = raw12065step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3376 node3376Labels := by rfl

theorem canonical12066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12066 raw12066Labels = mixedMoment B node3376 node3376Labels := by
  calc
    mixedMoment B raw12066 raw12066Labels = mixedMoment B raw12066step0 raw12066step0Labels := by
      have ha : raw12066step0 = (fun i j => raw12066 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12066step0 raw12066; decide +kernel
      have hl : raw12066step0Labels = raw12066Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12066 raw12066Labels permutation194 permutation2
    mixedMoment B raw12066step0 raw12066step0Labels = mixedMoment B raw12066step1 raw12066step1Labels := by
      have ha : raw12066step1 = -raw12066step0 := by apply Matrix.ext; change ∀ i j, raw12066step1 i j = -(raw12066step0 i j); unfold raw12066step1 raw12066step0; decide +kernel
      have hl : raw12066step1Labels = raw12066step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3376 node3376Labels := by rfl

theorem canonical12067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12067 raw12067Labels = mixedMoment B node3390 node3390Labels := by
  calc
    mixedMoment B raw12067 raw12067Labels = mixedMoment B raw12067step0 raw12067step0Labels := by
      have ha : raw12067step0 = (fun i j => raw12067 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12067step0 raw12067; decide +kernel
      have hl : raw12067step0Labels = raw12067Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12067 raw12067Labels permutation176 permutation2
    mixedMoment B raw12067step0 raw12067step0Labels = mixedMoment B raw12067step1 raw12067step1Labels := by
      have ha : raw12067step1 = -raw12067step0 := by apply Matrix.ext; change ∀ i j, raw12067step1 i j = -(raw12067step0 i j); unfold raw12067step1 raw12067step0; decide +kernel
      have hl : raw12067step1Labels = raw12067step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3390 node3390Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1276 node1276Labels = Sparse.eval nodeValue1276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1276) = mixedMoment B node1276 node1276Labels := rfl
  simpa [nodeValue1276, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1358 node1358Labels = Sparse.eval nodeValue1358 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1358) = mixedMoment B node1358 node1358Labels := rfl
  simpa [nodeValue1358, Sparse.eval] using hc.symm

theorem sound1360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1360 node1360Labels = Sparse.eval nodeValue1360 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1360) = mixedMoment B node1360 node1360Labels := rfl
  simpa [nodeValue1360, Sparse.eval] using hc.symm

theorem sound1366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1366 node1366Labels = Sparse.eval nodeValue1366 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1366) = mixedMoment B node1366 node1366Labels := rfl
  simpa [nodeValue1366, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1421 node1421Labels = Sparse.eval nodeValue1421 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1421) = mixedMoment B node1421 node1421Labels := rfl
  simpa [nodeValue1421, Sparse.eval] using hc.symm

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

theorem sound2010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2010 node2010Labels = Sparse.eval nodeValue2010 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2010) = mixedMoment B node2010 node2010Labels := rfl
  simpa [nodeValue2010, Sparse.eval] using hc.symm

theorem sound2011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2011 node2011Labels = Sparse.eval nodeValue2011 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2011) = mixedMoment B node2011 node2011Labels := rfl
  simpa [nodeValue2011, Sparse.eval] using hc.symm

theorem sound2023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2023 node2023Labels = Sparse.eval nodeValue2023 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2023) = mixedMoment B node2023 node2023Labels := rfl
  simpa [nodeValue2023, Sparse.eval] using hc.symm

theorem sound2024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2024 node2024Labels = Sparse.eval nodeValue2024 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2024) = mixedMoment B node2024 node2024Labels := rfl
  simpa [nodeValue2024, Sparse.eval] using hc.symm

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

theorem sound2234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2234 node2234Labels = Sparse.eval nodeValue2234 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2234) = mixedMoment B node2234 node2234Labels := rfl
  simpa [nodeValue2234, Sparse.eval] using hc.symm

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

theorem sound2245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2245 node2245Labels = Sparse.eval nodeValue2245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2245) = mixedMoment B node2245 node2245Labels := rfl
  simpa [nodeValue2245, Sparse.eval] using hc.symm

theorem sound2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2277 node2277Labels = Sparse.eval nodeValue2277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2277) = mixedMoment B node2277 node2277Labels := rfl
  simpa [nodeValue2277, Sparse.eval] using hc.symm

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

theorem sound2493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2493 node2493Labels = Sparse.eval nodeValue2493 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2493) = mixedMoment B node2493 node2493Labels := rfl
  simpa [nodeValue2493, Sparse.eval] using hc.symm

theorem sound2494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2494 node2494Labels = Sparse.eval nodeValue2494 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2494) = mixedMoment B node2494 node2494Labels := rfl
  simpa [nodeValue2494, Sparse.eval] using hc.symm

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

theorem sound2573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2573 node2573Labels = Sparse.eval nodeValue2573 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2573) = mixedMoment B node2573 node2573Labels := rfl
  simpa [nodeValue2573, Sparse.eval] using hc.symm

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

theorem sound2645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2645 node2645Labels = Sparse.eval nodeValue2645 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2645) = mixedMoment B node2645 node2645Labels := rfl
  simpa [nodeValue2645, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2721 node2721Labels = Sparse.eval nodeValue2721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2721) = mixedMoment B node2721 node2721Labels := rfl
  simpa [nodeValue2721, Sparse.eval] using hc.symm

theorem sound2730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2730 node2730Labels = Sparse.eval nodeValue2730 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2730) = mixedMoment B node2730 node2730Labels := rfl
  simpa [nodeValue2730, Sparse.eval] using hc.symm

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

theorem sound2757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2757 node2757Labels = Sparse.eval nodeValue2757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2757) = mixedMoment B node2757 node2757Labels := rfl
  simpa [nodeValue2757, Sparse.eval] using hc.symm

theorem sound2773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2773 node2773Labels = Sparse.eval nodeValue2773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2773) = mixedMoment B node2773 node2773Labels := rfl
  simpa [nodeValue2773, Sparse.eval] using hc.symm

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

theorem sound2862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2862 node2862Labels = Sparse.eval nodeValue2862 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2862) = mixedMoment B node2862 node2862Labels := rfl
  simpa [nodeValue2862, Sparse.eval] using hc.symm

theorem sound2864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2864 node2864Labels = Sparse.eval nodeValue2864 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2864) = mixedMoment B node2864 node2864Labels := rfl
  simpa [nodeValue2864, Sparse.eval] using hc.symm

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

theorem sound3029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3029 node3029Labels = Sparse.eval nodeValue3029 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3029) = mixedMoment B node3029 node3029Labels := rfl
  simpa [nodeValue3029, Sparse.eval] using hc.symm

theorem sound3030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3030 node3030Labels = Sparse.eval nodeValue3030 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3030) = mixedMoment B node3030 node3030Labels := rfl
  simpa [nodeValue3030, Sparse.eval] using hc.symm

theorem sound3034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3034 node3034Labels = Sparse.eval nodeValue3034 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3034) = mixedMoment B node3034 node3034Labels := rfl
  simpa [nodeValue3034, Sparse.eval] using hc.symm

theorem sound3036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3036 node3036Labels = Sparse.eval nodeValue3036 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3036) = mixedMoment B node3036 node3036Labels := rfl
  simpa [nodeValue3036, Sparse.eval] using hc.symm

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

theorem sound3043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3043 node3043Labels = Sparse.eval nodeValue3043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3043) = mixedMoment B node3043 node3043Labels := rfl
  simpa [nodeValue3043, Sparse.eval] using hc.symm

theorem sound3051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3051 node3051Labels = Sparse.eval nodeValue3051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3051) = mixedMoment B node3051 node3051Labels := rfl
  simpa [nodeValue3051, Sparse.eval] using hc.symm

theorem sound3053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3053 node3053Labels = Sparse.eval nodeValue3053 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3053) = mixedMoment B node3053 node3053Labels := rfl
  simpa [nodeValue3053, Sparse.eval] using hc.symm

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

theorem sound3376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3376 node3376Labels = Sparse.eval nodeValue3376 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3376) = mixedMoment B node3376 node3376Labels := rfl
  simpa [nodeValue3376, Sparse.eval] using hc.symm

theorem sound3378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3378 node3378Labels = Sparse.eval nodeValue3378 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3378) = mixedMoment B node3378 node3378Labels := rfl
  simpa [nodeValue3378, Sparse.eval] using hc.symm

theorem sound3390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3390 node3390Labels = Sparse.eval nodeValue3390 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3390) = mixedMoment B node3390 node3390Labels := rfl
  simpa [nodeValue3390, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem sound3906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3906 node3906Labels = Sparse.eval nodeValue3906 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3906) = mixedMoment B node3906 node3906Labels := rfl
  simpa [nodeValue3906, Sparse.eval] using hc.symm

theorem sound3910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3910 node3910Labels = Sparse.eval nodeValue3910 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3910) = mixedMoment B node3910 node3910Labels := rfl
  simpa [nodeValue3910, Sparse.eval] using hc.symm

theorem sound3957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3957 node3957Labels = Sparse.eval nodeValue3957 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3957) = mixedMoment B node3957 node3957Labels := rfl
  simpa [nodeValue3957, Sparse.eval] using hc.symm

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

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

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

theorem sound4793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4793 node4793Labels = Sparse.eval nodeValue4793 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4793) = mixedMoment B node4793 node4793Labels := rfl
  simpa [nodeValue4793, Sparse.eval] using hc.symm

theorem sound4794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4794 node4794Labels = Sparse.eval nodeValue4794 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4794) = mixedMoment B node4794 node4794Labels := rfl
  simpa [nodeValue4794, Sparse.eval] using hc.symm

theorem sound4795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4795 node4795Labels = Sparse.eval nodeValue4795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4795) = mixedMoment B node4795 node4795Labels := rfl
  simpa [nodeValue4795, Sparse.eval] using hc.symm

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

theorem sound4806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4806 node4806Labels = Sparse.eval nodeValue4806 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4806) = mixedMoment B node4806 node4806Labels := rfl
  simpa [nodeValue4806, Sparse.eval] using hc.symm

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

theorem sound4878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4878 node4878Labels = Sparse.eval nodeValue4878 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4878) = mixedMoment B node4878 node4878Labels := rfl
  simpa [nodeValue4878, Sparse.eval] using hc.symm

theorem sound4889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4889 node4889Labels = Sparse.eval nodeValue4889 (mixedVector B) := by
  have h := singleton4889 B _hB
  rw [sound2245 B _hB _hF, sound2277 B _hB _hF] at h
  norm_num [nodeValue4889, nodeValue2245, nodeValue2277, Sparse.eval] at h ⊢
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

theorem sound5230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5230 node5230Labels = Sparse.eval nodeValue5230 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5230) = mixedMoment B node5230 node5230Labels := rfl
  simpa [nodeValue5230, Sparse.eval] using hc.symm

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

theorem zero5256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5256 node5256Labels = 0 := by
  exact mixedMoment_alpha B hF node5256 node5256Labels 1 permutation203
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

theorem sound5262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5262 node5262Labels = Sparse.eval nodeValue5262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5262) = mixedMoment B node5262 node5262Labels := rfl
  simpa [nodeValue5262, Sparse.eval] using hc.symm

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

theorem sound5299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5299 node5299Labels = Sparse.eval nodeValue5299 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5299) = mixedMoment B node5299 node5299Labels := rfl
  simpa [nodeValue5299, Sparse.eval] using hc.symm

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

theorem sourceEq702 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm702 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA702 + difference 0 0) (sourceB702 + difference 0 0) sourceC702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA702 + difference 0 0) (sourceB702 + difference 0 0) sourceC702) = raw11862 := by
      apply Matrix.ext; unfold tripleCharges sourceA702 sourceB702 sourceC702 difference raw11862; decide +kernel
    rw [ha]
    exact (canonical11862 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA702 + difference 0 1) (sourceB702 + difference 1 0) sourceC702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA702 + difference 0 1) (sourceB702 + difference 1 0) sourceC702) = raw11863 := by
      apply Matrix.ext; unfold tripleCharges sourceA702 sourceB702 sourceC702 difference raw11863; decide +kernel
    rw [ha]
    exact (canonical11863 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA702 + difference 0 2) (sourceB702 + difference 2 0) sourceC702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA702 + difference 0 2) (sourceB702 + difference 2 0) sourceC702) = raw11864 := by
      apply Matrix.ext; unfold tripleCharges sourceA702 sourceB702 sourceC702 difference raw11864; decide +kernel
    rw [ha]
    exact (canonical11864 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA702 + difference 0 3) (sourceB702 + difference 3 0) sourceC702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3906) := by
    have ha : (tripleCharges (sourceA702 + difference 0 3) (sourceB702 + difference 3 0) sourceC702) = raw11865 := by
      apply Matrix.ext; unfold tripleCharges sourceA702 sourceB702 sourceC702 difference raw11865; decide +kernel
    rw [ha]
    exact (canonical11865 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA702 + difference 0 4) (sourceB702 + difference 4 0) sourceC702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3906) := by
    have ha : (tripleCharges (sourceA702 + difference 0 4) (sourceB702 + difference 4 0) sourceC702) = raw11866 := by
      apply Matrix.ext; unfold tripleCharges sourceA702 sourceB702 sourceC702 difference raw11866; decide +kernel
    rw [ha]
    exact (canonical11866 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA702 + difference 0 5) (sourceB702 + difference 5 0) sourceC702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA702 + difference 0 5) (sourceB702 + difference 5 0) sourceC702) = raw11867 := by
      apply Matrix.ext; unfold tripleCharges sourceA702 sourceB702 sourceC702 difference raw11867; decide +kernel
    rw [ha]
    exact (canonical11867 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA702 + sourceB702) sourceC702) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA702 + sourceB702) sourceC702) = raw11868 := by
      apply Matrix.ext; unfold doubleCharges sourceA702 sourceB702 sourceC702 raw11868; decide +kernel
    rw [ha]
    exact (canonical11868 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA702 sourceB702 sourceC702
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm702, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources22
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq704 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm704 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA704 + difference 1 0) (sourceB704 + difference 0 1) sourceC704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1276) := by
    have ha : (tripleCharges (sourceA704 + difference 1 0) (sourceB704 + difference 0 1) sourceC704) = raw11869 := by
      apply Matrix.ext; unfold tripleCharges sourceA704 sourceB704 sourceC704 difference raw11869; decide +kernel
    rw [ha]
    exact (canonical11869 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA704 + difference 1 1) (sourceB704 + difference 1 1) sourceC704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA704 + difference 1 1) (sourceB704 + difference 1 1) sourceC704) = raw11862 := by
      apply Matrix.ext; unfold tripleCharges sourceA704 sourceB704 sourceC704 difference raw11862; decide +kernel
    rw [ha]
    exact (canonical11862 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA704 + difference 1 2) (sourceB704 + difference 2 1) sourceC704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2645) := by
    have ha : (tripleCharges (sourceA704 + difference 1 2) (sourceB704 + difference 2 1) sourceC704) = raw11874 := by
      apply Matrix.ext; unfold tripleCharges sourceA704 sourceB704 sourceC704 difference raw11874; decide +kernel
    rw [ha]
    exact (canonical11874 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA704 + difference 1 3) (sourceB704 + difference 3 1) sourceC704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA704 + difference 1 3) (sourceB704 + difference 3 1) sourceC704) = raw11875 := by
      apply Matrix.ext; unfold tripleCharges sourceA704 sourceB704 sourceC704 difference raw11875; decide +kernel
    rw [ha]
    exact (canonical11875 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA704 + difference 1 4) (sourceB704 + difference 4 1) sourceC704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA704 + difference 1 4) (sourceB704 + difference 4 1) sourceC704) = raw11876 := by
      apply Matrix.ext; unfold tripleCharges sourceA704 sourceB704 sourceC704 difference raw11876; decide +kernel
    rw [ha]
    exact (canonical11876 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA704 + difference 1 5) (sourceB704 + difference 5 1) sourceC704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2757) := by
    have ha : (tripleCharges (sourceA704 + difference 1 5) (sourceB704 + difference 5 1) sourceC704) = raw11877 := by
      apply Matrix.ext; unfold tripleCharges sourceA704 sourceB704 sourceC704 difference raw11877; decide +kernel
    rw [ha]
    exact (canonical11877 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA704 + sourceB704) sourceC704) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA704 + sourceB704) sourceC704) = raw11868 := by
      apply Matrix.ext; unfold doubleCharges sourceA704 sourceB704 sourceC704 raw11868; decide +kernel
    rw [ha]
    exact (canonical11868 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA704 sourceB704 sourceC704
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm704, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq705 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm705 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA705 + difference 0 1) (sourceB705 + difference 1 0) sourceC705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA705 + difference 0 1) (sourceB705 + difference 1 0) sourceC705) = raw11863 := by
      apply Matrix.ext; unfold tripleCharges sourceA705 sourceB705 sourceC705 difference raw11863; decide +kernel
    rw [ha]
    exact (canonical11863 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA705 + difference 1 1) (sourceB705 + difference 1 1) sourceC705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA705 + difference 1 1) (sourceB705 + difference 1 1) sourceC705) = raw11862 := by
      apply Matrix.ext; unfold tripleCharges sourceA705 sourceB705 sourceC705 difference raw11862; decide +kernel
    rw [ha]
    exact (canonical11862 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA705 + difference 2 1) (sourceB705 + difference 1 2) sourceC705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA705 + difference 2 1) (sourceB705 + difference 1 2) sourceC705) = raw11878 := by
      apply Matrix.ext; unfold tripleCharges sourceA705 sourceB705 sourceC705 difference raw11878; decide +kernel
    rw [ha]
    exact (canonical11878 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA705 + difference 3 1) (sourceB705 + difference 1 3) sourceC705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2494) := by
    have ha : (tripleCharges (sourceA705 + difference 3 1) (sourceB705 + difference 1 3) sourceC705) = raw11879 := by
      apply Matrix.ext; unfold tripleCharges sourceA705 sourceB705 sourceC705 difference raw11879; decide +kernel
    rw [ha]
    exact (canonical11879 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA705 + difference 4 1) (sourceB705 + difference 1 4) sourceC705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2494) := by
    have ha : (tripleCharges (sourceA705 + difference 4 1) (sourceB705 + difference 1 4) sourceC705) = raw11880 := by
      apply Matrix.ext; unfold tripleCharges sourceA705 sourceB705 sourceC705 difference raw11880; decide +kernel
    rw [ha]
    exact (canonical11880 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA705 + difference 5 1) (sourceB705 + difference 1 5) sourceC705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2493) := by
    have ha : (tripleCharges (sourceA705 + difference 5 1) (sourceB705 + difference 1 5) sourceC705) = raw11881 := by
      apply Matrix.ext; unfold tripleCharges sourceA705 sourceB705 sourceC705 difference raw11881; decide +kernel
    rw [ha]
    exact (canonical11881 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA705 + sourceB705) sourceC705) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA705 + sourceB705) sourceC705) = raw11868 := by
      apply Matrix.ext; unfold doubleCharges sourceA705 sourceB705 sourceC705 raw11868; decide +kernel
    rw [ha]
    exact (canonical11868 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA705 sourceB705 sourceC705
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm705, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq709 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm709 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA709 + difference 0 0) (sourceB709 + difference 0 0) sourceC709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA709 + difference 0 0) (sourceB709 + difference 0 0) sourceC709) = raw11972 := by
      apply Matrix.ext; unfold tripleCharges sourceA709 sourceB709 sourceC709 difference raw11972; decide +kernel
    rw [ha]
    exact (canonical11972 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA709 + difference 0 1) (sourceB709 + difference 1 0) sourceC709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA709 + difference 0 1) (sourceB709 + difference 1 0) sourceC709) = raw11973 := by
      apply Matrix.ext; unfold tripleCharges sourceA709 sourceB709 sourceC709 difference raw11973; decide +kernel
    rw [ha]
    exact (canonical11973 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA709 + difference 0 2) (sourceB709 + difference 2 0) sourceC709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA709 + difference 0 2) (sourceB709 + difference 2 0) sourceC709) = raw11974 := by
      apply Matrix.ext; unfold tripleCharges sourceA709 sourceB709 sourceC709 difference raw11974; decide +kernel
    rw [ha]
    exact (canonical11974 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA709 + difference 0 3) (sourceB709 + difference 3 0) sourceC709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA709 + difference 0 3) (sourceB709 + difference 3 0) sourceC709) = raw11975 := by
      apply Matrix.ext; unfold tripleCharges sourceA709 sourceB709 sourceC709 difference raw11975; decide +kernel
    rw [ha]
    exact (canonical11975 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA709 + difference 0 4) (sourceB709 + difference 4 0) sourceC709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA709 + difference 0 4) (sourceB709 + difference 4 0) sourceC709) = raw11976 := by
      apply Matrix.ext; unfold tripleCharges sourceA709 sourceB709 sourceC709 difference raw11976; decide +kernel
    rw [ha]
    exact (canonical11976 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA709 + difference 0 5) (sourceB709 + difference 5 0) sourceC709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA709 + difference 0 5) (sourceB709 + difference 5 0) sourceC709) = raw11977 := by
      apply Matrix.ext; unfold tripleCharges sourceA709 sourceB709 sourceC709 difference raw11977; decide +kernel
    rw [ha]
    exact (canonical11977 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA709 + sourceB709) sourceC709) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA709 + sourceB709) sourceC709) = raw11978 := by
      apply Matrix.ext; unfold doubleCharges sourceA709 sourceB709 sourceC709 raw11978; decide +kernel
    rw [ha]
    exact (canonical11978 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA709 sourceB709 sourceC709
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm709, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq710 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm710 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA710 + difference 0 0) (sourceB710 + difference 0 0) sourceC710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA710 + difference 0 0) (sourceB710 + difference 0 0) sourceC710) = raw11972 := by
      apply Matrix.ext; unfold tripleCharges sourceA710 sourceB710 sourceC710 difference raw11972; decide +kernel
    rw [ha]
    exact (canonical11972 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA710 + difference 1 0) (sourceB710 + difference 0 1) sourceC710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1366) := by
    have ha : (tripleCharges (sourceA710 + difference 1 0) (sourceB710 + difference 0 1) sourceC710) = raw11979 := by
      apply Matrix.ext; unfold tripleCharges sourceA710 sourceB710 sourceC710 difference raw11979; decide +kernel
    rw [ha]
    exact (canonical11979 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA710 + difference 2 0) (sourceB710 + difference 0 2) sourceC710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1421) := by
    have ha : (tripleCharges (sourceA710 + difference 2 0) (sourceB710 + difference 0 2) sourceC710) = raw11980 := by
      apply Matrix.ext; unfold tripleCharges sourceA710 sourceB710 sourceC710 difference raw11980; decide +kernel
    rw [ha]
    exact (canonical11980 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA710 + difference 3 0) (sourceB710 + difference 0 3) sourceC710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1358) := by
    have ha : (tripleCharges (sourceA710 + difference 3 0) (sourceB710 + difference 0 3) sourceC710) = raw11981 := by
      apply Matrix.ext; unfold tripleCharges sourceA710 sourceB710 sourceC710 difference raw11981; decide +kernel
    rw [ha]
    exact (canonical11981 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA710 + difference 4 0) (sourceB710 + difference 0 4) sourceC710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1358) := by
    have ha : (tripleCharges (sourceA710 + difference 4 0) (sourceB710 + difference 0 4) sourceC710) = raw11982 := by
      apply Matrix.ext; unfold tripleCharges sourceA710 sourceB710 sourceC710 difference raw11982; decide +kernel
    rw [ha]
    exact (canonical11982 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA710 + difference 5 0) (sourceB710 + difference 0 5) sourceC710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1360) := by
    have ha : (tripleCharges (sourceA710 + difference 5 0) (sourceB710 + difference 0 5) sourceC710) = raw11983 := by
      apply Matrix.ext; unfold tripleCharges sourceA710 sourceB710 sourceC710 difference raw11983; decide +kernel
    rw [ha]
    exact (canonical11983 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA710 + sourceB710) sourceC710) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA710 + sourceB710) sourceC710) = raw11978 := by
      apply Matrix.ext; unfold doubleCharges sourceA710 sourceB710 sourceC710 raw11978; decide +kernel
    rw [ha]
    exact (canonical11978 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA710 sourceB710 sourceC710
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm710, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq711 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm711 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA711 + difference 1 0) (sourceB711 + difference 0 1) sourceC711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1366) := by
    have ha : (tripleCharges (sourceA711 + difference 1 0) (sourceB711 + difference 0 1) sourceC711) = raw11979 := by
      apply Matrix.ext; unfold tripleCharges sourceA711 sourceB711 sourceC711 difference raw11979; decide +kernel
    rw [ha]
    exact (canonical11979 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA711 + difference 1 1) (sourceB711 + difference 1 1) sourceC711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA711 + difference 1 1) (sourceB711 + difference 1 1) sourceC711) = raw11972 := by
      apply Matrix.ext; unfold tripleCharges sourceA711 sourceB711 sourceC711 difference raw11972; decide +kernel
    rw [ha]
    exact (canonical11972 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA711 + difference 1 2) (sourceB711 + difference 2 1) sourceC711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2880) := by
    have ha : (tripleCharges (sourceA711 + difference 1 2) (sourceB711 + difference 2 1) sourceC711) = raw11984 := by
      apply Matrix.ext; unfold tripleCharges sourceA711 sourceB711 sourceC711 difference raw11984; decide +kernel
    rw [ha]
    exact (canonical11984 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA711 + difference 1 3) (sourceB711 + difference 3 1) sourceC711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA711 + difference 1 3) (sourceB711 + difference 3 1) sourceC711) = raw11985 := by
      apply Matrix.ext; unfold tripleCharges sourceA711 sourceB711 sourceC711 difference raw11985; decide +kernel
    rw [ha]
    exact (canonical11985 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA711 + difference 1 4) (sourceB711 + difference 4 1) sourceC711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA711 + difference 1 4) (sourceB711 + difference 4 1) sourceC711) = raw11986 := by
      apply Matrix.ext; unfold tripleCharges sourceA711 sourceB711 sourceC711 difference raw11986; decide +kernel
    rw [ha]
    exact (canonical11986 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA711 + difference 1 5) (sourceB711 + difference 5 1) sourceC711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA711 + difference 1 5) (sourceB711 + difference 5 1) sourceC711) = raw11987 := by
      apply Matrix.ext; unfold tripleCharges sourceA711 sourceB711 sourceC711 difference raw11987; decide +kernel
    rw [ha]
    exact (canonical11987 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA711 + sourceB711) sourceC711) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA711 + sourceB711) sourceC711) = raw11978 := by
      apply Matrix.ext; unfold doubleCharges sourceA711 sourceB711 sourceC711 raw11978; decide +kernel
    rw [ha]
    exact (canonical11978 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA711 sourceB711 sourceC711
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm711, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq713 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm713 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA713 + difference 0 2) (sourceB713 + difference 2 0) sourceC713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA713 + difference 0 2) (sourceB713 + difference 2 0) sourceC713) = raw11974 := by
      apply Matrix.ext; unfold tripleCharges sourceA713 sourceB713 sourceC713 difference raw11974; decide +kernel
    rw [ha]
    exact (canonical11974 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA713 + difference 1 2) (sourceB713 + difference 2 1) sourceC713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2880) := by
    have ha : (tripleCharges (sourceA713 + difference 1 2) (sourceB713 + difference 2 1) sourceC713) = raw11984 := by
      apply Matrix.ext; unfold tripleCharges sourceA713 sourceB713 sourceC713 difference raw11984; decide +kernel
    rw [ha]
    exact (canonical11984 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA713 + difference 2 2) (sourceB713 + difference 2 2) sourceC713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA713 + difference 2 2) (sourceB713 + difference 2 2) sourceC713) = raw11972 := by
      apply Matrix.ext; unfold tripleCharges sourceA713 sourceB713 sourceC713 difference raw11972; decide +kernel
    rw [ha]
    exact (canonical11972 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA713 + difference 3 2) (sourceB713 + difference 2 3) sourceC713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2862) := by
    have ha : (tripleCharges (sourceA713 + difference 3 2) (sourceB713 + difference 2 3) sourceC713) = raw11992 := by
      apply Matrix.ext; unfold tripleCharges sourceA713 sourceB713 sourceC713 difference raw11992; decide +kernel
    rw [ha]
    exact (canonical11992 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA713 + difference 4 2) (sourceB713 + difference 2 4) sourceC713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2862) := by
    have ha : (tripleCharges (sourceA713 + difference 4 2) (sourceB713 + difference 2 4) sourceC713) = raw11993 := by
      apply Matrix.ext; unfold tripleCharges sourceA713 sourceB713 sourceC713 difference raw11993; decide +kernel
    rw [ha]
    exact (canonical11993 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA713 + difference 5 2) (sourceB713 + difference 2 5) sourceC713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2864) := by
    have ha : (tripleCharges (sourceA713 + difference 5 2) (sourceB713 + difference 2 5) sourceC713) = raw11994 := by
      apply Matrix.ext; unfold tripleCharges sourceA713 sourceB713 sourceC713 difference raw11994; decide +kernel
    rw [ha]
    exact (canonical11994 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA713 + sourceB713) sourceC713) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA713 + sourceB713) sourceC713) = raw11978 := by
      apply Matrix.ext; unfold doubleCharges sourceA713 sourceB713 sourceC713 raw11978; decide +kernel
    rw [ha]
    exact (canonical11978 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA713 sourceB713 sourceC713
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm713, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq714 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm714 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA714 + difference 0 3) (sourceB714 + difference 3 0) sourceC714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA714 + difference 0 3) (sourceB714 + difference 3 0) sourceC714) = raw11975 := by
      apply Matrix.ext; unfold tripleCharges sourceA714 sourceB714 sourceC714 difference raw11975; decide +kernel
    rw [ha]
    exact (canonical11975 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA714 + difference 1 3) (sourceB714 + difference 3 1) sourceC714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA714 + difference 1 3) (sourceB714 + difference 3 1) sourceC714) = raw11985 := by
      apply Matrix.ext; unfold tripleCharges sourceA714 sourceB714 sourceC714 difference raw11985; decide +kernel
    rw [ha]
    exact (canonical11985 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA714 + difference 2 3) (sourceB714 + difference 3 2) sourceC714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2573) := by
    have ha : (tripleCharges (sourceA714 + difference 2 3) (sourceB714 + difference 3 2) sourceC714) = raw11995 := by
      apply Matrix.ext; unfold tripleCharges sourceA714 sourceB714 sourceC714 difference raw11995; decide +kernel
    rw [ha]
    exact (canonical11995 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA714 + difference 3 3) (sourceB714 + difference 3 3) sourceC714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA714 + difference 3 3) (sourceB714 + difference 3 3) sourceC714) = raw11972 := by
      apply Matrix.ext; unfold tripleCharges sourceA714 sourceB714 sourceC714 difference raw11972; decide +kernel
    rw [ha]
    exact (canonical11972 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA714 + difference 4 3) (sourceB714 + difference 3 4) sourceC714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3029) := by
    have ha : (tripleCharges (sourceA714 + difference 4 3) (sourceB714 + difference 3 4) sourceC714) = raw11996 := by
      apply Matrix.ext; unfold tripleCharges sourceA714 sourceB714 sourceC714 difference raw11996; decide +kernel
    rw [ha]
    exact (canonical11996 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA714 + difference 5 3) (sourceB714 + difference 3 5) sourceC714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3030) := by
    have ha : (tripleCharges (sourceA714 + difference 5 3) (sourceB714 + difference 3 5) sourceC714) = raw11997 := by
      apply Matrix.ext; unfold tripleCharges sourceA714 sourceB714 sourceC714 difference raw11997; decide +kernel
    rw [ha]
    exact (canonical11997 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA714 + sourceB714) sourceC714) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA714 + sourceB714) sourceC714) = raw11978 := by
      apply Matrix.ext; unfold doubleCharges sourceA714 sourceB714 sourceC714 raw11978; decide +kernel
    rw [ha]
    exact (canonical11978 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA714 sourceB714 sourceC714
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm714, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq715 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm715 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA715 + difference 0 1) (sourceB715 + difference 1 0) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA715 + difference 0 1) (sourceB715 + difference 1 0) sourceC715) = raw11998 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw11998; decide +kernel
    rw [ha]
    exact (canonical11998 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA715 + difference 0 2) (sourceB715 + difference 2 0) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA715 + difference 0 2) (sourceB715 + difference 2 0) sourceC715) = raw11664 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw11664; decide +kernel
    rw [ha]
    exact (canonical11664 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA715 + difference 0 3) (sourceB715 + difference 3 0) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA715 + difference 0 3) (sourceB715 + difference 3 0) sourceC715) = raw11999 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw11999; decide +kernel
    rw [ha]
    exact (canonical11999 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA715 + difference 0 4) (sourceB715 + difference 4 0) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA715 + difference 0 4) (sourceB715 + difference 4 0) sourceC715) = raw12000 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12000; decide +kernel
    rw [ha]
    exact (canonical12000 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA715 + difference 0 5) (sourceB715 + difference 5 0) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5227) := by
    have ha : (tripleCharges (sourceA715 + difference 0 5) (sourceB715 + difference 5 0) sourceC715) = raw12001 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12001; decide +kernel
    rw [ha]
    exact (canonical12001 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA715 + difference 1 0) (sourceB715 + difference 0 1) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA715 + difference 1 0) (sourceB715 + difference 0 1) sourceC715) = raw12002 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12002; decide +kernel
    rw [ha]
    exact (canonical12002 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA715 + difference 1 2) (sourceB715 + difference 2 1) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA715 + difference 1 2) (sourceB715 + difference 2 1) sourceC715) = raw11669 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw11669; decide +kernel
    rw [ha]
    exact (canonical11669 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA715 + difference 1 3) (sourceB715 + difference 3 1) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA715 + difference 1 3) (sourceB715 + difference 3 1) sourceC715) = raw12003 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12003; decide +kernel
    rw [ha]
    exact (canonical12003 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA715 + difference 1 4) (sourceB715 + difference 4 1) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA715 + difference 1 4) (sourceB715 + difference 4 1) sourceC715) = raw12004 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12004; decide +kernel
    rw [ha]
    exact (canonical12004 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA715 + difference 1 5) (sourceB715 + difference 5 1) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA715 + difference 1 5) (sourceB715 + difference 5 1) sourceC715) = raw12005 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12005; decide +kernel
    rw [ha]
    exact (canonical12005 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA715 + difference 2 0) (sourceB715 + difference 0 2) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4793) := by
    have ha : (tripleCharges (sourceA715 + difference 2 0) (sourceB715 + difference 0 2) sourceC715) = raw12006 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12006; decide +kernel
    rw [ha]
    exact (canonical12006 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA715 + difference 2 1) (sourceB715 + difference 1 2) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4794) := by
    have ha : (tripleCharges (sourceA715 + difference 2 1) (sourceB715 + difference 1 2) sourceC715) = raw12007 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12007; decide +kernel
    rw [ha]
    exact (canonical12007 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA715 + difference 2 3) (sourceB715 + difference 3 2) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4806) := by
    have ha : (tripleCharges (sourceA715 + difference 2 3) (sourceB715 + difference 3 2) sourceC715) = raw12008 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12008; decide +kernel
    rw [ha]
    exact (canonical12008 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA715 + difference 2 4) (sourceB715 + difference 4 2) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4806) := by
    have ha : (tripleCharges (sourceA715 + difference 2 4) (sourceB715 + difference 4 2) sourceC715) = raw12009 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12009; decide +kernel
    rw [ha]
    exact (canonical12009 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA715 + difference 2 5) (sourceB715 + difference 5 2) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4878) := by
    have ha : (tripleCharges (sourceA715 + difference 2 5) (sourceB715 + difference 5 2) sourceC715) = raw12010 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12010; decide +kernel
    rw [ha]
    exact (canonical12010 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA715 + difference 3 0) (sourceB715 + difference 0 3) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA715 + difference 3 0) (sourceB715 + difference 0 3) sourceC715) = raw12011 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12011; decide +kernel
    rw [ha]
    exact (canonical12011 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA715 + difference 3 1) (sourceB715 + difference 1 3) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA715 + difference 3 1) (sourceB715 + difference 1 3) sourceC715) = raw12012 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12012; decide +kernel
    rw [ha]
    exact (canonical12012 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA715 + difference 3 2) (sourceB715 + difference 2 3) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA715 + difference 3 2) (sourceB715 + difference 2 3) sourceC715) = raw11679 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw11679; decide +kernel
    rw [ha]
    exact (canonical11679 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA715 + difference 3 4) (sourceB715 + difference 4 3) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5263) := by
    have ha : (tripleCharges (sourceA715 + difference 3 4) (sourceB715 + difference 4 3) sourceC715) = raw12013 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12013; decide +kernel
    rw [ha]
    exact (canonical12013 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA715 + difference 3 5) (sourceB715 + difference 5 3) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA715 + difference 3 5) (sourceB715 + difference 5 3) sourceC715) = raw12014 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12014; decide +kernel
    rw [ha]
    exact (canonical12014 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA715 + difference 4 0) (sourceB715 + difference 0 4) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA715 + difference 4 0) (sourceB715 + difference 0 4) sourceC715) = raw12015 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12015; decide +kernel
    rw [ha]
    exact (canonical12015 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA715 + difference 4 1) (sourceB715 + difference 1 4) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA715 + difference 4 1) (sourceB715 + difference 1 4) sourceC715) = raw12016 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12016; decide +kernel
    rw [ha]
    exact (canonical12016 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA715 + difference 4 2) (sourceB715 + difference 2 4) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA715 + difference 4 2) (sourceB715 + difference 2 4) sourceC715) = raw11684 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw11684; decide +kernel
    rw [ha]
    exact (canonical11684 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA715 + difference 4 3) (sourceB715 + difference 3 4) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5263) := by
    have ha : (tripleCharges (sourceA715 + difference 4 3) (sourceB715 + difference 3 4) sourceC715) = raw12017 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12017; decide +kernel
    rw [ha]
    exact (canonical12017 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA715 + difference 4 5) (sourceB715 + difference 5 4) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA715 + difference 4 5) (sourceB715 + difference 5 4) sourceC715) = raw12018 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12018; decide +kernel
    rw [ha]
    exact (canonical12018 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA715 + difference 5 0) (sourceB715 + difference 0 5) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA715 + difference 5 0) (sourceB715 + difference 0 5) sourceC715) = raw11670 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw11670; decide +kernel
    rw [ha]
    exact (canonical11670 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA715 + difference 5 1) (sourceB715 + difference 1 5) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5230) := by
    have ha : (tripleCharges (sourceA715 + difference 5 1) (sourceB715 + difference 1 5) sourceC715) = raw11671 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw11671; decide +kernel
    rw [ha]
    exact (canonical11671 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA715 + difference 5 2) (sourceB715 + difference 2 5) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA715 + difference 5 2) (sourceB715 + difference 2 5) sourceC715) = raw12019 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw12019; decide +kernel
    rw [ha]
    exact (canonical12019 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA715 + difference 5 3) (sourceB715 + difference 3 5) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5262) := by
    have ha : (tripleCharges (sourceA715 + difference 5 3) (sourceB715 + difference 3 5) sourceC715) = raw11672 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw11672; decide +kernel
    rw [ha]
    exact (canonical11672 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA715 + difference 5 4) (sourceB715 + difference 4 5) sourceC715) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5262) := by
    have ha : (tripleCharges (sourceA715 + difference 5 4) (sourceB715 + difference 4 5) sourceC715) = raw11673 := by
      apply Matrix.ext; unfold tripleCharges sourceA715 sourceB715 sourceC715 difference raw11673; decide +kernel
    rw [ha]
    exact (canonical11673 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA715 sourceB715 sourceC715
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm715, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq717 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm717 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA717 + difference 0 1) (sourceB717 + difference 1 0) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2676) := by
    have ha : (tripleCharges (sourceA717 + difference 0 1) (sourceB717 + difference 1 0) sourceC717) = raw12042 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12042; decide +kernel
    rw [ha]
    exact (canonical12042 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA717 + difference 0 2) (sourceB717 + difference 2 0) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA717 + difference 0 2) (sourceB717 + difference 2 0) sourceC717) = raw11724 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw11724; decide +kernel
    rw [ha]
    exact (canonical11724 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA717 + difference 0 3) (sourceB717 + difference 3 0) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA717 + difference 0 3) (sourceB717 + difference 3 0) sourceC717) = raw12043 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12043; decide +kernel
    rw [ha]
    exact (canonical12043 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA717 + difference 0 4) (sourceB717 + difference 4 0) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA717 + difference 0 4) (sourceB717 + difference 4 0) sourceC717) = raw12044 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12044; decide +kernel
    rw [ha]
    exact (canonical12044 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA717 + difference 0 5) (sourceB717 + difference 5 0) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA717 + difference 0 5) (sourceB717 + difference 5 0) sourceC717) = raw12045 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12045; decide +kernel
    rw [ha]
    exact (canonical12045 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA717 + difference 1 0) (sourceB717 + difference 0 1) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA717 + difference 1 0) (sourceB717 + difference 0 1) sourceC717) = raw12046 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12046; decide +kernel
    rw [ha]
    exact (canonical12046 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA717 + difference 1 2) (sourceB717 + difference 2 1) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA717 + difference 1 2) (sourceB717 + difference 2 1) sourceC717) = raw11729 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw11729; decide +kernel
    rw [ha]
    exact (canonical11729 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA717 + difference 1 3) (sourceB717 + difference 3 1) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA717 + difference 1 3) (sourceB717 + difference 3 1) sourceC717) = raw12047 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12047; decide +kernel
    rw [ha]
    exact (canonical12047 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA717 + difference 1 4) (sourceB717 + difference 4 1) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA717 + difference 1 4) (sourceB717 + difference 4 1) sourceC717) = raw12048 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12048; decide +kernel
    rw [ha]
    exact (canonical12048 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA717 + difference 1 5) (sourceB717 + difference 5 1) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA717 + difference 1 5) (sourceB717 + difference 5 1) sourceC717) = raw12049 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12049; decide +kernel
    rw [ha]
    exact (canonical12049 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA717 + difference 2 0) (sourceB717 + difference 0 2) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA717 + difference 2 0) (sourceB717 + difference 0 2) sourceC717) = raw12050 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12050; decide +kernel
    rw [ha]
    exact (canonical12050 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA717 + difference 2 1) (sourceB717 + difference 1 2) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2011) := by
    have ha : (tripleCharges (sourceA717 + difference 2 1) (sourceB717 + difference 1 2) sourceC717) = raw12051 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12051; decide +kernel
    rw [ha]
    exact (canonical12051 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA717 + difference 2 3) (sourceB717 + difference 3 2) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2024) := by
    have ha : (tripleCharges (sourceA717 + difference 2 3) (sourceB717 + difference 3 2) sourceC717) = raw12052 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12052; decide +kernel
    rw [ha]
    exact (canonical12052 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA717 + difference 2 4) (sourceB717 + difference 4 2) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2024) := by
    have ha : (tripleCharges (sourceA717 + difference 2 4) (sourceB717 + difference 4 2) sourceC717) = raw12053 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12053; decide +kernel
    rw [ha]
    exact (canonical12053 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA717 + difference 2 5) (sourceB717 + difference 5 2) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2234) := by
    have ha : (tripleCharges (sourceA717 + difference 2 5) (sourceB717 + difference 5 2) sourceC717) = raw12054 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12054; decide +kernel
    rw [ha]
    exact (canonical12054 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA717 + difference 3 0) (sourceB717 + difference 0 3) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3203) := by
    have ha : (tripleCharges (sourceA717 + difference 3 0) (sourceB717 + difference 0 3) sourceC717) = raw12055 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12055; decide +kernel
    rw [ha]
    exact (canonical12055 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA717 + difference 3 1) (sourceB717 + difference 1 3) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3043) := by
    have ha : (tripleCharges (sourceA717 + difference 3 1) (sourceB717 + difference 1 3) sourceC717) = raw12056 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12056; decide +kernel
    rw [ha]
    exact (canonical12056 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA717 + difference 3 2) (sourceB717 + difference 2 3) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA717 + difference 3 2) (sourceB717 + difference 2 3) sourceC717) = raw11739 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw11739; decide +kernel
    rw [ha]
    exact (canonical11739 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA717 + difference 3 4) (sourceB717 + difference 4 3) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3036) := by
    have ha : (tripleCharges (sourceA717 + difference 3 4) (sourceB717 + difference 4 3) sourceC717) = raw12057 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12057; decide +kernel
    rw [ha]
    exact (canonical12057 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA717 + difference 3 5) (sourceB717 + difference 5 3) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA717 + difference 3 5) (sourceB717 + difference 5 3) sourceC717) = raw12058 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12058; decide +kernel
    rw [ha]
    exact (canonical12058 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA717 + difference 4 0) (sourceB717 + difference 0 4) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3203) := by
    have ha : (tripleCharges (sourceA717 + difference 4 0) (sourceB717 + difference 0 4) sourceC717) = raw12059 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12059; decide +kernel
    rw [ha]
    exact (canonical12059 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA717 + difference 4 1) (sourceB717 + difference 1 4) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3043) := by
    have ha : (tripleCharges (sourceA717 + difference 4 1) (sourceB717 + difference 1 4) sourceC717) = raw12060 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12060; decide +kernel
    rw [ha]
    exact (canonical12060 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA717 + difference 4 2) (sourceB717 + difference 2 4) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA717 + difference 4 2) (sourceB717 + difference 2 4) sourceC717) = raw11744 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw11744; decide +kernel
    rw [ha]
    exact (canonical11744 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA717 + difference 4 3) (sourceB717 + difference 3 4) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3036) := by
    have ha : (tripleCharges (sourceA717 + difference 4 3) (sourceB717 + difference 3 4) sourceC717) = raw12061 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12061; decide +kernel
    rw [ha]
    exact (canonical12061 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA717 + difference 4 5) (sourceB717 + difference 5 4) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA717 + difference 4 5) (sourceB717 + difference 5 4) sourceC717) = raw12062 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12062; decide +kernel
    rw [ha]
    exact (canonical12062 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA717 + difference 5 0) (sourceB717 + difference 0 5) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA717 + difference 5 0) (sourceB717 + difference 0 5) sourceC717) = raw11730 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw11730; decide +kernel
    rw [ha]
    exact (canonical11730 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA717 + difference 5 1) (sourceB717 + difference 1 5) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3041) := by
    have ha : (tripleCharges (sourceA717 + difference 5 1) (sourceB717 + difference 1 5) sourceC717) = raw11731 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw11731; decide +kernel
    rw [ha]
    exact (canonical11731 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA717 + difference 5 2) (sourceB717 + difference 2 5) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3085) := by
    have ha : (tripleCharges (sourceA717 + difference 5 2) (sourceB717 + difference 2 5) sourceC717) = raw12063 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw12063; decide +kernel
    rw [ha]
    exact (canonical12063 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA717 + difference 5 3) (sourceB717 + difference 3 5) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3034) := by
    have ha : (tripleCharges (sourceA717 + difference 5 3) (sourceB717 + difference 3 5) sourceC717) = raw11732 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw11732; decide +kernel
    rw [ha]
    exact (canonical11732 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA717 + difference 5 4) (sourceB717 + difference 4 5) sourceC717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3034) := by
    have ha : (tripleCharges (sourceA717 + difference 5 4) (sourceB717 + difference 4 5) sourceC717) = raw11733 := by
      apply Matrix.ext; unfold tripleCharges sourceA717 sourceB717 sourceC717 difference raw11733; decide +kernel
    rw [ha]
    exact (canonical11733 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA717 sourceB717 sourceC717
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm717, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq718 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm718 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA718 + difference 0 0) (sourceB718 + difference 0 0) sourceC718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA718 + difference 0 0) (sourceB718 + difference 0 0) sourceC718) = raw11764 := by
      apply Matrix.ext; unfold tripleCharges sourceA718 sourceB718 sourceC718 difference raw11764; decide +kernel
    rw [ha]
    exact (canonical11764 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA718 + difference 0 1) (sourceB718 + difference 1 0) sourceC718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3378) := by
    have ha : (tripleCharges (sourceA718 + difference 0 1) (sourceB718 + difference 1 0) sourceC718) = raw12064 := by
      apply Matrix.ext; unfold tripleCharges sourceA718 sourceB718 sourceC718 difference raw12064; decide +kernel
    rw [ha]
    exact (canonical12064 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA718 + difference 0 2) (sourceB718 + difference 2 0) sourceC718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA718 + difference 0 2) (sourceB718 + difference 2 0) sourceC718) = raw11755 := by
      apply Matrix.ext; unfold tripleCharges sourceA718 sourceB718 sourceC718 difference raw11755; decide +kernel
    rw [ha]
    exact (canonical11755 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA718 + difference 0 3) (sourceB718 + difference 3 0) sourceC718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA718 + difference 0 3) (sourceB718 + difference 3 0) sourceC718) = raw12065 := by
      apply Matrix.ext; unfold tripleCharges sourceA718 sourceB718 sourceC718 difference raw12065; decide +kernel
    rw [ha]
    exact (canonical12065 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA718 + difference 0 4) (sourceB718 + difference 4 0) sourceC718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA718 + difference 0 4) (sourceB718 + difference 4 0) sourceC718) = raw12066 := by
      apply Matrix.ext; unfold tripleCharges sourceA718 sourceB718 sourceC718 difference raw12066; decide +kernel
    rw [ha]
    exact (canonical12066 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA718 + difference 0 5) (sourceB718 + difference 5 0) sourceC718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3390) := by
    have ha : (tripleCharges (sourceA718 + difference 0 5) (sourceB718 + difference 5 0) sourceC718) = raw12067 := by
      apply Matrix.ext; unfold tripleCharges sourceA718 sourceB718 sourceC718 difference raw12067; decide +kernel
    rw [ha]
    exact (canonical12067 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA718 + sourceB718) sourceC718) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA718 + sourceB718) sourceC718) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA718 sourceB718 sourceC718 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA718 sourceB718 sourceC718
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm718, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck609 : Integer.Sparse.reindex keyMap MixedData.row609 = numericRow609 := by decide +kernel

theorem numericCheck609 (x : Master → ℝ) : Integer.Sparse.eval numericRow609 x =
    (1 : ℝ) * reducedSource609 x := by
  norm_num [numericRow609, reducedSource609, Integer.Sparse.eval, Sparse.eval, nodeValue2730, nodeValue3812, nodeValue3906, nodeValue4092]

theorem reindexCheck610 : Integer.Sparse.reindex keyMap MixedData.row610 = numericRow610 := by decide +kernel

theorem numericCheck610 (x : Master → ℝ) : Integer.Sparse.eval numericRow610 x =
    (1 : ℝ) * reducedSource610 x := by
  norm_num [numericRow610, reducedSource610, Integer.Sparse.eval, Sparse.eval, nodeValue1276, nodeValue2645, nodeValue2730, nodeValue2757, nodeValue2773, nodeValue4092]

theorem reindexCheck611 : Integer.Sparse.reindex keyMap MixedData.row611 = numericRow611 := by decide +kernel

theorem numericCheck611 (x : Master → ℝ) : Integer.Sparse.eval numericRow611 x =
    (1 : ℝ) * reducedSource611 x := by
  norm_num [numericRow611, reducedSource611, Integer.Sparse.eval, Sparse.eval, nodeValue2493, nodeValue2494, nodeValue2508, nodeValue2730, nodeValue3812, nodeValue4092]

theorem reindexCheck615 : Integer.Sparse.reindex keyMap MixedData.row615 = numericRow615 := by decide +kernel

theorem numericCheck615 (x : Master → ℝ) : Integer.Sparse.eval numericRow615 x =
    (1 : ℝ) * reducedSource615 x := by
  norm_num [numericRow615, reducedSource615, Integer.Sparse.eval, Sparse.eval, nodeValue3037, nodeValue3846, nodeValue3849, nodeValue3910, nodeValue3957, nodeValue4091]

theorem reindexCheck616 : Integer.Sparse.reindex keyMap MixedData.row616 = numericRow616 := by decide +kernel

theorem numericCheck616 (x : Master → ℝ) : Integer.Sparse.eval numericRow616 x =
    (1 : ℝ) * reducedSource616 x := by
  norm_num [numericRow616, reducedSource616, Integer.Sparse.eval, Sparse.eval, nodeValue1358, nodeValue1360, nodeValue1366, nodeValue1421, nodeValue3037, nodeValue4091]

theorem reindexCheck617 : Integer.Sparse.reindex keyMap MixedData.row617 = numericRow617 := by decide +kernel

theorem numericCheck617 (x : Master → ℝ) : Integer.Sparse.eval numericRow617 x =
    (1 : ℝ) * reducedSource617 x := by
  norm_num [numericRow617, reducedSource617, Integer.Sparse.eval, Sparse.eval, nodeValue1366, nodeValue2880, nodeValue3037, nodeValue3053, nodeValue4091]

theorem reindexCheck618 : Integer.Sparse.reindex keyMap MixedData.row618 = numericRow618 := by decide +kernel

theorem numericCheck618 (x : Master → ℝ) : Integer.Sparse.eval numericRow618 x =
    (1 : ℝ) * reducedSource618 x := by
  norm_num [numericRow618, reducedSource618, Integer.Sparse.eval, Sparse.eval, nodeValue2862, nodeValue2864, nodeValue2880, nodeValue3037, nodeValue3957, nodeValue4091]

theorem reindexCheck619 : Integer.Sparse.reindex keyMap MixedData.row619 = numericRow619 := by decide +kernel

theorem numericCheck619 (x : Master → ℝ) : Integer.Sparse.eval numericRow619 x =
    (1 : ℝ) * reducedSource619 x := by
  norm_num [numericRow619, reducedSource619, Integer.Sparse.eval, Sparse.eval, nodeValue2573, nodeValue3029, nodeValue3030, nodeValue3037, nodeValue3849, nodeValue4091]

theorem reindexCheck620 : Integer.Sparse.reindex keyMap MixedData.row620 = numericRow620 := by decide +kernel

theorem numericCheck620 (x : Master → ℝ) : Integer.Sparse.eval numericRow620 x =
    (17280 : ℝ) * reducedSource620 x := by
  norm_num [numericRow620, reducedSource620, Integer.Sparse.eval, Sparse.eval, nodeValue4793, nodeValue4794, nodeValue4795, nodeValue4805, nodeValue4806, nodeValue4878, nodeValue4889, nodeValue5226, nodeValue5227, nodeValue5230, nodeValue5231, nodeValue5256, nodeValue5257, nodeValue5262, nodeValue5263, nodeValue5265, nodeValue5292, nodeValue5299, nodeValue5301]
  ring

theorem reindexCheck621 : Integer.Sparse.reindex keyMap MixedData.row621 = numericRow621 := by decide +kernel

theorem numericCheck621 (x : Master → ℝ) : Integer.Sparse.eval numericRow621 x =
    (4320 : ℝ) * reducedSource621 x := by
  norm_num [numericRow621, reducedSource621, Integer.Sparse.eval, Sparse.eval, nodeValue2117, nodeValue2118, nodeValue2131, nodeValue2213, nodeValue2214, nodeValue2219, nodeValue2277, nodeValue2675, nodeValue2676, nodeValue2720, nodeValue2721, nodeValue2727, nodeValue2728, nodeValue2730, nodeValue2766, nodeValue2773, nodeValue2775, nodeValue3043, nodeValue3087, nodeValue3091, nodeValue3093]
  ring

theorem reindexCheck622 : Integer.Sparse.reindex keyMap MixedData.row622 = numericRow622 := by decide +kernel

theorem numericCheck622 (x : Master → ℝ) : Integer.Sparse.eval numericRow622 x =
    (4320 : ℝ) * reducedSource622 x := by
  norm_num [numericRow622, reducedSource622, Integer.Sparse.eval, Sparse.eval, nodeValue2010, nodeValue2011, nodeValue2024, nodeValue2234, nodeValue2669, nodeValue2671, nodeValue2676, nodeValue2721, nodeValue3034, nodeValue3036, nodeValue3037, nodeValue3041, nodeValue3043, nodeValue3051, nodeValue3053, nodeValue3085, nodeValue3087, nodeValue3100, nodeValue3199, nodeValue3203, nodeValue3223]
  ring

theorem reindexCheck623 : Integer.Sparse.reindex keyMap MixedData.row623 = numericRow623 := by decide +kernel

theorem numericCheck623 (x : Master → ℝ) : Integer.Sparse.eval numericRow623 x =
    (1 : ℝ) * reducedSource623 x := by
  norm_num [numericRow623, reducedSource623, Integer.Sparse.eval, Sparse.eval, nodeValue3376, nodeValue3378, nodeValue3390, nodeValue3526, nodeValue3532, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero609 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource609 (mixedVector B) = 0 := by
  have h2730 : mixedVector B (Sum.inr 2730) = Sparse.eval nodeValue2730 (mixedVector B) := by
    change mixedMoment B node2730 node2730Labels = _
    exact sound2730 B hB hF
  have h3812 : mixedVector B (Sum.inr 3812) = Sparse.eval nodeValue3812 (mixedVector B) := by
    change mixedMoment B node3812 node3812Labels = _
    exact sound3812 B hB hF
  have h3906 : mixedVector B (Sum.inr 3906) = Sparse.eval nodeValue3906 (mixedVector B) := by
    change mixedMoment B node3906 node3906Labels = _
    exact sound3906 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm702, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2730, h3812, h3906, h4092, reducedSource609] using sourceEq702 B hB

theorem rowSound609 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row609 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck609, numericCheck609, reducedZero609 B hB hF, mul_zero]

theorem reducedZero610 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource610 (mixedVector B) = 0 := by
  have h1276 : mixedVector B (Sum.inr 1276) = Sparse.eval nodeValue1276 (mixedVector B) := by
    change mixedMoment B node1276 node1276Labels = _
    exact sound1276 B hB hF
  have h2645 : mixedVector B (Sum.inr 2645) = Sparse.eval nodeValue2645 (mixedVector B) := by
    change mixedMoment B node2645 node2645Labels = _
    exact sound2645 B hB hF
  have h2730 : mixedVector B (Sum.inr 2730) = Sparse.eval nodeValue2730 (mixedVector B) := by
    change mixedMoment B node2730 node2730Labels = _
    exact sound2730 B hB hF
  have h2757 : mixedVector B (Sum.inr 2757) = Sparse.eval nodeValue2757 (mixedVector B) := by
    change mixedMoment B node2757 node2757Labels = _
    exact sound2757 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm704, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1276, h2645, h2730, h2757, h2773, h4092, reducedSource610] using sourceEq704 B hB

theorem rowSound610 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row610 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck610, numericCheck610, reducedZero610 B hB hF, mul_zero]

theorem reducedZero611 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource611 (mixedVector B) = 0 := by
  have h2493 : mixedVector B (Sum.inr 2493) = Sparse.eval nodeValue2493 (mixedVector B) := by
    change mixedMoment B node2493 node2493Labels = _
    exact sound2493 B hB hF
  have h2494 : mixedVector B (Sum.inr 2494) = Sparse.eval nodeValue2494 (mixedVector B) := by
    change mixedMoment B node2494 node2494Labels = _
    exact sound2494 B hB hF
  have h2508 : mixedVector B (Sum.inr 2508) = Sparse.eval nodeValue2508 (mixedVector B) := by
    change mixedMoment B node2508 node2508Labels = _
    exact sound2508 B hB hF
  have h2730 : mixedVector B (Sum.inr 2730) = Sparse.eval nodeValue2730 (mixedVector B) := by
    change mixedMoment B node2730 node2730Labels = _
    exact sound2730 B hB hF
  have h3812 : mixedVector B (Sum.inr 3812) = Sparse.eval nodeValue3812 (mixedVector B) := by
    change mixedMoment B node3812 node3812Labels = _
    exact sound3812 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm705, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2493, h2494, h2508, h2730, h3812, h4092, reducedSource611] using sourceEq705 B hB

theorem rowSound611 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row611 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck611, numericCheck611, reducedZero611 B hB hF, mul_zero]

theorem reducedZero615 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource615 (mixedVector B) = 0 := by
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3846 : mixedVector B (Sum.inr 3846) = Sparse.eval nodeValue3846 (mixedVector B) := by
    change mixedMoment B node3846 node3846Labels = _
    exact sound3846 B hB hF
  have h3849 : mixedVector B (Sum.inr 3849) = Sparse.eval nodeValue3849 (mixedVector B) := by
    change mixedMoment B node3849 node3849Labels = _
    exact sound3849 B hB hF
  have h3910 : mixedVector B (Sum.inr 3910) = Sparse.eval nodeValue3910 (mixedVector B) := by
    change mixedMoment B node3910 node3910Labels = _
    exact sound3910 B hB hF
  have h3957 : mixedVector B (Sum.inr 3957) = Sparse.eval nodeValue3957 (mixedVector B) := by
    change mixedMoment B node3957 node3957Labels = _
    exact sound3957 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm709, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3037, h3846, h3849, h3910, h3957, h4091, reducedSource615] using sourceEq709 B hB

theorem rowSound615 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row615 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck615, numericCheck615, reducedZero615 B hB hF, mul_zero]

theorem reducedZero616 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource616 (mixedVector B) = 0 := by
  have h1358 : mixedVector B (Sum.inr 1358) = Sparse.eval nodeValue1358 (mixedVector B) := by
    change mixedMoment B node1358 node1358Labels = _
    exact sound1358 B hB hF
  have h1360 : mixedVector B (Sum.inr 1360) = Sparse.eval nodeValue1360 (mixedVector B) := by
    change mixedMoment B node1360 node1360Labels = _
    exact sound1360 B hB hF
  have h1366 : mixedVector B (Sum.inr 1366) = Sparse.eval nodeValue1366 (mixedVector B) := by
    change mixedMoment B node1366 node1366Labels = _
    exact sound1366 B hB hF
  have h1421 : mixedVector B (Sum.inr 1421) = Sparse.eval nodeValue1421 (mixedVector B) := by
    change mixedMoment B node1421 node1421Labels = _
    exact sound1421 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm710, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1358, h1360, h1366, h1421, h3037, h4091, reducedSource616] using sourceEq710 B hB

theorem rowSound616 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row616 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck616, numericCheck616, reducedZero616 B hB hF, mul_zero]

theorem reducedZero617 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource617 (mixedVector B) = 0 := by
  have h1366 : mixedVector B (Sum.inr 1366) = Sparse.eval nodeValue1366 (mixedVector B) := by
    change mixedMoment B node1366 node1366Labels = _
    exact sound1366 B hB hF
  have h2880 : mixedVector B (Sum.inr 2880) = Sparse.eval nodeValue2880 (mixedVector B) := by
    change mixedMoment B node2880 node2880Labels = _
    exact sound2880 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3053 : mixedVector B (Sum.inr 3053) = Sparse.eval nodeValue3053 (mixedVector B) := by
    change mixedMoment B node3053 node3053Labels = _
    exact sound3053 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm711, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1366, h2880, h3037, h3053, h4091, reducedSource617] using sourceEq711 B hB

theorem rowSound617 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row617 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck617, numericCheck617, reducedZero617 B hB hF, mul_zero]

theorem reducedZero618 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource618 (mixedVector B) = 0 := by
  have h2862 : mixedVector B (Sum.inr 2862) = Sparse.eval nodeValue2862 (mixedVector B) := by
    change mixedMoment B node2862 node2862Labels = _
    exact sound2862 B hB hF
  have h2864 : mixedVector B (Sum.inr 2864) = Sparse.eval nodeValue2864 (mixedVector B) := by
    change mixedMoment B node2864 node2864Labels = _
    exact sound2864 B hB hF
  have h2880 : mixedVector B (Sum.inr 2880) = Sparse.eval nodeValue2880 (mixedVector B) := by
    change mixedMoment B node2880 node2880Labels = _
    exact sound2880 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3957 : mixedVector B (Sum.inr 3957) = Sparse.eval nodeValue3957 (mixedVector B) := by
    change mixedMoment B node3957 node3957Labels = _
    exact sound3957 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm713, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2862, h2864, h2880, h3037, h3957, h4091, reducedSource618] using sourceEq713 B hB

theorem rowSound618 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row618 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck618, numericCheck618, reducedZero618 B hB hF, mul_zero]

theorem reducedZero619 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource619 (mixedVector B) = 0 := by
  have h2573 : mixedVector B (Sum.inr 2573) = Sparse.eval nodeValue2573 (mixedVector B) := by
    change mixedMoment B node2573 node2573Labels = _
    exact sound2573 B hB hF
  have h3029 : mixedVector B (Sum.inr 3029) = Sparse.eval nodeValue3029 (mixedVector B) := by
    change mixedMoment B node3029 node3029Labels = _
    exact sound3029 B hB hF
  have h3030 : mixedVector B (Sum.inr 3030) = Sparse.eval nodeValue3030 (mixedVector B) := by
    change mixedMoment B node3030 node3030Labels = _
    exact sound3030 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3849 : mixedVector B (Sum.inr 3849) = Sparse.eval nodeValue3849 (mixedVector B) := by
    change mixedMoment B node3849 node3849Labels = _
    exact sound3849 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm714, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2573, h3029, h3030, h3037, h3849, h4091, reducedSource619] using sourceEq714 B hB

theorem rowSound619 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row619 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck619, numericCheck619, reducedZero619 B hB hF, mul_zero]

theorem reducedZero620 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource620 (mixedVector B) = 0 := by
  have h4793 : mixedVector B (Sum.inr 4793) = Sparse.eval nodeValue4793 (mixedVector B) := by
    change mixedMoment B node4793 node4793Labels = _
    exact sound4793 B hB hF
  have h4794 : mixedVector B (Sum.inr 4794) = Sparse.eval nodeValue4794 (mixedVector B) := by
    change mixedMoment B node4794 node4794Labels = _
    exact sound4794 B hB hF
  have h4795 : mixedVector B (Sum.inr 4795) = Sparse.eval nodeValue4795 (mixedVector B) := by
    change mixedMoment B node4795 node4795Labels = _
    exact sound4795 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4806 : mixedVector B (Sum.inr 4806) = Sparse.eval nodeValue4806 (mixedVector B) := by
    change mixedMoment B node4806 node4806Labels = _
    exact sound4806 B hB hF
  have h4878 : mixedVector B (Sum.inr 4878) = Sparse.eval nodeValue4878 (mixedVector B) := by
    change mixedMoment B node4878 node4878Labels = _
    exact sound4878 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h5226 : mixedVector B (Sum.inr 5226) = Sparse.eval nodeValue5226 (mixedVector B) := by
    change mixedMoment B node5226 node5226Labels = _
    exact sound5226 B hB hF
  have h5227 : mixedVector B (Sum.inr 5227) = Sparse.eval nodeValue5227 (mixedVector B) := by
    change mixedMoment B node5227 node5227Labels = _
    exact sound5227 B hB hF
  have h5230 : mixedVector B (Sum.inr 5230) = Sparse.eval nodeValue5230 (mixedVector B) := by
    change mixedMoment B node5230 node5230Labels = _
    exact sound5230 B hB hF
  have h5231 : mixedVector B (Sum.inr 5231) = Sparse.eval nodeValue5231 (mixedVector B) := by
    change mixedMoment B node5231 node5231Labels = _
    exact sound5231 B hB hF
  have h5256 : mixedVector B (Sum.inr 5256) = Sparse.eval nodeValue5256 (mixedVector B) := by
    change mixedMoment B node5256 node5256Labels = _
    exact sound5256 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5262 : mixedVector B (Sum.inr 5262) = Sparse.eval nodeValue5262 (mixedVector B) := by
    change mixedMoment B node5262 node5262Labels = _
    exact sound5262 B hB hF
  have h5263 : mixedVector B (Sum.inr 5263) = Sparse.eval nodeValue5263 (mixedVector B) := by
    change mixedMoment B node5263 node5263Labels = _
    exact sound5263 B hB hF
  have h5265 : mixedVector B (Sum.inr 5265) = Sparse.eval nodeValue5265 (mixedVector B) := by
    change mixedMoment B node5265 node5265Labels = _
    exact sound5265 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292_e B hB hF
  have h5299 : mixedVector B (Sum.inr 5299) = Sparse.eval nodeValue5299 (mixedVector B) := by
    change mixedMoment B node5299 node5299Labels = _
    exact sound5299 B hB hF
  have h5301 : mixedVector B (Sum.inr 5301) = Sparse.eval nodeValue5301 (mixedVector B) := by
    change mixedMoment B node5301 node5301Labels = _
    exact sound5301 B hB hF
  simpa only [sourceForm715, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4793, h4794, h4795, h4805, h4806, h4878, h4889, h5226, h5227, h5230, h5231, h5256, h5257, h5262, h5263, h5265, h5292, h5299, h5301, reducedSource620] using sourceEq715 B hB

theorem rowSound620 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row620 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck620, numericCheck620, reducedZero620 B hB hF, mul_zero]

theorem rowSound621 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row621 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck621, numericCheck621, reducedZero621_e B hB hF, mul_zero]

theorem reducedZero622 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource622 (mixedVector B) = 0 := by
  have h2010 : mixedVector B (Sum.inr 2010) = Sparse.eval nodeValue2010 (mixedVector B) := by
    change mixedMoment B node2010 node2010Labels = _
    exact sound2010 B hB hF
  have h2011 : mixedVector B (Sum.inr 2011) = Sparse.eval nodeValue2011 (mixedVector B) := by
    change mixedMoment B node2011 node2011Labels = _
    exact sound2011 B hB hF
  have h2024 : mixedVector B (Sum.inr 2024) = Sparse.eval nodeValue2024 (mixedVector B) := by
    change mixedMoment B node2024 node2024Labels = _
    exact sound2024 B hB hF
  have h2234 : mixedVector B (Sum.inr 2234) = Sparse.eval nodeValue2234 (mixedVector B) := by
    change mixedMoment B node2234 node2234Labels = _
    exact sound2234 B hB hF
  have h2669 : mixedVector B (Sum.inr 2669) = Sparse.eval nodeValue2669 (mixedVector B) := by
    change mixedMoment B node2669 node2669Labels = _
    exact sound2669 B hB hF
  have h2671 : mixedVector B (Sum.inr 2671) = Sparse.eval nodeValue2671 (mixedVector B) := by
    change mixedMoment B node2671 node2671Labels = _
    exact sound2671 B hB hF
  have h2676 : mixedVector B (Sum.inr 2676) = Sparse.eval nodeValue2676 (mixedVector B) := by
    change mixedMoment B node2676 node2676Labels = _
    exact sound2676 B hB hF
  have h2721 : mixedVector B (Sum.inr 2721) = Sparse.eval nodeValue2721 (mixedVector B) := by
    change mixedMoment B node2721 node2721Labels = _
    exact sound2721 B hB hF
  have h3034 : mixedVector B (Sum.inr 3034) = Sparse.eval nodeValue3034 (mixedVector B) := by
    change mixedMoment B node3034 node3034Labels = _
    exact sound3034 B hB hF
  have h3036 : mixedVector B (Sum.inr 3036) = Sparse.eval nodeValue3036 (mixedVector B) := by
    change mixedMoment B node3036 node3036Labels = _
    exact sound3036 B hB hF
  have h3037 : mixedVector B (Sum.inr 3037) = Sparse.eval nodeValue3037 (mixedVector B) := by
    change mixedMoment B node3037 node3037Labels = _
    exact sound3037 B hB hF
  have h3041 : mixedVector B (Sum.inr 3041) = Sparse.eval nodeValue3041 (mixedVector B) := by
    change mixedMoment B node3041 node3041Labels = _
    exact sound3041 B hB hF
  have h3043 : mixedVector B (Sum.inr 3043) = Sparse.eval nodeValue3043 (mixedVector B) := by
    change mixedMoment B node3043 node3043Labels = _
    exact sound3043 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3053 : mixedVector B (Sum.inr 3053) = Sparse.eval nodeValue3053 (mixedVector B) := by
    change mixedMoment B node3053 node3053Labels = _
    exact sound3053 B hB hF
  have h3085 : mixedVector B (Sum.inr 3085) = Sparse.eval nodeValue3085 (mixedVector B) := by
    change mixedMoment B node3085 node3085Labels = _
    exact sound3085 B hB hF
  have h3087 : mixedVector B (Sum.inr 3087) = Sparse.eval nodeValue3087 (mixedVector B) := by
    change mixedMoment B node3087 node3087Labels = _
    exact sound3087_e B hB hF
  have h3100 : mixedVector B (Sum.inr 3100) = Sparse.eval nodeValue3100 (mixedVector B) := by
    change mixedMoment B node3100 node3100Labels = _
    exact sound3100_e B hB hF
  have h3199 : mixedVector B (Sum.inr 3199) = Sparse.eval nodeValue3199 (mixedVector B) := by
    change mixedMoment B node3199 node3199Labels = _
    exact sound3199 B hB hF
  have h3203 : mixedVector B (Sum.inr 3203) = Sparse.eval nodeValue3203 (mixedVector B) := by
    change mixedMoment B node3203 node3203Labels = _
    exact sound3203_e B hB hF
  have h3223 : mixedVector B (Sum.inr 3223) = Sparse.eval nodeValue3223 (mixedVector B) := by
    change mixedMoment B node3223 node3223Labels = _
    exact sound3223_e B hB hF
  simpa only [sourceForm717, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2010, h2011, h2024, h2234, h2669, h2671, h2676, h2721, h3034, h3036, h3037, h3041, h3043, h3051, h3053, h3085, h3087, h3100, h3199, h3203, h3223, reducedSource622] using sourceEq717 B hB

theorem rowSound622 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row622 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck622, numericCheck622, reducedZero622 B hB hF, mul_zero]

theorem reducedZero623 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource623 (mixedVector B) = 0 := by
  have h3376 : mixedVector B (Sum.inr 3376) = Sparse.eval nodeValue3376 (mixedVector B) := by
    change mixedMoment B node3376 node3376Labels = _
    exact sound3376 B hB hF
  have h3378 : mixedVector B (Sum.inr 3378) = Sparse.eval nodeValue3378 (mixedVector B) := by
    change mixedMoment B node3378 node3378Labels = _
    exact sound3378 B hB hF
  have h3390 : mixedVector B (Sum.inr 3390) = Sparse.eval nodeValue3390 (mixedVector B) := by
    change mixedMoment B node3390 node3390Labels = _
    exact sound3390 B hB hF
  have h3526 : mixedVector B (Sum.inr 3526) = Sparse.eval nodeValue3526 (mixedVector B) := by
    change mixedMoment B node3526 node3526Labels = _
    exact sound3526 B hB hF
  have h3532 : mixedVector B (Sum.inr 3532) = Sparse.eval nodeValue3532 (mixedVector B) := by
    change mixedMoment B node3532 node3532Labels = _
    exact sound3532 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm718, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3376, h3378, h3390, h3526, h3532, h4083, reducedSource623] using sourceEq718 B hB

theorem rowSound623 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row623 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck623, numericCheck623, reducedZero623 B hB hF, mul_zero]

theorem sourceRowsAt608 : MixedData.sourceRows (608 : Fin 2425) =
    MixedData.row608 := by decide +kernel

theorem sourceRowsAt609 : MixedData.sourceRows (609 : Fin 2425) =
    MixedData.row609 := by decide +kernel

theorem sourceRowsAt610 : MixedData.sourceRows (610 : Fin 2425) =
    MixedData.row610 := by decide +kernel

theorem sourceRowsAt611 : MixedData.sourceRows (611 : Fin 2425) =
    MixedData.row611 := by decide +kernel

theorem sourceRowsAt612 : MixedData.sourceRows (612 : Fin 2425) =
    MixedData.row612 := by decide +kernel

theorem sourceRowsAt613 : MixedData.sourceRows (613 : Fin 2425) =
    MixedData.row613 := by decide +kernel

theorem sourceRowsAt614 : MixedData.sourceRows (614 : Fin 2425) =
    MixedData.row614 := by decide +kernel

theorem sourceRowsAt615 : MixedData.sourceRows (615 : Fin 2425) =
    MixedData.row615 := by decide +kernel

theorem sourceRowsAt616 : MixedData.sourceRows (616 : Fin 2425) =
    MixedData.row616 := by decide +kernel

theorem sourceRowsAt617 : MixedData.sourceRows (617 : Fin 2425) =
    MixedData.row617 := by decide +kernel

theorem sourceRowsAt618 : MixedData.sourceRows (618 : Fin 2425) =
    MixedData.row618 := by decide +kernel

theorem sourceRowsAt619 : MixedData.sourceRows (619 : Fin 2425) =
    MixedData.row619 := by decide +kernel

theorem sourceRowsAt620 : MixedData.sourceRows (620 : Fin 2425) =
    MixedData.row620 := by decide +kernel

theorem sourceRowsAt621 : MixedData.sourceRows (621 : Fin 2425) =
    MixedData.row621 := by decide +kernel

theorem sourceRowsAt622 : MixedData.sourceRows (622 : Fin 2425) =
    MixedData.row622 := by decide +kernel

theorem sourceRowsAt623 : MixedData.sourceRows (623 : Fin 2425) =
    MixedData.row623 := by decide +kernel

theorem chunkSound38_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 38) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 608 ∨ k.val = 609 ∨ k.val = 610 ∨ k.val = 611 ∨ k.val = 612 ∨ k.val = 613 ∨ k.val = 614 ∨ k.val = 615 ∨ k.val = 616 ∨ k.val = 617 ∨ k.val = 618 ∨ k.val = 619 ∨ k.val = 620 ∨ k.val = 621 ∨ k.val = 622 ∨ k.val = 623 := by omega
  rcases heq with h608 | h609 | h610 | h611 | h612 | h613 | h614 | h615 | h616 | h617 | h618 | h619 | h620 | h621 | h622 | h623
  · have he : k = (608 : Fin 2425) := Fin.ext h608
    subst k
    rw [sourceRowsAt608]
    exact rowSound608_e B hB hF
  · have he : k = (609 : Fin 2425) := Fin.ext h609
    subst k
    rw [sourceRowsAt609]
    exact rowSound609 B hB hF
  · have he : k = (610 : Fin 2425) := Fin.ext h610
    subst k
    rw [sourceRowsAt610]
    exact rowSound610 B hB hF
  · have he : k = (611 : Fin 2425) := Fin.ext h611
    subst k
    rw [sourceRowsAt611]
    exact rowSound611 B hB hF
  · have he : k = (612 : Fin 2425) := Fin.ext h612
    subst k
    rw [sourceRowsAt612]
    exact rowSound612_e B hB hF
  · have he : k = (613 : Fin 2425) := Fin.ext h613
    subst k
    rw [sourceRowsAt613]
    exact rowSound613_e B hB hF
  · have he : k = (614 : Fin 2425) := Fin.ext h614
    subst k
    rw [sourceRowsAt614]
    exact rowSound614_e B hB hF
  · have he : k = (615 : Fin 2425) := Fin.ext h615
    subst k
    rw [sourceRowsAt615]
    exact rowSound615 B hB hF
  · have he : k = (616 : Fin 2425) := Fin.ext h616
    subst k
    rw [sourceRowsAt616]
    exact rowSound616 B hB hF
  · have he : k = (617 : Fin 2425) := Fin.ext h617
    subst k
    rw [sourceRowsAt617]
    exact rowSound617 B hB hF
  · have he : k = (618 : Fin 2425) := Fin.ext h618
    subst k
    rw [sourceRowsAt618]
    exact rowSound618 B hB hF
  · have he : k = (619 : Fin 2425) := Fin.ext h619
    subst k
    rw [sourceRowsAt619]
    exact rowSound619 B hB hF
  · have he : k = (620 : Fin 2425) := Fin.ext h620
    subst k
    rw [sourceRowsAt620]
    exact rowSound620 B hB hF
  · have he : k = (621 : Fin 2425) := Fin.ext h621
    subst k
    rw [sourceRowsAt621]
    exact rowSound621 B hB hF
  · have he : k = (622 : Fin 2425) := Fin.ext h622
    subst k
    rw [sourceRowsAt622]
    exact rowSound622 B hB hF
  · have he : k = (623 : Fin 2425) := Fin.ext h623
    subst k
    rw [sourceRowsAt623]
    exact rowSound623 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound38_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound38_e_oai
