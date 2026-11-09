-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound68_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:30:49.91499+00:00
-- url     : https://prove2.me/submissions/c745ae88-243e-4edd-9061-97acdddca40d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1093_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1094_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1095_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1096_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1097_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1098_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1103_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1280 raw1280Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw1280 raw1280Labels = mixedMoment B raw1280step0 raw1280step0Labels := by
      have ha : raw1280step0 = (fun i j => raw1280 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1280step0 raw1280; decide +kernel
      have hl : raw1280step0Labels = raw1280Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1280 raw1280Labels permutation2 permutation6
    mixedMoment B raw1280step0 raw1280step0Labels = mixedMoment B raw1280step1 raw1280step1Labels := by
      have ha : raw1280step1 = -raw1280step0 := by apply Matrix.ext; change ∀ i j, raw1280step1 i j = -(raw1280step0 i j); unfold raw1280step1 raw1280step0; decide +kernel
      have hl : raw1280step1Labels = raw1280step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1280step1 raw1280step1Labels = mixedMoment B raw1280step2 raw1280step2Labels := by
      have ha : raw1280step2 = raw1280step1 := by apply Matrix.ext; unfold raw1280step2 raw1280step1; decide +kernel
      have hl : raw1280step1Labels = labelEmbedding1 ∘ raw1280step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1280step1 raw1280step1Labels raw1280step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1752 node1752Labels := by rfl

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

theorem canonical1428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1428 raw1428Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw1428 raw1428Labels = mixedMoment B raw1428step0 raw1428step0Labels := by
      have ha : raw1428step0 = (fun i j => raw1428 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1428step0 raw1428; decide +kernel
      have hl : raw1428step0Labels = raw1428Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1428 raw1428Labels permutation8 permutation4
    mixedMoment B raw1428step0 raw1428step0Labels = mixedMoment B raw1428step1 raw1428step1Labels := by
      have ha : raw1428step1 = raw1428step0 := by apply Matrix.ext; unfold raw1428step1 raw1428step0; decide +kernel
      have hl : raw1428step0Labels = labelEmbedding7 ∘ raw1428step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1428step0 raw1428step0Labels raw1428step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4605 node4605Labels := by rfl

theorem canonical1429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1429 raw1429Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw1429 raw1429Labels = mixedMoment B raw1429step0 raw1429step0Labels := by
      have ha : raw1429step0 = (fun i j => raw1429 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1429step0 raw1429; decide +kernel
      have hl : raw1429step0Labels = raw1429Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1429 raw1429Labels permutation8 permutation4
    _ = mixedMoment B node1239 node1239Labels := by rfl

theorem canonical1430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1430 raw1430Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw1430 raw1430Labels = mixedMoment B raw1430step0 raw1430step0Labels := by
      have ha : raw1430step0 = (fun i j => raw1430 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1430step0 raw1430; decide +kernel
      have hl : raw1430step0Labels = raw1430Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1430 raw1430Labels permutation31 permutation6
    mixedMoment B raw1430step0 raw1430step0Labels = mixedMoment B raw1430step1 raw1430step1Labels := by
      have ha : raw1430step1 = raw1430step0 := by apply Matrix.ext; unfold raw1430step1 raw1430step0; decide +kernel
      have hl : raw1430step0Labels = labelEmbedding1 ∘ raw1430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1430step0 raw1430step0Labels raw1430step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

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

theorem canonical1797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1797 raw1797Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw1797 raw1797Labels = mixedMoment B raw1797step0 raw1797step0Labels := by
      have ha : raw1797step0 = (fun i j => raw1797 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1797step0 raw1797; decide +kernel
      have hl : raw1797step0Labels = raw1797Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1797 raw1797Labels permutation8 permutation4
    mixedMoment B raw1797step0 raw1797step0Labels = mixedMoment B raw1797step1 raw1797step1Labels := by
      have ha : raw1797step1 = raw1797step0 := by apply Matrix.ext; unfold raw1797step1 raw1797step0; decide +kernel
      have hl : raw1797step0Labels = labelEmbedding7 ∘ raw1797step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1797step0 raw1797step0Labels raw1797step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4868 node4868Labels := by rfl

theorem canonical1798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1798 raw1798Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw1798 raw1798Labels = mixedMoment B raw1798step0 raw1798step0Labels := by
      have ha : raw1798step0 = (fun i j => raw1798 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1798step0 raw1798; decide +kernel
      have hl : raw1798step0Labels = raw1798Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1798 raw1798Labels permutation8 permutation4
    _ = mixedMoment B node2109 node2109Labels := by rfl

theorem canonical1799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1799 raw1799Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw1799 raw1799Labels = mixedMoment B raw1799step0 raw1799step0Labels := by
      have ha : raw1799step0 = (fun i j => raw1799 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1799step0 raw1799; decide +kernel
      have hl : raw1799step0Labels = raw1799Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1799 raw1799Labels permutation10 permutation6
    mixedMoment B raw1799step0 raw1799step0Labels = mixedMoment B raw1799step1 raw1799step1Labels := by
      have ha : raw1799step1 = -raw1799step0 := by apply Matrix.ext; change ∀ i j, raw1799step1 i j = -(raw1799step0 i j); unfold raw1799step1 raw1799step0; decide +kernel
      have hl : raw1799step1Labels = raw1799step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1799step1 raw1799step1Labels = mixedMoment B raw1799step2 raw1799step2Labels := by
      have ha : raw1799step2 = raw1799step1 := by apply Matrix.ext; unfold raw1799step2 raw1799step1; decide +kernel
      have hl : raw1799step1Labels = labelEmbedding1 ∘ raw1799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1799step1 raw1799step1Labels raw1799step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical153
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19631 raw19631Labels = mixedMoment B node4189 node4189Labels := by
  calc
    mixedMoment B raw19631 raw19631Labels = mixedMoment B raw19631step0 raw19631step0Labels := by
      have hz : ∀ j, raw19631 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19631step0 = (fun i j => raw19631 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19631step0 raw19631; decide +kernel
      have hl : raw19631step0Labels = raw19631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19631 raw19631Labels permutation434 hz
    mixedMoment B raw19631step0 raw19631step0Labels = mixedMoment B raw19631step1 raw19631step1Labels := by
      have hz : ∀ j, raw19631step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19631step1 = (fun i j => raw19631step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19631step1 raw19631step0; decide +kernel
      have hl : raw19631step1Labels = raw19631step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19631step0 raw19631step0Labels permutation80 hz
    mixedMoment B raw19631step1 raw19631step1Labels = mixedMoment B raw19631step2 raw19631step2Labels := by
      have hz : ∀ j, raw19631step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19631step2 = (fun i j => raw19631step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19631step2 raw19631step1; decide +kernel
      have hl : raw19631step2Labels = raw19631step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19631step1 raw19631step1Labels permutation14 hz
    mixedMoment B raw19631step2 raw19631step2Labels = mixedMoment B raw19631step3 raw19631step3Labels := by
      have ha : raw19631step3 = (fun i j => raw19631step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19631step3 raw19631step2; decide +kernel
      have hl : raw19631step3Labels = raw19631step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19631step2 raw19631step2Labels permutation2 permutation3
    mixedMoment B raw19631step3 raw19631step3Labels = mixedMoment B raw19631step4 raw19631step4Labels := by
      have ha : raw19631step4 = raw19631step3 := by apply Matrix.ext; unfold raw19631step4 raw19631step3; decide +kernel
      have hl : raw19631step3Labels = labelEmbedding6 ∘ raw19631step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19631step3 raw19631step3Labels raw19631step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4189 node4189Labels := by rfl

theorem canonical19632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19632 raw19632Labels = mixedMoment B node4370 node4370Labels := by
  calc
    mixedMoment B raw19632 raw19632Labels = mixedMoment B raw19632step0 raw19632step0Labels := by
      have hz : ∀ j, raw19632 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19632step0 = (fun i j => raw19632 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19632step0 raw19632; decide +kernel
      have hl : raw19632step0Labels = raw19632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19632 raw19632Labels permutation434 hz
    mixedMoment B raw19632step0 raw19632step0Labels = mixedMoment B raw19632step1 raw19632step1Labels := by
      have hz : ∀ j, raw19632step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19632step1 = (fun i j => raw19632step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19632step1 raw19632step0; decide +kernel
      have hl : raw19632step1Labels = raw19632step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19632step0 raw19632step0Labels permutation80 hz
    mixedMoment B raw19632step1 raw19632step1Labels = mixedMoment B raw19632step2 raw19632step2Labels := by
      have ha : raw19632step2 = (fun i j => raw19632step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19632step2 raw19632step1; decide +kernel
      have hl : raw19632step2Labels = raw19632step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19632step1 raw19632step1Labels permutation31 permutation2
    mixedMoment B raw19632step2 raw19632step2Labels = mixedMoment B raw19632step3 raw19632step3Labels := by
      have ha : raw19632step3 = -raw19632step2 := by apply Matrix.ext; change ∀ i j, raw19632step3 i j = -(raw19632step2 i j); unfold raw19632step3 raw19632step2; decide +kernel
      have hl : raw19632step3Labels = raw19632step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4370 node4370Labels := by rfl

theorem canonical19633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19633 raw19633Labels = mixedMoment B node4370 node4370Labels := by
  calc
    mixedMoment B raw19633 raw19633Labels = mixedMoment B raw19633step0 raw19633step0Labels := by
      have hz : ∀ j, raw19633 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19633step0 = (fun i j => raw19633 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19633step0 raw19633; decide +kernel
      have hl : raw19633step0Labels = raw19633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19633 raw19633Labels permutation434 hz
    mixedMoment B raw19633step0 raw19633step0Labels = mixedMoment B raw19633step1 raw19633step1Labels := by
      have hz : ∀ j, raw19633step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19633step1 = (fun i j => raw19633step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19633step1 raw19633step0; decide +kernel
      have hl : raw19633step1Labels = raw19633step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19633step0 raw19633step0Labels permutation56 hz
    mixedMoment B raw19633step1 raw19633step1Labels = mixedMoment B raw19633step2 raw19633step2Labels := by
      have ha : raw19633step2 = (fun i j => raw19633step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19633step2 raw19633step1; decide +kernel
      have hl : raw19633step2Labels = raw19633step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19633step1 raw19633step1Labels permutation31 permutation2
    mixedMoment B raw19633step2 raw19633step2Labels = mixedMoment B raw19633step3 raw19633step3Labels := by
      have ha : raw19633step3 = -raw19633step2 := by apply Matrix.ext; change ∀ i j, raw19633step3 i j = -(raw19633step2 i j); unfold raw19633step3 raw19633step2; decide +kernel
      have hl : raw19633step3Labels = raw19633step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4370 node4370Labels := by rfl

theorem canonical19634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19634 raw19634Labels = mixedMoment B node4370 node4370Labels := by
  calc
    mixedMoment B raw19634 raw19634Labels = mixedMoment B raw19634step0 raw19634step0Labels := by
      have hz : ∀ j, raw19634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19634step0 = (fun i j => raw19634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19634step0 raw19634; decide +kernel
      have hl : raw19634step0Labels = raw19634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19634 raw19634Labels permutation346 hz
    mixedMoment B raw19634step0 raw19634step0Labels = mixedMoment B raw19634step1 raw19634step1Labels := by
      have hz : ∀ j, raw19634step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19634step1 = (fun i j => raw19634step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19634step1 raw19634step0; decide +kernel
      have hl : raw19634step1Labels = raw19634step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19634step0 raw19634step0Labels permutation56 hz
    mixedMoment B raw19634step1 raw19634step1Labels = mixedMoment B raw19634step2 raw19634step2Labels := by
      have ha : raw19634step2 = (fun i j => raw19634step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19634step2 raw19634step1; decide +kernel
      have hl : raw19634step2Labels = raw19634step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19634step1 raw19634step1Labels permutation31 permutation2
    mixedMoment B raw19634step2 raw19634step2Labels = mixedMoment B raw19634step3 raw19634step3Labels := by
      have ha : raw19634step3 = -raw19634step2 := by apply Matrix.ext; change ∀ i j, raw19634step3 i j = -(raw19634step2 i j); unfold raw19634step3 raw19634step2; decide +kernel
      have hl : raw19634step3Labels = raw19634step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4370 node4370Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical157
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20099 raw20099Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw20099 raw20099Labels = mixedMoment B raw20099step0 raw20099step0Labels := by
      have hz : ∀ j, raw20099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20099step0 = (fun i j => raw20099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20099step0 raw20099; decide +kernel
      have hl : raw20099step0Labels = raw20099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099 raw20099Labels permutation434 hz
    mixedMoment B raw20099step0 raw20099step0Labels = mixedMoment B raw20099step1 raw20099step1Labels := by
      have hz : ∀ j, raw20099step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20099step1 = (fun i j => raw20099step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20099step1 raw20099step0; decide +kernel
      have hl : raw20099step1Labels = raw20099step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099step0 raw20099step0Labels permutation80 hz
    mixedMoment B raw20099step1 raw20099step1Labels = mixedMoment B raw20099step2 raw20099step2Labels := by
      have hz : ∀ j, raw20099step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20099step2 = (fun i j => raw20099step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20099step2 raw20099step1; decide +kernel
      have hl : raw20099step2Labels = raw20099step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099step1 raw20099step1Labels permutation14 hz
    mixedMoment B raw20099step2 raw20099step2Labels = mixedMoment B raw20099step3 raw20099step3Labels := by
      have ha : raw20099step3 = -raw20099step2 := by apply Matrix.ext; change ∀ i j, raw20099step3 i j = -(raw20099step2 i j); unfold raw20099step3 raw20099step2; decide +kernel
      have hl : raw20099step3Labels = raw20099step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical20161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20161 raw20161Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw20161 raw20161Labels = mixedMoment B raw20161step0 raw20161step0Labels := by
      have hz : ∀ j, raw20161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20161step0 = (fun i j => raw20161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20161step0 raw20161; decide +kernel
      have hl : raw20161step0Labels = raw20161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20161 raw20161Labels permutation346 hz
    mixedMoment B raw20161step0 raw20161step0Labels = mixedMoment B raw20161step1 raw20161step1Labels := by
      have hz : ∀ j, raw20161step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20161step1 = (fun i j => raw20161step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20161step1 raw20161step0; decide +kernel
      have hl : raw20161step1Labels = raw20161step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20161step0 raw20161step0Labels permutation56 hz
    mixedMoment B raw20161step1 raw20161step1Labels = mixedMoment B raw20161step2 raw20161step2Labels := by
      have ha : raw20161step2 = (fun i j => raw20161step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20161step2 raw20161step1; decide +kernel
      have hl : raw20161step2Labels = raw20161step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20161step1 raw20161step1Labels permutation10 permutation4
    mixedMoment B raw20161step2 raw20161step2Labels = mixedMoment B raw20161step3 raw20161step3Labels := by
      have ha : raw20161step3 = -raw20161step2 := by apply Matrix.ext; change ∀ i j, raw20161step3 i j = -(raw20161step2 i j); unfold raw20161step3 raw20161step2; decide +kernel
      have hl : raw20161step3Labels = raw20161step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical20213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20213 raw20213Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw20213 raw20213Labels = mixedMoment B raw20213step0 raw20213step0Labels := by
      have hz : ∀ j, raw20213 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20213step0 = (fun i j => raw20213 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20213step0 raw20213; decide +kernel
      have hl : raw20213step0Labels = raw20213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20213 raw20213Labels permutation434 hz
    mixedMoment B raw20213step0 raw20213step0Labels = mixedMoment B raw20213step1 raw20213step1Labels := by
      have hz : ∀ j, raw20213step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20213step1 = (fun i j => raw20213step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20213step1 raw20213step0; decide +kernel
      have hl : raw20213step1Labels = raw20213step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20213step0 raw20213step0Labels permutation56 hz
    mixedMoment B raw20213step1 raw20213step1Labels = mixedMoment B raw20213step2 raw20213step2Labels := by
      have ha : raw20213step2 = (fun i j => raw20213step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20213step2 raw20213step1; decide +kernel
      have hl : raw20213step2Labels = raw20213step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20213step1 raw20213step1Labels permutation10 permutation4
    mixedMoment B raw20213step2 raw20213step2Labels = mixedMoment B raw20213step3 raw20213step3Labels := by
      have ha : raw20213step3 = -raw20213step2 := by apply Matrix.ext; change ∀ i j, raw20213step3 i j = -(raw20213step2 i j); unfold raw20213step3 raw20213step2; decide +kernel
      have hl : raw20213step3Labels = raw20213step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1725 node1725Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical158
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20265 raw20265Labels = mixedMoment B node3310 node3310Labels := by
  calc
    mixedMoment B raw20265 raw20265Labels = mixedMoment B raw20265step0 raw20265step0Labels := by
      have hz : ∀ j, raw20265 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20265step0 = (fun i j => raw20265 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20265step0 raw20265; decide +kernel
      have hl : raw20265step0Labels = raw20265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20265 raw20265Labels permutation434 hz
    mixedMoment B raw20265step0 raw20265step0Labels = mixedMoment B raw20265step1 raw20265step1Labels := by
      have hz : ∀ j, raw20265step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20265step1 = (fun i j => raw20265step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20265step1 raw20265step0; decide +kernel
      have hl : raw20265step1Labels = raw20265step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20265step0 raw20265step0Labels permutation80 hz
    mixedMoment B raw20265step1 raw20265step1Labels = mixedMoment B raw20265step2 raw20265step2Labels := by
      have hz : ∀ j, raw20265step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20265step2 = (fun i j => raw20265step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20265step2 raw20265step1; decide +kernel
      have hl : raw20265step2Labels = raw20265step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20265step1 raw20265step1Labels permutation14 hz
    mixedMoment B raw20265step2 raw20265step2Labels = mixedMoment B raw20265step3 raw20265step3Labels := by
      have ha : raw20265step3 = -raw20265step2 := by apply Matrix.ext; change ∀ i j, raw20265step3 i j = -(raw20265step2 i j); unfold raw20265step3 raw20265step2; decide +kernel
      have hl : raw20265step3Labels = raw20265step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3310 node3310Labels := by rfl

theorem canonical20268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20268 raw20268Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw20268 raw20268Labels = mixedMoment B raw20268step0 raw20268step0Labels := by
      have hz : ∀ j, raw20268 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20268step0 = (fun i j => raw20268 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20268step0 raw20268; decide +kernel
      have hl : raw20268step0Labels = raw20268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20268 raw20268Labels permutation434 hz
    mixedMoment B raw20268step0 raw20268step0Labels = mixedMoment B raw20268step1 raw20268step1Labels := by
      have hz : ∀ j, raw20268step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20268step1 = (fun i j => raw20268step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20268step1 raw20268step0; decide +kernel
      have hl : raw20268step1Labels = raw20268step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20268step0 raw20268step0Labels permutation80 hz
    mixedMoment B raw20268step1 raw20268step1Labels = mixedMoment B raw20268step2 raw20268step2Labels := by
      have ha : raw20268step2 = (fun i j => raw20268step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20268step2 raw20268step1; decide +kernel
      have hl : raw20268step2Labels = raw20268step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20268step1 raw20268step1Labels permutation8 permutation4
    mixedMoment B raw20268step2 raw20268step2Labels = mixedMoment B raw20268step3 raw20268step3Labels := by
      have ha : raw20268step3 = -raw20268step2 := by apply Matrix.ext; change ∀ i j, raw20268step3 i j = -(raw20268step2 i j); unfold raw20268step3 raw20268step2; decide +kernel
      have hl : raw20268step3Labels = raw20268step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3300 node3300Labels := by rfl

theorem canonical20298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20298 raw20298Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw20298 raw20298Labels = mixedMoment B raw20298step0 raw20298step0Labels := by
      have hz : ∀ j, raw20298 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20298step0 = (fun i j => raw20298 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20298step0 raw20298; decide +kernel
      have hl : raw20298step0Labels = raw20298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20298 raw20298Labels permutation434 hz
    mixedMoment B raw20298step0 raw20298step0Labels = mixedMoment B raw20298step1 raw20298step1Labels := by
      have hz : ∀ j, raw20298step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20298step1 = (fun i j => raw20298step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20298step1 raw20298step0; decide +kernel
      have hl : raw20298step1Labels = raw20298step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20298step0 raw20298step0Labels permutation80 hz
    mixedMoment B raw20298step1 raw20298step1Labels = mixedMoment B raw20298step2 raw20298step2Labels := by
      have ha : raw20298step2 = -raw20298step1 := by apply Matrix.ext; change ∀ i j, raw20298step2 i j = -(raw20298step1 i j); unfold raw20298step2 raw20298step1; decide +kernel
      have hl : raw20298step2Labels = raw20298step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1750 node1750Labels := by rfl

theorem canonical20303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20303 raw20303Labels = mixedMoment B node3310 node3310Labels := by
  calc
    mixedMoment B raw20303 raw20303Labels = mixedMoment B raw20303step0 raw20303step0Labels := by
      have hz : ∀ j, raw20303 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20303step0 = (fun i j => raw20303 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20303step0 raw20303; decide +kernel
      have hl : raw20303step0Labels = raw20303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20303 raw20303Labels permutation434 hz
    mixedMoment B raw20303step0 raw20303step0Labels = mixedMoment B raw20303step1 raw20303step1Labels := by
      have hz : ∀ j, raw20303step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20303step1 = (fun i j => raw20303step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20303step1 raw20303step0; decide +kernel
      have hl : raw20303step1Labels = raw20303step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20303step0 raw20303step0Labels permutation80 hz
    mixedMoment B raw20303step1 raw20303step1Labels = mixedMoment B raw20303step2 raw20303step2Labels := by
      have hz : ∀ j, raw20303step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20303step2 = (fun i j => raw20303step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20303step2 raw20303step1; decide +kernel
      have hl : raw20303step2Labels = raw20303step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20303step1 raw20303step1Labels permutation14 hz
    mixedMoment B raw20303step2 raw20303step2Labels = mixedMoment B raw20303step3 raw20303step3Labels := by
      have ha : raw20303step3 = (fun i j => raw20303step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20303step3 raw20303step2; decide +kernel
      have hl : raw20303step3Labels = raw20303step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20303step2 raw20303step2Labels permutation2 permutation4
    mixedMoment B raw20303step3 raw20303step3Labels = mixedMoment B raw20303step4 raw20303step4Labels := by
      have ha : raw20303step4 = -raw20303step3 := by apply Matrix.ext; change ∀ i j, raw20303step4 i j = -(raw20303step3 i j); unfold raw20303step4 raw20303step3; decide +kernel
      have hl : raw20303step4Labels = raw20303step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3310 node3310Labels := by rfl

theorem canonical20315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20315 raw20315Labels = mixedMoment B node1181 node1181Labels := by
  calc
    mixedMoment B raw20315 raw20315Labels = mixedMoment B raw20315step0 raw20315step0Labels := by
      have hz : ∀ j, raw20315 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20315step0 = (fun i j => raw20315 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20315step0 raw20315; decide +kernel
      have hl : raw20315step0Labels = raw20315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20315 raw20315Labels permutation346 hz
    mixedMoment B raw20315step0 raw20315step0Labels = mixedMoment B raw20315step1 raw20315step1Labels := by
      have ha : raw20315step1 = (fun i j => raw20315step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20315step1 raw20315step0; decide +kernel
      have hl : raw20315step1Labels = raw20315step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20315step0 raw20315step0Labels permutation38 permutation2
    _ = mixedMoment B node1181 node1181Labels := by rfl

theorem canonical20320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20320 raw20320Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw20320 raw20320Labels = mixedMoment B raw20320step0 raw20320step0Labels := by
      have hz : ∀ j, raw20320 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20320step0 = (fun i j => raw20320 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20320step0 raw20320; decide +kernel
      have hl : raw20320step0Labels = raw20320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20320 raw20320Labels permutation346 hz
    mixedMoment B raw20320step0 raw20320step0Labels = mixedMoment B raw20320step1 raw20320step1Labels := by
      have ha : raw20320step1 = (fun i j => raw20320step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20320step1 raw20320step0; decide +kernel
      have hl : raw20320step1Labels = raw20320step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20320step0 raw20320step0Labels permutation38 permutation2
    _ = mixedMoment B node2672 node2672Labels := by rfl

theorem canonical20321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20321 raw20321Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw20321 raw20321Labels = mixedMoment B raw20321step0 raw20321step0Labels := by
      have hz : ∀ j, raw20321 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20321step0 = (fun i j => raw20321 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20321step0 raw20321; decide +kernel
      have hl : raw20321step0Labels = raw20321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20321 raw20321Labels permutation346 hz
    mixedMoment B raw20321step0 raw20321step0Labels = mixedMoment B raw20321step1 raw20321step1Labels := by
      have ha : raw20321step1 = (fun i j => raw20321step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20321step1 raw20321step0; decide +kernel
      have hl : raw20321step1Labels = raw20321step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20321step0 raw20321step0Labels permutation38 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical20322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20322 raw20322Labels = mixedMoment B node1188 node1188Labels := by
  calc
    mixedMoment B raw20322 raw20322Labels = mixedMoment B raw20322step0 raw20322step0Labels := by
      have hz : ∀ j, raw20322 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20322step0 = (fun i j => raw20322 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20322step0 raw20322; decide +kernel
      have hl : raw20322step0Labels = raw20322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20322 raw20322Labels permutation346 hz
    mixedMoment B raw20322step0 raw20322step0Labels = mixedMoment B raw20322step1 raw20322step1Labels := by
      have ha : raw20322step1 = (fun i j => raw20322step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20322step1 raw20322step0; decide +kernel
      have hl : raw20322step1Labels = raw20322step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20322step0 raw20322step0Labels permutation38 permutation2
    _ = mixedMoment B node1188 node1188Labels := by rfl

theorem canonical20323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20323 raw20323Labels = mixedMoment B node1178 node1178Labels := by
  calc
    mixedMoment B raw20323 raw20323Labels = mixedMoment B raw20323step0 raw20323step0Labels := by
      have ha : raw20323step0 = (fun i j => raw20323 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20323step0 raw20323; decide +kernel
      have hl : raw20323step0Labels = raw20323Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20323 raw20323Labels permutation200 permutation2
    _ = mixedMoment B node1178 node1178Labels := by rfl

theorem canonical20324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20324 raw20324Labels = mixedMoment B node1257 node1257Labels := by
  calc
    mixedMoment B raw20324 raw20324Labels = mixedMoment B raw20324step0 raw20324step0Labels := by
      have hz : ∀ j, raw20324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20324step0 = (fun i j => raw20324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20324step0 raw20324; decide +kernel
      have hl : raw20324step0Labels = raw20324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20324 raw20324Labels permutation346 hz
    _ = mixedMoment B node1257 node1257Labels := by rfl

theorem canonical20325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20325 raw20325Labels = mixedMoment B node1182 node1182Labels := by
  calc
    mixedMoment B raw20325 raw20325Labels = mixedMoment B raw20325step0 raw20325step0Labels := by
      have hz : ∀ j, raw20325 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20325step0 = (fun i j => raw20325 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20325step0 raw20325; decide +kernel
      have hl : raw20325step0Labels = raw20325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20325 raw20325Labels permutation346 hz
    mixedMoment B raw20325step0 raw20325step0Labels = mixedMoment B raw20325step1 raw20325step1Labels := by
      have ha : raw20325step1 = (fun i j => raw20325step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20325step1 raw20325step0; decide +kernel
      have hl : raw20325step1Labels = raw20325step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20325step0 raw20325step0Labels permutation38 permutation2
    _ = mixedMoment B node1182 node1182Labels := by rfl

theorem canonical20326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20326 raw20326Labels = mixedMoment B node1179 node1179Labels := by
  calc
    mixedMoment B raw20326 raw20326Labels = mixedMoment B raw20326step0 raw20326step0Labels := by
      have hz : ∀ j, raw20326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20326step0 = (fun i j => raw20326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20326step0 raw20326; decide +kernel
      have hl : raw20326step0Labels = raw20326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20326 raw20326Labels permutation346 hz
    mixedMoment B raw20326step0 raw20326step0Labels = mixedMoment B raw20326step1 raw20326step1Labels := by
      have ha : raw20326step1 = (fun i j => raw20326step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20326step1 raw20326step0; decide +kernel
      have hl : raw20326step1Labels = raw20326step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20326step0 raw20326step0Labels permutation38 permutation2
    _ = mixedMoment B node1179 node1179Labels := by rfl

theorem canonical20327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20327 raw20327Labels = mixedMoment B node2032 node2032Labels := by
  calc
    mixedMoment B raw20327 raw20327Labels = mixedMoment B raw20327step0 raw20327step0Labels := by
      have hz : ∀ j, raw20327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20327step0 = (fun i j => raw20327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20327step0 raw20327; decide +kernel
      have hl : raw20327step0Labels = raw20327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20327 raw20327Labels permutation346 hz
    mixedMoment B raw20327step0 raw20327step0Labels = mixedMoment B raw20327step1 raw20327step1Labels := by
      have ha : raw20327step1 = (fun i j => raw20327step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20327step1 raw20327step0; decide +kernel
      have hl : raw20327step1Labels = raw20327step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20327step0 raw20327step0Labels permutation151 permutation2
    mixedMoment B raw20327step1 raw20327step1Labels = mixedMoment B raw20327step2 raw20327step2Labels := by
      have ha : raw20327step2 = -raw20327step1 := by apply Matrix.ext; change ∀ i j, raw20327step2 i j = -(raw20327step1 i j); unfold raw20327step2 raw20327step1; decide +kernel
      have hl : raw20327step2Labels = raw20327step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2032 node2032Labels := by rfl

theorem canonical20328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20328 raw20328Labels = mixedMoment B node1991 node1991Labels := by
  calc
    mixedMoment B raw20328 raw20328Labels = mixedMoment B raw20328step0 raw20328step0Labels := by
      have ha : raw20328step0 = (fun i j => raw20328 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20328step0 raw20328; decide +kernel
      have hl : raw20328step0Labels = raw20328Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20328 raw20328Labels permutation676 permutation2
    mixedMoment B raw20328step0 raw20328step0Labels = mixedMoment B raw20328step1 raw20328step1Labels := by
      have ha : raw20328step1 = -raw20328step0 := by apply Matrix.ext; change ∀ i j, raw20328step1 i j = -(raw20328step0 i j); unfold raw20328step1 raw20328step0; decide +kernel
      have hl : raw20328step1Labels = raw20328step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1991 node1991Labels := by rfl

theorem canonical20329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20329 raw20329Labels = mixedMoment B node2003 node2003Labels := by
  calc
    mixedMoment B raw20329 raw20329Labels = mixedMoment B raw20329step0 raw20329step0Labels := by
      have hz : ∀ j, raw20329 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20329step0 = (fun i j => raw20329 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20329step0 raw20329; decide +kernel
      have hl : raw20329step0Labels = raw20329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20329 raw20329Labels permutation346 hz
    mixedMoment B raw20329step0 raw20329step0Labels = mixedMoment B raw20329step1 raw20329step1Labels := by
      have ha : raw20329step1 = (fun i j => raw20329step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20329step1 raw20329step0; decide +kernel
      have hl : raw20329step1Labels = raw20329step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20329step0 raw20329step0Labels permutation149 permutation2
    mixedMoment B raw20329step1 raw20329step1Labels = mixedMoment B raw20329step2 raw20329step2Labels := by
      have ha : raw20329step2 = -raw20329step1 := by apply Matrix.ext; change ∀ i j, raw20329step2 i j = -(raw20329step1 i j); unfold raw20329step2 raw20329step1; decide +kernel
      have hl : raw20329step2Labels = raw20329step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2003 node2003Labels := by rfl

theorem canonical20330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20330 raw20330Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw20330 raw20330Labels = mixedMoment B raw20330step0 raw20330step0Labels := by
      have hz : ∀ j, raw20330 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20330step0 = (fun i j => raw20330 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20330step0 raw20330; decide +kernel
      have hl : raw20330step0Labels = raw20330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20330 raw20330Labels permutation520 hz
    mixedMoment B raw20330step0 raw20330step0Labels = mixedMoment B raw20330step1 raw20330step1Labels := by
      have hz : ∀ j, raw20330step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20330step1 = (fun i j => raw20330step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20330step1 raw20330step0; decide +kernel
      have hl : raw20330step1Labels = raw20330step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20330step0 raw20330step0Labels permutation80 hz
    mixedMoment B raw20330step1 raw20330step1Labels = mixedMoment B raw20330step2 raw20330step2Labels := by
      have ha : raw20330step2 = (fun i j => raw20330step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20330step2 raw20330step1; decide +kernel
      have hl : raw20330step2Labels = raw20330step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20330step1 raw20330step1Labels permutation29 permutation2
    mixedMoment B raw20330step2 raw20330step2Labels = mixedMoment B raw20330step3 raw20330step3Labels := by
      have ha : raw20330step3 = -raw20330step2 := by apply Matrix.ext; change ∀ i j, raw20330step3 i j = -(raw20330step2 i j); unfold raw20330step3 raw20330step2; decide +kernel
      have hl : raw20330step3Labels = raw20330step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2218 node2218Labels := by rfl

theorem canonical20331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20331 raw20331Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw20331 raw20331Labels = mixedMoment B raw20331step0 raw20331step0Labels := by
      have hz : ∀ j, raw20331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20331step0 = (fun i j => raw20331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20331step0 raw20331; decide +kernel
      have hl : raw20331step0Labels = raw20331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20331 raw20331Labels permutation346 hz
    mixedMoment B raw20331step0 raw20331step0Labels = mixedMoment B raw20331step1 raw20331step1Labels := by
      have ha : raw20331step1 = (fun i j => raw20331step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20331step1 raw20331step0; decide +kernel
      have hl : raw20331step1Labels = raw20331step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20331step0 raw20331step0Labels permutation38 permutation2
    _ = mixedMoment B node2670 node2670Labels := by rfl

theorem canonical20332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20332 raw20332Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw20332 raw20332Labels = mixedMoment B raw20332step0 raw20332step0Labels := by
      have hz : ∀ j, raw20332 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20332step0 = (fun i j => raw20332 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20332step0 raw20332; decide +kernel
      have hl : raw20332step0Labels = raw20332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20332 raw20332Labels permutation520 hz
    mixedMoment B raw20332step0 raw20332step0Labels = mixedMoment B raw20332step1 raw20332step1Labels := by
      have hz : ∀ j, raw20332step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20332step1 = (fun i j => raw20332step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20332step1 raw20332step0; decide +kernel
      have hl : raw20332step1Labels = raw20332step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20332step0 raw20332step0Labels permutation80 hz
    mixedMoment B raw20332step1 raw20332step1Labels = mixedMoment B raw20332step2 raw20332step2Labels := by
      have ha : raw20332step2 = (fun i j => raw20332step1 (permutation28 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20332step2 raw20332step1; decide +kernel
      have hl : raw20332step2Labels = raw20332step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20332step1 raw20332step1Labels permutation28 permutation0
    mixedMoment B raw20332step2 raw20332step2Labels = mixedMoment B raw20332step3 raw20332step3Labels := by
      have ha : raw20332step3 = -raw20332step2 := by apply Matrix.ext; change ∀ i j, raw20332step3 i j = -(raw20332step2 i j); unfold raw20332step3 raw20332step2; decide +kernel
      have hl : raw20332step3Labels = raw20332step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical20333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20333 raw20333Labels = mixedMoment B node1195 node1195Labels := by
  calc
    mixedMoment B raw20333 raw20333Labels = mixedMoment B raw20333step0 raw20333step0Labels := by
      have ha : raw20333step0 = (fun i j => raw20333 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20333step0 raw20333; decide +kernel
      have hl : raw20333step0Labels = raw20333Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20333 raw20333Labels permutation182 permutation2
    _ = mixedMoment B node1195 node1195Labels := by rfl

theorem canonical20334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20334 raw20334Labels = mixedMoment B node2469 node2469Labels := by
  calc
    mixedMoment B raw20334 raw20334Labels = mixedMoment B raw20334step0 raw20334step0Labels := by
      have ha : raw20334step0 = (fun i j => raw20334 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20334step0 raw20334; decide +kernel
      have hl : raw20334step0Labels = raw20334Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20334 raw20334Labels permutation682 permutation2
    mixedMoment B raw20334step0 raw20334step0Labels = mixedMoment B raw20334step1 raw20334step1Labels := by
      have ha : raw20334step1 = -raw20334step0 := by apply Matrix.ext; change ∀ i j, raw20334step1 i j = -(raw20334step0 i j); unfold raw20334step1 raw20334step0; decide +kernel
      have hl : raw20334step1Labels = raw20334step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2469 node2469Labels := by rfl

theorem canonical20335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20335 raw20335Labels = mixedMoment B node2449 node2449Labels := by
  calc
    mixedMoment B raw20335 raw20335Labels = mixedMoment B raw20335step0 raw20335step0Labels := by
      have ha : raw20335step0 = (fun i j => raw20335 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20335step0 raw20335; decide +kernel
      have hl : raw20335step0Labels = raw20335Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20335 raw20335Labels permutation182 permutation2
    _ = mixedMoment B node2449 node2449Labels := by rfl

theorem canonical20336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20336 raw20336Labels = mixedMoment B node2449 node2449Labels := by
  calc
    mixedMoment B raw20336 raw20336Labels = mixedMoment B raw20336step0 raw20336step0Labels := by
      have ha : raw20336step0 = (fun i j => raw20336 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20336step0 raw20336; decide +kernel
      have hl : raw20336step0Labels = raw20336Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20336 raw20336Labels permutation206 permutation2
    _ = mixedMoment B node2449 node2449Labels := by rfl

theorem canonical20337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20337 raw20337Labels = mixedMoment B node2691 node2691Labels := by
  calc
    mixedMoment B raw20337 raw20337Labels = mixedMoment B raw20337step0 raw20337step0Labels := by
      have ha : raw20337step0 = (fun i j => raw20337 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20337step0 raw20337; decide +kernel
      have hl : raw20337step0Labels = raw20337Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20337 raw20337Labels permutation182 permutation2
    _ = mixedMoment B node2691 node2691Labels := by rfl

theorem canonical20338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20338 raw20338Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw20338 raw20338Labels = mixedMoment B raw20338step0 raw20338step0Labels := by
      have ha : raw20338step0 = (fun i j => raw20338 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20338step0 raw20338; decide +kernel
      have hl : raw20338step0Labels = raw20338Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20338 raw20338Labels permutation182 permutation2
    _ = mixedMoment B node2694 node2694Labels := by rfl

theorem canonical20339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20339 raw20339Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw20339 raw20339Labels = mixedMoment B raw20339step0 raw20339step0Labels := by
      have ha : raw20339step0 = (fun i j => raw20339 (permutation182 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20339step0 raw20339; decide +kernel
      have hl : raw20339step0Labels = raw20339Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20339 raw20339Labels permutation182 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical20340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20340 raw20340Labels = mixedMoment B node1200 node1200Labels := by
  calc
    mixedMoment B raw20340 raw20340Labels = mixedMoment B raw20340step0 raw20340step0Labels := by
      have ha : raw20340step0 = (fun i j => raw20340 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20340step0 raw20340; decide +kernel
      have hl : raw20340step0Labels = raw20340Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20340 raw20340Labels permutation182 permutation2
    _ = mixedMoment B node1200 node1200Labels := by rfl

theorem canonical20341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20341 raw20341Labels = mixedMoment B node1210 node1210Labels := by
  calc
    mixedMoment B raw20341 raw20341Labels = mixedMoment B raw20341step0 raw20341step0Labels := by
      have ha : raw20341step0 = (fun i j => raw20341 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20341step0 raw20341; decide +kernel
      have hl : raw20341step0Labels = raw20341Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20341 raw20341Labels permutation200 permutation2
    _ = mixedMoment B node1210 node1210Labels := by rfl

theorem canonical20342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20342 raw20342Labels = mixedMoment B node1210 node1210Labels := by
  calc
    mixedMoment B raw20342 raw20342Labels = mixedMoment B raw20342step0 raw20342step0Labels := by
      have ha : raw20342step0 = (fun i j => raw20342 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20342step0 raw20342; decide +kernel
      have hl : raw20342step0Labels = raw20342Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20342 raw20342Labels permutation176 permutation2
    _ = mixedMoment B node1210 node1210Labels := by rfl

theorem canonical20343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20343 raw20343Labels = mixedMoment B node1196 node1196Labels := by
  calc
    mixedMoment B raw20343 raw20343Labels = mixedMoment B raw20343step0 raw20343step0Labels := by
      have ha : raw20343step0 = (fun i j => raw20343 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20343step0 raw20343; decide +kernel
      have hl : raw20343step0Labels = raw20343Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20343 raw20343Labels permutation182 permutation2
    _ = mixedMoment B node1196 node1196Labels := by rfl

theorem canonical20344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20344 raw20344Labels = mixedMoment B node1194 node1194Labels := by
  calc
    mixedMoment B raw20344 raw20344Labels = mixedMoment B raw20344step0 raw20344step0Labels := by
      have ha : raw20344step0 = (fun i j => raw20344 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20344step0 raw20344; decide +kernel
      have hl : raw20344step0Labels = raw20344Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20344 raw20344Labels permutation182 permutation2
    _ = mixedMoment B node1194 node1194Labels := by rfl

theorem canonical20345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20345 raw20345Labels = mixedMoment B node2008 node2008Labels := by
  calc
    mixedMoment B raw20345 raw20345Labels = mixedMoment B raw20345step0 raw20345step0Labels := by
      have ha : raw20345step0 = (fun i j => raw20345 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20345step0 raw20345; decide +kernel
      have hl : raw20345step0Labels = raw20345Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20345 raw20345Labels permutation682 permutation2
    mixedMoment B raw20345step0 raw20345step0Labels = mixedMoment B raw20345step1 raw20345step1Labels := by
      have ha : raw20345step1 = -raw20345step0 := by apply Matrix.ext; change ∀ i j, raw20345step1 i j = -(raw20345step0 i j); unfold raw20345step1 raw20345step0; decide +kernel
      have hl : raw20345step1Labels = raw20345step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2008 node2008Labels := by rfl

theorem canonical20346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20346 raw20346Labels = mixedMoment B node1987 node1987Labels := by
  calc
    mixedMoment B raw20346 raw20346Labels = mixedMoment B raw20346step0 raw20346step0Labels := by
      have ha : raw20346step0 = (fun i j => raw20346 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20346step0 raw20346; decide +kernel
      have hl : raw20346step0Labels = raw20346Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20346 raw20346Labels permutation676 permutation2
    mixedMoment B raw20346step0 raw20346step0Labels = mixedMoment B raw20346step1 raw20346step1Labels := by
      have ha : raw20346step1 = -raw20346step0 := by apply Matrix.ext; change ∀ i j, raw20346step1 i j = -(raw20346step0 i j); unfold raw20346step1 raw20346step0; decide +kernel
      have hl : raw20346step1Labels = raw20346step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1987 node1987Labels := by rfl

theorem canonical20347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20347 raw20347Labels = mixedMoment B node1987 node1987Labels := by
  calc
    mixedMoment B raw20347 raw20347Labels = mixedMoment B raw20347step0 raw20347step0Labels := by
      have ha : raw20347step0 = (fun i j => raw20347 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20347step0 raw20347; decide +kernel
      have hl : raw20347step0Labels = raw20347Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20347 raw20347Labels permutation674 permutation2
    mixedMoment B raw20347step0 raw20347step0Labels = mixedMoment B raw20347step1 raw20347step1Labels := by
      have ha : raw20347step1 = -raw20347step0 := by apply Matrix.ext; change ∀ i j, raw20347step1 i j = -(raw20347step0 i j); unfold raw20347step1 raw20347step0; decide +kernel
      have hl : raw20347step1Labels = raw20347step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1987 node1987Labels := by rfl

theorem canonical20348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20348 raw20348Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw20348 raw20348Labels = mixedMoment B raw20348step0 raw20348step0Labels := by
      have hz : ∀ j, raw20348 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20348step0 = (fun i j => raw20348 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20348step0 raw20348; decide +kernel
      have hl : raw20348step0Labels = raw20348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20348 raw20348Labels permutation520 hz
    mixedMoment B raw20348step0 raw20348step0Labels = mixedMoment B raw20348step1 raw20348step1Labels := by
      have ha : raw20348step1 = (fun i j => raw20348step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20348step1 raw20348step0; decide +kernel
      have hl : raw20348step1Labels = raw20348step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20348step0 raw20348step0Labels permutation137 permutation2
    mixedMoment B raw20348step1 raw20348step1Labels = mixedMoment B raw20348step2 raw20348step2Labels := by
      have ha : raw20348step2 = -raw20348step1 := by apply Matrix.ext; change ∀ i j, raw20348step2 i j = -(raw20348step1 i j); unfold raw20348step2 raw20348step1; decide +kernel
      have hl : raw20348step2Labels = raw20348step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2193 node2193Labels := by rfl

theorem canonical20349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20349 raw20349Labels = mixedMoment B node2693 node2693Labels := by
  calc
    mixedMoment B raw20349 raw20349Labels = mixedMoment B raw20349step0 raw20349step0Labels := by
      have ha : raw20349step0 = (fun i j => raw20349 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20349step0 raw20349; decide +kernel
      have hl : raw20349step0Labels = raw20349Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20349 raw20349Labels permutation182 permutation2
    _ = mixedMoment B node2693 node2693Labels := by rfl

theorem canonical20350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20350 raw20350Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw20350 raw20350Labels = mixedMoment B raw20350step0 raw20350step0Labels := by
      have hz : ∀ j, raw20350 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20350step0 = (fun i j => raw20350 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20350step0 raw20350; decide +kernel
      have hl : raw20350step0Labels = raw20350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20350 raw20350Labels permutation520 hz
    mixedMoment B raw20350step0 raw20350step0Labels = mixedMoment B raw20350step1 raw20350step1Labels := by
      have ha : raw20350step1 = (fun i j => raw20350step0 (permutation137 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20350step1 raw20350step0; decide +kernel
      have hl : raw20350step1Labels = raw20350step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20350step0 raw20350step0Labels permutation137 permutation0
    mixedMoment B raw20350step1 raw20350step1Labels = mixedMoment B raw20350step2 raw20350step2Labels := by
      have ha : raw20350step2 = -raw20350step1 := by apply Matrix.ext; change ∀ i j, raw20350step2 i j = -(raw20350step1 i j); unfold raw20350step2 raw20350step1; decide +kernel
      have hl : raw20350step2Labels = raw20350step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical159
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20474 raw20474Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw20474 raw20474Labels = mixedMoment B raw20474step0 raw20474step0Labels := by
      have hz : ∀ j, raw20474 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20474step0 = (fun i j => raw20474 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20474step0 raw20474; decide +kernel
      have hl : raw20474step0Labels = raw20474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20474 raw20474Labels permutation434 hz
    mixedMoment B raw20474step0 raw20474step0Labels = mixedMoment B raw20474step1 raw20474step1Labels := by
      have hz : ∀ j, raw20474step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20474step1 = (fun i j => raw20474step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20474step1 raw20474step0; decide +kernel
      have hl : raw20474step1Labels = raw20474step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20474step0 raw20474step0Labels permutation56 hz
    mixedMoment B raw20474step1 raw20474step1Labels = mixedMoment B raw20474step2 raw20474step2Labels := by
      have ha : raw20474step2 = -raw20474step1 := by apply Matrix.ext; change ∀ i j, raw20474step2 i j = -(raw20474step1 i j); unfold raw20474step2 raw20474step1; decide +kernel
      have hl : raw20474step2Labels = raw20474step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1750 node1750Labels := by rfl

theorem canonical20475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20475 raw20475Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw20475 raw20475Labels = mixedMoment B raw20475step0 raw20475step0Labels := by
      have hz : ∀ j, raw20475 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20475step0 = (fun i j => raw20475 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20475step0 raw20475; decide +kernel
      have hl : raw20475step0Labels = raw20475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20475 raw20475Labels permutation346 hz
    mixedMoment B raw20475step0 raw20475step0Labels = mixedMoment B raw20475step1 raw20475step1Labels := by
      have hz : ∀ j, raw20475step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20475step1 = (fun i j => raw20475step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20475step1 raw20475step0; decide +kernel
      have hl : raw20475step1Labels = raw20475step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20475step0 raw20475step0Labels permutation56 hz
    mixedMoment B raw20475step1 raw20475step1Labels = mixedMoment B raw20475step2 raw20475step2Labels := by
      have ha : raw20475step2 = -raw20475step1 := by apply Matrix.ext; change ∀ i j, raw20475step2 i j = -(raw20475step1 i j); unfold raw20475step2 raw20475step1; decide +kernel
      have hl : raw20475step2Labels = raw20475step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1750 node1750Labels := by rfl

theorem canonical20476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20476 raw20476Labels = mixedMoment B node1756 node1756Labels := by
  calc
    mixedMoment B raw20476 raw20476Labels = mixedMoment B raw20476step0 raw20476step0Labels := by
      have hz : ∀ j, raw20476 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20476step0 = (fun i j => raw20476 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20476step0 raw20476; decide +kernel
      have hl : raw20476step0Labels = raw20476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20476 raw20476Labels permutation434 hz
    mixedMoment B raw20476step0 raw20476step0Labels = mixedMoment B raw20476step1 raw20476step1Labels := by
      have hz : ∀ j, raw20476step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20476step1 = (fun i j => raw20476step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20476step1 raw20476step0; decide +kernel
      have hl : raw20476step1Labels = raw20476step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20476step0 raw20476step0Labels permutation80 hz
    mixedMoment B raw20476step1 raw20476step1Labels = mixedMoment B raw20476step2 raw20476step2Labels := by
      have hz : ∀ j, raw20476step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20476step2 = (fun i j => raw20476step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20476step2 raw20476step1; decide +kernel
      have hl : raw20476step2Labels = raw20476step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20476step1 raw20476step1Labels permutation14 hz
    mixedMoment B raw20476step2 raw20476step2Labels = mixedMoment B raw20476step3 raw20476step3Labels := by
      have ha : raw20476step3 = (fun i j => raw20476step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20476step3 raw20476step2; decide +kernel
      have hl : raw20476step3Labels = raw20476step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20476step2 raw20476step2Labels permutation3 permutation2
    mixedMoment B raw20476step3 raw20476step3Labels = mixedMoment B raw20476step4 raw20476step4Labels := by
      have ha : raw20476step4 = -raw20476step3 := by apply Matrix.ext; change ∀ i j, raw20476step4 i j = -(raw20476step3 i j); unfold raw20476step4 raw20476step3; decide +kernel
      have hl : raw20476step4Labels = raw20476step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1756 node1756Labels := by rfl

theorem canonical20477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20477 raw20477Labels = mixedMoment B node1754 node1754Labels := by
  calc
    mixedMoment B raw20477 raw20477Labels = mixedMoment B raw20477step0 raw20477step0Labels := by
      have hz : ∀ j, raw20477 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20477step0 = (fun i j => raw20477 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20477step0 raw20477; decide +kernel
      have hl : raw20477step0Labels = raw20477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20477 raw20477Labels permutation434 hz
    mixedMoment B raw20477step0 raw20477step0Labels = mixedMoment B raw20477step1 raw20477step1Labels := by
      have hz : ∀ j, raw20477step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20477step1 = (fun i j => raw20477step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20477step1 raw20477step0; decide +kernel
      have hl : raw20477step1Labels = raw20477step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20477step0 raw20477step0Labels permutation80 hz
    mixedMoment B raw20477step1 raw20477step1Labels = mixedMoment B raw20477step2 raw20477step2Labels := by
      have hz : ∀ j, raw20477step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20477step2 = (fun i j => raw20477step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20477step2 raw20477step1; decide +kernel
      have hl : raw20477step2Labels = raw20477step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20477step1 raw20477step1Labels permutation14 hz
    mixedMoment B raw20477step2 raw20477step2Labels = mixedMoment B raw20477step3 raw20477step3Labels := by
      have ha : raw20477step3 = -raw20477step2 := by apply Matrix.ext; change ∀ i j, raw20477step3 i j = -(raw20477step2 i j); unfold raw20477step3 raw20477step2; decide +kernel
      have hl : raw20477step3Labels = raw20477step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1754 node1754Labels := by rfl

theorem canonical20478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20478 raw20478Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw20478 raw20478Labels = mixedMoment B raw20478step0 raw20478step0Labels := by
      have hz : ∀ j, raw20478 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20478step0 = (fun i j => raw20478 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20478step0 raw20478; decide +kernel
      have hl : raw20478step0Labels = raw20478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20478 raw20478Labels permutation434 hz
    mixedMoment B raw20478step0 raw20478step0Labels = mixedMoment B raw20478step1 raw20478step1Labels := by
      have hz : ∀ j, raw20478step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20478step1 = (fun i j => raw20478step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20478step1 raw20478step0; decide +kernel
      have hl : raw20478step1Labels = raw20478step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20478step0 raw20478step0Labels permutation80 hz
    mixedMoment B raw20478step1 raw20478step1Labels = mixedMoment B raw20478step2 raw20478step2Labels := by
      have ha : raw20478step2 = (fun i j => raw20478step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20478step2 raw20478step1; decide +kernel
      have hl : raw20478step2Labels = raw20478step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20478step1 raw20478step1Labels permutation10 permutation4
    mixedMoment B raw20478step2 raw20478step2Labels = mixedMoment B raw20478step3 raw20478step3Labels := by
      have ha : raw20478step3 = -raw20478step2 := by apply Matrix.ext; change ∀ i j, raw20478step3 i j = -(raw20478step2 i j); unfold raw20478step3 raw20478step2; decide +kernel
      have hl : raw20478step3Labels = raw20478step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical20479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20479 raw20479Labels = mixedMoment B node1754 node1754Labels := by
  calc
    mixedMoment B raw20479 raw20479Labels = mixedMoment B raw20479step0 raw20479step0Labels := by
      have hz : ∀ j, raw20479 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20479step0 = (fun i j => raw20479 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20479step0 raw20479; decide +kernel
      have hl : raw20479step0Labels = raw20479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20479 raw20479Labels permutation434 hz
    mixedMoment B raw20479step0 raw20479step0Labels = mixedMoment B raw20479step1 raw20479step1Labels := by
      have hz : ∀ j, raw20479step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20479step1 = (fun i j => raw20479step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20479step1 raw20479step0; decide +kernel
      have hl : raw20479step1Labels = raw20479step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20479step0 raw20479step0Labels permutation80 hz
    mixedMoment B raw20479step1 raw20479step1Labels = mixedMoment B raw20479step2 raw20479step2Labels := by
      have hz : ∀ j, raw20479step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20479step2 = (fun i j => raw20479step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20479step2 raw20479step1; decide +kernel
      have hl : raw20479step2Labels = raw20479step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20479step1 raw20479step1Labels permutation14 hz
    mixedMoment B raw20479step2 raw20479step2Labels = mixedMoment B raw20479step3 raw20479step3Labels := by
      have ha : raw20479step3 = (fun i j => raw20479step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20479step3 raw20479step2; decide +kernel
      have hl : raw20479step3Labels = raw20479step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20479step2 raw20479step2Labels permutation2 permutation4
    mixedMoment B raw20479step3 raw20479step3Labels = mixedMoment B raw20479step4 raw20479step4Labels := by
      have ha : raw20479step4 = -raw20479step3 := by apply Matrix.ext; change ∀ i j, raw20479step4 i j = -(raw20479step3 i j); unfold raw20479step4 raw20479step3; decide +kernel
      have hl : raw20479step4Labels = raw20479step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1754 node1754Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical160
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20480 raw20480Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw20480 raw20480Labels = mixedMoment B raw20480step0 raw20480step0Labels := by
      have hz : ∀ j, raw20480 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20480step0 = (fun i j => raw20480 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20480step0 raw20480; decide +kernel
      have hl : raw20480step0Labels = raw20480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20480 raw20480Labels permutation434 hz
    mixedMoment B raw20480step0 raw20480step0Labels = mixedMoment B raw20480step1 raw20480step1Labels := by
      have hz : ∀ j, raw20480step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20480step1 = (fun i j => raw20480step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20480step1 raw20480step0; decide +kernel
      have hl : raw20480step1Labels = raw20480step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20480step0 raw20480step0Labels permutation80 hz
    mixedMoment B raw20480step1 raw20480step1Labels = mixedMoment B raw20480step2 raw20480step2Labels := by
      have hz : ∀ j, raw20480step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20480step2 = (fun i j => raw20480step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20480step2 raw20480step1; decide +kernel
      have hl : raw20480step2Labels = raw20480step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20480step1 raw20480step1Labels permutation14 hz
    mixedMoment B raw20480step2 raw20480step2Labels = mixedMoment B raw20480step3 raw20480step3Labels := by
      have ha : raw20480step3 = (fun i j => raw20480step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20480step3 raw20480step2; decide +kernel
      have hl : raw20480step3Labels = raw20480step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20480step2 raw20480step2Labels permutation2 permutation4
    mixedMoment B raw20480step3 raw20480step3Labels = mixedMoment B raw20480step4 raw20480step4Labels := by
      have ha : raw20480step4 = -raw20480step3 := by apply Matrix.ext; change ∀ i j, raw20480step4 i j = -(raw20480step3 i j); unfold raw20480step4 raw20480step3; decide +kernel
      have hl : raw20480step4Labels = raw20480step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1730 node1730Labels := by rfl

theorem canonical20481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20481 raw20481Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw20481 raw20481Labels = mixedMoment B raw20481step0 raw20481step0Labels := by
      have hz : ∀ j, raw20481 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20481step0 = (fun i j => raw20481 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20481step0 raw20481; decide +kernel
      have hl : raw20481step0Labels = raw20481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20481 raw20481Labels permutation434 hz
    mixedMoment B raw20481step0 raw20481step0Labels = mixedMoment B raw20481step1 raw20481step1Labels := by
      have hz : ∀ j, raw20481step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20481step1 = (fun i j => raw20481step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20481step1 raw20481step0; decide +kernel
      have hl : raw20481step1Labels = raw20481step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20481step0 raw20481step0Labels permutation56 hz
    mixedMoment B raw20481step1 raw20481step1Labels = mixedMoment B raw20481step2 raw20481step2Labels := by
      have ha : raw20481step2 = (fun i j => raw20481step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20481step2 raw20481step1; decide +kernel
      have hl : raw20481step2Labels = raw20481step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20481step1 raw20481step1Labels permutation8 permutation4
    mixedMoment B raw20481step2 raw20481step2Labels = mixedMoment B raw20481step3 raw20481step3Labels := by
      have ha : raw20481step3 = -raw20481step2 := by apply Matrix.ext; change ∀ i j, raw20481step3 i j = -(raw20481step2 i j); unfold raw20481step3 raw20481step2; decide +kernel
      have hl : raw20481step3Labels = raw20481step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3300 node3300Labels := by rfl

theorem canonical20482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20482 raw20482Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw20482 raw20482Labels = mixedMoment B raw20482step0 raw20482step0Labels := by
      have hz : ∀ j, raw20482 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20482step0 = (fun i j => raw20482 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20482step0 raw20482; decide +kernel
      have hl : raw20482step0Labels = raw20482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20482 raw20482Labels permutation346 hz
    mixedMoment B raw20482step0 raw20482step0Labels = mixedMoment B raw20482step1 raw20482step1Labels := by
      have hz : ∀ j, raw20482step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20482step1 = (fun i j => raw20482step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20482step1 raw20482step0; decide +kernel
      have hl : raw20482step1Labels = raw20482step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20482step0 raw20482step0Labels permutation56 hz
    mixedMoment B raw20482step1 raw20482step1Labels = mixedMoment B raw20482step2 raw20482step2Labels := by
      have ha : raw20482step2 = (fun i j => raw20482step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20482step2 raw20482step1; decide +kernel
      have hl : raw20482step2Labels = raw20482step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20482step1 raw20482step1Labels permutation8 permutation4
    mixedMoment B raw20482step2 raw20482step2Labels = mixedMoment B raw20482step3 raw20482step3Labels := by
      have ha : raw20482step3 = -raw20482step2 := by apply Matrix.ext; change ∀ i j, raw20482step3 i j = -(raw20482step2 i j); unfold raw20482step3 raw20482step2; decide +kernel
      have hl : raw20482step3Labels = raw20482step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3300 node3300Labels := by rfl

theorem canonical20483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20483 raw20483Labels = mixedMoment B node4184 node4184Labels := by
  calc
    mixedMoment B raw20483 raw20483Labels = mixedMoment B raw20483step0 raw20483step0Labels := by
      have hz : ∀ j, raw20483 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20483step0 = (fun i j => raw20483 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20483step0 raw20483; decide +kernel
      have hl : raw20483step0Labels = raw20483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20483 raw20483Labels permutation434 hz
    mixedMoment B raw20483step0 raw20483step0Labels = mixedMoment B raw20483step1 raw20483step1Labels := by
      have hz : ∀ j, raw20483step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20483step1 = (fun i j => raw20483step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20483step1 raw20483step0; decide +kernel
      have hl : raw20483step1Labels = raw20483step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20483step0 raw20483step0Labels permutation80 hz
    mixedMoment B raw20483step1 raw20483step1Labels = mixedMoment B raw20483step2 raw20483step2Labels := by
      have ha : raw20483step2 = (fun i j => raw20483step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20483step2 raw20483step1; decide +kernel
      have hl : raw20483step2Labels = raw20483step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20483step1 raw20483step1Labels permutation8 permutation3
    mixedMoment B raw20483step2 raw20483step2Labels = mixedMoment B raw20483step3 raw20483step3Labels := by
      have ha : raw20483step3 = raw20483step2 := by apply Matrix.ext; unfold raw20483step3 raw20483step2; decide +kernel
      have hl : raw20483step2Labels = labelEmbedding6 ∘ raw20483step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20483step2 raw20483step2Labels raw20483step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4184 node4184Labels := by rfl

theorem canonical20484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20484 raw20484Labels = mixedMoment B node4552 node4552Labels := by
  calc
    mixedMoment B raw20484 raw20484Labels = mixedMoment B raw20484step0 raw20484step0Labels := by
      have hz : ∀ j, raw20484 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20484step0 = (fun i j => raw20484 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20484step0 raw20484; decide +kernel
      have hl : raw20484step0Labels = raw20484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20484 raw20484Labels permutation434 hz
    mixedMoment B raw20484step0 raw20484step0Labels = mixedMoment B raw20484step1 raw20484step1Labels := by
      have ha : raw20484step1 = (fun i j => raw20484step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20484step1 raw20484step0; decide +kernel
      have hl : raw20484step1Labels = raw20484step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20484step0 raw20484step0Labels permutation38 permutation3
    mixedMoment B raw20484step1 raw20484step1Labels = mixedMoment B raw20484step2 raw20484step2Labels := by
      have ha : raw20484step2 = raw20484step1 := by apply Matrix.ext; unfold raw20484step2 raw20484step1; decide +kernel
      have hl : raw20484step1Labels = labelEmbedding6 ∘ raw20484step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20484step1 raw20484step1Labels raw20484step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4552 node4552Labels := by rfl

theorem canonical20485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20485 raw20485Labels = mixedMoment B node4552 node4552Labels := by
  calc
    mixedMoment B raw20485 raw20485Labels = mixedMoment B raw20485step0 raw20485step0Labels := by
      have hz : ∀ j, raw20485 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20485step0 = (fun i j => raw20485 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20485step0 raw20485; decide +kernel
      have hl : raw20485step0Labels = raw20485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20485 raw20485Labels permutation346 hz
    mixedMoment B raw20485step0 raw20485step0Labels = mixedMoment B raw20485step1 raw20485step1Labels := by
      have ha : raw20485step1 = (fun i j => raw20485step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20485step1 raw20485step0; decide +kernel
      have hl : raw20485step1Labels = raw20485step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20485step0 raw20485step0Labels permutation38 permutation3
    mixedMoment B raw20485step1 raw20485step1Labels = mixedMoment B raw20485step2 raw20485step2Labels := by
      have ha : raw20485step2 = raw20485step1 := by apply Matrix.ext; unfold raw20485step2 raw20485step1; decide +kernel
      have hl : raw20485step1Labels = labelEmbedding6 ∘ raw20485step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20485step1 raw20485step1Labels raw20485step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4552 node4552Labels := by rfl

theorem canonical20486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20486 raw20486Labels = mixedMoment B node4184 node4184Labels := by
  calc
    mixedMoment B raw20486 raw20486Labels = mixedMoment B raw20486step0 raw20486step0Labels := by
      have hz : ∀ j, raw20486 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20486step0 = (fun i j => raw20486 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20486step0 raw20486; decide +kernel
      have hl : raw20486step0Labels = raw20486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20486 raw20486Labels permutation434 hz
    mixedMoment B raw20486step0 raw20486step0Labels = mixedMoment B raw20486step1 raw20486step1Labels := by
      have hz : ∀ j, raw20486step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20486step1 = (fun i j => raw20486step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20486step1 raw20486step0; decide +kernel
      have hl : raw20486step1Labels = raw20486step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20486step0 raw20486step0Labels permutation56 hz
    mixedMoment B raw20486step1 raw20486step1Labels = mixedMoment B raw20486step2 raw20486step2Labels := by
      have ha : raw20486step2 = (fun i j => raw20486step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20486step2 raw20486step1; decide +kernel
      have hl : raw20486step2Labels = raw20486step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20486step1 raw20486step1Labels permutation8 permutation3
    mixedMoment B raw20486step2 raw20486step2Labels = mixedMoment B raw20486step3 raw20486step3Labels := by
      have ha : raw20486step3 = raw20486step2 := by apply Matrix.ext; unfold raw20486step3 raw20486step2; decide +kernel
      have hl : raw20486step2Labels = labelEmbedding6 ∘ raw20486step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20486step2 raw20486step2Labels raw20486step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4184 node4184Labels := by rfl

theorem canonical20487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20487 raw20487Labels = mixedMoment B node4552 node4552Labels := by
  calc
    mixedMoment B raw20487 raw20487Labels = mixedMoment B raw20487step0 raw20487step0Labels := by
      have hz : ∀ j, raw20487 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20487step0 = (fun i j => raw20487 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20487step0 raw20487; decide +kernel
      have hl : raw20487step0Labels = raw20487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20487 raw20487Labels permutation434 hz
    mixedMoment B raw20487step0 raw20487step0Labels = mixedMoment B raw20487step1 raw20487step1Labels := by
      have ha : raw20487step1 = (fun i j => raw20487step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20487step1 raw20487step0; decide +kernel
      have hl : raw20487step1Labels = raw20487step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20487step0 raw20487step0Labels permutation32 permutation3
    mixedMoment B raw20487step1 raw20487step1Labels = mixedMoment B raw20487step2 raw20487step2Labels := by
      have ha : raw20487step2 = raw20487step1 := by apply Matrix.ext; unfold raw20487step2 raw20487step1; decide +kernel
      have hl : raw20487step1Labels = labelEmbedding6 ∘ raw20487step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20487step1 raw20487step1Labels raw20487step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4552 node4552Labels := by rfl

theorem canonical20488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20488 raw20488Labels = mixedMoment B node4552 node4552Labels := by
  calc
    mixedMoment B raw20488 raw20488Labels = mixedMoment B raw20488step0 raw20488step0Labels := by
      have hz : ∀ j, raw20488 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20488step0 = (fun i j => raw20488 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20488step0 raw20488; decide +kernel
      have hl : raw20488step0Labels = raw20488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20488 raw20488Labels permutation265 hz
    mixedMoment B raw20488step0 raw20488step0Labels = mixedMoment B raw20488step1 raw20488step1Labels := by
      have ha : raw20488step1 = (fun i j => raw20488step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20488step1 raw20488step0; decide +kernel
      have hl : raw20488step1Labels = raw20488step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20488step0 raw20488step0Labels permutation38 permutation3
    mixedMoment B raw20488step1 raw20488step1Labels = mixedMoment B raw20488step2 raw20488step2Labels := by
      have ha : raw20488step2 = raw20488step1 := by apply Matrix.ext; unfold raw20488step2 raw20488step1; decide +kernel
      have hl : raw20488step1Labels = labelEmbedding6 ∘ raw20488step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20488step1 raw20488step1Labels raw20488step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4552 node4552Labels := by rfl

theorem canonical20489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20489 raw20489Labels = mixedMoment B node4184 node4184Labels := by
  calc
    mixedMoment B raw20489 raw20489Labels = mixedMoment B raw20489step0 raw20489step0Labels := by
      have hz : ∀ j, raw20489 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20489step0 = (fun i j => raw20489 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20489step0 raw20489; decide +kernel
      have hl : raw20489step0Labels = raw20489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20489 raw20489Labels permutation346 hz
    mixedMoment B raw20489step0 raw20489step0Labels = mixedMoment B raw20489step1 raw20489step1Labels := by
      have hz : ∀ j, raw20489step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20489step1 = (fun i j => raw20489step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20489step1 raw20489step0; decide +kernel
      have hl : raw20489step1Labels = raw20489step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20489step0 raw20489step0Labels permutation56 hz
    mixedMoment B raw20489step1 raw20489step1Labels = mixedMoment B raw20489step2 raw20489step2Labels := by
      have ha : raw20489step2 = (fun i j => raw20489step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20489step2 raw20489step1; decide +kernel
      have hl : raw20489step2Labels = raw20489step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20489step1 raw20489step1Labels permutation8 permutation3
    mixedMoment B raw20489step2 raw20489step2Labels = mixedMoment B raw20489step3 raw20489step3Labels := by
      have ha : raw20489step3 = raw20489step2 := by apply Matrix.ext; unfold raw20489step3 raw20489step2; decide +kernel
      have hl : raw20489step2Labels = labelEmbedding6 ∘ raw20489step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20489step2 raw20489step2Labels raw20489step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4184 node4184Labels := by rfl

theorem canonical20490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20490 raw20490Labels = mixedMoment B node4552 node4552Labels := by
  calc
    mixedMoment B raw20490 raw20490Labels = mixedMoment B raw20490step0 raw20490step0Labels := by
      have hz : ∀ j, raw20490 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20490step0 = (fun i j => raw20490 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20490step0 raw20490; decide +kernel
      have hl : raw20490step0Labels = raw20490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20490 raw20490Labels permutation346 hz
    mixedMoment B raw20490step0 raw20490step0Labels = mixedMoment B raw20490step1 raw20490step1Labels := by
      have ha : raw20490step1 = (fun i j => raw20490step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20490step1 raw20490step0; decide +kernel
      have hl : raw20490step1Labels = raw20490step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20490step0 raw20490step0Labels permutation32 permutation3
    mixedMoment B raw20490step1 raw20490step1Labels = mixedMoment B raw20490step2 raw20490step2Labels := by
      have ha : raw20490step2 = raw20490step1 := by apply Matrix.ext; unfold raw20490step2 raw20490step1; decide +kernel
      have hl : raw20490step1Labels = labelEmbedding6 ∘ raw20490step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20490step1 raw20490step1Labels raw20490step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4552 node4552Labels := by rfl

theorem canonical20491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20491 raw20491Labels = mixedMoment B node4552 node4552Labels := by
  calc
    mixedMoment B raw20491 raw20491Labels = mixedMoment B raw20491step0 raw20491step0Labels := by
      have hz : ∀ j, raw20491 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20491step0 = (fun i j => raw20491 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20491step0 raw20491; decide +kernel
      have hl : raw20491step0Labels = raw20491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20491 raw20491Labels permutation265 hz
    mixedMoment B raw20491step0 raw20491step0Labels = mixedMoment B raw20491step1 raw20491step1Labels := by
      have ha : raw20491step1 = (fun i j => raw20491step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20491step1 raw20491step0; decide +kernel
      have hl : raw20491step1Labels = raw20491step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20491step0 raw20491step0Labels permutation32 permutation3
    mixedMoment B raw20491step1 raw20491step1Labels = mixedMoment B raw20491step2 raw20491step2Labels := by
      have ha : raw20491step2 = raw20491step1 := by apply Matrix.ext; unfold raw20491step2 raw20491step1; decide +kernel
      have hl : raw20491step1Labels = labelEmbedding6 ∘ raw20491step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20491step1 raw20491step1Labels raw20491step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4552 node4552Labels := by rfl

theorem canonical20492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20492 raw20492Labels = mixedMoment B node4193 node4193Labels := by
  calc
    mixedMoment B raw20492 raw20492Labels = mixedMoment B raw20492step0 raw20492step0Labels := by
      have hz : ∀ j, raw20492 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20492step0 = (fun i j => raw20492 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20492step0 raw20492; decide +kernel
      have hl : raw20492step0Labels = raw20492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20492 raw20492Labels permutation434 hz
    mixedMoment B raw20492step0 raw20492step0Labels = mixedMoment B raw20492step1 raw20492step1Labels := by
      have hz : ∀ j, raw20492step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20492step1 = (fun i j => raw20492step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20492step1 raw20492step0; decide +kernel
      have hl : raw20492step1Labels = raw20492step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20492step0 raw20492step0Labels permutation80 hz
    mixedMoment B raw20492step1 raw20492step1Labels = mixedMoment B raw20492step2 raw20492step2Labels := by
      have hz : ∀ j, raw20492step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20492step2 = (fun i j => raw20492step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20492step2 raw20492step1; decide +kernel
      have hl : raw20492step2Labels = raw20492step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20492step1 raw20492step1Labels permutation14 hz
    mixedMoment B raw20492step2 raw20492step2Labels = mixedMoment B raw20492step3 raw20492step3Labels := by
      have ha : raw20492step3 = (fun i j => raw20492step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20492step3 raw20492step2; decide +kernel
      have hl : raw20492step3Labels = raw20492step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20492step2 raw20492step2Labels permutation2 permutation3
    mixedMoment B raw20492step3 raw20492step3Labels = mixedMoment B raw20492step4 raw20492step4Labels := by
      have ha : raw20492step4 = raw20492step3 := by apply Matrix.ext; unfold raw20492step4 raw20492step3; decide +kernel
      have hl : raw20492step3Labels = labelEmbedding6 ∘ raw20492step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20492step3 raw20492step3Labels raw20492step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4193 node4193Labels := by rfl

theorem canonical20493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20493 raw20493Labels = mixedMoment B node4560 node4560Labels := by
  calc
    mixedMoment B raw20493 raw20493Labels = mixedMoment B raw20493step0 raw20493step0Labels := by
      have hz : ∀ j, raw20493 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20493step0 = (fun i j => raw20493 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20493step0 raw20493; decide +kernel
      have hl : raw20493step0Labels = raw20493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20493 raw20493Labels permutation434 hz
    mixedMoment B raw20493step0 raw20493step0Labels = mixedMoment B raw20493step1 raw20493step1Labels := by
      have hz : ∀ j, raw20493step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20493step1 = (fun i j => raw20493step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20493step1 raw20493step0; decide +kernel
      have hl : raw20493step1Labels = raw20493step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20493step0 raw20493step0Labels permutation80 hz
    mixedMoment B raw20493step1 raw20493step1Labels = mixedMoment B raw20493step2 raw20493step2Labels := by
      have ha : raw20493step2 = (fun i j => raw20493step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20493step2 raw20493step1; decide +kernel
      have hl : raw20493step2Labels = raw20493step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20493step1 raw20493step1Labels permutation8 permutation3
    mixedMoment B raw20493step2 raw20493step2Labels = mixedMoment B raw20493step3 raw20493step3Labels := by
      have ha : raw20493step3 = raw20493step2 := by apply Matrix.ext; unfold raw20493step3 raw20493step2; decide +kernel
      have hl : raw20493step2Labels = labelEmbedding6 ∘ raw20493step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20493step2 raw20493step2Labels raw20493step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4560 node4560Labels := by rfl

theorem canonical20494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20494 raw20494Labels = mixedMoment B node4560 node4560Labels := by
  calc
    mixedMoment B raw20494 raw20494Labels = mixedMoment B raw20494step0 raw20494step0Labels := by
      have hz : ∀ j, raw20494 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20494step0 = (fun i j => raw20494 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20494step0 raw20494; decide +kernel
      have hl : raw20494step0Labels = raw20494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20494 raw20494Labels permutation434 hz
    mixedMoment B raw20494step0 raw20494step0Labels = mixedMoment B raw20494step1 raw20494step1Labels := by
      have hz : ∀ j, raw20494step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20494step1 = (fun i j => raw20494step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20494step1 raw20494step0; decide +kernel
      have hl : raw20494step1Labels = raw20494step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20494step0 raw20494step0Labels permutation56 hz
    mixedMoment B raw20494step1 raw20494step1Labels = mixedMoment B raw20494step2 raw20494step2Labels := by
      have ha : raw20494step2 = (fun i j => raw20494step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20494step2 raw20494step1; decide +kernel
      have hl : raw20494step2Labels = raw20494step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20494step1 raw20494step1Labels permutation8 permutation3
    mixedMoment B raw20494step2 raw20494step2Labels = mixedMoment B raw20494step3 raw20494step3Labels := by
      have ha : raw20494step3 = raw20494step2 := by apply Matrix.ext; unfold raw20494step3 raw20494step2; decide +kernel
      have hl : raw20494step2Labels = labelEmbedding6 ∘ raw20494step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20494step2 raw20494step2Labels raw20494step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4560 node4560Labels := by rfl

theorem canonical20495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20495 raw20495Labels = mixedMoment B node4560 node4560Labels := by
  calc
    mixedMoment B raw20495 raw20495Labels = mixedMoment B raw20495step0 raw20495step0Labels := by
      have hz : ∀ j, raw20495 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20495step0 = (fun i j => raw20495 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20495step0 raw20495; decide +kernel
      have hl : raw20495step0Labels = raw20495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20495 raw20495Labels permutation346 hz
    mixedMoment B raw20495step0 raw20495step0Labels = mixedMoment B raw20495step1 raw20495step1Labels := by
      have hz : ∀ j, raw20495step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20495step1 = (fun i j => raw20495step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20495step1 raw20495step0; decide +kernel
      have hl : raw20495step1Labels = raw20495step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20495step0 raw20495step0Labels permutation56 hz
    mixedMoment B raw20495step1 raw20495step1Labels = mixedMoment B raw20495step2 raw20495step2Labels := by
      have ha : raw20495step2 = (fun i j => raw20495step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20495step2 raw20495step1; decide +kernel
      have hl : raw20495step2Labels = raw20495step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20495step1 raw20495step1Labels permutation8 permutation3
    mixedMoment B raw20495step2 raw20495step2Labels = mixedMoment B raw20495step3 raw20495step3Labels := by
      have ha : raw20495step3 = raw20495step2 := by apply Matrix.ext; unfold raw20495step3 raw20495step2; decide +kernel
      have hl : raw20495step2Labels = labelEmbedding6 ∘ raw20495step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20495step2 raw20495step2Labels raw20495step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4560 node4560Labels := by rfl

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

theorem canonical2319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2319 raw2319Labels = mixedMoment B node5305 node5305Labels := by
  calc
    mixedMoment B raw2319 raw2319Labels = mixedMoment B raw2319step0 raw2319step0Labels := by
      have ha : raw2319step0 = (fun i j => raw2319 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2319step0 raw2319; decide +kernel
      have hl : raw2319step0Labels = raw2319Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2319 raw2319Labels permutation2 permutation4
    mixedMoment B raw2319step0 raw2319step0Labels = mixedMoment B raw2319step1 raw2319step1Labels := by
      have ha : raw2319step1 = raw2319step0 := by apply Matrix.ext; unfold raw2319step1 raw2319step0; decide +kernel
      have hl : raw2319step0Labels = labelEmbedding7 ∘ raw2319step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2319step0 raw2319step0Labels raw2319step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5305 node5305Labels := by rfl

theorem canonical2320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2320 raw2320Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw2320 raw2320Labels = mixedMoment B raw2320step0 raw2320step0Labels := by
      have ha : raw2320step0 = (fun i j => raw2320 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2320step0 raw2320; decide +kernel
      have hl : raw2320step0Labels = raw2320Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2320 raw2320Labels permutation2 permutation4
    _ = mixedMoment B node2783 node2783Labels := by rfl

theorem canonical2321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2321 raw2321Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw2321 raw2321Labels = mixedMoment B raw2321step0 raw2321step0Labels := by
      have ha : raw2321step0 = (fun i j => raw2321 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2321step0 raw2321; decide +kernel
      have hl : raw2321step0Labels = raw2321Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2321 raw2321Labels permutation7 permutation6
    mixedMoment B raw2321step0 raw2321step0Labels = mixedMoment B raw2321step1 raw2321step1Labels := by
      have ha : raw2321step1 = raw2321step0 := by apply Matrix.ext; unfold raw2321step1 raw2321step0; decide +kernel
      have hl : raw2321step0Labels = labelEmbedding1 ∘ raw2321step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2321step0 raw2321step0Labels raw2321step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2783 node2783Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5106 raw5106Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw5106 raw5106Labels = mixedMoment B raw5106step0 raw5106step0Labels := by
      have hz : ∀ j, raw5106 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5106step0 = (fun i j => raw5106 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5106step0 raw5106; decide +kernel
      have hl : raw5106step0Labels = raw5106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5106 raw5106Labels permutation434 hz
    mixedMoment B raw5106step0 raw5106step0Labels = mixedMoment B raw5106step1 raw5106step1Labels := by
      have hz : ∀ j, raw5106step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5106step1 = (fun i j => raw5106step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5106step1 raw5106step0; decide +kernel
      have hl : raw5106step1Labels = raw5106step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5106step0 raw5106step0Labels permutation80 hz
    mixedMoment B raw5106step1 raw5106step1Labels = mixedMoment B raw5106step2 raw5106step2Labels := by
      have ha : raw5106step2 = (fun i j => raw5106step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5106step2 raw5106step1; decide +kernel
      have hl : raw5106step2Labels = raw5106step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5106step1 raw5106step1Labels permutation10 permutation2
    _ = mixedMoment B node4605 node4605Labels := by rfl

theorem canonical5111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5111 raw5111Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw5111 raw5111Labels = mixedMoment B raw5111step0 raw5111step0Labels := by
      have hz : ∀ j, raw5111 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5111step0 = (fun i j => raw5111 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5111step0 raw5111; decide +kernel
      have hl : raw5111step0Labels = raw5111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5111 raw5111Labels permutation434 hz
    mixedMoment B raw5111step0 raw5111step0Labels = mixedMoment B raw5111step1 raw5111step1Labels := by
      have hz : ∀ j, raw5111step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5111step1 = (fun i j => raw5111step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5111step1 raw5111step0; decide +kernel
      have hl : raw5111step1Labels = raw5111step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5111step0 raw5111step0Labels permutation56 hz
    mixedMoment B raw5111step1 raw5111step1Labels = mixedMoment B raw5111step2 raw5111step2Labels := by
      have ha : raw5111step2 = (fun i j => raw5111step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5111step2 raw5111step1; decide +kernel
      have hl : raw5111step2Labels = raw5111step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5111step1 raw5111step1Labels permutation10 permutation2
    _ = mixedMoment B node4605 node4605Labels := by rfl

theorem canonical5116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5116 raw5116Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw5116 raw5116Labels = mixedMoment B raw5116step0 raw5116step0Labels := by
      have hz : ∀ j, raw5116 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5116step0 = (fun i j => raw5116 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5116step0 raw5116; decide +kernel
      have hl : raw5116step0Labels = raw5116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5116 raw5116Labels permutation346 hz
    mixedMoment B raw5116step0 raw5116step0Labels = mixedMoment B raw5116step1 raw5116step1Labels := by
      have hz : ∀ j, raw5116step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5116step1 = (fun i j => raw5116step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5116step1 raw5116step0; decide +kernel
      have hl : raw5116step1Labels = raw5116step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5116step0 raw5116step0Labels permutation56 hz
    mixedMoment B raw5116step1 raw5116step1Labels = mixedMoment B raw5116step2 raw5116step2Labels := by
      have ha : raw5116step2 = (fun i j => raw5116step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5116step2 raw5116step1; decide +kernel
      have hl : raw5116step2Labels = raw5116step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5116step1 raw5116step1Labels permutation10 permutation2
    _ = mixedMoment B node4605 node4605Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5122 raw5122Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw5122 raw5122Labels = mixedMoment B raw5122step0 raw5122step0Labels := by
      have hz : ∀ j, raw5122 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5122step0 = (fun i j => raw5122 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5122step0 raw5122; decide +kernel
      have hl : raw5122step0Labels = raw5122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5122 raw5122Labels permutation434 hz
    mixedMoment B raw5122step0 raw5122step0Labels = mixedMoment B raw5122step1 raw5122step1Labels := by
      have hz : ∀ j, raw5122step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5122step1 = (fun i j => raw5122step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5122step1 raw5122step0; decide +kernel
      have hl : raw5122step1Labels = raw5122step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5122step0 raw5122step0Labels permutation80 hz
    mixedMoment B raw5122step1 raw5122step1Labels = mixedMoment B raw5122step2 raw5122step2Labels := by
      have ha : raw5122step2 = (fun i j => raw5122step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5122step2 raw5122step1; decide +kernel
      have hl : raw5122step2Labels = raw5122step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5122step1 raw5122step1Labels permutation31 permutation2
    mixedMoment B raw5122step2 raw5122step2Labels = mixedMoment B raw5122step3 raw5122step3Labels := by
      have ha : raw5122step3 = -raw5122step2 := by apply Matrix.ext; change ∀ i j, raw5122step3 i j = -(raw5122step2 i j); unfold raw5122step3 raw5122step2; decide +kernel
      have hl : raw5122step3Labels = raw5122step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4868 node4868Labels := by rfl

theorem canonical5123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5123 raw5123Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw5123 raw5123Labels = mixedMoment B raw5123step0 raw5123step0Labels := by
      have hz : ∀ j, raw5123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5123step0 = (fun i j => raw5123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5123step0 raw5123; decide +kernel
      have hl : raw5123step0Labels = raw5123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5123 raw5123Labels permutation434 hz
    mixedMoment B raw5123step0 raw5123step0Labels = mixedMoment B raw5123step1 raw5123step1Labels := by
      have hz : ∀ j, raw5123step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5123step1 = (fun i j => raw5123step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5123step1 raw5123step0; decide +kernel
      have hl : raw5123step1Labels = raw5123step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5123step0 raw5123step0Labels permutation56 hz
    mixedMoment B raw5123step1 raw5123step1Labels = mixedMoment B raw5123step2 raw5123step2Labels := by
      have ha : raw5123step2 = (fun i j => raw5123step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5123step2 raw5123step1; decide +kernel
      have hl : raw5123step2Labels = raw5123step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5123step1 raw5123step1Labels permutation31 permutation2
    mixedMoment B raw5123step2 raw5123step2Labels = mixedMoment B raw5123step3 raw5123step3Labels := by
      have ha : raw5123step3 = -raw5123step2 := by apply Matrix.ext; change ∀ i j, raw5123step3 i j = -(raw5123step2 i j); unfold raw5123step3 raw5123step2; decide +kernel
      have hl : raw5123step3Labels = raw5123step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4868 node4868Labels := by rfl

theorem canonical5124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5124 raw5124Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw5124 raw5124Labels = mixedMoment B raw5124step0 raw5124step0Labels := by
      have hz : ∀ j, raw5124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5124step0 = (fun i j => raw5124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5124step0 raw5124; decide +kernel
      have hl : raw5124step0Labels = raw5124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5124 raw5124Labels permutation346 hz
    mixedMoment B raw5124step0 raw5124step0Labels = mixedMoment B raw5124step1 raw5124step1Labels := by
      have hz : ∀ j, raw5124step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5124step1 = (fun i j => raw5124step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5124step1 raw5124step0; decide +kernel
      have hl : raw5124step1Labels = raw5124step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5124step0 raw5124step0Labels permutation56 hz
    mixedMoment B raw5124step1 raw5124step1Labels = mixedMoment B raw5124step2 raw5124step2Labels := by
      have ha : raw5124step2 = (fun i j => raw5124step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5124step2 raw5124step1; decide +kernel
      have hl : raw5124step2Labels = raw5124step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5124step1 raw5124step1Labels permutation31 permutation2
    mixedMoment B raw5124step2 raw5124step2Labels = mixedMoment B raw5124step3 raw5124step3Labels := by
      have ha : raw5124step3 = -raw5124step2 := by apply Matrix.ext; change ∀ i j, raw5124step3 i j = -(raw5124step2 i j); unfold raw5124step3 raw5124step2; decide +kernel
      have hl : raw5124step3Labels = raw5124step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4868 node4868Labels := by rfl

theorem canonical5125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5125 raw5125Labels = mixedMoment B node5305 node5305Labels := by
  calc
    mixedMoment B raw5125 raw5125Labels = mixedMoment B raw5125step0 raw5125step0Labels := by
      have hz : ∀ j, raw5125 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5125step0 = (fun i j => raw5125 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5125step0 raw5125; decide +kernel
      have hl : raw5125step0Labels = raw5125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5125 raw5125Labels permutation434 hz
    mixedMoment B raw5125step0 raw5125step0Labels = mixedMoment B raw5125step1 raw5125step1Labels := by
      have hz : ∀ j, raw5125step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5125step1 = (fun i j => raw5125step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5125step1 raw5125step0; decide +kernel
      have hl : raw5125step1Labels = raw5125step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5125step0 raw5125step0Labels permutation80 hz
    mixedMoment B raw5125step1 raw5125step1Labels = mixedMoment B raw5125step2 raw5125step2Labels := by
      have hz : ∀ j, raw5125step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5125step2 = (fun i j => raw5125step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5125step2 raw5125step1; decide +kernel
      have hl : raw5125step2Labels = raw5125step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5125step1 raw5125step1Labels permutation14 hz
    _ = mixedMoment B node5305 node5305Labels := by rfl

theorem canonical5126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5126 raw5126Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw5126 raw5126Labels = mixedMoment B raw5126step0 raw5126step0Labels := by
      have hz : ∀ j, raw5126 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5126step0 = (fun i j => raw5126 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5126step0 raw5126; decide +kernel
      have hl : raw5126step0Labels = raw5126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5126 raw5126Labels permutation434 hz
    mixedMoment B raw5126step0 raw5126step0Labels = mixedMoment B raw5126step1 raw5126step1Labels := by
      have hz : ∀ j, raw5126step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5126step1 = (fun i j => raw5126step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5126step1 raw5126step0; decide +kernel
      have hl : raw5126step1Labels = raw5126step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5126step0 raw5126step0Labels permutation80 hz
    mixedMoment B raw5126step1 raw5126step1Labels = mixedMoment B raw5126step2 raw5126step2Labels := by
      have hz : ∀ j, raw5126step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5126step2 = (fun i j => raw5126step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5126step2 raw5126step1; decide +kernel
      have hl : raw5126step2Labels = raw5126step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5126step1 raw5126step1Labels permutation14 hz
    mixedMoment B raw5126step2 raw5126step2Labels = mixedMoment B raw5126step3 raw5126step3Labels := by
      have ha : raw5126step3 = (fun i j => raw5126step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5126step3 raw5126step2; decide +kernel
      have hl : raw5126step3Labels = raw5126step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5126step2 raw5126step2Labels permutation7 permutation2
    mixedMoment B raw5126step3 raw5126step3Labels = mixedMoment B raw5126step4 raw5126step4Labels := by
      have ha : raw5126step4 = -raw5126step3 := by apply Matrix.ext; change ∀ i j, raw5126step4 i j = -(raw5126step3 i j); unfold raw5126step4 raw5126step3; decide +kernel
      have hl : raw5126step4Labels = raw5126step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4468 node4468Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10242 raw10242Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw10242 raw10242Labels = mixedMoment B raw10242step0 raw10242step0Labels := by
      have hz : ∀ j, raw10242 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10242step0 = (fun i j => raw10242 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10242step0 raw10242; decide +kernel
      have hl : raw10242step0Labels = raw10242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10242 raw10242Labels permutation434 hz
    mixedMoment B raw10242step0 raw10242step0Labels = mixedMoment B raw10242step1 raw10242step1Labels := by
      have hz : ∀ j, raw10242step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10242step1 = (fun i j => raw10242step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10242step1 raw10242step0; decide +kernel
      have hl : raw10242step1Labels = raw10242step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10242step0 raw10242step0Labels permutation80 hz
    mixedMoment B raw10242step1 raw10242step1Labels = mixedMoment B raw10242step2 raw10242step2Labels := by
      have ha : raw10242step2 = (fun i j => raw10242step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10242step2 raw10242step1; decide +kernel
      have hl : raw10242step2Labels = raw10242step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10242step1 raw10242step1Labels permutation10 permutation2
    _ = mixedMoment B node4617 node4617Labels := by rfl

theorem canonical10246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10246 raw10246Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw10246 raw10246Labels = mixedMoment B raw10246step0 raw10246step0Labels := by
      have hz : ∀ j, raw10246 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10246step0 = (fun i j => raw10246 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10246step0 raw10246; decide +kernel
      have hl : raw10246step0Labels = raw10246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10246 raw10246Labels permutation434 hz
    mixedMoment B raw10246step0 raw10246step0Labels = mixedMoment B raw10246step1 raw10246step1Labels := by
      have hz : ∀ j, raw10246step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10246step1 = (fun i j => raw10246step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10246step1 raw10246step0; decide +kernel
      have hl : raw10246step1Labels = raw10246step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10246step0 raw10246step0Labels permutation56 hz
    mixedMoment B raw10246step1 raw10246step1Labels = mixedMoment B raw10246step2 raw10246step2Labels := by
      have ha : raw10246step2 = (fun i j => raw10246step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10246step2 raw10246step1; decide +kernel
      have hl : raw10246step2Labels = raw10246step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10246step1 raw10246step1Labels permutation10 permutation2
    _ = mixedMoment B node4617 node4617Labels := by rfl

theorem canonical10250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10250 raw10250Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw10250 raw10250Labels = mixedMoment B raw10250step0 raw10250step0Labels := by
      have hz : ∀ j, raw10250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10250step0 = (fun i j => raw10250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10250step0 raw10250; decide +kernel
      have hl : raw10250step0Labels = raw10250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10250 raw10250Labels permutation346 hz
    mixedMoment B raw10250step0 raw10250step0Labels = mixedMoment B raw10250step1 raw10250step1Labels := by
      have hz : ∀ j, raw10250step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10250step1 = (fun i j => raw10250step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10250step1 raw10250step0; decide +kernel
      have hl : raw10250step1Labels = raw10250step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10250step0 raw10250step0Labels permutation56 hz
    mixedMoment B raw10250step1 raw10250step1Labels = mixedMoment B raw10250step2 raw10250step2Labels := by
      have ha : raw10250step2 = (fun i j => raw10250step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10250step2 raw10250step1; decide +kernel
      have hl : raw10250step2Labels = raw10250step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10250step1 raw10250step1Labels permutation10 permutation2
    _ = mixedMoment B node4617 node4617Labels := by rfl

theorem canonical10254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10254 raw10254Labels = mixedMoment B node4626 node4626Labels := by
  calc
    mixedMoment B raw10254 raw10254Labels = mixedMoment B raw10254step0 raw10254step0Labels := by
      have hz : ∀ j, raw10254 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10254step0 = (fun i j => raw10254 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10254step0 raw10254; decide +kernel
      have hl : raw10254step0Labels = raw10254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10254 raw10254Labels permutation434 hz
    mixedMoment B raw10254step0 raw10254step0Labels = mixedMoment B raw10254step1 raw10254step1Labels := by
      have hz : ∀ j, raw10254step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10254step1 = (fun i j => raw10254step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10254step1 raw10254step0; decide +kernel
      have hl : raw10254step1Labels = raw10254step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10254step0 raw10254step0Labels permutation80 hz
    mixedMoment B raw10254step1 raw10254step1Labels = mixedMoment B raw10254step2 raw10254step2Labels := by
      have hz : ∀ j, raw10254step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10254step2 = (fun i j => raw10254step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10254step2 raw10254step1; decide +kernel
      have hl : raw10254step2Labels = raw10254step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10254step1 raw10254step1Labels permutation14 hz
    _ = mixedMoment B node4626 node4626Labels := by rfl

theorem canonical10259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10259 raw10259Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw10259 raw10259Labels = mixedMoment B raw10259step0 raw10259step0Labels := by
      have hz : ∀ j, raw10259 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10259step0 = (fun i j => raw10259 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10259step0 raw10259; decide +kernel
      have hl : raw10259step0Labels = raw10259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10259 raw10259Labels permutation434 hz
    mixedMoment B raw10259step0 raw10259step0Labels = mixedMoment B raw10259step1 raw10259step1Labels := by
      have hz : ∀ j, raw10259step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10259step1 = (fun i j => raw10259step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10259step1 raw10259step0; decide +kernel
      have hl : raw10259step1Labels = raw10259step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10259step0 raw10259step0Labels permutation80 hz
    mixedMoment B raw10259step1 raw10259step1Labels = mixedMoment B raw10259step2 raw10259step2Labels := by
      have hz : ∀ j, raw10259step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10259step2 = (fun i j => raw10259step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10259step2 raw10259step1; decide +kernel
      have hl : raw10259step2Labels = raw10259step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10259step1 raw10259step1Labels permutation14 hz
    mixedMoment B raw10259step2 raw10259step2Labels = mixedMoment B raw10259step3 raw10259step3Labels := by
      have ha : raw10259step3 = (fun i j => raw10259step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10259step3 raw10259step2; decide +kernel
      have hl : raw10259step3Labels = raw10259step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10259step2 raw10259step2Labels permutation7 permutation2
    mixedMoment B raw10259step3 raw10259step3Labels = mixedMoment B raw10259step4 raw10259step4Labels := by
      have ha : raw10259step4 = -raw10259step3 := by apply Matrix.ext; change ∀ i j, raw10259step4 i j = -(raw10259step3 i j); unfold raw10259step4 raw10259step3; decide +kernel
      have hl : raw10259step4Labels = raw10259step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4897 node4897Labels := by rfl

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

theorem canonical1278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1278 raw1278Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw1278 raw1278Labels = mixedMoment B raw1278step0 raw1278step0Labels := by
      have ha : raw1278step0 = (fun i j => raw1278 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1278step0 raw1278; decide +kernel
      have hl : raw1278step0Labels = raw1278Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1278 raw1278Labels permutation2 permutation4
    mixedMoment B raw1278step0 raw1278step0Labels = mixedMoment B raw1278step1 raw1278step1Labels := by
      have ha : raw1278step1 = raw1278step0 := by apply Matrix.ext; unfold raw1278step1 raw1278step0; decide +kernel
      have hl : raw1278step0Labels = labelEmbedding7 ∘ raw1278step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1278step0 raw1278step0Labels raw1278step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical1279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1279 raw1279Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw1279 raw1279Labels = mixedMoment B raw1279step0 raw1279step0Labels := by
      have ha : raw1279step0 = (fun i j => raw1279 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1279step0 raw1279; decide +kernel
      have hl : raw1279step0Labels = raw1279Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1279 raw1279Labels permutation2 permutation4
    _ = mixedMoment B node1051 node1051Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4468 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4468 node4468Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1051 node1051Labels + mixedMoment B node1752 node1752Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1278 singletonSmall4468
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4468) = raw1278Labels := by decide +kernel
  rw [hl, canonical1278 B hB] at h
  have hc0 : mixedMoment B raw1278 (Fin.cases (0 : Fin 2) singletonSmall4468) =
      mixedMoment B node1051 node1051Labels := by
    have ha : raw1278 = raw1279 := by apply Matrix.ext; unfold raw1278 raw1279; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4468 = raw1279Labels := by decide +kernel
    rw [ha, hj, canonical1279 B hB]
  have hc1 : mixedMoment B raw1278 (Fin.cases (1 : Fin 2) singletonSmall4468) =
      mixedMoment B node1752 node1752Labels := by
    have ha : raw1278 = raw1280 := by apply Matrix.ext; unfold raw1278 raw1280; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4468 = raw1280Labels := by decide +kernel
    rw [ha, hj, canonical1280 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4605 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4605 node4605Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1239 node1239Labels + mixedMoment B node2226 node2226Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1428 singletonSmall4605
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4605) = raw1428Labels := by decide +kernel
  rw [hl, canonical1428 B hB] at h
  have hc0 : mixedMoment B raw1428 (Fin.cases (0 : Fin 2) singletonSmall4605) =
      mixedMoment B node1239 node1239Labels := by
    have ha : raw1428 = raw1429 := by apply Matrix.ext; unfold raw1428 raw1429; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4605 = raw1429Labels := by decide +kernel
    rw [ha, hj, canonical1429 B hB]
  have hc1 : mixedMoment B raw1428 (Fin.cases (1 : Fin 2) singletonSmall4605) =
      mixedMoment B node2226 node2226Labels := by
    have ha : raw1428 = raw1430 := by apply Matrix.ext; unfold raw1428 raw1430; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4605 = raw1430Labels := by decide +kernel
    rw [ha, hj, canonical1430 B hB]
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

theorem singleton4868 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4868 node4868Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2109 node2109Labels + mixedMoment B node2261 node2261Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1797 singletonSmall4868
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4868) = raw1797Labels := by decide +kernel
  rw [hl, canonical1797 B hB] at h
  have hc0 : mixedMoment B raw1797 (Fin.cases (0 : Fin 2) singletonSmall4868) =
      mixedMoment B node2109 node2109Labels := by
    have ha : raw1797 = raw1798 := by apply Matrix.ext; unfold raw1797 raw1798; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4868 = raw1798Labels := by decide +kernel
    rw [ha, hj, canonical1798 B hB]
  have hc1 : mixedMoment B raw1797 (Fin.cases (1 : Fin 2) singletonSmall4868) =
      mixedMoment B node2261 node2261Labels := by
    have ha : raw1797 = raw1799 := by apply Matrix.ext; unfold raw1797 raw1799; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4868 = raw1799Labels := by decide +kernel
    rw [ha, hj, canonical1799 B hB]
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

theorem singleton5305 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5305 node5305Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2783 node2783Labels + mixedMoment B node2783 node2783Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2319 singletonSmall5305
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5305) = raw2319Labels := by decide +kernel
  rw [hl, canonical2319 B hB] at h
  have hc0 : mixedMoment B raw2319 (Fin.cases (0 : Fin 2) singletonSmall5305) =
      mixedMoment B node2783 node2783Labels := by
    have ha : raw2319 = raw2320 := by apply Matrix.ext; unfold raw2319 raw2320; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5305 = raw2320Labels := by decide +kernel
    rw [ha, hj, canonical2320 B hB]
  have hc1 : mixedMoment B raw2319 (Fin.cases (1 : Fin 2) singletonSmall5305) =
      mixedMoment B node2783 node2783Labels := by
    have ha : raw2319 = raw2321 := by apply Matrix.ext; unfold raw2319 raw2321; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5305 = raw2321Labels := by decide +kernel
    rw [ha, hj, canonical2321 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound1051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1051 node1051Labels = Sparse.eval nodeValue1051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1051) = mixedMoment B node1051 node1051Labels := rfl
  simpa [nodeValue1051, Sparse.eval] using hc.symm

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

theorem sound1178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1178 node1178Labels = Sparse.eval nodeValue1178 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1178) = mixedMoment B node1178 node1178Labels := rfl
  simpa [nodeValue1178, Sparse.eval] using hc.symm

theorem sound1179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1179 node1179Labels = Sparse.eval nodeValue1179 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1179) = mixedMoment B node1179 node1179Labels := rfl
  simpa [nodeValue1179, Sparse.eval] using hc.symm

theorem sound1181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1181 node1181Labels = Sparse.eval nodeValue1181 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1181) = mixedMoment B node1181 node1181Labels := rfl
  simpa [nodeValue1181, Sparse.eval] using hc.symm

theorem sound1182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1182 node1182Labels = Sparse.eval nodeValue1182 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1182) = mixedMoment B node1182 node1182Labels := rfl
  simpa [nodeValue1182, Sparse.eval] using hc.symm

theorem sound1188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1188 node1188Labels = Sparse.eval nodeValue1188 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1188) = mixedMoment B node1188 node1188Labels := rfl
  simpa [nodeValue1188, Sparse.eval] using hc.symm

theorem sound1194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1194 node1194Labels = Sparse.eval nodeValue1194 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1194) = mixedMoment B node1194 node1194Labels := rfl
  simpa [nodeValue1194, Sparse.eval] using hc.symm

theorem sound1195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1195 node1195Labels = Sparse.eval nodeValue1195 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1195) = mixedMoment B node1195 node1195Labels := rfl
  simpa [nodeValue1195, Sparse.eval] using hc.symm

theorem sound1196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1196 node1196Labels = Sparse.eval nodeValue1196 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1196) = mixedMoment B node1196 node1196Labels := rfl
  simpa [nodeValue1196, Sparse.eval] using hc.symm

theorem sound1200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1200 node1200Labels = Sparse.eval nodeValue1200 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1200) = mixedMoment B node1200 node1200Labels := rfl
  simpa [nodeValue1200, Sparse.eval] using hc.symm

theorem sound1210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1210 node1210Labels = Sparse.eval nodeValue1210 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1210) = mixedMoment B node1210 node1210Labels := rfl
  simpa [nodeValue1210, Sparse.eval] using hc.symm

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

theorem sound1239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1239 node1239Labels = Sparse.eval nodeValue1239 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1239) = mixedMoment B node1239 node1239Labels := rfl
  simpa [nodeValue1239, Sparse.eval] using hc.symm

theorem sound1257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1257 node1257Labels = Sparse.eval nodeValue1257 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1257) = mixedMoment B node1257 node1257Labels := rfl
  simpa [nodeValue1257, Sparse.eval] using hc.symm

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

theorem sound1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1725 node1725Labels = Sparse.eval nodeValue1725 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1725) = mixedMoment B node1725 node1725Labels := rfl
  simpa [nodeValue1725, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1730 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1730 node1730Labels = 0 := by
  exact mixedMoment_order_one B hB node1730 node1730Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1754 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1754 node1754Labels = 0 := by
  exact mixedMoment_order_one B hB node1754 node1754Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1730 node1730Labels = Sparse.eval nodeValue1730 (mixedVector B) := by
  simpa only [nodeValue1730, Sparse.eval_nil] using zero1730 B _hB _hF

theorem sound1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1750 node1750Labels = Sparse.eval nodeValue1750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1750) = mixedMoment B node1750 node1750Labels := rfl
  simpa [nodeValue1750, Sparse.eval] using hc.symm

theorem sound1752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1752 node1752Labels = Sparse.eval nodeValue1752 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1752) = mixedMoment B node1752 node1752Labels := rfl
  simpa [nodeValue1752, Sparse.eval] using hc.symm

theorem sound1754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1754 node1754Labels = Sparse.eval nodeValue1754 (mixedVector B) := by
  simpa only [nodeValue1754, Sparse.eval_nil] using zero1754 B _hB _hF

theorem sound1756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1756 node1756Labels = Sparse.eval nodeValue1756 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1756) = mixedMoment B node1756 node1756Labels := rfl
  simpa [nodeValue1756, Sparse.eval] using hc.symm

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

theorem sound1987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1987 node1987Labels = Sparse.eval nodeValue1987 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1987) = mixedMoment B node1987 node1987Labels := rfl
  simpa [nodeValue1987, Sparse.eval] using hc.symm

theorem sound1991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1991 node1991Labels = Sparse.eval nodeValue1991 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1991) = mixedMoment B node1991 node1991Labels := rfl
  simpa [nodeValue1991, Sparse.eval] using hc.symm

theorem sound2003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2003 node2003Labels = Sparse.eval nodeValue2003 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2003) = mixedMoment B node2003 node2003Labels := rfl
  simpa [nodeValue2003, Sparse.eval] using hc.symm

theorem sound2008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2008 node2008Labels = Sparse.eval nodeValue2008 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2008) = mixedMoment B node2008 node2008Labels := rfl
  simpa [nodeValue2008, Sparse.eval] using hc.symm

theorem sound2032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2032 node2032Labels = Sparse.eval nodeValue2032 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2032) = mixedMoment B node2032 node2032Labels := rfl
  simpa [nodeValue2032, Sparse.eval] using hc.symm

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

theorem sound2109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2109 node2109Labels = Sparse.eval nodeValue2109 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2109) = mixedMoment B node2109 node2109Labels := rfl
  simpa [nodeValue2109, Sparse.eval] using hc.symm

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

theorem sound2193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2193 node2193Labels = Sparse.eval nodeValue2193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2193) = mixedMoment B node2193 node2193Labels := rfl
  simpa [nodeValue2193, Sparse.eval] using hc.symm

theorem sound2218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2218 node2218Labels = Sparse.eval nodeValue2218 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2218) = mixedMoment B node2218 node2218Labels := rfl
  simpa [nodeValue2218, Sparse.eval] using hc.symm

theorem sound2226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2226 node2226Labels = Sparse.eval nodeValue2226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2226) = mixedMoment B node2226 node2226Labels := rfl
  simpa [nodeValue2226, Sparse.eval] using hc.symm

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

theorem sound2261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2261 node2261Labels = Sparse.eval nodeValue2261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2261) = mixedMoment B node2261 node2261Labels := rfl
  simpa [nodeValue2261, Sparse.eval] using hc.symm

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

theorem sound2449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2449 node2449Labels = Sparse.eval nodeValue2449 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2449) = mixedMoment B node2449 node2449Labels := rfl
  simpa [nodeValue2449, Sparse.eval] using hc.symm

theorem sound2469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2469 node2469Labels = Sparse.eval nodeValue2469 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2469) = mixedMoment B node2469 node2469Labels := rfl
  simpa [nodeValue2469, Sparse.eval] using hc.symm

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

theorem sound2670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2670 node2670Labels = Sparse.eval nodeValue2670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2670) = mixedMoment B node2670 node2670Labels := rfl
  simpa [nodeValue2670, Sparse.eval] using hc.symm

theorem sound2672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2672 node2672Labels = Sparse.eval nodeValue2672 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2672) = mixedMoment B node2672 node2672Labels := rfl
  simpa [nodeValue2672, Sparse.eval] using hc.symm

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

theorem zero2691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2691 node2691Labels = 0 := by
  exact mixedMoment_alpha B hF node2691 node2691Labels 1 permutation212
    (by decide +kernel)

theorem zero2693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2693 node2693Labels = 0 := by
  exact mixedMoment_alpha B hF node2693 node2693Labels 1 permutation213
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

theorem sound2691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2691 node2691Labels = Sparse.eval nodeValue2691 (mixedVector B) := by
  simpa only [nodeValue2691, Sparse.eval_nil] using zero2691 B _hB _hF

theorem sound2693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2693 node2693Labels = Sparse.eval nodeValue2693 (mixedVector B) := by
  simpa only [nodeValue2693, Sparse.eval_nil] using zero2693 B _hB _hF

theorem sound2694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2694 node2694Labels = Sparse.eval nodeValue2694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2694) = mixedMoment B node2694 node2694Labels := rfl
  simpa [nodeValue2694, Sparse.eval] using hc.symm

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

theorem sound2783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2783 node2783Labels = Sparse.eval nodeValue2783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2783) = mixedMoment B node2783 node2783Labels := rfl
  simpa [nodeValue2783, Sparse.eval] using hc.symm

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

theorem sound3300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3300 node3300Labels = Sparse.eval nodeValue3300 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3300) = mixedMoment B node3300 node3300Labels := rfl
  simpa [nodeValue3300, Sparse.eval] using hc.symm

theorem sound3310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3310 node3310Labels = Sparse.eval nodeValue3310 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3310) = mixedMoment B node3310 node3310Labels := rfl
  simpa [nodeValue3310, Sparse.eval] using hc.symm

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

theorem sound4070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4070 node4070Labels = Sparse.eval nodeValue4070 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4070) = mixedMoment B node4070 node4070Labels := rfl
  simpa [nodeValue4070, Sparse.eval] using hc.symm

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

theorem sound4082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4082 node4082Labels = Sparse.eval nodeValue4082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4082) = mixedMoment B node4082 node4082Labels := rfl
  simpa [nodeValue4082, Sparse.eval] using hc.symm

theorem sound4088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4088 node4088Labels = Sparse.eval nodeValue4088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4088) = mixedMoment B node4088 node4088Labels := rfl
  simpa [nodeValue4088, Sparse.eval] using hc.symm

theorem sound4090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4090 node4090Labels = Sparse.eval nodeValue4090 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4090) = mixedMoment B node4090 node4090Labels := rfl
  simpa [nodeValue4090, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4184 node4184Labels = Sparse.eval nodeValue4184 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4184) = mixedMoment B node4184 node4184Labels := rfl
  simpa [nodeValue4184, Sparse.eval] using hc.symm

theorem sound4189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4189 node4189Labels = Sparse.eval nodeValue4189 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4189) = mixedMoment B node4189 node4189Labels := rfl
  simpa [nodeValue4189, Sparse.eval] using hc.symm

theorem sound4193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4193 node4193Labels = Sparse.eval nodeValue4193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4193) = mixedMoment B node4193 node4193Labels := rfl
  simpa [nodeValue4193, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4370 node4370Labels = Sparse.eval nodeValue4370 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4370) = mixedMoment B node4370 node4370Labels := rfl
  simpa [nodeValue4370, Sparse.eval] using hc.symm

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

theorem sound4468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4468 node4468Labels = Sparse.eval nodeValue4468 (mixedVector B) := by
  have h := singleton4468 B _hB
  rw [sound1051 B _hB _hF, sound1752 B _hB _hF] at h
  norm_num [nodeValue4468, nodeValue1051, nodeValue1752, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4552 node4552Labels = Sparse.eval nodeValue4552 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4552) = mixedMoment B node4552 node4552Labels := rfl
  simpa [nodeValue4552, Sparse.eval] using hc.symm

theorem sound4560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4560 node4560Labels = Sparse.eval nodeValue4560 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4560) = mixedMoment B node4560 node4560Labels := rfl
  simpa [nodeValue4560, Sparse.eval] using hc.symm

theorem sound4605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4605 node4605Labels = Sparse.eval nodeValue4605 (mixedVector B) := by
  have h := singleton4605 B _hB
  rw [sound1239 B _hB _hF, sound2226 B _hB _hF] at h
  norm_num [nodeValue4605, nodeValue1239, nodeValue2226, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4617 node4617Labels = Sparse.eval nodeValue4617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4617) = mixedMoment B node4617 node4617Labels := rfl
  simpa [nodeValue4617, Sparse.eval] using hc.symm

theorem sound4626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4626 node4626Labels = Sparse.eval nodeValue4626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4626) = mixedMoment B node4626 node4626Labels := rfl
  simpa [nodeValue4626, Sparse.eval] using hc.symm

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

theorem zero4897 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4897 node4897Labels = 0 := by
  exact mixedMoment_order_one B hB node4897 node4897Labels 1
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

theorem sound4868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4868 node4868Labels = Sparse.eval nodeValue4868 (mixedVector B) := by
  have h := singleton4868 B _hB
  rw [sound2109 B _hB _hF, sound2261 B _hB _hF] at h
  norm_num [nodeValue4868, nodeValue2109, nodeValue2261, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4897 node4897Labels = Sparse.eval nodeValue4897 (mixedVector B) := by
  simpa only [nodeValue4897, Sparse.eval_nil] using zero4897 B _hB _hF

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

theorem sound5305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5305 node5305Labels = Sparse.eval nodeValue5305 (mixedVector B) := by
  have h := singleton5305 B _hB
  rw [sound2783 B _hB _hF] at h
  norm_num [nodeValue5305, nodeValue2783, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources39
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1258 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1258 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1258 + difference 0 5) (sourceB1258 + difference 5 0) sourceC1258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA1258 + difference 0 5) (sourceB1258 + difference 5 0) sourceC1258) = raw20320 := by
      apply Matrix.ext; unfold tripleCharges sourceA1258 sourceB1258 sourceC1258 difference raw20320; decide +kernel
    rw [ha]
    exact (canonical20320 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1258 + difference 1 5) (sourceB1258 + difference 5 1) sourceC1258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1188) := by
    have ha : (tripleCharges (sourceA1258 + difference 1 5) (sourceB1258 + difference 5 1) sourceC1258) = raw20322 := by
      apply Matrix.ext; unfold tripleCharges sourceA1258 sourceB1258 sourceC1258 difference raw20322; decide +kernel
    rw [ha]
    exact (canonical20322 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1258 + difference 2 5) (sourceB1258 + difference 5 2) sourceC1258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1178) := by
    have ha : (tripleCharges (sourceA1258 + difference 2 5) (sourceB1258 + difference 5 2) sourceC1258) = raw20323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1258 sourceB1258 sourceC1258 difference raw20323; decide +kernel
    rw [ha]
    exact (canonical20323 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1258 + difference 3 5) (sourceB1258 + difference 5 3) sourceC1258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1257) := by
    have ha : (tripleCharges (sourceA1258 + difference 3 5) (sourceB1258 + difference 5 3) sourceC1258) = raw20324 := by
      apply Matrix.ext; unfold tripleCharges sourceA1258 sourceB1258 sourceC1258 difference raw20324; decide +kernel
    rw [ha]
    exact (canonical20324 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1258 + difference 4 5) (sourceB1258 + difference 5 4) sourceC1258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1182) := by
    have ha : (tripleCharges (sourceA1258 + difference 4 5) (sourceB1258 + difference 5 4) sourceC1258) = raw20325 := by
      apply Matrix.ext; unfold tripleCharges sourceA1258 sourceB1258 sourceC1258 difference raw20325; decide +kernel
    rw [ha]
    exact (canonical20325 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1258 + difference 5 5) (sourceB1258 + difference 5 5) sourceC1258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1181) := by
    have ha : (tripleCharges (sourceA1258 + difference 5 5) (sourceB1258 + difference 5 5) sourceC1258) = raw20315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1258 sourceB1258 sourceC1258 difference raw20315; decide +kernel
    rw [ha]
    exact (canonical20315 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1258 + sourceB1258) sourceC1258) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1258 + sourceB1258) sourceC1258) = raw20321 := by
      apply Matrix.ext; unfold doubleCharges sourceA1258 sourceB1258 sourceC1258 raw20321; decide +kernel
    rw [ha]
    exact (canonical20321 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1258 sourceB1258 sourceC1258
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1258, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1259 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1259 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1259 + difference 0 0) (sourceB1259 + difference 0 0) sourceC1259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1179) := by
    have ha : (tripleCharges (sourceA1259 + difference 0 0) (sourceB1259 + difference 0 0) sourceC1259) = raw20326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1259 sourceB1259 sourceC1259 difference raw20326; decide +kernel
    rw [ha]
    exact (canonical20326 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1259 + difference 0 1) (sourceB1259 + difference 1 0) sourceC1259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2032) := by
    have ha : (tripleCharges (sourceA1259 + difference 0 1) (sourceB1259 + difference 1 0) sourceC1259) = raw20327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1259 sourceB1259 sourceC1259 difference raw20327; decide +kernel
    rw [ha]
    exact (canonical20327 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1259 + difference 0 2) (sourceB1259 + difference 2 0) sourceC1259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1991) := by
    have ha : (tripleCharges (sourceA1259 + difference 0 2) (sourceB1259 + difference 2 0) sourceC1259) = raw20328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1259 sourceB1259 sourceC1259 difference raw20328; decide +kernel
    rw [ha]
    exact (canonical20328 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1259 + difference 0 3) (sourceB1259 + difference 3 0) sourceC1259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2003) := by
    have ha : (tripleCharges (sourceA1259 + difference 0 3) (sourceB1259 + difference 3 0) sourceC1259) = raw20329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1259 sourceB1259 sourceC1259 difference raw20329; decide +kernel
    rw [ha]
    exact (canonical20329 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1259 + difference 0 4) (sourceB1259 + difference 4 0) sourceC1259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1259 + difference 0 4) (sourceB1259 + difference 4 0) sourceC1259) = raw20330 := by
      apply Matrix.ext; unfold tripleCharges sourceA1259 sourceB1259 sourceC1259 difference raw20330; decide +kernel
    rw [ha]
    exact (canonical20330 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1259 + difference 0 5) (sourceB1259 + difference 5 0) sourceC1259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA1259 + difference 0 5) (sourceB1259 + difference 5 0) sourceC1259) = raw20331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1259 sourceB1259 sourceC1259 difference raw20331; decide +kernel
    rw [ha]
    exact (canonical20331 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1259 + sourceB1259) sourceC1259) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1259 + sourceB1259) sourceC1259) = raw20332 := by
      apply Matrix.ext; unfold doubleCharges sourceA1259 sourceB1259 sourceC1259 raw20332; decide +kernel
    rw [ha]
    exact (canonical20332 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1259 sourceB1259 sourceC1259
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1259, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1260 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1260 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1260 + difference 0 0) (sourceB1260 + difference 0 0) sourceC1260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1195) := by
    have ha : (tripleCharges (sourceA1260 + difference 0 0) (sourceB1260 + difference 0 0) sourceC1260) = raw20333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1260 sourceB1260 sourceC1260 difference raw20333; decide +kernel
    rw [ha]
    exact (canonical20333 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1260 + difference 0 1) (sourceB1260 + difference 1 0) sourceC1260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2469) := by
    have ha : (tripleCharges (sourceA1260 + difference 0 1) (sourceB1260 + difference 1 0) sourceC1260) = raw20334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1260 sourceB1260 sourceC1260 difference raw20334; decide +kernel
    rw [ha]
    exact (canonical20334 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1260 + difference 0 2) (sourceB1260 + difference 2 0) sourceC1260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2449) := by
    have ha : (tripleCharges (sourceA1260 + difference 0 2) (sourceB1260 + difference 2 0) sourceC1260) = raw20335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1260 sourceB1260 sourceC1260 difference raw20335; decide +kernel
    rw [ha]
    exact (canonical20335 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1260 + difference 0 3) (sourceB1260 + difference 3 0) sourceC1260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2449) := by
    have ha : (tripleCharges (sourceA1260 + difference 0 3) (sourceB1260 + difference 3 0) sourceC1260) = raw20336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1260 sourceB1260 sourceC1260 difference raw20336; decide +kernel
    rw [ha]
    exact (canonical20336 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1260 + difference 0 4) (sourceB1260 + difference 4 0) sourceC1260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2691) := by
    have ha : (tripleCharges (sourceA1260 + difference 0 4) (sourceB1260 + difference 4 0) sourceC1260) = raw20337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1260 sourceB1260 sourceC1260 difference raw20337; decide +kernel
    rw [ha]
    exact (canonical20337 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1260 + difference 0 5) (sourceB1260 + difference 5 0) sourceC1260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA1260 + difference 0 5) (sourceB1260 + difference 5 0) sourceC1260) = raw20338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1260 sourceB1260 sourceC1260 difference raw20338; decide +kernel
    rw [ha]
    exact (canonical20338 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1260 + sourceB1260) sourceC1260) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA1260 + sourceB1260) sourceC1260) = raw20339 := by
      apply Matrix.ext; unfold doubleCharges sourceA1260 sourceB1260 sourceC1260 raw20339; decide +kernel
    rw [ha]
    exact (canonical20339 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1260 sourceB1260 sourceC1260
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1260, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1261 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1261 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1261 + difference 0 5) (sourceB1261 + difference 5 0) sourceC1261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA1261 + difference 0 5) (sourceB1261 + difference 5 0) sourceC1261) = raw20338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1261 sourceB1261 sourceC1261 difference raw20338; decide +kernel
    rw [ha]
    exact (canonical20338 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1261 + difference 1 5) (sourceB1261 + difference 5 1) sourceC1261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1200) := by
    have ha : (tripleCharges (sourceA1261 + difference 1 5) (sourceB1261 + difference 5 1) sourceC1261) = raw20340 := by
      apply Matrix.ext; unfold tripleCharges sourceA1261 sourceB1261 sourceC1261 difference raw20340; decide +kernel
    rw [ha]
    exact (canonical20340 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1261 + difference 2 5) (sourceB1261 + difference 5 2) sourceC1261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1210) := by
    have ha : (tripleCharges (sourceA1261 + difference 2 5) (sourceB1261 + difference 5 2) sourceC1261) = raw20341 := by
      apply Matrix.ext; unfold tripleCharges sourceA1261 sourceB1261 sourceC1261 difference raw20341; decide +kernel
    rw [ha]
    exact (canonical20341 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1261 + difference 3 5) (sourceB1261 + difference 5 3) sourceC1261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1210) := by
    have ha : (tripleCharges (sourceA1261 + difference 3 5) (sourceB1261 + difference 5 3) sourceC1261) = raw20342 := by
      apply Matrix.ext; unfold tripleCharges sourceA1261 sourceB1261 sourceC1261 difference raw20342; decide +kernel
    rw [ha]
    exact (canonical20342 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1261 + difference 4 5) (sourceB1261 + difference 5 4) sourceC1261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1196) := by
    have ha : (tripleCharges (sourceA1261 + difference 4 5) (sourceB1261 + difference 5 4) sourceC1261) = raw20343 := by
      apply Matrix.ext; unfold tripleCharges sourceA1261 sourceB1261 sourceC1261 difference raw20343; decide +kernel
    rw [ha]
    exact (canonical20343 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1261 + difference 5 5) (sourceB1261 + difference 5 5) sourceC1261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1195) := by
    have ha : (tripleCharges (sourceA1261 + difference 5 5) (sourceB1261 + difference 5 5) sourceC1261) = raw20333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1261 sourceB1261 sourceC1261 difference raw20333; decide +kernel
    rw [ha]
    exact (canonical20333 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1261 + sourceB1261) sourceC1261) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA1261 + sourceB1261) sourceC1261) = raw20339 := by
      apply Matrix.ext; unfold doubleCharges sourceA1261 sourceB1261 sourceC1261 raw20339; decide +kernel
    rw [ha]
    exact (canonical20339 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1261 sourceB1261 sourceC1261
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1261, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1262 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1262 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1262 + difference 0 0) (sourceB1262 + difference 0 0) sourceC1262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1194) := by
    have ha : (tripleCharges (sourceA1262 + difference 0 0) (sourceB1262 + difference 0 0) sourceC1262) = raw20344 := by
      apply Matrix.ext; unfold tripleCharges sourceA1262 sourceB1262 sourceC1262 difference raw20344; decide +kernel
    rw [ha]
    exact (canonical20344 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1262 + difference 0 1) (sourceB1262 + difference 1 0) sourceC1262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2008) := by
    have ha : (tripleCharges (sourceA1262 + difference 0 1) (sourceB1262 + difference 1 0) sourceC1262) = raw20345 := by
      apply Matrix.ext; unfold tripleCharges sourceA1262 sourceB1262 sourceC1262 difference raw20345; decide +kernel
    rw [ha]
    exact (canonical20345 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1262 + difference 0 2) (sourceB1262 + difference 2 0) sourceC1262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1987) := by
    have ha : (tripleCharges (sourceA1262 + difference 0 2) (sourceB1262 + difference 2 0) sourceC1262) = raw20346 := by
      apply Matrix.ext; unfold tripleCharges sourceA1262 sourceB1262 sourceC1262 difference raw20346; decide +kernel
    rw [ha]
    exact (canonical20346 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1262 + difference 0 3) (sourceB1262 + difference 3 0) sourceC1262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1987) := by
    have ha : (tripleCharges (sourceA1262 + difference 0 3) (sourceB1262 + difference 3 0) sourceC1262) = raw20347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1262 sourceB1262 sourceC1262 difference raw20347; decide +kernel
    rw [ha]
    exact (canonical20347 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1262 + difference 0 4) (sourceB1262 + difference 4 0) sourceC1262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA1262 + difference 0 4) (sourceB1262 + difference 4 0) sourceC1262) = raw20348 := by
      apply Matrix.ext; unfold tripleCharges sourceA1262 sourceB1262 sourceC1262 difference raw20348; decide +kernel
    rw [ha]
    exact (canonical20348 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1262 + difference 0 5) (sourceB1262 + difference 5 0) sourceC1262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2693) := by
    have ha : (tripleCharges (sourceA1262 + difference 0 5) (sourceB1262 + difference 5 0) sourceC1262) = raw20349 := by
      apply Matrix.ext; unfold tripleCharges sourceA1262 sourceB1262 sourceC1262 difference raw20349; decide +kernel
    rw [ha]
    exact (canonical20349 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1262 + sourceB1262) sourceC1262) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1262 + sourceB1262) sourceC1262) = raw20350 := by
      apply Matrix.ext; unfold doubleCharges sourceA1262 sourceB1262 sourceC1262 raw20350; decide +kernel
    rw [ha]
    exact (canonical20350 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1262 sourceB1262 sourceC1262
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1262, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1269 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1269 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1269 + difference 0 0) (sourceB1269 + difference 0 0) sourceC1269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3310) := by
    have ha : (tripleCharges (sourceA1269 + difference 0 0) (sourceB1269 + difference 0 0) sourceC1269) = raw20303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1269 sourceB1269 sourceC1269 difference raw20303; decide +kernel
    rw [ha]
    exact (canonical20303 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1269 + difference 0 1) (sourceB1269 + difference 1 0) sourceC1269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1269 + difference 0 1) (sourceB1269 + difference 1 0) sourceC1269) = raw20298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1269 sourceB1269 sourceC1269 difference raw20298; decide +kernel
    rw [ha]
    exact (canonical20298 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1269 + difference 0 2) (sourceB1269 + difference 2 0) sourceC1269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1269 + difference 0 2) (sourceB1269 + difference 2 0) sourceC1269) = raw20474 := by
      apply Matrix.ext; unfold tripleCharges sourceA1269 sourceB1269 sourceC1269 difference raw20474; decide +kernel
    rw [ha]
    exact (canonical20474 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1269 + difference 0 3) (sourceB1269 + difference 3 0) sourceC1269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1269 + difference 0 3) (sourceB1269 + difference 3 0) sourceC1269) = raw20475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1269 sourceB1269 sourceC1269 difference raw20475; decide +kernel
    rw [ha]
    exact (canonical20475 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1269 + difference 0 4) (sourceB1269 + difference 4 0) sourceC1269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1756) := by
    have ha : (tripleCharges (sourceA1269 + difference 0 4) (sourceB1269 + difference 4 0) sourceC1269) = raw20476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1269 sourceB1269 sourceC1269 difference raw20476; decide +kernel
    rw [ha]
    exact (canonical20476 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1269 + difference 0 5) (sourceB1269 + difference 5 0) sourceC1269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1754) := by
    have ha : (tripleCharges (sourceA1269 + difference 0 5) (sourceB1269 + difference 5 0) sourceC1269) = raw20477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1269 sourceB1269 sourceC1269 difference raw20477; decide +kernel
    rw [ha]
    exact (canonical20477 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1269 + sourceB1269) sourceC1269) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1269 + sourceB1269) sourceC1269) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1269 sourceB1269 sourceC1269 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1269 sourceB1269 sourceC1269
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1269, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1270 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1270 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1270 + difference 0 0) (sourceB1270 + difference 0 0) sourceC1270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3310) := by
    have ha : (tripleCharges (sourceA1270 + difference 0 0) (sourceB1270 + difference 0 0) sourceC1270) = raw20303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1270 sourceB1270 sourceC1270 difference raw20303; decide +kernel
    rw [ha]
    exact (canonical20303 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1270 + difference 1 0) (sourceB1270 + difference 0 1) sourceC1270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1270 + difference 1 0) (sourceB1270 + difference 0 1) sourceC1270) = raw20478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1270 sourceB1270 sourceC1270 difference raw20478; decide +kernel
    rw [ha]
    exact (canonical20478 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1270 + difference 2 0) (sourceB1270 + difference 0 2) sourceC1270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1270 + difference 2 0) (sourceB1270 + difference 0 2) sourceC1270) = raw20213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1270 sourceB1270 sourceC1270 difference raw20213; decide +kernel
    rw [ha]
    exact (canonical20213 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1270 + difference 3 0) (sourceB1270 + difference 0 3) sourceC1270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1270 + difference 3 0) (sourceB1270 + difference 0 3) sourceC1270) = raw20161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1270 sourceB1270 sourceC1270 difference raw20161; decide +kernel
    rw [ha]
    exact (canonical20161 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1270 + difference 4 0) (sourceB1270 + difference 0 4) sourceC1270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1754) := by
    have ha : (tripleCharges (sourceA1270 + difference 4 0) (sourceB1270 + difference 0 4) sourceC1270) = raw20479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1270 sourceB1270 sourceC1270 difference raw20479; decide +kernel
    rw [ha]
    exact (canonical20479 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1270 + difference 5 0) (sourceB1270 + difference 0 5) sourceC1270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1270 + difference 5 0) (sourceB1270 + difference 0 5) sourceC1270) = raw20480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1270 sourceB1270 sourceC1270 difference raw20480; decide +kernel
    rw [ha]
    exact (canonical20480 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1270 + sourceB1270) sourceC1270) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1270 + sourceB1270) sourceC1270) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1270 sourceB1270 sourceC1270 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1270 sourceB1270 sourceC1270
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1270, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1271 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1271 + difference 4 0) (sourceB1271 + difference 0 4) sourceC1271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1754) := by
    have ha : (tripleCharges (sourceA1271 + difference 4 0) (sourceB1271 + difference 0 4) sourceC1271) = raw20479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1271 sourceB1271 sourceC1271 difference raw20479; decide +kernel
    rw [ha]
    exact (canonical20479 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1271 + difference 4 1) (sourceB1271 + difference 1 4) sourceC1271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1271 + difference 4 1) (sourceB1271 + difference 1 4) sourceC1271) = raw20268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1271 sourceB1271 sourceC1271 difference raw20268; decide +kernel
    rw [ha]
    exact (canonical20268 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1271 + difference 4 2) (sourceB1271 + difference 2 4) sourceC1271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1271 + difference 4 2) (sourceB1271 + difference 2 4) sourceC1271) = raw20481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1271 sourceB1271 sourceC1271 difference raw20481; decide +kernel
    rw [ha]
    exact (canonical20481 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1271 + difference 4 3) (sourceB1271 + difference 3 4) sourceC1271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1271 + difference 4 3) (sourceB1271 + difference 3 4) sourceC1271) = raw20482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1271 sourceB1271 sourceC1271 difference raw20482; decide +kernel
    rw [ha]
    exact (canonical20482 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1271 + difference 4 4) (sourceB1271 + difference 4 4) sourceC1271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3310) := by
    have ha : (tripleCharges (sourceA1271 + difference 4 4) (sourceB1271 + difference 4 4) sourceC1271) = raw20303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1271 sourceB1271 sourceC1271 difference raw20303; decide +kernel
    rw [ha]
    exact (canonical20303 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1271 + difference 4 5) (sourceB1271 + difference 5 4) sourceC1271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3310) := by
    have ha : (tripleCharges (sourceA1271 + difference 4 5) (sourceB1271 + difference 5 4) sourceC1271) = raw20265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1271 sourceB1271 sourceC1271 difference raw20265; decide +kernel
    rw [ha]
    exact (canonical20265 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1271 + sourceB1271) sourceC1271) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1271 + sourceB1271) sourceC1271) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1271 sourceB1271 sourceC1271 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1271 sourceB1271 sourceC1271
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1271, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1272 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1272 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1272 + difference 0 1) (sourceB1272 + difference 1 0) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA1272 + difference 0 1) (sourceB1272 + difference 1 0) sourceC1272) = raw5122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw5122; decide +kernel
    rw [ha]
    exact (canonical5122 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1272 + difference 0 2) (sourceB1272 + difference 2 0) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA1272 + difference 0 2) (sourceB1272 + difference 2 0) sourceC1272) = raw5123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw5123; decide +kernel
    rw [ha]
    exact (canonical5123 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1272 + difference 0 3) (sourceB1272 + difference 3 0) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA1272 + difference 0 3) (sourceB1272 + difference 3 0) sourceC1272) = raw5124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw5124; decide +kernel
    rw [ha]
    exact (canonical5124 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1272 + difference 0 4) (sourceB1272 + difference 4 0) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA1272 + difference 0 4) (sourceB1272 + difference 4 0) sourceC1272) = raw10259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw10259; decide +kernel
    rw [ha]
    exact (canonical10259 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1272 + difference 0 5) (sourceB1272 + difference 5 0) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5305) := by
    have ha : (tripleCharges (sourceA1272 + difference 0 5) (sourceB1272 + difference 5 0) sourceC1272) = raw5125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw5125; decide +kernel
    rw [ha]
    exact (canonical5125 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1272 + difference 1 0) (sourceB1272 + difference 0 1) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4184) := by
    have ha : (tripleCharges (sourceA1272 + difference 1 0) (sourceB1272 + difference 0 1) sourceC1272) = raw20483 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20483; decide +kernel
    rw [ha]
    exact (canonical20483 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1272 + difference 1 2) (sourceB1272 + difference 2 1) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4552) := by
    have ha : (tripleCharges (sourceA1272 + difference 1 2) (sourceB1272 + difference 2 1) sourceC1272) = raw20484 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20484; decide +kernel
    rw [ha]
    exact (canonical20484 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1272 + difference 1 3) (sourceB1272 + difference 3 1) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4552) := by
    have ha : (tripleCharges (sourceA1272 + difference 1 3) (sourceB1272 + difference 3 1) sourceC1272) = raw20485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20485; decide +kernel
    rw [ha]
    exact (canonical20485 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1272 + difference 1 4) (sourceB1272 + difference 4 1) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1272 + difference 1 4) (sourceB1272 + difference 4 1) sourceC1272) = raw5106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw5106; decide +kernel
    rw [ha]
    exact (canonical5106 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1272 + difference 1 5) (sourceB1272 + difference 5 1) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA1272 + difference 1 5) (sourceB1272 + difference 5 1) sourceC1272) = raw10242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw10242; decide +kernel
    rw [ha]
    exact (canonical10242 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1272 + difference 2 0) (sourceB1272 + difference 0 2) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4184) := by
    have ha : (tripleCharges (sourceA1272 + difference 2 0) (sourceB1272 + difference 0 2) sourceC1272) = raw20486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20486; decide +kernel
    rw [ha]
    exact (canonical20486 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1272 + difference 2 1) (sourceB1272 + difference 1 2) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4552) := by
    have ha : (tripleCharges (sourceA1272 + difference 2 1) (sourceB1272 + difference 1 2) sourceC1272) = raw20487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20487; decide +kernel
    rw [ha]
    exact (canonical20487 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1272 + difference 2 3) (sourceB1272 + difference 3 2) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4552) := by
    have ha : (tripleCharges (sourceA1272 + difference 2 3) (sourceB1272 + difference 3 2) sourceC1272) = raw20488 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20488; decide +kernel
    rw [ha]
    exact (canonical20488 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1272 + difference 2 4) (sourceB1272 + difference 4 2) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1272 + difference 2 4) (sourceB1272 + difference 4 2) sourceC1272) = raw5111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw5111; decide +kernel
    rw [ha]
    exact (canonical5111 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1272 + difference 2 5) (sourceB1272 + difference 5 2) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA1272 + difference 2 5) (sourceB1272 + difference 5 2) sourceC1272) = raw10246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw10246; decide +kernel
    rw [ha]
    exact (canonical10246 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1272 + difference 3 0) (sourceB1272 + difference 0 3) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4184) := by
    have ha : (tripleCharges (sourceA1272 + difference 3 0) (sourceB1272 + difference 0 3) sourceC1272) = raw20489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20489; decide +kernel
    rw [ha]
    exact (canonical20489 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1272 + difference 3 1) (sourceB1272 + difference 1 3) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4552) := by
    have ha : (tripleCharges (sourceA1272 + difference 3 1) (sourceB1272 + difference 1 3) sourceC1272) = raw20490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20490; decide +kernel
    rw [ha]
    exact (canonical20490 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1272 + difference 3 2) (sourceB1272 + difference 2 3) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4552) := by
    have ha : (tripleCharges (sourceA1272 + difference 3 2) (sourceB1272 + difference 2 3) sourceC1272) = raw20491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20491; decide +kernel
    rw [ha]
    exact (canonical20491 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1272 + difference 3 4) (sourceB1272 + difference 4 3) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1272 + difference 3 4) (sourceB1272 + difference 4 3) sourceC1272) = raw5116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw5116; decide +kernel
    rw [ha]
    exact (canonical5116 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1272 + difference 3 5) (sourceB1272 + difference 5 3) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA1272 + difference 3 5) (sourceB1272 + difference 5 3) sourceC1272) = raw10250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw10250; decide +kernel
    rw [ha]
    exact (canonical10250 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1272 + difference 4 0) (sourceB1272 + difference 0 4) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4193) := by
    have ha : (tripleCharges (sourceA1272 + difference 4 0) (sourceB1272 + difference 0 4) sourceC1272) = raw20492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20492; decide +kernel
    rw [ha]
    exact (canonical20492 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1272 + difference 4 1) (sourceB1272 + difference 1 4) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4560) := by
    have ha : (tripleCharges (sourceA1272 + difference 4 1) (sourceB1272 + difference 1 4) sourceC1272) = raw20493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20493; decide +kernel
    rw [ha]
    exact (canonical20493 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1272 + difference 4 2) (sourceB1272 + difference 2 4) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4560) := by
    have ha : (tripleCharges (sourceA1272 + difference 4 2) (sourceB1272 + difference 2 4) sourceC1272) = raw20494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20494; decide +kernel
    rw [ha]
    exact (canonical20494 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1272 + difference 4 3) (sourceB1272 + difference 3 4) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4560) := by
    have ha : (tripleCharges (sourceA1272 + difference 4 3) (sourceB1272 + difference 3 4) sourceC1272) = raw20495 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20495; decide +kernel
    rw [ha]
    exact (canonical20495 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1272 + difference 4 5) (sourceB1272 + difference 5 4) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4626) := by
    have ha : (tripleCharges (sourceA1272 + difference 4 5) (sourceB1272 + difference 5 4) sourceC1272) = raw10254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw10254; decide +kernel
    rw [ha]
    exact (canonical10254 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1272 + difference 5 0) (sourceB1272 + difference 0 5) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4189) := by
    have ha : (tripleCharges (sourceA1272 + difference 5 0) (sourceB1272 + difference 0 5) sourceC1272) = raw19631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw19631; decide +kernel
    rw [ha]
    exact (canonical19631 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1272 + difference 5 1) (sourceB1272 + difference 1 5) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4370) := by
    have ha : (tripleCharges (sourceA1272 + difference 5 1) (sourceB1272 + difference 1 5) sourceC1272) = raw19632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw19632; decide +kernel
    rw [ha]
    exact (canonical19632 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1272 + difference 5 2) (sourceB1272 + difference 2 5) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4370) := by
    have ha : (tripleCharges (sourceA1272 + difference 5 2) (sourceB1272 + difference 2 5) sourceC1272) = raw19633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw19633; decide +kernel
    rw [ha]
    exact (canonical19633 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1272 + difference 5 3) (sourceB1272 + difference 3 5) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4370) := by
    have ha : (tripleCharges (sourceA1272 + difference 5 3) (sourceB1272 + difference 3 5) sourceC1272) = raw19634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw19634; decide +kernel
    rw [ha]
    exact (canonical19634 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1272 + difference 5 4) (sourceB1272 + difference 4 5) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1272 + difference 5 4) (sourceB1272 + difference 4 5) sourceC1272) = raw5126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw5126; decide +kernel
    rw [ha]
    exact (canonical5126 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1272 sourceB1272 sourceC1272
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1272, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1088 : Integer.Sparse.reindex keyMap MixedData.row1088 = numericRow1088 := by decide +kernel

theorem numericCheck1088 (x : Master → ℝ) : Integer.Sparse.eval numericRow1088 x =
    (1 : ℝ) * reducedSource1088 x := by
  norm_num [numericRow1088, reducedSource1088, Integer.Sparse.eval, Sparse.eval, nodeValue1178, nodeValue1181, nodeValue1182, nodeValue1188, nodeValue1257, nodeValue2672, nodeValue4088]

theorem reindexCheck1089 : Integer.Sparse.reindex keyMap MixedData.row1089 = numericRow1089 := by decide +kernel

theorem numericCheck1089 (x : Master → ℝ) : Integer.Sparse.eval numericRow1089 x =
    (1 : ℝ) * reducedSource1089 x := by
  norm_num [numericRow1089, reducedSource1089, Integer.Sparse.eval, Sparse.eval, nodeValue1179, nodeValue1991, nodeValue2003, nodeValue2032, nodeValue2218, nodeValue2670, nodeValue4082]

theorem reindexCheck1090 : Integer.Sparse.reindex keyMap MixedData.row1090 = numericRow1090 := by decide +kernel

theorem numericCheck1090 (x : Master → ℝ) : Integer.Sparse.eval numericRow1090 x =
    (1 : ℝ) * reducedSource1090 x := by
  norm_num [numericRow1090, reducedSource1090, Integer.Sparse.eval, Sparse.eval, nodeValue1195, nodeValue2449, nodeValue2469, nodeValue2691, nodeValue2694, nodeValue4090]

theorem reindexCheck1091 : Integer.Sparse.reindex keyMap MixedData.row1091 = numericRow1091 := by decide +kernel

theorem numericCheck1091 (x : Master → ℝ) : Integer.Sparse.eval numericRow1091 x =
    (1 : ℝ) * reducedSource1091 x := by
  norm_num [numericRow1091, reducedSource1091, Integer.Sparse.eval, Sparse.eval, nodeValue1195, nodeValue1196, nodeValue1200, nodeValue1210, nodeValue2694, nodeValue4090]

theorem reindexCheck1092 : Integer.Sparse.reindex keyMap MixedData.row1092 = numericRow1092 := by decide +kernel

theorem numericCheck1092 (x : Master → ℝ) : Integer.Sparse.eval numericRow1092 x =
    (1 : ℝ) * reducedSource1092 x := by
  norm_num [numericRow1092, reducedSource1092, Integer.Sparse.eval, Sparse.eval, nodeValue1194, nodeValue1987, nodeValue2008, nodeValue2193, nodeValue2693, nodeValue4080]

theorem reindexCheck1099 : Integer.Sparse.reindex keyMap MixedData.row1099 = numericRow1099 := by decide +kernel

theorem numericCheck1099 (x : Master → ℝ) : Integer.Sparse.eval numericRow1099 x =
    (1 : ℝ) * reducedSource1099 x := by
  norm_num [numericRow1099, reducedSource1099, Integer.Sparse.eval, Sparse.eval, nodeValue1750, nodeValue1754, nodeValue1756, nodeValue3310, nodeValue4070]

theorem reindexCheck1100 : Integer.Sparse.reindex keyMap MixedData.row1100 = numericRow1100 := by decide +kernel

theorem numericCheck1100 (x : Master → ℝ) : Integer.Sparse.eval numericRow1100 x =
    (1 : ℝ) * reducedSource1100 x := by
  norm_num [numericRow1100, reducedSource1100, Integer.Sparse.eval, Sparse.eval, nodeValue1725, nodeValue1730, nodeValue1754, nodeValue3310, nodeValue4070]

theorem reindexCheck1101 : Integer.Sparse.reindex keyMap MixedData.row1101 = numericRow1101 := by decide +kernel

theorem numericCheck1101 (x : Master → ℝ) : Integer.Sparse.eval numericRow1101 x =
    (1 : ℝ) * reducedSource1101 x := by
  norm_num [numericRow1101, reducedSource1101, Integer.Sparse.eval, Sparse.eval, nodeValue1754, nodeValue3300, nodeValue3310, nodeValue4070]

theorem reindexCheck1102 : Integer.Sparse.reindex keyMap MixedData.row1102 = numericRow1102 := by decide +kernel

theorem numericCheck1102 (x : Master → ℝ) : Integer.Sparse.eval numericRow1102 x =
    (4 : ℝ) * reducedSource1102 x := by
  norm_num [numericRow1102, reducedSource1102, Integer.Sparse.eval, Sparse.eval, nodeValue4184, nodeValue4189, nodeValue4193, nodeValue4370, nodeValue4468, nodeValue4552, nodeValue4560, nodeValue4605, nodeValue4617, nodeValue4626, nodeValue4868, nodeValue4897, nodeValue5305]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1088 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1088 (mixedVector B) = 0 := by
  have h1178 : mixedVector B (Sum.inr 1178) = Sparse.eval nodeValue1178 (mixedVector B) := by
    change mixedMoment B node1178 node1178Labels = _
    exact sound1178 B hB hF
  have h1181 : mixedVector B (Sum.inr 1181) = Sparse.eval nodeValue1181 (mixedVector B) := by
    change mixedMoment B node1181 node1181Labels = _
    exact sound1181 B hB hF
  have h1182 : mixedVector B (Sum.inr 1182) = Sparse.eval nodeValue1182 (mixedVector B) := by
    change mixedMoment B node1182 node1182Labels = _
    exact sound1182 B hB hF
  have h1188 : mixedVector B (Sum.inr 1188) = Sparse.eval nodeValue1188 (mixedVector B) := by
    change mixedMoment B node1188 node1188Labels = _
    exact sound1188 B hB hF
  have h1257 : mixedVector B (Sum.inr 1257) = Sparse.eval nodeValue1257 (mixedVector B) := by
    change mixedMoment B node1257 node1257Labels = _
    exact sound1257 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1258, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1178, h1181, h1182, h1188, h1257, h2672, h4088, reducedSource1088] using sourceEq1258 B hB

theorem rowSound1088 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1088 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1088, numericCheck1088, reducedZero1088 B hB hF, mul_zero]

theorem reducedZero1089 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1089 (mixedVector B) = 0 := by
  have h1179 : mixedVector B (Sum.inr 1179) = Sparse.eval nodeValue1179 (mixedVector B) := by
    change mixedMoment B node1179 node1179Labels = _
    exact sound1179 B hB hF
  have h1991 : mixedVector B (Sum.inr 1991) = Sparse.eval nodeValue1991 (mixedVector B) := by
    change mixedMoment B node1991 node1991Labels = _
    exact sound1991 B hB hF
  have h2003 : mixedVector B (Sum.inr 2003) = Sparse.eval nodeValue2003 (mixedVector B) := by
    change mixedMoment B node2003 node2003Labels = _
    exact sound2003 B hB hF
  have h2032 : mixedVector B (Sum.inr 2032) = Sparse.eval nodeValue2032 (mixedVector B) := by
    change mixedMoment B node2032 node2032Labels = _
    exact sound2032 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h2670 : mixedVector B (Sum.inr 2670) = Sparse.eval nodeValue2670 (mixedVector B) := by
    change mixedMoment B node2670 node2670Labels = _
    exact sound2670 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1259, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1179, h1991, h2003, h2032, h2218, h2670, h4082, reducedSource1089] using sourceEq1259 B hB

theorem rowSound1089 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1089 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1089, numericCheck1089, reducedZero1089 B hB hF, mul_zero]

theorem reducedZero1090 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1090 (mixedVector B) = 0 := by
  have h1195 : mixedVector B (Sum.inr 1195) = Sparse.eval nodeValue1195 (mixedVector B) := by
    change mixedMoment B node1195 node1195Labels = _
    exact sound1195 B hB hF
  have h2449 : mixedVector B (Sum.inr 2449) = Sparse.eval nodeValue2449 (mixedVector B) := by
    change mixedMoment B node2449 node2449Labels = _
    exact sound2449 B hB hF
  have h2469 : mixedVector B (Sum.inr 2469) = Sparse.eval nodeValue2469 (mixedVector B) := by
    change mixedMoment B node2469 node2469Labels = _
    exact sound2469 B hB hF
  have h2691 : mixedVector B (Sum.inr 2691) = Sparse.eval nodeValue2691 (mixedVector B) := by
    change mixedMoment B node2691 node2691Labels = _
    exact sound2691 B hB hF
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm1260, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1195, h2449, h2469, h2691, h2694, h4090, reducedSource1090] using sourceEq1260 B hB

theorem rowSound1090 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1090 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1090, numericCheck1090, reducedZero1090 B hB hF, mul_zero]

theorem reducedZero1091 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1091 (mixedVector B) = 0 := by
  have h1195 : mixedVector B (Sum.inr 1195) = Sparse.eval nodeValue1195 (mixedVector B) := by
    change mixedMoment B node1195 node1195Labels = _
    exact sound1195 B hB hF
  have h1196 : mixedVector B (Sum.inr 1196) = Sparse.eval nodeValue1196 (mixedVector B) := by
    change mixedMoment B node1196 node1196Labels = _
    exact sound1196 B hB hF
  have h1200 : mixedVector B (Sum.inr 1200) = Sparse.eval nodeValue1200 (mixedVector B) := by
    change mixedMoment B node1200 node1200Labels = _
    exact sound1200 B hB hF
  have h1210 : mixedVector B (Sum.inr 1210) = Sparse.eval nodeValue1210 (mixedVector B) := by
    change mixedMoment B node1210 node1210Labels = _
    exact sound1210 B hB hF
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm1261, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1195, h1196, h1200, h1210, h2694, h4090, reducedSource1091] using sourceEq1261 B hB

theorem rowSound1091 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1091 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1091, numericCheck1091, reducedZero1091 B hB hF, mul_zero]

theorem reducedZero1092 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1092 (mixedVector B) = 0 := by
  have h1194 : mixedVector B (Sum.inr 1194) = Sparse.eval nodeValue1194 (mixedVector B) := by
    change mixedMoment B node1194 node1194Labels = _
    exact sound1194 B hB hF
  have h1987 : mixedVector B (Sum.inr 1987) = Sparse.eval nodeValue1987 (mixedVector B) := by
    change mixedMoment B node1987 node1987Labels = _
    exact sound1987 B hB hF
  have h2008 : mixedVector B (Sum.inr 2008) = Sparse.eval nodeValue2008 (mixedVector B) := by
    change mixedMoment B node2008 node2008Labels = _
    exact sound2008 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h2693 : mixedVector B (Sum.inr 2693) = Sparse.eval nodeValue2693 (mixedVector B) := by
    change mixedMoment B node2693 node2693Labels = _
    exact sound2693 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1262, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1194, h1987, h2008, h2193, h2693, h4080, reducedSource1092] using sourceEq1262 B hB

theorem rowSound1092 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1092 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1092, numericCheck1092, reducedZero1092 B hB hF, mul_zero]

theorem reducedZero1099 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1099 (mixedVector B) = 0 := by
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h1754 : mixedVector B (Sum.inr 1754) = Sparse.eval nodeValue1754 (mixedVector B) := by
    change mixedMoment B node1754 node1754Labels = _
    exact sound1754 B hB hF
  have h1756 : mixedVector B (Sum.inr 1756) = Sparse.eval nodeValue1756 (mixedVector B) := by
    change mixedMoment B node1756 node1756Labels = _
    exact sound1756 B hB hF
  have h3310 : mixedVector B (Sum.inr 3310) = Sparse.eval nodeValue3310 (mixedVector B) := by
    change mixedMoment B node3310 node3310Labels = _
    exact sound3310 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1269, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1750, h1754, h1756, h3310, h4070, reducedSource1099] using sourceEq1269 B hB

theorem rowSound1099 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1099 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1099, numericCheck1099, reducedZero1099 B hB hF, mul_zero]

theorem reducedZero1100 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1100 (mixedVector B) = 0 := by
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h1730 : mixedVector B (Sum.inr 1730) = Sparse.eval nodeValue1730 (mixedVector B) := by
    change mixedMoment B node1730 node1730Labels = _
    exact sound1730 B hB hF
  have h1754 : mixedVector B (Sum.inr 1754) = Sparse.eval nodeValue1754 (mixedVector B) := by
    change mixedMoment B node1754 node1754Labels = _
    exact sound1754 B hB hF
  have h3310 : mixedVector B (Sum.inr 3310) = Sparse.eval nodeValue3310 (mixedVector B) := by
    change mixedMoment B node3310 node3310Labels = _
    exact sound3310 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1270, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1725, h1730, h1754, h3310, h4070, reducedSource1100] using sourceEq1270 B hB

theorem rowSound1100 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1100 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1100, numericCheck1100, reducedZero1100 B hB hF, mul_zero]

theorem reducedZero1101 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1101 (mixedVector B) = 0 := by
  have h1754 : mixedVector B (Sum.inr 1754) = Sparse.eval nodeValue1754 (mixedVector B) := by
    change mixedMoment B node1754 node1754Labels = _
    exact sound1754 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h3310 : mixedVector B (Sum.inr 3310) = Sparse.eval nodeValue3310 (mixedVector B) := by
    change mixedMoment B node3310 node3310Labels = _
    exact sound3310 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1271, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1754, h3300, h3310, h4070, reducedSource1101] using sourceEq1271 B hB

theorem rowSound1101 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1101 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1101, numericCheck1101, reducedZero1101 B hB hF, mul_zero]

theorem reducedZero1102 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1102 (mixedVector B) = 0 := by
  have h4184 : mixedVector B (Sum.inr 4184) = Sparse.eval nodeValue4184 (mixedVector B) := by
    change mixedMoment B node4184 node4184Labels = _
    exact sound4184 B hB hF
  have h4189 : mixedVector B (Sum.inr 4189) = Sparse.eval nodeValue4189 (mixedVector B) := by
    change mixedMoment B node4189 node4189Labels = _
    exact sound4189 B hB hF
  have h4193 : mixedVector B (Sum.inr 4193) = Sparse.eval nodeValue4193 (mixedVector B) := by
    change mixedMoment B node4193 node4193Labels = _
    exact sound4193 B hB hF
  have h4370 : mixedVector B (Sum.inr 4370) = Sparse.eval nodeValue4370 (mixedVector B) := by
    change mixedMoment B node4370 node4370Labels = _
    exact sound4370 B hB hF
  have h4468 : mixedVector B (Sum.inr 4468) = Sparse.eval nodeValue4468 (mixedVector B) := by
    change mixedMoment B node4468 node4468Labels = _
    exact sound4468 B hB hF
  have h4552 : mixedVector B (Sum.inr 4552) = Sparse.eval nodeValue4552 (mixedVector B) := by
    change mixedMoment B node4552 node4552Labels = _
    exact sound4552 B hB hF
  have h4560 : mixedVector B (Sum.inr 4560) = Sparse.eval nodeValue4560 (mixedVector B) := by
    change mixedMoment B node4560 node4560Labels = _
    exact sound4560 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4617 : mixedVector B (Sum.inr 4617) = Sparse.eval nodeValue4617 (mixedVector B) := by
    change mixedMoment B node4617 node4617Labels = _
    exact sound4617 B hB hF
  have h4626 : mixedVector B (Sum.inr 4626) = Sparse.eval nodeValue4626 (mixedVector B) := by
    change mixedMoment B node4626 node4626Labels = _
    exact sound4626 B hB hF
  have h4868 : mixedVector B (Sum.inr 4868) = Sparse.eval nodeValue4868 (mixedVector B) := by
    change mixedMoment B node4868 node4868Labels = _
    exact sound4868 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  have h5305 : mixedVector B (Sum.inr 5305) = Sparse.eval nodeValue5305 (mixedVector B) := by
    change mixedMoment B node5305 node5305Labels = _
    exact sound5305 B hB hF
  simpa only [sourceForm1272, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4184, h4189, h4193, h4370, h4468, h4552, h4560, h4605, h4617, h4626, h4868, h4897, h5305, reducedSource1102] using sourceEq1272 B hB

theorem rowSound1102 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1102 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1102, numericCheck1102, reducedZero1102 B hB hF, mul_zero]

theorem sourceRowsAt1088 : MixedData.sourceRows (1088 : Fin 2425) =
    MixedData.row1088 := by decide +kernel

theorem sourceRowsAt1089 : MixedData.sourceRows (1089 : Fin 2425) =
    MixedData.row1089 := by decide +kernel

theorem sourceRowsAt1090 : MixedData.sourceRows (1090 : Fin 2425) =
    MixedData.row1090 := by decide +kernel

theorem sourceRowsAt1091 : MixedData.sourceRows (1091 : Fin 2425) =
    MixedData.row1091 := by decide +kernel

theorem sourceRowsAt1092 : MixedData.sourceRows (1092 : Fin 2425) =
    MixedData.row1092 := by decide +kernel

theorem sourceRowsAt1093 : MixedData.sourceRows (1093 : Fin 2425) =
    MixedData.row1093 := by decide +kernel

theorem sourceRowsAt1094 : MixedData.sourceRows (1094 : Fin 2425) =
    MixedData.row1094 := by decide +kernel

theorem sourceRowsAt1095 : MixedData.sourceRows (1095 : Fin 2425) =
    MixedData.row1095 := by decide +kernel

theorem sourceRowsAt1096 : MixedData.sourceRows (1096 : Fin 2425) =
    MixedData.row1096 := by decide +kernel

theorem sourceRowsAt1097 : MixedData.sourceRows (1097 : Fin 2425) =
    MixedData.row1097 := by decide +kernel

theorem sourceRowsAt1098 : MixedData.sourceRows (1098 : Fin 2425) =
    MixedData.row1098 := by decide +kernel

theorem sourceRowsAt1099 : MixedData.sourceRows (1099 : Fin 2425) =
    MixedData.row1099 := by decide +kernel

theorem sourceRowsAt1100 : MixedData.sourceRows (1100 : Fin 2425) =
    MixedData.row1100 := by decide +kernel

theorem sourceRowsAt1101 : MixedData.sourceRows (1101 : Fin 2425) =
    MixedData.row1101 := by decide +kernel

theorem sourceRowsAt1102 : MixedData.sourceRows (1102 : Fin 2425) =
    MixedData.row1102 := by decide +kernel

theorem sourceRowsAt1103 : MixedData.sourceRows (1103 : Fin 2425) =
    MixedData.row1103 := by decide +kernel

theorem chunkSound68_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 68) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1088 ∨ k.val = 1089 ∨ k.val = 1090 ∨ k.val = 1091 ∨ k.val = 1092 ∨ k.val = 1093 ∨ k.val = 1094 ∨ k.val = 1095 ∨ k.val = 1096 ∨ k.val = 1097 ∨ k.val = 1098 ∨ k.val = 1099 ∨ k.val = 1100 ∨ k.val = 1101 ∨ k.val = 1102 ∨ k.val = 1103 := by omega
  rcases heq with h1088 | h1089 | h1090 | h1091 | h1092 | h1093 | h1094 | h1095 | h1096 | h1097 | h1098 | h1099 | h1100 | h1101 | h1102 | h1103
  · have he : k = (1088 : Fin 2425) := Fin.ext h1088
    subst k
    rw [sourceRowsAt1088]
    exact rowSound1088 B hB hF
  · have he : k = (1089 : Fin 2425) := Fin.ext h1089
    subst k
    rw [sourceRowsAt1089]
    exact rowSound1089 B hB hF
  · have he : k = (1090 : Fin 2425) := Fin.ext h1090
    subst k
    rw [sourceRowsAt1090]
    exact rowSound1090 B hB hF
  · have he : k = (1091 : Fin 2425) := Fin.ext h1091
    subst k
    rw [sourceRowsAt1091]
    exact rowSound1091 B hB hF
  · have he : k = (1092 : Fin 2425) := Fin.ext h1092
    subst k
    rw [sourceRowsAt1092]
    exact rowSound1092 B hB hF
  · have he : k = (1093 : Fin 2425) := Fin.ext h1093
    subst k
    rw [sourceRowsAt1093]
    exact rowSound1093_e B hB hF
  · have he : k = (1094 : Fin 2425) := Fin.ext h1094
    subst k
    rw [sourceRowsAt1094]
    exact rowSound1094_e B hB hF
  · have he : k = (1095 : Fin 2425) := Fin.ext h1095
    subst k
    rw [sourceRowsAt1095]
    exact rowSound1095_e B hB hF
  · have he : k = (1096 : Fin 2425) := Fin.ext h1096
    subst k
    rw [sourceRowsAt1096]
    exact rowSound1096_e B hB hF
  · have he : k = (1097 : Fin 2425) := Fin.ext h1097
    subst k
    rw [sourceRowsAt1097]
    exact rowSound1097_e B hB hF
  · have he : k = (1098 : Fin 2425) := Fin.ext h1098
    subst k
    rw [sourceRowsAt1098]
    exact rowSound1098_e B hB hF
  · have he : k = (1099 : Fin 2425) := Fin.ext h1099
    subst k
    rw [sourceRowsAt1099]
    exact rowSound1099 B hB hF
  · have he : k = (1100 : Fin 2425) := Fin.ext h1100
    subst k
    rw [sourceRowsAt1100]
    exact rowSound1100 B hB hF
  · have he : k = (1101 : Fin 2425) := Fin.ext h1101
    subst k
    rw [sourceRowsAt1101]
    exact rowSound1101 B hB hF
  · have he : k = (1102 : Fin 2425) := Fin.ext h1102
    subst k
    rw [sourceRowsAt1102]
    exact rowSound1102 B hB hF
  · have he : k = (1103 : Fin 2425) := Fin.ext h1103
    subst k
    rw [sourceRowsAt1103]
    exact rowSound1103_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound68_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound68_e_oai
