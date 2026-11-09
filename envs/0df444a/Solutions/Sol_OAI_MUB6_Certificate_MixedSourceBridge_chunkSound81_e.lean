-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:35:51.759691+00:00
-- url     : https://prove2.me/submissions/92596d17-075b-49fd-b0f9-efe78d22921b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1300_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1301_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1303_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1309_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1310_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1311_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1749 raw1749Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw1749 raw1749Labels = mixedMoment B raw1749step0 raw1749step0Labels := by
      have ha : raw1749step0 = (fun i j => raw1749 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1749step0 raw1749; decide +kernel
      have hl : raw1749step0Labels = raw1749Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1749 raw1749Labels permutation32 permutation4
    mixedMoment B raw1749step0 raw1749step0Labels = mixedMoment B raw1749step1 raw1749step1Labels := by
      have ha : raw1749step1 = raw1749step0 := by apply Matrix.ext; unfold raw1749step1 raw1749step0; decide +kernel
      have hl : raw1749step0Labels = labelEmbedding7 ∘ raw1749step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1749step0 raw1749step0Labels raw1749step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

theorem canonical1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1750 raw1750Labels = mixedMoment B node2029 node2029Labels := by
  calc
    mixedMoment B raw1750 raw1750Labels = mixedMoment B raw1750step0 raw1750step0Labels := by
      have ha : raw1750step0 = (fun i j => raw1750 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1750step0 raw1750; decide +kernel
      have hl : raw1750step0Labels = raw1750Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1750 raw1750Labels permutation32 permutation4
    _ = mixedMoment B node2029 node2029Labels := by rfl

theorem canonical1751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1751 raw1751Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw1751 raw1751Labels = mixedMoment B raw1751step0 raw1751step0Labels := by
      have ha : raw1751step0 = (fun i j => raw1751 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1751step0 raw1751; decide +kernel
      have hl : raw1751step0Labels = raw1751Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1751 raw1751Labels permutation32 permutation6
    mixedMoment B raw1751step0 raw1751step0Labels = mixedMoment B raw1751step1 raw1751step1Labels := by
      have ha : raw1751step1 = -raw1751step0 := by apply Matrix.ext; change ∀ i j, raw1751step1 i j = -(raw1751step0 i j); unfold raw1751step1 raw1751step0; decide +kernel
      have hl : raw1751step1Labels = raw1751step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1751step1 raw1751step1Labels = mixedMoment B raw1751step2 raw1751step2Labels := by
      have ha : raw1751step2 = raw1751step1 := by apply Matrix.ext; unfold raw1751step2 raw1751step1; decide +kernel
      have hl : raw1751step1Labels = labelEmbedding1 ∘ raw1751step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1751step1 raw1751step1Labels raw1751step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2225 node2225Labels := by rfl

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

theorem canonical1809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1809 raw1809Labels = mixedMoment B node4875 node4875Labels := by
  calc
    mixedMoment B raw1809 raw1809Labels = mixedMoment B raw1809step0 raw1809step0Labels := by
      have ha : raw1809step0 = (fun i j => raw1809 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1809step0 raw1809; decide +kernel
      have hl : raw1809step0Labels = raw1809Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1809 raw1809Labels permutation8 permutation4
    mixedMoment B raw1809step0 raw1809step0Labels = mixedMoment B raw1809step1 raw1809step1Labels := by
      have ha : raw1809step1 = raw1809step0 := by apply Matrix.ext; unfold raw1809step1 raw1809step0; decide +kernel
      have hl : raw1809step0Labels = labelEmbedding7 ∘ raw1809step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1809step0 raw1809step0Labels raw1809step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4875 node4875Labels := by rfl

theorem canonical1810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1810 raw1810Labels = mixedMoment B node2116 node2116Labels := by
  calc
    mixedMoment B raw1810 raw1810Labels = mixedMoment B raw1810step0 raw1810step0Labels := by
      have ha : raw1810step0 = (fun i j => raw1810 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1810step0 raw1810; decide +kernel
      have hl : raw1810step0Labels = raw1810Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1810 raw1810Labels permutation8 permutation4
    _ = mixedMoment B node2116 node2116Labels := by rfl

theorem canonical1811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1811 raw1811Labels = mixedMoment B node2288 node2288Labels := by
  calc
    mixedMoment B raw1811 raw1811Labels = mixedMoment B raw1811step0 raw1811step0Labels := by
      have ha : raw1811step0 = (fun i j => raw1811 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1811step0 raw1811; decide +kernel
      have hl : raw1811step0Labels = raw1811Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1811 raw1811Labels permutation8 permutation6
    mixedMoment B raw1811step0 raw1811step0Labels = mixedMoment B raw1811step1 raw1811step1Labels := by
      have ha : raw1811step1 = -raw1811step0 := by apply Matrix.ext; change ∀ i j, raw1811step1 i j = -(raw1811step0 i j); unfold raw1811step1 raw1811step0; decide +kernel
      have hl : raw1811step1Labels = raw1811step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1811step1 raw1811step1Labels = mixedMoment B raw1811step2 raw1811step2Labels := by
      have ha : raw1811step2 = raw1811step1 := by apply Matrix.ext; unfold raw1811step2 raw1811step1; decide +kernel
      have hl : raw1811step1Labels = labelEmbedding1 ∘ raw1811step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1811step1 raw1811step1Labels raw1811step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2288 node2288Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical165
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21144 raw21144Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw21144 raw21144Labels = mixedMoment B raw21144step0 raw21144step0Labels := by
      have hz : ∀ j, raw21144 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21144step0 = (fun i j => raw21144 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21144step0 raw21144; decide +kernel
      have hl : raw21144step0Labels = raw21144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21144 raw21144Labels permutation434 hz
    mixedMoment B raw21144step0 raw21144step0Labels = mixedMoment B raw21144step1 raw21144step1Labels := by
      have hz : ∀ j, raw21144step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21144step1 = (fun i j => raw21144step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21144step1 raw21144step0; decide +kernel
      have hl : raw21144step1Labels = raw21144step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21144step0 raw21144step0Labels permutation80 hz
    _ = mixedMoment B node4895 node4895Labels := by rfl

theorem canonical21157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21157 raw21157Labels = mixedMoment B node4161 node4161Labels := by
  calc
    mixedMoment B raw21157 raw21157Labels = mixedMoment B raw21157step0 raw21157step0Labels := by
      have hz : ∀ j, raw21157 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21157step0 = (fun i j => raw21157 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21157step0 raw21157; decide +kernel
      have hl : raw21157step0Labels = raw21157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21157 raw21157Labels permutation434 hz
    mixedMoment B raw21157step0 raw21157step0Labels = mixedMoment B raw21157step1 raw21157step1Labels := by
      have hz : ∀ j, raw21157step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21157step1 = (fun i j => raw21157step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21157step1 raw21157step0; decide +kernel
      have hl : raw21157step1Labels = raw21157step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21157step0 raw21157step0Labels permutation80 hz
    _ = mixedMoment B node4161 node4161Labels := by rfl

theorem canonical21158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21158 raw21158Labels = mixedMoment B node4374 node4374Labels := by
  calc
    mixedMoment B raw21158 raw21158Labels = mixedMoment B raw21158step0 raw21158step0Labels := by
      have hz : ∀ j, raw21158 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21158step0 = (fun i j => raw21158 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21158step0 raw21158; decide +kernel
      have hl : raw21158step0Labels = raw21158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21158 raw21158Labels permutation434 hz
    mixedMoment B raw21158step0 raw21158step0Labels = mixedMoment B raw21158step1 raw21158step1Labels := by
      have hz : ∀ j, raw21158step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21158step1 = (fun i j => raw21158step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21158step1 raw21158step0; decide +kernel
      have hl : raw21158step1Labels = raw21158step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21158step0 raw21158step0Labels permutation80 hz
    _ = mixedMoment B node4374 node4374Labels := by rfl

theorem canonical21159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21159 raw21159Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw21159 raw21159Labels = mixedMoment B raw21159step0 raw21159step0Labels := by
      have hz : ∀ j, raw21159 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21159step0 = (fun i j => raw21159 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21159step0 raw21159; decide +kernel
      have hl : raw21159step0Labels = raw21159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21159 raw21159Labels permutation434 hz
    mixedMoment B raw21159step0 raw21159step0Labels = mixedMoment B raw21159step1 raw21159step1Labels := by
      have ha : raw21159step1 = (fun i j => raw21159step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21159step1 raw21159step0; decide +kernel
      have hl : raw21159step1Labels = raw21159step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21159step0 raw21159step0Labels permutation38 permutation2
    _ = mixedMoment B node4335 node4335Labels := by rfl

theorem canonical21160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21160 raw21160Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw21160 raw21160Labels = mixedMoment B raw21160step0 raw21160step0Labels := by
      have hz : ∀ j, raw21160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21160step0 = (fun i j => raw21160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21160step0 raw21160; decide +kernel
      have hl : raw21160step0Labels = raw21160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21160 raw21160Labels permutation346 hz
    mixedMoment B raw21160step0 raw21160step0Labels = mixedMoment B raw21160step1 raw21160step1Labels := by
      have ha : raw21160step1 = (fun i j => raw21160step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21160step1 raw21160step0; decide +kernel
      have hl : raw21160step1Labels = raw21160step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21160step0 raw21160step0Labels permutation38 permutation2
    _ = mixedMoment B node4335 node4335Labels := by rfl

theorem canonical21196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21196 raw21196Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw21196 raw21196Labels = mixedMoment B raw21196step0 raw21196step0Labels := by
      have hz : ∀ j, raw21196 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21196step0 = (fun i j => raw21196 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21196step0 raw21196; decide +kernel
      have hl : raw21196step0Labels = raw21196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21196 raw21196Labels permutation434 hz
    mixedMoment B raw21196step0 raw21196step0Labels = mixedMoment B raw21196step1 raw21196step1Labels := by
      have hz : ∀ j, raw21196step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21196step1 = (fun i j => raw21196step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21196step1 raw21196step0; decide +kernel
      have hl : raw21196step1Labels = raw21196step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21196step0 raw21196step0Labels permutation80 hz
    mixedMoment B raw21196step1 raw21196step1Labels = mixedMoment B raw21196step2 raw21196step2Labels := by
      have ha : raw21196step2 = (fun i j => raw21196step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21196step2 raw21196step1; decide +kernel
      have hl : raw21196step2Labels = raw21196step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21196step1 raw21196step1Labels permutation8 permutation7
    mixedMoment B raw21196step2 raw21196step2Labels = mixedMoment B raw21196step3 raw21196step3Labels := by
      have ha : raw21196step3 = -raw21196step2 := by apply Matrix.ext; change ∀ i j, raw21196step3 i j = -(raw21196step2 i j); unfold raw21196step3 raw21196step2; decide +kernel
      have hl : raw21196step3Labels = raw21196step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21196step3 raw21196step3Labels = mixedMoment B raw21196step4 raw21196step4Labels := by
      have ha : raw21196step4 = raw21196step3 := by apply Matrix.ext; unfold raw21196step4 raw21196step3; decide +kernel
      have hl : raw21196step3Labels = labelEmbedding1 ∘ raw21196step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21196step3 raw21196step3Labels raw21196step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

theorem canonical21209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21209 raw21209Labels = mixedMoment B node1533 node1533Labels := by
  calc
    mixedMoment B raw21209 raw21209Labels = mixedMoment B raw21209step0 raw21209step0Labels := by
      have hz : ∀ j, raw21209 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21209step0 = (fun i j => raw21209 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21209step0 raw21209; decide +kernel
      have hl : raw21209step0Labels = raw21209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21209 raw21209Labels permutation434 hz
    mixedMoment B raw21209step0 raw21209step0Labels = mixedMoment B raw21209step1 raw21209step1Labels := by
      have hz : ∀ j, raw21209step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21209step1 = (fun i j => raw21209step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21209step1 raw21209step0; decide +kernel
      have hl : raw21209step1Labels = raw21209step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21209step0 raw21209step0Labels permutation80 hz
    mixedMoment B raw21209step1 raw21209step1Labels = mixedMoment B raw21209step2 raw21209step2Labels := by
      have ha : raw21209step2 = (fun i j => raw21209step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21209step2 raw21209step1; decide +kernel
      have hl : raw21209step2Labels = raw21209step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21209step1 raw21209step1Labels permutation8 permutation7
    mixedMoment B raw21209step2 raw21209step2Labels = mixedMoment B raw21209step3 raw21209step3Labels := by
      have ha : raw21209step3 = -raw21209step2 := by apply Matrix.ext; change ∀ i j, raw21209step3 i j = -(raw21209step2 i j); unfold raw21209step3 raw21209step2; decide +kernel
      have hl : raw21209step3Labels = raw21209step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21209step3 raw21209step3Labels = mixedMoment B raw21209step4 raw21209step4Labels := by
      have ha : raw21209step4 = raw21209step3 := by apply Matrix.ext; unfold raw21209step4 raw21209step3; decide +kernel
      have hl : raw21209step3Labels = labelEmbedding1 ∘ raw21209step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21209step3 raw21209step3Labels raw21209step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1533 node1533Labels := by rfl

theorem canonical21210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21210 raw21210Labels = mixedMoment B node1748 node1748Labels := by
  calc
    mixedMoment B raw21210 raw21210Labels = mixedMoment B raw21210step0 raw21210step0Labels := by
      have hz : ∀ j, raw21210 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21210step0 = (fun i j => raw21210 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21210step0 raw21210; decide +kernel
      have hl : raw21210step0Labels = raw21210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21210 raw21210Labels permutation434 hz
    mixedMoment B raw21210step0 raw21210step0Labels = mixedMoment B raw21210step1 raw21210step1Labels := by
      have hz : ∀ j, raw21210step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21210step1 = (fun i j => raw21210step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21210step1 raw21210step0; decide +kernel
      have hl : raw21210step1Labels = raw21210step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21210step0 raw21210step0Labels permutation80 hz
    mixedMoment B raw21210step1 raw21210step1Labels = mixedMoment B raw21210step2 raw21210step2Labels := by
      have ha : raw21210step2 = (fun i j => raw21210step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21210step2 raw21210step1; decide +kernel
      have hl : raw21210step2Labels = raw21210step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21210step1 raw21210step1Labels permutation8 permutation7
    mixedMoment B raw21210step2 raw21210step2Labels = mixedMoment B raw21210step3 raw21210step3Labels := by
      have ha : raw21210step3 = -raw21210step2 := by apply Matrix.ext; change ∀ i j, raw21210step3 i j = -(raw21210step2 i j); unfold raw21210step3 raw21210step2; decide +kernel
      have hl : raw21210step3Labels = raw21210step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21210step3 raw21210step3Labels = mixedMoment B raw21210step4 raw21210step4Labels := by
      have ha : raw21210step4 = raw21210step3 := by apply Matrix.ext; unfold raw21210step4 raw21210step3; decide +kernel
      have hl : raw21210step3Labels = labelEmbedding1 ∘ raw21210step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21210step3 raw21210step3Labels raw21210step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1748 node1748Labels := by rfl

theorem canonical21211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21211 raw21211Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw21211 raw21211Labels = mixedMoment B raw21211step0 raw21211step0Labels := by
      have hz : ∀ j, raw21211 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21211step0 = (fun i j => raw21211 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21211step0 raw21211; decide +kernel
      have hl : raw21211step0Labels = raw21211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21211 raw21211Labels permutation434 hz
    mixedMoment B raw21211step0 raw21211step0Labels = mixedMoment B raw21211step1 raw21211step1Labels := by
      have ha : raw21211step1 = (fun i j => raw21211step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21211step1 raw21211step0; decide +kernel
      have hl : raw21211step1Labels = raw21211step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21211step0 raw21211step0Labels permutation38 permutation7
    mixedMoment B raw21211step1 raw21211step1Labels = mixedMoment B raw21211step2 raw21211step2Labels := by
      have ha : raw21211step2 = -raw21211step1 := by apply Matrix.ext; change ∀ i j, raw21211step2 i j = -(raw21211step1 i j); unfold raw21211step2 raw21211step1; decide +kernel
      have hl : raw21211step2Labels = raw21211step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21211step2 raw21211step2Labels = mixedMoment B raw21211step3 raw21211step3Labels := by
      have ha : raw21211step3 = raw21211step2 := by apply Matrix.ext; unfold raw21211step3 raw21211step2; decide +kernel
      have hl : raw21211step2Labels = labelEmbedding1 ∘ raw21211step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21211step2 raw21211step2Labels raw21211step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

theorem canonical21212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21212 raw21212Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw21212 raw21212Labels = mixedMoment B raw21212step0 raw21212step0Labels := by
      have hz : ∀ j, raw21212 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21212step0 = (fun i j => raw21212 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21212step0 raw21212; decide +kernel
      have hl : raw21212step0Labels = raw21212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21212 raw21212Labels permutation346 hz
    mixedMoment B raw21212step0 raw21212step0Labels = mixedMoment B raw21212step1 raw21212step1Labels := by
      have ha : raw21212step1 = (fun i j => raw21212step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21212step1 raw21212step0; decide +kernel
      have hl : raw21212step1Labels = raw21212step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21212step0 raw21212step0Labels permutation38 permutation7
    mixedMoment B raw21212step1 raw21212step1Labels = mixedMoment B raw21212step2 raw21212step2Labels := by
      have ha : raw21212step2 = -raw21212step1 := by apply Matrix.ext; change ∀ i j, raw21212step2 i j = -(raw21212step1 i j); unfold raw21212step2 raw21212step1; decide +kernel
      have hl : raw21212step2Labels = raw21212step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21212step2 raw21212step2Labels = mixedMoment B raw21212step3 raw21212step3Labels := by
      have ha : raw21212step3 = raw21212step2 := by apply Matrix.ext; unfold raw21212step3 raw21212step2; decide +kernel
      have hl : raw21212step2Labels = labelEmbedding1 ∘ raw21212step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21212step2 raw21212step2Labels raw21212step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

theorem canonical21222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21222 raw21222Labels = mixedMoment B node589 node589Labels := by
  calc
    mixedMoment B raw21222 raw21222Labels = mixedMoment B raw21222step0 raw21222step0Labels := by
      have hz : ∀ j, raw21222 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21222step0 = (fun i j => raw21222 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21222step0 raw21222; decide +kernel
      have hl : raw21222step0Labels = raw21222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21222 raw21222Labels permutation434 hz
    mixedMoment B raw21222step0 raw21222step0Labels = mixedMoment B raw21222step1 raw21222step1Labels := by
      have hz : ∀ j, raw21222step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21222step1 = (fun i j => raw21222step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21222step1 raw21222step0; decide +kernel
      have hl : raw21222step1Labels = raw21222step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21222step0 raw21222step0Labels permutation80 hz
    _ = mixedMoment B node589 node589Labels := by rfl

theorem canonical21227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21227 raw21227Labels = mixedMoment B node1086 node1086Labels := by
  calc
    mixedMoment B raw21227 raw21227Labels = mixedMoment B raw21227step0 raw21227step0Labels := by
      have hz : ∀ j, raw21227 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21227step0 = (fun i j => raw21227 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21227step0 raw21227; decide +kernel
      have hl : raw21227step0Labels = raw21227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21227 raw21227Labels permutation434 hz
    mixedMoment B raw21227step0 raw21227step0Labels = mixedMoment B raw21227step1 raw21227step1Labels := by
      have hz : ∀ j, raw21227step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21227step1 = (fun i j => raw21227step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21227step1 raw21227step0; decide +kernel
      have hl : raw21227step1Labels = raw21227step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21227step0 raw21227step0Labels permutation80 hz
    _ = mixedMoment B node1086 node1086Labels := by rfl

theorem canonical21230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21230 raw21230Labels = mixedMoment B node953 node953Labels := by
  calc
    mixedMoment B raw21230 raw21230Labels = mixedMoment B raw21230step0 raw21230step0Labels := by
      have hz : ∀ j, raw21230 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21230step0 = (fun i j => raw21230 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21230step0 raw21230; decide +kernel
      have hl : raw21230step0Labels = raw21230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21230 raw21230Labels permutation434 hz
    mixedMoment B raw21230step0 raw21230step0Labels = mixedMoment B raw21230step1 raw21230step1Labels := by
      have hz : ∀ j, raw21230step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21230step1 = (fun i j => raw21230step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21230step1 raw21230step0; decide +kernel
      have hl : raw21230step1Labels = raw21230step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21230step0 raw21230step0Labels permutation80 hz
    _ = mixedMoment B node953 node953Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical179
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23017 raw23017Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw23017 raw23017Labels = mixedMoment B raw23017step0 raw23017step0Labels := by
      have hz : ∀ j, raw23017 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23017step0 = (fun i j => raw23017 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23017step0 raw23017; decide +kernel
      have hl : raw23017step0Labels = raw23017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23017 raw23017Labels permutation434 hz
    mixedMoment B raw23017step0 raw23017step0Labels = mixedMoment B raw23017step1 raw23017step1Labels := by
      have hz : ∀ j, raw23017step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23017step1 = (fun i j => raw23017step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23017step1 raw23017step0; decide +kernel
      have hl : raw23017step1Labels = raw23017step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23017step0 raw23017step0Labels permutation80 hz
    mixedMoment B raw23017step1 raw23017step1Labels = mixedMoment B raw23017step2 raw23017step2Labels := by
      have ha : raw23017step2 = (fun i j => raw23017step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23017step2 raw23017step1; decide +kernel
      have hl : raw23017step2Labels = raw23017step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23017step1 raw23017step1Labels permutation9 permutation2
    _ = mixedMoment B node1049 node1049Labels := by rfl

theorem canonical23018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23018 raw23018Labels = mixedMoment B node613 node613Labels := by
  calc
    mixedMoment B raw23018 raw23018Labels = mixedMoment B raw23018step0 raw23018step0Labels := by
      have hz : ∀ j, raw23018 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23018step0 = (fun i j => raw23018 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23018step0 raw23018; decide +kernel
      have hl : raw23018step0Labels = raw23018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23018 raw23018Labels permutation434 hz
    mixedMoment B raw23018step0 raw23018step0Labels = mixedMoment B raw23018step1 raw23018step1Labels := by
      have hz : ∀ j, raw23018step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23018step1 = (fun i j => raw23018step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23018step1 raw23018step0; decide +kernel
      have hl : raw23018step1Labels = raw23018step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23018step0 raw23018step0Labels permutation80 hz
    mixedMoment B raw23018step1 raw23018step1Labels = mixedMoment B raw23018step2 raw23018step2Labels := by
      have ha : raw23018step2 = (fun i j => raw23018step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23018step2 raw23018step1; decide +kernel
      have hl : raw23018step2Labels = raw23018step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23018step1 raw23018step1Labels permutation9 permutation2
    _ = mixedMoment B node613 node613Labels := by rfl

theorem canonical23019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23019 raw23019Labels = mixedMoment B node582 node582Labels := by
  calc
    mixedMoment B raw23019 raw23019Labels = mixedMoment B raw23019step0 raw23019step0Labels := by
      have hz : ∀ j, raw23019 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23019step0 = (fun i j => raw23019 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23019step0 raw23019; decide +kernel
      have hl : raw23019step0Labels = raw23019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23019 raw23019Labels permutation434 hz
    mixedMoment B raw23019step0 raw23019step0Labels = mixedMoment B raw23019step1 raw23019step1Labels := by
      have ha : raw23019step1 = (fun i j => raw23019step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23019step1 raw23019step0; decide +kernel
      have hl : raw23019step1Labels = raw23019step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23019step0 raw23019step0Labels permutation33 permutation2
    _ = mixedMoment B node582 node582Labels := by rfl

theorem canonical23020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23020 raw23020Labels = mixedMoment B node582 node582Labels := by
  calc
    mixedMoment B raw23020 raw23020Labels = mixedMoment B raw23020step0 raw23020step0Labels := by
      have hz : ∀ j, raw23020 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23020step0 = (fun i j => raw23020 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23020step0 raw23020; decide +kernel
      have hl : raw23020step0Labels = raw23020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23020 raw23020Labels permutation346 hz
    mixedMoment B raw23020step0 raw23020step0Labels = mixedMoment B raw23020step1 raw23020step1Labels := by
      have ha : raw23020step1 = (fun i j => raw23020step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23020step1 raw23020step0; decide +kernel
      have hl : raw23020step1Labels = raw23020step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23020step0 raw23020step0Labels permutation33 permutation2
    _ = mixedMoment B node582 node582Labels := by rfl

theorem canonical23021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23021 raw23021Labels = mixedMoment B node588 node588Labels := by
  calc
    mixedMoment B raw23021 raw23021Labels = mixedMoment B raw23021step0 raw23021step0Labels := by
      have hz : ∀ j, raw23021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23021step0 = (fun i j => raw23021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23021step0 raw23021; decide +kernel
      have hl : raw23021step0Labels = raw23021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23021 raw23021Labels permutation434 hz
    mixedMoment B raw23021step0 raw23021step0Labels = mixedMoment B raw23021step1 raw23021step1Labels := by
      have hz : ∀ j, raw23021step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23021step1 = (fun i j => raw23021step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23021step1 raw23021step0; decide +kernel
      have hl : raw23021step1Labels = raw23021step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23021step0 raw23021step0Labels permutation80 hz
    mixedMoment B raw23021step1 raw23021step1Labels = mixedMoment B raw23021step2 raw23021step2Labels := by
      have ha : raw23021step2 = (fun i j => raw23021step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23021step2 raw23021step1; decide +kernel
      have hl : raw23021step2Labels = raw23021step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23021step1 raw23021step1Labels permutation9 permutation2
    _ = mixedMoment B node588 node588Labels := by rfl

theorem canonical23022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23022 raw23022Labels = mixedMoment B node590 node590Labels := by
  calc
    mixedMoment B raw23022 raw23022Labels = mixedMoment B raw23022step0 raw23022step0Labels := by
      have hz : ∀ j, raw23022 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23022step0 = (fun i j => raw23022 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23022step0 raw23022; decide +kernel
      have hl : raw23022step0Labels = raw23022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23022 raw23022Labels permutation434 hz
    mixedMoment B raw23022step0 raw23022step0Labels = mixedMoment B raw23022step1 raw23022step1Labels := by
      have hz : ∀ j, raw23022step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23022step1 = (fun i j => raw23022step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23022step1 raw23022step0; decide +kernel
      have hl : raw23022step1Labels = raw23022step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23022step0 raw23022step0Labels permutation80 hz
    _ = mixedMoment B node590 node590Labels := by rfl

theorem canonical23023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23023 raw23023Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw23023 raw23023Labels = mixedMoment B raw23023step0 raw23023step0Labels := by
      have hz : ∀ j, raw23023 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw23023step0 = (fun i j => raw23023 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw23023step0 raw23023; decide +kernel
      have hl : raw23023step0Labels = raw23023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23023 raw23023Labels permutation590 hz
    mixedMoment B raw23023step0 raw23023step0Labels = mixedMoment B raw23023step1 raw23023step1Labels := by
      have hz : ∀ j, raw23023step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw23023step1 = (fun i j => raw23023step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw23023step1 raw23023step0; decide +kernel
      have hl : raw23023step1Labels = raw23023step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23023step0 raw23023step0Labels permutation104 hz
    mixedMoment B raw23023step1 raw23023step1Labels = mixedMoment B raw23023step2 raw23023step2Labels := by
      have hz : ∀ j, raw23023step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw23023step2 = (fun i j => raw23023step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw23023step2 raw23023step1; decide +kernel
      have hl : raw23023step2Labels = raw23023step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23023step1 raw23023step1Labels permutation20 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical23024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23024 raw23024Labels = mixedMoment B node932 node932Labels := by
  calc
    mixedMoment B raw23024 raw23024Labels = mixedMoment B raw23024step0 raw23024step0Labels := by
      have hz : ∀ j, raw23024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23024step0 = (fun i j => raw23024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23024step0 raw23024; decide +kernel
      have hl : raw23024step0Labels = raw23024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23024 raw23024Labels permutation434 hz
    mixedMoment B raw23024step0 raw23024step0Labels = mixedMoment B raw23024step1 raw23024step1Labels := by
      have ha : raw23024step1 = (fun i j => raw23024step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23024step1 raw23024step0; decide +kernel
      have hl : raw23024step1Labels = raw23024step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23024step0 raw23024step0Labels permutation39 permutation2
    _ = mixedMoment B node932 node932Labels := by rfl

theorem canonical23025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23025 raw23025Labels = mixedMoment B node932 node932Labels := by
  calc
    mixedMoment B raw23025 raw23025Labels = mixedMoment B raw23025step0 raw23025step0Labels := by
      have hz : ∀ j, raw23025 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23025step0 = (fun i j => raw23025 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23025step0 raw23025; decide +kernel
      have hl : raw23025step0Labels = raw23025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23025 raw23025Labels permutation346 hz
    mixedMoment B raw23025step0 raw23025step0Labels = mixedMoment B raw23025step1 raw23025step1Labels := by
      have ha : raw23025step1 = (fun i j => raw23025step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23025step1 raw23025step0; decide +kernel
      have hl : raw23025step1Labels = raw23025step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23025step0 raw23025step0Labels permutation39 permutation2
    _ = mixedMoment B node932 node932Labels := by rfl

theorem canonical23026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23026 raw23026Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw23026 raw23026Labels = mixedMoment B raw23026step0 raw23026step0Labels := by
      have hz : ∀ j, raw23026 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23026step0 = (fun i j => raw23026 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23026step0 raw23026; decide +kernel
      have hl : raw23026step0Labels = raw23026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23026 raw23026Labels permutation434 hz
    mixedMoment B raw23026step0 raw23026step0Labels = mixedMoment B raw23026step1 raw23026step1Labels := by
      have hz : ∀ j, raw23026step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23026step1 = (fun i j => raw23026step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23026step1 raw23026step0; decide +kernel
      have hl : raw23026step1Labels = raw23026step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23026step0 raw23026step0Labels permutation80 hz
    _ = mixedMoment B node1087 node1087Labels := by rfl

theorem canonical23027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23027 raw23027Labels = mixedMoment B node1082 node1082Labels := by
  calc
    mixedMoment B raw23027 raw23027Labels = mixedMoment B raw23027step0 raw23027step0Labels := by
      have hz : ∀ j, raw23027 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23027step0 = (fun i j => raw23027 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23027step0 raw23027; decide +kernel
      have hl : raw23027step0Labels = raw23027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23027 raw23027Labels permutation434 hz
    mixedMoment B raw23027step0 raw23027step0Labels = mixedMoment B raw23027step1 raw23027step1Labels := by
      have hz : ∀ j, raw23027step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23027step1 = (fun i j => raw23027step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23027step1 raw23027step0; decide +kernel
      have hl : raw23027step1Labels = raw23027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23027step0 raw23027step0Labels permutation80 hz
    mixedMoment B raw23027step1 raw23027step1Labels = mixedMoment B raw23027step2 raw23027step2Labels := by
      have ha : raw23027step2 = (fun i j => raw23027step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23027step2 raw23027step1; decide +kernel
      have hl : raw23027step2Labels = raw23027step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23027step1 raw23027step1Labels permutation12 permutation2
    _ = mixedMoment B node1082 node1082Labels := by rfl

theorem canonical23028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23028 raw23028Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw23028 raw23028Labels = mixedMoment B raw23028step0 raw23028step0Labels := by
      have hz : ∀ j, raw23028 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23028step0 = (fun i j => raw23028 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23028step0 raw23028; decide +kernel
      have hl : raw23028step0Labels = raw23028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23028 raw23028Labels permutation434 hz
    mixedMoment B raw23028step0 raw23028step0Labels = mixedMoment B raw23028step1 raw23028step1Labels := by
      have hz : ∀ j, raw23028step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23028step1 = (fun i j => raw23028step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23028step1 raw23028step0; decide +kernel
      have hl : raw23028step1Labels = raw23028step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23028step0 raw23028step0Labels permutation80 hz
    mixedMoment B raw23028step1 raw23028step1Labels = mixedMoment B raw23028step2 raw23028step2Labels := by
      have ha : raw23028step2 = (fun i j => raw23028step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23028step2 raw23028step1; decide +kernel
      have hl : raw23028step2Labels = raw23028step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23028step1 raw23028step1Labels permutation9 permutation2
    _ = mixedMoment B node2115 node2115Labels := by rfl

theorem canonical23029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23029 raw23029Labels = mixedMoment B node946 node946Labels := by
  calc
    mixedMoment B raw23029 raw23029Labels = mixedMoment B raw23029step0 raw23029step0Labels := by
      have hz : ∀ j, raw23029 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23029step0 = (fun i j => raw23029 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23029step0 raw23029; decide +kernel
      have hl : raw23029step0Labels = raw23029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23029 raw23029Labels permutation434 hz
    mixedMoment B raw23029step0 raw23029step0Labels = mixedMoment B raw23029step1 raw23029step1Labels := by
      have ha : raw23029step1 = (fun i j => raw23029step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23029step1 raw23029step0; decide +kernel
      have hl : raw23029step1Labels = raw23029step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23029step0 raw23029step0Labels permutation33 permutation2
    _ = mixedMoment B node946 node946Labels := by rfl

theorem canonical23030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23030 raw23030Labels = mixedMoment B node946 node946Labels := by
  calc
    mixedMoment B raw23030 raw23030Labels = mixedMoment B raw23030step0 raw23030step0Labels := by
      have hz : ∀ j, raw23030 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23030step0 = (fun i j => raw23030 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23030step0 raw23030; decide +kernel
      have hl : raw23030step0Labels = raw23030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23030 raw23030Labels permutation346 hz
    mixedMoment B raw23030step0 raw23030step0Labels = mixedMoment B raw23030step1 raw23030step1Labels := by
      have ha : raw23030step1 = (fun i j => raw23030step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23030step1 raw23030step0; decide +kernel
      have hl : raw23030step1Labels = raw23030step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23030step0 raw23030step0Labels permutation33 permutation2
    _ = mixedMoment B node946 node946Labels := by rfl

theorem canonical23031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23031 raw23031Labels = mixedMoment B node952 node952Labels := by
  calc
    mixedMoment B raw23031 raw23031Labels = mixedMoment B raw23031step0 raw23031step0Labels := by
      have hz : ∀ j, raw23031 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23031step0 = (fun i j => raw23031 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23031step0 raw23031; decide +kernel
      have hl : raw23031step0Labels = raw23031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23031 raw23031Labels permutation434 hz
    mixedMoment B raw23031step0 raw23031step0Labels = mixedMoment B raw23031step1 raw23031step1Labels := by
      have hz : ∀ j, raw23031step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23031step1 = (fun i j => raw23031step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23031step1 raw23031step0; decide +kernel
      have hl : raw23031step1Labels = raw23031step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23031step0 raw23031step0Labels permutation80 hz
    mixedMoment B raw23031step1 raw23031step1Labels = mixedMoment B raw23031step2 raw23031step2Labels := by
      have ha : raw23031step2 = (fun i j => raw23031step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23031step2 raw23031step1; decide +kernel
      have hl : raw23031step2Labels = raw23031step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23031step1 raw23031step1Labels permutation9 permutation2
    _ = mixedMoment B node952 node952Labels := by rfl

theorem canonical23032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23032 raw23032Labels = mixedMoment B node954 node954Labels := by
  calc
    mixedMoment B raw23032 raw23032Labels = mixedMoment B raw23032step0 raw23032step0Labels := by
      have hz : ∀ j, raw23032 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23032step0 = (fun i j => raw23032 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23032step0 raw23032; decide +kernel
      have hl : raw23032step0Labels = raw23032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23032 raw23032Labels permutation434 hz
    mixedMoment B raw23032step0 raw23032step0Labels = mixedMoment B raw23032step1 raw23032step1Labels := by
      have hz : ∀ j, raw23032step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23032step1 = (fun i j => raw23032step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23032step1 raw23032step0; decide +kernel
      have hl : raw23032step1Labels = raw23032step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23032step0 raw23032step0Labels permutation80 hz
    _ = mixedMoment B node954 node954Labels := by rfl

theorem canonical23033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23033 raw23033Labels = mixedMoment B node906 node906Labels := by
  calc
    mixedMoment B raw23033 raw23033Labels = mixedMoment B raw23033step0 raw23033step0Labels := by
      have ha : raw23033step0 = (fun i j => raw23033 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23033step0 raw23033; decide +kernel
      have hl : raw23033step0Labels = raw23033Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23033 raw23033Labels permutation201 permutation2
    _ = mixedMoment B node906 node906Labels := by rfl

theorem canonical23034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23034 raw23034Labels = mixedMoment B node1042 node1042Labels := by
  calc
    mixedMoment B raw23034 raw23034Labels = mixedMoment B raw23034step0 raw23034step0Labels := by
      have hz : ∀ j, raw23034 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23034step0 = (fun i j => raw23034 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23034step0 raw23034; decide +kernel
      have hl : raw23034step0Labels = raw23034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23034 raw23034Labels permutation434 hz
    _ = mixedMoment B node1042 node1042Labels := by rfl

theorem canonical23035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23035 raw23035Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw23035 raw23035Labels = mixedMoment B raw23035step0 raw23035step0Labels := by
      have hz : ∀ j, raw23035 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23035step0 = (fun i j => raw23035 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23035step0 raw23035; decide +kernel
      have hl : raw23035step0Labels = raw23035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23035 raw23035Labels permutation434 hz
    mixedMoment B raw23035step0 raw23035step0Labels = mixedMoment B raw23035step1 raw23035step1Labels := by
      have ha : raw23035step1 = (fun i j => raw23035step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23035step1 raw23035step0; decide +kernel
      have hl : raw23035step1Labels = raw23035step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23035step0 raw23035step0Labels permutation33 permutation2
    _ = mixedMoment B node1040 node1040Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical180
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23149 raw23149Labels = mixedMoment B node4186 node4186Labels := by
  calc
    mixedMoment B raw23149 raw23149Labels = mixedMoment B raw23149step0 raw23149step0Labels := by
      have hz : ∀ j, raw23149 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23149step0 = (fun i j => raw23149 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23149step0 raw23149; decide +kernel
      have hl : raw23149step0Labels = raw23149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23149 raw23149Labels permutation434 hz
    mixedMoment B raw23149step0 raw23149step0Labels = mixedMoment B raw23149step1 raw23149step1Labels := by
      have hz : ∀ j, raw23149step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23149step1 = (fun i j => raw23149step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23149step1 raw23149step0; decide +kernel
      have hl : raw23149step1Labels = raw23149step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23149step0 raw23149step0Labels permutation80 hz
    _ = mixedMoment B node4186 node4186Labels := by rfl

theorem canonical23150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23150 raw23150Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw23150 raw23150Labels = mixedMoment B raw23150step0 raw23150step0Labels := by
      have hz : ∀ j, raw23150 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23150step0 = (fun i j => raw23150 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23150step0 raw23150; decide +kernel
      have hl : raw23150step0Labels = raw23150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23150 raw23150Labels permutation434 hz
    mixedMoment B raw23150step0 raw23150step0Labels = mixedMoment B raw23150step1 raw23150step1Labels := by
      have ha : raw23150step1 = (fun i j => raw23150step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23150step1 raw23150step0; decide +kernel
      have hl : raw23150step1Labels = raw23150step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23150step0 raw23150step0Labels permutation38 permutation2
    _ = mixedMoment B node4355 node4355Labels := by rfl

theorem canonical23151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23151 raw23151Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw23151 raw23151Labels = mixedMoment B raw23151step0 raw23151step0Labels := by
      have hz : ∀ j, raw23151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23151step0 = (fun i j => raw23151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23151step0 raw23151; decide +kernel
      have hl : raw23151step0Labels = raw23151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23151 raw23151Labels permutation346 hz
    mixedMoment B raw23151step0 raw23151step0Labels = mixedMoment B raw23151step1 raw23151step1Labels := by
      have ha : raw23151step1 = (fun i j => raw23151step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23151step1 raw23151step0; decide +kernel
      have hl : raw23151step1Labels = raw23151step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23151step0 raw23151step0Labels permutation38 permutation2
    _ = mixedMoment B node4355 node4355Labels := by rfl

theorem canonical23152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23152 raw23152Labels = mixedMoment B node4502 node4502Labels := by
  calc
    mixedMoment B raw23152 raw23152Labels = mixedMoment B raw23152step0 raw23152step0Labels := by
      have hz : ∀ j, raw23152 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23152step0 = (fun i j => raw23152 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23152step0 raw23152; decide +kernel
      have hl : raw23152step0Labels = raw23152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23152 raw23152Labels permutation434 hz
    mixedMoment B raw23152step0 raw23152step0Labels = mixedMoment B raw23152step1 raw23152step1Labels := by
      have hz : ∀ j, raw23152step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23152step1 = (fun i j => raw23152step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23152step1 raw23152step0; decide +kernel
      have hl : raw23152step1Labels = raw23152step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23152step0 raw23152step0Labels permutation80 hz
    mixedMoment B raw23152step1 raw23152step1Labels = mixedMoment B raw23152step2 raw23152step2Labels := by
      have ha : raw23152step2 = (fun i j => raw23152step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23152step2 raw23152step1; decide +kernel
      have hl : raw23152step2Labels = raw23152step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23152step1 raw23152step1Labels permutation9 permutation2
    _ = mixedMoment B node4502 node4502Labels := by rfl

theorem canonical23153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23153 raw23153Labels = mixedMoment B node4155 node4155Labels := by
  calc
    mixedMoment B raw23153 raw23153Labels = mixedMoment B raw23153step0 raw23153step0Labels := by
      have hz : ∀ j, raw23153 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23153step0 = (fun i j => raw23153 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23153step0 raw23153; decide +kernel
      have hl : raw23153step0Labels = raw23153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23153 raw23153Labels permutation434 hz
    _ = mixedMoment B node4155 node4155Labels := by rfl

theorem canonical23154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23154 raw23154Labels = mixedMoment B node4369 node4369Labels := by
  calc
    mixedMoment B raw23154 raw23154Labels = mixedMoment B raw23154step0 raw23154step0Labels := by
      have hz : ∀ j, raw23154 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23154step0 = (fun i j => raw23154 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23154step0 raw23154; decide +kernel
      have hl : raw23154step0Labels = raw23154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23154 raw23154Labels permutation434 hz
    _ = mixedMoment B node4369 node4369Labels := by rfl

theorem canonical23155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23155 raw23155Labels = mixedMoment B node4329 node4329Labels := by
  calc
    mixedMoment B raw23155 raw23155Labels = mixedMoment B raw23155step0 raw23155step0Labels := by
      have ha : raw23155step0 = (fun i j => raw23155 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23155step0 raw23155; decide +kernel
      have hl : raw23155step0Labels = raw23155Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23155 raw23155Labels permutation200 permutation2
    _ = mixedMoment B node4329 node4329Labels := by rfl

theorem canonical23156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23156 raw23156Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw23156 raw23156Labels = mixedMoment B raw23156step0 raw23156step0Labels := by
      have hz : ∀ j, raw23156 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23156step0 = (fun i j => raw23156 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23156step0 raw23156; decide +kernel
      have hl : raw23156step0Labels = raw23156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23156 raw23156Labels permutation434 hz
    mixedMoment B raw23156step0 raw23156step0Labels = mixedMoment B raw23156step1 raw23156step1Labels := by
      have ha : raw23156step1 = (fun i j => raw23156step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23156step1 raw23156step0; decide +kernel
      have hl : raw23156step1Labels = raw23156step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23156step0 raw23156step0Labels permutation33 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical23157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23157 raw23157Labels = mixedMoment B node4155 node4155Labels := by
  calc
    mixedMoment B raw23157 raw23157Labels = mixedMoment B raw23157step0 raw23157step0Labels := by
      have hz : ∀ j, raw23157 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23157step0 = (fun i j => raw23157 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23157step0 raw23157; decide +kernel
      have hl : raw23157step0Labels = raw23157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23157 raw23157Labels permutation346 hz
    _ = mixedMoment B node4155 node4155Labels := by rfl

theorem canonical23158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23158 raw23158Labels = mixedMoment B node4369 node4369Labels := by
  calc
    mixedMoment B raw23158 raw23158Labels = mixedMoment B raw23158step0 raw23158step0Labels := by
      have hz : ∀ j, raw23158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23158step0 = (fun i j => raw23158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23158step0 raw23158; decide +kernel
      have hl : raw23158step0Labels = raw23158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23158 raw23158Labels permutation346 hz
    _ = mixedMoment B node4369 node4369Labels := by rfl

theorem canonical23159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23159 raw23159Labels = mixedMoment B node4329 node4329Labels := by
  calc
    mixedMoment B raw23159 raw23159Labels = mixedMoment B raw23159step0 raw23159step0Labels := by
      have ha : raw23159step0 = (fun i j => raw23159 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23159step0 raw23159; decide +kernel
      have hl : raw23159step0Labels = raw23159Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23159 raw23159Labels permutation176 permutation2
    _ = mixedMoment B node4329 node4329Labels := by rfl

theorem canonical23160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23160 raw23160Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw23160 raw23160Labels = mixedMoment B raw23160step0 raw23160step0Labels := by
      have hz : ∀ j, raw23160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23160step0 = (fun i j => raw23160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23160step0 raw23160; decide +kernel
      have hl : raw23160step0Labels = raw23160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23160 raw23160Labels permutation346 hz
    mixedMoment B raw23160step0 raw23160step0Labels = mixedMoment B raw23160step1 raw23160step1Labels := by
      have ha : raw23160step1 = (fun i j => raw23160step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23160step1 raw23160step0; decide +kernel
      have hl : raw23160step1Labels = raw23160step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23160step0 raw23160step0Labels permutation33 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical23161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23161 raw23161Labels = mixedMoment B node4161 node4161Labels := by
  calc
    mixedMoment B raw23161 raw23161Labels = mixedMoment B raw23161step0 raw23161step0Labels := by
      have hz : ∀ j, raw23161 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23161step0 = (fun i j => raw23161 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23161step0 raw23161; decide +kernel
      have hl : raw23161step0Labels = raw23161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23161 raw23161Labels permutation434 hz
    mixedMoment B raw23161step0 raw23161step0Labels = mixedMoment B raw23161step1 raw23161step1Labels := by
      have hz : ∀ j, raw23161step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23161step1 = (fun i j => raw23161step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23161step1 raw23161step0; decide +kernel
      have hl : raw23161step1Labels = raw23161step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23161step0 raw23161step0Labels permutation80 hz
    mixedMoment B raw23161step1 raw23161step1Labels = mixedMoment B raw23161step2 raw23161step2Labels := by
      have ha : raw23161step2 = (fun i j => raw23161step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23161step2 raw23161step1; decide +kernel
      have hl : raw23161step2Labels = raw23161step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23161step1 raw23161step1Labels permutation9 permutation2
    _ = mixedMoment B node4161 node4161Labels := by rfl

theorem canonical23162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23162 raw23162Labels = mixedMoment B node4374 node4374Labels := by
  calc
    mixedMoment B raw23162 raw23162Labels = mixedMoment B raw23162step0 raw23162step0Labels := by
      have hz : ∀ j, raw23162 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23162step0 = (fun i j => raw23162 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23162step0 raw23162; decide +kernel
      have hl : raw23162step0Labels = raw23162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23162 raw23162Labels permutation434 hz
    mixedMoment B raw23162step0 raw23162step0Labels = mixedMoment B raw23162step1 raw23162step1Labels := by
      have hz : ∀ j, raw23162step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23162step1 = (fun i j => raw23162step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23162step1 raw23162step0; decide +kernel
      have hl : raw23162step1Labels = raw23162step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23162step0 raw23162step0Labels permutation80 hz
    mixedMoment B raw23162step1 raw23162step1Labels = mixedMoment B raw23162step2 raw23162step2Labels := by
      have ha : raw23162step2 = (fun i j => raw23162step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23162step2 raw23162step1; decide +kernel
      have hl : raw23162step2Labels = raw23162step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23162step1 raw23162step1Labels permutation9 permutation2
    _ = mixedMoment B node4374 node4374Labels := by rfl

theorem canonical23163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23163 raw23163Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw23163 raw23163Labels = mixedMoment B raw23163step0 raw23163step0Labels := by
      have hz : ∀ j, raw23163 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23163step0 = (fun i j => raw23163 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23163step0 raw23163; decide +kernel
      have hl : raw23163step0Labels = raw23163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23163 raw23163Labels permutation434 hz
    mixedMoment B raw23163step0 raw23163step0Labels = mixedMoment B raw23163step1 raw23163step1Labels := by
      have ha : raw23163step1 = (fun i j => raw23163step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23163step1 raw23163step0; decide +kernel
      have hl : raw23163step1Labels = raw23163step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23163step0 raw23163step0Labels permutation39 permutation2
    _ = mixedMoment B node4335 node4335Labels := by rfl

theorem canonical23164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23164 raw23164Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw23164 raw23164Labels = mixedMoment B raw23164step0 raw23164step0Labels := by
      have hz : ∀ j, raw23164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23164step0 = (fun i j => raw23164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23164step0 raw23164; decide +kernel
      have hl : raw23164step0Labels = raw23164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23164 raw23164Labels permutation346 hz
    mixedMoment B raw23164step0 raw23164step0Labels = mixedMoment B raw23164step1 raw23164step1Labels := by
      have ha : raw23164step1 = (fun i j => raw23164step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23164step1 raw23164step0; decide +kernel
      have hl : raw23164step1Labels = raw23164step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23164step0 raw23164step0Labels permutation39 permutation2
    _ = mixedMoment B node4335 node4335Labels := by rfl

theorem canonical23165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23165 raw23165Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw23165 raw23165Labels = mixedMoment B raw23165step0 raw23165step0Labels := by
      have hz : ∀ j, raw23165 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23165step0 = (fun i j => raw23165 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23165step0 raw23165; decide +kernel
      have hl : raw23165step0Labels = raw23165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23165 raw23165Labels permutation434 hz
    mixedMoment B raw23165step0 raw23165step0Labels = mixedMoment B raw23165step1 raw23165step1Labels := by
      have hz : ∀ j, raw23165step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23165step1 = (fun i j => raw23165step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23165step1 raw23165step0; decide +kernel
      have hl : raw23165step1Labels = raw23165step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23165step0 raw23165step0Labels permutation80 hz
    mixedMoment B raw23165step1 raw23165step1Labels = mixedMoment B raw23165step2 raw23165step2Labels := by
      have ha : raw23165step2 = (fun i j => raw23165step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23165step2 raw23165step1; decide +kernel
      have hl : raw23165step2Labels = raw23165step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23165step1 raw23165step1Labels permutation9 permutation2
    _ = mixedMoment B node4463 node4463Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical181
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23188 raw23188Labels = mixedMoment B node1536 node1536Labels := by
  calc
    mixedMoment B raw23188 raw23188Labels = mixedMoment B raw23188step0 raw23188step0Labels := by
      have hz : ∀ j, raw23188 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23188step0 = (fun i j => raw23188 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23188step0 raw23188; decide +kernel
      have hl : raw23188step0Labels = raw23188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23188 raw23188Labels permutation434 hz
    mixedMoment B raw23188step0 raw23188step0Labels = mixedMoment B raw23188step1 raw23188step1Labels := by
      have hz : ∀ j, raw23188step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23188step1 = (fun i j => raw23188step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23188step1 raw23188step0; decide +kernel
      have hl : raw23188step1Labels = raw23188step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23188step0 raw23188step0Labels permutation80 hz
    mixedMoment B raw23188step1 raw23188step1Labels = mixedMoment B raw23188step2 raw23188step2Labels := by
      have ha : raw23188step2 = (fun i j => raw23188step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23188step2 raw23188step1; decide +kernel
      have hl : raw23188step2Labels = raw23188step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23188step1 raw23188step1Labels permutation8 permutation7
    mixedMoment B raw23188step2 raw23188step2Labels = mixedMoment B raw23188step3 raw23188step3Labels := by
      have ha : raw23188step3 = -raw23188step2 := by apply Matrix.ext; change ∀ i j, raw23188step3 i j = -(raw23188step2 i j); unfold raw23188step3 raw23188step2; decide +kernel
      have hl : raw23188step3Labels = raw23188step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23188step3 raw23188step3Labels = mixedMoment B raw23188step4 raw23188step4Labels := by
      have ha : raw23188step4 = raw23188step3 := by apply Matrix.ext; unfold raw23188step4 raw23188step3; decide +kernel
      have hl : raw23188step3Labels = labelEmbedding1 ∘ raw23188step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23188step3 raw23188step3Labels raw23188step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1536 node1536Labels := by rfl

theorem canonical23189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23189 raw23189Labels = mixedMoment B node1691 node1691Labels := by
  calc
    mixedMoment B raw23189 raw23189Labels = mixedMoment B raw23189step0 raw23189step0Labels := by
      have hz : ∀ j, raw23189 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23189step0 = (fun i j => raw23189 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23189step0 raw23189; decide +kernel
      have hl : raw23189step0Labels = raw23189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23189 raw23189Labels permutation434 hz
    mixedMoment B raw23189step0 raw23189step0Labels = mixedMoment B raw23189step1 raw23189step1Labels := by
      have ha : raw23189step1 = (fun i j => raw23189step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23189step1 raw23189step0; decide +kernel
      have hl : raw23189step1Labels = raw23189step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23189step0 raw23189step0Labels permutation38 permutation7
    mixedMoment B raw23189step1 raw23189step1Labels = mixedMoment B raw23189step2 raw23189step2Labels := by
      have ha : raw23189step2 = -raw23189step1 := by apply Matrix.ext; change ∀ i j, raw23189step2 i j = -(raw23189step1 i j); unfold raw23189step2 raw23189step1; decide +kernel
      have hl : raw23189step2Labels = raw23189step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23189step2 raw23189step2Labels = mixedMoment B raw23189step3 raw23189step3Labels := by
      have ha : raw23189step3 = raw23189step2 := by apply Matrix.ext; unfold raw23189step3 raw23189step2; decide +kernel
      have hl : raw23189step2Labels = labelEmbedding1 ∘ raw23189step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23189step2 raw23189step2Labels raw23189step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1691 node1691Labels := by rfl

theorem canonical23190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23190 raw23190Labels = mixedMoment B node1691 node1691Labels := by
  calc
    mixedMoment B raw23190 raw23190Labels = mixedMoment B raw23190step0 raw23190step0Labels := by
      have hz : ∀ j, raw23190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23190step0 = (fun i j => raw23190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23190step0 raw23190; decide +kernel
      have hl : raw23190step0Labels = raw23190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23190 raw23190Labels permutation346 hz
    mixedMoment B raw23190step0 raw23190step0Labels = mixedMoment B raw23190step1 raw23190step1Labels := by
      have ha : raw23190step1 = (fun i j => raw23190step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23190step1 raw23190step0; decide +kernel
      have hl : raw23190step1Labels = raw23190step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23190step0 raw23190step0Labels permutation38 permutation7
    mixedMoment B raw23190step1 raw23190step1Labels = mixedMoment B raw23190step2 raw23190step2Labels := by
      have ha : raw23190step2 = -raw23190step1 := by apply Matrix.ext; change ∀ i j, raw23190step2 i j = -(raw23190step1 i j); unfold raw23190step2 raw23190step1; decide +kernel
      have hl : raw23190step2Labels = raw23190step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23190step2 raw23190step2Labels = mixedMoment B raw23190step3 raw23190step3Labels := by
      have ha : raw23190step3 = raw23190step2 := by apply Matrix.ext; unfold raw23190step3 raw23190step2; decide +kernel
      have hl : raw23190step2Labels = labelEmbedding1 ∘ raw23190step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23190step2 raw23190step2Labels raw23190step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1691 node1691Labels := by rfl

theorem canonical23191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23191 raw23191Labels = mixedMoment B node1753 node1753Labels := by
  calc
    mixedMoment B raw23191 raw23191Labels = mixedMoment B raw23191step0 raw23191step0Labels := by
      have hz : ∀ j, raw23191 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23191step0 = (fun i j => raw23191 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23191step0 raw23191; decide +kernel
      have hl : raw23191step0Labels = raw23191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23191 raw23191Labels permutation434 hz
    mixedMoment B raw23191step0 raw23191step0Labels = mixedMoment B raw23191step1 raw23191step1Labels := by
      have hz : ∀ j, raw23191step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23191step1 = (fun i j => raw23191step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23191step1 raw23191step0; decide +kernel
      have hl : raw23191step1Labels = raw23191step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23191step0 raw23191step0Labels permutation80 hz
    mixedMoment B raw23191step1 raw23191step1Labels = mixedMoment B raw23191step2 raw23191step2Labels := by
      have ha : raw23191step2 = (fun i j => raw23191step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23191step2 raw23191step1; decide +kernel
      have hl : raw23191step2Labels = raw23191step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23191step1 raw23191step1Labels permutation9 permutation7
    mixedMoment B raw23191step2 raw23191step2Labels = mixedMoment B raw23191step3 raw23191step3Labels := by
      have ha : raw23191step3 = -raw23191step2 := by apply Matrix.ext; change ∀ i j, raw23191step3 i j = -(raw23191step2 i j); unfold raw23191step3 raw23191step2; decide +kernel
      have hl : raw23191step3Labels = raw23191step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23191step3 raw23191step3Labels = mixedMoment B raw23191step4 raw23191step4Labels := by
      have ha : raw23191step4 = raw23191step3 := by apply Matrix.ext; unfold raw23191step4 raw23191step3; decide +kernel
      have hl : raw23191step3Labels = labelEmbedding1 ∘ raw23191step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23191step3 raw23191step3Labels raw23191step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1753 node1753Labels := by rfl

theorem canonical23192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23192 raw23192Labels = mixedMoment B node1515 node1515Labels := by
  calc
    mixedMoment B raw23192 raw23192Labels = mixedMoment B raw23192step0 raw23192step0Labels := by
      have hz : ∀ j, raw23192 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23192step0 = (fun i j => raw23192 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23192step0 raw23192; decide +kernel
      have hl : raw23192step0Labels = raw23192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23192 raw23192Labels permutation434 hz
    mixedMoment B raw23192step0 raw23192step0Labels = mixedMoment B raw23192step1 raw23192step1Labels := by
      have ha : raw23192step1 = (fun i j => raw23192step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23192step1 raw23192step0; decide +kernel
      have hl : raw23192step1Labels = raw23192step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23192step0 raw23192step0Labels permutation38 permutation7
    mixedMoment B raw23192step1 raw23192step1Labels = mixedMoment B raw23192step2 raw23192step2Labels := by
      have ha : raw23192step2 = -raw23192step1 := by apply Matrix.ext; change ∀ i j, raw23192step2 i j = -(raw23192step1 i j); unfold raw23192step2 raw23192step1; decide +kernel
      have hl : raw23192step2Labels = raw23192step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23192step2 raw23192step2Labels = mixedMoment B raw23192step3 raw23192step3Labels := by
      have ha : raw23192step3 = raw23192step2 := by apply Matrix.ext; unfold raw23192step3 raw23192step2; decide +kernel
      have hl : raw23192step2Labels = labelEmbedding1 ∘ raw23192step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23192step2 raw23192step2Labels raw23192step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1515 node1515Labels := by rfl

theorem canonical23193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23193 raw23193Labels = mixedMoment B node1721 node1721Labels := by
  calc
    mixedMoment B raw23193 raw23193Labels = mixedMoment B raw23193step0 raw23193step0Labels := by
      have hz : ∀ j, raw23193 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23193step0 = (fun i j => raw23193 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23193step0 raw23193; decide +kernel
      have hl : raw23193step0Labels = raw23193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23193 raw23193Labels permutation434 hz
    mixedMoment B raw23193step0 raw23193step0Labels = mixedMoment B raw23193step1 raw23193step1Labels := by
      have ha : raw23193step1 = (fun i j => raw23193step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23193step1 raw23193step0; decide +kernel
      have hl : raw23193step1Labels = raw23193step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23193step0 raw23193step0Labels permutation38 permutation7
    mixedMoment B raw23193step1 raw23193step1Labels = mixedMoment B raw23193step2 raw23193step2Labels := by
      have ha : raw23193step2 = -raw23193step1 := by apply Matrix.ext; change ∀ i j, raw23193step2 i j = -(raw23193step1 i j); unfold raw23193step2 raw23193step1; decide +kernel
      have hl : raw23193step2Labels = raw23193step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23193step2 raw23193step2Labels = mixedMoment B raw23193step3 raw23193step3Labels := by
      have ha : raw23193step3 = raw23193step2 := by apply Matrix.ext; unfold raw23193step3 raw23193step2; decide +kernel
      have hl : raw23193step2Labels = labelEmbedding1 ∘ raw23193step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23193step2 raw23193step2Labels raw23193step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1721 node1721Labels := by rfl

theorem canonical23194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23194 raw23194Labels = mixedMoment B node1671 node1671Labels := by
  calc
    mixedMoment B raw23194 raw23194Labels = mixedMoment B raw23194step0 raw23194step0Labels := by
      have ha : raw23194step0 = (fun i j => raw23194 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23194step0 raw23194; decide +kernel
      have hl : raw23194step0Labels = raw23194Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23194 raw23194Labels permutation206 permutation7
    mixedMoment B raw23194step0 raw23194step0Labels = mixedMoment B raw23194step1 raw23194step1Labels := by
      have ha : raw23194step1 = -raw23194step0 := by apply Matrix.ext; change ∀ i j, raw23194step1 i j = -(raw23194step0 i j); unfold raw23194step1 raw23194step0; decide +kernel
      have hl : raw23194step1Labels = raw23194step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23194step1 raw23194step1Labels = mixedMoment B raw23194step2 raw23194step2Labels := by
      have ha : raw23194step2 = raw23194step1 := by apply Matrix.ext; unfold raw23194step2 raw23194step1; decide +kernel
      have hl : raw23194step1Labels = labelEmbedding1 ∘ raw23194step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23194step1 raw23194step1Labels raw23194step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1671 node1671Labels := by rfl

theorem canonical23195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23195 raw23195Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw23195 raw23195Labels = mixedMoment B raw23195step0 raw23195step0Labels := by
      have hz : ∀ j, raw23195 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23195step0 = (fun i j => raw23195 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23195step0 raw23195; decide +kernel
      have hl : raw23195step0Labels = raw23195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23195 raw23195Labels permutation434 hz
    mixedMoment B raw23195step0 raw23195step0Labels = mixedMoment B raw23195step1 raw23195step1Labels := by
      have ha : raw23195step1 = (fun i j => raw23195step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23195step1 raw23195step0; decide +kernel
      have hl : raw23195step1Labels = raw23195step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23195step0 raw23195step0Labels permutation39 permutation7
    mixedMoment B raw23195step1 raw23195step1Labels = mixedMoment B raw23195step2 raw23195step2Labels := by
      have ha : raw23195step2 = -raw23195step1 := by apply Matrix.ext; change ∀ i j, raw23195step2 i j = -(raw23195step1 i j); unfold raw23195step2 raw23195step1; decide +kernel
      have hl : raw23195step2Labels = raw23195step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23195step2 raw23195step2Labels = mixedMoment B raw23195step3 raw23195step3Labels := by
      have ha : raw23195step3 = raw23195step2 := by apply Matrix.ext; unfold raw23195step3 raw23195step2; decide +kernel
      have hl : raw23195step2Labels = labelEmbedding1 ∘ raw23195step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23195step2 raw23195step2Labels raw23195step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical23196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23196 raw23196Labels = mixedMoment B node1515 node1515Labels := by
  calc
    mixedMoment B raw23196 raw23196Labels = mixedMoment B raw23196step0 raw23196step0Labels := by
      have hz : ∀ j, raw23196 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23196step0 = (fun i j => raw23196 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23196step0 raw23196; decide +kernel
      have hl : raw23196step0Labels = raw23196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23196 raw23196Labels permutation346 hz
    mixedMoment B raw23196step0 raw23196step0Labels = mixedMoment B raw23196step1 raw23196step1Labels := by
      have ha : raw23196step1 = (fun i j => raw23196step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23196step1 raw23196step0; decide +kernel
      have hl : raw23196step1Labels = raw23196step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23196step0 raw23196step0Labels permutation38 permutation7
    mixedMoment B raw23196step1 raw23196step1Labels = mixedMoment B raw23196step2 raw23196step2Labels := by
      have ha : raw23196step2 = -raw23196step1 := by apply Matrix.ext; change ∀ i j, raw23196step2 i j = -(raw23196step1 i j); unfold raw23196step2 raw23196step1; decide +kernel
      have hl : raw23196step2Labels = raw23196step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23196step2 raw23196step2Labels = mixedMoment B raw23196step3 raw23196step3Labels := by
      have ha : raw23196step3 = raw23196step2 := by apply Matrix.ext; unfold raw23196step3 raw23196step2; decide +kernel
      have hl : raw23196step2Labels = labelEmbedding1 ∘ raw23196step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23196step2 raw23196step2Labels raw23196step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1515 node1515Labels := by rfl

theorem canonical23197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23197 raw23197Labels = mixedMoment B node1721 node1721Labels := by
  calc
    mixedMoment B raw23197 raw23197Labels = mixedMoment B raw23197step0 raw23197step0Labels := by
      have hz : ∀ j, raw23197 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23197step0 = (fun i j => raw23197 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23197step0 raw23197; decide +kernel
      have hl : raw23197step0Labels = raw23197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23197 raw23197Labels permutation346 hz
    mixedMoment B raw23197step0 raw23197step0Labels = mixedMoment B raw23197step1 raw23197step1Labels := by
      have ha : raw23197step1 = (fun i j => raw23197step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23197step1 raw23197step0; decide +kernel
      have hl : raw23197step1Labels = raw23197step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23197step0 raw23197step0Labels permutation38 permutation7
    mixedMoment B raw23197step1 raw23197step1Labels = mixedMoment B raw23197step2 raw23197step2Labels := by
      have ha : raw23197step2 = -raw23197step1 := by apply Matrix.ext; change ∀ i j, raw23197step2 i j = -(raw23197step1 i j); unfold raw23197step2 raw23197step1; decide +kernel
      have hl : raw23197step2Labels = raw23197step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23197step2 raw23197step2Labels = mixedMoment B raw23197step3 raw23197step3Labels := by
      have ha : raw23197step3 = raw23197step2 := by apply Matrix.ext; unfold raw23197step3 raw23197step2; decide +kernel
      have hl : raw23197step2Labels = labelEmbedding1 ∘ raw23197step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23197step2 raw23197step2Labels raw23197step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1721 node1721Labels := by rfl

theorem canonical23198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23198 raw23198Labels = mixedMoment B node1671 node1671Labels := by
  calc
    mixedMoment B raw23198 raw23198Labels = mixedMoment B raw23198step0 raw23198step0Labels := by
      have ha : raw23198step0 = (fun i j => raw23198 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23198step0 raw23198; decide +kernel
      have hl : raw23198step0Labels = raw23198Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23198 raw23198Labels permutation182 permutation7
    mixedMoment B raw23198step0 raw23198step0Labels = mixedMoment B raw23198step1 raw23198step1Labels := by
      have ha : raw23198step1 = -raw23198step0 := by apply Matrix.ext; change ∀ i j, raw23198step1 i j = -(raw23198step0 i j); unfold raw23198step1 raw23198step0; decide +kernel
      have hl : raw23198step1Labels = raw23198step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23198step1 raw23198step1Labels = mixedMoment B raw23198step2 raw23198step2Labels := by
      have ha : raw23198step2 = raw23198step1 := by apply Matrix.ext; unfold raw23198step2 raw23198step1; decide +kernel
      have hl : raw23198step1Labels = labelEmbedding1 ∘ raw23198step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23198step1 raw23198step1Labels raw23198step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1671 node1671Labels := by rfl

theorem canonical23199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23199 raw23199Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw23199 raw23199Labels = mixedMoment B raw23199step0 raw23199step0Labels := by
      have hz : ∀ j, raw23199 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23199step0 = (fun i j => raw23199 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23199step0 raw23199; decide +kernel
      have hl : raw23199step0Labels = raw23199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23199 raw23199Labels permutation346 hz
    mixedMoment B raw23199step0 raw23199step0Labels = mixedMoment B raw23199step1 raw23199step1Labels := by
      have ha : raw23199step1 = (fun i j => raw23199step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23199step1 raw23199step0; decide +kernel
      have hl : raw23199step1Labels = raw23199step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23199step0 raw23199step0Labels permutation39 permutation7
    mixedMoment B raw23199step1 raw23199step1Labels = mixedMoment B raw23199step2 raw23199step2Labels := by
      have ha : raw23199step2 = -raw23199step1 := by apply Matrix.ext; change ∀ i j, raw23199step2 i j = -(raw23199step1 i j); unfold raw23199step2 raw23199step1; decide +kernel
      have hl : raw23199step2Labels = raw23199step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23199step2 raw23199step2Labels = mixedMoment B raw23199step3 raw23199step3Labels := by
      have ha : raw23199step3 = raw23199step2 := by apply Matrix.ext; unfold raw23199step3 raw23199step2; decide +kernel
      have hl : raw23199step2Labels = labelEmbedding1 ∘ raw23199step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23199step2 raw23199step2Labels raw23199step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical23200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23200 raw23200Labels = mixedMoment B node1533 node1533Labels := by
  calc
    mixedMoment B raw23200 raw23200Labels = mixedMoment B raw23200step0 raw23200step0Labels := by
      have hz : ∀ j, raw23200 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23200step0 = (fun i j => raw23200 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23200step0 raw23200; decide +kernel
      have hl : raw23200step0Labels = raw23200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23200 raw23200Labels permutation434 hz
    mixedMoment B raw23200step0 raw23200step0Labels = mixedMoment B raw23200step1 raw23200step1Labels := by
      have hz : ∀ j, raw23200step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23200step1 = (fun i j => raw23200step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23200step1 raw23200step0; decide +kernel
      have hl : raw23200step1Labels = raw23200step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23200step0 raw23200step0Labels permutation80 hz
    mixedMoment B raw23200step1 raw23200step1Labels = mixedMoment B raw23200step2 raw23200step2Labels := by
      have ha : raw23200step2 = (fun i j => raw23200step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23200step2 raw23200step1; decide +kernel
      have hl : raw23200step2Labels = raw23200step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23200step1 raw23200step1Labels permutation9 permutation7
    mixedMoment B raw23200step2 raw23200step2Labels = mixedMoment B raw23200step3 raw23200step3Labels := by
      have ha : raw23200step3 = -raw23200step2 := by apply Matrix.ext; change ∀ i j, raw23200step3 i j = -(raw23200step2 i j); unfold raw23200step3 raw23200step2; decide +kernel
      have hl : raw23200step3Labels = raw23200step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23200step3 raw23200step3Labels = mixedMoment B raw23200step4 raw23200step4Labels := by
      have ha : raw23200step4 = raw23200step3 := by apply Matrix.ext; unfold raw23200step4 raw23200step3; decide +kernel
      have hl : raw23200step3Labels = labelEmbedding1 ∘ raw23200step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23200step3 raw23200step3Labels raw23200step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1533 node1533Labels := by rfl

theorem canonical23201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23201 raw23201Labels = mixedMoment B node1748 node1748Labels := by
  calc
    mixedMoment B raw23201 raw23201Labels = mixedMoment B raw23201step0 raw23201step0Labels := by
      have hz : ∀ j, raw23201 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23201step0 = (fun i j => raw23201 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23201step0 raw23201; decide +kernel
      have hl : raw23201step0Labels = raw23201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23201 raw23201Labels permutation434 hz
    mixedMoment B raw23201step0 raw23201step0Labels = mixedMoment B raw23201step1 raw23201step1Labels := by
      have hz : ∀ j, raw23201step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23201step1 = (fun i j => raw23201step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23201step1 raw23201step0; decide +kernel
      have hl : raw23201step1Labels = raw23201step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23201step0 raw23201step0Labels permutation80 hz
    mixedMoment B raw23201step1 raw23201step1Labels = mixedMoment B raw23201step2 raw23201step2Labels := by
      have ha : raw23201step2 = (fun i j => raw23201step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23201step2 raw23201step1; decide +kernel
      have hl : raw23201step2Labels = raw23201step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23201step1 raw23201step1Labels permutation9 permutation7
    mixedMoment B raw23201step2 raw23201step2Labels = mixedMoment B raw23201step3 raw23201step3Labels := by
      have ha : raw23201step3 = -raw23201step2 := by apply Matrix.ext; change ∀ i j, raw23201step3 i j = -(raw23201step2 i j); unfold raw23201step3 raw23201step2; decide +kernel
      have hl : raw23201step3Labels = raw23201step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23201step3 raw23201step3Labels = mixedMoment B raw23201step4 raw23201step4Labels := by
      have ha : raw23201step4 = raw23201step3 := by apply Matrix.ext; unfold raw23201step4 raw23201step3; decide +kernel
      have hl : raw23201step3Labels = labelEmbedding1 ∘ raw23201step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23201step3 raw23201step3Labels raw23201step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1748 node1748Labels := by rfl

theorem canonical23202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23202 raw23202Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw23202 raw23202Labels = mixedMoment B raw23202step0 raw23202step0Labels := by
      have hz : ∀ j, raw23202 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23202step0 = (fun i j => raw23202 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23202step0 raw23202; decide +kernel
      have hl : raw23202step0Labels = raw23202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23202 raw23202Labels permutation434 hz
    mixedMoment B raw23202step0 raw23202step0Labels = mixedMoment B raw23202step1 raw23202step1Labels := by
      have ha : raw23202step1 = (fun i j => raw23202step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23202step1 raw23202step0; decide +kernel
      have hl : raw23202step1Labels = raw23202step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23202step0 raw23202step0Labels permutation39 permutation7
    mixedMoment B raw23202step1 raw23202step1Labels = mixedMoment B raw23202step2 raw23202step2Labels := by
      have ha : raw23202step2 = -raw23202step1 := by apply Matrix.ext; change ∀ i j, raw23202step2 i j = -(raw23202step1 i j); unfold raw23202step2 raw23202step1; decide +kernel
      have hl : raw23202step2Labels = raw23202step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23202step2 raw23202step2Labels = mixedMoment B raw23202step3 raw23202step3Labels := by
      have ha : raw23202step3 = raw23202step2 := by apply Matrix.ext; unfold raw23202step3 raw23202step2; decide +kernel
      have hl : raw23202step2Labels = labelEmbedding1 ∘ raw23202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23202step2 raw23202step2Labels raw23202step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

theorem canonical23203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23203 raw23203Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw23203 raw23203Labels = mixedMoment B raw23203step0 raw23203step0Labels := by
      have hz : ∀ j, raw23203 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23203step0 = (fun i j => raw23203 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23203step0 raw23203; decide +kernel
      have hl : raw23203step0Labels = raw23203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23203 raw23203Labels permutation346 hz
    mixedMoment B raw23203step0 raw23203step0Labels = mixedMoment B raw23203step1 raw23203step1Labels := by
      have ha : raw23203step1 = (fun i j => raw23203step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23203step1 raw23203step0; decide +kernel
      have hl : raw23203step1Labels = raw23203step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23203step0 raw23203step0Labels permutation39 permutation7
    mixedMoment B raw23203step1 raw23203step1Labels = mixedMoment B raw23203step2 raw23203step2Labels := by
      have ha : raw23203step2 = -raw23203step1 := by apply Matrix.ext; change ∀ i j, raw23203step2 i j = -(raw23203step1 i j); unfold raw23203step2 raw23203step1; decide +kernel
      have hl : raw23203step2Labels = raw23203step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23203step2 raw23203step2Labels = mixedMoment B raw23203step3 raw23203step3Labels := by
      have ha : raw23203step3 = raw23203step2 := by apply Matrix.ext; unfold raw23203step3 raw23203step2; decide +kernel
      have hl : raw23203step2Labels = labelEmbedding1 ∘ raw23203step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23203step2 raw23203step2Labels raw23203step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

theorem canonical23204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23204 raw23204Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw23204 raw23204Labels = mixedMoment B raw23204step0 raw23204step0Labels := by
      have hz : ∀ j, raw23204 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23204step0 = (fun i j => raw23204 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23204step0 raw23204; decide +kernel
      have hl : raw23204step0Labels = raw23204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23204 raw23204Labels permutation434 hz
    mixedMoment B raw23204step0 raw23204step0Labels = mixedMoment B raw23204step1 raw23204step1Labels := by
      have hz : ∀ j, raw23204step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23204step1 = (fun i j => raw23204step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23204step1 raw23204step0; decide +kernel
      have hl : raw23204step1Labels = raw23204step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23204step0 raw23204step0Labels permutation80 hz
    mixedMoment B raw23204step1 raw23204step1Labels = mixedMoment B raw23204step2 raw23204step2Labels := by
      have ha : raw23204step2 = (fun i j => raw23204step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23204step2 raw23204step1; decide +kernel
      have hl : raw23204step2Labels = raw23204step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23204step1 raw23204step1Labels permutation9 permutation7
    mixedMoment B raw23204step2 raw23204step2Labels = mixedMoment B raw23204step3 raw23204step3Labels := by
      have ha : raw23204step3 = -raw23204step2 := by apply Matrix.ext; change ∀ i j, raw23204step3 i j = -(raw23204step2 i j); unfold raw23204step3 raw23204step2; decide +kernel
      have hl : raw23204step3Labels = raw23204step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23204step3 raw23204step3Labels = mixedMoment B raw23204step4 raw23204step4Labels := by
      have ha : raw23204step4 = raw23204step3 := by apply Matrix.ext; unfold raw23204step4 raw23204step3; decide +kernel
      have hl : raw23204step3Labels = labelEmbedding1 ∘ raw23204step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23204step3 raw23204step3Labels raw23204step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

theorem canonical23205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23205 raw23205Labels = mixedMoment B node1050 node1050Labels := by
  calc
    mixedMoment B raw23205 raw23205Labels = mixedMoment B raw23205step0 raw23205step0Labels := by
      have hz : ∀ j, raw23205 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23205step0 = (fun i j => raw23205 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23205step0 raw23205; decide +kernel
      have hl : raw23205step0Labels = raw23205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23205 raw23205Labels permutation434 hz
    mixedMoment B raw23205step0 raw23205step0Labels = mixedMoment B raw23205step1 raw23205step1Labels := by
      have hz : ∀ j, raw23205step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23205step1 = (fun i j => raw23205step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23205step1 raw23205step0; decide +kernel
      have hl : raw23205step1Labels = raw23205step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23205step0 raw23205step0Labels permutation80 hz
    _ = mixedMoment B node1050 node1050Labels := by rfl

theorem canonical23206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23206 raw23206Labels = mixedMoment B node614 node614Labels := by
  calc
    mixedMoment B raw23206 raw23206Labels = mixedMoment B raw23206step0 raw23206step0Labels := by
      have hz : ∀ j, raw23206 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23206step0 = (fun i j => raw23206 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23206step0 raw23206; decide +kernel
      have hl : raw23206step0Labels = raw23206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23206 raw23206Labels permutation434 hz
    mixedMoment B raw23206step0 raw23206step0Labels = mixedMoment B raw23206step1 raw23206step1Labels := by
      have hz : ∀ j, raw23206step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23206step1 = (fun i j => raw23206step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23206step1 raw23206step0; decide +kernel
      have hl : raw23206step1Labels = raw23206step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23206step0 raw23206step0Labels permutation80 hz
    _ = mixedMoment B node614 node614Labels := by rfl

theorem canonical23207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23207 raw23207Labels = mixedMoment B node583 node583Labels := by
  calc
    mixedMoment B raw23207 raw23207Labels = mixedMoment B raw23207step0 raw23207step0Labels := by
      have hz : ∀ j, raw23207 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23207step0 = (fun i j => raw23207 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23207step0 raw23207; decide +kernel
      have hl : raw23207step0Labels = raw23207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23207 raw23207Labels permutation434 hz
    _ = mixedMoment B node583 node583Labels := by rfl

theorem canonical23208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23208 raw23208Labels = mixedMoment B node583 node583Labels := by
  calc
    mixedMoment B raw23208 raw23208Labels = mixedMoment B raw23208step0 raw23208step0Labels := by
      have hz : ∀ j, raw23208 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23208step0 = (fun i j => raw23208 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23208step0 raw23208; decide +kernel
      have hl : raw23208step0Labels = raw23208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23208 raw23208Labels permutation346 hz
    _ = mixedMoment B node583 node583Labels := by rfl

theorem canonical23209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23209 raw23209Labels = mixedMoment B node589 node589Labels := by
  calc
    mixedMoment B raw23209 raw23209Labels = mixedMoment B raw23209step0 raw23209step0Labels := by
      have hz : ∀ j, raw23209 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23209step0 = (fun i j => raw23209 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23209step0 raw23209; decide +kernel
      have hl : raw23209step0Labels = raw23209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23209 raw23209Labels permutation434 hz
    mixedMoment B raw23209step0 raw23209step0Labels = mixedMoment B raw23209step1 raw23209step1Labels := by
      have hz : ∀ j, raw23209step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23209step1 = (fun i j => raw23209step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23209step1 raw23209step0; decide +kernel
      have hl : raw23209step1Labels = raw23209step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23209step0 raw23209step0Labels permutation80 hz
    mixedMoment B raw23209step1 raw23209step1Labels = mixedMoment B raw23209step2 raw23209step2Labels := by
      have ha : raw23209step2 = (fun i j => raw23209step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23209step2 raw23209step1; decide +kernel
      have hl : raw23209step2Labels = raw23209step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23209step1 raw23209step1Labels permutation9 permutation2
    _ = mixedMoment B node589 node589Labels := by rfl

theorem canonical23210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23210 raw23210Labels = mixedMoment B node933 node933Labels := by
  calc
    mixedMoment B raw23210 raw23210Labels = mixedMoment B raw23210step0 raw23210step0Labels := by
      have hz : ∀ j, raw23210 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23210step0 = (fun i j => raw23210 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23210step0 raw23210; decide +kernel
      have hl : raw23210step0Labels = raw23210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23210 raw23210Labels permutation434 hz
    mixedMoment B raw23210step0 raw23210step0Labels = mixedMoment B raw23210step1 raw23210step1Labels := by
      have ha : raw23210step1 = (fun i j => raw23210step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23210step1 raw23210step0; decide +kernel
      have hl : raw23210step1Labels = raw23210step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23210step0 raw23210step0Labels permutation38 permutation2
    _ = mixedMoment B node933 node933Labels := by rfl

theorem canonical23211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23211 raw23211Labels = mixedMoment B node933 node933Labels := by
  calc
    mixedMoment B raw23211 raw23211Labels = mixedMoment B raw23211step0 raw23211step0Labels := by
      have hz : ∀ j, raw23211 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23211step0 = (fun i j => raw23211 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23211step0 raw23211; decide +kernel
      have hl : raw23211step0Labels = raw23211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23211 raw23211Labels permutation346 hz
    mixedMoment B raw23211step0 raw23211step0Labels = mixedMoment B raw23211step1 raw23211step1Labels := by
      have ha : raw23211step1 = (fun i j => raw23211step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23211step1 raw23211step0; decide +kernel
      have hl : raw23211step1Labels = raw23211step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23211step0 raw23211step0Labels permutation38 permutation2
    _ = mixedMoment B node933 node933Labels := by rfl

theorem canonical23212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23212 raw23212Labels = mixedMoment B node1086 node1086Labels := by
  calc
    mixedMoment B raw23212 raw23212Labels = mixedMoment B raw23212step0 raw23212step0Labels := by
      have hz : ∀ j, raw23212 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23212step0 = (fun i j => raw23212 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23212step0 raw23212; decide +kernel
      have hl : raw23212step0Labels = raw23212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23212 raw23212Labels permutation434 hz
    mixedMoment B raw23212step0 raw23212step0Labels = mixedMoment B raw23212step1 raw23212step1Labels := by
      have hz : ∀ j, raw23212step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23212step1 = (fun i j => raw23212step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23212step1 raw23212step0; decide +kernel
      have hl : raw23212step1Labels = raw23212step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23212step0 raw23212step0Labels permutation80 hz
    mixedMoment B raw23212step1 raw23212step1Labels = mixedMoment B raw23212step2 raw23212step2Labels := by
      have ha : raw23212step2 = (fun i j => raw23212step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23212step2 raw23212step1; decide +kernel
      have hl : raw23212step2Labels = raw23212step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23212step1 raw23212step1Labels permutation9 permutation2
    _ = mixedMoment B node1086 node1086Labels := by rfl

theorem canonical23213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23213 raw23213Labels = mixedMoment B node947 node947Labels := by
  calc
    mixedMoment B raw23213 raw23213Labels = mixedMoment B raw23213step0 raw23213step0Labels := by
      have hz : ∀ j, raw23213 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23213step0 = (fun i j => raw23213 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23213step0 raw23213; decide +kernel
      have hl : raw23213step0Labels = raw23213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23213 raw23213Labels permutation434 hz
    _ = mixedMoment B node947 node947Labels := by rfl

theorem canonical23214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23214 raw23214Labels = mixedMoment B node947 node947Labels := by
  calc
    mixedMoment B raw23214 raw23214Labels = mixedMoment B raw23214step0 raw23214step0Labels := by
      have hz : ∀ j, raw23214 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23214step0 = (fun i j => raw23214 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23214step0 raw23214; decide +kernel
      have hl : raw23214step0Labels = raw23214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23214 raw23214Labels permutation346 hz
    _ = mixedMoment B node947 node947Labels := by rfl

theorem canonical23215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23215 raw23215Labels = mixedMoment B node953 node953Labels := by
  calc
    mixedMoment B raw23215 raw23215Labels = mixedMoment B raw23215step0 raw23215step0Labels := by
      have hz : ∀ j, raw23215 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23215step0 = (fun i j => raw23215 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23215step0 raw23215; decide +kernel
      have hl : raw23215step0Labels = raw23215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23215 raw23215Labels permutation434 hz
    mixedMoment B raw23215step0 raw23215step0Labels = mixedMoment B raw23215step1 raw23215step1Labels := by
      have hz : ∀ j, raw23215step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23215step1 = (fun i j => raw23215step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23215step1 raw23215step0; decide +kernel
      have hl : raw23215step1Labels = raw23215step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23215step0 raw23215step0Labels permutation80 hz
    mixedMoment B raw23215step1 raw23215step1Labels = mixedMoment B raw23215step2 raw23215step2Labels := by
      have ha : raw23215step2 = (fun i j => raw23215step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23215step2 raw23215step1; decide +kernel
      have hl : raw23215step2Labels = raw23215step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23215step1 raw23215step1Labels permutation9 permutation2
    _ = mixedMoment B node953 node953Labels := by rfl

theorem canonical23216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23216 raw23216Labels = mixedMoment B node907 node907Labels := by
  calc
    mixedMoment B raw23216 raw23216Labels = mixedMoment B raw23216step0 raw23216step0Labels := by
      have ha : raw23216step0 = (fun i j => raw23216 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23216step0 raw23216; decide +kernel
      have hl : raw23216step0Labels = raw23216Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23216 raw23216Labels permutation200 permutation2
    _ = mixedMoment B node907 node907Labels := by rfl

theorem canonical23217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23217 raw23217Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw23217 raw23217Labels = mixedMoment B raw23217step0 raw23217step0Labels := by
      have hz : ∀ j, raw23217 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23217step0 = (fun i j => raw23217 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23217step0 raw23217; decide +kernel
      have hl : raw23217step0Labels = raw23217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23217 raw23217Labels permutation434 hz
    _ = mixedMoment B node1041 node1041Labels := by rfl

theorem canonical23218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23218 raw23218Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw23218 raw23218Labels = mixedMoment B raw23218step0 raw23218step0Labels := by
      have hz : ∀ j, raw23218 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23218step0 = (fun i j => raw23218 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23218step0 raw23218; decide +kernel
      have hl : raw23218step0Labels = raw23218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23218 raw23218Labels permutation434 hz
    mixedMoment B raw23218step0 raw23218step0Labels = mixedMoment B raw23218step1 raw23218step1Labels := by
      have ha : raw23218step1 = (fun i j => raw23218step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23218step1 raw23218step0; decide +kernel
      have hl : raw23218step1Labels = raw23218step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23218step0 raw23218step0Labels permutation33 permutation2
    _ = mixedMoment B node1041 node1041Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw831 raw831Labels = mixedMoment B node4186 node4186Labels := by
  calc
    mixedMoment B raw831 raw831Labels = mixedMoment B raw831step0 raw831step0Labels := by
      have ha : raw831step0 = (fun i j => raw831 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw831step0 raw831; decide +kernel
      have hl : raw831step0Labels = raw831Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw831 raw831Labels permutation8 permutation4
    mixedMoment B raw831step0 raw831step0Labels = mixedMoment B raw831step1 raw831step1Labels := by
      have ha : raw831step1 = raw831step0 := by apply Matrix.ext; unfold raw831step1 raw831step0; decide +kernel
      have hl : raw831step0Labels = labelEmbedding7 ∘ raw831step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw831step0 raw831step0Labels raw831step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4186 node4186Labels := by rfl

theorem canonical832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw832 raw832Labels = mixedMoment B node614 node614Labels := by
  calc
    mixedMoment B raw832 raw832Labels = mixedMoment B raw832step0 raw832step0Labels := by
      have ha : raw832step0 = (fun i j => raw832 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw832step0 raw832; decide +kernel
      have hl : raw832step0Labels = raw832Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw832 raw832Labels permutation8 permutation4
    _ = mixedMoment B node614 node614Labels := by rfl

theorem canonical833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw833 raw833Labels = mixedMoment B node1536 node1536Labels := by
  calc
    mixedMoment B raw833 raw833Labels = mixedMoment B raw833step0 raw833step0Labels := by
      have ha : raw833step0 = (fun i j => raw833 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw833step0 raw833; decide +kernel
      have hl : raw833step0Labels = raw833Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw833 raw833Labels permutation8 permutation6
    mixedMoment B raw833step0 raw833step0Labels = mixedMoment B raw833step1 raw833step1Labels := by
      have ha : raw833step1 = -raw833step0 := by apply Matrix.ext; change ∀ i j, raw833step1 i j = -(raw833step0 i j); unfold raw833step1 raw833step0; decide +kernel
      have hl : raw833step1Labels = raw833step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw833step1 raw833step1Labels = mixedMoment B raw833step2 raw833step2Labels := by
      have ha : raw833step2 = raw833step1 := by apply Matrix.ext; unfold raw833step2 raw833step1; decide +kernel
      have hl : raw833step1Labels = labelEmbedding1 ∘ raw833step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw833step1 raw833step1Labels raw833step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1536 node1536Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1149 raw1149Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw1149 raw1149Labels = mixedMoment B raw1149step0 raw1149step0Labels := by
      have ha : raw1149step0 = (fun i j => raw1149 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1149step0 raw1149; decide +kernel
      have hl : raw1149step0Labels = raw1149Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1149 raw1149Labels permutation32 permutation4
    mixedMoment B raw1149step0 raw1149step0Labels = mixedMoment B raw1149step1 raw1149step1Labels := by
      have ha : raw1149step1 = raw1149step0 := by apply Matrix.ext; unfold raw1149step1 raw1149step0; decide +kernel
      have hl : raw1149step0Labels = labelEmbedding7 ∘ raw1149step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1149step0 raw1149step0Labels raw1149step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4355 node4355Labels := by rfl

theorem canonical1150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1150 raw1150Labels = mixedMoment B node933 node933Labels := by
  calc
    mixedMoment B raw1150 raw1150Labels = mixedMoment B raw1150step0 raw1150step0Labels := by
      have ha : raw1150step0 = (fun i j => raw1150 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1150step0 raw1150; decide +kernel
      have hl : raw1150step0Labels = raw1150Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1150 raw1150Labels permutation32 permutation4
    _ = mixedMoment B node933 node933Labels := by rfl

theorem canonical1151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1151 raw1151Labels = mixedMoment B node1691 node1691Labels := by
  calc
    mixedMoment B raw1151 raw1151Labels = mixedMoment B raw1151step0 raw1151step0Labels := by
      have ha : raw1151step0 = (fun i j => raw1151 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1151step0 raw1151; decide +kernel
      have hl : raw1151step0Labels = raw1151Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1151 raw1151Labels permutation32 permutation6
    mixedMoment B raw1151step0 raw1151step0Labels = mixedMoment B raw1151step1 raw1151step1Labels := by
      have ha : raw1151step1 = -raw1151step0 := by apply Matrix.ext; change ∀ i j, raw1151step1 i j = -(raw1151step0 i j); unfold raw1151step1 raw1151step0; decide +kernel
      have hl : raw1151step1Labels = raw1151step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1151step1 raw1151step1Labels = mixedMoment B raw1151step2 raw1151step2Labels := by
      have ha : raw1151step2 = raw1151step1 := by apply Matrix.ext; unfold raw1151step2 raw1151step1; decide +kernel
      have hl : raw1151step1Labels = labelEmbedding1 ∘ raw1151step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1151step1 raw1151step1Labels raw1151step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1691 node1691Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11403 raw11403Labels = mixedMoment B node4502 node4502Labels := by
  calc
    mixedMoment B raw11403 raw11403Labels = mixedMoment B raw11403step0 raw11403step0Labels := by
      have hz : ∀ j, raw11403 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11403step0 = (fun i j => raw11403 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11403step0 raw11403; decide +kernel
      have hl : raw11403step0Labels = raw11403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11403 raw11403Labels permutation434 hz
    mixedMoment B raw11403step0 raw11403step0Labels = mixedMoment B raw11403step1 raw11403step1Labels := by
      have hz : ∀ j, raw11403step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11403step1 = (fun i j => raw11403step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11403step1 raw11403step0; decide +kernel
      have hl : raw11403step1Labels = raw11403step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11403step0 raw11403step0Labels permutation80 hz
    _ = mixedMoment B node4502 node4502Labels := by rfl

theorem canonical11408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11408 raw11408Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw11408 raw11408Labels = mixedMoment B raw11408step0 raw11408step0Labels := by
      have hz : ∀ j, raw11408 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11408step0 = (fun i j => raw11408 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11408step0 raw11408; decide +kernel
      have hl : raw11408step0Labels = raw11408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11408 raw11408Labels permutation434 hz
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical11413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11413 raw11413Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw11413 raw11413Labels = mixedMoment B raw11413step0 raw11413step0Labels := by
      have hz : ∀ j, raw11413 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11413step0 = (fun i j => raw11413 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11413step0 raw11413; decide +kernel
      have hl : raw11413step0Labels = raw11413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11413 raw11413Labels permutation346 hz
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical11419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11419 raw11419Labels = mixedMoment B node4875 node4875Labels := by
  calc
    mixedMoment B raw11419 raw11419Labels = mixedMoment B raw11419step0 raw11419step0Labels := by
      have hz : ∀ j, raw11419 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11419step0 = (fun i j => raw11419 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11419step0 raw11419; decide +kernel
      have hl : raw11419step0Labels = raw11419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11419 raw11419Labels permutation434 hz
    mixedMoment B raw11419step0 raw11419step0Labels = mixedMoment B raw11419step1 raw11419step1Labels := by
      have hz : ∀ j, raw11419step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11419step1 = (fun i j => raw11419step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11419step1 raw11419step0; decide +kernel
      have hl : raw11419step1Labels = raw11419step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11419step0 raw11419step0Labels permutation80 hz
    _ = mixedMoment B node4875 node4875Labels := by rfl

theorem canonical11420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11420 raw11420Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw11420 raw11420Labels = mixedMoment B raw11420step0 raw11420step0Labels := by
      have hz : ∀ j, raw11420 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11420step0 = (fun i j => raw11420 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11420step0 raw11420; decide +kernel
      have hl : raw11420step0Labels = raw11420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11420 raw11420Labels permutation434 hz
    mixedMoment B raw11420step0 raw11420step0Labels = mixedMoment B raw11420step1 raw11420step1Labels := by
      have ha : raw11420step1 = (fun i j => raw11420step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11420step1 raw11420step0; decide +kernel
      have hl : raw11420step1Labels = raw11420step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11420step0 raw11420step0Labels permutation38 permutation2
    _ = mixedMoment B node4811 node4811Labels := by rfl

theorem canonical11421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11421 raw11421Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw11421 raw11421Labels = mixedMoment B raw11421step0 raw11421step0Labels := by
      have hz : ∀ j, raw11421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11421step0 = (fun i j => raw11421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11421step0 raw11421; decide +kernel
      have hl : raw11421step0Labels = raw11421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11421 raw11421Labels permutation346 hz
    mixedMoment B raw11421step0 raw11421step0Labels = mixedMoment B raw11421step1 raw11421step1Labels := by
      have ha : raw11421step1 = (fun i j => raw11421step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11421step1 raw11421step0; decide +kernel
      have hl : raw11421step1Labels = raw11421step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11421step0 raw11421step0Labels permutation38 permutation2
    _ = mixedMoment B node4811 node4811Labels := by rfl

theorem canonical11422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11422 raw11422Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw11422 raw11422Labels = mixedMoment B raw11422step0 raw11422step0Labels := by
      have hz : ∀ j, raw11422 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11422step0 = (fun i j => raw11422 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11422step0 raw11422; decide +kernel
      have hl : raw11422step0Labels = raw11422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11422 raw11422Labels permutation434 hz
    mixedMoment B raw11422step0 raw11422step0Labels = mixedMoment B raw11422step1 raw11422step1Labels := by
      have hz : ∀ j, raw11422step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11422step1 = (fun i j => raw11422step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11422step1 raw11422step0; decide +kernel
      have hl : raw11422step1Labels = raw11422step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11422step0 raw11422step0Labels permutation80 hz
    mixedMoment B raw11422step1 raw11422step1Labels = mixedMoment B raw11422step2 raw11422step2Labels := by
      have ha : raw11422step2 = (fun i j => raw11422step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11422step2 raw11422step1; decide +kernel
      have hl : raw11422step2Labels = raw11422step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11422step1 raw11422step1Labels permutation9 permutation2
    _ = mixedMoment B node4895 node4895Labels := by rfl

theorem canonical11423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11423 raw11423Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw11423 raw11423Labels = mixedMoment B raw11423step0 raw11423step0Labels := by
      have hz : ∀ j, raw11423 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11423step0 = (fun i j => raw11423 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11423step0 raw11423; decide +kernel
      have hl : raw11423step0Labels = raw11423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11423 raw11423Labels permutation434 hz
    mixedMoment B raw11423step0 raw11423step0Labels = mixedMoment B raw11423step1 raw11423step1Labels := by
      have hz : ∀ j, raw11423step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11423step1 = (fun i j => raw11423step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11423step1 raw11423step0; decide +kernel
      have hl : raw11423step1Labels = raw11423step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11423step0 raw11423step0Labels permutation80 hz
    _ = mixedMoment B node4463 node4463Labels := by rfl

theorem canonical11433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11433 raw11433Labels = mixedMoment B node1753 node1753Labels := by
  calc
    mixedMoment B raw11433 raw11433Labels = mixedMoment B raw11433step0 raw11433step0Labels := by
      have hz : ∀ j, raw11433 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11433step0 = (fun i j => raw11433 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11433step0 raw11433; decide +kernel
      have hl : raw11433step0Labels = raw11433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11433 raw11433Labels permutation434 hz
    mixedMoment B raw11433step0 raw11433step0Labels = mixedMoment B raw11433step1 raw11433step1Labels := by
      have hz : ∀ j, raw11433step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11433step1 = (fun i j => raw11433step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11433step1 raw11433step0; decide +kernel
      have hl : raw11433step1Labels = raw11433step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11433step0 raw11433step0Labels permutation80 hz
    mixedMoment B raw11433step1 raw11433step1Labels = mixedMoment B raw11433step2 raw11433step2Labels := by
      have ha : raw11433step2 = (fun i j => raw11433step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11433step2 raw11433step1; decide +kernel
      have hl : raw11433step2Labels = raw11433step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11433step1 raw11433step1Labels permutation8 permutation7
    mixedMoment B raw11433step2 raw11433step2Labels = mixedMoment B raw11433step3 raw11433step3Labels := by
      have ha : raw11433step3 = -raw11433step2 := by apply Matrix.ext; change ∀ i j, raw11433step3 i j = -(raw11433step2 i j); unfold raw11433step3 raw11433step2; decide +kernel
      have hl : raw11433step3Labels = raw11433step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11433step3 raw11433step3Labels = mixedMoment B raw11433step4 raw11433step4Labels := by
      have ha : raw11433step4 = raw11433step3 := by apply Matrix.ext; unfold raw11433step4 raw11433step3; decide +kernel
      have hl : raw11433step3Labels = labelEmbedding1 ∘ raw11433step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11433step3 raw11433step3Labels raw11433step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1753 node1753Labels := by rfl

theorem canonical11438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11438 raw11438Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw11438 raw11438Labels = mixedMoment B raw11438step0 raw11438step0Labels := by
      have hz : ∀ j, raw11438 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11438step0 = (fun i j => raw11438 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11438step0 raw11438; decide +kernel
      have hl : raw11438step0Labels = raw11438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11438 raw11438Labels permutation434 hz
    mixedMoment B raw11438step0 raw11438step0Labels = mixedMoment B raw11438step1 raw11438step1Labels := by
      have ha : raw11438step1 = (fun i j => raw11438step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11438step1 raw11438step0; decide +kernel
      have hl : raw11438step1Labels = raw11438step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11438step0 raw11438step0Labels permutation38 permutation7
    mixedMoment B raw11438step1 raw11438step1Labels = mixedMoment B raw11438step2 raw11438step2Labels := by
      have ha : raw11438step2 = -raw11438step1 := by apply Matrix.ext; change ∀ i j, raw11438step2 i j = -(raw11438step1 i j); unfold raw11438step2 raw11438step1; decide +kernel
      have hl : raw11438step2Labels = raw11438step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11438step2 raw11438step2Labels = mixedMoment B raw11438step3 raw11438step3Labels := by
      have ha : raw11438step3 = raw11438step2 := by apply Matrix.ext; unfold raw11438step3 raw11438step2; decide +kernel
      have hl : raw11438step2Labels = labelEmbedding1 ∘ raw11438step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11438step2 raw11438step2Labels raw11438step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical11443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11443 raw11443Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw11443 raw11443Labels = mixedMoment B raw11443step0 raw11443step0Labels := by
      have hz : ∀ j, raw11443 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11443step0 = (fun i j => raw11443 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11443step0 raw11443; decide +kernel
      have hl : raw11443step0Labels = raw11443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11443 raw11443Labels permutation346 hz
    mixedMoment B raw11443step0 raw11443step0Labels = mixedMoment B raw11443step1 raw11443step1Labels := by
      have ha : raw11443step1 = (fun i j => raw11443step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11443step1 raw11443step0; decide +kernel
      have hl : raw11443step1Labels = raw11443step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11443step0 raw11443step0Labels permutation38 permutation7
    mixedMoment B raw11443step1 raw11443step1Labels = mixedMoment B raw11443step2 raw11443step2Labels := by
      have ha : raw11443step2 = -raw11443step1 := by apply Matrix.ext; change ∀ i j, raw11443step2 i j = -(raw11443step1 i j); unfold raw11443step2 raw11443step1; decide +kernel
      have hl : raw11443step2Labels = raw11443step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11443step2 raw11443step2Labels = mixedMoment B raw11443step3 raw11443step3Labels := by
      have ha : raw11443step3 = raw11443step2 := by apply Matrix.ext; unfold raw11443step3 raw11443step2; decide +kernel
      have hl : raw11443step2Labels = labelEmbedding1 ∘ raw11443step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11443step2 raw11443step2Labels raw11443step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical11449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11449 raw11449Labels = mixedMoment B node2288 node2288Labels := by
  calc
    mixedMoment B raw11449 raw11449Labels = mixedMoment B raw11449step0 raw11449step0Labels := by
      have hz : ∀ j, raw11449 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11449step0 = (fun i j => raw11449 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11449step0 raw11449; decide +kernel
      have hl : raw11449step0Labels = raw11449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11449 raw11449Labels permutation434 hz
    mixedMoment B raw11449step0 raw11449step0Labels = mixedMoment B raw11449step1 raw11449step1Labels := by
      have hz : ∀ j, raw11449step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11449step1 = (fun i j => raw11449step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11449step1 raw11449step0; decide +kernel
      have hl : raw11449step1Labels = raw11449step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11449step0 raw11449step0Labels permutation80 hz
    mixedMoment B raw11449step1 raw11449step1Labels = mixedMoment B raw11449step2 raw11449step2Labels := by
      have ha : raw11449step2 = (fun i j => raw11449step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11449step2 raw11449step1; decide +kernel
      have hl : raw11449step2Labels = raw11449step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11449step1 raw11449step1Labels permutation8 permutation7
    mixedMoment B raw11449step2 raw11449step2Labels = mixedMoment B raw11449step3 raw11449step3Labels := by
      have ha : raw11449step3 = -raw11449step2 := by apply Matrix.ext; change ∀ i j, raw11449step3 i j = -(raw11449step2 i j); unfold raw11449step3 raw11449step2; decide +kernel
      have hl : raw11449step3Labels = raw11449step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11449step3 raw11449step3Labels = mixedMoment B raw11449step4 raw11449step4Labels := by
      have ha : raw11449step4 = raw11449step3 := by apply Matrix.ext; unfold raw11449step4 raw11449step3; decide +kernel
      have hl : raw11449step3Labels = labelEmbedding1 ∘ raw11449step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11449step3 raw11449step3Labels raw11449step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2288 node2288Labels := by rfl

theorem canonical11450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11450 raw11450Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw11450 raw11450Labels = mixedMoment B raw11450step0 raw11450step0Labels := by
      have hz : ∀ j, raw11450 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11450step0 = (fun i j => raw11450 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11450step0 raw11450; decide +kernel
      have hl : raw11450step0Labels = raw11450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11450 raw11450Labels permutation434 hz
    mixedMoment B raw11450step0 raw11450step0Labels = mixedMoment B raw11450step1 raw11450step1Labels := by
      have ha : raw11450step1 = (fun i j => raw11450step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11450step1 raw11450step0; decide +kernel
      have hl : raw11450step1Labels = raw11450step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11450step0 raw11450step0Labels permutation38 permutation7
    mixedMoment B raw11450step1 raw11450step1Labels = mixedMoment B raw11450step2 raw11450step2Labels := by
      have ha : raw11450step2 = -raw11450step1 := by apply Matrix.ext; change ∀ i j, raw11450step2 i j = -(raw11450step1 i j); unfold raw11450step2 raw11450step1; decide +kernel
      have hl : raw11450step2Labels = raw11450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11450step2 raw11450step2Labels = mixedMoment B raw11450step3 raw11450step3Labels := by
      have ha : raw11450step3 = raw11450step2 := by apply Matrix.ext; unfold raw11450step3 raw11450step2; decide +kernel
      have hl : raw11450step2Labels = labelEmbedding1 ∘ raw11450step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11450step2 raw11450step2Labels raw11450step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2225 node2225Labels := by rfl

theorem canonical11451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11451 raw11451Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw11451 raw11451Labels = mixedMoment B raw11451step0 raw11451step0Labels := by
      have hz : ∀ j, raw11451 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11451step0 = (fun i j => raw11451 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11451step0 raw11451; decide +kernel
      have hl : raw11451step0Labels = raw11451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11451 raw11451Labels permutation346 hz
    mixedMoment B raw11451step0 raw11451step0Labels = mixedMoment B raw11451step1 raw11451step1Labels := by
      have ha : raw11451step1 = (fun i j => raw11451step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11451step1 raw11451step0; decide +kernel
      have hl : raw11451step1Labels = raw11451step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11451step0 raw11451step0Labels permutation38 permutation7
    mixedMoment B raw11451step1 raw11451step1Labels = mixedMoment B raw11451step2 raw11451step2Labels := by
      have ha : raw11451step2 = -raw11451step1 := by apply Matrix.ext; change ∀ i j, raw11451step2 i j = -(raw11451step1 i j); unfold raw11451step2 raw11451step1; decide +kernel
      have hl : raw11451step2Labels = raw11451step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11451step2 raw11451step2Labels = mixedMoment B raw11451step3 raw11451step3Labels := by
      have ha : raw11451step3 = raw11451step2 := by apply Matrix.ext; unfold raw11451step3 raw11451step2; decide +kernel
      have hl : raw11451step2Labels = labelEmbedding1 ∘ raw11451step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11451step2 raw11451step2Labels raw11451step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2225 node2225Labels := by rfl

theorem canonical11452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11452 raw11452Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw11452 raw11452Labels = mixedMoment B raw11452step0 raw11452step0Labels := by
      have hz : ∀ j, raw11452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11452step0 = (fun i j => raw11452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11452step0 raw11452; decide +kernel
      have hl : raw11452step0Labels = raw11452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11452 raw11452Labels permutation434 hz
    mixedMoment B raw11452step0 raw11452step0Labels = mixedMoment B raw11452step1 raw11452step1Labels := by
      have hz : ∀ j, raw11452step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11452step1 = (fun i j => raw11452step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11452step1 raw11452step0; decide +kernel
      have hl : raw11452step1Labels = raw11452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11452step0 raw11452step0Labels permutation80 hz
    mixedMoment B raw11452step1 raw11452step1Labels = mixedMoment B raw11452step2 raw11452step2Labels := by
      have ha : raw11452step2 = (fun i j => raw11452step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11452step2 raw11452step1; decide +kernel
      have hl : raw11452step2Labels = raw11452step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11452step1 raw11452step1Labels permutation9 permutation7
    mixedMoment B raw11452step2 raw11452step2Labels = mixedMoment B raw11452step3 raw11452step3Labels := by
      have ha : raw11452step3 = -raw11452step2 := by apply Matrix.ext; change ∀ i j, raw11452step3 i j = -(raw11452step2 i j); unfold raw11452step3 raw11452step2; decide +kernel
      have hl : raw11452step3Labels = raw11452step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11452step3 raw11452step3Labels = mixedMoment B raw11452step4 raw11452step4Labels := by
      have ha : raw11452step4 = raw11452step3 := by apply Matrix.ext; unfold raw11452step4 raw11452step3; decide +kernel
      have hl : raw11452step3Labels = labelEmbedding1 ∘ raw11452step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11452step3 raw11452step3Labels raw11452step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

theorem canonical11453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11453 raw11453Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw11453 raw11453Labels = mixedMoment B raw11453step0 raw11453step0Labels := by
      have hz : ∀ j, raw11453 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11453step0 = (fun i j => raw11453 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11453step0 raw11453; decide +kernel
      have hl : raw11453step0Labels = raw11453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11453 raw11453Labels permutation434 hz
    mixedMoment B raw11453step0 raw11453step0Labels = mixedMoment B raw11453step1 raw11453step1Labels := by
      have hz : ∀ j, raw11453step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11453step1 = (fun i j => raw11453step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11453step1 raw11453step0; decide +kernel
      have hl : raw11453step1Labels = raw11453step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11453step0 raw11453step0Labels permutation80 hz
    mixedMoment B raw11453step1 raw11453step1Labels = mixedMoment B raw11453step2 raw11453step2Labels := by
      have ha : raw11453step2 = (fun i j => raw11453step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11453step2 raw11453step1; decide +kernel
      have hl : raw11453step2Labels = raw11453step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11453step1 raw11453step1Labels permutation8 permutation7
    mixedMoment B raw11453step2 raw11453step2Labels = mixedMoment B raw11453step3 raw11453step3Labels := by
      have ha : raw11453step3 = -raw11453step2 := by apply Matrix.ext; change ∀ i j, raw11453step3 i j = -(raw11453step2 i j); unfold raw11453step3 raw11453step2; decide +kernel
      have hl : raw11453step3Labels = raw11453step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11453step3 raw11453step3Labels = mixedMoment B raw11453step4 raw11453step4Labels := by
      have ha : raw11453step4 = raw11453step3 := by apply Matrix.ext; unfold raw11453step4 raw11453step3; decide +kernel
      have hl : raw11453step3Labels = labelEmbedding1 ∘ raw11453step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11453step3 raw11453step3Labels raw11453step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

theorem canonical11462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11462 raw11462Labels = mixedMoment B node2116 node2116Labels := by
  calc
    mixedMoment B raw11462 raw11462Labels = mixedMoment B raw11462step0 raw11462step0Labels := by
      have hz : ∀ j, raw11462 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11462step0 = (fun i j => raw11462 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11462step0 raw11462; decide +kernel
      have hl : raw11462step0Labels = raw11462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11462 raw11462Labels permutation434 hz
    mixedMoment B raw11462step0 raw11462step0Labels = mixedMoment B raw11462step1 raw11462step1Labels := by
      have hz : ∀ j, raw11462step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11462step1 = (fun i j => raw11462step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11462step1 raw11462step0; decide +kernel
      have hl : raw11462step1Labels = raw11462step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11462step0 raw11462step0Labels permutation80 hz
    _ = mixedMoment B node2116 node2116Labels := by rfl

theorem canonical11464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11464 raw11464Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw11464 raw11464Labels = mixedMoment B raw11464step0 raw11464step0Labels := by
      have hz : ∀ j, raw11464 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11464step0 = (fun i j => raw11464 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11464step0 raw11464; decide +kernel
      have hl : raw11464step0Labels = raw11464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11464 raw11464Labels permutation434 hz
    mixedMoment B raw11464step0 raw11464step0Labels = mixedMoment B raw11464step1 raw11464step1Labels := by
      have hz : ∀ j, raw11464step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11464step1 = (fun i j => raw11464step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11464step1 raw11464step0; decide +kernel
      have hl : raw11464step1Labels = raw11464step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11464step0 raw11464step0Labels permutation80 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

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

theorem canonical1260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1260 raw1260Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw1260 raw1260Labels = mixedMoment B raw1260step0 raw1260step0Labels := by
      have ha : raw1260step0 = (fun i j => raw1260 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1260step0 raw1260; decide +kernel
      have hl : raw1260step0Labels = raw1260Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1260 raw1260Labels permutation32 permutation4
    mixedMoment B raw1260step0 raw1260step0Labels = mixedMoment B raw1260step1 raw1260step1Labels := by
      have ha : raw1260step1 = raw1260step0 := by apply Matrix.ext; unfold raw1260step1 raw1260step0; decide +kernel
      have hl : raw1260step0Labels = labelEmbedding7 ∘ raw1260step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1260step0 raw1260step0Labels raw1260step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical1261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1261 raw1261Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw1261 raw1261Labels = mixedMoment B raw1261step0 raw1261step0Labels := by
      have ha : raw1261step0 = (fun i j => raw1261 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1261step0 raw1261; decide +kernel
      have hl : raw1261step0Labels = raw1261Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1261 raw1261Labels permutation32 permutation4
    _ = mixedMoment B node1041 node1041Labels := by rfl

theorem canonical1262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1262 raw1262Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw1262 raw1262Labels = mixedMoment B raw1262step0 raw1262step0Labels := by
      have ha : raw1262step0 = (fun i j => raw1262 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1262step0 raw1262; decide +kernel
      have hl : raw1262step0Labels = raw1262Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1262 raw1262Labels permutation38 permutation6
    mixedMoment B raw1262step0 raw1262step0Labels = mixedMoment B raw1262step1 raw1262step1Labels := by
      have ha : raw1262step1 = -raw1262step0 := by apply Matrix.ext; change ∀ i j, raw1262step1 i j = -(raw1262step0 i j); unfold raw1262step1 raw1262step0; decide +kernel
      have hl : raw1262step1Labels = raw1262step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1262step1 raw1262step1Labels = mixedMoment B raw1262step2 raw1262step2Labels := by
      have ha : raw1262step2 = raw1262step1 := by apply Matrix.ext; unfold raw1262step2 raw1262step1; decide +kernel
      have hl : raw1262step1Labels = labelEmbedding1 ∘ raw1262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1262step1 raw1262step1Labels raw1262step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical1269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1269 raw1269Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw1269 raw1269Labels = mixedMoment B raw1269step0 raw1269step0Labels := by
      have ha : raw1269step0 = (fun i j => raw1269 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1269step0 raw1269; decide +kernel
      have hl : raw1269step0Labels = raw1269Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1269 raw1269Labels permutation8 permutation4
    mixedMoment B raw1269step0 raw1269step0Labels = mixedMoment B raw1269step1 raw1269step1Labels := by
      have ha : raw1269step1 = raw1269step0 := by apply Matrix.ext; unfold raw1269step1 raw1269step0; decide +kernel
      have hl : raw1269step0Labels = labelEmbedding7 ∘ raw1269step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1269step0 raw1269step0Labels raw1269step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

theorem canonical1270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1270 raw1270Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw1270 raw1270Labels = mixedMoment B raw1270step0 raw1270step0Labels := by
      have ha : raw1270step0 = (fun i j => raw1270 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1270step0 raw1270; decide +kernel
      have hl : raw1270step0Labels = raw1270Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1270 raw1270Labels permutation8 permutation4
    _ = mixedMoment B node1046 node1046Labels := by rfl

theorem canonical1271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1271 raw1271Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw1271 raw1271Labels = mixedMoment B raw1271step0 raw1271step0Labels := by
      have ha : raw1271step0 = (fun i j => raw1271 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1271step0 raw1271; decide +kernel
      have hl : raw1271step0Labels = raw1271Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1271 raw1271Labels permutation8 permutation6
    mixedMoment B raw1271step0 raw1271step0Labels = mixedMoment B raw1271step1 raw1271step1Labels := by
      have ha : raw1271step1 = -raw1271step0 := by apply Matrix.ext; change ∀ i j, raw1271step1 i j = -(raw1271step0 i j); unfold raw1271step1 raw1271step0; decide +kernel
      have hl : raw1271step1Labels = raw1271step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1271step1 raw1271step1Labels = mixedMoment B raw1271step2 raw1271step2Labels := by
      have ha : raw1271step2 = raw1271step1 := by apply Matrix.ext; unfold raw1271step2 raw1271step1; decide +kernel
      have hl : raw1271step1Labels = labelEmbedding1 ∘ raw1271step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1271step1 raw1271step1Labels raw1271step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4186 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4186 node4186Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node614 node614Labels + mixedMoment B node1536 node1536Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw831 singletonSmall4186
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4186) = raw831Labels := by decide +kernel
  rw [hl, canonical831 B hB] at h
  have hc0 : mixedMoment B raw831 (Fin.cases (0 : Fin 2) singletonSmall4186) =
      mixedMoment B node614 node614Labels := by
    have ha : raw831 = raw832 := by apply Matrix.ext; unfold raw831 raw832; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4186 = raw832Labels := by decide +kernel
    rw [ha, hj, canonical832 B hB]
  have hc1 : mixedMoment B raw831 (Fin.cases (1 : Fin 2) singletonSmall4186) =
      mixedMoment B node1536 node1536Labels := by
    have ha : raw831 = raw833 := by apply Matrix.ext; unfold raw831 raw833; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4186 = raw833Labels := by decide +kernel
    rw [ha, hj, canonical833 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4355 node4355Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node933 node933Labels + mixedMoment B node1691 node1691Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1149 singletonSmall4355
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4355) = raw1149Labels := by decide +kernel
  rw [hl, canonical1149 B hB] at h
  have hc0 : mixedMoment B raw1149 (Fin.cases (0 : Fin 2) singletonSmall4355) =
      mixedMoment B node933 node933Labels := by
    have ha : raw1149 = raw1150 := by apply Matrix.ext; unfold raw1149 raw1150; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4355 = raw1150Labels := by decide +kernel
    rw [ha, hj, canonical1150 B hB]
  have hc1 : mixedMoment B raw1149 (Fin.cases (1 : Fin 2) singletonSmall4355) =
      mixedMoment B node1691 node1691Labels := by
    have ha : raw1149 = raw1151 := by apply Matrix.ext; unfold raw1149 raw1151; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4355 = raw1151Labels := by decide +kernel
    rw [ha, hj, canonical1151 B hB]
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

theorem singleton4458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4458 node4458Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1041 node1041Labels + mixedMoment B node1724 node1724Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1260 singletonSmall4458
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4458) = raw1260Labels := by decide +kernel
  rw [hl, canonical1260 B hB] at h
  have hc0 : mixedMoment B raw1260 (Fin.cases (0 : Fin 2) singletonSmall4458) =
      mixedMoment B node1041 node1041Labels := by
    have ha : raw1260 = raw1261 := by apply Matrix.ext; unfold raw1260 raw1261; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4458 = raw1261Labels := by decide +kernel
    rw [ha, hj, canonical1261 B hB]
  have hc1 : mixedMoment B raw1260 (Fin.cases (1 : Fin 2) singletonSmall4458) =
      mixedMoment B node1724 node1724Labels := by
    have ha : raw1260 = raw1262 := by apply Matrix.ext; unfold raw1260 raw1262; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4458 = raw1262Labels := by decide +kernel
    rw [ha, hj, canonical1262 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4463 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4463 node4463Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1046 node1046Labels + mixedMoment B node1750 node1750Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1269 singletonSmall4463
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4463) = raw1269Labels := by decide +kernel
  rw [hl, canonical1269 B hB] at h
  have hc0 : mixedMoment B raw1269 (Fin.cases (0 : Fin 2) singletonSmall4463) =
      mixedMoment B node1046 node1046Labels := by
    have ha : raw1269 = raw1270 := by apply Matrix.ext; unfold raw1269 raw1270; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4463 = raw1270Labels := by decide +kernel
    rw [ha, hj, canonical1270 B hB]
  have hc1 : mixedMoment B raw1269 (Fin.cases (1 : Fin 2) singletonSmall4463) =
      mixedMoment B node1750 node1750Labels := by
    have ha : raw1269 = raw1271 := by apply Matrix.ext; unfold raw1269 raw1271; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4463 = raw1271Labels := by decide +kernel
    rw [ha, hj, canonical1271 B hB]
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

theorem singleton4811 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4811 node4811Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2029 node2029Labels + mixedMoment B node2225 node2225Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1749 singletonSmall4811
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4811) = raw1749Labels := by decide +kernel
  rw [hl, canonical1749 B hB] at h
  have hc0 : mixedMoment B raw1749 (Fin.cases (0 : Fin 2) singletonSmall4811) =
      mixedMoment B node2029 node2029Labels := by
    have ha : raw1749 = raw1750 := by apply Matrix.ext; unfold raw1749 raw1750; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4811 = raw1750Labels := by decide +kernel
    rw [ha, hj, canonical1750 B hB]
  have hc1 : mixedMoment B raw1749 (Fin.cases (1 : Fin 2) singletonSmall4811) =
      mixedMoment B node2225 node2225Labels := by
    have ha : raw1749 = raw1751 := by apply Matrix.ext; unfold raw1749 raw1751; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4811 = raw1751Labels := by decide +kernel
    rw [ha, hj, canonical1751 B hB]
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

theorem singleton4875 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4875 node4875Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2116 node2116Labels + mixedMoment B node2288 node2288Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1809 singletonSmall4875
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4875) = raw1809Labels := by decide +kernel
  rw [hl, canonical1809 B hB] at h
  have hc0 : mixedMoment B raw1809 (Fin.cases (0 : Fin 2) singletonSmall4875) =
      mixedMoment B node2116 node2116Labels := by
    have ha : raw1809 = raw1810 := by apply Matrix.ext; unfold raw1809 raw1810; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4875 = raw1810Labels := by decide +kernel
    rw [ha, hj, canonical1810 B hB]
  have hc1 : mixedMoment B raw1809 (Fin.cases (1 : Fin 2) singletonSmall4875) =
      mixedMoment B node2288 node2288Labels := by
    have ha : raw1809 = raw1811 := by apply Matrix.ext; unfold raw1809 raw1811; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4875 = raw1811Labels := by decide +kernel
    rw [ha, hj, canonical1811 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node907 node907Labels = 0 := by
  exact mixedMoment_alpha B hF node907 node907Labels 1 permutation152
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node906 node906Labels = Sparse.eval nodeValue906 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 906) = mixedMoment B node906 node906Labels := rfl
  simpa [nodeValue906, Sparse.eval] using hc.symm

theorem sound907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node907 node907Labels = Sparse.eval nodeValue907 (mixedVector B) := by
  simpa only [nodeValue907, Sparse.eval_nil] using zero907 B _hB _hF

theorem sound932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node932 node932Labels = Sparse.eval nodeValue932 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 932) = mixedMoment B node932 node932Labels := rfl
  simpa [nodeValue932, Sparse.eval] using hc.symm

theorem sound933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node933 node933Labels = Sparse.eval nodeValue933 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 933) = mixedMoment B node933 node933Labels := rfl
  simpa [nodeValue933, Sparse.eval] using hc.symm

theorem sound946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node946 node946Labels = Sparse.eval nodeValue946 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 946) = mixedMoment B node946 node946Labels := rfl
  simpa [nodeValue946, Sparse.eval] using hc.symm

theorem sound947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node947 node947Labels = Sparse.eval nodeValue947 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 947) = mixedMoment B node947 node947Labels := rfl
  simpa [nodeValue947, Sparse.eval] using hc.symm

theorem sound952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node952 node952Labels = Sparse.eval nodeValue952 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 952) = mixedMoment B node952 node952Labels := rfl
  simpa [nodeValue952, Sparse.eval] using hc.symm

theorem sound953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node953 node953Labels = Sparse.eval nodeValue953 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 953) = mixedMoment B node953 node953Labels := rfl
  simpa [nodeValue953, Sparse.eval] using hc.symm

theorem sound954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node954 node954Labels = Sparse.eval nodeValue954 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 954) = mixedMoment B node954 node954Labels := rfl
  simpa [nodeValue954, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1082 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1082 node1082Labels = 0 := by
  exact mixedMoment_order_one B hB node1082 node1082Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1086 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1086 node1086Labels = 0 := by
  exact mixedMoment_order_one B hB node1086 node1086Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1040 node1040Labels = Sparse.eval nodeValue1040 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1040) = mixedMoment B node1040 node1040Labels := rfl
  simpa [nodeValue1040, Sparse.eval] using hc.symm

theorem sound1041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1041 node1041Labels = Sparse.eval nodeValue1041 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1041) = mixedMoment B node1041 node1041Labels := rfl
  simpa [nodeValue1041, Sparse.eval] using hc.symm

theorem sound1042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1042 node1042Labels = Sparse.eval nodeValue1042 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1042) = mixedMoment B node1042 node1042Labels := rfl
  simpa [nodeValue1042, Sparse.eval] using hc.symm

theorem sound1046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1046 node1046Labels = Sparse.eval nodeValue1046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1046) = mixedMoment B node1046 node1046Labels := rfl
  simpa [nodeValue1046, Sparse.eval] using hc.symm

theorem sound1049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1049 node1049Labels = Sparse.eval nodeValue1049 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1049) = mixedMoment B node1049 node1049Labels := rfl
  simpa [nodeValue1049, Sparse.eval] using hc.symm

theorem sound1050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1050 node1050Labels = Sparse.eval nodeValue1050 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1050) = mixedMoment B node1050 node1050Labels := rfl
  simpa [nodeValue1050, Sparse.eval] using hc.symm

theorem sound1082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1082 node1082Labels = Sparse.eval nodeValue1082 (mixedVector B) := by
  simpa only [nodeValue1082, Sparse.eval_nil] using zero1082 B _hB _hF

theorem sound1086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1086 node1086Labels = Sparse.eval nodeValue1086 (mixedVector B) := by
  simpa only [nodeValue1086, Sparse.eval_nil] using zero1086 B _hB _hF

theorem sound1087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1087 node1087Labels = Sparse.eval nodeValue1087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1087) = mixedMoment B node1087 node1087Labels := rfl
  simpa [nodeValue1087, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1515 node1515Labels = Sparse.eval nodeValue1515 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1515) = mixedMoment B node1515 node1515Labels := rfl
  simpa [nodeValue1515, Sparse.eval] using hc.symm

theorem sound1533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1533 node1533Labels = Sparse.eval nodeValue1533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1533) = mixedMoment B node1533 node1533Labels := rfl
  simpa [nodeValue1533, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1536 node1536Labels = Sparse.eval nodeValue1536 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1536) = mixedMoment B node1536 node1536Labels := rfl
  simpa [nodeValue1536, Sparse.eval] using hc.symm

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

theorem zero1671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1671 node1671Labels = 0 := by
  exact mixedMoment_alpha B hF node1671 node1671Labels 1 permutation487
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

theorem sound1671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1671 node1671Labels = Sparse.eval nodeValue1671 (mixedVector B) := by
  simpa only [nodeValue1671, Sparse.eval_nil] using zero1671 B _hB _hF

theorem sound1689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1689 node1689Labels = Sparse.eval nodeValue1689 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1689) = mixedMoment B node1689 node1689Labels := rfl
  simpa [nodeValue1689, Sparse.eval] using hc.symm

theorem sound1691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1691 node1691Labels = Sparse.eval nodeValue1691 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1691) = mixedMoment B node1691 node1691Labels := rfl
  simpa [nodeValue1691, Sparse.eval] using hc.symm

theorem sound1721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1721 node1721Labels = Sparse.eval nodeValue1721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1721) = mixedMoment B node1721 node1721Labels := rfl
  simpa [nodeValue1721, Sparse.eval] using hc.symm

theorem sound1724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1724 node1724Labels = Sparse.eval nodeValue1724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1724) = mixedMoment B node1724 node1724Labels := rfl
  simpa [nodeValue1724, Sparse.eval] using hc.symm

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

theorem zero1753 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1753 node1753Labels = 0 := by
  exact mixedMoment_order_one B hB node1753 node1753Labels 1
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

theorem sound1748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1748 node1748Labels = Sparse.eval nodeValue1748 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1748) = mixedMoment B node1748 node1748Labels := rfl
  simpa [nodeValue1748, Sparse.eval] using hc.symm

theorem sound1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1750 node1750Labels = Sparse.eval nodeValue1750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1750) = mixedMoment B node1750 node1750Labels := rfl
  simpa [nodeValue1750, Sparse.eval] using hc.symm

theorem sound1753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1753 node1753Labels = Sparse.eval nodeValue1753 (mixedVector B) := by
  simpa only [nodeValue1753, Sparse.eval_nil] using zero1753 B _hB _hF

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

theorem sound2029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2029 node2029Labels = Sparse.eval nodeValue2029 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2029) = mixedMoment B node2029 node2029Labels := rfl
  simpa [nodeValue2029, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2115 node2115Labels = Sparse.eval nodeValue2115 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2115) = mixedMoment B node2115 node2115Labels := rfl
  simpa [nodeValue2115, Sparse.eval] using hc.symm

theorem sound2116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2116 node2116Labels = Sparse.eval nodeValue2116 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2116) = mixedMoment B node2116 node2116Labels := rfl
  simpa [nodeValue2116, Sparse.eval] using hc.symm

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

theorem sound2225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2225 node2225Labels = Sparse.eval nodeValue2225 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2225) = mixedMoment B node2225 node2225Labels := rfl
  simpa [nodeValue2225, Sparse.eval] using hc.symm

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

theorem zero2291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = 0 := by
  exact mixedMoment_order_one B hB node2291 node2291Labels 1
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

theorem sound2288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2288 node2288Labels = Sparse.eval nodeValue2288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2288) = mixedMoment B node2288 node2288Labels := rfl
  simpa [nodeValue2288, Sparse.eval] using hc.symm

theorem sound2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = Sparse.eval nodeValue2291 (mixedVector B) := by
  simpa only [nodeValue2291, Sparse.eval_nil] using zero2291 B _hB _hF

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

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node582 node582Labels = Sparse.eval nodeValue582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 582) = mixedMoment B node582 node582Labels := rfl
  simpa [nodeValue582, Sparse.eval] using hc.symm

theorem sound583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node583 node583Labels = Sparse.eval nodeValue583 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 583) = mixedMoment B node583 node583Labels := rfl
  simpa [nodeValue583, Sparse.eval] using hc.symm

theorem sound588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node588 node588Labels = Sparse.eval nodeValue588 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 588) = mixedMoment B node588 node588Labels := rfl
  simpa [nodeValue588, Sparse.eval] using hc.symm

theorem sound589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node589 node589Labels = Sparse.eval nodeValue589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 589) = mixedMoment B node589 node589Labels := rfl
  simpa [nodeValue589, Sparse.eval] using hc.symm

theorem sound590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node590 node590Labels = Sparse.eval nodeValue590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 590) = mixedMoment B node590 node590Labels := rfl
  simpa [nodeValue590, Sparse.eval] using hc.symm

theorem sound613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node613 node613Labels = Sparse.eval nodeValue613 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 613) = mixedMoment B node613 node613Labels := rfl
  simpa [nodeValue613, Sparse.eval] using hc.symm

theorem sound614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node614 node614Labels = Sparse.eval nodeValue614 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 614) = mixedMoment B node614 node614Labels := rfl
  simpa [nodeValue614, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4155 node4155Labels = Sparse.eval nodeValue4155 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4155) = mixedMoment B node4155 node4155Labels := rfl
  simpa [nodeValue4155, Sparse.eval] using hc.symm

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

theorem sound4161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4161 node4161Labels = Sparse.eval nodeValue4161 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4161) = mixedMoment B node4161 node4161Labels := rfl
  simpa [nodeValue4161, Sparse.eval] using hc.symm

theorem sound4186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4186 node4186Labels = Sparse.eval nodeValue4186 (mixedVector B) := by
  have h := singleton4186 B _hB
  rw [sound614 B _hB _hF, sound1536 B _hB _hF] at h
  norm_num [nodeValue4186, nodeValue614, nodeValue1536, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node4329 node4329Labels = 0 := by
  exact mixedMoment_alpha B hF node4329 node4329Labels 1 permutation152
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4329 node4329Labels = Sparse.eval nodeValue4329 (mixedVector B) := by
  simpa only [nodeValue4329, Sparse.eval_nil] using zero4329 B _hB _hF

theorem sound4335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4335 node4335Labels = Sparse.eval nodeValue4335 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4335) = mixedMoment B node4335 node4335Labels := rfl
  simpa [nodeValue4335, Sparse.eval] using hc.symm

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

theorem sound4355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4355 node4355Labels = Sparse.eval nodeValue4355 (mixedVector B) := by
  have h := singleton4355 B _hB
  rw [sound933 B _hB _hF, sound1691 B _hB _hF] at h
  norm_num [nodeValue4355, nodeValue933, nodeValue1691, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4369 node4369Labels = Sparse.eval nodeValue4369 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4369) = mixedMoment B node4369 node4369Labels := rfl
  simpa [nodeValue4369, Sparse.eval] using hc.symm

theorem sound4374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4374 node4374Labels = Sparse.eval nodeValue4374 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4374) = mixedMoment B node4374 node4374Labels := rfl
  simpa [nodeValue4374, Sparse.eval] using hc.symm

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

theorem sound4458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4458 node4458Labels = Sparse.eval nodeValue4458 (mixedVector B) := by
  have h := singleton4458 B _hB
  rw [sound1041 B _hB _hF, sound1724 B _hB _hF] at h
  norm_num [nodeValue4458, nodeValue1041, nodeValue1724, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4463 node4463Labels = Sparse.eval nodeValue4463 (mixedVector B) := by
  have h := singleton4463 B _hB
  rw [sound1046 B _hB _hF, sound1750 B _hB _hF] at h
  norm_num [nodeValue4463, nodeValue1046, nodeValue1750, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4502 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4502 node4502Labels = 0 := by
  exact mixedMoment_order_one B hB node4502 node4502Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4502 node4502Labels = Sparse.eval nodeValue4502 (mixedVector B) := by
  simpa only [nodeValue4502, Sparse.eval_nil] using zero4502 B _hB _hF

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

theorem sound4811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4811 node4811Labels = Sparse.eval nodeValue4811 (mixedVector B) := by
  have h := singleton4811 B _hB
  rw [sound2029 B _hB _hF, sound2225 B _hB _hF] at h
  norm_num [nodeValue4811, nodeValue2029, nodeValue2225, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem zero4895 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4895 node4895Labels = 0 := by
  exact mixedMoment_order_one B hB node4895 node4895Labels 1
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

theorem sound4875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4875 node4875Labels = Sparse.eval nodeValue4875 (mixedVector B) := by
  have h := singleton4875 B _hB
  rw [sound2116 B _hB _hF, sound2288 B _hB _hF] at h
  norm_num [nodeValue4875, nodeValue2116, nodeValue2288, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4895 node4895Labels = Sparse.eval nodeValue4895 (mixedVector B) := by
  simpa only [nodeValue4895, Sparse.eval_nil] using zero4895 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources47
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1513 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1513 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1513 + difference 0 0) (sourceB1513 + difference 0 0) sourceC1513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1513 + difference 0 0) (sourceB1513 + difference 0 0) sourceC1513) = raw23017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1513 sourceB1513 sourceC1513 difference raw23017; decide +kernel
    rw [ha]
    exact (canonical23017 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1513 + difference 1 0) (sourceB1513 + difference 0 1) sourceC1513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 613) := by
    have ha : (tripleCharges (sourceA1513 + difference 1 0) (sourceB1513 + difference 0 1) sourceC1513) = raw23018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1513 sourceB1513 sourceC1513 difference raw23018; decide +kernel
    rw [ha]
    exact (canonical23018 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1513 + difference 2 0) (sourceB1513 + difference 0 2) sourceC1513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 582) := by
    have ha : (tripleCharges (sourceA1513 + difference 2 0) (sourceB1513 + difference 0 2) sourceC1513) = raw23019 := by
      apply Matrix.ext; unfold tripleCharges sourceA1513 sourceB1513 sourceC1513 difference raw23019; decide +kernel
    rw [ha]
    exact (canonical23019 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1513 + difference 3 0) (sourceB1513 + difference 0 3) sourceC1513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 582) := by
    have ha : (tripleCharges (sourceA1513 + difference 3 0) (sourceB1513 + difference 0 3) sourceC1513) = raw23020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1513 sourceB1513 sourceC1513 difference raw23020; decide +kernel
    rw [ha]
    exact (canonical23020 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1513 + difference 4 0) (sourceB1513 + difference 0 4) sourceC1513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 588) := by
    have ha : (tripleCharges (sourceA1513 + difference 4 0) (sourceB1513 + difference 0 4) sourceC1513) = raw23021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1513 sourceB1513 sourceC1513 difference raw23021; decide +kernel
    rw [ha]
    exact (canonical23021 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1513 + difference 5 0) (sourceB1513 + difference 0 5) sourceC1513) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 590) := by
    have ha : (tripleCharges (sourceA1513 + difference 5 0) (sourceB1513 + difference 0 5) sourceC1513) = raw23022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1513 sourceB1513 sourceC1513 difference raw23022; decide +kernel
    rw [ha]
    exact (canonical23022 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1513 + sourceB1513) sourceC1513) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1513 + sourceB1513) sourceC1513) = raw23023 := by
      apply Matrix.ext; unfold doubleCharges sourceA1513 sourceB1513 sourceC1513 raw23023; decide +kernel
    rw [ha]
    exact (canonical23023 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1513 sourceB1513 sourceC1513
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1513, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1514 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1514 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1514 + difference 1 0) (sourceB1514 + difference 0 1) sourceC1514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 613) := by
    have ha : (tripleCharges (sourceA1514 + difference 1 0) (sourceB1514 + difference 0 1) sourceC1514) = raw23018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1514 sourceB1514 sourceC1514 difference raw23018; decide +kernel
    rw [ha]
    exact (canonical23018 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1514 + difference 1 1) (sourceB1514 + difference 1 1) sourceC1514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1514 + difference 1 1) (sourceB1514 + difference 1 1) sourceC1514) = raw23017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1514 sourceB1514 sourceC1514 difference raw23017; decide +kernel
    rw [ha]
    exact (canonical23017 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1514 + difference 1 2) (sourceB1514 + difference 2 1) sourceC1514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 932) := by
    have ha : (tripleCharges (sourceA1514 + difference 1 2) (sourceB1514 + difference 2 1) sourceC1514) = raw23024 := by
      apply Matrix.ext; unfold tripleCharges sourceA1514 sourceB1514 sourceC1514 difference raw23024; decide +kernel
    rw [ha]
    exact (canonical23024 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1514 + difference 1 3) (sourceB1514 + difference 3 1) sourceC1514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 932) := by
    have ha : (tripleCharges (sourceA1514 + difference 1 3) (sourceB1514 + difference 3 1) sourceC1514) = raw23025 := by
      apply Matrix.ext; unfold tripleCharges sourceA1514 sourceB1514 sourceC1514 difference raw23025; decide +kernel
    rw [ha]
    exact (canonical23025 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1514 + difference 1 4) (sourceB1514 + difference 4 1) sourceC1514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1514 + difference 1 4) (sourceB1514 + difference 4 1) sourceC1514) = raw23026 := by
      apply Matrix.ext; unfold tripleCharges sourceA1514 sourceB1514 sourceC1514 difference raw23026; decide +kernel
    rw [ha]
    exact (canonical23026 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1514 + difference 1 5) (sourceB1514 + difference 5 1) sourceC1514) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1082) := by
    have ha : (tripleCharges (sourceA1514 + difference 1 5) (sourceB1514 + difference 5 1) sourceC1514) = raw23027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1514 sourceB1514 sourceC1514 difference raw23027; decide +kernel
    rw [ha]
    exact (canonical23027 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1514 + sourceB1514) sourceC1514) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1514 + sourceB1514) sourceC1514) = raw23023 := by
      apply Matrix.ext; unfold doubleCharges sourceA1514 sourceB1514 sourceC1514 raw23023; decide +kernel
    rw [ha]
    exact (canonical23023 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1514 sourceB1514 sourceC1514
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1514, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1515 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1515 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1515 + difference 0 1) (sourceB1515 + difference 1 0) sourceC1515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA1515 + difference 0 1) (sourceB1515 + difference 1 0) sourceC1515) = raw23028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1515 sourceB1515 sourceC1515 difference raw23028; decide +kernel
    rw [ha]
    exact (canonical23028 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1515 + difference 1 1) (sourceB1515 + difference 1 1) sourceC1515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1515 + difference 1 1) (sourceB1515 + difference 1 1) sourceC1515) = raw23017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1515 sourceB1515 sourceC1515 difference raw23017; decide +kernel
    rw [ha]
    exact (canonical23017 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1515 + difference 2 1) (sourceB1515 + difference 1 2) sourceC1515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 946) := by
    have ha : (tripleCharges (sourceA1515 + difference 2 1) (sourceB1515 + difference 1 2) sourceC1515) = raw23029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1515 sourceB1515 sourceC1515 difference raw23029; decide +kernel
    rw [ha]
    exact (canonical23029 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1515 + difference 3 1) (sourceB1515 + difference 1 3) sourceC1515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 946) := by
    have ha : (tripleCharges (sourceA1515 + difference 3 1) (sourceB1515 + difference 1 3) sourceC1515) = raw23030 := by
      apply Matrix.ext; unfold tripleCharges sourceA1515 sourceB1515 sourceC1515 difference raw23030; decide +kernel
    rw [ha]
    exact (canonical23030 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1515 + difference 4 1) (sourceB1515 + difference 1 4) sourceC1515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 952) := by
    have ha : (tripleCharges (sourceA1515 + difference 4 1) (sourceB1515 + difference 1 4) sourceC1515) = raw23031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1515 sourceB1515 sourceC1515 difference raw23031; decide +kernel
    rw [ha]
    exact (canonical23031 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1515 + difference 5 1) (sourceB1515 + difference 1 5) sourceC1515) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 954) := by
    have ha : (tripleCharges (sourceA1515 + difference 5 1) (sourceB1515 + difference 1 5) sourceC1515) = raw23032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1515 sourceB1515 sourceC1515 difference raw23032; decide +kernel
    rw [ha]
    exact (canonical23032 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1515 + sourceB1515) sourceC1515) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1515 + sourceB1515) sourceC1515) = raw23023 := by
      apply Matrix.ext; unfold doubleCharges sourceA1515 sourceB1515 sourceC1515 raw23023; decide +kernel
    rw [ha]
    exact (canonical23023 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1515 sourceB1515 sourceC1515
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1515, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1516 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1516 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1516 + difference 2 0) (sourceB1516 + difference 0 2) sourceC1516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 582) := by
    have ha : (tripleCharges (sourceA1516 + difference 2 0) (sourceB1516 + difference 0 2) sourceC1516) = raw23019 := by
      apply Matrix.ext; unfold tripleCharges sourceA1516 sourceB1516 sourceC1516 difference raw23019; decide +kernel
    rw [ha]
    exact (canonical23019 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1516 + difference 2 1) (sourceB1516 + difference 1 2) sourceC1516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 946) := by
    have ha : (tripleCharges (sourceA1516 + difference 2 1) (sourceB1516 + difference 1 2) sourceC1516) = raw23029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1516 sourceB1516 sourceC1516 difference raw23029; decide +kernel
    rw [ha]
    exact (canonical23029 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1516 + difference 2 2) (sourceB1516 + difference 2 2) sourceC1516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1516 + difference 2 2) (sourceB1516 + difference 2 2) sourceC1516) = raw23017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1516 sourceB1516 sourceC1516 difference raw23017; decide +kernel
    rw [ha]
    exact (canonical23017 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1516 + difference 2 3) (sourceB1516 + difference 3 2) sourceC1516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 906) := by
    have ha : (tripleCharges (sourceA1516 + difference 2 3) (sourceB1516 + difference 3 2) sourceC1516) = raw23033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1516 sourceB1516 sourceC1516 difference raw23033; decide +kernel
    rw [ha]
    exact (canonical23033 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1516 + difference 2 4) (sourceB1516 + difference 4 2) sourceC1516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA1516 + difference 2 4) (sourceB1516 + difference 4 2) sourceC1516) = raw23034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1516 sourceB1516 sourceC1516 difference raw23034; decide +kernel
    rw [ha]
    exact (canonical23034 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1516 + difference 2 5) (sourceB1516 + difference 5 2) sourceC1516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1516 + difference 2 5) (sourceB1516 + difference 5 2) sourceC1516) = raw23035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1516 sourceB1516 sourceC1516 difference raw23035; decide +kernel
    rw [ha]
    exact (canonical23035 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1516 + sourceB1516) sourceC1516) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1516 + sourceB1516) sourceC1516) = raw23023 := by
      apply Matrix.ext; unfold doubleCharges sourceA1516 sourceB1516 sourceC1516 raw23023; decide +kernel
    rw [ha]
    exact (canonical23023 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1516 sourceB1516 sourceC1516
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1516, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1522 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1522 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1522 + difference 0 1) (sourceB1522 + difference 1 0) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4875) := by
    have ha : (tripleCharges (sourceA1522 + difference 0 1) (sourceB1522 + difference 1 0) sourceC1522) = raw11419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw11419; decide +kernel
    rw [ha]
    exact (canonical11419 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1522 + difference 0 2) (sourceB1522 + difference 2 0) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA1522 + difference 0 2) (sourceB1522 + difference 2 0) sourceC1522) = raw11420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw11420; decide +kernel
    rw [ha]
    exact (canonical11420 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1522 + difference 0 3) (sourceB1522 + difference 3 0) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA1522 + difference 0 3) (sourceB1522 + difference 3 0) sourceC1522) = raw11421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw11421; decide +kernel
    rw [ha]
    exact (canonical11421 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1522 + difference 0 4) (sourceB1522 + difference 4 0) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1522 + difference 0 4) (sourceB1522 + difference 4 0) sourceC1522) = raw21144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw21144; decide +kernel
    rw [ha]
    exact (canonical21144 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1522 + difference 0 5) (sourceB1522 + difference 5 0) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1522 + difference 0 5) (sourceB1522 + difference 5 0) sourceC1522) = raw11422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw11422; decide +kernel
    rw [ha]
    exact (canonical11422 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1522 + difference 1 0) (sourceB1522 + difference 0 1) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4186) := by
    have ha : (tripleCharges (sourceA1522 + difference 1 0) (sourceB1522 + difference 0 1) sourceC1522) = raw23149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23149; decide +kernel
    rw [ha]
    exact (canonical23149 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1522 + difference 1 2) (sourceB1522 + difference 2 1) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA1522 + difference 1 2) (sourceB1522 + difference 2 1) sourceC1522) = raw23150 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23150; decide +kernel
    rw [ha]
    exact (canonical23150 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1522 + difference 1 3) (sourceB1522 + difference 3 1) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA1522 + difference 1 3) (sourceB1522 + difference 3 1) sourceC1522) = raw23151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23151; decide +kernel
    rw [ha]
    exact (canonical23151 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1522 + difference 1 4) (sourceB1522 + difference 4 1) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1522 + difference 1 4) (sourceB1522 + difference 4 1) sourceC1522) = raw11403 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw11403; decide +kernel
    rw [ha]
    exact (canonical11403 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1522 + difference 1 5) (sourceB1522 + difference 5 1) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1522 + difference 1 5) (sourceB1522 + difference 5 1) sourceC1522) = raw23152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23152; decide +kernel
    rw [ha]
    exact (canonical23152 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1522 + difference 2 0) (sourceB1522 + difference 0 2) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4155) := by
    have ha : (tripleCharges (sourceA1522 + difference 2 0) (sourceB1522 + difference 0 2) sourceC1522) = raw23153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23153; decide +kernel
    rw [ha]
    exact (canonical23153 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1522 + difference 2 1) (sourceB1522 + difference 1 2) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4369) := by
    have ha : (tripleCharges (sourceA1522 + difference 2 1) (sourceB1522 + difference 1 2) sourceC1522) = raw23154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23154; decide +kernel
    rw [ha]
    exact (canonical23154 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1522 + difference 2 3) (sourceB1522 + difference 3 2) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4329) := by
    have ha : (tripleCharges (sourceA1522 + difference 2 3) (sourceB1522 + difference 3 2) sourceC1522) = raw23155 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23155; decide +kernel
    rw [ha]
    exact (canonical23155 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1522 + difference 2 4) (sourceB1522 + difference 4 2) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1522 + difference 2 4) (sourceB1522 + difference 4 2) sourceC1522) = raw11408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw11408; decide +kernel
    rw [ha]
    exact (canonical11408 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1522 + difference 2 5) (sourceB1522 + difference 5 2) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1522 + difference 2 5) (sourceB1522 + difference 5 2) sourceC1522) = raw23156 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23156; decide +kernel
    rw [ha]
    exact (canonical23156 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1522 + difference 3 0) (sourceB1522 + difference 0 3) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4155) := by
    have ha : (tripleCharges (sourceA1522 + difference 3 0) (sourceB1522 + difference 0 3) sourceC1522) = raw23157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23157; decide +kernel
    rw [ha]
    exact (canonical23157 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1522 + difference 3 1) (sourceB1522 + difference 1 3) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4369) := by
    have ha : (tripleCharges (sourceA1522 + difference 3 1) (sourceB1522 + difference 1 3) sourceC1522) = raw23158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23158; decide +kernel
    rw [ha]
    exact (canonical23158 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1522 + difference 3 2) (sourceB1522 + difference 2 3) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4329) := by
    have ha : (tripleCharges (sourceA1522 + difference 3 2) (sourceB1522 + difference 2 3) sourceC1522) = raw23159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23159; decide +kernel
    rw [ha]
    exact (canonical23159 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1522 + difference 3 4) (sourceB1522 + difference 4 3) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1522 + difference 3 4) (sourceB1522 + difference 4 3) sourceC1522) = raw11413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw11413; decide +kernel
    rw [ha]
    exact (canonical11413 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1522 + difference 3 5) (sourceB1522 + difference 5 3) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1522 + difference 3 5) (sourceB1522 + difference 5 3) sourceC1522) = raw23160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23160; decide +kernel
    rw [ha]
    exact (canonical23160 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1522 + difference 4 0) (sourceB1522 + difference 0 4) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4161) := by
    have ha : (tripleCharges (sourceA1522 + difference 4 0) (sourceB1522 + difference 0 4) sourceC1522) = raw23161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23161; decide +kernel
    rw [ha]
    exact (canonical23161 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1522 + difference 4 1) (sourceB1522 + difference 1 4) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4374) := by
    have ha : (tripleCharges (sourceA1522 + difference 4 1) (sourceB1522 + difference 1 4) sourceC1522) = raw23162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23162; decide +kernel
    rw [ha]
    exact (canonical23162 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1522 + difference 4 2) (sourceB1522 + difference 2 4) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA1522 + difference 4 2) (sourceB1522 + difference 2 4) sourceC1522) = raw23163 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23163; decide +kernel
    rw [ha]
    exact (canonical23163 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1522 + difference 4 3) (sourceB1522 + difference 3 4) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA1522 + difference 4 3) (sourceB1522 + difference 3 4) sourceC1522) = raw23164 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23164; decide +kernel
    rw [ha]
    exact (canonical23164 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1522 + difference 4 5) (sourceB1522 + difference 5 4) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1522 + difference 4 5) (sourceB1522 + difference 5 4) sourceC1522) = raw23165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw23165; decide +kernel
    rw [ha]
    exact (canonical23165 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1522 + difference 5 0) (sourceB1522 + difference 0 5) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4161) := by
    have ha : (tripleCharges (sourceA1522 + difference 5 0) (sourceB1522 + difference 0 5) sourceC1522) = raw21157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw21157; decide +kernel
    rw [ha]
    exact (canonical21157 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1522 + difference 5 1) (sourceB1522 + difference 1 5) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4374) := by
    have ha : (tripleCharges (sourceA1522 + difference 5 1) (sourceB1522 + difference 1 5) sourceC1522) = raw21158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw21158; decide +kernel
    rw [ha]
    exact (canonical21158 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1522 + difference 5 2) (sourceB1522 + difference 2 5) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA1522 + difference 5 2) (sourceB1522 + difference 2 5) sourceC1522) = raw21159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw21159; decide +kernel
    rw [ha]
    exact (canonical21159 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1522 + difference 5 3) (sourceB1522 + difference 3 5) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA1522 + difference 5 3) (sourceB1522 + difference 3 5) sourceC1522) = raw21160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw21160; decide +kernel
    rw [ha]
    exact (canonical21160 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1522 + difference 5 4) (sourceB1522 + difference 4 5) sourceC1522) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1522 + difference 5 4) (sourceB1522 + difference 4 5) sourceC1522) = raw11423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1522 sourceB1522 sourceC1522 difference raw11423; decide +kernel
    rw [ha]
    exact (canonical11423 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1522 sourceB1522 sourceC1522
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1522, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1524 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1524 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1524 + difference 0 1) (sourceB1524 + difference 1 0) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2288) := by
    have ha : (tripleCharges (sourceA1524 + difference 0 1) (sourceB1524 + difference 1 0) sourceC1524) = raw11449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw11449; decide +kernel
    rw [ha]
    exact (canonical11449 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1524 + difference 0 2) (sourceB1524 + difference 2 0) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA1524 + difference 0 2) (sourceB1524 + difference 2 0) sourceC1524) = raw11450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw11450; decide +kernel
    rw [ha]
    exact (canonical11450 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1524 + difference 0 3) (sourceB1524 + difference 3 0) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA1524 + difference 0 3) (sourceB1524 + difference 3 0) sourceC1524) = raw11451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw11451; decide +kernel
    rw [ha]
    exact (canonical11451 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1524 + difference 0 4) (sourceB1524 + difference 4 0) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA1524 + difference 0 4) (sourceB1524 + difference 4 0) sourceC1524) = raw21196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw21196; decide +kernel
    rw [ha]
    exact (canonical21196 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1524 + difference 0 5) (sourceB1524 + difference 5 0) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA1524 + difference 0 5) (sourceB1524 + difference 5 0) sourceC1524) = raw11452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw11452; decide +kernel
    rw [ha]
    exact (canonical11452 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1524 + difference 1 0) (sourceB1524 + difference 0 1) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1536) := by
    have ha : (tripleCharges (sourceA1524 + difference 1 0) (sourceB1524 + difference 0 1) sourceC1524) = raw23188 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23188; decide +kernel
    rw [ha]
    exact (canonical23188 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1524 + difference 1 2) (sourceB1524 + difference 2 1) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1691) := by
    have ha : (tripleCharges (sourceA1524 + difference 1 2) (sourceB1524 + difference 2 1) sourceC1524) = raw23189 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23189; decide +kernel
    rw [ha]
    exact (canonical23189 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1524 + difference 1 3) (sourceB1524 + difference 3 1) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1691) := by
    have ha : (tripleCharges (sourceA1524 + difference 1 3) (sourceB1524 + difference 3 1) sourceC1524) = raw23190 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23190; decide +kernel
    rw [ha]
    exact (canonical23190 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1524 + difference 1 4) (sourceB1524 + difference 4 1) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1753) := by
    have ha : (tripleCharges (sourceA1524 + difference 1 4) (sourceB1524 + difference 4 1) sourceC1524) = raw11433 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw11433; decide +kernel
    rw [ha]
    exact (canonical11433 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1524 + difference 1 5) (sourceB1524 + difference 5 1) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1753) := by
    have ha : (tripleCharges (sourceA1524 + difference 1 5) (sourceB1524 + difference 5 1) sourceC1524) = raw23191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23191; decide +kernel
    rw [ha]
    exact (canonical23191 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1524 + difference 2 0) (sourceB1524 + difference 0 2) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1515) := by
    have ha : (tripleCharges (sourceA1524 + difference 2 0) (sourceB1524 + difference 0 2) sourceC1524) = raw23192 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23192; decide +kernel
    rw [ha]
    exact (canonical23192 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1524 + difference 2 1) (sourceB1524 + difference 1 2) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1721) := by
    have ha : (tripleCharges (sourceA1524 + difference 2 1) (sourceB1524 + difference 1 2) sourceC1524) = raw23193 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23193; decide +kernel
    rw [ha]
    exact (canonical23193 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1524 + difference 2 3) (sourceB1524 + difference 3 2) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1671) := by
    have ha : (tripleCharges (sourceA1524 + difference 2 3) (sourceB1524 + difference 3 2) sourceC1524) = raw23194 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23194; decide +kernel
    rw [ha]
    exact (canonical23194 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1524 + difference 2 4) (sourceB1524 + difference 4 2) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1524 + difference 2 4) (sourceB1524 + difference 4 2) sourceC1524) = raw11438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw11438; decide +kernel
    rw [ha]
    exact (canonical11438 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1524 + difference 2 5) (sourceB1524 + difference 5 2) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1524 + difference 2 5) (sourceB1524 + difference 5 2) sourceC1524) = raw23195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23195; decide +kernel
    rw [ha]
    exact (canonical23195 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1524 + difference 3 0) (sourceB1524 + difference 0 3) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1515) := by
    have ha : (tripleCharges (sourceA1524 + difference 3 0) (sourceB1524 + difference 0 3) sourceC1524) = raw23196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23196; decide +kernel
    rw [ha]
    exact (canonical23196 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1524 + difference 3 1) (sourceB1524 + difference 1 3) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1721) := by
    have ha : (tripleCharges (sourceA1524 + difference 3 1) (sourceB1524 + difference 1 3) sourceC1524) = raw23197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23197; decide +kernel
    rw [ha]
    exact (canonical23197 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1524 + difference 3 2) (sourceB1524 + difference 2 3) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1671) := by
    have ha : (tripleCharges (sourceA1524 + difference 3 2) (sourceB1524 + difference 2 3) sourceC1524) = raw23198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23198; decide +kernel
    rw [ha]
    exact (canonical23198 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1524 + difference 3 4) (sourceB1524 + difference 4 3) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1524 + difference 3 4) (sourceB1524 + difference 4 3) sourceC1524) = raw11443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw11443; decide +kernel
    rw [ha]
    exact (canonical11443 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1524 + difference 3 5) (sourceB1524 + difference 5 3) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1524 + difference 3 5) (sourceB1524 + difference 5 3) sourceC1524) = raw23199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23199; decide +kernel
    rw [ha]
    exact (canonical23199 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1524 + difference 4 0) (sourceB1524 + difference 0 4) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1533) := by
    have ha : (tripleCharges (sourceA1524 + difference 4 0) (sourceB1524 + difference 0 4) sourceC1524) = raw23200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23200; decide +kernel
    rw [ha]
    exact (canonical23200 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1524 + difference 4 1) (sourceB1524 + difference 1 4) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1748) := by
    have ha : (tripleCharges (sourceA1524 + difference 4 1) (sourceB1524 + difference 1 4) sourceC1524) = raw23201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23201; decide +kernel
    rw [ha]
    exact (canonical23201 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1524 + difference 4 2) (sourceB1524 + difference 2 4) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA1524 + difference 4 2) (sourceB1524 + difference 2 4) sourceC1524) = raw23202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23202; decide +kernel
    rw [ha]
    exact (canonical23202 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1524 + difference 4 3) (sourceB1524 + difference 3 4) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA1524 + difference 4 3) (sourceB1524 + difference 3 4) sourceC1524) = raw23203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23203; decide +kernel
    rw [ha]
    exact (canonical23203 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1524 + difference 4 5) (sourceB1524 + difference 5 4) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1524 + difference 4 5) (sourceB1524 + difference 5 4) sourceC1524) = raw23204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw23204; decide +kernel
    rw [ha]
    exact (canonical23204 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1524 + difference 5 0) (sourceB1524 + difference 0 5) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1533) := by
    have ha : (tripleCharges (sourceA1524 + difference 5 0) (sourceB1524 + difference 0 5) sourceC1524) = raw21209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw21209; decide +kernel
    rw [ha]
    exact (canonical21209 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1524 + difference 5 1) (sourceB1524 + difference 1 5) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1748) := by
    have ha : (tripleCharges (sourceA1524 + difference 5 1) (sourceB1524 + difference 1 5) sourceC1524) = raw21210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw21210; decide +kernel
    rw [ha]
    exact (canonical21210 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1524 + difference 5 2) (sourceB1524 + difference 2 5) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA1524 + difference 5 2) (sourceB1524 + difference 2 5) sourceC1524) = raw21211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw21211; decide +kernel
    rw [ha]
    exact (canonical21211 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1524 + difference 5 3) (sourceB1524 + difference 3 5) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA1524 + difference 5 3) (sourceB1524 + difference 3 5) sourceC1524) = raw21212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw21212; decide +kernel
    rw [ha]
    exact (canonical21212 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1524 + difference 5 4) (sourceB1524 + difference 4 5) sourceC1524) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1524 + difference 5 4) (sourceB1524 + difference 4 5) sourceC1524) = raw11453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1524 sourceB1524 sourceC1524 difference raw11453; decide +kernel
    rw [ha]
    exact (canonical11453 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1524 sourceB1524 sourceC1524
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1524, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1525 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1525 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1525 + difference 0 0) (sourceB1525 + difference 0 0) sourceC1525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1050) := by
    have ha : (tripleCharges (sourceA1525 + difference 0 0) (sourceB1525 + difference 0 0) sourceC1525) = raw23205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1525 sourceB1525 sourceC1525 difference raw23205; decide +kernel
    rw [ha]
    exact (canonical23205 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1525 + difference 1 0) (sourceB1525 + difference 0 1) sourceC1525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 614) := by
    have ha : (tripleCharges (sourceA1525 + difference 1 0) (sourceB1525 + difference 0 1) sourceC1525) = raw23206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1525 sourceB1525 sourceC1525 difference raw23206; decide +kernel
    rw [ha]
    exact (canonical23206 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1525 + difference 2 0) (sourceB1525 + difference 0 2) sourceC1525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 583) := by
    have ha : (tripleCharges (sourceA1525 + difference 2 0) (sourceB1525 + difference 0 2) sourceC1525) = raw23207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1525 sourceB1525 sourceC1525 difference raw23207; decide +kernel
    rw [ha]
    exact (canonical23207 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1525 + difference 3 0) (sourceB1525 + difference 0 3) sourceC1525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 583) := by
    have ha : (tripleCharges (sourceA1525 + difference 3 0) (sourceB1525 + difference 0 3) sourceC1525) = raw23208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1525 sourceB1525 sourceC1525 difference raw23208; decide +kernel
    rw [ha]
    exact (canonical23208 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1525 + difference 4 0) (sourceB1525 + difference 0 4) sourceC1525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 589) := by
    have ha : (tripleCharges (sourceA1525 + difference 4 0) (sourceB1525 + difference 0 4) sourceC1525) = raw23209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1525 sourceB1525 sourceC1525 difference raw23209; decide +kernel
    rw [ha]
    exact (canonical23209 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1525 + difference 5 0) (sourceB1525 + difference 0 5) sourceC1525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 589) := by
    have ha : (tripleCharges (sourceA1525 + difference 5 0) (sourceB1525 + difference 0 5) sourceC1525) = raw21222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1525 sourceB1525 sourceC1525 difference raw21222; decide +kernel
    rw [ha]
    exact (canonical21222 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1525 + sourceB1525) sourceC1525) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1525 + sourceB1525) sourceC1525) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA1525 sourceB1525 sourceC1525 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1525 sourceB1525 sourceC1525
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1525, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1526 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1526 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1526 + difference 1 0) (sourceB1526 + difference 0 1) sourceC1526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 614) := by
    have ha : (tripleCharges (sourceA1526 + difference 1 0) (sourceB1526 + difference 0 1) sourceC1526) = raw23206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1526 sourceB1526 sourceC1526 difference raw23206; decide +kernel
    rw [ha]
    exact (canonical23206 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1526 + difference 1 1) (sourceB1526 + difference 1 1) sourceC1526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1050) := by
    have ha : (tripleCharges (sourceA1526 + difference 1 1) (sourceB1526 + difference 1 1) sourceC1526) = raw23205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1526 sourceB1526 sourceC1526 difference raw23205; decide +kernel
    rw [ha]
    exact (canonical23205 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1526 + difference 1 2) (sourceB1526 + difference 2 1) sourceC1526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 933) := by
    have ha : (tripleCharges (sourceA1526 + difference 1 2) (sourceB1526 + difference 2 1) sourceC1526) = raw23210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1526 sourceB1526 sourceC1526 difference raw23210; decide +kernel
    rw [ha]
    exact (canonical23210 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1526 + difference 1 3) (sourceB1526 + difference 3 1) sourceC1526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 933) := by
    have ha : (tripleCharges (sourceA1526 + difference 1 3) (sourceB1526 + difference 3 1) sourceC1526) = raw23211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1526 sourceB1526 sourceC1526 difference raw23211; decide +kernel
    rw [ha]
    exact (canonical23211 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1526 + difference 1 4) (sourceB1526 + difference 4 1) sourceC1526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1086) := by
    have ha : (tripleCharges (sourceA1526 + difference 1 4) (sourceB1526 + difference 4 1) sourceC1526) = raw21227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1526 sourceB1526 sourceC1526 difference raw21227; decide +kernel
    rw [ha]
    exact (canonical21227 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1526 + difference 1 5) (sourceB1526 + difference 5 1) sourceC1526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1086) := by
    have ha : (tripleCharges (sourceA1526 + difference 1 5) (sourceB1526 + difference 5 1) sourceC1526) = raw23212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1526 sourceB1526 sourceC1526 difference raw23212; decide +kernel
    rw [ha]
    exact (canonical23212 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1526 + sourceB1526) sourceC1526) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1526 + sourceB1526) sourceC1526) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA1526 sourceB1526 sourceC1526 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1526 sourceB1526 sourceC1526
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1526, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1527 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1527 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1527 + difference 0 1) (sourceB1527 + difference 1 0) sourceC1527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2116) := by
    have ha : (tripleCharges (sourceA1527 + difference 0 1) (sourceB1527 + difference 1 0) sourceC1527) = raw11462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1527 sourceB1527 sourceC1527 difference raw11462; decide +kernel
    rw [ha]
    exact (canonical11462 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1527 + difference 1 1) (sourceB1527 + difference 1 1) sourceC1527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1050) := by
    have ha : (tripleCharges (sourceA1527 + difference 1 1) (sourceB1527 + difference 1 1) sourceC1527) = raw23205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1527 sourceB1527 sourceC1527 difference raw23205; decide +kernel
    rw [ha]
    exact (canonical23205 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1527 + difference 2 1) (sourceB1527 + difference 1 2) sourceC1527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 947) := by
    have ha : (tripleCharges (sourceA1527 + difference 2 1) (sourceB1527 + difference 1 2) sourceC1527) = raw23213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1527 sourceB1527 sourceC1527 difference raw23213; decide +kernel
    rw [ha]
    exact (canonical23213 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1527 + difference 3 1) (sourceB1527 + difference 1 3) sourceC1527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 947) := by
    have ha : (tripleCharges (sourceA1527 + difference 3 1) (sourceB1527 + difference 1 3) sourceC1527) = raw23214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1527 sourceB1527 sourceC1527 difference raw23214; decide +kernel
    rw [ha]
    exact (canonical23214 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1527 + difference 4 1) (sourceB1527 + difference 1 4) sourceC1527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 953) := by
    have ha : (tripleCharges (sourceA1527 + difference 4 1) (sourceB1527 + difference 1 4) sourceC1527) = raw23215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1527 sourceB1527 sourceC1527 difference raw23215; decide +kernel
    rw [ha]
    exact (canonical23215 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1527 + difference 5 1) (sourceB1527 + difference 1 5) sourceC1527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 953) := by
    have ha : (tripleCharges (sourceA1527 + difference 5 1) (sourceB1527 + difference 1 5) sourceC1527) = raw21230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1527 sourceB1527 sourceC1527 difference raw21230; decide +kernel
    rw [ha]
    exact (canonical21230 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1527 + sourceB1527) sourceC1527) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1527 + sourceB1527) sourceC1527) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA1527 sourceB1527 sourceC1527 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1527 sourceB1527 sourceC1527
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1527, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1528 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1528 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1528 + difference 2 0) (sourceB1528 + difference 0 2) sourceC1528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 583) := by
    have ha : (tripleCharges (sourceA1528 + difference 2 0) (sourceB1528 + difference 0 2) sourceC1528) = raw23207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1528 sourceB1528 sourceC1528 difference raw23207; decide +kernel
    rw [ha]
    exact (canonical23207 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1528 + difference 2 1) (sourceB1528 + difference 1 2) sourceC1528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 947) := by
    have ha : (tripleCharges (sourceA1528 + difference 2 1) (sourceB1528 + difference 1 2) sourceC1528) = raw23213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1528 sourceB1528 sourceC1528 difference raw23213; decide +kernel
    rw [ha]
    exact (canonical23213 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1528 + difference 2 2) (sourceB1528 + difference 2 2) sourceC1528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1050) := by
    have ha : (tripleCharges (sourceA1528 + difference 2 2) (sourceB1528 + difference 2 2) sourceC1528) = raw23205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1528 sourceB1528 sourceC1528 difference raw23205; decide +kernel
    rw [ha]
    exact (canonical23205 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1528 + difference 2 3) (sourceB1528 + difference 3 2) sourceC1528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 907) := by
    have ha : (tripleCharges (sourceA1528 + difference 2 3) (sourceB1528 + difference 3 2) sourceC1528) = raw23216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1528 sourceB1528 sourceC1528 difference raw23216; decide +kernel
    rw [ha]
    exact (canonical23216 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1528 + difference 2 4) (sourceB1528 + difference 4 2) sourceC1528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1528 + difference 2 4) (sourceB1528 + difference 4 2) sourceC1528) = raw23217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1528 sourceB1528 sourceC1528 difference raw23217; decide +kernel
    rw [ha]
    exact (canonical23217 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1528 + difference 2 5) (sourceB1528 + difference 5 2) sourceC1528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1528 + difference 2 5) (sourceB1528 + difference 5 2) sourceC1528) = raw23218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1528 sourceB1528 sourceC1528 difference raw23218; decide +kernel
    rw [ha]
    exact (canonical23218 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1528 + sourceB1528) sourceC1528) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1528 + sourceB1528) sourceC1528) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA1528 sourceB1528 sourceC1528 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1528 sourceB1528 sourceC1528
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1528, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1296 : Integer.Sparse.reindex keyMap MixedData.row1296 = numericRow1296 := by decide +kernel

theorem numericCheck1296 (x : Master → ℝ) : Integer.Sparse.eval numericRow1296 x =
    (1 : ℝ) * reducedSource1296 x := by
  norm_num [numericRow1296, reducedSource1296, Integer.Sparse.eval, Sparse.eval, nodeValue582, nodeValue588, nodeValue590, nodeValue613, nodeValue1049, nodeValue4084]

theorem reindexCheck1297 : Integer.Sparse.reindex keyMap MixedData.row1297 = numericRow1297 := by decide +kernel

theorem numericCheck1297 (x : Master → ℝ) : Integer.Sparse.eval numericRow1297 x =
    (1 : ℝ) * reducedSource1297 x := by
  norm_num [numericRow1297, reducedSource1297, Integer.Sparse.eval, Sparse.eval, nodeValue613, nodeValue932, nodeValue1049, nodeValue1082, nodeValue1087, nodeValue4084]

theorem reindexCheck1298 : Integer.Sparse.reindex keyMap MixedData.row1298 = numericRow1298 := by decide +kernel

theorem numericCheck1298 (x : Master → ℝ) : Integer.Sparse.eval numericRow1298 x =
    (1 : ℝ) * reducedSource1298 x := by
  norm_num [numericRow1298, reducedSource1298, Integer.Sparse.eval, Sparse.eval, nodeValue946, nodeValue952, nodeValue954, nodeValue1049, nodeValue2115, nodeValue4084]

theorem reindexCheck1299 : Integer.Sparse.reindex keyMap MixedData.row1299 = numericRow1299 := by decide +kernel

theorem numericCheck1299 (x : Master → ℝ) : Integer.Sparse.eval numericRow1299 x =
    (1 : ℝ) * reducedSource1299 x := by
  norm_num [numericRow1299, reducedSource1299, Integer.Sparse.eval, Sparse.eval, nodeValue582, nodeValue906, nodeValue946, nodeValue1040, nodeValue1042, nodeValue1049, nodeValue4084]

theorem reindexCheck1302 : Integer.Sparse.reindex keyMap MixedData.row1302 = numericRow1302 := by decide +kernel

theorem numericCheck1302 (x : Master → ℝ) : Integer.Sparse.eval numericRow1302 x =
    (4 : ℝ) * reducedSource1302 x := by
  norm_num [numericRow1302, reducedSource1302, Integer.Sparse.eval, Sparse.eval, nodeValue4155, nodeValue4161, nodeValue4186, nodeValue4329, nodeValue4335, nodeValue4355, nodeValue4369, nodeValue4374, nodeValue4458, nodeValue4463, nodeValue4502, nodeValue4811, nodeValue4875, nodeValue4895] <;> ring

theorem reindexCheck1304 : Integer.Sparse.reindex keyMap MixedData.row1304 = numericRow1304 := by decide +kernel

theorem numericCheck1304 (x : Master → ℝ) : Integer.Sparse.eval numericRow1304 x =
    (1 : ℝ) * reducedSource1304 x := by
  norm_num [numericRow1304, reducedSource1304, Integer.Sparse.eval, Sparse.eval, nodeValue1515, nodeValue1533, nodeValue1536, nodeValue1671, nodeValue1689, nodeValue1691, nodeValue1721, nodeValue1724, nodeValue1748, nodeValue1750, nodeValue1753, nodeValue2225, nodeValue2288, nodeValue2291]

theorem reindexCheck1305 : Integer.Sparse.reindex keyMap MixedData.row1305 = numericRow1305 := by decide +kernel

theorem numericCheck1305 (x : Master → ℝ) : Integer.Sparse.eval numericRow1305 x =
    (1 : ℝ) * reducedSource1305 x := by
  norm_num [numericRow1305, reducedSource1305, Integer.Sparse.eval, Sparse.eval, nodeValue583, nodeValue589, nodeValue614, nodeValue1050, nodeValue4083]

theorem reindexCheck1306 : Integer.Sparse.reindex keyMap MixedData.row1306 = numericRow1306 := by decide +kernel

theorem numericCheck1306 (x : Master → ℝ) : Integer.Sparse.eval numericRow1306 x =
    (1 : ℝ) * reducedSource1306 x := by
  norm_num [numericRow1306, reducedSource1306, Integer.Sparse.eval, Sparse.eval, nodeValue614, nodeValue933, nodeValue1050, nodeValue1086, nodeValue4083]

theorem reindexCheck1307 : Integer.Sparse.reindex keyMap MixedData.row1307 = numericRow1307 := by decide +kernel

theorem numericCheck1307 (x : Master → ℝ) : Integer.Sparse.eval numericRow1307 x =
    (1 : ℝ) * reducedSource1307 x := by
  norm_num [numericRow1307, reducedSource1307, Integer.Sparse.eval, Sparse.eval, nodeValue947, nodeValue953, nodeValue1050, nodeValue2116, nodeValue4083]

theorem reindexCheck1308 : Integer.Sparse.reindex keyMap MixedData.row1308 = numericRow1308 := by decide +kernel

theorem numericCheck1308 (x : Master → ℝ) : Integer.Sparse.eval numericRow1308 x =
    (1 : ℝ) * reducedSource1308 x := by
  norm_num [numericRow1308, reducedSource1308, Integer.Sparse.eval, Sparse.eval, nodeValue583, nodeValue907, nodeValue947, nodeValue1041, nodeValue1050, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1296 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1296 (mixedVector B) = 0 := by
  have h582 : mixedVector B (Sum.inr 582) = Sparse.eval nodeValue582 (mixedVector B) := by
    change mixedMoment B node582 node582Labels = _
    exact sound582 B hB hF
  have h588 : mixedVector B (Sum.inr 588) = Sparse.eval nodeValue588 (mixedVector B) := by
    change mixedMoment B node588 node588Labels = _
    exact sound588 B hB hF
  have h590 : mixedVector B (Sum.inr 590) = Sparse.eval nodeValue590 (mixedVector B) := by
    change mixedMoment B node590 node590Labels = _
    exact sound590 B hB hF
  have h613 : mixedVector B (Sum.inr 613) = Sparse.eval nodeValue613 (mixedVector B) := by
    change mixedMoment B node613 node613Labels = _
    exact sound613 B hB hF
  have h1049 : mixedVector B (Sum.inr 1049) = Sparse.eval nodeValue1049 (mixedVector B) := by
    change mixedMoment B node1049 node1049Labels = _
    exact sound1049 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1513, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h582, h588, h590, h613, h1049, h4084, reducedSource1296] using sourceEq1513 B hB

theorem rowSound1296 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1296 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1296, numericCheck1296, reducedZero1296 B hB hF, mul_zero]

theorem reducedZero1297 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1297 (mixedVector B) = 0 := by
  have h613 : mixedVector B (Sum.inr 613) = Sparse.eval nodeValue613 (mixedVector B) := by
    change mixedMoment B node613 node613Labels = _
    exact sound613 B hB hF
  have h932 : mixedVector B (Sum.inr 932) = Sparse.eval nodeValue932 (mixedVector B) := by
    change mixedMoment B node932 node932Labels = _
    exact sound932 B hB hF
  have h1049 : mixedVector B (Sum.inr 1049) = Sparse.eval nodeValue1049 (mixedVector B) := by
    change mixedMoment B node1049 node1049Labels = _
    exact sound1049 B hB hF
  have h1082 : mixedVector B (Sum.inr 1082) = Sparse.eval nodeValue1082 (mixedVector B) := by
    change mixedMoment B node1082 node1082Labels = _
    exact sound1082 B hB hF
  have h1087 : mixedVector B (Sum.inr 1087) = Sparse.eval nodeValue1087 (mixedVector B) := by
    change mixedMoment B node1087 node1087Labels = _
    exact sound1087 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1514, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h613, h932, h1049, h1082, h1087, h4084, reducedSource1297] using sourceEq1514 B hB

theorem rowSound1297 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1297 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1297, numericCheck1297, reducedZero1297 B hB hF, mul_zero]

theorem reducedZero1298 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1298 (mixedVector B) = 0 := by
  have h946 : mixedVector B (Sum.inr 946) = Sparse.eval nodeValue946 (mixedVector B) := by
    change mixedMoment B node946 node946Labels = _
    exact sound946 B hB hF
  have h952 : mixedVector B (Sum.inr 952) = Sparse.eval nodeValue952 (mixedVector B) := by
    change mixedMoment B node952 node952Labels = _
    exact sound952 B hB hF
  have h954 : mixedVector B (Sum.inr 954) = Sparse.eval nodeValue954 (mixedVector B) := by
    change mixedMoment B node954 node954Labels = _
    exact sound954 B hB hF
  have h1049 : mixedVector B (Sum.inr 1049) = Sparse.eval nodeValue1049 (mixedVector B) := by
    change mixedMoment B node1049 node1049Labels = _
    exact sound1049 B hB hF
  have h2115 : mixedVector B (Sum.inr 2115) = Sparse.eval nodeValue2115 (mixedVector B) := by
    change mixedMoment B node2115 node2115Labels = _
    exact sound2115 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1515, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h946, h952, h954, h1049, h2115, h4084, reducedSource1298] using sourceEq1515 B hB

theorem rowSound1298 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1298 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1298, numericCheck1298, reducedZero1298 B hB hF, mul_zero]

theorem reducedZero1299 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1299 (mixedVector B) = 0 := by
  have h582 : mixedVector B (Sum.inr 582) = Sparse.eval nodeValue582 (mixedVector B) := by
    change mixedMoment B node582 node582Labels = _
    exact sound582 B hB hF
  have h906 : mixedVector B (Sum.inr 906) = Sparse.eval nodeValue906 (mixedVector B) := by
    change mixedMoment B node906 node906Labels = _
    exact sound906 B hB hF
  have h946 : mixedVector B (Sum.inr 946) = Sparse.eval nodeValue946 (mixedVector B) := by
    change mixedMoment B node946 node946Labels = _
    exact sound946 B hB hF
  have h1040 : mixedVector B (Sum.inr 1040) = Sparse.eval nodeValue1040 (mixedVector B) := by
    change mixedMoment B node1040 node1040Labels = _
    exact sound1040 B hB hF
  have h1042 : mixedVector B (Sum.inr 1042) = Sparse.eval nodeValue1042 (mixedVector B) := by
    change mixedMoment B node1042 node1042Labels = _
    exact sound1042 B hB hF
  have h1049 : mixedVector B (Sum.inr 1049) = Sparse.eval nodeValue1049 (mixedVector B) := by
    change mixedMoment B node1049 node1049Labels = _
    exact sound1049 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1516, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h582, h906, h946, h1040, h1042, h1049, h4084, reducedSource1299] using sourceEq1516 B hB

theorem rowSound1299 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1299 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1299, numericCheck1299, reducedZero1299 B hB hF, mul_zero]

theorem reducedZero1302 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1302 (mixedVector B) = 0 := by
  have h4155 : mixedVector B (Sum.inr 4155) = Sparse.eval nodeValue4155 (mixedVector B) := by
    change mixedMoment B node4155 node4155Labels = _
    exact sound4155 B hB hF
  have h4161 : mixedVector B (Sum.inr 4161) = Sparse.eval nodeValue4161 (mixedVector B) := by
    change mixedMoment B node4161 node4161Labels = _
    exact sound4161 B hB hF
  have h4186 : mixedVector B (Sum.inr 4186) = Sparse.eval nodeValue4186 (mixedVector B) := by
    change mixedMoment B node4186 node4186Labels = _
    exact sound4186 B hB hF
  have h4329 : mixedVector B (Sum.inr 4329) = Sparse.eval nodeValue4329 (mixedVector B) := by
    change mixedMoment B node4329 node4329Labels = _
    exact sound4329 B hB hF
  have h4335 : mixedVector B (Sum.inr 4335) = Sparse.eval nodeValue4335 (mixedVector B) := by
    change mixedMoment B node4335 node4335Labels = _
    exact sound4335 B hB hF
  have h4355 : mixedVector B (Sum.inr 4355) = Sparse.eval nodeValue4355 (mixedVector B) := by
    change mixedMoment B node4355 node4355Labels = _
    exact sound4355 B hB hF
  have h4369 : mixedVector B (Sum.inr 4369) = Sparse.eval nodeValue4369 (mixedVector B) := by
    change mixedMoment B node4369 node4369Labels = _
    exact sound4369 B hB hF
  have h4374 : mixedVector B (Sum.inr 4374) = Sparse.eval nodeValue4374 (mixedVector B) := by
    change mixedMoment B node4374 node4374Labels = _
    exact sound4374 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4502 : mixedVector B (Sum.inr 4502) = Sparse.eval nodeValue4502 (mixedVector B) := by
    change mixedMoment B node4502 node4502Labels = _
    exact sound4502 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4875 : mixedVector B (Sum.inr 4875) = Sparse.eval nodeValue4875 (mixedVector B) := by
    change mixedMoment B node4875 node4875Labels = _
    exact sound4875 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  simpa only [sourceForm1522, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4155, h4161, h4186, h4329, h4335, h4355, h4369, h4374, h4458, h4463, h4502, h4811, h4875, h4895, reducedSource1302] using sourceEq1522 B hB

theorem rowSound1302 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1302 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1302, numericCheck1302, reducedZero1302 B hB hF, mul_zero]

theorem reducedZero1304 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1304 (mixedVector B) = 0 := by
  have h1515 : mixedVector B (Sum.inr 1515) = Sparse.eval nodeValue1515 (mixedVector B) := by
    change mixedMoment B node1515 node1515Labels = _
    exact sound1515 B hB hF
  have h1533 : mixedVector B (Sum.inr 1533) = Sparse.eval nodeValue1533 (mixedVector B) := by
    change mixedMoment B node1533 node1533Labels = _
    exact sound1533 B hB hF
  have h1536 : mixedVector B (Sum.inr 1536) = Sparse.eval nodeValue1536 (mixedVector B) := by
    change mixedMoment B node1536 node1536Labels = _
    exact sound1536 B hB hF
  have h1671 : mixedVector B (Sum.inr 1671) = Sparse.eval nodeValue1671 (mixedVector B) := by
    change mixedMoment B node1671 node1671Labels = _
    exact sound1671 B hB hF
  have h1689 : mixedVector B (Sum.inr 1689) = Sparse.eval nodeValue1689 (mixedVector B) := by
    change mixedMoment B node1689 node1689Labels = _
    exact sound1689 B hB hF
  have h1691 : mixedVector B (Sum.inr 1691) = Sparse.eval nodeValue1691 (mixedVector B) := by
    change mixedMoment B node1691 node1691Labels = _
    exact sound1691 B hB hF
  have h1721 : mixedVector B (Sum.inr 1721) = Sparse.eval nodeValue1721 (mixedVector B) := by
    change mixedMoment B node1721 node1721Labels = _
    exact sound1721 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h1748 : mixedVector B (Sum.inr 1748) = Sparse.eval nodeValue1748 (mixedVector B) := by
    change mixedMoment B node1748 node1748Labels = _
    exact sound1748 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h1753 : mixedVector B (Sum.inr 1753) = Sparse.eval nodeValue1753 (mixedVector B) := by
    change mixedMoment B node1753 node1753Labels = _
    exact sound1753 B hB hF
  have h2225 : mixedVector B (Sum.inr 2225) = Sparse.eval nodeValue2225 (mixedVector B) := by
    change mixedMoment B node2225 node2225Labels = _
    exact sound2225 B hB hF
  have h2288 : mixedVector B (Sum.inr 2288) = Sparse.eval nodeValue2288 (mixedVector B) := by
    change mixedMoment B node2288 node2288Labels = _
    exact sound2288 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  simpa only [sourceForm1524, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1515, h1533, h1536, h1671, h1689, h1691, h1721, h1724, h1748, h1750, h1753, h2225, h2288, h2291, reducedSource1304] using sourceEq1524 B hB

theorem rowSound1304 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1304 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1304, numericCheck1304, reducedZero1304 B hB hF, mul_zero]

theorem reducedZero1305 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1305 (mixedVector B) = 0 := by
  have h583 : mixedVector B (Sum.inr 583) = Sparse.eval nodeValue583 (mixedVector B) := by
    change mixedMoment B node583 node583Labels = _
    exact sound583 B hB hF
  have h589 : mixedVector B (Sum.inr 589) = Sparse.eval nodeValue589 (mixedVector B) := by
    change mixedMoment B node589 node589Labels = _
    exact sound589 B hB hF
  have h614 : mixedVector B (Sum.inr 614) = Sparse.eval nodeValue614 (mixedVector B) := by
    change mixedMoment B node614 node614Labels = _
    exact sound614 B hB hF
  have h1050 : mixedVector B (Sum.inr 1050) = Sparse.eval nodeValue1050 (mixedVector B) := by
    change mixedMoment B node1050 node1050Labels = _
    exact sound1050 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1525, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h583, h589, h614, h1050, h4083, reducedSource1305] using sourceEq1525 B hB

theorem rowSound1305 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1305 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1305, numericCheck1305, reducedZero1305 B hB hF, mul_zero]

theorem reducedZero1306 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1306 (mixedVector B) = 0 := by
  have h614 : mixedVector B (Sum.inr 614) = Sparse.eval nodeValue614 (mixedVector B) := by
    change mixedMoment B node614 node614Labels = _
    exact sound614 B hB hF
  have h933 : mixedVector B (Sum.inr 933) = Sparse.eval nodeValue933 (mixedVector B) := by
    change mixedMoment B node933 node933Labels = _
    exact sound933 B hB hF
  have h1050 : mixedVector B (Sum.inr 1050) = Sparse.eval nodeValue1050 (mixedVector B) := by
    change mixedMoment B node1050 node1050Labels = _
    exact sound1050 B hB hF
  have h1086 : mixedVector B (Sum.inr 1086) = Sparse.eval nodeValue1086 (mixedVector B) := by
    change mixedMoment B node1086 node1086Labels = _
    exact sound1086 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1526, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h614, h933, h1050, h1086, h4083, reducedSource1306] using sourceEq1526 B hB

theorem rowSound1306 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1306 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1306, numericCheck1306, reducedZero1306 B hB hF, mul_zero]

theorem reducedZero1307 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1307 (mixedVector B) = 0 := by
  have h947 : mixedVector B (Sum.inr 947) = Sparse.eval nodeValue947 (mixedVector B) := by
    change mixedMoment B node947 node947Labels = _
    exact sound947 B hB hF
  have h953 : mixedVector B (Sum.inr 953) = Sparse.eval nodeValue953 (mixedVector B) := by
    change mixedMoment B node953 node953Labels = _
    exact sound953 B hB hF
  have h1050 : mixedVector B (Sum.inr 1050) = Sparse.eval nodeValue1050 (mixedVector B) := by
    change mixedMoment B node1050 node1050Labels = _
    exact sound1050 B hB hF
  have h2116 : mixedVector B (Sum.inr 2116) = Sparse.eval nodeValue2116 (mixedVector B) := by
    change mixedMoment B node2116 node2116Labels = _
    exact sound2116 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1527, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h947, h953, h1050, h2116, h4083, reducedSource1307] using sourceEq1527 B hB

theorem rowSound1307 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1307 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1307, numericCheck1307, reducedZero1307 B hB hF, mul_zero]

theorem reducedZero1308 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1308 (mixedVector B) = 0 := by
  have h583 : mixedVector B (Sum.inr 583) = Sparse.eval nodeValue583 (mixedVector B) := by
    change mixedMoment B node583 node583Labels = _
    exact sound583 B hB hF
  have h907 : mixedVector B (Sum.inr 907) = Sparse.eval nodeValue907 (mixedVector B) := by
    change mixedMoment B node907 node907Labels = _
    exact sound907 B hB hF
  have h947 : mixedVector B (Sum.inr 947) = Sparse.eval nodeValue947 (mixedVector B) := by
    change mixedMoment B node947 node947Labels = _
    exact sound947 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h1050 : mixedVector B (Sum.inr 1050) = Sparse.eval nodeValue1050 (mixedVector B) := by
    change mixedMoment B node1050 node1050Labels = _
    exact sound1050 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1528, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h583, h907, h947, h1041, h1050, h4083, reducedSource1308] using sourceEq1528 B hB

theorem rowSound1308 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1308 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1308, numericCheck1308, reducedZero1308 B hB hF, mul_zero]

theorem sourceRowsAt1296 : MixedData.sourceRows (1296 : Fin 2425) =
    MixedData.row1296 := by decide +kernel

theorem sourceRowsAt1297 : MixedData.sourceRows (1297 : Fin 2425) =
    MixedData.row1297 := by decide +kernel

theorem sourceRowsAt1298 : MixedData.sourceRows (1298 : Fin 2425) =
    MixedData.row1298 := by decide +kernel

theorem sourceRowsAt1299 : MixedData.sourceRows (1299 : Fin 2425) =
    MixedData.row1299 := by decide +kernel

theorem sourceRowsAt1300 : MixedData.sourceRows (1300 : Fin 2425) =
    MixedData.row1300 := by decide +kernel

theorem sourceRowsAt1301 : MixedData.sourceRows (1301 : Fin 2425) =
    MixedData.row1301 := by decide +kernel

theorem sourceRowsAt1302 : MixedData.sourceRows (1302 : Fin 2425) =
    MixedData.row1302 := by decide +kernel

theorem sourceRowsAt1303 : MixedData.sourceRows (1303 : Fin 2425) =
    MixedData.row1303 := by decide +kernel

theorem sourceRowsAt1304 : MixedData.sourceRows (1304 : Fin 2425) =
    MixedData.row1304 := by decide +kernel

theorem sourceRowsAt1305 : MixedData.sourceRows (1305 : Fin 2425) =
    MixedData.row1305 := by decide +kernel

theorem sourceRowsAt1306 : MixedData.sourceRows (1306 : Fin 2425) =
    MixedData.row1306 := by decide +kernel

theorem sourceRowsAt1307 : MixedData.sourceRows (1307 : Fin 2425) =
    MixedData.row1307 := by decide +kernel

theorem sourceRowsAt1308 : MixedData.sourceRows (1308 : Fin 2425) =
    MixedData.row1308 := by decide +kernel

theorem sourceRowsAt1309 : MixedData.sourceRows (1309 : Fin 2425) =
    MixedData.row1309 := by decide +kernel

theorem sourceRowsAt1310 : MixedData.sourceRows (1310 : Fin 2425) =
    MixedData.row1310 := by decide +kernel

theorem sourceRowsAt1311 : MixedData.sourceRows (1311 : Fin 2425) =
    MixedData.row1311 := by decide +kernel

theorem chunkSound81_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 81) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1296 ∨ k.val = 1297 ∨ k.val = 1298 ∨ k.val = 1299 ∨ k.val = 1300 ∨ k.val = 1301 ∨ k.val = 1302 ∨ k.val = 1303 ∨ k.val = 1304 ∨ k.val = 1305 ∨ k.val = 1306 ∨ k.val = 1307 ∨ k.val = 1308 ∨ k.val = 1309 ∨ k.val = 1310 ∨ k.val = 1311 := by omega
  rcases heq with h1296 | h1297 | h1298 | h1299 | h1300 | h1301 | h1302 | h1303 | h1304 | h1305 | h1306 | h1307 | h1308 | h1309 | h1310 | h1311
  · have he : k = (1296 : Fin 2425) := Fin.ext h1296
    subst k
    rw [sourceRowsAt1296]
    exact rowSound1296 B hB hF
  · have he : k = (1297 : Fin 2425) := Fin.ext h1297
    subst k
    rw [sourceRowsAt1297]
    exact rowSound1297 B hB hF
  · have he : k = (1298 : Fin 2425) := Fin.ext h1298
    subst k
    rw [sourceRowsAt1298]
    exact rowSound1298 B hB hF
  · have he : k = (1299 : Fin 2425) := Fin.ext h1299
    subst k
    rw [sourceRowsAt1299]
    exact rowSound1299 B hB hF
  · have he : k = (1300 : Fin 2425) := Fin.ext h1300
    subst k
    rw [sourceRowsAt1300]
    exact rowSound1300_e B hB hF
  · have he : k = (1301 : Fin 2425) := Fin.ext h1301
    subst k
    rw [sourceRowsAt1301]
    exact rowSound1301_e B hB hF
  · have he : k = (1302 : Fin 2425) := Fin.ext h1302
    subst k
    rw [sourceRowsAt1302]
    exact rowSound1302 B hB hF
  · have he : k = (1303 : Fin 2425) := Fin.ext h1303
    subst k
    rw [sourceRowsAt1303]
    exact rowSound1303_e B hB hF
  · have he : k = (1304 : Fin 2425) := Fin.ext h1304
    subst k
    rw [sourceRowsAt1304]
    exact rowSound1304 B hB hF
  · have he : k = (1305 : Fin 2425) := Fin.ext h1305
    subst k
    rw [sourceRowsAt1305]
    exact rowSound1305 B hB hF
  · have he : k = (1306 : Fin 2425) := Fin.ext h1306
    subst k
    rw [sourceRowsAt1306]
    exact rowSound1306 B hB hF
  · have he : k = (1307 : Fin 2425) := Fin.ext h1307
    subst k
    rw [sourceRowsAt1307]
    exact rowSound1307 B hB hF
  · have he : k = (1308 : Fin 2425) := Fin.ext h1308
    subst k
    rw [sourceRowsAt1308]
    exact rowSound1308 B hB hF
  · have he : k = (1309 : Fin 2425) := Fin.ext h1309
    subst k
    rw [sourceRowsAt1309]
    exact rowSound1309_e B hB hF
  · have he : k = (1310 : Fin 2425) := Fin.ext h1310
    subst k
    rw [sourceRowsAt1310]
    exact rowSound1310_e B hB hF
  · have he : k = (1311 : Fin 2425) := Fin.ext h1311
    subst k
    rw [sourceRowsAt1311]
    exact rowSound1311_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81_e_oai
