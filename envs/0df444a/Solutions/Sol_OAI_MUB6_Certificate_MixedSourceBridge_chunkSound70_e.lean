-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound70_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:31:48.129641+00:00
-- url     : https://prove2.me/submissions/4d5cb146-0473-4ccc-b79c-43cab88e13cd

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1120_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1121_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1124_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1130_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound1131_e

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

theorem canonical1365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1365 raw1365Labels = mixedMoment B node4543 node4543Labels := by
  calc
    mixedMoment B raw1365 raw1365Labels = mixedMoment B raw1365step0 raw1365step0Labels := by
      have ha : raw1365step0 = (fun i j => raw1365 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1365step0 raw1365; decide +kernel
      have hl : raw1365step0Labels = raw1365Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1365 raw1365Labels permutation32 permutation4
    mixedMoment B raw1365step0 raw1365step0Labels = mixedMoment B raw1365step1 raw1365step1Labels := by
      have ha : raw1365step1 = raw1365step0 := by apply Matrix.ext; unfold raw1365step1 raw1365step0; decide +kernel
      have hl : raw1365step0Labels = labelEmbedding7 ∘ raw1365step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1365step0 raw1365step0Labels raw1365step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4543 node4543Labels := by rfl

theorem canonical1366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1366 raw1366Labels = mixedMoment B node1128 node1128Labels := by
  calc
    mixedMoment B raw1366 raw1366Labels = mixedMoment B raw1366step0 raw1366step0Labels := by
      have ha : raw1366step0 = (fun i j => raw1366 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1366step0 raw1366; decide +kernel
      have hl : raw1366step0Labels = raw1366Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1366 raw1366Labels permutation32 permutation4
    _ = mixedMoment B node1128 node1128Labels := by rfl

theorem canonical1367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1367 raw1367Labels = mixedMoment B node2184 node2184Labels := by
  calc
    mixedMoment B raw1367 raw1367Labels = mixedMoment B raw1367step0 raw1367step0Labels := by
      have ha : raw1367step0 = (fun i j => raw1367 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1367step0 raw1367; decide +kernel
      have hl : raw1367step0Labels = raw1367Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1367 raw1367Labels permutation145 permutation6
    mixedMoment B raw1367step0 raw1367step0Labels = mixedMoment B raw1367step1 raw1367step1Labels := by
      have ha : raw1367step1 = raw1367step0 := by apply Matrix.ext; unfold raw1367step1 raw1367step0; decide +kernel
      have hl : raw1367step0Labels = labelEmbedding1 ∘ raw1367step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1367step0 raw1367step0Labels raw1367step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2184 node2184Labels := by rfl

theorem canonical1392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1392 raw1392Labels = mixedMoment B node4557 node4557Labels := by
  calc
    mixedMoment B raw1392 raw1392Labels = mixedMoment B raw1392step0 raw1392step0Labels := by
      have ha : raw1392step0 = (fun i j => raw1392 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1392step0 raw1392; decide +kernel
      have hl : raw1392step0Labels = raw1392Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1392 raw1392Labels permutation8 permutation4
    mixedMoment B raw1392step0 raw1392step0Labels = mixedMoment B raw1392step1 raw1392step1Labels := by
      have ha : raw1392step1 = raw1392step0 := by apply Matrix.ext; unfold raw1392step1 raw1392step0; decide +kernel
      have hl : raw1392step0Labels = labelEmbedding7 ∘ raw1392step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1392step0 raw1392step0Labels raw1392step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4557 node4557Labels := by rfl

theorem canonical1393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1393 raw1393Labels = mixedMoment B node1143 node1143Labels := by
  calc
    mixedMoment B raw1393 raw1393Labels = mixedMoment B raw1393step0 raw1393step0Labels := by
      have ha : raw1393step0 = (fun i j => raw1393 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1393step0 raw1393; decide +kernel
      have hl : raw1393step0Labels = raw1393Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1393 raw1393Labels permutation8 permutation4
    _ = mixedMoment B node1143 node1143Labels := by rfl

theorem canonical1394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1394 raw1394Labels = mixedMoment B node2167 node2167Labels := by
  calc
    mixedMoment B raw1394 raw1394Labels = mixedMoment B raw1394step0 raw1394step0Labels := by
      have ha : raw1394step0 = (fun i j => raw1394 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1394step0 raw1394; decide +kernel
      have hl : raw1394step0Labels = raw1394Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1394 raw1394Labels permutation31 permutation6
    mixedMoment B raw1394step0 raw1394step0Labels = mixedMoment B raw1394step1 raw1394step1Labels := by
      have ha : raw1394step1 = raw1394step0 := by apply Matrix.ext; unfold raw1394step1 raw1394step0; decide +kernel
      have hl : raw1394step0Labels = labelEmbedding1 ∘ raw1394step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1394step0 raw1394step0Labels raw1394step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2167 node2167Labels := by rfl

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

theorem canonical1446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1446 raw1446Labels = mixedMoment B node4621 node4621Labels := by
  calc
    mixedMoment B raw1446 raw1446Labels = mixedMoment B raw1446step0 raw1446step0Labels := by
      have ha : raw1446step0 = (fun i j => raw1446 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1446step0 raw1446; decide +kernel
      have hl : raw1446step0Labels = raw1446Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1446 raw1446Labels permutation2 permutation4
    mixedMoment B raw1446step0 raw1446step0Labels = mixedMoment B raw1446step1 raw1446step1Labels := by
      have ha : raw1446step1 = raw1446step0 := by apply Matrix.ext; unfold raw1446step1 raw1446step0; decide +kernel
      have hl : raw1446step0Labels = labelEmbedding7 ∘ raw1446step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1446step0 raw1446step0Labels raw1446step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4621 node4621Labels := by rfl

theorem canonical1447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1447 raw1447Labels = mixedMoment B node1297 node1297Labels := by
  calc
    mixedMoment B raw1447 raw1447Labels = mixedMoment B raw1447step0 raw1447step0Labels := by
      have ha : raw1447step0 = (fun i j => raw1447 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1447step0 raw1447; decide +kernel
      have hl : raw1447step0Labels = raw1447Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1447 raw1447Labels permutation2 permutation4
    _ = mixedMoment B node1297 node1297Labels := by rfl

theorem canonical1448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1448 raw1448Labels = mixedMoment B node2289 node2289Labels := by
  calc
    mixedMoment B raw1448 raw1448Labels = mixedMoment B raw1448step0 raw1448step0Labels := by
      have ha : raw1448step0 = (fun i j => raw1448 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1448step0 raw1448; decide +kernel
      have hl : raw1448step0Labels = raw1448Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1448 raw1448Labels permutation7 permutation6
    mixedMoment B raw1448step0 raw1448step0Labels = mixedMoment B raw1448step1 raw1448step1Labels := by
      have ha : raw1448step1 = raw1448step0 := by apply Matrix.ext; unfold raw1448step1 raw1448step0; decide +kernel
      have hl : raw1448step0Labels = labelEmbedding1 ∘ raw1448step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1448step0 raw1448step0Labels raw1448step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2289 node2289Labels := by rfl

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

theorem canonical1737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1737 raw1737Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw1737 raw1737Labels = mixedMoment B raw1737step0 raw1737step0Labels := by
      have ha : raw1737step0 = (fun i j => raw1737 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1737step0 raw1737; decide +kernel
      have hl : raw1737step0Labels = raw1737Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1737 raw1737Labels permutation32 permutation4
    mixedMoment B raw1737step0 raw1737step0Labels = mixedMoment B raw1737step1 raw1737step1Labels := by
      have ha : raw1737step1 = raw1737step0 := by apply Matrix.ext; unfold raw1737step1 raw1737step0; decide +kernel
      have hl : raw1737step0Labels = labelEmbedding7 ∘ raw1737step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1737step0 raw1737step0Labels raw1737step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical1738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1738 raw1738Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw1738 raw1738Labels = mixedMoment B raw1738step0 raw1738step0Labels := by
      have ha : raw1738step0 = (fun i j => raw1738 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1738step0 raw1738; decide +kernel
      have hl : raw1738step0Labels = raw1738Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1738 raw1738Labels permutation32 permutation4
    _ = mixedMoment B node2022 node2022Labels := by rfl

theorem canonical1739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1739 raw1739Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw1739 raw1739Labels = mixedMoment B raw1739step0 raw1739step0Labels := by
      have ha : raw1739step0 = (fun i j => raw1739 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1739step0 raw1739; decide +kernel
      have hl : raw1739step0Labels = raw1739Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1739 raw1739Labels permutation34 permutation6
    mixedMoment B raw1739step0 raw1739step0Labels = mixedMoment B raw1739step1 raw1739step1Labels := by
      have ha : raw1739step1 = -raw1739step0 := by apply Matrix.ext; change ∀ i j, raw1739step1 i j = -(raw1739step0 i j); unfold raw1739step1 raw1739step0; decide +kernel
      have hl : raw1739step1Labels = raw1739step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1739step1 raw1739step1Labels = mixedMoment B raw1739step2 raw1739step2Labels := by
      have ha : raw1739step2 = raw1739step1 := by apply Matrix.ext; unfold raw1739step2 raw1739step1; decide +kernel
      have hl : raw1739step1Labels = labelEmbedding1 ∘ raw1739step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1739step1 raw1739step1Labels raw1739step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19855 raw19855Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw19855 raw19855Labels = mixedMoment B raw19855step0 raw19855step0Labels := by
      have hz : ∀ j, raw19855 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19855step0 = (fun i j => raw19855 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19855step0 raw19855; decide +kernel
      have hl : raw19855step0Labels = raw19855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19855 raw19855Labels permutation346 hz
    mixedMoment B raw19855step0 raw19855step0Labels = mixedMoment B raw19855step1 raw19855step1Labels := by
      have hz : ∀ j, raw19855step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19855step1 = (fun i j => raw19855step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19855step1 raw19855step0; decide +kernel
      have hl : raw19855step1Labels = raw19855step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19855step0 raw19855step0Labels permutation56 hz
    mixedMoment B raw19855step1 raw19855step1Labels = mixedMoment B raw19855step2 raw19855step2Labels := by
      have ha : raw19855step2 = (fun i j => raw19855step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19855step2 raw19855step1; decide +kernel
      have hl : raw19855step2Labels = raw19855step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19855step1 raw19855step1Labels permutation29 permutation2
    mixedMoment B raw19855step2 raw19855step2Labels = mixedMoment B raw19855step3 raw19855step3Labels := by
      have ha : raw19855step3 = -raw19855step2 := by apply Matrix.ext; change ∀ i j, raw19855step3 i j = -(raw19855step2 i j); unfold raw19855step3 raw19855step2; decide +kernel
      have hl : raw19855step3Labels = raw19855step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1710 node1710Labels := by rfl

theorem canonical19856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19856 raw19856Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw19856 raw19856Labels = mixedMoment B raw19856step0 raw19856step0Labels := by
      have hz : ∀ j, raw19856 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19856step0 = (fun i j => raw19856 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19856step0 raw19856; decide +kernel
      have hl : raw19856step0Labels = raw19856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19856 raw19856Labels permutation346 hz
    mixedMoment B raw19856step0 raw19856step0Labels = mixedMoment B raw19856step1 raw19856step1Labels := by
      have hz : ∀ j, raw19856step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19856step1 = (fun i j => raw19856step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19856step1 raw19856step0; decide +kernel
      have hl : raw19856step1Labels = raw19856step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19856step0 raw19856step0Labels permutation56 hz
    mixedMoment B raw19856step1 raw19856step1Labels = mixedMoment B raw19856step2 raw19856step2Labels := by
      have ha : raw19856step2 = (fun i j => raw19856step1 (permutation29 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19856step2 raw19856step1; decide +kernel
      have hl : raw19856step2Labels = raw19856step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19856step1 raw19856step1Labels permutation29 permutation0
    mixedMoment B raw19856step2 raw19856step2Labels = mixedMoment B raw19856step3 raw19856step3Labels := by
      have ha : raw19856step3 = -raw19856step2 := by apply Matrix.ext; change ∀ i j, raw19856step3 i j = -(raw19856step2 i j); unfold raw19856step3 raw19856step2; decide +kernel
      have hl : raw19856step3Labels = raw19856step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical19864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19864 raw19864Labels = mixedMoment B node1231 node1231Labels := by
  calc
    mixedMoment B raw19864 raw19864Labels = mixedMoment B raw19864step0 raw19864step0Labels := by
      have hz : ∀ j, raw19864 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19864step0 = (fun i j => raw19864 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19864step0 raw19864; decide +kernel
      have hl : raw19864step0Labels = raw19864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19864 raw19864Labels permutation346 hz
    mixedMoment B raw19864step0 raw19864step0Labels = mixedMoment B raw19864step1 raw19864step1Labels := by
      have hz : ∀ j, raw19864step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19864step1 = (fun i j => raw19864step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19864step1 raw19864step0; decide +kernel
      have hl : raw19864step1Labels = raw19864step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19864step0 raw19864step0Labels permutation56 hz
    _ = mixedMoment B node1231 node1231Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20840 raw20840Labels = mixedMoment B node1617 node1617Labels := by
  calc
    mixedMoment B raw20840 raw20840Labels = mixedMoment B raw20840step0 raw20840step0Labels := by
      have hz : ∀ j, raw20840 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20840step0 = (fun i j => raw20840 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20840step0 raw20840; decide +kernel
      have hl : raw20840step0Labels = raw20840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20840 raw20840Labels permutation346 hz
    mixedMoment B raw20840step0 raw20840step0Labels = mixedMoment B raw20840step1 raw20840step1Labels := by
      have ha : raw20840step1 = (fun i j => raw20840step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20840step1 raw20840step0; decide +kernel
      have hl : raw20840step1Labels = raw20840step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20840step0 raw20840step0Labels permutation38 permutation4
    mixedMoment B raw20840step1 raw20840step1Labels = mixedMoment B raw20840step2 raw20840step2Labels := by
      have ha : raw20840step2 = -raw20840step1 := by apply Matrix.ext; change ∀ i j, raw20840step2 i j = -(raw20840step1 i j); unfold raw20840step2 raw20840step1; decide +kernel
      have hl : raw20840step2Labels = raw20840step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1617 node1617Labels := by rfl

theorem canonical20841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20841 raw20841Labels = mixedMoment B node1617 node1617Labels := by
  calc
    mixedMoment B raw20841 raw20841Labels = mixedMoment B raw20841step0 raw20841step0Labels := by
      have hz : ∀ j, raw20841 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20841step0 = (fun i j => raw20841 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20841step0 raw20841; decide +kernel
      have hl : raw20841step0Labels = raw20841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20841 raw20841Labels permutation265 hz
    mixedMoment B raw20841step0 raw20841step0Labels = mixedMoment B raw20841step1 raw20841step1Labels := by
      have ha : raw20841step1 = (fun i j => raw20841step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20841step1 raw20841step0; decide +kernel
      have hl : raw20841step1Labels = raw20841step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20841step0 raw20841step0Labels permutation38 permutation4
    mixedMoment B raw20841step1 raw20841step1Labels = mixedMoment B raw20841step2 raw20841step2Labels := by
      have ha : raw20841step2 = -raw20841step1 := by apply Matrix.ext; change ∀ i j, raw20841step2 i j = -(raw20841step1 i j); unfold raw20841step2 raw20841step1; decide +kernel
      have hl : raw20841step2Labels = raw20841step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1617 node1617Labels := by rfl

theorem canonical20842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20842 raw20842Labels = mixedMoment B node1630 node1630Labels := by
  calc
    mixedMoment B raw20842 raw20842Labels = mixedMoment B raw20842step0 raw20842step0Labels := by
      have hz : ∀ j, raw20842 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20842step0 = (fun i j => raw20842 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20842step0 raw20842; decide +kernel
      have hl : raw20842step0Labels = raw20842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20842 raw20842Labels permutation346 hz
    mixedMoment B raw20842step0 raw20842step0Labels = mixedMoment B raw20842step1 raw20842step1Labels := by
      have hz : ∀ j, raw20842step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20842step1 = (fun i j => raw20842step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20842step1 raw20842step0; decide +kernel
      have hl : raw20842step1Labels = raw20842step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20842step0 raw20842step0Labels permutation56 hz
    mixedMoment B raw20842step1 raw20842step1Labels = mixedMoment B raw20842step2 raw20842step2Labels := by
      have ha : raw20842step2 = (fun i j => raw20842step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20842step2 raw20842step1; decide +kernel
      have hl : raw20842step2Labels = raw20842step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20842step1 raw20842step1Labels permutation8 permutation4
    mixedMoment B raw20842step2 raw20842step2Labels = mixedMoment B raw20842step3 raw20842step3Labels := by
      have ha : raw20842step3 = -raw20842step2 := by apply Matrix.ext; change ∀ i j, raw20842step3 i j = -(raw20842step2 i j); unfold raw20842step3 raw20842step2; decide +kernel
      have hl : raw20842step3Labels = raw20842step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1630 node1630Labels := by rfl

theorem canonical20843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20843 raw20843Labels = mixedMoment B node1625 node1625Labels := by
  calc
    mixedMoment B raw20843 raw20843Labels = mixedMoment B raw20843step0 raw20843step0Labels := by
      have hz : ∀ j, raw20843 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20843step0 = (fun i j => raw20843 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20843step0 raw20843; decide +kernel
      have hl : raw20843step0Labels = raw20843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20843 raw20843Labels permutation346 hz
    mixedMoment B raw20843step0 raw20843step0Labels = mixedMoment B raw20843step1 raw20843step1Labels := by
      have hz : ∀ j, raw20843step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20843step1 = (fun i j => raw20843step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20843step1 raw20843step0; decide +kernel
      have hl : raw20843step1Labels = raw20843step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20843step0 raw20843step0Labels permutation56 hz
    mixedMoment B raw20843step1 raw20843step1Labels = mixedMoment B raw20843step2 raw20843step2Labels := by
      have ha : raw20843step2 = (fun i j => raw20843step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20843step2 raw20843step1; decide +kernel
      have hl : raw20843step2Labels = raw20843step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20843step1 raw20843step1Labels permutation8 permutation4
    mixedMoment B raw20843step2 raw20843step2Labels = mixedMoment B raw20843step3 raw20843step3Labels := by
      have ha : raw20843step3 = -raw20843step2 := by apply Matrix.ext; change ∀ i j, raw20843step3 i j = -(raw20843step2 i j); unfold raw20843step3 raw20843step2; decide +kernel
      have hl : raw20843step3Labels = raw20843step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1625 node1625Labels := by rfl

theorem canonical20844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20844 raw20844Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw20844 raw20844Labels = mixedMoment B raw20844step0 raw20844step0Labels := by
      have hz : ∀ j, raw20844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20844step0 = (fun i j => raw20844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20844step0 raw20844; decide +kernel
      have hl : raw20844step0Labels = raw20844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20844 raw20844Labels permutation346 hz
    mixedMoment B raw20844step0 raw20844step0Labels = mixedMoment B raw20844step1 raw20844step1Labels := by
      have hz : ∀ j, raw20844step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20844step1 = (fun i j => raw20844step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20844step1 raw20844step0; decide +kernel
      have hl : raw20844step1Labels = raw20844step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20844step0 raw20844step0Labels permutation56 hz
    _ = mixedMoment B node5272 node5272Labels := by rfl

theorem canonical20845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20845 raw20845Labels = mixedMoment B node4157 node4157Labels := by
  calc
    mixedMoment B raw20845 raw20845Labels = mixedMoment B raw20845step0 raw20845step0Labels := by
      have hz : ∀ j, raw20845 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20845step0 = (fun i j => raw20845 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20845step0 raw20845; decide +kernel
      have hl : raw20845step0Labels = raw20845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20845 raw20845Labels permutation346 hz
    mixedMoment B raw20845step0 raw20845step0Labels = mixedMoment B raw20845step1 raw20845step1Labels := by
      have ha : raw20845step1 = (fun i j => raw20845step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20845step1 raw20845step0; decide +kernel
      have hl : raw20845step1Labels = raw20845step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20845step0 raw20845step0Labels permutation38 permutation3
    mixedMoment B raw20845step1 raw20845step1Labels = mixedMoment B raw20845step2 raw20845step2Labels := by
      have ha : raw20845step2 = raw20845step1 := by apply Matrix.ext; unfold raw20845step2 raw20845step1; decide +kernel
      have hl : raw20845step1Labels = labelEmbedding6 ∘ raw20845step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20845step1 raw20845step1Labels raw20845step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4157 node4157Labels := by rfl

theorem canonical20846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20846 raw20846Labels = mixedMoment B node4532 node4532Labels := by
  calc
    mixedMoment B raw20846 raw20846Labels = mixedMoment B raw20846step0 raw20846step0Labels := by
      have ha : raw20846step0 = (fun i j => raw20846 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20846step0 raw20846; decide +kernel
      have hl : raw20846step0Labels = raw20846Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20846 raw20846Labels permutation182 permutation3
    mixedMoment B raw20846step0 raw20846step0Labels = mixedMoment B raw20846step1 raw20846step1Labels := by
      have ha : raw20846step1 = raw20846step0 := by apply Matrix.ext; unfold raw20846step1 raw20846step0; decide +kernel
      have hl : raw20846step0Labels = labelEmbedding6 ∘ raw20846step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20846step0 raw20846step0Labels raw20846step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4532 node4532Labels := by rfl

theorem canonical20847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20847 raw20847Labels = mixedMoment B node4543 node4543Labels := by
  calc
    mixedMoment B raw20847 raw20847Labels = mixedMoment B raw20847step0 raw20847step0Labels := by
      have hz : ∀ j, raw20847 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20847step0 = (fun i j => raw20847 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20847step0 raw20847; decide +kernel
      have hl : raw20847step0Labels = raw20847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20847 raw20847Labels permutation346 hz
    mixedMoment B raw20847step0 raw20847step0Labels = mixedMoment B raw20847step1 raw20847step1Labels := by
      have ha : raw20847step1 = (fun i j => raw20847step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20847step1 raw20847step0; decide +kernel
      have hl : raw20847step1Labels = raw20847step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20847step0 raw20847step0Labels permutation38 permutation2
    _ = mixedMoment B node4543 node4543Labels := by rfl

theorem canonical20848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20848 raw20848Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw20848 raw20848Labels = mixedMoment B raw20848step0 raw20848step0Labels := by
      have hz : ∀ j, raw20848 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20848step0 = (fun i j => raw20848 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20848step0 raw20848; decide +kernel
      have hl : raw20848step0Labels = raw20848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20848 raw20848Labels permutation520 hz
    mixedMoment B raw20848step0 raw20848step0Labels = mixedMoment B raw20848step1 raw20848step1Labels := by
      have hz : ∀ j, raw20848step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20848step1 = (fun i j => raw20848step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20848step1 raw20848step0; decide +kernel
      have hl : raw20848step1Labels = raw20848step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20848step0 raw20848step0Labels permutation80 hz
    mixedMoment B raw20848step1 raw20848step1Labels = mixedMoment B raw20848step2 raw20848step2Labels := by
      have ha : raw20848step2 = (fun i j => raw20848step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20848step2 raw20848step1; decide +kernel
      have hl : raw20848step2Labels = raw20848step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20848step1 raw20848step1Labels permutation10 permutation2
    _ = mixedMoment B node4605 node4605Labels := by rfl

theorem canonical20849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20849 raw20849Labels = mixedMoment B node4157 node4157Labels := by
  calc
    mixedMoment B raw20849 raw20849Labels = mixedMoment B raw20849step0 raw20849step0Labels := by
      have hz : ∀ j, raw20849 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20849step0 = (fun i j => raw20849 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20849step0 raw20849; decide +kernel
      have hl : raw20849step0Labels = raw20849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20849 raw20849Labels permutation265 hz
    mixedMoment B raw20849step0 raw20849step0Labels = mixedMoment B raw20849step1 raw20849step1Labels := by
      have ha : raw20849step1 = (fun i j => raw20849step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20849step1 raw20849step0; decide +kernel
      have hl : raw20849step1Labels = raw20849step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20849step0 raw20849step0Labels permutation38 permutation3
    mixedMoment B raw20849step1 raw20849step1Labels = mixedMoment B raw20849step2 raw20849step2Labels := by
      have ha : raw20849step2 = raw20849step1 := by apply Matrix.ext; unfold raw20849step2 raw20849step1; decide +kernel
      have hl : raw20849step1Labels = labelEmbedding6 ∘ raw20849step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20849step1 raw20849step1Labels raw20849step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4157 node4157Labels := by rfl

theorem canonical20850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20850 raw20850Labels = mixedMoment B node4532 node4532Labels := by
  calc
    mixedMoment B raw20850 raw20850Labels = mixedMoment B raw20850step0 raw20850step0Labels := by
      have ha : raw20850step0 = (fun i j => raw20850 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20850step0 raw20850; decide +kernel
      have hl : raw20850step0Labels = raw20850Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20850 raw20850Labels permutation158 permutation3
    mixedMoment B raw20850step0 raw20850step0Labels = mixedMoment B raw20850step1 raw20850step1Labels := by
      have ha : raw20850step1 = raw20850step0 := by apply Matrix.ext; unfold raw20850step1 raw20850step0; decide +kernel
      have hl : raw20850step0Labels = labelEmbedding6 ∘ raw20850step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20850step0 raw20850step0Labels raw20850step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4532 node4532Labels := by rfl

theorem canonical20851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20851 raw20851Labels = mixedMoment B node4543 node4543Labels := by
  calc
    mixedMoment B raw20851 raw20851Labels = mixedMoment B raw20851step0 raw20851step0Labels := by
      have hz : ∀ j, raw20851 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20851step0 = (fun i j => raw20851 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20851step0 raw20851; decide +kernel
      have hl : raw20851step0Labels = raw20851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20851 raw20851Labels permutation265 hz
    mixedMoment B raw20851step0 raw20851step0Labels = mixedMoment B raw20851step1 raw20851step1Labels := by
      have ha : raw20851step1 = (fun i j => raw20851step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20851step1 raw20851step0; decide +kernel
      have hl : raw20851step1Labels = raw20851step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20851step0 raw20851step0Labels permutation38 permutation2
    _ = mixedMoment B node4543 node4543Labels := by rfl

theorem canonical20852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20852 raw20852Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw20852 raw20852Labels = mixedMoment B raw20852step0 raw20852step0Labels := by
      have hz : ∀ j, raw20852 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20852step0 = (fun i j => raw20852 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20852step0 raw20852; decide +kernel
      have hl : raw20852step0Labels = raw20852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20852 raw20852Labels permutation520 hz
    mixedMoment B raw20852step0 raw20852step0Labels = mixedMoment B raw20852step1 raw20852step1Labels := by
      have hz : ∀ j, raw20852step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20852step1 = (fun i j => raw20852step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20852step1 raw20852step0; decide +kernel
      have hl : raw20852step1Labels = raw20852step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20852step0 raw20852step0Labels permutation56 hz
    mixedMoment B raw20852step1 raw20852step1Labels = mixedMoment B raw20852step2 raw20852step2Labels := by
      have ha : raw20852step2 = (fun i j => raw20852step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20852step2 raw20852step1; decide +kernel
      have hl : raw20852step2Labels = raw20852step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20852step1 raw20852step1Labels permutation10 permutation2
    _ = mixedMoment B node4605 node4605Labels := by rfl

theorem canonical20853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20853 raw20853Labels = mixedMoment B node4184 node4184Labels := by
  calc
    mixedMoment B raw20853 raw20853Labels = mixedMoment B raw20853step0 raw20853step0Labels := by
      have hz : ∀ j, raw20853 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20853step0 = (fun i j => raw20853 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20853step0 raw20853; decide +kernel
      have hl : raw20853step0Labels = raw20853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20853 raw20853Labels permutation346 hz
    mixedMoment B raw20853step0 raw20853step0Labels = mixedMoment B raw20853step1 raw20853step1Labels := by
      have hz : ∀ j, raw20853step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20853step1 = (fun i j => raw20853step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20853step1 raw20853step0; decide +kernel
      have hl : raw20853step1Labels = raw20853step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20853step0 raw20853step0Labels permutation56 hz
    mixedMoment B raw20853step1 raw20853step1Labels = mixedMoment B raw20853step2 raw20853step2Labels := by
      have ha : raw20853step2 = (fun i j => raw20853step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20853step2 raw20853step1; decide +kernel
      have hl : raw20853step2Labels = raw20853step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20853step1 raw20853step1Labels permutation10 permutation3
    mixedMoment B raw20853step2 raw20853step2Labels = mixedMoment B raw20853step3 raw20853step3Labels := by
      have ha : raw20853step3 = raw20853step2 := by apply Matrix.ext; unfold raw20853step3 raw20853step2; decide +kernel
      have hl : raw20853step2Labels = labelEmbedding6 ∘ raw20853step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20853step2 raw20853step2Labels raw20853step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4184 node4184Labels := by rfl

theorem canonical20854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20854 raw20854Labels = mixedMoment B node4552 node4552Labels := by
  calc
    mixedMoment B raw20854 raw20854Labels = mixedMoment B raw20854step0 raw20854step0Labels := by
      have hz : ∀ j, raw20854 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20854step0 = (fun i j => raw20854 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20854step0 raw20854; decide +kernel
      have hl : raw20854step0Labels = raw20854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20854 raw20854Labels permutation346 hz
    mixedMoment B raw20854step0 raw20854step0Labels = mixedMoment B raw20854step1 raw20854step1Labels := by
      have ha : raw20854step1 = (fun i j => raw20854step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20854step1 raw20854step0; decide +kernel
      have hl : raw20854step1Labels = raw20854step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20854step0 raw20854step0Labels permutation34 permutation3
    mixedMoment B raw20854step1 raw20854step1Labels = mixedMoment B raw20854step2 raw20854step2Labels := by
      have ha : raw20854step2 = raw20854step1 := by apply Matrix.ext; unfold raw20854step2 raw20854step1; decide +kernel
      have hl : raw20854step1Labels = labelEmbedding6 ∘ raw20854step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20854step1 raw20854step1Labels raw20854step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4552 node4552Labels := by rfl

theorem canonical20855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20855 raw20855Labels = mixedMoment B node4552 node4552Labels := by
  calc
    mixedMoment B raw20855 raw20855Labels = mixedMoment B raw20855step0 raw20855step0Labels := by
      have hz : ∀ j, raw20855 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20855step0 = (fun i j => raw20855 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20855step0 raw20855; decide +kernel
      have hl : raw20855step0Labels = raw20855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20855 raw20855Labels permutation265 hz
    mixedMoment B raw20855step0 raw20855step0Labels = mixedMoment B raw20855step1 raw20855step1Labels := by
      have ha : raw20855step1 = (fun i j => raw20855step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20855step1 raw20855step0; decide +kernel
      have hl : raw20855step1Labels = raw20855step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20855step0 raw20855step0Labels permutation34 permutation3
    mixedMoment B raw20855step1 raw20855step1Labels = mixedMoment B raw20855step2 raw20855step2Labels := by
      have ha : raw20855step2 = raw20855step1 := by apply Matrix.ext; unfold raw20855step2 raw20855step1; decide +kernel
      have hl : raw20855step1Labels = labelEmbedding6 ∘ raw20855step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20855step1 raw20855step1Labels raw20855step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4552 node4552Labels := by rfl

theorem canonical20856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20856 raw20856Labels = mixedMoment B node4621 node4621Labels := by
  calc
    mixedMoment B raw20856 raw20856Labels = mixedMoment B raw20856step0 raw20856step0Labels := by
      have hz : ∀ j, raw20856 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20856step0 = (fun i j => raw20856 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20856step0 raw20856; decide +kernel
      have hl : raw20856step0Labels = raw20856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20856 raw20856Labels permutation520 hz
    mixedMoment B raw20856step0 raw20856step0Labels = mixedMoment B raw20856step1 raw20856step1Labels := by
      have hz : ∀ j, raw20856step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20856step1 = (fun i j => raw20856step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20856step1 raw20856step0; decide +kernel
      have hl : raw20856step1Labels = raw20856step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20856step0 raw20856step0Labels permutation80 hz
    mixedMoment B raw20856step1 raw20856step1Labels = mixedMoment B raw20856step2 raw20856step2Labels := by
      have hz : ∀ j, raw20856step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20856step2 = (fun i j => raw20856step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20856step2 raw20856step1; decide +kernel
      have hl : raw20856step2Labels = raw20856step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20856step1 raw20856step1Labels permutation14 hz
    _ = mixedMoment B node4621 node4621Labels := by rfl

theorem canonical20857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20857 raw20857Labels = mixedMoment B node4162 node4162Labels := by
  calc
    mixedMoment B raw20857 raw20857Labels = mixedMoment B raw20857step0 raw20857step0Labels := by
      have hz : ∀ j, raw20857 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20857step0 = (fun i j => raw20857 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20857step0 raw20857; decide +kernel
      have hl : raw20857step0Labels = raw20857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20857 raw20857Labels permutation346 hz
    mixedMoment B raw20857step0 raw20857step0Labels = mixedMoment B raw20857step1 raw20857step1Labels := by
      have hz : ∀ j, raw20857step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20857step1 = (fun i j => raw20857step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20857step1 raw20857step0; decide +kernel
      have hl : raw20857step1Labels = raw20857step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20857step0 raw20857step0Labels permutation56 hz
    mixedMoment B raw20857step1 raw20857step1Labels = mixedMoment B raw20857step2 raw20857step2Labels := by
      have ha : raw20857step2 = (fun i j => raw20857step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20857step2 raw20857step1; decide +kernel
      have hl : raw20857step2Labels = raw20857step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20857step1 raw20857step1Labels permutation8 permutation3
    mixedMoment B raw20857step2 raw20857step2Labels = mixedMoment B raw20857step3 raw20857step3Labels := by
      have ha : raw20857step3 = raw20857step2 := by apply Matrix.ext; unfold raw20857step3 raw20857step2; decide +kernel
      have hl : raw20857step2Labels = labelEmbedding6 ∘ raw20857step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20857step2 raw20857step2Labels raw20857step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4162 node4162Labels := by rfl

theorem canonical20858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20858 raw20858Labels = mixedMoment B node4536 node4536Labels := by
  calc
    mixedMoment B raw20858 raw20858Labels = mixedMoment B raw20858step0 raw20858step0Labels := by
      have hz : ∀ j, raw20858 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20858step0 = (fun i j => raw20858 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20858step0 raw20858; decide +kernel
      have hl : raw20858step0Labels = raw20858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20858 raw20858Labels permutation346 hz
    mixedMoment B raw20858step0 raw20858step0Labels = mixedMoment B raw20858step1 raw20858step1Labels := by
      have ha : raw20858step1 = (fun i j => raw20858step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20858step1 raw20858step0; decide +kernel
      have hl : raw20858step1Labels = raw20858step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20858step0 raw20858step0Labels permutation32 permutation3
    mixedMoment B raw20858step1 raw20858step1Labels = mixedMoment B raw20858step2 raw20858step2Labels := by
      have ha : raw20858step2 = raw20858step1 := by apply Matrix.ext; unfold raw20858step2 raw20858step1; decide +kernel
      have hl : raw20858step1Labels = labelEmbedding6 ∘ raw20858step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20858step1 raw20858step1Labels raw20858step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4536 node4536Labels := by rfl

theorem canonical20859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20859 raw20859Labels = mixedMoment B node4536 node4536Labels := by
  calc
    mixedMoment B raw20859 raw20859Labels = mixedMoment B raw20859step0 raw20859step0Labels := by
      have hz : ∀ j, raw20859 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20859step0 = (fun i j => raw20859 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20859step0 raw20859; decide +kernel
      have hl : raw20859step0Labels = raw20859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20859 raw20859Labels permutation265 hz
    mixedMoment B raw20859step0 raw20859step0Labels = mixedMoment B raw20859step1 raw20859step1Labels := by
      have ha : raw20859step1 = (fun i j => raw20859step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20859step1 raw20859step0; decide +kernel
      have hl : raw20859step1Labels = raw20859step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20859step0 raw20859step0Labels permutation32 permutation3
    mixedMoment B raw20859step1 raw20859step1Labels = mixedMoment B raw20859step2 raw20859step2Labels := by
      have ha : raw20859step2 = raw20859step1 := by apply Matrix.ext; unfold raw20859step2 raw20859step1; decide +kernel
      have hl : raw20859step1Labels = labelEmbedding6 ∘ raw20859step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20859step1 raw20859step1Labels raw20859step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4536 node4536Labels := by rfl

theorem canonical20860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20860 raw20860Labels = mixedMoment B node4557 node4557Labels := by
  calc
    mixedMoment B raw20860 raw20860Labels = mixedMoment B raw20860step0 raw20860step0Labels := by
      have hz : ∀ j, raw20860 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20860step0 = (fun i j => raw20860 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20860step0 raw20860; decide +kernel
      have hl : raw20860step0Labels = raw20860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20860 raw20860Labels permutation346 hz
    mixedMoment B raw20860step0 raw20860step0Labels = mixedMoment B raw20860step1 raw20860step1Labels := by
      have hz : ∀ j, raw20860step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20860step1 = (fun i j => raw20860step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20860step1 raw20860step0; decide +kernel
      have hl : raw20860step1Labels = raw20860step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20860step0 raw20860step0Labels permutation56 hz
    _ = mixedMoment B node4557 node4557Labels := by rfl

theorem canonical20861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20861 raw20861Labels = mixedMoment B node4159 node4159Labels := by
  calc
    mixedMoment B raw20861 raw20861Labels = mixedMoment B raw20861step0 raw20861step0Labels := by
      have hz : ∀ j, raw20861 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20861step0 = (fun i j => raw20861 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20861step0 raw20861; decide +kernel
      have hl : raw20861step0Labels = raw20861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20861 raw20861Labels permutation346 hz
    mixedMoment B raw20861step0 raw20861step0Labels = mixedMoment B raw20861step1 raw20861step1Labels := by
      have hz : ∀ j, raw20861step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20861step1 = (fun i j => raw20861step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20861step1 raw20861step0; decide +kernel
      have hl : raw20861step1Labels = raw20861step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20861step0 raw20861step0Labels permutation56 hz
    mixedMoment B raw20861step1 raw20861step1Labels = mixedMoment B raw20861step2 raw20861step2Labels := by
      have ha : raw20861step2 = (fun i j => raw20861step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20861step2 raw20861step1; decide +kernel
      have hl : raw20861step2Labels = raw20861step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20861step1 raw20861step1Labels permutation8 permutation3
    mixedMoment B raw20861step2 raw20861step2Labels = mixedMoment B raw20861step3 raw20861step3Labels := by
      have ha : raw20861step3 = raw20861step2 := by apply Matrix.ext; unfold raw20861step3 raw20861step2; decide +kernel
      have hl : raw20861step2Labels = labelEmbedding6 ∘ raw20861step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20861step2 raw20861step2Labels raw20861step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4159 node4159Labels := by rfl

theorem canonical20862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20862 raw20862Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw20862 raw20862Labels = mixedMoment B raw20862step0 raw20862step0Labels := by
      have hz : ∀ j, raw20862 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20862step0 = (fun i j => raw20862 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20862step0 raw20862; decide +kernel
      have hl : raw20862step0Labels = raw20862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20862 raw20862Labels permutation346 hz
    mixedMoment B raw20862step0 raw20862step0Labels = mixedMoment B raw20862step1 raw20862step1Labels := by
      have ha : raw20862step1 = (fun i j => raw20862step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20862step1 raw20862step0; decide +kernel
      have hl : raw20862step1Labels = raw20862step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20862step0 raw20862step0Labels permutation151 permutation2
    mixedMoment B raw20862step1 raw20862step1Labels = mixedMoment B raw20862step2 raw20862step2Labels := by
      have ha : raw20862step2 = -raw20862step1 := by apply Matrix.ext; change ∀ i j, raw20862step2 i j = -(raw20862step1 i j); unfold raw20862step2 raw20862step1; decide +kernel
      have hl : raw20862step2Labels = raw20862step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4330 node4330Labels := by rfl

theorem canonical20863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20863 raw20863Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw20863 raw20863Labels = mixedMoment B raw20863step0 raw20863step0Labels := by
      have hz : ∀ j, raw20863 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20863step0 = (fun i j => raw20863 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20863step0 raw20863; decide +kernel
      have hl : raw20863step0Labels = raw20863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20863 raw20863Labels permutation265 hz
    mixedMoment B raw20863step0 raw20863step0Labels = mixedMoment B raw20863step1 raw20863step1Labels := by
      have ha : raw20863step1 = (fun i j => raw20863step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20863step1 raw20863step0; decide +kernel
      have hl : raw20863step1Labels = raw20863step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20863step0 raw20863step0Labels permutation151 permutation2
    mixedMoment B raw20863step1 raw20863step1Labels = mixedMoment B raw20863step2 raw20863step2Labels := by
      have ha : raw20863step2 = -raw20863step1 := by apply Matrix.ext; change ∀ i j, raw20863step2 i j = -(raw20863step1 i j); unfold raw20863step2 raw20863step1; decide +kernel
      have hl : raw20863step2Labels = raw20863step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4330 node4330Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical163
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20864 raw20864Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw20864 raw20864Labels = mixedMoment B raw20864step0 raw20864step0Labels := by
      have hz : ∀ j, raw20864 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20864step0 = (fun i j => raw20864 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20864step0 raw20864; decide +kernel
      have hl : raw20864step0Labels = raw20864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20864 raw20864Labels permutation346 hz
    mixedMoment B raw20864step0 raw20864step0Labels = mixedMoment B raw20864step1 raw20864step1Labels := by
      have hz : ∀ j, raw20864step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20864step1 = (fun i j => raw20864step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20864step1 raw20864step0; decide +kernel
      have hl : raw20864step1Labels = raw20864step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20864step0 raw20864step0Labels permutation56 hz
    mixedMoment B raw20864step1 raw20864step1Labels = mixedMoment B raw20864step2 raw20864step2Labels := by
      have ha : raw20864step2 = (fun i j => raw20864step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20864step2 raw20864step1; decide +kernel
      have hl : raw20864step2Labels = raw20864step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20864step1 raw20864step1Labels permutation31 permutation2
    mixedMoment B raw20864step2 raw20864step2Labels = mixedMoment B raw20864step3 raw20864step3Labels := by
      have ha : raw20864step3 = -raw20864step2 := by apply Matrix.ext; change ∀ i j, raw20864step3 i j = -(raw20864step2 i j); unfold raw20864step3 raw20864step2; decide +kernel
      have hl : raw20864step3Labels = raw20864step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4356 node4356Labels := by rfl

theorem canonical20865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20865 raw20865Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw20865 raw20865Labels = mixedMoment B raw20865step0 raw20865step0Labels := by
      have hz : ∀ j, raw20865 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20865step0 = (fun i j => raw20865 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20865step0 raw20865; decide +kernel
      have hl : raw20865step0Labels = raw20865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20865 raw20865Labels permutation520 hz
    mixedMoment B raw20865step0 raw20865step0Labels = mixedMoment B raw20865step1 raw20865step1Labels := by
      have hz : ∀ j, raw20865step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20865step1 = (fun i j => raw20865step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20865step1 raw20865step0; decide +kernel
      have hl : raw20865step1Labels = raw20865step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20865step0 raw20865step0Labels permutation80 hz
    mixedMoment B raw20865step1 raw20865step1Labels = mixedMoment B raw20865step2 raw20865step2Labels := by
      have hz : ∀ j, raw20865step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20865step2 = (fun i j => raw20865step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20865step2 raw20865step1; decide +kernel
      have hl : raw20865step2Labels = raw20865step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20865step1 raw20865step1Labels permutation14 hz
    mixedMoment B raw20865step2 raw20865step2Labels = mixedMoment B raw20865step3 raw20865step3Labels := by
      have ha : raw20865step3 = (fun i j => raw20865step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20865step3 raw20865step2; decide +kernel
      have hl : raw20865step3Labels = raw20865step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20865step2 raw20865step2Labels permutation7 permutation2
    mixedMoment B raw20865step3 raw20865step3Labels = mixedMoment B raw20865step4 raw20865step4Labels := by
      have ha : raw20865step4 = -raw20865step3 := by apply Matrix.ext; change ∀ i j, raw20865step4 i j = -(raw20865step3 i j); unfold raw20865step4 raw20865step3; decide +kernel
      have hl : raw20865step4Labels = raw20865step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical20888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20888 raw20888Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw20888 raw20888Labels = mixedMoment B raw20888step0 raw20888step0Labels := by
      have hz : ∀ j, raw20888 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20888step0 = (fun i j => raw20888 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20888step0 raw20888; decide +kernel
      have hl : raw20888step0Labels = raw20888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20888 raw20888Labels permutation346 hz
    mixedMoment B raw20888step0 raw20888step0Labels = mixedMoment B raw20888step1 raw20888step1Labels := by
      have hz : ∀ j, raw20888step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20888step1 = (fun i j => raw20888step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20888step1 raw20888step0; decide +kernel
      have hl : raw20888step1Labels = raw20888step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20888step0 raw20888step0Labels permutation56 hz
    mixedMoment B raw20888step1 raw20888step1Labels = mixedMoment B raw20888step2 raw20888step2Labels := by
      have ha : raw20888step2 = (fun i j => raw20888step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20888step2 raw20888step1; decide +kernel
      have hl : raw20888step2Labels = raw20888step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20888step1 raw20888step1Labels permutation31 permutation7
    mixedMoment B raw20888step2 raw20888step2Labels = mixedMoment B raw20888step3 raw20888step3Labels := by
      have ha : raw20888step3 = raw20888step2 := by apply Matrix.ext; unfold raw20888step3 raw20888step2; decide +kernel
      have hl : raw20888step2Labels = labelEmbedding1 ∘ raw20888step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20888step2 raw20888step2Labels raw20888step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical20889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20889 raw20889Labels = mixedMoment B node1528 node1528Labels := by
  calc
    mixedMoment B raw20889 raw20889Labels = mixedMoment B raw20889step0 raw20889step0Labels := by
      have hz : ∀ j, raw20889 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20889step0 = (fun i j => raw20889 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20889step0 raw20889; decide +kernel
      have hl : raw20889step0Labels = raw20889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20889 raw20889Labels permutation346 hz
    mixedMoment B raw20889step0 raw20889step0Labels = mixedMoment B raw20889step1 raw20889step1Labels := by
      have ha : raw20889step1 = (fun i j => raw20889step0 (permutation52 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20889step1 raw20889step0; decide +kernel
      have hl : raw20889step1Labels = raw20889step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20889step0 raw20889step0Labels permutation52 permutation5
    mixedMoment B raw20889step1 raw20889step1Labels = mixedMoment B raw20889step2 raw20889step2Labels := by
      have ha : raw20889step2 = -raw20889step1 := by apply Matrix.ext; change ∀ i j, raw20889step2 i j = -(raw20889step1 i j); unfold raw20889step2 raw20889step1; decide +kernel
      have hl : raw20889step2Labels = raw20889step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20889step2 raw20889step2Labels = mixedMoment B raw20889step3 raw20889step3Labels := by
      have ha : raw20889step3 = raw20889step2 := by apply Matrix.ext; unfold raw20889step3 raw20889step2; decide +kernel
      have hl : raw20889step2Labels = labelEmbedding1 ∘ raw20889step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20889step2 raw20889step2Labels raw20889step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1528 node1528Labels := by rfl

theorem canonical20890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20890 raw20890Labels = mixedMoment B node2172 node2172Labels := by
  calc
    mixedMoment B raw20890 raw20890Labels = mixedMoment B raw20890step0 raw20890step0Labels := by
      have ha : raw20890step0 = (fun i j => raw20890 (permutation620 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20890step0 raw20890; decide +kernel
      have hl : raw20890step0Labels = raw20890Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20890 raw20890Labels permutation620 permutation7
    mixedMoment B raw20890step0 raw20890step0Labels = mixedMoment B raw20890step1 raw20890step1Labels := by
      have ha : raw20890step1 = raw20890step0 := by apply Matrix.ext; unfold raw20890step1 raw20890step0; decide +kernel
      have hl : raw20890step0Labels = labelEmbedding1 ∘ raw20890step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20890step0 raw20890step0Labels raw20890step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2172 node2172Labels := by rfl

theorem canonical20891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20891 raw20891Labels = mixedMoment B node2184 node2184Labels := by
  calc
    mixedMoment B raw20891 raw20891Labels = mixedMoment B raw20891step0 raw20891step0Labels := by
      have hz : ∀ j, raw20891 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20891step0 = (fun i j => raw20891 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20891step0 raw20891; decide +kernel
      have hl : raw20891step0Labels = raw20891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20891 raw20891Labels permutation346 hz
    mixedMoment B raw20891step0 raw20891step0Labels = mixedMoment B raw20891step1 raw20891step1Labels := by
      have ha : raw20891step1 = (fun i j => raw20891step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20891step1 raw20891step0; decide +kernel
      have hl : raw20891step1Labels = raw20891step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20891step0 raw20891step0Labels permutation139 permutation7
    mixedMoment B raw20891step1 raw20891step1Labels = mixedMoment B raw20891step2 raw20891step2Labels := by
      have ha : raw20891step2 = raw20891step1 := by apply Matrix.ext; unfold raw20891step2 raw20891step1; decide +kernel
      have hl : raw20891step1Labels = labelEmbedding1 ∘ raw20891step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20891step1 raw20891step1Labels raw20891step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2184 node2184Labels := by rfl

theorem canonical20892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20892 raw20892Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw20892 raw20892Labels = mixedMoment B raw20892step0 raw20892step0Labels := by
      have hz : ∀ j, raw20892 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20892step0 = (fun i j => raw20892 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20892step0 raw20892; decide +kernel
      have hl : raw20892step0Labels = raw20892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20892 raw20892Labels permutation520 hz
    mixedMoment B raw20892step0 raw20892step0Labels = mixedMoment B raw20892step1 raw20892step1Labels := by
      have hz : ∀ j, raw20892step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20892step1 = (fun i j => raw20892step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20892step1 raw20892step0; decide +kernel
      have hl : raw20892step1Labels = raw20892step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20892step0 raw20892step0Labels permutation80 hz
    mixedMoment B raw20892step1 raw20892step1Labels = mixedMoment B raw20892step2 raw20892step2Labels := by
      have ha : raw20892step2 = (fun i j => raw20892step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20892step2 raw20892step1; decide +kernel
      have hl : raw20892step2Labels = raw20892step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20892step1 raw20892step1Labels permutation29 permutation7
    mixedMoment B raw20892step2 raw20892step2Labels = mixedMoment B raw20892step3 raw20892step3Labels := by
      have ha : raw20892step3 = raw20892step2 := by apply Matrix.ext; unfold raw20892step3 raw20892step2; decide +kernel
      have hl : raw20892step2Labels = labelEmbedding1 ∘ raw20892step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20892step2 raw20892step2Labels raw20892step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical20893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20893 raw20893Labels = mixedMoment B node1528 node1528Labels := by
  calc
    mixedMoment B raw20893 raw20893Labels = mixedMoment B raw20893step0 raw20893step0Labels := by
      have hz : ∀ j, raw20893 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20893step0 = (fun i j => raw20893 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20893step0 raw20893; decide +kernel
      have hl : raw20893step0Labels = raw20893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20893 raw20893Labels permutation265 hz
    mixedMoment B raw20893step0 raw20893step0Labels = mixedMoment B raw20893step1 raw20893step1Labels := by
      have ha : raw20893step1 = (fun i j => raw20893step0 (permutation52 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20893step1 raw20893step0; decide +kernel
      have hl : raw20893step1Labels = raw20893step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20893step0 raw20893step0Labels permutation52 permutation5
    mixedMoment B raw20893step1 raw20893step1Labels = mixedMoment B raw20893step2 raw20893step2Labels := by
      have ha : raw20893step2 = -raw20893step1 := by apply Matrix.ext; change ∀ i j, raw20893step2 i j = -(raw20893step1 i j); unfold raw20893step2 raw20893step1; decide +kernel
      have hl : raw20893step2Labels = raw20893step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20893step2 raw20893step2Labels = mixedMoment B raw20893step3 raw20893step3Labels := by
      have ha : raw20893step3 = raw20893step2 := by apply Matrix.ext; unfold raw20893step3 raw20893step2; decide +kernel
      have hl : raw20893step2Labels = labelEmbedding1 ∘ raw20893step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20893step2 raw20893step2Labels raw20893step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1528 node1528Labels := by rfl

theorem canonical20894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20894 raw20894Labels = mixedMoment B node2172 node2172Labels := by
  calc
    mixedMoment B raw20894 raw20894Labels = mixedMoment B raw20894step0 raw20894step0Labels := by
      have ha : raw20894step0 = (fun i j => raw20894 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20894step0 raw20894; decide +kernel
      have hl : raw20894step0Labels = raw20894Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20894 raw20894Labels permutation644 permutation7
    mixedMoment B raw20894step0 raw20894step0Labels = mixedMoment B raw20894step1 raw20894step1Labels := by
      have ha : raw20894step1 = raw20894step0 := by apply Matrix.ext; unfold raw20894step1 raw20894step0; decide +kernel
      have hl : raw20894step0Labels = labelEmbedding1 ∘ raw20894step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20894step0 raw20894step0Labels raw20894step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2172 node2172Labels := by rfl

theorem canonical20895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20895 raw20895Labels = mixedMoment B node2184 node2184Labels := by
  calc
    mixedMoment B raw20895 raw20895Labels = mixedMoment B raw20895step0 raw20895step0Labels := by
      have hz : ∀ j, raw20895 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20895step0 = (fun i j => raw20895 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20895step0 raw20895; decide +kernel
      have hl : raw20895step0Labels = raw20895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20895 raw20895Labels permutation265 hz
    mixedMoment B raw20895step0 raw20895step0Labels = mixedMoment B raw20895step1 raw20895step1Labels := by
      have ha : raw20895step1 = (fun i j => raw20895step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20895step1 raw20895step0; decide +kernel
      have hl : raw20895step1Labels = raw20895step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20895step0 raw20895step0Labels permutation139 permutation7
    mixedMoment B raw20895step1 raw20895step1Labels = mixedMoment B raw20895step2 raw20895step2Labels := by
      have ha : raw20895step2 = raw20895step1 := by apply Matrix.ext; unfold raw20895step2 raw20895step1; decide +kernel
      have hl : raw20895step1Labels = labelEmbedding1 ∘ raw20895step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20895step1 raw20895step1Labels raw20895step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2184 node2184Labels := by rfl

theorem canonical20896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20896 raw20896Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw20896 raw20896Labels = mixedMoment B raw20896step0 raw20896step0Labels := by
      have hz : ∀ j, raw20896 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20896step0 = (fun i j => raw20896 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20896step0 raw20896; decide +kernel
      have hl : raw20896step0Labels = raw20896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20896 raw20896Labels permutation520 hz
    mixedMoment B raw20896step0 raw20896step0Labels = mixedMoment B raw20896step1 raw20896step1Labels := by
      have hz : ∀ j, raw20896step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20896step1 = (fun i j => raw20896step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20896step1 raw20896step0; decide +kernel
      have hl : raw20896step1Labels = raw20896step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20896step0 raw20896step0Labels permutation56 hz
    mixedMoment B raw20896step1 raw20896step1Labels = mixedMoment B raw20896step2 raw20896step2Labels := by
      have ha : raw20896step2 = (fun i j => raw20896step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20896step2 raw20896step1; decide +kernel
      have hl : raw20896step2Labels = raw20896step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20896step1 raw20896step1Labels permutation29 permutation7
    mixedMoment B raw20896step2 raw20896step2Labels = mixedMoment B raw20896step3 raw20896step3Labels := by
      have ha : raw20896step3 = raw20896step2 := by apply Matrix.ext; unfold raw20896step3 raw20896step2; decide +kernel
      have hl : raw20896step2Labels = labelEmbedding1 ∘ raw20896step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20896step2 raw20896step2Labels raw20896step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical20897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20897 raw20897Labels = mixedMoment B node1530 node1530Labels := by
  calc
    mixedMoment B raw20897 raw20897Labels = mixedMoment B raw20897step0 raw20897step0Labels := by
      have hz : ∀ j, raw20897 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20897step0 = (fun i j => raw20897 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20897step0 raw20897; decide +kernel
      have hl : raw20897step0Labels = raw20897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20897 raw20897Labels permutation346 hz
    mixedMoment B raw20897step0 raw20897step0Labels = mixedMoment B raw20897step1 raw20897step1Labels := by
      have hz : ∀ j, raw20897step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20897step1 = (fun i j => raw20897step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20897step1 raw20897step0; decide +kernel
      have hl : raw20897step1Labels = raw20897step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20897step0 raw20897step0Labels permutation56 hz
    mixedMoment B raw20897step1 raw20897step1Labels = mixedMoment B raw20897step2 raw20897step2Labels := by
      have ha : raw20897step2 = (fun i j => raw20897step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20897step2 raw20897step1; decide +kernel
      have hl : raw20897step2Labels = raw20897step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20897step1 raw20897step1Labels permutation13 permutation5
    mixedMoment B raw20897step2 raw20897step2Labels = mixedMoment B raw20897step3 raw20897step3Labels := by
      have ha : raw20897step3 = -raw20897step2 := by apply Matrix.ext; change ∀ i j, raw20897step3 i j = -(raw20897step2 i j); unfold raw20897step3 raw20897step2; decide +kernel
      have hl : raw20897step3Labels = raw20897step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20897step3 raw20897step3Labels = mixedMoment B raw20897step4 raw20897step4Labels := by
      have ha : raw20897step4 = raw20897step3 := by apply Matrix.ext; unfold raw20897step4 raw20897step3; decide +kernel
      have hl : raw20897step3Labels = labelEmbedding1 ∘ raw20897step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20897step3 raw20897step3Labels raw20897step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1530 node1530Labels := by rfl

theorem canonical20898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20898 raw20898Labels = mixedMoment B node2200 node2200Labels := by
  calc
    mixedMoment B raw20898 raw20898Labels = mixedMoment B raw20898step0 raw20898step0Labels := by
      have hz : ∀ j, raw20898 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20898step0 = (fun i j => raw20898 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20898step0 raw20898; decide +kernel
      have hl : raw20898step0Labels = raw20898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20898 raw20898Labels permutation346 hz
    mixedMoment B raw20898step0 raw20898step0Labels = mixedMoment B raw20898step1 raw20898step1Labels := by
      have ha : raw20898step1 = (fun i j => raw20898step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20898step1 raw20898step0; decide +kernel
      have hl : raw20898step1Labels = raw20898step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20898step0 raw20898step0Labels permutation149 permutation7
    mixedMoment B raw20898step1 raw20898step1Labels = mixedMoment B raw20898step2 raw20898step2Labels := by
      have ha : raw20898step2 = raw20898step1 := by apply Matrix.ext; unfold raw20898step2 raw20898step1; decide +kernel
      have hl : raw20898step1Labels = labelEmbedding1 ∘ raw20898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20898step1 raw20898step1Labels raw20898step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2200 node2200Labels := by rfl

theorem canonical20899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20899 raw20899Labels = mixedMoment B node2200 node2200Labels := by
  calc
    mixedMoment B raw20899 raw20899Labels = mixedMoment B raw20899step0 raw20899step0Labels := by
      have hz : ∀ j, raw20899 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20899step0 = (fun i j => raw20899 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20899step0 raw20899; decide +kernel
      have hl : raw20899step0Labels = raw20899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20899 raw20899Labels permutation265 hz
    mixedMoment B raw20899step0 raw20899step0Labels = mixedMoment B raw20899step1 raw20899step1Labels := by
      have ha : raw20899step1 = (fun i j => raw20899step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20899step1 raw20899step0; decide +kernel
      have hl : raw20899step1Labels = raw20899step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20899step0 raw20899step0Labels permutation149 permutation7
    mixedMoment B raw20899step1 raw20899step1Labels = mixedMoment B raw20899step2 raw20899step2Labels := by
      have ha : raw20899step2 = raw20899step1 := by apply Matrix.ext; unfold raw20899step2 raw20899step1; decide +kernel
      have hl : raw20899step1Labels = labelEmbedding1 ∘ raw20899step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20899step1 raw20899step1Labels raw20899step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2200 node2200Labels := by rfl

theorem canonical20900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20900 raw20900Labels = mixedMoment B node2289 node2289Labels := by
  calc
    mixedMoment B raw20900 raw20900Labels = mixedMoment B raw20900step0 raw20900step0Labels := by
      have hz : ∀ j, raw20900 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20900step0 = (fun i j => raw20900 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20900step0 raw20900; decide +kernel
      have hl : raw20900step0Labels = raw20900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20900 raw20900Labels permutation520 hz
    mixedMoment B raw20900step0 raw20900step0Labels = mixedMoment B raw20900step1 raw20900step1Labels := by
      have hz : ∀ j, raw20900step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20900step1 = (fun i j => raw20900step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20900step1 raw20900step0; decide +kernel
      have hl : raw20900step1Labels = raw20900step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20900step0 raw20900step0Labels permutation80 hz
    mixedMoment B raw20900step1 raw20900step1Labels = mixedMoment B raw20900step2 raw20900step2Labels := by
      have hz : ∀ j, raw20900step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20900step2 = (fun i j => raw20900step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20900step2 raw20900step1; decide +kernel
      have hl : raw20900step2Labels = raw20900step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20900step1 raw20900step1Labels permutation14 hz
    mixedMoment B raw20900step2 raw20900step2Labels = mixedMoment B raw20900step3 raw20900step3Labels := by
      have ha : raw20900step3 = (fun i j => raw20900step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20900step3 raw20900step2; decide +kernel
      have hl : raw20900step3Labels = raw20900step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20900step2 raw20900step2Labels permutation7 permutation7
    mixedMoment B raw20900step3 raw20900step3Labels = mixedMoment B raw20900step4 raw20900step4Labels := by
      have ha : raw20900step4 = raw20900step3 := by apply Matrix.ext; unfold raw20900step4 raw20900step3; decide +kernel
      have hl : raw20900step3Labels = labelEmbedding1 ∘ raw20900step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20900step3 raw20900step3Labels raw20900step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2289 node2289Labels := by rfl

theorem canonical20901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20901 raw20901Labels = mixedMoment B node1529 node1529Labels := by
  calc
    mixedMoment B raw20901 raw20901Labels = mixedMoment B raw20901step0 raw20901step0Labels := by
      have hz : ∀ j, raw20901 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20901step0 = (fun i j => raw20901 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20901step0 raw20901; decide +kernel
      have hl : raw20901step0Labels = raw20901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20901 raw20901Labels permutation346 hz
    mixedMoment B raw20901step0 raw20901step0Labels = mixedMoment B raw20901step1 raw20901step1Labels := by
      have hz : ∀ j, raw20901step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20901step1 = (fun i j => raw20901step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20901step1 raw20901step0; decide +kernel
      have hl : raw20901step1Labels = raw20901step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20901step0 raw20901step0Labels permutation56 hz
    mixedMoment B raw20901step1 raw20901step1Labels = mixedMoment B raw20901step2 raw20901step2Labels := by
      have ha : raw20901step2 = (fun i j => raw20901step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20901step2 raw20901step1; decide +kernel
      have hl : raw20901step2Labels = raw20901step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20901step1 raw20901step1Labels permutation12 permutation5
    mixedMoment B raw20901step2 raw20901step2Labels = mixedMoment B raw20901step3 raw20901step3Labels := by
      have ha : raw20901step3 = -raw20901step2 := by apply Matrix.ext; change ∀ i j, raw20901step3 i j = -(raw20901step2 i j); unfold raw20901step3 raw20901step2; decide +kernel
      have hl : raw20901step3Labels = raw20901step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20901step3 raw20901step3Labels = mixedMoment B raw20901step4 raw20901step4Labels := by
      have ha : raw20901step4 = raw20901step3 := by apply Matrix.ext; unfold raw20901step4 raw20901step3; decide +kernel
      have hl : raw20901step3Labels = labelEmbedding1 ∘ raw20901step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20901step3 raw20901step3Labels raw20901step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1529 node1529Labels := by rfl

theorem canonical20902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20902 raw20902Labels = mixedMoment B node2149 node2149Labels := by
  calc
    mixedMoment B raw20902 raw20902Labels = mixedMoment B raw20902step0 raw20902step0Labels := by
      have hz : ∀ j, raw20902 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20902step0 = (fun i j => raw20902 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20902step0 raw20902; decide +kernel
      have hl : raw20902step0Labels = raw20902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20902 raw20902Labels permutation346 hz
    mixedMoment B raw20902step0 raw20902step0Labels = mixedMoment B raw20902step1 raw20902step1Labels := by
      have ha : raw20902step1 = (fun i j => raw20902step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20902step1 raw20902step0; decide +kernel
      have hl : raw20902step1Labels = raw20902step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20902step0 raw20902step0Labels permutation149 permutation7
    mixedMoment B raw20902step1 raw20902step1Labels = mixedMoment B raw20902step2 raw20902step2Labels := by
      have ha : raw20902step2 = raw20902step1 := by apply Matrix.ext; unfold raw20902step2 raw20902step1; decide +kernel
      have hl : raw20902step1Labels = labelEmbedding1 ∘ raw20902step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20902step1 raw20902step1Labels raw20902step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2149 node2149Labels := by rfl

theorem canonical20903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20903 raw20903Labels = mixedMoment B node2149 node2149Labels := by
  calc
    mixedMoment B raw20903 raw20903Labels = mixedMoment B raw20903step0 raw20903step0Labels := by
      have hz : ∀ j, raw20903 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20903step0 = (fun i j => raw20903 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20903step0 raw20903; decide +kernel
      have hl : raw20903step0Labels = raw20903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20903 raw20903Labels permutation265 hz
    mixedMoment B raw20903step0 raw20903step0Labels = mixedMoment B raw20903step1 raw20903step1Labels := by
      have ha : raw20903step1 = (fun i j => raw20903step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20903step1 raw20903step0; decide +kernel
      have hl : raw20903step1Labels = raw20903step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20903step0 raw20903step0Labels permutation149 permutation7
    mixedMoment B raw20903step1 raw20903step1Labels = mixedMoment B raw20903step2 raw20903step2Labels := by
      have ha : raw20903step2 = raw20903step1 := by apply Matrix.ext; unfold raw20903step2 raw20903step1; decide +kernel
      have hl : raw20903step1Labels = labelEmbedding1 ∘ raw20903step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20903step1 raw20903step1Labels raw20903step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2149 node2149Labels := by rfl

theorem canonical20904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20904 raw20904Labels = mixedMoment B node2167 node2167Labels := by
  calc
    mixedMoment B raw20904 raw20904Labels = mixedMoment B raw20904step0 raw20904step0Labels := by
      have hz : ∀ j, raw20904 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20904step0 = (fun i j => raw20904 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20904step0 raw20904; decide +kernel
      have hl : raw20904step0Labels = raw20904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20904 raw20904Labels permutation346 hz
    mixedMoment B raw20904step0 raw20904step0Labels = mixedMoment B raw20904step1 raw20904step1Labels := by
      have hz : ∀ j, raw20904step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20904step1 = (fun i j => raw20904step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20904step1 raw20904step0; decide +kernel
      have hl : raw20904step1Labels = raw20904step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20904step0 raw20904step0Labels permutation56 hz
    mixedMoment B raw20904step1 raw20904step1Labels = mixedMoment B raw20904step2 raw20904step2Labels := by
      have ha : raw20904step2 = (fun i j => raw20904step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20904step2 raw20904step1; decide +kernel
      have hl : raw20904step2Labels = raw20904step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20904step1 raw20904step1Labels permutation31 permutation7
    mixedMoment B raw20904step2 raw20904step2Labels = mixedMoment B raw20904step3 raw20904step3Labels := by
      have ha : raw20904step3 = raw20904step2 := by apply Matrix.ext; unfold raw20904step3 raw20904step2; decide +kernel
      have hl : raw20904step2Labels = labelEmbedding1 ∘ raw20904step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20904step2 raw20904step2Labels raw20904step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2167 node2167Labels := by rfl

theorem canonical20905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20905 raw20905Labels = mixedMoment B node1532 node1532Labels := by
  calc
    mixedMoment B raw20905 raw20905Labels = mixedMoment B raw20905step0 raw20905step0Labels := by
      have hz : ∀ j, raw20905 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20905step0 = (fun i j => raw20905 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20905step0 raw20905; decide +kernel
      have hl : raw20905step0Labels = raw20905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20905 raw20905Labels permutation346 hz
    mixedMoment B raw20905step0 raw20905step0Labels = mixedMoment B raw20905step1 raw20905step1Labels := by
      have hz : ∀ j, raw20905step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20905step1 = (fun i j => raw20905step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20905step1 raw20905step0; decide +kernel
      have hl : raw20905step1Labels = raw20905step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20905step0 raw20905step0Labels permutation56 hz
    mixedMoment B raw20905step1 raw20905step1Labels = mixedMoment B raw20905step2 raw20905step2Labels := by
      have ha : raw20905step2 = (fun i j => raw20905step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20905step2 raw20905step1; decide +kernel
      have hl : raw20905step2Labels = raw20905step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20905step1 raw20905step1Labels permutation8 permutation5
    mixedMoment B raw20905step2 raw20905step2Labels = mixedMoment B raw20905step3 raw20905step3Labels := by
      have ha : raw20905step3 = -raw20905step2 := by apply Matrix.ext; change ∀ i j, raw20905step3 i j = -(raw20905step2 i j); unfold raw20905step3 raw20905step2; decide +kernel
      have hl : raw20905step3Labels = raw20905step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20905step3 raw20905step3Labels = mixedMoment B raw20905step4 raw20905step4Labels := by
      have ha : raw20905step4 = raw20905step3 := by apply Matrix.ext; unfold raw20905step4 raw20905step3; decide +kernel
      have hl : raw20905step3Labels = labelEmbedding1 ∘ raw20905step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20905step3 raw20905step3Labels raw20905step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1532 node1532Labels := by rfl

theorem canonical20906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20906 raw20906Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw20906 raw20906Labels = mixedMoment B raw20906step0 raw20906step0Labels := by
      have hz : ∀ j, raw20906 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20906step0 = (fun i j => raw20906 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20906step0 raw20906; decide +kernel
      have hl : raw20906step0Labels = raw20906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20906 raw20906Labels permutation346 hz
    mixedMoment B raw20906step0 raw20906step0Labels = mixedMoment B raw20906step1 raw20906step1Labels := by
      have ha : raw20906step1 = (fun i j => raw20906step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20906step1 raw20906step0; decide +kernel
      have hl : raw20906step1Labels = raw20906step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20906step0 raw20906step0Labels permutation149 permutation7
    mixedMoment B raw20906step1 raw20906step1Labels = mixedMoment B raw20906step2 raw20906step2Labels := by
      have ha : raw20906step2 = raw20906step1 := by apply Matrix.ext; unfold raw20906step2 raw20906step1; decide +kernel
      have hl : raw20906step1Labels = labelEmbedding1 ∘ raw20906step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20906step1 raw20906step1Labels raw20906step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

theorem canonical20907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20907 raw20907Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw20907 raw20907Labels = mixedMoment B raw20907step0 raw20907step0Labels := by
      have hz : ∀ j, raw20907 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20907step0 = (fun i j => raw20907 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20907step0 raw20907; decide +kernel
      have hl : raw20907step0Labels = raw20907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20907 raw20907Labels permutation265 hz
    mixedMoment B raw20907step0 raw20907step0Labels = mixedMoment B raw20907step1 raw20907step1Labels := by
      have ha : raw20907step1 = (fun i j => raw20907step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20907step1 raw20907step0; decide +kernel
      have hl : raw20907step1Labels = raw20907step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20907step0 raw20907step0Labels permutation149 permutation7
    mixedMoment B raw20907step1 raw20907step1Labels = mixedMoment B raw20907step2 raw20907step2Labels := by
      have ha : raw20907step2 = raw20907step1 := by apply Matrix.ext; unfold raw20907step2 raw20907step1; decide +kernel
      have hl : raw20907step1Labels = labelEmbedding1 ∘ raw20907step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20907step1 raw20907step1Labels raw20907step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

theorem canonical20908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20908 raw20908Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw20908 raw20908Labels = mixedMoment B raw20908step0 raw20908step0Labels := by
      have hz : ∀ j, raw20908 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20908step0 = (fun i j => raw20908 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20908step0 raw20908; decide +kernel
      have hl : raw20908step0Labels = raw20908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20908 raw20908Labels permutation346 hz
    mixedMoment B raw20908step0 raw20908step0Labels = mixedMoment B raw20908step1 raw20908step1Labels := by
      have hz : ∀ j, raw20908step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20908step1 = (fun i j => raw20908step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20908step1 raw20908step0; decide +kernel
      have hl : raw20908step1Labels = raw20908step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20908step0 raw20908step0Labels permutation56 hz
    mixedMoment B raw20908step1 raw20908step1Labels = mixedMoment B raw20908step2 raw20908step2Labels := by
      have ha : raw20908step2 = (fun i j => raw20908step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20908step2 raw20908step1; decide +kernel
      have hl : raw20908step2Labels = raw20908step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20908step1 raw20908step1Labels permutation31 permutation7
    mixedMoment B raw20908step2 raw20908step2Labels = mixedMoment B raw20908step3 raw20908step3Labels := by
      have ha : raw20908step3 = raw20908step2 := by apply Matrix.ext; unfold raw20908step3 raw20908step2; decide +kernel
      have hl : raw20908step2Labels = labelEmbedding1 ∘ raw20908step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20908step2 raw20908step2Labels raw20908step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

theorem canonical20909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20909 raw20909Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw20909 raw20909Labels = mixedMoment B raw20909step0 raw20909step0Labels := by
      have hz : ∀ j, raw20909 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20909step0 = (fun i j => raw20909 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20909step0 raw20909; decide +kernel
      have hl : raw20909step0Labels = raw20909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20909 raw20909Labels permutation520 hz
    mixedMoment B raw20909step0 raw20909step0Labels = mixedMoment B raw20909step1 raw20909step1Labels := by
      have hz : ∀ j, raw20909step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20909step1 = (fun i j => raw20909step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20909step1 raw20909step0; decide +kernel
      have hl : raw20909step1Labels = raw20909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20909step0 raw20909step0Labels permutation80 hz
    mixedMoment B raw20909step1 raw20909step1Labels = mixedMoment B raw20909step2 raw20909step2Labels := by
      have hz : ∀ j, raw20909step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20909step2 = (fun i j => raw20909step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20909step2 raw20909step1; decide +kernel
      have hl : raw20909step2Labels = raw20909step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20909step1 raw20909step1Labels permutation14 hz
    mixedMoment B raw20909step2 raw20909step2Labels = mixedMoment B raw20909step3 raw20909step3Labels := by
      have ha : raw20909step3 = (fun i j => raw20909step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20909step3 raw20909step2; decide +kernel
      have hl : raw20909step3Labels = raw20909step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20909step2 raw20909step2Labels permutation7 permutation7
    mixedMoment B raw20909step3 raw20909step3Labels = mixedMoment B raw20909step4 raw20909step4Labels := by
      have ha : raw20909step4 = raw20909step3 := by apply Matrix.ext; unfold raw20909step4 raw20909step3; decide +kernel
      have hl : raw20909step3Labels = labelEmbedding1 ∘ raw20909step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20909step3 raw20909step3Labels raw20909step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1752 node1752Labels := by rfl

theorem canonical20910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20910 raw20910Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw20910 raw20910Labels = mixedMoment B raw20910step0 raw20910step0Labels := by
      have hz : ∀ j, raw20910 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20910step0 = (fun i j => raw20910 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20910step0 raw20910; decide +kernel
      have hl : raw20910step0Labels = raw20910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20910 raw20910Labels permutation346 hz
    mixedMoment B raw20910step0 raw20910step0Labels = mixedMoment B raw20910step1 raw20910step1Labels := by
      have hz : ∀ j, raw20910step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20910step1 = (fun i j => raw20910step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20910step1 raw20910step0; decide +kernel
      have hl : raw20910step1Labels = raw20910step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20910step0 raw20910step0Labels permutation56 hz
    _ = mixedMoment B node1239 node1239Labels := by rfl

theorem canonical20911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20911 raw20911Labels = mixedMoment B node624 node624Labels := by
  calc
    mixedMoment B raw20911 raw20911Labels = mixedMoment B raw20911step0 raw20911step0Labels := by
      have hz : ∀ j, raw20911 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20911step0 = (fun i j => raw20911 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20911step0 raw20911; decide +kernel
      have hl : raw20911step0Labels = raw20911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20911 raw20911Labels permutation346 hz
    mixedMoment B raw20911step0 raw20911step0Labels = mixedMoment B raw20911step1 raw20911step1Labels := by
      have ha : raw20911step1 = (fun i j => raw20911step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20911step1 raw20911step0; decide +kernel
      have hl : raw20911step1Labels = raw20911step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20911step0 raw20911step0Labels permutation38 permutation2
    _ = mixedMoment B node624 node624Labels := by rfl

theorem canonical20912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20912 raw20912Labels = mixedMoment B node624 node624Labels := by
  calc
    mixedMoment B raw20912 raw20912Labels = mixedMoment B raw20912step0 raw20912step0Labels := by
      have hz : ∀ j, raw20912 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20912step0 = (fun i j => raw20912 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20912step0 raw20912; decide +kernel
      have hl : raw20912step0Labels = raw20912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20912 raw20912Labels permutation265 hz
    mixedMoment B raw20912step0 raw20912step0Labels = mixedMoment B raw20912step1 raw20912step1Labels := by
      have ha : raw20912step1 = (fun i j => raw20912step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20912step1 raw20912step0; decide +kernel
      have hl : raw20912step1Labels = raw20912step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20912step0 raw20912step0Labels permutation38 permutation2
    _ = mixedMoment B node624 node624Labels := by rfl

theorem canonical20913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20913 raw20913Labels = mixedMoment B node639 node639Labels := by
  calc
    mixedMoment B raw20913 raw20913Labels = mixedMoment B raw20913step0 raw20913step0Labels := by
      have hz : ∀ j, raw20913 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20913step0 = (fun i j => raw20913 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20913step0 raw20913; decide +kernel
      have hl : raw20913step0Labels = raw20913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20913 raw20913Labels permutation346 hz
    mixedMoment B raw20913step0 raw20913step0Labels = mixedMoment B raw20913step1 raw20913step1Labels := by
      have hz : ∀ j, raw20913step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20913step1 = (fun i j => raw20913step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20913step1 raw20913step0; decide +kernel
      have hl : raw20913step1Labels = raw20913step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20913step0 raw20913step0Labels permutation56 hz
    _ = mixedMoment B node639 node639Labels := by rfl

theorem canonical20914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20914 raw20914Labels = mixedMoment B node634 node634Labels := by
  calc
    mixedMoment B raw20914 raw20914Labels = mixedMoment B raw20914step0 raw20914step0Labels := by
      have hz : ∀ j, raw20914 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20914step0 = (fun i j => raw20914 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20914step0 raw20914; decide +kernel
      have hl : raw20914step0Labels = raw20914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20914 raw20914Labels permutation346 hz
    mixedMoment B raw20914step0 raw20914step0Labels = mixedMoment B raw20914step1 raw20914step1Labels := by
      have hz : ∀ j, raw20914step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20914step1 = (fun i j => raw20914step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20914step1 raw20914step0; decide +kernel
      have hl : raw20914step1Labels = raw20914step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20914step0 raw20914step0Labels permutation56 hz
    _ = mixedMoment B node634 node634Labels := by rfl

theorem canonical20915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20915 raw20915Labels = mixedMoment B node628 node628Labels := by
  calc
    mixedMoment B raw20915 raw20915Labels = mixedMoment B raw20915step0 raw20915step0Labels := by
      have hz : ∀ j, raw20915 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20915step0 = (fun i j => raw20915 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20915step0 raw20915; decide +kernel
      have hl : raw20915step0Labels = raw20915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20915 raw20915Labels permutation346 hz
    mixedMoment B raw20915step0 raw20915step0Labels = mixedMoment B raw20915step1 raw20915step1Labels := by
      have hz : ∀ j, raw20915step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20915step1 = (fun i j => raw20915step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20915step1 raw20915step0; decide +kernel
      have hl : raw20915step1Labels = raw20915step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20915step0 raw20915step0Labels permutation56 hz
    _ = mixedMoment B node628 node628Labels := by rfl

theorem canonical20916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20916 raw20916Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw20916 raw20916Labels = mixedMoment B raw20916step0 raw20916step0Labels := by
      have hz : ∀ j, raw20916 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20916step0 = (fun i j => raw20916 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20916step0 raw20916; decide +kernel
      have hl : raw20916step0Labels = raw20916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20916 raw20916Labels permutation520 hz
    mixedMoment B raw20916step0 raw20916step0Labels = mixedMoment B raw20916step1 raw20916step1Labels := by
      have hz : ∀ j, raw20916step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20916step1 = (fun i j => raw20916step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20916step1 raw20916step0; decide +kernel
      have hl : raw20916step1Labels = raw20916step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20916step0 raw20916step0Labels permutation80 hz
    mixedMoment B raw20916step1 raw20916step1Labels = mixedMoment B raw20916step2 raw20916step2Labels := by
      have hz : ∀ j, raw20916step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20916step2 = (fun i j => raw20916step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20916step2 raw20916step1; decide +kernel
      have hl : raw20916step2Labels = raw20916step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20916step1 raw20916step1Labels permutation14 hz
    mixedMoment B raw20916step2 raw20916step2Labels = mixedMoment B raw20916step3 raw20916step3Labels := by
      have ha : raw20916step3 = (fun i j => raw20916step2 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20916step3 raw20916step2; decide +kernel
      have hl : raw20916step3Labels = raw20916step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20916step2 raw20916step2Labels permutation7 permutation0
    mixedMoment B raw20916step3 raw20916step3Labels = mixedMoment B raw20916step4 raw20916step4Labels := by
      have ha : raw20916step4 = -raw20916step3 := by apply Matrix.ext; change ∀ i j, raw20916step4 i j = -(raw20916step3 i j); unfold raw20916step4 raw20916step3; decide +kernel
      have hl : raw20916step4Labels = raw20916step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical20917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20917 raw20917Labels = mixedMoment B node1147 node1147Labels := by
  calc
    mixedMoment B raw20917 raw20917Labels = mixedMoment B raw20917step0 raw20917step0Labels := by
      have ha : raw20917step0 = (fun i j => raw20917 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20917step0 raw20917; decide +kernel
      have hl : raw20917step0Labels = raw20917Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20917 raw20917Labels permutation182 permutation2
    _ = mixedMoment B node1147 node1147Labels := by rfl

theorem canonical20918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20918 raw20918Labels = mixedMoment B node1128 node1128Labels := by
  calc
    mixedMoment B raw20918 raw20918Labels = mixedMoment B raw20918step0 raw20918step0Labels := by
      have hz : ∀ j, raw20918 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20918step0 = (fun i j => raw20918 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20918step0 raw20918; decide +kernel
      have hl : raw20918step0Labels = raw20918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20918 raw20918Labels permutation346 hz
    mixedMoment B raw20918step0 raw20918step0Labels = mixedMoment B raw20918step1 raw20918step1Labels := by
      have ha : raw20918step1 = (fun i j => raw20918step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20918step1 raw20918step0; decide +kernel
      have hl : raw20918step1Labels = raw20918step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20918step0 raw20918step0Labels permutation38 permutation2
    _ = mixedMoment B node1128 node1128Labels := by rfl

theorem canonical20919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20919 raw20919Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw20919 raw20919Labels = mixedMoment B raw20919step0 raw20919step0Labels := by
      have hz : ∀ j, raw20919 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20919step0 = (fun i j => raw20919 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20919step0 raw20919; decide +kernel
      have hl : raw20919step0Labels = raw20919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20919 raw20919Labels permutation520 hz
    mixedMoment B raw20919step0 raw20919step0Labels = mixedMoment B raw20919step1 raw20919step1Labels := by
      have hz : ∀ j, raw20919step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20919step1 = (fun i j => raw20919step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20919step1 raw20919step0; decide +kernel
      have hl : raw20919step1Labels = raw20919step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20919step0 raw20919step0Labels permutation80 hz
    mixedMoment B raw20919step1 raw20919step1Labels = mixedMoment B raw20919step2 raw20919step2Labels := by
      have ha : raw20919step2 = (fun i j => raw20919step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20919step2 raw20919step1; decide +kernel
      have hl : raw20919step2Labels = raw20919step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20919step1 raw20919step1Labels permutation10 permutation2
    _ = mixedMoment B node1239 node1239Labels := by rfl

theorem canonical20920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20920 raw20920Labels = mixedMoment B node1234 node1234Labels := by
  calc
    mixedMoment B raw20920 raw20920Labels = mixedMoment B raw20920step0 raw20920step0Labels := by
      have hz : ∀ j, raw20920 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20920step0 = (fun i j => raw20920 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20920step0 raw20920; decide +kernel
      have hl : raw20920step0Labels = raw20920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20920 raw20920Labels permutation346 hz
    mixedMoment B raw20920step0 raw20920step0Labels = mixedMoment B raw20920step1 raw20920step1Labels := by
      have ha : raw20920step1 = (fun i j => raw20920step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20920step1 raw20920step0; decide +kernel
      have hl : raw20920step1Labels = raw20920step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20920step0 raw20920step0Labels permutation38 permutation2
    _ = mixedMoment B node1234 node1234Labels := by rfl

theorem canonical20921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20921 raw20921Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw20921 raw20921Labels = mixedMoment B raw20921step0 raw20921step0Labels := by
      have hz : ∀ j, raw20921 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20921step0 = (fun i j => raw20921 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20921step0 raw20921; decide +kernel
      have hl : raw20921step0Labels = raw20921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20921 raw20921Labels permutation346 hz
    mixedMoment B raw20921step0 raw20921step0Labels = mixedMoment B raw20921step1 raw20921step1Labels := by
      have ha : raw20921step1 = (fun i j => raw20921step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20921step1 raw20921step0; decide +kernel
      have hl : raw20921step1Labels = raw20921step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20921step0 raw20921step0Labels permutation151 permutation2
    mixedMoment B raw20921step1 raw20921step1Labels = mixedMoment B raw20921step2 raw20921step2Labels := by
      have ha : raw20921step2 = -raw20921step1 := by apply Matrix.ext; change ∀ i j, raw20921step2 i j = -(raw20921step1 i j); unfold raw20921step2 raw20921step1; decide +kernel
      have hl : raw20921step2Labels = raw20921step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2022 node2022Labels := by rfl

theorem canonical20922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20922 raw20922Labels = mixedMoment B node1147 node1147Labels := by
  calc
    mixedMoment B raw20922 raw20922Labels = mixedMoment B raw20922step0 raw20922step0Labels := by
      have ha : raw20922step0 = (fun i j => raw20922 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20922step0 raw20922; decide +kernel
      have hl : raw20922step0Labels = raw20922Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20922 raw20922Labels permutation158 permutation2
    _ = mixedMoment B node1147 node1147Labels := by rfl

theorem canonical20923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20923 raw20923Labels = mixedMoment B node1157 node1157Labels := by
  calc
    mixedMoment B raw20923 raw20923Labels = mixedMoment B raw20923step0 raw20923step0Labels := by
      have hz : ∀ j, raw20923 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20923step0 = (fun i j => raw20923 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20923step0 raw20923; decide +kernel
      have hl : raw20923step0Labels = raw20923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20923 raw20923Labels permutation346 hz
    _ = mixedMoment B node1157 node1157Labels := by rfl

theorem canonical20924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20924 raw20924Labels = mixedMoment B node1153 node1153Labels := by
  calc
    mixedMoment B raw20924 raw20924Labels = mixedMoment B raw20924step0 raw20924step0Labels := by
      have hz : ∀ j, raw20924 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20924step0 = (fun i j => raw20924 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20924step0 raw20924; decide +kernel
      have hl : raw20924step0Labels = raw20924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20924 raw20924Labels permutation346 hz
    _ = mixedMoment B node1153 node1153Labels := by rfl

theorem canonical20925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20925 raw20925Labels = mixedMoment B node908 node908Labels := by
  calc
    mixedMoment B raw20925 raw20925Labels = mixedMoment B raw20925step0 raw20925step0Labels := by
      have hz : ∀ j, raw20925 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20925step0 = (fun i j => raw20925 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20925step0 raw20925; decide +kernel
      have hl : raw20925step0Labels = raw20925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20925 raw20925Labels permutation346 hz
    mixedMoment B raw20925step0 raw20925step0Labels = mixedMoment B raw20925step1 raw20925step1Labels := by
      have ha : raw20925step1 = (fun i j => raw20925step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20925step1 raw20925step0; decide +kernel
      have hl : raw20925step1Labels = raw20925step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20925step0 raw20925step0Labels permutation151 permutation2
    mixedMoment B raw20925step1 raw20925step1Labels = mixedMoment B raw20925step2 raw20925step2Labels := by
      have ha : raw20925step2 = -raw20925step1 := by apply Matrix.ext; change ∀ i j, raw20925step2 i j = -(raw20925step1 i j); unfold raw20925step2 raw20925step1; decide +kernel
      have hl : raw20925step2Labels = raw20925step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node908 node908Labels := by rfl

theorem canonical20926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20926 raw20926Labels = mixedMoment B node2060 node2060Labels := by
  calc
    mixedMoment B raw20926 raw20926Labels = mixedMoment B raw20926step0 raw20926step0Labels := by
      have hz : ∀ j, raw20926 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20926step0 = (fun i j => raw20926 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20926step0 raw20926; decide +kernel
      have hl : raw20926step0Labels = raw20926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20926 raw20926Labels permutation346 hz
    mixedMoment B raw20926step0 raw20926step0Labels = mixedMoment B raw20926step1 raw20926step1Labels := by
      have hz : ∀ j, raw20926step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20926step1 = (fun i j => raw20926step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20926step1 raw20926step0; decide +kernel
      have hl : raw20926step1Labels = raw20926step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20926step0 raw20926step0Labels permutation56 hz
    mixedMoment B raw20926step1 raw20926step1Labels = mixedMoment B raw20926step2 raw20926step2Labels := by
      have ha : raw20926step2 = (fun i j => raw20926step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20926step2 raw20926step1; decide +kernel
      have hl : raw20926step2Labels = raw20926step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20926step1 raw20926step1Labels permutation31 permutation2
    mixedMoment B raw20926step2 raw20926step2Labels = mixedMoment B raw20926step3 raw20926step3Labels := by
      have ha : raw20926step3 = -raw20926step2 := by apply Matrix.ext; change ∀ i j, raw20926step3 i j = -(raw20926step2 i j); unfold raw20926step3 raw20926step2; decide +kernel
      have hl : raw20926step3Labels = raw20926step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2060 node2060Labels := by rfl

theorem canonical20927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20927 raw20927Labels = mixedMoment B node1128 node1128Labels := by
  calc
    mixedMoment B raw20927 raw20927Labels = mixedMoment B raw20927step0 raw20927step0Labels := by
      have hz : ∀ j, raw20927 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20927step0 = (fun i j => raw20927 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20927step0 raw20927; decide +kernel
      have hl : raw20927step0Labels = raw20927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20927 raw20927Labels permutation265 hz
    mixedMoment B raw20927step0 raw20927step0Labels = mixedMoment B raw20927step1 raw20927step1Labels := by
      have ha : raw20927step1 = (fun i j => raw20927step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20927step1 raw20927step0; decide +kernel
      have hl : raw20927step1Labels = raw20927step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20927step0 raw20927step0Labels permutation38 permutation2
    _ = mixedMoment B node1128 node1128Labels := by rfl

theorem canonical20928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20928 raw20928Labels = mixedMoment B node1143 node1143Labels := by
  calc
    mixedMoment B raw20928 raw20928Labels = mixedMoment B raw20928step0 raw20928step0Labels := by
      have hz : ∀ j, raw20928 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20928step0 = (fun i j => raw20928 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20928step0 raw20928; decide +kernel
      have hl : raw20928step0Labels = raw20928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20928 raw20928Labels permutation346 hz
    mixedMoment B raw20928step0 raw20928step0Labels = mixedMoment B raw20928step1 raw20928step1Labels := by
      have hz : ∀ j, raw20928step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20928step1 = (fun i j => raw20928step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20928step1 raw20928step0; decide +kernel
      have hl : raw20928step1Labels = raw20928step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20928step0 raw20928step0Labels permutation56 hz
    _ = mixedMoment B node1143 node1143Labels := by rfl

theorem canonical20929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20929 raw20929Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw20929 raw20929Labels = mixedMoment B raw20929step0 raw20929step0Labels := by
      have hz : ∀ j, raw20929 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20929step0 = (fun i j => raw20929 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20929step0 raw20929; decide +kernel
      have hl : raw20929step0Labels = raw20929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20929 raw20929Labels permutation346 hz
    mixedMoment B raw20929step0 raw20929step0Labels = mixedMoment B raw20929step1 raw20929step1Labels := by
      have hz : ∀ j, raw20929step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20929step1 = (fun i j => raw20929step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20929step1 raw20929step0; decide +kernel
      have hl : raw20929step1Labels = raw20929step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20929step0 raw20929step0Labels permutation56 hz
    mixedMoment B raw20929step1 raw20929step1Labels = mixedMoment B raw20929step2 raw20929step2Labels := by
      have ha : raw20929step2 = (fun i j => raw20929step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20929step2 raw20929step1; decide +kernel
      have hl : raw20929step2Labels = raw20929step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20929step1 raw20929step1Labels permutation31 permutation2
    mixedMoment B raw20929step2 raw20929step2Labels = mixedMoment B raw20929step3 raw20929step3Labels := by
      have ha : raw20929step3 = -raw20929step2 := by apply Matrix.ext; change ∀ i j, raw20929step3 i j = -(raw20929step2 i j); unfold raw20929step3 raw20929step2; decide +kernel
      have hl : raw20929step3Labels = raw20929step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node934 node934Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical164
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20994 raw20994Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw20994 raw20994Labels = mixedMoment B raw20994step0 raw20994step0Labels := by
      have hz : ∀ j, raw20994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20994step0 = (fun i j => raw20994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20994step0 raw20994; decide +kernel
      have hl : raw20994step0Labels = raw20994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20994 raw20994Labels permutation346 hz
    mixedMoment B raw20994step0 raw20994step0Labels = mixedMoment B raw20994step1 raw20994step1Labels := by
      have hz : ∀ j, raw20994step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20994step1 = (fun i j => raw20994step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20994step1 raw20994step0; decide +kernel
      have hl : raw20994step1Labels = raw20994step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20994step0 raw20994step0Labels permutation56 hz
    mixedMoment B raw20994step1 raw20994step1Labels = mixedMoment B raw20994step2 raw20994step2Labels := by
      have ha : raw20994step2 = (fun i j => raw20994step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20994step2 raw20994step1; decide +kernel
      have hl : raw20994step2Labels = raw20994step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20994step1 raw20994step1Labels permutation31 permutation4
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical20995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20995 raw20995Labels = mixedMoment B node1599 node1599Labels := by
  calc
    mixedMoment B raw20995 raw20995Labels = mixedMoment B raw20995step0 raw20995step0Labels := by
      have hz : ∀ j, raw20995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20995step0 = (fun i j => raw20995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20995step0 raw20995; decide +kernel
      have hl : raw20995step0Labels = raw20995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20995 raw20995Labels permutation346 hz
    mixedMoment B raw20995step0 raw20995step0Labels = mixedMoment B raw20995step1 raw20995step1Labels := by
      have ha : raw20995step1 = (fun i j => raw20995step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20995step1 raw20995step0; decide +kernel
      have hl : raw20995step1Labels = raw20995step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20995step0 raw20995step0Labels permutation40 permutation4
    mixedMoment B raw20995step1 raw20995step1Labels = mixedMoment B raw20995step2 raw20995step2Labels := by
      have ha : raw20995step2 = -raw20995step1 := by apply Matrix.ext; change ∀ i j, raw20995step2 i j = -(raw20995step1 i j); unfold raw20995step2 raw20995step1; decide +kernel
      have hl : raw20995step2Labels = raw20995step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1599 node1599Labels := by rfl

theorem canonical20996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20996 raw20996Labels = mixedMoment B node1599 node1599Labels := by
  calc
    mixedMoment B raw20996 raw20996Labels = mixedMoment B raw20996step0 raw20996step0Labels := by
      have hz : ∀ j, raw20996 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20996step0 = (fun i j => raw20996 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20996step0 raw20996; decide +kernel
      have hl : raw20996step0Labels = raw20996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20996 raw20996Labels permutation265 hz
    mixedMoment B raw20996step0 raw20996step0Labels = mixedMoment B raw20996step1 raw20996step1Labels := by
      have ha : raw20996step1 = (fun i j => raw20996step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20996step1 raw20996step0; decide +kernel
      have hl : raw20996step1Labels = raw20996step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20996step0 raw20996step0Labels permutation40 permutation4
    mixedMoment B raw20996step1 raw20996step1Labels = mixedMoment B raw20996step2 raw20996step2Labels := by
      have ha : raw20996step2 = -raw20996step1 := by apply Matrix.ext; change ∀ i j, raw20996step2 i j = -(raw20996step1 i j); unfold raw20996step2 raw20996step1; decide +kernel
      have hl : raw20996step2Labels = raw20996step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1599 node1599Labels := by rfl

theorem canonical20997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20997 raw20997Labels = mixedMoment B node1002 node1002Labels := by
  calc
    mixedMoment B raw20997 raw20997Labels = mixedMoment B raw20997step0 raw20997step0Labels := by
      have hz : ∀ j, raw20997 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20997step0 = (fun i j => raw20997 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20997step0 raw20997; decide +kernel
      have hl : raw20997step0Labels = raw20997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20997 raw20997Labels permutation346 hz
    mixedMoment B raw20997step0 raw20997step0Labels = mixedMoment B raw20997step1 raw20997step1Labels := by
      have hz : ∀ j, raw20997step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20997step1 = (fun i j => raw20997step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20997step1 raw20997step0; decide +kernel
      have hl : raw20997step1Labels = raw20997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20997step0 raw20997step0Labels permutation56 hz
    mixedMoment B raw20997step1 raw20997step1Labels = mixedMoment B raw20997step2 raw20997step2Labels := by
      have ha : raw20997step2 = (fun i j => raw20997step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20997step2 raw20997step1; decide +kernel
      have hl : raw20997step2Labels = raw20997step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20997step1 raw20997step1Labels permutation31 permutation4
    _ = mixedMoment B node1002 node1002Labels := by rfl

theorem canonical20998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20998 raw20998Labels = mixedMoment B node1637 node1637Labels := by
  calc
    mixedMoment B raw20998 raw20998Labels = mixedMoment B raw20998step0 raw20998step0Labels := by
      have hz : ∀ j, raw20998 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20998step0 = (fun i j => raw20998 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20998step0 raw20998; decide +kernel
      have hl : raw20998step0Labels = raw20998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20998 raw20998Labels permutation346 hz
    mixedMoment B raw20998step0 raw20998step0Labels = mixedMoment B raw20998step1 raw20998step1Labels := by
      have ha : raw20998step1 = (fun i j => raw20998step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20998step1 raw20998step0; decide +kernel
      have hl : raw20998step1Labels = raw20998step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20998step0 raw20998step0Labels permutation151 permutation2
    mixedMoment B raw20998step1 raw20998step1Labels = mixedMoment B raw20998step2 raw20998step2Labels := by
      have ha : raw20998step2 = -raw20998step1 := by apply Matrix.ext; change ∀ i j, raw20998step2 i j = -(raw20998step1 i j); unfold raw20998step2 raw20998step1; decide +kernel
      have hl : raw20998step2Labels = raw20998step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1637 node1637Labels := by rfl

theorem canonical20999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20999 raw20999Labels = mixedMoment B node1637 node1637Labels := by
  calc
    mixedMoment B raw20999 raw20999Labels = mixedMoment B raw20999step0 raw20999step0Labels := by
      have hz : ∀ j, raw20999 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20999step0 = (fun i j => raw20999 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20999step0 raw20999; decide +kernel
      have hl : raw20999step0Labels = raw20999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20999 raw20999Labels permutation265 hz
    mixedMoment B raw20999step0 raw20999step0Labels = mixedMoment B raw20999step1 raw20999step1Labels := by
      have ha : raw20999step1 = (fun i j => raw20999step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20999step1 raw20999step0; decide +kernel
      have hl : raw20999step1Labels = raw20999step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20999step0 raw20999step0Labels permutation151 permutation2
    mixedMoment B raw20999step1 raw20999step1Labels = mixedMoment B raw20999step2 raw20999step2Labels := by
      have ha : raw20999step2 = -raw20999step1 := by apply Matrix.ext; change ∀ i j, raw20999step2 i j = -(raw20999step1 i j); unfold raw20999step2 raw20999step1; decide +kernel
      have hl : raw20999step2Labels = raw20999step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1637 node1637Labels := by rfl

theorem canonical21000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21000 raw21000Labels = mixedMoment B node1650 node1650Labels := by
  calc
    mixedMoment B raw21000 raw21000Labels = mixedMoment B raw21000step0 raw21000step0Labels := by
      have hz : ∀ j, raw21000 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21000step0 = (fun i j => raw21000 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21000step0 raw21000; decide +kernel
      have hl : raw21000step0Labels = raw21000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21000 raw21000Labels permutation346 hz
    mixedMoment B raw21000step0 raw21000step0Labels = mixedMoment B raw21000step1 raw21000step1Labels := by
      have hz : ∀ j, raw21000step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21000step1 = (fun i j => raw21000step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21000step1 raw21000step0; decide +kernel
      have hl : raw21000step1Labels = raw21000step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21000step0 raw21000step0Labels permutation56 hz
    mixedMoment B raw21000step1 raw21000step1Labels = mixedMoment B raw21000step2 raw21000step2Labels := by
      have ha : raw21000step2 = (fun i j => raw21000step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21000step2 raw21000step1; decide +kernel
      have hl : raw21000step2Labels = raw21000step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21000step1 raw21000step1Labels permutation31 permutation2
    mixedMoment B raw21000step2 raw21000step2Labels = mixedMoment B raw21000step3 raw21000step3Labels := by
      have ha : raw21000step3 = -raw21000step2 := by apply Matrix.ext; change ∀ i j, raw21000step3 i j = -(raw21000step2 i j); unfold raw21000step3 raw21000step2; decide +kernel
      have hl : raw21000step3Labels = raw21000step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1650 node1650Labels := by rfl

theorem canonical21001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21001 raw21001Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw21001 raw21001Labels = mixedMoment B raw21001step0 raw21001step0Labels := by
      have hz : ∀ j, raw21001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21001step0 = (fun i j => raw21001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21001step0 raw21001; decide +kernel
      have hl : raw21001step0Labels = raw21001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21001 raw21001Labels permutation346 hz
    mixedMoment B raw21001step0 raw21001step0Labels = mixedMoment B raw21001step1 raw21001step1Labels := by
      have hz : ∀ j, raw21001step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21001step1 = (fun i j => raw21001step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21001step1 raw21001step0; decide +kernel
      have hl : raw21001step1Labels = raw21001step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21001step0 raw21001step0Labels permutation56 hz
    _ = mixedMoment B node2737 node2737Labels := by rfl

theorem canonical21002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21002 raw21002Labels = mixedMoment B node1191 node1191Labels := by
  calc
    mixedMoment B raw21002 raw21002Labels = mixedMoment B raw21002step0 raw21002step0Labels := by
      have hz : ∀ j, raw21002 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21002step0 = (fun i j => raw21002 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21002step0 raw21002; decide +kernel
      have hl : raw21002step0Labels = raw21002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21002 raw21002Labels permutation346 hz
    mixedMoment B raw21002step0 raw21002step0Labels = mixedMoment B raw21002step1 raw21002step1Labels := by
      have hz : ∀ j, raw21002step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21002step1 = (fun i j => raw21002step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21002step1 raw21002step0; decide +kernel
      have hl : raw21002step1Labels = raw21002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21002step0 raw21002step0Labels permutation56 hz
    _ = mixedMoment B node1191 node1191Labels := by rfl

theorem canonical21003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21003 raw21003Labels = mixedMoment B node2391 node2391Labels := by
  calc
    mixedMoment B raw21003 raw21003Labels = mixedMoment B raw21003step0 raw21003step0Labels := by
      have hz : ∀ j, raw21003 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21003step0 = (fun i j => raw21003 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21003step0 raw21003; decide +kernel
      have hl : raw21003step0Labels = raw21003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21003 raw21003Labels permutation346 hz
    mixedMoment B raw21003step0 raw21003step0Labels = mixedMoment B raw21003step1 raw21003step1Labels := by
      have ha : raw21003step1 = (fun i j => raw21003step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21003step1 raw21003step0; decide +kernel
      have hl : raw21003step1Labels = raw21003step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21003step0 raw21003step0Labels permutation151 permutation2
    mixedMoment B raw21003step1 raw21003step1Labels = mixedMoment B raw21003step2 raw21003step2Labels := by
      have ha : raw21003step2 = -raw21003step1 := by apply Matrix.ext; change ∀ i j, raw21003step2 i j = -(raw21003step1 i j); unfold raw21003step2 raw21003step1; decide +kernel
      have hl : raw21003step2Labels = raw21003step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2391 node2391Labels := by rfl

theorem canonical21004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21004 raw21004Labels = mixedMoment B node2391 node2391Labels := by
  calc
    mixedMoment B raw21004 raw21004Labels = mixedMoment B raw21004step0 raw21004step0Labels := by
      have hz : ∀ j, raw21004 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21004step0 = (fun i j => raw21004 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21004step0 raw21004; decide +kernel
      have hl : raw21004step0Labels = raw21004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21004 raw21004Labels permutation265 hz
    mixedMoment B raw21004step0 raw21004step0Labels = mixedMoment B raw21004step1 raw21004step1Labels := by
      have ha : raw21004step1 = (fun i j => raw21004step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21004step1 raw21004step0; decide +kernel
      have hl : raw21004step1Labels = raw21004step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21004step0 raw21004step0Labels permutation151 permutation2
    mixedMoment B raw21004step1 raw21004step1Labels = mixedMoment B raw21004step2 raw21004step2Labels := by
      have ha : raw21004step2 = -raw21004step1 := by apply Matrix.ext; change ∀ i j, raw21004step2 i j = -(raw21004step1 i j); unfold raw21004step2 raw21004step1; decide +kernel
      have hl : raw21004step2Labels = raw21004step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2391 node2391Labels := by rfl

theorem canonical21005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21005 raw21005Labels = mixedMoment B node2407 node2407Labels := by
  calc
    mixedMoment B raw21005 raw21005Labels = mixedMoment B raw21005step0 raw21005step0Labels := by
      have hz : ∀ j, raw21005 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21005step0 = (fun i j => raw21005 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21005step0 raw21005; decide +kernel
      have hl : raw21005step0Labels = raw21005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21005 raw21005Labels permutation346 hz
    mixedMoment B raw21005step0 raw21005step0Labels = mixedMoment B raw21005step1 raw21005step1Labels := by
      have hz : ∀ j, raw21005step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21005step1 = (fun i j => raw21005step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21005step1 raw21005step0; decide +kernel
      have hl : raw21005step1Labels = raw21005step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21005step0 raw21005step0Labels permutation56 hz
    _ = mixedMoment B node2407 node2407Labels := by rfl

theorem canonical21006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21006 raw21006Labels = mixedMoment B node2680 node2680Labels := by
  calc
    mixedMoment B raw21006 raw21006Labels = mixedMoment B raw21006step0 raw21006step0Labels := by
      have hz : ∀ j, raw21006 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21006step0 = (fun i j => raw21006 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21006step0 raw21006; decide +kernel
      have hl : raw21006step0Labels = raw21006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21006 raw21006Labels permutation346 hz
    mixedMoment B raw21006step0 raw21006step0Labels = mixedMoment B raw21006step1 raw21006step1Labels := by
      have hz : ∀ j, raw21006step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21006step1 = (fun i j => raw21006step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21006step1 raw21006step0; decide +kernel
      have hl : raw21006step1Labels = raw21006step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21006step0 raw21006step0Labels permutation56 hz
    _ = mixedMoment B node2680 node2680Labels := by rfl

theorem canonical21007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21007 raw21007Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw21007 raw21007Labels = mixedMoment B raw21007step0 raw21007step0Labels := by
      have hz : ∀ j, raw21007 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21007step0 = (fun i j => raw21007 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21007step0 raw21007; decide +kernel
      have hl : raw21007step0Labels = raw21007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21007 raw21007Labels permutation346 hz
    mixedMoment B raw21007step0 raw21007step0Labels = mixedMoment B raw21007step1 raw21007step1Labels := by
      have hz : ∀ j, raw21007step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21007step1 = (fun i j => raw21007step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21007step1 raw21007step0; decide +kernel
      have hl : raw21007step1Labels = raw21007step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21007step0 raw21007step0Labels permutation56 hz
    _ = mixedMoment B node2686 node2686Labels := by rfl

theorem canonical21008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21008 raw21008Labels = mixedMoment B node4089 node4089Labels := by
  calc
    mixedMoment B raw21008 raw21008Labels = mixedMoment B raw21008step0 raw21008step0Labels := by
      have hz : ∀ j, raw21008 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21008step0 = (fun i j => raw21008 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21008step0 raw21008; decide +kernel
      have hl : raw21008step0Labels = raw21008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21008 raw21008Labels permutation346 hz
    mixedMoment B raw21008step0 raw21008step0Labels = mixedMoment B raw21008step1 raw21008step1Labels := by
      have hz : ∀ j, raw21008step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21008step1 = (fun i j => raw21008step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21008step1 raw21008step0; decide +kernel
      have hl : raw21008step1Labels = raw21008step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21008step0 raw21008step0Labels permutation56 hz
    _ = mixedMoment B node4089 node4089Labels := by rfl

theorem canonical21009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21009 raw21009Labels = mixedMoment B node1185 node1185Labels := by
  calc
    mixedMoment B raw21009 raw21009Labels = mixedMoment B raw21009step0 raw21009step0Labels := by
      have hz : ∀ j, raw21009 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21009step0 = (fun i j => raw21009 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21009step0 raw21009; decide +kernel
      have hl : raw21009step0Labels = raw21009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21009 raw21009Labels permutation346 hz
    mixedMoment B raw21009step0 raw21009step0Labels = mixedMoment B raw21009step1 raw21009step1Labels := by
      have ha : raw21009step1 = (fun i j => raw21009step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21009step1 raw21009step0; decide +kernel
      have hl : raw21009step1Labels = raw21009step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21009step0 raw21009step0Labels permutation38 permutation2
    _ = mixedMoment B node1185 node1185Labels := by rfl

theorem canonical21010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21010 raw21010Labels = mixedMoment B node1185 node1185Labels := by
  calc
    mixedMoment B raw21010 raw21010Labels = mixedMoment B raw21010step0 raw21010step0Labels := by
      have hz : ∀ j, raw21010 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21010step0 = (fun i j => raw21010 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21010step0 raw21010; decide +kernel
      have hl : raw21010step0Labels = raw21010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21010 raw21010Labels permutation265 hz
    mixedMoment B raw21010step0 raw21010step0Labels = mixedMoment B raw21010step1 raw21010step1Labels := by
      have ha : raw21010step1 = (fun i j => raw21010step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21010step1 raw21010step0; decide +kernel
      have hl : raw21010step1Labels = raw21010step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21010step0 raw21010step0Labels permutation38 permutation2
    _ = mixedMoment B node1185 node1185Labels := by rfl

theorem canonical21011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21011 raw21011Labels = mixedMoment B node1288 node1288Labels := by
  calc
    mixedMoment B raw21011 raw21011Labels = mixedMoment B raw21011step0 raw21011step0Labels := by
      have hz : ∀ j, raw21011 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21011step0 = (fun i j => raw21011 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21011step0 raw21011; decide +kernel
      have hl : raw21011step0Labels = raw21011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21011 raw21011Labels permutation346 hz
    mixedMoment B raw21011step0 raw21011step0Labels = mixedMoment B raw21011step1 raw21011step1Labels := by
      have hz : ∀ j, raw21011step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21011step1 = (fun i j => raw21011step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21011step1 raw21011step0; decide +kernel
      have hl : raw21011step1Labels = raw21011step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21011step0 raw21011step0Labels permutation56 hz
    _ = mixedMoment B node1288 node1288Labels := by rfl

theorem canonical21012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21012 raw21012Labels = mixedMoment B node1193 node1193Labels := by
  calc
    mixedMoment B raw21012 raw21012Labels = mixedMoment B raw21012step0 raw21012step0Labels := by
      have hz : ∀ j, raw21012 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21012step0 = (fun i j => raw21012 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21012step0 raw21012; decide +kernel
      have hl : raw21012step0Labels = raw21012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21012 raw21012Labels permutation346 hz
    mixedMoment B raw21012step0 raw21012step0Labels = mixedMoment B raw21012step1 raw21012step1Labels := by
      have hz : ∀ j, raw21012step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21012step1 = (fun i j => raw21012step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21012step1 raw21012step0; decide +kernel
      have hl : raw21012step1Labels = raw21012step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21012step0 raw21012step0Labels permutation56 hz
    _ = mixedMoment B node1193 node1193Labels := by rfl

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

theorem canonical2283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2283 raw2283Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw2283 raw2283Labels = mixedMoment B raw2283step0 raw2283step0Labels := by
      have ha : raw2283step0 = (fun i j => raw2283 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2283step0 raw2283; decide +kernel
      have hl : raw2283step0Labels = raw2283Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2283 raw2283Labels permutation8 permutation4
    mixedMoment B raw2283step0 raw2283step0Labels = mixedMoment B raw2283step1 raw2283step1Labels := by
      have ha : raw2283step1 = raw2283step0 := by apply Matrix.ext; unfold raw2283step1 raw2283step0; decide +kernel
      have hl : raw2283step0Labels = labelEmbedding7 ∘ raw2283step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2283step0 raw2283step0Labels raw2283step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5272 node5272Labels := by rfl

theorem canonical2284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2284 raw2284Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw2284 raw2284Labels = mixedMoment B raw2284step0 raw2284step0Labels := by
      have ha : raw2284step0 = (fun i j => raw2284 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2284step0 raw2284; decide +kernel
      have hl : raw2284step0Labels = raw2284Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2284 raw2284Labels permutation8 permutation4
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical2285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2285 raw2285Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw2285 raw2285Labels = mixedMoment B raw2285step0 raw2285step0Labels := by
      have ha : raw2285step0 = (fun i j => raw2285 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2285step0 raw2285; decide +kernel
      have hl : raw2285step0Labels = raw2285Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2285 raw2285Labels permutation31 permutation6
    mixedMoment B raw2285step0 raw2285step0Labels = mixedMoment B raw2285step1 raw2285step1Labels := by
      have ha : raw2285step1 = raw2285step0 := by apply Matrix.ext; unfold raw2285step1 raw2285step0; decide +kernel
      have hl : raw2285step0Labels = labelEmbedding1 ∘ raw2285step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2285step0 raw2285step0Labels raw2285step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10587 raw10587Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw10587 raw10587Labels = mixedMoment B raw10587step0 raw10587step0Labels := by
      have hz : ∀ j, raw10587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10587step0 = (fun i j => raw10587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10587step0 raw10587; decide +kernel
      have hl : raw10587step0Labels = raw10587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10587 raw10587Labels permutation346 hz
    mixedMoment B raw10587step0 raw10587step0Labels = mixedMoment B raw10587step1 raw10587step1Labels := by
      have ha : raw10587step1 = (fun i j => raw10587step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10587step1 raw10587step0; decide +kernel
      have hl : raw10587step1Labels = raw10587step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10587step0 raw10587step0Labels permutation38 permutation2
    _ = mixedMoment B node4600 node4600Labels := by rfl

theorem canonical10592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10592 raw10592Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw10592 raw10592Labels = mixedMoment B raw10592step0 raw10592step0Labels := by
      have hz : ∀ j, raw10592 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10592step0 = (fun i j => raw10592 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10592step0 raw10592; decide +kernel
      have hl : raw10592step0Labels = raw10592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10592 raw10592Labels permutation265 hz
    mixedMoment B raw10592step0 raw10592step0Labels = mixedMoment B raw10592step1 raw10592step1Labels := by
      have ha : raw10592step1 = (fun i j => raw10592step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10592step1 raw10592step0; decide +kernel
      have hl : raw10592step1Labels = raw10592step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10592step0 raw10592step0Labels permutation38 permutation2
    _ = mixedMoment B node4600 node4600Labels := by rfl

theorem canonical10597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10597 raw10597Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw10597 raw10597Labels = mixedMoment B raw10597step0 raw10597step0Labels := by
      have hz : ∀ j, raw10597 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10597step0 = (fun i j => raw10597 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10597step0 raw10597; decide +kernel
      have hl : raw10597step0Labels = raw10597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10597 raw10597Labels permutation346 hz
    mixedMoment B raw10597step0 raw10597step0Labels = mixedMoment B raw10597step1 raw10597step1Labels := by
      have hz : ∀ j, raw10597step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10597step1 = (fun i j => raw10597step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10597step1 raw10597step0; decide +kernel
      have hl : raw10597step1Labels = raw10597step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10597step0 raw10597step0Labels permutation56 hz
    _ = mixedMoment B node4617 node4617Labels := by rfl

theorem canonical10602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10602 raw10602Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw10602 raw10602Labels = mixedMoment B raw10602step0 raw10602step0Labels := by
      have hz : ∀ j, raw10602 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10602step0 = (fun i j => raw10602 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10602step0 raw10602; decide +kernel
      have hl : raw10602step0Labels = raw10602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10602 raw10602Labels permutation346 hz
    mixedMoment B raw10602step0 raw10602step0Labels = mixedMoment B raw10602step1 raw10602step1Labels := by
      have hz : ∀ j, raw10602step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10602step1 = (fun i j => raw10602step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10602step1 raw10602step0; decide +kernel
      have hl : raw10602step1Labels = raw10602step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10602step0 raw10602step0Labels permutation56 hz
    _ = mixedMoment B node4611 node4611Labels := by rfl

theorem canonical10608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10608 raw10608Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw10608 raw10608Labels = mixedMoment B raw10608step0 raw10608step0Labels := by
      have hz : ∀ j, raw10608 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10608step0 = (fun i j => raw10608 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10608step0 raw10608; decide +kernel
      have hl : raw10608step0Labels = raw10608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10608 raw10608Labels permutation346 hz
    mixedMoment B raw10608step0 raw10608step0Labels = mixedMoment B raw10608step1 raw10608step1Labels := by
      have ha : raw10608step1 = (fun i j => raw10608step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10608step1 raw10608step0; decide +kernel
      have hl : raw10608step1Labels = raw10608step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10608step0 raw10608step0Labels permutation151 permutation2
    mixedMoment B raw10608step1 raw10608step1Labels = mixedMoment B raw10608step2 raw10608step2Labels := by
      have ha : raw10608step2 = -raw10608step1 := by apply Matrix.ext; change ∀ i j, raw10608step2 i j = -(raw10608step1 i j); unfold raw10608step2 raw10608step1; decide +kernel
      have hl : raw10608step2Labels = raw10608step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical10609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10609 raw10609Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw10609 raw10609Labels = mixedMoment B raw10609step0 raw10609step0Labels := by
      have hz : ∀ j, raw10609 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10609step0 = (fun i j => raw10609 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10609step0 raw10609; decide +kernel
      have hl : raw10609step0Labels = raw10609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10609 raw10609Labels permutation265 hz
    mixedMoment B raw10609step0 raw10609step0Labels = mixedMoment B raw10609step1 raw10609step1Labels := by
      have ha : raw10609step1 = (fun i j => raw10609step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10609step1 raw10609step0; decide +kernel
      have hl : raw10609step1Labels = raw10609step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10609step0 raw10609step0Labels permutation151 permutation2
    mixedMoment B raw10609step1 raw10609step1Labels = mixedMoment B raw10609step2 raw10609step2Labels := by
      have ha : raw10609step2 = -raw10609step1 := by apply Matrix.ext; change ∀ i j, raw10609step2 i j = -(raw10609step1 i j); unfold raw10609step2 raw10609step1; decide +kernel
      have hl : raw10609step2Labels = raw10609step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical10610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10610 raw10610Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw10610 raw10610Labels = mixedMoment B raw10610step0 raw10610step0Labels := by
      have hz : ∀ j, raw10610 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10610step0 = (fun i j => raw10610 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10610step0 raw10610; decide +kernel
      have hl : raw10610step0Labels = raw10610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10610 raw10610Labels permutation346 hz
    mixedMoment B raw10610step0 raw10610step0Labels = mixedMoment B raw10610step1 raw10610step1Labels := by
      have hz : ∀ j, raw10610step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10610step1 = (fun i j => raw10610step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10610step1 raw10610step0; decide +kernel
      have hl : raw10610step1Labels = raw10610step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10610step0 raw10610step0Labels permutation56 hz
    mixedMoment B raw10610step1 raw10610step1Labels = mixedMoment B raw10610step2 raw10610step2Labels := by
      have ha : raw10610step2 = (fun i j => raw10610step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10610step2 raw10610step1; decide +kernel
      have hl : raw10610step2Labels = raw10610step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10610step1 raw10610step1Labels permutation31 permutation2
    mixedMoment B raw10610step2 raw10610step2Labels = mixedMoment B raw10610step3 raw10610step3Labels := by
      have ha : raw10610step3 = -raw10610step2 := by apply Matrix.ext; change ∀ i j, raw10610step3 i j = -(raw10610step2 i j); unfold raw10610step3 raw10610step2; decide +kernel
      have hl : raw10610step3Labels = raw10610step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4841 node4841Labels := by rfl

theorem canonical10611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10611 raw10611Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw10611 raw10611Labels = mixedMoment B raw10611step0 raw10611step0Labels := by
      have hz : ∀ j, raw10611 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10611step0 = (fun i j => raw10611 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10611step0 raw10611; decide +kernel
      have hl : raw10611step0Labels = raw10611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10611 raw10611Labels permutation520 hz
    mixedMoment B raw10611step0 raw10611step0Labels = mixedMoment B raw10611step1 raw10611step1Labels := by
      have hz : ∀ j, raw10611step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10611step1 = (fun i j => raw10611step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10611step1 raw10611step0; decide +kernel
      have hl : raw10611step1Labels = raw10611step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10611step0 raw10611step0Labels permutation80 hz
    mixedMoment B raw10611step1 raw10611step1Labels = mixedMoment B raw10611step2 raw10611step2Labels := by
      have hz : ∀ j, raw10611step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10611step2 = (fun i j => raw10611step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10611step2 raw10611step1; decide +kernel
      have hl : raw10611step2Labels = raw10611step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10611step1 raw10611step1Labels permutation14 hz
    mixedMoment B raw10611step2 raw10611step2Labels = mixedMoment B raw10611step3 raw10611step3Labels := by
      have ha : raw10611step3 = (fun i j => raw10611step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10611step3 raw10611step2; decide +kernel
      have hl : raw10611step3Labels = raw10611step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10611step2 raw10611step2Labels permutation7 permutation2
    mixedMoment B raw10611step3 raw10611step3Labels = mixedMoment B raw10611step4 raw10611step4Labels := by
      have ha : raw10611step4 = -raw10611step3 := by apply Matrix.ext; change ∀ i j, raw10611step4 i j = -(raw10611step3 i j); unfold raw10611step4 raw10611step3; decide +kernel
      have hl : raw10611step4Labels = raw10611step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4897 node4897Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10647 raw10647Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw10647 raw10647Labels = mixedMoment B raw10647step0 raw10647step0Labels := by
      have hz : ∀ j, raw10647 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10647step0 = (fun i j => raw10647 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10647step0 raw10647; decide +kernel
      have hl : raw10647step0Labels = raw10647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10647 raw10647Labels permutation346 hz
    mixedMoment B raw10647step0 raw10647step0Labels = mixedMoment B raw10647step1 raw10647step1Labels := by
      have ha : raw10647step1 = (fun i j => raw10647step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10647step1 raw10647step0; decide +kernel
      have hl : raw10647step1Labels = raw10647step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10647step0 raw10647step0Labels permutation139 permutation7
    mixedMoment B raw10647step1 raw10647step1Labels = mixedMoment B raw10647step2 raw10647step2Labels := by
      have ha : raw10647step2 = raw10647step1 := by apply Matrix.ext; unfold raw10647step2 raw10647step1; decide +kernel
      have hl : raw10647step1Labels = labelEmbedding1 ∘ raw10647step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10647step1 raw10647step1Labels raw10647step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

theorem canonical10652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10652 raw10652Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw10652 raw10652Labels = mixedMoment B raw10652step0 raw10652step0Labels := by
      have hz : ∀ j, raw10652 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10652step0 = (fun i j => raw10652 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10652step0 raw10652; decide +kernel
      have hl : raw10652step0Labels = raw10652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10652 raw10652Labels permutation265 hz
    mixedMoment B raw10652step0 raw10652step0Labels = mixedMoment B raw10652step1 raw10652step1Labels := by
      have ha : raw10652step1 = (fun i j => raw10652step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10652step1 raw10652step0; decide +kernel
      have hl : raw10652step1Labels = raw10652step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10652step0 raw10652step0Labels permutation139 permutation7
    mixedMoment B raw10652step1 raw10652step1Labels = mixedMoment B raw10652step2 raw10652step2Labels := by
      have ha : raw10652step2 = raw10652step1 := by apply Matrix.ext; unfold raw10652step2 raw10652step1; decide +kernel
      have hl : raw10652step1Labels = labelEmbedding1 ∘ raw10652step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10652step1 raw10652step1Labels raw10652step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

theorem canonical10657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10657 raw10657Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw10657 raw10657Labels = mixedMoment B raw10657step0 raw10657step0Labels := by
      have hz : ∀ j, raw10657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10657step0 = (fun i j => raw10657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10657step0 raw10657; decide +kernel
      have hl : raw10657step0Labels = raw10657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10657 raw10657Labels permutation346 hz
    mixedMoment B raw10657step0 raw10657step0Labels = mixedMoment B raw10657step1 raw10657step1Labels := by
      have hz : ∀ j, raw10657step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10657step1 = (fun i j => raw10657step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10657step1 raw10657step0; decide +kernel
      have hl : raw10657step1Labels = raw10657step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10657step0 raw10657step0Labels permutation56 hz
    mixedMoment B raw10657step1 raw10657step1Labels = mixedMoment B raw10657step2 raw10657step2Labels := by
      have ha : raw10657step2 = (fun i j => raw10657step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10657step2 raw10657step1; decide +kernel
      have hl : raw10657step2Labels = raw10657step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10657step1 raw10657step1Labels permutation31 permutation7
    mixedMoment B raw10657step2 raw10657step2Labels = mixedMoment B raw10657step3 raw10657step3Labels := by
      have ha : raw10657step3 = raw10657step2 := by apply Matrix.ext; unfold raw10657step3 raw10657step2; decide +kernel
      have hl : raw10657step2Labels = labelEmbedding1 ∘ raw10657step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10657step2 raw10657step2Labels raw10657step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

theorem canonical10662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10662 raw10662Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw10662 raw10662Labels = mixedMoment B raw10662step0 raw10662step0Labels := by
      have hz : ∀ j, raw10662 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10662step0 = (fun i j => raw10662 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10662step0 raw10662; decide +kernel
      have hl : raw10662step0Labels = raw10662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10662 raw10662Labels permutation346 hz
    mixedMoment B raw10662step0 raw10662step0Labels = mixedMoment B raw10662step1 raw10662step1Labels := by
      have hz : ∀ j, raw10662step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10662step1 = (fun i j => raw10662step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10662step1 raw10662step0; decide +kernel
      have hl : raw10662step1Labels = raw10662step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10662step0 raw10662step0Labels permutation56 hz
    mixedMoment B raw10662step1 raw10662step1Labels = mixedMoment B raw10662step2 raw10662step2Labels := by
      have ha : raw10662step2 = (fun i j => raw10662step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10662step2 raw10662step1; decide +kernel
      have hl : raw10662step2Labels = raw10662step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10662step1 raw10662step1Labels permutation31 permutation7
    mixedMoment B raw10662step2 raw10662step2Labels = mixedMoment B raw10662step3 raw10662step3Labels := by
      have ha : raw10662step3 = raw10662step2 := by apply Matrix.ext; unfold raw10662step3 raw10662step2; decide +kernel
      have hl : raw10662step2Labels = labelEmbedding1 ∘ raw10662step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10662step2 raw10662step2Labels raw10662step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2683 node2683Labels := by rfl

theorem canonical10668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10668 raw10668Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw10668 raw10668Labels = mixedMoment B raw10668step0 raw10668step0Labels := by
      have hz : ∀ j, raw10668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10668step0 = (fun i j => raw10668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10668step0 raw10668; decide +kernel
      have hl : raw10668step0Labels = raw10668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10668 raw10668Labels permutation346 hz
    mixedMoment B raw10668step0 raw10668step0Labels = mixedMoment B raw10668step1 raw10668step1Labels := by
      have ha : raw10668step1 = (fun i j => raw10668step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10668step1 raw10668step0; decide +kernel
      have hl : raw10668step1Labels = raw10668step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10668step0 raw10668step0Labels permutation149 permutation7
    mixedMoment B raw10668step1 raw10668step1Labels = mixedMoment B raw10668step2 raw10668step2Labels := by
      have ha : raw10668step2 = raw10668step1 := by apply Matrix.ext; unfold raw10668step2 raw10668step1; decide +kernel
      have hl : raw10668step1Labels = labelEmbedding1 ∘ raw10668step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10668step1 raw10668step1Labels raw10668step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical10669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10669 raw10669Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw10669 raw10669Labels = mixedMoment B raw10669step0 raw10669step0Labels := by
      have hz : ∀ j, raw10669 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10669step0 = (fun i j => raw10669 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10669step0 raw10669; decide +kernel
      have hl : raw10669step0Labels = raw10669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10669 raw10669Labels permutation265 hz
    mixedMoment B raw10669step0 raw10669step0Labels = mixedMoment B raw10669step1 raw10669step1Labels := by
      have ha : raw10669step1 = (fun i j => raw10669step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10669step1 raw10669step0; decide +kernel
      have hl : raw10669step1Labels = raw10669step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10669step0 raw10669step0Labels permutation149 permutation7
    mixedMoment B raw10669step1 raw10669step1Labels = mixedMoment B raw10669step2 raw10669step2Labels := by
      have ha : raw10669step2 = raw10669step1 := by apply Matrix.ext; unfold raw10669step2 raw10669step1; decide +kernel
      have hl : raw10669step1Labels = labelEmbedding1 ∘ raw10669step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10669step1 raw10669step1Labels raw10669step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

theorem canonical10670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10670 raw10670Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw10670 raw10670Labels = mixedMoment B raw10670step0 raw10670step0Labels := by
      have hz : ∀ j, raw10670 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10670step0 = (fun i j => raw10670 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10670step0 raw10670; decide +kernel
      have hl : raw10670step0Labels = raw10670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10670 raw10670Labels permutation346 hz
    mixedMoment B raw10670step0 raw10670step0Labels = mixedMoment B raw10670step1 raw10670step1Labels := by
      have hz : ∀ j, raw10670step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10670step1 = (fun i j => raw10670step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10670step1 raw10670step0; decide +kernel
      have hl : raw10670step1Labels = raw10670step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10670step0 raw10670step0Labels permutation56 hz
    mixedMoment B raw10670step1 raw10670step1Labels = mixedMoment B raw10670step2 raw10670step2Labels := by
      have ha : raw10670step2 = (fun i j => raw10670step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10670step2 raw10670step1; decide +kernel
      have hl : raw10670step2Labels = raw10670step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10670step1 raw10670step1Labels permutation31 permutation7
    mixedMoment B raw10670step2 raw10670step2Labels = mixedMoment B raw10670step3 raw10670step3Labels := by
      have ha : raw10670step3 = raw10670step2 := by apply Matrix.ext; unfold raw10670step3 raw10670step2; decide +kernel
      have hl : raw10670step2Labels = labelEmbedding1 ∘ raw10670step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10670step2 raw10670step2Labels raw10670step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

theorem canonical10671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10671 raw10671Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw10671 raw10671Labels = mixedMoment B raw10671step0 raw10671step0Labels := by
      have hz : ∀ j, raw10671 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10671step0 = (fun i j => raw10671 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10671step0 raw10671; decide +kernel
      have hl : raw10671step0Labels = raw10671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10671 raw10671Labels permutation520 hz
    mixedMoment B raw10671step0 raw10671step0Labels = mixedMoment B raw10671step1 raw10671step1Labels := by
      have hz : ∀ j, raw10671step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10671step1 = (fun i j => raw10671step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10671step1 raw10671step0; decide +kernel
      have hl : raw10671step1Labels = raw10671step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10671step0 raw10671step0Labels permutation80 hz
    mixedMoment B raw10671step1 raw10671step1Labels = mixedMoment B raw10671step2 raw10671step2Labels := by
      have hz : ∀ j, raw10671step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10671step2 = (fun i j => raw10671step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10671step2 raw10671step1; decide +kernel
      have hl : raw10671step2Labels = raw10671step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10671step1 raw10671step1Labels permutation14 hz
    mixedMoment B raw10671step2 raw10671step2Labels = mixedMoment B raw10671step3 raw10671step3Labels := by
      have ha : raw10671step3 = (fun i j => raw10671step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10671step3 raw10671step2; decide +kernel
      have hl : raw10671step3Labels = raw10671step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10671step2 raw10671step2Labels permutation7 permutation7
    mixedMoment B raw10671step3 raw10671step3Labels = mixedMoment B raw10671step4 raw10671step4Labels := by
      have ha : raw10671step4 = raw10671step3 := by apply Matrix.ext; unfold raw10671step4 raw10671step3; decide +kernel
      have hl : raw10671step3Labels = labelEmbedding1 ∘ raw10671step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10671step3 raw10671step3Labels raw10671step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2292 node2292Labels := by rfl

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

theorem canonical1152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1152 raw1152Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw1152 raw1152Labels = mixedMoment B raw1152step0 raw1152step0Labels := by
      have ha : raw1152step0 = (fun i j => raw1152 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1152step0 raw1152; decide +kernel
      have hl : raw1152step0Labels = raw1152Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1152 raw1152Labels permutation8 permutation4
    mixedMoment B raw1152step0 raw1152step0Labels = mixedMoment B raw1152step1 raw1152step1Labels := by
      have ha : raw1152step1 = raw1152step0 := by apply Matrix.ext; unfold raw1152step1 raw1152step0; decide +kernel
      have hl : raw1152step0Labels = labelEmbedding7 ∘ raw1152step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1152step0 raw1152step0Labels raw1152step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4356 node4356Labels := by rfl

theorem canonical1153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1153 raw1153Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw1153 raw1153Labels = mixedMoment B raw1153step0 raw1153step0Labels := by
      have ha : raw1153step0 = (fun i j => raw1153 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1153step0 raw1153; decide +kernel
      have hl : raw1153step0Labels = raw1153Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1153 raw1153Labels permutation8 permutation4
    _ = mixedMoment B node934 node934Labels := by rfl

theorem canonical1154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1154 raw1154Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw1154 raw1154Labels = mixedMoment B raw1154step0 raw1154step0Labels := by
      have ha : raw1154step0 = (fun i j => raw1154 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1154step0 raw1154; decide +kernel
      have hl : raw1154step0Labels = raw1154Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1154 raw1154Labels permutation8 permutation6
    mixedMoment B raw1154step0 raw1154step0Labels = mixedMoment B raw1154step1 raw1154step1Labels := by
      have ha : raw1154step1 = -raw1154step0 := by apply Matrix.ext; change ∀ i j, raw1154step1 i j = -(raw1154step0 i j); unfold raw1154step1 raw1154step0; decide +kernel
      have hl : raw1154step1Labels = raw1154step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1154step1 raw1154step1Labels = mixedMoment B raw1154step2 raw1154step2Labels := by
      have ha : raw1154step2 = raw1154step1 := by apply Matrix.ext; unfold raw1154step2 raw1154step1; decide +kernel
      have hl : raw1154step1Labels = labelEmbedding1 ∘ raw1154step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1154step1 raw1154step1Labels raw1154step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4356 node4356Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node934 node934Labels + mixedMoment B node1692 node1692Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1152 singletonSmall4356
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4356) = raw1152Labels := by decide +kernel
  rw [hl, canonical1152 B hB] at h
  have hc0 : mixedMoment B raw1152 (Fin.cases (0 : Fin 2) singletonSmall4356) =
      mixedMoment B node934 node934Labels := by
    have ha : raw1152 = raw1153 := by apply Matrix.ext; unfold raw1152 raw1153; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4356 = raw1153Labels := by decide +kernel
    rw [ha, hj, canonical1153 B hB]
  have hc1 : mixedMoment B raw1152 (Fin.cases (1 : Fin 2) singletonSmall4356) =
      mixedMoment B node1692 node1692Labels := by
    have ha : raw1152 = raw1154 := by apply Matrix.ext; unfold raw1152 raw1154; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4356 = raw1154Labels := by decide +kernel
    rw [ha, hj, canonical1154 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4543 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4543 node4543Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1128 node1128Labels + mixedMoment B node2184 node2184Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1365 singletonSmall4543
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4543) = raw1365Labels := by decide +kernel
  rw [hl, canonical1365 B hB] at h
  have hc0 : mixedMoment B raw1365 (Fin.cases (0 : Fin 2) singletonSmall4543) =
      mixedMoment B node1128 node1128Labels := by
    have ha : raw1365 = raw1366 := by apply Matrix.ext; unfold raw1365 raw1366; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4543 = raw1366Labels := by decide +kernel
    rw [ha, hj, canonical1366 B hB]
  have hc1 : mixedMoment B raw1365 (Fin.cases (1 : Fin 2) singletonSmall4543) =
      mixedMoment B node2184 node2184Labels := by
    have ha : raw1365 = raw1367 := by apply Matrix.ext; unfold raw1365 raw1367; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4543 = raw1367Labels := by decide +kernel
    rw [ha, hj, canonical1367 B hB]
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

theorem singleton4557 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4557 node4557Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1143 node1143Labels + mixedMoment B node2167 node2167Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1392 singletonSmall4557
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4557) = raw1392Labels := by decide +kernel
  rw [hl, canonical1392 B hB] at h
  have hc0 : mixedMoment B raw1392 (Fin.cases (0 : Fin 2) singletonSmall4557) =
      mixedMoment B node1143 node1143Labels := by
    have ha : raw1392 = raw1393 := by apply Matrix.ext; unfold raw1392 raw1393; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4557 = raw1393Labels := by decide +kernel
    rw [ha, hj, canonical1393 B hB]
  have hc1 : mixedMoment B raw1392 (Fin.cases (1 : Fin 2) singletonSmall4557) =
      mixedMoment B node2167 node2167Labels := by
    have ha : raw1392 = raw1394 := by apply Matrix.ext; unfold raw1392 raw1394; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4557 = raw1394Labels := by decide +kernel
    rw [ha, hj, canonical1394 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4621 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4621 node4621Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1297 node1297Labels + mixedMoment B node2289 node2289Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1446 singletonSmall4621
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4621) = raw1446Labels := by decide +kernel
  rw [hl, canonical1446 B hB] at h
  have hc0 : mixedMoment B raw1446 (Fin.cases (0 : Fin 2) singletonSmall4621) =
      mixedMoment B node1297 node1297Labels := by
    have ha : raw1446 = raw1447 := by apply Matrix.ext; unfold raw1446 raw1447; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4621 = raw1447Labels := by decide +kernel
    rw [ha, hj, canonical1447 B hB]
  have hc1 : mixedMoment B raw1446 (Fin.cases (1 : Fin 2) singletonSmall4621) =
      mixedMoment B node2289 node2289Labels := by
    have ha : raw1446 = raw1448 := by apply Matrix.ext; unfold raw1446 raw1448; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4621 = raw1448Labels := by decide +kernel
    rw [ha, hj, canonical1448 B hB]
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

theorem singleton4804 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4804 node4804Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2022 node2022Labels + mixedMoment B node2203 node2203Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1737 singletonSmall4804
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4804) = raw1737Labels := by decide +kernel
  rw [hl, canonical1737 B hB] at h
  have hc0 : mixedMoment B raw1737 (Fin.cases (0 : Fin 2) singletonSmall4804) =
      mixedMoment B node2022 node2022Labels := by
    have ha : raw1737 = raw1738 := by apply Matrix.ext; unfold raw1737 raw1738; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4804 = raw1738Labels := by decide +kernel
    rw [ha, hj, canonical1738 B hB]
  have hc1 : mixedMoment B raw1737 (Fin.cases (1 : Fin 2) singletonSmall4804) =
      mixedMoment B node2203 node2203Labels := by
    have ha : raw1737 = raw1739 := by apply Matrix.ext; unfold raw1737 raw1739; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4804 = raw1739Labels := by decide +kernel
    rw [ha, hj, canonical1739 B hB]
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

theorem singleton5272 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5272 node5272Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2740 node2740Labels + mixedMoment B node2740 node2740Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2283 singletonSmall5272
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5272) = raw2283Labels := by decide +kernel
  rw [hl, canonical2283 B hB] at h
  have hc0 : mixedMoment B raw2283 (Fin.cases (0 : Fin 2) singletonSmall5272) =
      mixedMoment B node2740 node2740Labels := by
    have ha : raw2283 = raw2284 := by apply Matrix.ext; unfold raw2283 raw2284; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5272 = raw2284Labels := by decide +kernel
    rw [ha, hj, canonical2284 B hB]
  have hc1 : mixedMoment B raw2283 (Fin.cases (1 : Fin 2) singletonSmall5272) =
      mixedMoment B node2740 node2740Labels := by
    have ha : raw2283 = raw2285 := by apply Matrix.ext; unfold raw2283 raw2285; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5272 = raw2285Labels := by decide +kernel
    rw [ha, hj, canonical2285 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node908 node908Labels = Sparse.eval nodeValue908 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 908) = mixedMoment B node908 node908Labels := rfl
  simpa [nodeValue908, Sparse.eval] using hc.symm

theorem sound934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node934 node934Labels = Sparse.eval nodeValue934 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 934) = mixedMoment B node934 node934Labels := rfl
  simpa [nodeValue934, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1002 node1002Labels = Sparse.eval nodeValue1002 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1002) = mixedMoment B node1002 node1002Labels := rfl
  simpa [nodeValue1002, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1128 node1128Labels = Sparse.eval nodeValue1128 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1128) = mixedMoment B node1128 node1128Labels := rfl
  simpa [nodeValue1128, Sparse.eval] using hc.symm

theorem sound1143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1143 node1143Labels = Sparse.eval nodeValue1143 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1143) = mixedMoment B node1143 node1143Labels := rfl
  simpa [nodeValue1143, Sparse.eval] using hc.symm

theorem sound1147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1147 node1147Labels = Sparse.eval nodeValue1147 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1147) = mixedMoment B node1147 node1147Labels := rfl
  simpa [nodeValue1147, Sparse.eval] using hc.symm

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

theorem sound1153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1153 node1153Labels = Sparse.eval nodeValue1153 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1153) = mixedMoment B node1153 node1153Labels := rfl
  simpa [nodeValue1153, Sparse.eval] using hc.symm

theorem sound1157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1157 node1157Labels = Sparse.eval nodeValue1157 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1157) = mixedMoment B node1157 node1157Labels := rfl
  simpa [nodeValue1157, Sparse.eval] using hc.symm

theorem sound1185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1185 node1185Labels = Sparse.eval nodeValue1185 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1185) = mixedMoment B node1185 node1185Labels := rfl
  simpa [nodeValue1185, Sparse.eval] using hc.symm

theorem sound1191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1191 node1191Labels = Sparse.eval nodeValue1191 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1191) = mixedMoment B node1191 node1191Labels := rfl
  simpa [nodeValue1191, Sparse.eval] using hc.symm

theorem sound1193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1193 node1193Labels = Sparse.eval nodeValue1193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1193) = mixedMoment B node1193 node1193Labels := rfl
  simpa [nodeValue1193, Sparse.eval] using hc.symm

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

theorem sound1231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1231 node1231Labels = Sparse.eval nodeValue1231 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1231) = mixedMoment B node1231 node1231Labels := rfl
  simpa [nodeValue1231, Sparse.eval] using hc.symm

theorem sound1234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1234 node1234Labels = Sparse.eval nodeValue1234 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1234) = mixedMoment B node1234 node1234Labels := rfl
  simpa [nodeValue1234, Sparse.eval] using hc.symm

theorem sound1239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1239 node1239Labels = Sparse.eval nodeValue1239 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1239) = mixedMoment B node1239 node1239Labels := rfl
  simpa [nodeValue1239, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1288 node1288Labels = Sparse.eval nodeValue1288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1288) = mixedMoment B node1288 node1288Labels := rfl
  simpa [nodeValue1288, Sparse.eval] using hc.symm

theorem sound1297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1297 node1297Labels = Sparse.eval nodeValue1297 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1297) = mixedMoment B node1297 node1297Labels := rfl
  simpa [nodeValue1297, Sparse.eval] using hc.symm

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

theorem sound1528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1528 node1528Labels = Sparse.eval nodeValue1528 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1528) = mixedMoment B node1528 node1528Labels := rfl
  simpa [nodeValue1528, Sparse.eval] using hc.symm

theorem sound1529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1529 node1529Labels = Sparse.eval nodeValue1529 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1529) = mixedMoment B node1529 node1529Labels := rfl
  simpa [nodeValue1529, Sparse.eval] using hc.symm

theorem sound1530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1530 node1530Labels = Sparse.eval nodeValue1530 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1530) = mixedMoment B node1530 node1530Labels := rfl
  simpa [nodeValue1530, Sparse.eval] using hc.symm

theorem sound1532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1532 node1532Labels = Sparse.eval nodeValue1532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1532) = mixedMoment B node1532 node1532Labels := rfl
  simpa [nodeValue1532, Sparse.eval] using hc.symm

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

theorem sound1599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1599 node1599Labels = Sparse.eval nodeValue1599 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1599) = mixedMoment B node1599 node1599Labels := rfl
  simpa [nodeValue1599, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1625 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1625 node1625Labels = 0 := by
  exact mixedMoment_order_one B hB node1625 node1625Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1617 node1617Labels = Sparse.eval nodeValue1617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1617) = mixedMoment B node1617 node1617Labels := rfl
  simpa [nodeValue1617, Sparse.eval] using hc.symm

theorem sound1625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1625 node1625Labels = Sparse.eval nodeValue1625 (mixedVector B) := by
  simpa only [nodeValue1625, Sparse.eval_nil] using zero1625 B _hB _hF

theorem sound1630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1630 node1630Labels = Sparse.eval nodeValue1630 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1630) = mixedMoment B node1630 node1630Labels := rfl
  simpa [nodeValue1630, Sparse.eval] using hc.symm

theorem sound1637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1637 node1637Labels = Sparse.eval nodeValue1637 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1637) = mixedMoment B node1637 node1637Labels := rfl
  simpa [nodeValue1637, Sparse.eval] using hc.symm

theorem sound1650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1650 node1650Labels = Sparse.eval nodeValue1650 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1650) = mixedMoment B node1650 node1650Labels := rfl
  simpa [nodeValue1650, Sparse.eval] using hc.symm

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

theorem sound1672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1672 node1672Labels = Sparse.eval nodeValue1672 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1672) = mixedMoment B node1672 node1672Labels := rfl
  simpa [nodeValue1672, Sparse.eval] using hc.symm

theorem sound1692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1692 node1692Labels = Sparse.eval nodeValue1692 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1692) = mixedMoment B node1692 node1692Labels := rfl
  simpa [nodeValue1692, Sparse.eval] using hc.symm

theorem sound1710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1710 node1710Labels = Sparse.eval nodeValue1710 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1710) = mixedMoment B node1710 node1710Labels := rfl
  simpa [nodeValue1710, Sparse.eval] using hc.symm

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

theorem sound1752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1752 node1752Labels = Sparse.eval nodeValue1752 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1752) = mixedMoment B node1752 node1752Labels := rfl
  simpa [nodeValue1752, Sparse.eval] using hc.symm

theorem sound1754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1754 node1754Labels = Sparse.eval nodeValue1754 (mixedVector B) := by
  simpa only [nodeValue1754, Sparse.eval_nil] using zero1754 B _hB _hF

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

theorem sound2022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2022 node2022Labels = Sparse.eval nodeValue2022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2022) = mixedMoment B node2022 node2022Labels := rfl
  simpa [nodeValue2022, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2060 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2060 node2060Labels = 0 := by
  exact mixedMoment_order_one B hB node2060 node2060Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2060 node2060Labels = Sparse.eval nodeValue2060 (mixedVector B) := by
  simpa only [nodeValue2060, Sparse.eval_nil] using zero2060 B _hB _hF

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

theorem sound2149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2149 node2149Labels = Sparse.eval nodeValue2149 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2149) = mixedMoment B node2149 node2149Labels := rfl
  simpa [nodeValue2149, Sparse.eval] using hc.symm

theorem sound2167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2167 node2167Labels = Sparse.eval nodeValue2167 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2167) = mixedMoment B node2167 node2167Labels := rfl
  simpa [nodeValue2167, Sparse.eval] using hc.symm

theorem sound2172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2172 node2172Labels = Sparse.eval nodeValue2172 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2172) = mixedMoment B node2172 node2172Labels := rfl
  simpa [nodeValue2172, Sparse.eval] using hc.symm

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

theorem zero2228 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2228 node2228Labels = 0 := by
  exact mixedMoment_order_one B hB node2228 node2228Labels 1
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

theorem sound2184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2184 node2184Labels = Sparse.eval nodeValue2184 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2184) = mixedMoment B node2184 node2184Labels := rfl
  simpa [nodeValue2184, Sparse.eval] using hc.symm

theorem sound2200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2200 node2200Labels = Sparse.eval nodeValue2200 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2200) = mixedMoment B node2200 node2200Labels := rfl
  simpa [nodeValue2200, Sparse.eval] using hc.symm

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

theorem sound2226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2226 node2226Labels = Sparse.eval nodeValue2226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2226) = mixedMoment B node2226 node2226Labels := rfl
  simpa [nodeValue2226, Sparse.eval] using hc.symm

theorem sound2228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2228 node2228Labels = Sparse.eval nodeValue2228 (mixedVector B) := by
  simpa only [nodeValue2228, Sparse.eval_nil] using zero2228 B _hB _hF

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

theorem zero2292 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2292 node2292Labels = 0 := by
  exact mixedMoment_order_one B hB node2292 node2292Labels 1
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

theorem sound2289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2289 node2289Labels = Sparse.eval nodeValue2289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2289) = mixedMoment B node2289 node2289Labels := rfl
  simpa [nodeValue2289, Sparse.eval] using hc.symm

theorem sound2292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2292 node2292Labels = Sparse.eval nodeValue2292 (mixedVector B) := by
  simpa only [nodeValue2292, Sparse.eval_nil] using zero2292 B _hB _hF

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

theorem sound2391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2391 node2391Labels = Sparse.eval nodeValue2391 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2391) = mixedMoment B node2391 node2391Labels := rfl
  simpa [nodeValue2391, Sparse.eval] using hc.symm

theorem sound2407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2407 node2407Labels = Sparse.eval nodeValue2407 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2407) = mixedMoment B node2407 node2407Labels := rfl
  simpa [nodeValue2407, Sparse.eval] using hc.symm

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

theorem sound2680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2680 node2680Labels = Sparse.eval nodeValue2680 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2680) = mixedMoment B node2680 node2680Labels := rfl
  simpa [nodeValue2680, Sparse.eval] using hc.symm

theorem sound2683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2683 node2683Labels = Sparse.eval nodeValue2683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2683) = mixedMoment B node2683 node2683Labels := rfl
  simpa [nodeValue2683, Sparse.eval] using hc.symm

theorem sound2686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2686 node2686Labels = Sparse.eval nodeValue2686 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2686) = mixedMoment B node2686 node2686Labels := rfl
  simpa [nodeValue2686, Sparse.eval] using hc.symm

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

theorem sound2702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2702 node2702Labels = Sparse.eval nodeValue2702 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2702) = mixedMoment B node2702 node2702Labels := rfl
  simpa [nodeValue2702, Sparse.eval] using hc.symm

theorem sound2737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2737 node2737Labels = Sparse.eval nodeValue2737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2737) = mixedMoment B node2737 node2737Labels := rfl
  simpa [nodeValue2737, Sparse.eval] using hc.symm

theorem sound2740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2740 node2740Labels = Sparse.eval nodeValue2740 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2740) = mixedMoment B node2740 node2740Labels := rfl
  simpa [nodeValue2740, Sparse.eval] using hc.symm

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

theorem sound4069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4069 node4069Labels = Sparse.eval nodeValue4069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4069) = mixedMoment B node4069 node4069Labels := rfl
  simpa [nodeValue4069, Sparse.eval] using hc.symm

theorem sound4070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4070 node4070Labels = Sparse.eval nodeValue4070 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4070) = mixedMoment B node4070 node4070Labels := rfl
  simpa [nodeValue4070, Sparse.eval] using hc.symm

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

theorem sound4089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4089 node4089Labels = Sparse.eval nodeValue4089 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4089) = mixedMoment B node4089 node4089Labels := rfl
  simpa [nodeValue4089, Sparse.eval] using hc.symm

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

theorem sound624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node624 node624Labels = Sparse.eval nodeValue624 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 624) = mixedMoment B node624 node624Labels := rfl
  simpa [nodeValue624, Sparse.eval] using hc.symm

theorem sound628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node628 node628Labels = Sparse.eval nodeValue628 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 628) = mixedMoment B node628 node628Labels := rfl
  simpa [nodeValue628, Sparse.eval] using hc.symm

theorem sound634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node634 node634Labels = Sparse.eval nodeValue634 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 634) = mixedMoment B node634 node634Labels := rfl
  simpa [nodeValue634, Sparse.eval] using hc.symm

theorem sound639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node639 node639Labels = Sparse.eval nodeValue639 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 639) = mixedMoment B node639 node639Labels := rfl
  simpa [nodeValue639, Sparse.eval] using hc.symm

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

theorem sound4157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4157 node4157Labels = Sparse.eval nodeValue4157 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4157) = mixedMoment B node4157 node4157Labels := rfl
  simpa [nodeValue4157, Sparse.eval] using hc.symm

theorem sound4159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4159 node4159Labels = Sparse.eval nodeValue4159 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4159) = mixedMoment B node4159 node4159Labels := rfl
  simpa [nodeValue4159, Sparse.eval] using hc.symm

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

theorem sound4162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4162 node4162Labels = Sparse.eval nodeValue4162 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4162) = mixedMoment B node4162 node4162Labels := rfl
  simpa [nodeValue4162, Sparse.eval] using hc.symm

theorem sound4184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4184 node4184Labels = Sparse.eval nodeValue4184 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4184) = mixedMoment B node4184 node4184Labels := rfl
  simpa [nodeValue4184, Sparse.eval] using hc.symm

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

theorem sound4330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4330 node4330Labels = Sparse.eval nodeValue4330 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4330) = mixedMoment B node4330 node4330Labels := rfl
  simpa [nodeValue4330, Sparse.eval] using hc.symm

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

theorem sound4356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4356 node4356Labels = Sparse.eval nodeValue4356 (mixedVector B) := by
  have h := singleton4356 B _hB
  rw [sound934 B _hB _hF, sound1692 B _hB _hF] at h
  norm_num [nodeValue4356, nodeValue934, nodeValue1692, Sparse.eval] at h ⊢
  linarith only [h]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4532 node4532Labels = Sparse.eval nodeValue4532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4532) = mixedMoment B node4532 node4532Labels := rfl
  simpa [nodeValue4532, Sparse.eval] using hc.symm

theorem sound4536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4536 node4536Labels = Sparse.eval nodeValue4536 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4536) = mixedMoment B node4536 node4536Labels := rfl
  simpa [nodeValue4536, Sparse.eval] using hc.symm

theorem sound4543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4543 node4543Labels = Sparse.eval nodeValue4543 (mixedVector B) := by
  have h := singleton4543 B _hB
  rw [sound1128 B _hB _hF, sound2184 B _hB _hF] at h
  norm_num [nodeValue4543, nodeValue1128, nodeValue2184, Sparse.eval] at h ⊢
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

theorem sound4557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4557 node4557Labels = Sparse.eval nodeValue4557 (mixedVector B) := by
  have h := singleton4557 B _hB
  rw [sound1143 B _hB _hF, sound2167 B _hB _hF] at h
  norm_num [nodeValue4557, nodeValue1143, nodeValue2167, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4600 node4600Labels = Sparse.eval nodeValue4600 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4600) = mixedMoment B node4600 node4600Labels := rfl
  simpa [nodeValue4600, Sparse.eval] using hc.symm

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

theorem sound4611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4611 node4611Labels = Sparse.eval nodeValue4611 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4611) = mixedMoment B node4611 node4611Labels := rfl
  simpa [nodeValue4611, Sparse.eval] using hc.symm

theorem sound4617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4617 node4617Labels = Sparse.eval nodeValue4617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4617) = mixedMoment B node4617 node4617Labels := rfl
  simpa [nodeValue4617, Sparse.eval] using hc.symm

theorem sound4621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4621 node4621Labels = Sparse.eval nodeValue4621 (mixedVector B) := by
  have h := singleton4621 B _hB
  rw [sound1297 B _hB _hF, sound2289 B _hB _hF] at h
  norm_num [nodeValue4621, nodeValue1297, nodeValue2289, Sparse.eval] at h ⊢
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

theorem zero4841 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4841 node4841Labels = 0 := by
  exact mixedMoment_order_one B hB node4841 node4841Labels 1
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

theorem sound4804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4804 node4804Labels = Sparse.eval nodeValue4804 (mixedVector B) := by
  have h := singleton4804 B _hB
  rw [sound2022 B _hB _hF, sound2203 B _hB _hF] at h
  norm_num [nodeValue4804, nodeValue2022, nodeValue2203, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4841 node4841Labels = Sparse.eval nodeValue4841 (mixedVector B) := by
  simpa only [nodeValue4841, Sparse.eval_nil] using zero4841 B _hB _hF

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

theorem sound5272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5272 node5272Labels = Sparse.eval nodeValue5272 (mixedVector B) := by
  have h := singleton5272 B _hB
  rw [sound2740 B _hB _hF] at h
  norm_num [nodeValue5272, nodeValue2740, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources40
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1295 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1295 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1295 + difference 0 0) (sourceB1295 + difference 0 0) sourceC1295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1295 + difference 0 0) (sourceB1295 + difference 0 0) sourceC1295) = raw20482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1295 sourceB1295 sourceC1295 difference raw20482; decide +kernel
    rw [ha]
    exact (canonical20482 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1295 + difference 1 0) (sourceB1295 + difference 0 1) sourceC1295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1617) := by
    have ha : (tripleCharges (sourceA1295 + difference 1 0) (sourceB1295 + difference 0 1) sourceC1295) = raw20840 := by
      apply Matrix.ext; unfold tripleCharges sourceA1295 sourceB1295 sourceC1295 difference raw20840; decide +kernel
    rw [ha]
    exact (canonical20840 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1295 + difference 2 0) (sourceB1295 + difference 0 2) sourceC1295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1617) := by
    have ha : (tripleCharges (sourceA1295 + difference 2 0) (sourceB1295 + difference 0 2) sourceC1295) = raw20841 := by
      apply Matrix.ext; unfold tripleCharges sourceA1295 sourceB1295 sourceC1295 difference raw20841; decide +kernel
    rw [ha]
    exact (canonical20841 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1295 + difference 3 0) (sourceB1295 + difference 0 3) sourceC1295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1754) := by
    have ha : (tripleCharges (sourceA1295 + difference 3 0) (sourceB1295 + difference 0 3) sourceC1295) = raw20479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1295 sourceB1295 sourceC1295 difference raw20479; decide +kernel
    rw [ha]
    exact (canonical20479 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1295 + difference 4 0) (sourceB1295 + difference 0 4) sourceC1295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1630) := by
    have ha : (tripleCharges (sourceA1295 + difference 4 0) (sourceB1295 + difference 0 4) sourceC1295) = raw20842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1295 sourceB1295 sourceC1295 difference raw20842; decide +kernel
    rw [ha]
    exact (canonical20842 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1295 + difference 5 0) (sourceB1295 + difference 0 5) sourceC1295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1625) := by
    have ha : (tripleCharges (sourceA1295 + difference 5 0) (sourceB1295 + difference 0 5) sourceC1295) = raw20843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1295 sourceB1295 sourceC1295 difference raw20843; decide +kernel
    rw [ha]
    exact (canonical20843 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1295 + sourceB1295) sourceC1295) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1295 + sourceB1295) sourceC1295) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1295 sourceB1295 sourceC1295 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1295 sourceB1295 sourceC1295
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1295, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1296 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1296 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1296 + difference 0 1) (sourceB1296 + difference 1 0) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA1296 + difference 0 1) (sourceB1296 + difference 1 0) sourceC1296) = raw10608 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw10608; decide +kernel
    rw [ha]
    exact (canonical10608 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1296 + difference 0 2) (sourceB1296 + difference 2 0) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA1296 + difference 0 2) (sourceB1296 + difference 2 0) sourceC1296) = raw10609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw10609; decide +kernel
    rw [ha]
    exact (canonical10609 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1296 + difference 0 3) (sourceB1296 + difference 3 0) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA1296 + difference 0 3) (sourceB1296 + difference 3 0) sourceC1296) = raw10610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw10610; decide +kernel
    rw [ha]
    exact (canonical10610 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1296 + difference 0 4) (sourceB1296 + difference 4 0) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA1296 + difference 0 4) (sourceB1296 + difference 4 0) sourceC1296) = raw10611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw10611; decide +kernel
    rw [ha]
    exact (canonical10611 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1296 + difference 0 5) (sourceB1296 + difference 5 0) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA1296 + difference 0 5) (sourceB1296 + difference 5 0) sourceC1296) = raw20844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20844; decide +kernel
    rw [ha]
    exact (canonical20844 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1296 + difference 1 0) (sourceB1296 + difference 0 1) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4157) := by
    have ha : (tripleCharges (sourceA1296 + difference 1 0) (sourceB1296 + difference 0 1) sourceC1296) = raw20845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20845; decide +kernel
    rw [ha]
    exact (canonical20845 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1296 + difference 1 2) (sourceB1296 + difference 2 1) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4532) := by
    have ha : (tripleCharges (sourceA1296 + difference 1 2) (sourceB1296 + difference 2 1) sourceC1296) = raw20846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20846; decide +kernel
    rw [ha]
    exact (canonical20846 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1296 + difference 1 3) (sourceB1296 + difference 3 1) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4543) := by
    have ha : (tripleCharges (sourceA1296 + difference 1 3) (sourceB1296 + difference 3 1) sourceC1296) = raw20847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20847; decide +kernel
    rw [ha]
    exact (canonical20847 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1296 + difference 1 4) (sourceB1296 + difference 4 1) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1296 + difference 1 4) (sourceB1296 + difference 4 1) sourceC1296) = raw20848 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20848; decide +kernel
    rw [ha]
    exact (canonical20848 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1296 + difference 1 5) (sourceB1296 + difference 5 1) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA1296 + difference 1 5) (sourceB1296 + difference 5 1) sourceC1296) = raw10587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw10587; decide +kernel
    rw [ha]
    exact (canonical10587 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1296 + difference 2 0) (sourceB1296 + difference 0 2) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4157) := by
    have ha : (tripleCharges (sourceA1296 + difference 2 0) (sourceB1296 + difference 0 2) sourceC1296) = raw20849 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20849; decide +kernel
    rw [ha]
    exact (canonical20849 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1296 + difference 2 1) (sourceB1296 + difference 1 2) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4532) := by
    have ha : (tripleCharges (sourceA1296 + difference 2 1) (sourceB1296 + difference 1 2) sourceC1296) = raw20850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20850; decide +kernel
    rw [ha]
    exact (canonical20850 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1296 + difference 2 3) (sourceB1296 + difference 3 2) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4543) := by
    have ha : (tripleCharges (sourceA1296 + difference 2 3) (sourceB1296 + difference 3 2) sourceC1296) = raw20851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20851; decide +kernel
    rw [ha]
    exact (canonical20851 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1296 + difference 2 4) (sourceB1296 + difference 4 2) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1296 + difference 2 4) (sourceB1296 + difference 4 2) sourceC1296) = raw20852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20852; decide +kernel
    rw [ha]
    exact (canonical20852 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1296 + difference 2 5) (sourceB1296 + difference 5 2) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA1296 + difference 2 5) (sourceB1296 + difference 5 2) sourceC1296) = raw10592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw10592; decide +kernel
    rw [ha]
    exact (canonical10592 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1296 + difference 3 0) (sourceB1296 + difference 0 3) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4184) := by
    have ha : (tripleCharges (sourceA1296 + difference 3 0) (sourceB1296 + difference 0 3) sourceC1296) = raw20853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20853; decide +kernel
    rw [ha]
    exact (canonical20853 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1296 + difference 3 1) (sourceB1296 + difference 1 3) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4552) := by
    have ha : (tripleCharges (sourceA1296 + difference 3 1) (sourceB1296 + difference 1 3) sourceC1296) = raw20854 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20854; decide +kernel
    rw [ha]
    exact (canonical20854 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1296 + difference 3 2) (sourceB1296 + difference 2 3) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4552) := by
    have ha : (tripleCharges (sourceA1296 + difference 3 2) (sourceB1296 + difference 2 3) sourceC1296) = raw20855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20855; decide +kernel
    rw [ha]
    exact (canonical20855 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1296 + difference 3 4) (sourceB1296 + difference 4 3) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4621) := by
    have ha : (tripleCharges (sourceA1296 + difference 3 4) (sourceB1296 + difference 4 3) sourceC1296) = raw20856 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20856; decide +kernel
    rw [ha]
    exact (canonical20856 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1296 + difference 3 5) (sourceB1296 + difference 5 3) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA1296 + difference 3 5) (sourceB1296 + difference 5 3) sourceC1296) = raw10597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw10597; decide +kernel
    rw [ha]
    exact (canonical10597 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1296 + difference 4 0) (sourceB1296 + difference 0 4) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4162) := by
    have ha : (tripleCharges (sourceA1296 + difference 4 0) (sourceB1296 + difference 0 4) sourceC1296) = raw20857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20857; decide +kernel
    rw [ha]
    exact (canonical20857 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1296 + difference 4 1) (sourceB1296 + difference 1 4) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4536) := by
    have ha : (tripleCharges (sourceA1296 + difference 4 1) (sourceB1296 + difference 1 4) sourceC1296) = raw20858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20858; decide +kernel
    rw [ha]
    exact (canonical20858 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1296 + difference 4 2) (sourceB1296 + difference 2 4) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4536) := by
    have ha : (tripleCharges (sourceA1296 + difference 4 2) (sourceB1296 + difference 2 4) sourceC1296) = raw20859 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20859; decide +kernel
    rw [ha]
    exact (canonical20859 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1296 + difference 4 3) (sourceB1296 + difference 3 4) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4557) := by
    have ha : (tripleCharges (sourceA1296 + difference 4 3) (sourceB1296 + difference 3 4) sourceC1296) = raw20860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20860; decide +kernel
    rw [ha]
    exact (canonical20860 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1296 + difference 4 5) (sourceB1296 + difference 5 4) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA1296 + difference 4 5) (sourceB1296 + difference 5 4) sourceC1296) = raw10602 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw10602; decide +kernel
    rw [ha]
    exact (canonical10602 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1296 + difference 5 0) (sourceB1296 + difference 0 5) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4159) := by
    have ha : (tripleCharges (sourceA1296 + difference 5 0) (sourceB1296 + difference 0 5) sourceC1296) = raw20861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20861; decide +kernel
    rw [ha]
    exact (canonical20861 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1296 + difference 5 1) (sourceB1296 + difference 1 5) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1296 + difference 5 1) (sourceB1296 + difference 1 5) sourceC1296) = raw20862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20862; decide +kernel
    rw [ha]
    exact (canonical20862 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1296 + difference 5 2) (sourceB1296 + difference 2 5) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1296 + difference 5 2) (sourceB1296 + difference 2 5) sourceC1296) = raw20863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20863; decide +kernel
    rw [ha]
    exact (canonical20863 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1296 + difference 5 3) (sourceB1296 + difference 3 5) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1296 + difference 5 3) (sourceB1296 + difference 3 5) sourceC1296) = raw20864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20864; decide +kernel
    rw [ha]
    exact (canonical20864 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1296 + difference 5 4) (sourceB1296 + difference 4 5) sourceC1296) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1296 + difference 5 4) (sourceB1296 + difference 4 5) sourceC1296) = raw20865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1296 sourceB1296 sourceC1296 difference raw20865; decide +kernel
    rw [ha]
    exact (canonical20865 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1296 sourceB1296 sourceC1296
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1296, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1298 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1298 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1298 + difference 0 1) (sourceB1298 + difference 1 0) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1298 + difference 0 1) (sourceB1298 + difference 1 0) sourceC1298) = raw10668 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw10668; decide +kernel
    rw [ha]
    exact (canonical10668 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1298 + difference 0 2) (sourceB1298 + difference 2 0) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1298 + difference 0 2) (sourceB1298 + difference 2 0) sourceC1298) = raw10669 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw10669; decide +kernel
    rw [ha]
    exact (canonical10669 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1298 + difference 0 3) (sourceB1298 + difference 3 0) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA1298 + difference 0 3) (sourceB1298 + difference 3 0) sourceC1298) = raw10670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw10670; decide +kernel
    rw [ha]
    exact (canonical10670 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1298 + difference 0 4) (sourceB1298 + difference 4 0) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA1298 + difference 0 4) (sourceB1298 + difference 4 0) sourceC1298) = raw10671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw10671; decide +kernel
    rw [ha]
    exact (canonical10671 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1298 + difference 0 5) (sourceB1298 + difference 5 0) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA1298 + difference 0 5) (sourceB1298 + difference 5 0) sourceC1298) = raw20888 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20888; decide +kernel
    rw [ha]
    exact (canonical20888 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1298 + difference 1 0) (sourceB1298 + difference 0 1) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1528) := by
    have ha : (tripleCharges (sourceA1298 + difference 1 0) (sourceB1298 + difference 0 1) sourceC1298) = raw20889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20889; decide +kernel
    rw [ha]
    exact (canonical20889 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1298 + difference 1 2) (sourceB1298 + difference 2 1) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2172) := by
    have ha : (tripleCharges (sourceA1298 + difference 1 2) (sourceB1298 + difference 2 1) sourceC1298) = raw20890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20890; decide +kernel
    rw [ha]
    exact (canonical20890 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1298 + difference 1 3) (sourceB1298 + difference 3 1) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2184) := by
    have ha : (tripleCharges (sourceA1298 + difference 1 3) (sourceB1298 + difference 3 1) sourceC1298) = raw20891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20891; decide +kernel
    rw [ha]
    exact (canonical20891 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1298 + difference 1 4) (sourceB1298 + difference 4 1) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1298 + difference 1 4) (sourceB1298 + difference 4 1) sourceC1298) = raw20892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20892; decide +kernel
    rw [ha]
    exact (canonical20892 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1298 + difference 1 5) (sourceB1298 + difference 5 1) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1298 + difference 1 5) (sourceB1298 + difference 5 1) sourceC1298) = raw10647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw10647; decide +kernel
    rw [ha]
    exact (canonical10647 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1298 + difference 2 0) (sourceB1298 + difference 0 2) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1528) := by
    have ha : (tripleCharges (sourceA1298 + difference 2 0) (sourceB1298 + difference 0 2) sourceC1298) = raw20893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20893; decide +kernel
    rw [ha]
    exact (canonical20893 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1298 + difference 2 1) (sourceB1298 + difference 1 2) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2172) := by
    have ha : (tripleCharges (sourceA1298 + difference 2 1) (sourceB1298 + difference 1 2) sourceC1298) = raw20894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20894; decide +kernel
    rw [ha]
    exact (canonical20894 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1298 + difference 2 3) (sourceB1298 + difference 3 2) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2184) := by
    have ha : (tripleCharges (sourceA1298 + difference 2 3) (sourceB1298 + difference 3 2) sourceC1298) = raw20895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20895; decide +kernel
    rw [ha]
    exact (canonical20895 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1298 + difference 2 4) (sourceB1298 + difference 4 2) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1298 + difference 2 4) (sourceB1298 + difference 4 2) sourceC1298) = raw20896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20896; decide +kernel
    rw [ha]
    exact (canonical20896 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1298 + difference 2 5) (sourceB1298 + difference 5 2) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1298 + difference 2 5) (sourceB1298 + difference 5 2) sourceC1298) = raw10652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw10652; decide +kernel
    rw [ha]
    exact (canonical10652 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1298 + difference 3 0) (sourceB1298 + difference 0 3) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1530) := by
    have ha : (tripleCharges (sourceA1298 + difference 3 0) (sourceB1298 + difference 0 3) sourceC1298) = raw20897 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20897; decide +kernel
    rw [ha]
    exact (canonical20897 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1298 + difference 3 1) (sourceB1298 + difference 1 3) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA1298 + difference 3 1) (sourceB1298 + difference 1 3) sourceC1298) = raw20898 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20898; decide +kernel
    rw [ha]
    exact (canonical20898 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1298 + difference 3 2) (sourceB1298 + difference 2 3) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA1298 + difference 3 2) (sourceB1298 + difference 2 3) sourceC1298) = raw20899 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20899; decide +kernel
    rw [ha]
    exact (canonical20899 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1298 + difference 3 4) (sourceB1298 + difference 4 3) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2289) := by
    have ha : (tripleCharges (sourceA1298 + difference 3 4) (sourceB1298 + difference 4 3) sourceC1298) = raw20900 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20900; decide +kernel
    rw [ha]
    exact (canonical20900 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1298 + difference 3 5) (sourceB1298 + difference 5 3) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1298 + difference 3 5) (sourceB1298 + difference 5 3) sourceC1298) = raw10657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw10657; decide +kernel
    rw [ha]
    exact (canonical10657 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1298 + difference 4 0) (sourceB1298 + difference 0 4) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1529) := by
    have ha : (tripleCharges (sourceA1298 + difference 4 0) (sourceB1298 + difference 0 4) sourceC1298) = raw20901 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20901; decide +kernel
    rw [ha]
    exact (canonical20901 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1298 + difference 4 1) (sourceB1298 + difference 1 4) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2149) := by
    have ha : (tripleCharges (sourceA1298 + difference 4 1) (sourceB1298 + difference 1 4) sourceC1298) = raw20902 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20902; decide +kernel
    rw [ha]
    exact (canonical20902 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1298 + difference 4 2) (sourceB1298 + difference 2 4) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2149) := by
    have ha : (tripleCharges (sourceA1298 + difference 4 2) (sourceB1298 + difference 2 4) sourceC1298) = raw20903 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20903; decide +kernel
    rw [ha]
    exact (canonical20903 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1298 + difference 4 3) (sourceB1298 + difference 3 4) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2167) := by
    have ha : (tripleCharges (sourceA1298 + difference 4 3) (sourceB1298 + difference 3 4) sourceC1298) = raw20904 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20904; decide +kernel
    rw [ha]
    exact (canonical20904 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1298 + difference 4 5) (sourceB1298 + difference 5 4) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA1298 + difference 4 5) (sourceB1298 + difference 5 4) sourceC1298) = raw10662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw10662; decide +kernel
    rw [ha]
    exact (canonical10662 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1298 + difference 5 0) (sourceB1298 + difference 0 5) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1532) := by
    have ha : (tripleCharges (sourceA1298 + difference 5 0) (sourceB1298 + difference 0 5) sourceC1298) = raw20905 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20905; decide +kernel
    rw [ha]
    exact (canonical20905 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1298 + difference 5 1) (sourceB1298 + difference 1 5) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1298 + difference 5 1) (sourceB1298 + difference 1 5) sourceC1298) = raw20906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20906; decide +kernel
    rw [ha]
    exact (canonical20906 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1298 + difference 5 2) (sourceB1298 + difference 2 5) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1298 + difference 5 2) (sourceB1298 + difference 2 5) sourceC1298) = raw20907 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20907; decide +kernel
    rw [ha]
    exact (canonical20907 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1298 + difference 5 3) (sourceB1298 + difference 3 5) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA1298 + difference 5 3) (sourceB1298 + difference 3 5) sourceC1298) = raw20908 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20908; decide +kernel
    rw [ha]
    exact (canonical20908 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1298 + difference 5 4) (sourceB1298 + difference 4 5) sourceC1298) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1298 + difference 5 4) (sourceB1298 + difference 4 5) sourceC1298) = raw20909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1298 sourceB1298 sourceC1298 difference raw20909; decide +kernel
    rw [ha]
    exact (canonical20909 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1298 sourceB1298 sourceC1298
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1298, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1299 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1299 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1299 + difference 0 0) (sourceB1299 + difference 0 0) sourceC1299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1299 + difference 0 0) (sourceB1299 + difference 0 0) sourceC1299) = raw20910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1299 sourceB1299 sourceC1299 difference raw20910; decide +kernel
    rw [ha]
    exact (canonical20910 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1299 + difference 1 0) (sourceB1299 + difference 0 1) sourceC1299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 624) := by
    have ha : (tripleCharges (sourceA1299 + difference 1 0) (sourceB1299 + difference 0 1) sourceC1299) = raw20911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1299 sourceB1299 sourceC1299 difference raw20911; decide +kernel
    rw [ha]
    exact (canonical20911 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1299 + difference 2 0) (sourceB1299 + difference 0 2) sourceC1299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 624) := by
    have ha : (tripleCharges (sourceA1299 + difference 2 0) (sourceB1299 + difference 0 2) sourceC1299) = raw20912 := by
      apply Matrix.ext; unfold tripleCharges sourceA1299 sourceB1299 sourceC1299 difference raw20912; decide +kernel
    rw [ha]
    exact (canonical20912 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1299 + difference 3 0) (sourceB1299 + difference 0 3) sourceC1299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 639) := by
    have ha : (tripleCharges (sourceA1299 + difference 3 0) (sourceB1299 + difference 0 3) sourceC1299) = raw20913 := by
      apply Matrix.ext; unfold tripleCharges sourceA1299 sourceB1299 sourceC1299 difference raw20913; decide +kernel
    rw [ha]
    exact (canonical20913 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1299 + difference 4 0) (sourceB1299 + difference 0 4) sourceC1299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 634) := by
    have ha : (tripleCharges (sourceA1299 + difference 4 0) (sourceB1299 + difference 0 4) sourceC1299) = raw20914 := by
      apply Matrix.ext; unfold tripleCharges sourceA1299 sourceB1299 sourceC1299 difference raw20914; decide +kernel
    rw [ha]
    exact (canonical20914 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1299 + difference 5 0) (sourceB1299 + difference 0 5) sourceC1299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 628) := by
    have ha : (tripleCharges (sourceA1299 + difference 5 0) (sourceB1299 + difference 0 5) sourceC1299) = raw20915 := by
      apply Matrix.ext; unfold tripleCharges sourceA1299 sourceB1299 sourceC1299 difference raw20915; decide +kernel
    rw [ha]
    exact (canonical20915 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1299 + sourceB1299) sourceC1299) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1299 + sourceB1299) sourceC1299) = raw20916 := by
      apply Matrix.ext; unfold doubleCharges sourceA1299 sourceB1299 sourceC1299 raw20916; decide +kernel
    rw [ha]
    exact (canonical20916 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1299 sourceB1299 sourceC1299
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1299, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1300 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1300 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1300 + difference 1 0) (sourceB1300 + difference 0 1) sourceC1300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 624) := by
    have ha : (tripleCharges (sourceA1300 + difference 1 0) (sourceB1300 + difference 0 1) sourceC1300) = raw20911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1300 sourceB1300 sourceC1300 difference raw20911; decide +kernel
    rw [ha]
    exact (canonical20911 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1300 + difference 1 1) (sourceB1300 + difference 1 1) sourceC1300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1300 + difference 1 1) (sourceB1300 + difference 1 1) sourceC1300) = raw20910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1300 sourceB1300 sourceC1300 difference raw20910; decide +kernel
    rw [ha]
    exact (canonical20910 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1300 + difference 1 2) (sourceB1300 + difference 2 1) sourceC1300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1147) := by
    have ha : (tripleCharges (sourceA1300 + difference 1 2) (sourceB1300 + difference 2 1) sourceC1300) = raw20917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1300 sourceB1300 sourceC1300 difference raw20917; decide +kernel
    rw [ha]
    exact (canonical20917 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1300 + difference 1 3) (sourceB1300 + difference 3 1) sourceC1300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1128) := by
    have ha : (tripleCharges (sourceA1300 + difference 1 3) (sourceB1300 + difference 3 1) sourceC1300) = raw20918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1300 sourceB1300 sourceC1300 difference raw20918; decide +kernel
    rw [ha]
    exact (canonical20918 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1300 + difference 1 4) (sourceB1300 + difference 4 1) sourceC1300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1300 + difference 1 4) (sourceB1300 + difference 4 1) sourceC1300) = raw20919 := by
      apply Matrix.ext; unfold tripleCharges sourceA1300 sourceB1300 sourceC1300 difference raw20919; decide +kernel
    rw [ha]
    exact (canonical20919 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1300 + difference 1 5) (sourceB1300 + difference 5 1) sourceC1300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1234) := by
    have ha : (tripleCharges (sourceA1300 + difference 1 5) (sourceB1300 + difference 5 1) sourceC1300) = raw20920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1300 sourceB1300 sourceC1300 difference raw20920; decide +kernel
    rw [ha]
    exact (canonical20920 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1300 + sourceB1300) sourceC1300) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1300 + sourceB1300) sourceC1300) = raw20916 := by
      apply Matrix.ext; unfold doubleCharges sourceA1300 sourceB1300 sourceC1300 raw20916; decide +kernel
    rw [ha]
    exact (canonical20916 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1300 sourceB1300 sourceC1300
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1300, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1301 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1301 + difference 0 1) (sourceB1301 + difference 1 0) sourceC1301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA1301 + difference 0 1) (sourceB1301 + difference 1 0) sourceC1301) = raw20921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1301 sourceB1301 sourceC1301 difference raw20921; decide +kernel
    rw [ha]
    exact (canonical20921 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1301 + difference 1 1) (sourceB1301 + difference 1 1) sourceC1301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1301 + difference 1 1) (sourceB1301 + difference 1 1) sourceC1301) = raw20910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1301 sourceB1301 sourceC1301 difference raw20910; decide +kernel
    rw [ha]
    exact (canonical20910 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1301 + difference 2 1) (sourceB1301 + difference 1 2) sourceC1301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1147) := by
    have ha : (tripleCharges (sourceA1301 + difference 2 1) (sourceB1301 + difference 1 2) sourceC1301) = raw20922 := by
      apply Matrix.ext; unfold tripleCharges sourceA1301 sourceB1301 sourceC1301 difference raw20922; decide +kernel
    rw [ha]
    exact (canonical20922 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1301 + difference 3 1) (sourceB1301 + difference 1 3) sourceC1301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1157) := by
    have ha : (tripleCharges (sourceA1301 + difference 3 1) (sourceB1301 + difference 1 3) sourceC1301) = raw20923 := by
      apply Matrix.ext; unfold tripleCharges sourceA1301 sourceB1301 sourceC1301 difference raw20923; decide +kernel
    rw [ha]
    exact (canonical20923 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1301 + difference 4 1) (sourceB1301 + difference 1 4) sourceC1301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1153) := by
    have ha : (tripleCharges (sourceA1301 + difference 4 1) (sourceB1301 + difference 1 4) sourceC1301) = raw20924 := by
      apply Matrix.ext; unfold tripleCharges sourceA1301 sourceB1301 sourceC1301 difference raw20924; decide +kernel
    rw [ha]
    exact (canonical20924 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1301 + difference 5 1) (sourceB1301 + difference 1 5) sourceC1301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 908) := by
    have ha : (tripleCharges (sourceA1301 + difference 5 1) (sourceB1301 + difference 1 5) sourceC1301) = raw20925 := by
      apply Matrix.ext; unfold tripleCharges sourceA1301 sourceB1301 sourceC1301 difference raw20925; decide +kernel
    rw [ha]
    exact (canonical20925 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1301 + sourceB1301) sourceC1301) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1301 + sourceB1301) sourceC1301) = raw20916 := by
      apply Matrix.ext; unfold doubleCharges sourceA1301 sourceB1301 sourceC1301 raw20916; decide +kernel
    rw [ha]
    exact (canonical20916 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1301 sourceB1301 sourceC1301
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1301, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1302 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1302 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1302 + difference 0 3) (sourceB1302 + difference 3 0) sourceC1302) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2060) := by
    have ha : (tripleCharges (sourceA1302 + difference 0 3) (sourceB1302 + difference 3 0) sourceC1302) = raw20926 := by
      apply Matrix.ext; unfold tripleCharges sourceA1302 sourceB1302 sourceC1302 difference raw20926; decide +kernel
    rw [ha]
    exact (canonical20926 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1302 + difference 1 3) (sourceB1302 + difference 3 1) sourceC1302) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1128) := by
    have ha : (tripleCharges (sourceA1302 + difference 1 3) (sourceB1302 + difference 3 1) sourceC1302) = raw20918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1302 sourceB1302 sourceC1302 difference raw20918; decide +kernel
    rw [ha]
    exact (canonical20918 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1302 + difference 2 3) (sourceB1302 + difference 3 2) sourceC1302) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1128) := by
    have ha : (tripleCharges (sourceA1302 + difference 2 3) (sourceB1302 + difference 3 2) sourceC1302) = raw20927 := by
      apply Matrix.ext; unfold tripleCharges sourceA1302 sourceB1302 sourceC1302 difference raw20927; decide +kernel
    rw [ha]
    exact (canonical20927 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1302 + difference 3 3) (sourceB1302 + difference 3 3) sourceC1302) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1302 + difference 3 3) (sourceB1302 + difference 3 3) sourceC1302) = raw20910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1302 sourceB1302 sourceC1302 difference raw20910; decide +kernel
    rw [ha]
    exact (canonical20910 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1302 + difference 4 3) (sourceB1302 + difference 3 4) sourceC1302) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1143) := by
    have ha : (tripleCharges (sourceA1302 + difference 4 3) (sourceB1302 + difference 3 4) sourceC1302) = raw20928 := by
      apply Matrix.ext; unfold tripleCharges sourceA1302 sourceB1302 sourceC1302 difference raw20928; decide +kernel
    rw [ha]
    exact (canonical20928 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1302 + difference 5 3) (sourceB1302 + difference 3 5) sourceC1302) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 934) := by
    have ha : (tripleCharges (sourceA1302 + difference 5 3) (sourceB1302 + difference 3 5) sourceC1302) = raw20929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1302 sourceB1302 sourceC1302 difference raw20929; decide +kernel
    rw [ha]
    exact (canonical20929 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1302 + sourceB1302) sourceC1302) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1302 + sourceB1302) sourceC1302) = raw20916 := by
      apply Matrix.ext; unfold doubleCharges sourceA1302 sourceB1302 sourceC1302 raw20916; decide +kernel
    rw [ha]
    exact (canonical20916 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1302 sourceB1302 sourceC1302
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1302, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1307 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1307 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1307 + difference 0 0) (sourceB1307 + difference 0 0) sourceC1307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1307 + difference 0 0) (sourceB1307 + difference 0 0) sourceC1307) = raw20994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1307 sourceB1307 sourceC1307 difference raw20994; decide +kernel
    rw [ha]
    exact (canonical20994 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1307 + difference 1 0) (sourceB1307 + difference 0 1) sourceC1307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1599) := by
    have ha : (tripleCharges (sourceA1307 + difference 1 0) (sourceB1307 + difference 0 1) sourceC1307) = raw20995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1307 sourceB1307 sourceC1307 difference raw20995; decide +kernel
    rw [ha]
    exact (canonical20995 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1307 + difference 2 0) (sourceB1307 + difference 0 2) sourceC1307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1599) := by
    have ha : (tripleCharges (sourceA1307 + difference 2 0) (sourceB1307 + difference 0 2) sourceC1307) = raw20996 := by
      apply Matrix.ext; unfold tripleCharges sourceA1307 sourceB1307 sourceC1307 difference raw20996; decide +kernel
    rw [ha]
    exact (canonical20996 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1307 + difference 3 0) (sourceB1307 + difference 0 3) sourceC1307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1307 + difference 3 0) (sourceB1307 + difference 0 3) sourceC1307) = raw20480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1307 sourceB1307 sourceC1307 difference raw20480; decide +kernel
    rw [ha]
    exact (canonical20480 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1307 + difference 4 0) (sourceB1307 + difference 0 4) sourceC1307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1625) := by
    have ha : (tripleCharges (sourceA1307 + difference 4 0) (sourceB1307 + difference 0 4) sourceC1307) = raw20843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1307 sourceB1307 sourceC1307 difference raw20843; decide +kernel
    rw [ha]
    exact (canonical20843 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1307 + difference 5 0) (sourceB1307 + difference 0 5) sourceC1307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1002) := by
    have ha : (tripleCharges (sourceA1307 + difference 5 0) (sourceB1307 + difference 0 5) sourceC1307) = raw20997 := by
      apply Matrix.ext; unfold tripleCharges sourceA1307 sourceB1307 sourceC1307 difference raw20997; decide +kernel
    rw [ha]
    exact (canonical20997 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1307 + sourceB1307) sourceC1307) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1307 + sourceB1307) sourceC1307) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1307 sourceB1307 sourceC1307 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1307 sourceB1307 sourceC1307
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1307, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1308 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1308 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1308 + difference 0 0) (sourceB1308 + difference 0 0) sourceC1308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1231) := by
    have ha : (tripleCharges (sourceA1308 + difference 0 0) (sourceB1308 + difference 0 0) sourceC1308) = raw19864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1308 sourceB1308 sourceC1308 difference raw19864; decide +kernel
    rw [ha]
    exact (canonical19864 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1308 + difference 0 1) (sourceB1308 + difference 1 0) sourceC1308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1637) := by
    have ha : (tripleCharges (sourceA1308 + difference 0 1) (sourceB1308 + difference 1 0) sourceC1308) = raw20998 := by
      apply Matrix.ext; unfold tripleCharges sourceA1308 sourceB1308 sourceC1308 difference raw20998; decide +kernel
    rw [ha]
    exact (canonical20998 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1308 + difference 0 2) (sourceB1308 + difference 2 0) sourceC1308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1637) := by
    have ha : (tripleCharges (sourceA1308 + difference 0 2) (sourceB1308 + difference 2 0) sourceC1308) = raw20999 := by
      apply Matrix.ext; unfold tripleCharges sourceA1308 sourceB1308 sourceC1308 difference raw20999; decide +kernel
    rw [ha]
    exact (canonical20999 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1308 + difference 0 3) (sourceB1308 + difference 3 0) sourceC1308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1650) := by
    have ha : (tripleCharges (sourceA1308 + difference 0 3) (sourceB1308 + difference 3 0) sourceC1308) = raw21000 := by
      apply Matrix.ext; unfold tripleCharges sourceA1308 sourceB1308 sourceC1308 difference raw21000; decide +kernel
    rw [ha]
    exact (canonical21000 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1308 + difference 0 4) (sourceB1308 + difference 4 0) sourceC1308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1308 + difference 0 4) (sourceB1308 + difference 4 0) sourceC1308) = raw19855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1308 sourceB1308 sourceC1308 difference raw19855; decide +kernel
    rw [ha]
    exact (canonical19855 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1308 + difference 0 5) (sourceB1308 + difference 5 0) sourceC1308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1308 + difference 0 5) (sourceB1308 + difference 5 0) sourceC1308) = raw21001 := by
      apply Matrix.ext; unfold tripleCharges sourceA1308 sourceB1308 sourceC1308 difference raw21001; decide +kernel
    rw [ha]
    exact (canonical21001 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1308 + sourceB1308) sourceC1308) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1308 + sourceB1308) sourceC1308) = raw19856 := by
      apply Matrix.ext; unfold doubleCharges sourceA1308 sourceB1308 sourceC1308 raw19856; decide +kernel
    rw [ha]
    exact (canonical19856 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1308 sourceB1308 sourceC1308
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1308, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1309 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1309 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1309 + difference 0 0) (sourceB1309 + difference 0 0) sourceC1309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1191) := by
    have ha : (tripleCharges (sourceA1309 + difference 0 0) (sourceB1309 + difference 0 0) sourceC1309) = raw21002 := by
      apply Matrix.ext; unfold tripleCharges sourceA1309 sourceB1309 sourceC1309 difference raw21002; decide +kernel
    rw [ha]
    exact (canonical21002 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1309 + difference 0 1) (sourceB1309 + difference 1 0) sourceC1309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2391) := by
    have ha : (tripleCharges (sourceA1309 + difference 0 1) (sourceB1309 + difference 1 0) sourceC1309) = raw21003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1309 sourceB1309 sourceC1309 difference raw21003; decide +kernel
    rw [ha]
    exact (canonical21003 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1309 + difference 0 2) (sourceB1309 + difference 2 0) sourceC1309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2391) := by
    have ha : (tripleCharges (sourceA1309 + difference 0 2) (sourceB1309 + difference 2 0) sourceC1309) = raw21004 := by
      apply Matrix.ext; unfold tripleCharges sourceA1309 sourceB1309 sourceC1309 difference raw21004; decide +kernel
    rw [ha]
    exact (canonical21004 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1309 + difference 0 3) (sourceB1309 + difference 3 0) sourceC1309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2407) := by
    have ha : (tripleCharges (sourceA1309 + difference 0 3) (sourceB1309 + difference 3 0) sourceC1309) = raw21005 := by
      apply Matrix.ext; unfold tripleCharges sourceA1309 sourceB1309 sourceC1309 difference raw21005; decide +kernel
    rw [ha]
    exact (canonical21005 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1309 + difference 0 4) (sourceB1309 + difference 4 0) sourceC1309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2680) := by
    have ha : (tripleCharges (sourceA1309 + difference 0 4) (sourceB1309 + difference 4 0) sourceC1309) = raw21006 := by
      apply Matrix.ext; unfold tripleCharges sourceA1309 sourceB1309 sourceC1309 difference raw21006; decide +kernel
    rw [ha]
    exact (canonical21006 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1309 + difference 0 5) (sourceB1309 + difference 5 0) sourceC1309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA1309 + difference 0 5) (sourceB1309 + difference 5 0) sourceC1309) = raw21007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1309 sourceB1309 sourceC1309 difference raw21007; decide +kernel
    rw [ha]
    exact (canonical21007 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1309 + sourceB1309) sourceC1309) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA1309 + sourceB1309) sourceC1309) = raw21008 := by
      apply Matrix.ext; unfold doubleCharges sourceA1309 sourceB1309 sourceC1309 raw21008; decide +kernel
    rw [ha]
    exact (canonical21008 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1309 sourceB1309 sourceC1309
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1309, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1310 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1310 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1310 + difference 0 5) (sourceB1310 + difference 5 0) sourceC1310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA1310 + difference 0 5) (sourceB1310 + difference 5 0) sourceC1310) = raw21007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1310 sourceB1310 sourceC1310 difference raw21007; decide +kernel
    rw [ha]
    exact (canonical21007 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1310 + difference 1 5) (sourceB1310 + difference 5 1) sourceC1310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1185) := by
    have ha : (tripleCharges (sourceA1310 + difference 1 5) (sourceB1310 + difference 5 1) sourceC1310) = raw21009 := by
      apply Matrix.ext; unfold tripleCharges sourceA1310 sourceB1310 sourceC1310 difference raw21009; decide +kernel
    rw [ha]
    exact (canonical21009 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1310 + difference 2 5) (sourceB1310 + difference 5 2) sourceC1310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1185) := by
    have ha : (tripleCharges (sourceA1310 + difference 2 5) (sourceB1310 + difference 5 2) sourceC1310) = raw21010 := by
      apply Matrix.ext; unfold tripleCharges sourceA1310 sourceB1310 sourceC1310 difference raw21010; decide +kernel
    rw [ha]
    exact (canonical21010 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1310 + difference 3 5) (sourceB1310 + difference 5 3) sourceC1310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1288) := by
    have ha : (tripleCharges (sourceA1310 + difference 3 5) (sourceB1310 + difference 5 3) sourceC1310) = raw21011 := by
      apply Matrix.ext; unfold tripleCharges sourceA1310 sourceB1310 sourceC1310 difference raw21011; decide +kernel
    rw [ha]
    exact (canonical21011 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1310 + difference 4 5) (sourceB1310 + difference 5 4) sourceC1310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1193) := by
    have ha : (tripleCharges (sourceA1310 + difference 4 5) (sourceB1310 + difference 5 4) sourceC1310) = raw21012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1310 sourceB1310 sourceC1310 difference raw21012; decide +kernel
    rw [ha]
    exact (canonical21012 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1310 + difference 5 5) (sourceB1310 + difference 5 5) sourceC1310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1191) := by
    have ha : (tripleCharges (sourceA1310 + difference 5 5) (sourceB1310 + difference 5 5) sourceC1310) = raw21002 := by
      apply Matrix.ext; unfold tripleCharges sourceA1310 sourceB1310 sourceC1310 difference raw21002; decide +kernel
    rw [ha]
    exact (canonical21002 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1310 + sourceB1310) sourceC1310) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA1310 + sourceB1310) sourceC1310) = raw21008 := by
      apply Matrix.ext; unfold doubleCharges sourceA1310 sourceB1310 sourceC1310 raw21008; decide +kernel
    rw [ha]
    exact (canonical21008 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1310 sourceB1310 sourceC1310
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1310, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1122 : Integer.Sparse.reindex keyMap MixedData.row1122 = numericRow1122 := by decide +kernel

theorem numericCheck1122 (x : Master → ℝ) : Integer.Sparse.eval numericRow1122 x =
    (1 : ℝ) * reducedSource1122 x := by
  norm_num [numericRow1122, reducedSource1122, Integer.Sparse.eval, Sparse.eval, nodeValue1617, nodeValue1625, nodeValue1630, nodeValue1754, nodeValue3300, nodeValue4070]

theorem reindexCheck1123 : Integer.Sparse.reindex keyMap MixedData.row1123 = numericRow1123 := by decide +kernel

theorem numericCheck1123 (x : Master → ℝ) : Integer.Sparse.eval numericRow1123 x =
    (4 : ℝ) * reducedSource1123 x := by
  norm_num [numericRow1123, reducedSource1123, Integer.Sparse.eval, Sparse.eval, nodeValue4157, nodeValue4159, nodeValue4162, nodeValue4184, nodeValue4330, nodeValue4356, nodeValue4468, nodeValue4532, nodeValue4536, nodeValue4543, nodeValue4552, nodeValue4557, nodeValue4600, nodeValue4605, nodeValue4611, nodeValue4617, nodeValue4621, nodeValue4804, nodeValue4841, nodeValue4897, nodeValue5272]
  ring

theorem reindexCheck1125 : Integer.Sparse.reindex keyMap MixedData.row1125 = numericRow1125 := by decide +kernel

theorem numericCheck1125 (x : Master → ℝ) : Integer.Sparse.eval numericRow1125 x =
    (1 : ℝ) * reducedSource1125 x := by
  norm_num [numericRow1125, reducedSource1125, Integer.Sparse.eval, Sparse.eval, nodeValue1528, nodeValue1529, nodeValue1530, nodeValue1532, nodeValue1672, nodeValue1692, nodeValue1752, nodeValue2149, nodeValue2167, nodeValue2172, nodeValue2184, nodeValue2200, nodeValue2203, nodeValue2226, nodeValue2228, nodeValue2289, nodeValue2292, nodeValue2683, nodeValue2702, nodeValue2737, nodeValue2740]

theorem reindexCheck1126 : Integer.Sparse.reindex keyMap MixedData.row1126 = numericRow1126 := by decide +kernel

theorem numericCheck1126 (x : Master → ℝ) : Integer.Sparse.eval numericRow1126 x =
    (1 : ℝ) * reducedSource1126 x := by
  norm_num [numericRow1126, reducedSource1126, Integer.Sparse.eval, Sparse.eval, nodeValue624, nodeValue628, nodeValue634, nodeValue639, nodeValue1239, nodeValue4084]

theorem reindexCheck1127 : Integer.Sparse.reindex keyMap MixedData.row1127 = numericRow1127 := by decide +kernel

theorem numericCheck1127 (x : Master → ℝ) : Integer.Sparse.eval numericRow1127 x =
    (1 : ℝ) * reducedSource1127 x := by
  norm_num [numericRow1127, reducedSource1127, Integer.Sparse.eval, Sparse.eval, nodeValue624, nodeValue1128, nodeValue1147, nodeValue1234, nodeValue1239, nodeValue4084]

theorem reindexCheck1128 : Integer.Sparse.reindex keyMap MixedData.row1128 = numericRow1128 := by decide +kernel

theorem numericCheck1128 (x : Master → ℝ) : Integer.Sparse.eval numericRow1128 x =
    (1 : ℝ) * reducedSource1128 x := by
  norm_num [numericRow1128, reducedSource1128, Integer.Sparse.eval, Sparse.eval, nodeValue908, nodeValue1147, nodeValue1153, nodeValue1157, nodeValue1239, nodeValue2022, nodeValue4084]

theorem reindexCheck1129 : Integer.Sparse.reindex keyMap MixedData.row1129 = numericRow1129 := by decide +kernel

theorem numericCheck1129 (x : Master → ℝ) : Integer.Sparse.eval numericRow1129 x =
    (1 : ℝ) * reducedSource1129 x := by
  norm_num [numericRow1129, reducedSource1129, Integer.Sparse.eval, Sparse.eval, nodeValue934, nodeValue1128, nodeValue1143, nodeValue1239, nodeValue2060, nodeValue4084]

theorem reindexCheck1132 : Integer.Sparse.reindex keyMap MixedData.row1132 = numericRow1132 := by decide +kernel

theorem numericCheck1132 (x : Master → ℝ) : Integer.Sparse.eval numericRow1132 x =
    (1 : ℝ) * reducedSource1132 x := by
  norm_num [numericRow1132, reducedSource1132, Integer.Sparse.eval, Sparse.eval, nodeValue1002, nodeValue1599, nodeValue1625, nodeValue1730, nodeValue2226, nodeValue4070]

theorem reindexCheck1133 : Integer.Sparse.reindex keyMap MixedData.row1133 = numericRow1133 := by decide +kernel

theorem numericCheck1133 (x : Master → ℝ) : Integer.Sparse.eval numericRow1133 x =
    (1 : ℝ) * reducedSource1133 x := by
  norm_num [numericRow1133, reducedSource1133, Integer.Sparse.eval, Sparse.eval, nodeValue1231, nodeValue1637, nodeValue1650, nodeValue1710, nodeValue2737, nodeValue4069]

theorem reindexCheck1134 : Integer.Sparse.reindex keyMap MixedData.row1134 = numericRow1134 := by decide +kernel

theorem numericCheck1134 (x : Master → ℝ) : Integer.Sparse.eval numericRow1134 x =
    (1 : ℝ) * reducedSource1134 x := by
  norm_num [numericRow1134, reducedSource1134, Integer.Sparse.eval, Sparse.eval, nodeValue1191, nodeValue2391, nodeValue2407, nodeValue2680, nodeValue2686, nodeValue4089]

theorem reindexCheck1135 : Integer.Sparse.reindex keyMap MixedData.row1135 = numericRow1135 := by decide +kernel

theorem numericCheck1135 (x : Master → ℝ) : Integer.Sparse.eval numericRow1135 x =
    (1 : ℝ) * reducedSource1135 x := by
  norm_num [numericRow1135, reducedSource1135, Integer.Sparse.eval, Sparse.eval, nodeValue1185, nodeValue1191, nodeValue1193, nodeValue1288, nodeValue2686, nodeValue4089]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1122 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1122 (mixedVector B) = 0 := by
  have h1617 : mixedVector B (Sum.inr 1617) = Sparse.eval nodeValue1617 (mixedVector B) := by
    change mixedMoment B node1617 node1617Labels = _
    exact sound1617 B hB hF
  have h1625 : mixedVector B (Sum.inr 1625) = Sparse.eval nodeValue1625 (mixedVector B) := by
    change mixedMoment B node1625 node1625Labels = _
    exact sound1625 B hB hF
  have h1630 : mixedVector B (Sum.inr 1630) = Sparse.eval nodeValue1630 (mixedVector B) := by
    change mixedMoment B node1630 node1630Labels = _
    exact sound1630 B hB hF
  have h1754 : mixedVector B (Sum.inr 1754) = Sparse.eval nodeValue1754 (mixedVector B) := by
    change mixedMoment B node1754 node1754Labels = _
    exact sound1754 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1295, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1617, h1625, h1630, h1754, h3300, h4070, reducedSource1122] using sourceEq1295 B hB

theorem rowSound1122 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1122 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1122, numericCheck1122, reducedZero1122 B hB hF, mul_zero]

theorem reducedZero1123 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1123 (mixedVector B) = 0 := by
  have h4157 : mixedVector B (Sum.inr 4157) = Sparse.eval nodeValue4157 (mixedVector B) := by
    change mixedMoment B node4157 node4157Labels = _
    exact sound4157 B hB hF
  have h4159 : mixedVector B (Sum.inr 4159) = Sparse.eval nodeValue4159 (mixedVector B) := by
    change mixedMoment B node4159 node4159Labels = _
    exact sound4159 B hB hF
  have h4162 : mixedVector B (Sum.inr 4162) = Sparse.eval nodeValue4162 (mixedVector B) := by
    change mixedMoment B node4162 node4162Labels = _
    exact sound4162 B hB hF
  have h4184 : mixedVector B (Sum.inr 4184) = Sparse.eval nodeValue4184 (mixedVector B) := by
    change mixedMoment B node4184 node4184Labels = _
    exact sound4184 B hB hF
  have h4330 : mixedVector B (Sum.inr 4330) = Sparse.eval nodeValue4330 (mixedVector B) := by
    change mixedMoment B node4330 node4330Labels = _
    exact sound4330 B hB hF
  have h4356 : mixedVector B (Sum.inr 4356) = Sparse.eval nodeValue4356 (mixedVector B) := by
    change mixedMoment B node4356 node4356Labels = _
    exact sound4356 B hB hF
  have h4468 : mixedVector B (Sum.inr 4468) = Sparse.eval nodeValue4468 (mixedVector B) := by
    change mixedMoment B node4468 node4468Labels = _
    exact sound4468 B hB hF
  have h4532 : mixedVector B (Sum.inr 4532) = Sparse.eval nodeValue4532 (mixedVector B) := by
    change mixedMoment B node4532 node4532Labels = _
    exact sound4532 B hB hF
  have h4536 : mixedVector B (Sum.inr 4536) = Sparse.eval nodeValue4536 (mixedVector B) := by
    change mixedMoment B node4536 node4536Labels = _
    exact sound4536 B hB hF
  have h4543 : mixedVector B (Sum.inr 4543) = Sparse.eval nodeValue4543 (mixedVector B) := by
    change mixedMoment B node4543 node4543Labels = _
    exact sound4543 B hB hF
  have h4552 : mixedVector B (Sum.inr 4552) = Sparse.eval nodeValue4552 (mixedVector B) := by
    change mixedMoment B node4552 node4552Labels = _
    exact sound4552 B hB hF
  have h4557 : mixedVector B (Sum.inr 4557) = Sparse.eval nodeValue4557 (mixedVector B) := by
    change mixedMoment B node4557 node4557Labels = _
    exact sound4557 B hB hF
  have h4600 : mixedVector B (Sum.inr 4600) = Sparse.eval nodeValue4600 (mixedVector B) := by
    change mixedMoment B node4600 node4600Labels = _
    exact sound4600 B hB hF
  have h4605 : mixedVector B (Sum.inr 4605) = Sparse.eval nodeValue4605 (mixedVector B) := by
    change mixedMoment B node4605 node4605Labels = _
    exact sound4605 B hB hF
  have h4611 : mixedVector B (Sum.inr 4611) = Sparse.eval nodeValue4611 (mixedVector B) := by
    change mixedMoment B node4611 node4611Labels = _
    exact sound4611 B hB hF
  have h4617 : mixedVector B (Sum.inr 4617) = Sparse.eval nodeValue4617 (mixedVector B) := by
    change mixedMoment B node4617 node4617Labels = _
    exact sound4617 B hB hF
  have h4621 : mixedVector B (Sum.inr 4621) = Sparse.eval nodeValue4621 (mixedVector B) := by
    change mixedMoment B node4621 node4621Labels = _
    exact sound4621 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  have h5272 : mixedVector B (Sum.inr 5272) = Sparse.eval nodeValue5272 (mixedVector B) := by
    change mixedMoment B node5272 node5272Labels = _
    exact sound5272 B hB hF
  simpa only [sourceForm1296, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4157, h4159, h4162, h4184, h4330, h4356, h4468, h4532, h4536, h4543, h4552, h4557, h4600, h4605, h4611, h4617, h4621, h4804, h4841, h4897, h5272, reducedSource1123] using sourceEq1296 B hB

theorem rowSound1123 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1123 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1123, numericCheck1123, reducedZero1123 B hB hF, mul_zero]

theorem reducedZero1125 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1125 (mixedVector B) = 0 := by
  have h1528 : mixedVector B (Sum.inr 1528) = Sparse.eval nodeValue1528 (mixedVector B) := by
    change mixedMoment B node1528 node1528Labels = _
    exact sound1528 B hB hF
  have h1529 : mixedVector B (Sum.inr 1529) = Sparse.eval nodeValue1529 (mixedVector B) := by
    change mixedMoment B node1529 node1529Labels = _
    exact sound1529 B hB hF
  have h1530 : mixedVector B (Sum.inr 1530) = Sparse.eval nodeValue1530 (mixedVector B) := by
    change mixedMoment B node1530 node1530Labels = _
    exact sound1530 B hB hF
  have h1532 : mixedVector B (Sum.inr 1532) = Sparse.eval nodeValue1532 (mixedVector B) := by
    change mixedMoment B node1532 node1532Labels = _
    exact sound1532 B hB hF
  have h1672 : mixedVector B (Sum.inr 1672) = Sparse.eval nodeValue1672 (mixedVector B) := by
    change mixedMoment B node1672 node1672Labels = _
    exact sound1672 B hB hF
  have h1692 : mixedVector B (Sum.inr 1692) = Sparse.eval nodeValue1692 (mixedVector B) := by
    change mixedMoment B node1692 node1692Labels = _
    exact sound1692 B hB hF
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h2149 : mixedVector B (Sum.inr 2149) = Sparse.eval nodeValue2149 (mixedVector B) := by
    change mixedMoment B node2149 node2149Labels = _
    exact sound2149 B hB hF
  have h2167 : mixedVector B (Sum.inr 2167) = Sparse.eval nodeValue2167 (mixedVector B) := by
    change mixedMoment B node2167 node2167Labels = _
    exact sound2167 B hB hF
  have h2172 : mixedVector B (Sum.inr 2172) = Sparse.eval nodeValue2172 (mixedVector B) := by
    change mixedMoment B node2172 node2172Labels = _
    exact sound2172 B hB hF
  have h2184 : mixedVector B (Sum.inr 2184) = Sparse.eval nodeValue2184 (mixedVector B) := by
    change mixedMoment B node2184 node2184Labels = _
    exact sound2184 B hB hF
  have h2200 : mixedVector B (Sum.inr 2200) = Sparse.eval nodeValue2200 (mixedVector B) := by
    change mixedMoment B node2200 node2200Labels = _
    exact sound2200 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h2228 : mixedVector B (Sum.inr 2228) = Sparse.eval nodeValue2228 (mixedVector B) := by
    change mixedMoment B node2228 node2228Labels = _
    exact sound2228 B hB hF
  have h2289 : mixedVector B (Sum.inr 2289) = Sparse.eval nodeValue2289 (mixedVector B) := by
    change mixedMoment B node2289 node2289Labels = _
    exact sound2289 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h2683 : mixedVector B (Sum.inr 2683) = Sparse.eval nodeValue2683 (mixedVector B) := by
    change mixedMoment B node2683 node2683Labels = _
    exact sound2683 B hB hF
  have h2702 : mixedVector B (Sum.inr 2702) = Sparse.eval nodeValue2702 (mixedVector B) := by
    change mixedMoment B node2702 node2702Labels = _
    exact sound2702 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  simpa only [sourceForm1298, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1528, h1529, h1530, h1532, h1672, h1692, h1752, h2149, h2167, h2172, h2184, h2200, h2203, h2226, h2228, h2289, h2292, h2683, h2702, h2737, h2740, reducedSource1125] using sourceEq1298 B hB

theorem rowSound1125 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1125 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1125, numericCheck1125, reducedZero1125 B hB hF, mul_zero]

theorem reducedZero1126 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1126 (mixedVector B) = 0 := by
  have h624 : mixedVector B (Sum.inr 624) = Sparse.eval nodeValue624 (mixedVector B) := by
    change mixedMoment B node624 node624Labels = _
    exact sound624 B hB hF
  have h628 : mixedVector B (Sum.inr 628) = Sparse.eval nodeValue628 (mixedVector B) := by
    change mixedMoment B node628 node628Labels = _
    exact sound628 B hB hF
  have h634 : mixedVector B (Sum.inr 634) = Sparse.eval nodeValue634 (mixedVector B) := by
    change mixedMoment B node634 node634Labels = _
    exact sound634 B hB hF
  have h639 : mixedVector B (Sum.inr 639) = Sparse.eval nodeValue639 (mixedVector B) := by
    change mixedMoment B node639 node639Labels = _
    exact sound639 B hB hF
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1299, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h624, h628, h634, h639, h1239, h4084, reducedSource1126] using sourceEq1299 B hB

theorem rowSound1126 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1126 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1126, numericCheck1126, reducedZero1126 B hB hF, mul_zero]

theorem reducedZero1127 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1127 (mixedVector B) = 0 := by
  have h624 : mixedVector B (Sum.inr 624) = Sparse.eval nodeValue624 (mixedVector B) := by
    change mixedMoment B node624 node624Labels = _
    exact sound624 B hB hF
  have h1128 : mixedVector B (Sum.inr 1128) = Sparse.eval nodeValue1128 (mixedVector B) := by
    change mixedMoment B node1128 node1128Labels = _
    exact sound1128 B hB hF
  have h1147 : mixedVector B (Sum.inr 1147) = Sparse.eval nodeValue1147 (mixedVector B) := by
    change mixedMoment B node1147 node1147Labels = _
    exact sound1147 B hB hF
  have h1234 : mixedVector B (Sum.inr 1234) = Sparse.eval nodeValue1234 (mixedVector B) := by
    change mixedMoment B node1234 node1234Labels = _
    exact sound1234 B hB hF
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1300, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h624, h1128, h1147, h1234, h1239, h4084, reducedSource1127] using sourceEq1300 B hB

theorem rowSound1127 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1127 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1127, numericCheck1127, reducedZero1127 B hB hF, mul_zero]

theorem reducedZero1128 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1128 (mixedVector B) = 0 := by
  have h908 : mixedVector B (Sum.inr 908) = Sparse.eval nodeValue908 (mixedVector B) := by
    change mixedMoment B node908 node908Labels = _
    exact sound908 B hB hF
  have h1147 : mixedVector B (Sum.inr 1147) = Sparse.eval nodeValue1147 (mixedVector B) := by
    change mixedMoment B node1147 node1147Labels = _
    exact sound1147 B hB hF
  have h1153 : mixedVector B (Sum.inr 1153) = Sparse.eval nodeValue1153 (mixedVector B) := by
    change mixedMoment B node1153 node1153Labels = _
    exact sound1153 B hB hF
  have h1157 : mixedVector B (Sum.inr 1157) = Sparse.eval nodeValue1157 (mixedVector B) := by
    change mixedMoment B node1157 node1157Labels = _
    exact sound1157 B hB hF
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h2022 : mixedVector B (Sum.inr 2022) = Sparse.eval nodeValue2022 (mixedVector B) := by
    change mixedMoment B node2022 node2022Labels = _
    exact sound2022 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1301, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h908, h1147, h1153, h1157, h1239, h2022, h4084, reducedSource1128] using sourceEq1301 B hB

theorem rowSound1128 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1128 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1128, numericCheck1128, reducedZero1128 B hB hF, mul_zero]

theorem reducedZero1129 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1129 (mixedVector B) = 0 := by
  have h934 : mixedVector B (Sum.inr 934) = Sparse.eval nodeValue934 (mixedVector B) := by
    change mixedMoment B node934 node934Labels = _
    exact sound934 B hB hF
  have h1128 : mixedVector B (Sum.inr 1128) = Sparse.eval nodeValue1128 (mixedVector B) := by
    change mixedMoment B node1128 node1128Labels = _
    exact sound1128 B hB hF
  have h1143 : mixedVector B (Sum.inr 1143) = Sparse.eval nodeValue1143 (mixedVector B) := by
    change mixedMoment B node1143 node1143Labels = _
    exact sound1143 B hB hF
  have h1239 : mixedVector B (Sum.inr 1239) = Sparse.eval nodeValue1239 (mixedVector B) := by
    change mixedMoment B node1239 node1239Labels = _
    exact sound1239 B hB hF
  have h2060 : mixedVector B (Sum.inr 2060) = Sparse.eval nodeValue2060 (mixedVector B) := by
    change mixedMoment B node2060 node2060Labels = _
    exact sound2060 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1302, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h934, h1128, h1143, h1239, h2060, h4084, reducedSource1129] using sourceEq1302 B hB

theorem rowSound1129 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1129 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1129, numericCheck1129, reducedZero1129 B hB hF, mul_zero]

theorem reducedZero1132 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1132 (mixedVector B) = 0 := by
  have h1002 : mixedVector B (Sum.inr 1002) = Sparse.eval nodeValue1002 (mixedVector B) := by
    change mixedMoment B node1002 node1002Labels = _
    exact sound1002 B hB hF
  have h1599 : mixedVector B (Sum.inr 1599) = Sparse.eval nodeValue1599 (mixedVector B) := by
    change mixedMoment B node1599 node1599Labels = _
    exact sound1599 B hB hF
  have h1625 : mixedVector B (Sum.inr 1625) = Sparse.eval nodeValue1625 (mixedVector B) := by
    change mixedMoment B node1625 node1625Labels = _
    exact sound1625 B hB hF
  have h1730 : mixedVector B (Sum.inr 1730) = Sparse.eval nodeValue1730 (mixedVector B) := by
    change mixedMoment B node1730 node1730Labels = _
    exact sound1730 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1307, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1002, h1599, h1625, h1730, h2226, h4070, reducedSource1132] using sourceEq1307 B hB

theorem rowSound1132 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1132 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1132, numericCheck1132, reducedZero1132 B hB hF, mul_zero]

theorem reducedZero1133 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1133 (mixedVector B) = 0 := by
  have h1231 : mixedVector B (Sum.inr 1231) = Sparse.eval nodeValue1231 (mixedVector B) := by
    change mixedMoment B node1231 node1231Labels = _
    exact sound1231 B hB hF
  have h1637 : mixedVector B (Sum.inr 1637) = Sparse.eval nodeValue1637 (mixedVector B) := by
    change mixedMoment B node1637 node1637Labels = _
    exact sound1637 B hB hF
  have h1650 : mixedVector B (Sum.inr 1650) = Sparse.eval nodeValue1650 (mixedVector B) := by
    change mixedMoment B node1650 node1650Labels = _
    exact sound1650 B hB hF
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1308, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1231, h1637, h1650, h1710, h2737, h4069, reducedSource1133] using sourceEq1308 B hB

theorem rowSound1133 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1133 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1133, numericCheck1133, reducedZero1133 B hB hF, mul_zero]

theorem reducedZero1134 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1134 (mixedVector B) = 0 := by
  have h1191 : mixedVector B (Sum.inr 1191) = Sparse.eval nodeValue1191 (mixedVector B) := by
    change mixedMoment B node1191 node1191Labels = _
    exact sound1191 B hB hF
  have h2391 : mixedVector B (Sum.inr 2391) = Sparse.eval nodeValue2391 (mixedVector B) := by
    change mixedMoment B node2391 node2391Labels = _
    exact sound2391 B hB hF
  have h2407 : mixedVector B (Sum.inr 2407) = Sparse.eval nodeValue2407 (mixedVector B) := by
    change mixedMoment B node2407 node2407Labels = _
    exact sound2407 B hB hF
  have h2680 : mixedVector B (Sum.inr 2680) = Sparse.eval nodeValue2680 (mixedVector B) := by
    change mixedMoment B node2680 node2680Labels = _
    exact sound2680 B hB hF
  have h2686 : mixedVector B (Sum.inr 2686) = Sparse.eval nodeValue2686 (mixedVector B) := by
    change mixedMoment B node2686 node2686Labels = _
    exact sound2686 B hB hF
  have h4089 : mixedVector B (Sum.inr 4089) = Sparse.eval nodeValue4089 (mixedVector B) := by
    change mixedMoment B node4089 node4089Labels = _
    exact sound4089 B hB hF
  simpa only [sourceForm1309, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1191, h2391, h2407, h2680, h2686, h4089, reducedSource1134] using sourceEq1309 B hB

theorem rowSound1134 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1134 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1134, numericCheck1134, reducedZero1134 B hB hF, mul_zero]

theorem reducedZero1135 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1135 (mixedVector B) = 0 := by
  have h1185 : mixedVector B (Sum.inr 1185) = Sparse.eval nodeValue1185 (mixedVector B) := by
    change mixedMoment B node1185 node1185Labels = _
    exact sound1185 B hB hF
  have h1191 : mixedVector B (Sum.inr 1191) = Sparse.eval nodeValue1191 (mixedVector B) := by
    change mixedMoment B node1191 node1191Labels = _
    exact sound1191 B hB hF
  have h1193 : mixedVector B (Sum.inr 1193) = Sparse.eval nodeValue1193 (mixedVector B) := by
    change mixedMoment B node1193 node1193Labels = _
    exact sound1193 B hB hF
  have h1288 : mixedVector B (Sum.inr 1288) = Sparse.eval nodeValue1288 (mixedVector B) := by
    change mixedMoment B node1288 node1288Labels = _
    exact sound1288 B hB hF
  have h2686 : mixedVector B (Sum.inr 2686) = Sparse.eval nodeValue2686 (mixedVector B) := by
    change mixedMoment B node2686 node2686Labels = _
    exact sound2686 B hB hF
  have h4089 : mixedVector B (Sum.inr 4089) = Sparse.eval nodeValue4089 (mixedVector B) := by
    change mixedMoment B node4089 node4089Labels = _
    exact sound4089 B hB hF
  simpa only [sourceForm1310, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1185, h1191, h1193, h1288, h2686, h4089, reducedSource1135] using sourceEq1310 B hB

theorem rowSound1135 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1135 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1135, numericCheck1135, reducedZero1135 B hB hF, mul_zero]

theorem sourceRowsAt1120 : MixedData.sourceRows (1120 : Fin 2425) =
    MixedData.row1120 := by decide +kernel

theorem sourceRowsAt1121 : MixedData.sourceRows (1121 : Fin 2425) =
    MixedData.row1121 := by decide +kernel

theorem sourceRowsAt1122 : MixedData.sourceRows (1122 : Fin 2425) =
    MixedData.row1122 := by decide +kernel

theorem sourceRowsAt1123 : MixedData.sourceRows (1123 : Fin 2425) =
    MixedData.row1123 := by decide +kernel

theorem sourceRowsAt1124 : MixedData.sourceRows (1124 : Fin 2425) =
    MixedData.row1124 := by decide +kernel

theorem sourceRowsAt1125 : MixedData.sourceRows (1125 : Fin 2425) =
    MixedData.row1125 := by decide +kernel

theorem sourceRowsAt1126 : MixedData.sourceRows (1126 : Fin 2425) =
    MixedData.row1126 := by decide +kernel

theorem sourceRowsAt1127 : MixedData.sourceRows (1127 : Fin 2425) =
    MixedData.row1127 := by decide +kernel

theorem sourceRowsAt1128 : MixedData.sourceRows (1128 : Fin 2425) =
    MixedData.row1128 := by decide +kernel

theorem sourceRowsAt1129 : MixedData.sourceRows (1129 : Fin 2425) =
    MixedData.row1129 := by decide +kernel

theorem sourceRowsAt1130 : MixedData.sourceRows (1130 : Fin 2425) =
    MixedData.row1130 := by decide +kernel

theorem sourceRowsAt1131 : MixedData.sourceRows (1131 : Fin 2425) =
    MixedData.row1131 := by decide +kernel

theorem sourceRowsAt1132 : MixedData.sourceRows (1132 : Fin 2425) =
    MixedData.row1132 := by decide +kernel

theorem sourceRowsAt1133 : MixedData.sourceRows (1133 : Fin 2425) =
    MixedData.row1133 := by decide +kernel

theorem sourceRowsAt1134 : MixedData.sourceRows (1134 : Fin 2425) =
    MixedData.row1134 := by decide +kernel

theorem sourceRowsAt1135 : MixedData.sourceRows (1135 : Fin 2425) =
    MixedData.row1135 := by decide +kernel

theorem chunkSound70_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 70) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1120 ∨ k.val = 1121 ∨ k.val = 1122 ∨ k.val = 1123 ∨ k.val = 1124 ∨ k.val = 1125 ∨ k.val = 1126 ∨ k.val = 1127 ∨ k.val = 1128 ∨ k.val = 1129 ∨ k.val = 1130 ∨ k.val = 1131 ∨ k.val = 1132 ∨ k.val = 1133 ∨ k.val = 1134 ∨ k.val = 1135 := by omega
  rcases heq with h1120 | h1121 | h1122 | h1123 | h1124 | h1125 | h1126 | h1127 | h1128 | h1129 | h1130 | h1131 | h1132 | h1133 | h1134 | h1135
  · have he : k = (1120 : Fin 2425) := Fin.ext h1120
    subst k
    rw [sourceRowsAt1120]
    exact rowSound1120_e B hB hF
  · have he : k = (1121 : Fin 2425) := Fin.ext h1121
    subst k
    rw [sourceRowsAt1121]
    exact rowSound1121_e B hB hF
  · have he : k = (1122 : Fin 2425) := Fin.ext h1122
    subst k
    rw [sourceRowsAt1122]
    exact rowSound1122 B hB hF
  · have he : k = (1123 : Fin 2425) := Fin.ext h1123
    subst k
    rw [sourceRowsAt1123]
    exact rowSound1123 B hB hF
  · have he : k = (1124 : Fin 2425) := Fin.ext h1124
    subst k
    rw [sourceRowsAt1124]
    exact rowSound1124_e B hB hF
  · have he : k = (1125 : Fin 2425) := Fin.ext h1125
    subst k
    rw [sourceRowsAt1125]
    exact rowSound1125 B hB hF
  · have he : k = (1126 : Fin 2425) := Fin.ext h1126
    subst k
    rw [sourceRowsAt1126]
    exact rowSound1126 B hB hF
  · have he : k = (1127 : Fin 2425) := Fin.ext h1127
    subst k
    rw [sourceRowsAt1127]
    exact rowSound1127 B hB hF
  · have he : k = (1128 : Fin 2425) := Fin.ext h1128
    subst k
    rw [sourceRowsAt1128]
    exact rowSound1128 B hB hF
  · have he : k = (1129 : Fin 2425) := Fin.ext h1129
    subst k
    rw [sourceRowsAt1129]
    exact rowSound1129 B hB hF
  · have he : k = (1130 : Fin 2425) := Fin.ext h1130
    subst k
    rw [sourceRowsAt1130]
    exact rowSound1130_e B hB hF
  · have he : k = (1131 : Fin 2425) := Fin.ext h1131
    subst k
    rw [sourceRowsAt1131]
    exact rowSound1131_e B hB hF
  · have he : k = (1132 : Fin 2425) := Fin.ext h1132
    subst k
    rw [sourceRowsAt1132]
    exact rowSound1132 B hB hF
  · have he : k = (1133 : Fin 2425) := Fin.ext h1133
    subst k
    rw [sourceRowsAt1133]
    exact rowSound1133 B hB hF
  · have he : k = (1134 : Fin 2425) := Fin.ext h1134
    subst k
    rw [sourceRowsAt1134]
    exact rowSound1134 B hB hF
  · have he : k = (1135 : Fin 2425) := Fin.ext h1135
    subst k
    rw [sourceRowsAt1135]
    exact rowSound1135 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound70_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound70_e_oai
