-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound39_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:14:16.52821+00:00
-- url     : https://prove2.me/submissions/853b570a-8b8c-4b13-bffc-6afcc5657a4e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5292_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound628_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound629_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound630_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound631_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound633_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound635_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound636_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem canonical1821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1821 raw1821Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw1821 raw1821Labels = mixedMoment B raw1821step0 raw1821step0Labels := by
      have ha : raw1821step0 = (fun i j => raw1821 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1821step0 raw1821; decide +kernel
      have hl : raw1821step0Labels = raw1821Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1821 raw1821Labels permutation8 permutation4
    mixedMoment B raw1821step0 raw1821step0Labels = mixedMoment B raw1821step1 raw1821step1Labels := by
      have ha : raw1821step1 = raw1821step0 := by apply Matrix.ext; unfold raw1821step1 raw1821step0; decide +kernel
      have hl : raw1821step0Labels = labelEmbedding7 ∘ raw1821step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1821step0 raw1821step0Labels raw1821step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical1822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1822 raw1822Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw1822 raw1822Labels = mixedMoment B raw1822step0 raw1822step0Labels := by
      have ha : raw1822step0 = (fun i j => raw1822 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1822step0 raw1822; decide +kernel
      have hl : raw1822step0Labels = raw1822Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1822 raw1822Labels permutation8 permutation4
    _ = mixedMoment B node2247 node2247Labels := by rfl

theorem canonical1823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1823 raw1823Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw1823 raw1823Labels = mixedMoment B raw1823step0 raw1823step0Labels := by
      have ha : raw1823step0 = (fun i j => raw1823 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1823step0 raw1823; decide +kernel
      have hl : raw1823step0Labels = raw1823Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1823 raw1823Labels permutation8 permutation6
    mixedMoment B raw1823step0 raw1823step0Labels = mixedMoment B raw1823step1 raw1823step1Labels := by
      have ha : raw1823step1 = -raw1823step0 := by apply Matrix.ext; change ∀ i j, raw1823step1 i j = -(raw1823step0 i j); unfold raw1823step1 raw1823step0; decide +kernel
      have hl : raw1823step1Labels = raw1823step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1823step1 raw1823step1Labels = mixedMoment B raw1823step2 raw1823step2Labels := by
      have ha : raw1823step2 = raw1823step1 := by apply Matrix.ext; unfold raw1823step2 raw1823step1; decide +kernel
      have hl : raw1823step1Labels = labelEmbedding1 ∘ raw1823step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1823step1 raw1823step1Labels raw1823step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2290 node2290Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2316 raw2316Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw2316 raw2316Labels = mixedMoment B raw2316step0 raw2316step0Labels := by
      have ha : raw2316step0 = (fun i j => raw2316 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2316step0 raw2316; decide +kernel
      have hl : raw2316step0Labels = raw2316Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2316 raw2316Labels permutation8 permutation4
    mixedMoment B raw2316step0 raw2316step0Labels = mixedMoment B raw2316step1 raw2316step1Labels := by
      have ha : raw2316step1 = raw2316step0 := by apply Matrix.ext; unfold raw2316step1 raw2316step0; decide +kernel
      have hl : raw2316step0Labels = labelEmbedding7 ∘ raw2316step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2316step0 raw2316step0Labels raw2316step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

theorem canonical2317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2317 raw2317Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw2317 raw2317Labels = mixedMoment B raw2317step0 raw2317step0Labels := by
      have ha : raw2317step0 = (fun i j => raw2317 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2317step0 raw2317; decide +kernel
      have hl : raw2317step0Labels = raw2317Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2317 raw2317Labels permutation8 permutation4
    _ = mixedMoment B node2782 node2782Labels := by rfl

theorem canonical2318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2318 raw2318Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw2318 raw2318Labels = mixedMoment B raw2318step0 raw2318step0Labels := by
      have ha : raw2318step0 = (fun i j => raw2318 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2318step0 raw2318; decide +kernel
      have hl : raw2318step0Labels = raw2318Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2318 raw2318Labels permutation8 permutation6
    mixedMoment B raw2318step0 raw2318step0Labels = mixedMoment B raw2318step1 raw2318step1Labels := by
      have ha : raw2318step1 = -raw2318step0 := by apply Matrix.ext; change ∀ i j, raw2318step1 i j = -(raw2318step0 i j); unfold raw2318step1 raw2318step0; decide +kernel
      have hl : raw2318step1Labels = raw2318step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2318step1 raw2318step1Labels = mixedMoment B raw2318step2 raw2318step2Labels := by
      have ha : raw2318step2 = raw2318step1 := by apply Matrix.ext; unfold raw2318step2 raw2318step1; decide +kernel
      have hl : raw2318step1Labels = labelEmbedding1 ∘ raw2318step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2318step1 raw2318step1Labels raw2318step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3583 node3583Labels := by rfl

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

theorem canonical11661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11661 raw11661Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw11661 raw11661Labels = mixedMoment B raw11661step0 raw11661step0Labels := by
      have hz : ∀ j, raw11661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11661step0 = (fun i j => raw11661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11661step0 raw11661; decide +kernel
      have hl : raw11661step0Labels = raw11661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11661 raw11661Labels permutation346 hz
    mixedMoment B raw11661step0 raw11661step0Labels = mixedMoment B raw11661step1 raw11661step1Labels := by
      have ha : raw11661step1 = (fun i j => raw11661step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11661step1 raw11661step0; decide +kernel
      have hl : raw11661step1Labels = raw11661step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11661step0 raw11661step0Labels permutation36 permutation7
    mixedMoment B raw11661step1 raw11661step1Labels = mixedMoment B raw11661step2 raw11661step2Labels := by
      have ha : raw11661step2 = raw11661step1 := by apply Matrix.ext; unfold raw11661step2 raw11661step1; decide +kernel
      have hl : raw11661step1Labels = labelEmbedding10 ∘ raw11661step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11661step1 raw11661step1Labels raw11661step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical11665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11665 raw11665Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw11665 raw11665Labels = mixedMoment B raw11665step0 raw11665step0Labels := by
      have hz : ∀ j, raw11665 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11665step0 = (fun i j => raw11665 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11665step0 raw11665; decide +kernel
      have hl : raw11665step0Labels = raw11665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11665 raw11665Labels permutation265 hz
    mixedMoment B raw11665step0 raw11665step0Labels = mixedMoment B raw11665step1 raw11665step1Labels := by
      have ha : raw11665step1 = (fun i j => raw11665step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11665step1 raw11665step0; decide +kernel
      have hl : raw11665step1Labels = raw11665step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11665step0 raw11665step0Labels permutation40 permutation4
    mixedMoment B raw11665step1 raw11665step1Labels = mixedMoment B raw11665step2 raw11665step2Labels := by
      have ha : raw11665step2 = -raw11665step1 := by apply Matrix.ext; change ∀ i j, raw11665step2 i j = -(raw11665step1 i j); unfold raw11665step2 raw11665step1; decide +kernel
      have hl : raw11665step2Labels = raw11665step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11665step2 raw11665step2Labels = mixedMoment B raw11665step3 raw11665step3Labels := by
      have ha : raw11665step3 = raw11665step2 := by apply Matrix.ext; unfold raw11665step3 raw11665step2; decide +kernel
      have hl : raw11665step2Labels = labelEmbedding7 ∘ raw11665step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11665step2 raw11665step2Labels raw11665step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical11667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11667 raw11667Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw11667 raw11667Labels = mixedMoment B raw11667step0 raw11667step0Labels := by
      have hz : ∀ j, raw11667 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11667step0 = (fun i j => raw11667 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11667step0 raw11667; decide +kernel
      have hl : raw11667step0Labels = raw11667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11667 raw11667Labels permutation265 hz
    mixedMoment B raw11667step0 raw11667step0Labels = mixedMoment B raw11667step1 raw11667step1Labels := by
      have ha : raw11667step1 = (fun i j => raw11667step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11667step1 raw11667step0; decide +kernel
      have hl : raw11667step1Labels = raw11667step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11667step0 raw11667step0Labels permutation32 permutation6
    mixedMoment B raw11667step1 raw11667step1Labels = mixedMoment B raw11667step2 raw11667step2Labels := by
      have ha : raw11667step2 = raw11667step1 := by apply Matrix.ext; unfold raw11667step2 raw11667step1; decide +kernel
      have hl : raw11667step1Labels = labelEmbedding9 ∘ raw11667step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11667step1 raw11667step1Labels raw11667step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

theorem canonical11668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11668 raw11668Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw11668 raw11668Labels = mixedMoment B raw11668step0 raw11668step0Labels := by
      have hz : ∀ j, raw11668 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11668step0 = (fun i j => raw11668 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11668step0 raw11668; decide +kernel
      have hl : raw11668step0Labels = raw11668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11668 raw11668Labels permutation265 hz
    mixedMoment B raw11668step0 raw11668step0Labels = mixedMoment B raw11668step1 raw11668step1Labels := by
      have ha : raw11668step1 = (fun i j => raw11668step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11668step1 raw11668step0; decide +kernel
      have hl : raw11668step1Labels = raw11668step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11668step0 raw11668step0Labels permutation34 permutation6
    mixedMoment B raw11668step1 raw11668step1Labels = mixedMoment B raw11668step2 raw11668step2Labels := by
      have ha : raw11668step2 = raw11668step1 := by apply Matrix.ext; unfold raw11668step2 raw11668step1; decide +kernel
      have hl : raw11668step1Labels = labelEmbedding9 ∘ raw11668step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11668step1 raw11668step1Labels raw11668step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

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

theorem canonical11677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11677 raw11677Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw11677 raw11677Labels = mixedMoment B raw11677step0 raw11677step0Labels := by
      have hz : ∀ j, raw11677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11677step0 = (fun i j => raw11677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11677step0 raw11677; decide +kernel
      have hl : raw11677step0Labels = raw11677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11677 raw11677Labels permutation346 hz
    mixedMoment B raw11677step0 raw11677step0Labels = mixedMoment B raw11677step1 raw11677step1Labels := by
      have ha : raw11677step1 = (fun i j => raw11677step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11677step1 raw11677step0; decide +kernel
      have hl : raw11677step1Labels = raw11677step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11677step0 raw11677step0Labels permutation34 permutation6
    mixedMoment B raw11677step1 raw11677step1Labels = mixedMoment B raw11677step2 raw11677step2Labels := by
      have ha : raw11677step2 = raw11677step1 := by apply Matrix.ext; unfold raw11677step2 raw11677step1; decide +kernel
      have hl : raw11677step1Labels = labelEmbedding9 ∘ raw11677step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11677step1 raw11677step1Labels raw11677step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical11682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11682 raw11682Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw11682 raw11682Labels = mixedMoment B raw11682step0 raw11682step0Labels := by
      have hz : ∀ j, raw11682 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11682step0 = (fun i j => raw11682 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11682step0 raw11682; decide +kernel
      have hl : raw11682step0Labels = raw11682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11682 raw11682Labels permutation346 hz
    mixedMoment B raw11682step0 raw11682step0Labels = mixedMoment B raw11682step1 raw11682step1Labels := by
      have ha : raw11682step1 = (fun i j => raw11682step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11682step1 raw11682step0; decide +kernel
      have hl : raw11682step1Labels = raw11682step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11682step0 raw11682step0Labels permutation32 permutation6
    mixedMoment B raw11682step1 raw11682step1Labels = mixedMoment B raw11682step2 raw11682step2Labels := by
      have ha : raw11682step2 = raw11682step1 := by apply Matrix.ext; unfold raw11682step2 raw11682step1; decide +kernel
      have hl : raw11682step1Labels = labelEmbedding9 ∘ raw11682step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11682step1 raw11682step1Labels raw11682step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical11687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11687 raw11687Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw11687 raw11687Labels = mixedMoment B raw11687step0 raw11687step0Labels := by
      have hz : ∀ j, raw11687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11687step0 = (fun i j => raw11687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11687step0 raw11687; decide +kernel
      have hl : raw11687step0Labels = raw11687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11687 raw11687Labels permutation346 hz
    mixedMoment B raw11687step0 raw11687step0Labels = mixedMoment B raw11687step1 raw11687step1Labels := by
      have ha : raw11687step1 = (fun i j => raw11687step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11687step1 raw11687step0; decide +kernel
      have hl : raw11687step1Labels = raw11687step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11687step0 raw11687step0Labels permutation32 permutation6
    mixedMoment B raw11687step1 raw11687step1Labels = mixedMoment B raw11687step2 raw11687step2Labels := by
      have ha : raw11687step2 = raw11687step1 := by apply Matrix.ext; unfold raw11687step2 raw11687step1; decide +kernel
      have hl : raw11687step1Labels = labelEmbedding9 ∘ raw11687step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11687step1 raw11687step1Labels raw11687step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

theorem canonical11752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11752 raw11752Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw11752 raw11752Labels = mixedMoment B raw11752step0 raw11752step0Labels := by
      have hz : ∀ j, raw11752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11752step0 = (fun i j => raw11752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11752step0 raw11752; decide +kernel
      have hl : raw11752step0Labels = raw11752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11752 raw11752Labels permutation346 hz
    mixedMoment B raw11752step0 raw11752step0Labels = mixedMoment B raw11752step1 raw11752step1Labels := by
      have ha : raw11752step1 = (fun i j => raw11752step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11752step1 raw11752step0; decide +kernel
      have hl : raw11752step1Labels = raw11752step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11752step0 raw11752step0Labels permutation50 permutation2
    mixedMoment B raw11752step1 raw11752step1Labels = mixedMoment B raw11752step2 raw11752step2Labels := by
      have ha : raw11752step2 = -raw11752step1 := by apply Matrix.ext; change ∀ i j, raw11752step2 i j = -(raw11752step1 i j); unfold raw11752step2 raw11752step1; decide +kernel
      have hl : raw11752step2Labels = raw11752step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3581 node3581Labels := by rfl

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

theorem canonical11757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11757 raw11757Labels = mixedMoment B node3373 node3373Labels := by
  calc
    mixedMoment B raw11757 raw11757Labels = mixedMoment B raw11757step0 raw11757step0Labels := by
      have ha : raw11757step0 = (fun i j => raw11757 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11757step0 raw11757; decide +kernel
      have hl : raw11757step0Labels = raw11757Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11757 raw11757Labels permutation160 permutation4
    mixedMoment B raw11757step0 raw11757step0Labels = mixedMoment B raw11757step1 raw11757step1Labels := by
      have ha : raw11757step1 = -raw11757step0 := by apply Matrix.ext; change ∀ i j, raw11757step1 i j = -(raw11757step0 i j); unfold raw11757step1 raw11757step0; decide +kernel
      have hl : raw11757step1Labels = raw11757step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3373 node3373Labels := by rfl

theorem canonical11762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11762 raw11762Labels = mixedMoment B node3500 node3500Labels := by
  calc
    mixedMoment B raw11762 raw11762Labels = mixedMoment B raw11762step0 raw11762step0Labels := by
      have ha : raw11762step0 = (fun i j => raw11762 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11762step0 raw11762; decide +kernel
      have hl : raw11762step0Labels = raw11762Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11762 raw11762Labels permutation160 permutation4
    mixedMoment B raw11762step0 raw11762step0Labels = mixedMoment B raw11762step1 raw11762step1Labels := by
      have ha : raw11762step1 = -raw11762step0 := by apply Matrix.ext; change ∀ i j, raw11762step1 i j = -(raw11762step0 i j); unfold raw11762step1 raw11762step0; decide +kernel
      have hl : raw11762step1Labels = raw11762step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3500 node3500Labels := by rfl

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

theorem canonical11768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11768 raw11768Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw11768 raw11768Labels = mixedMoment B raw11768step0 raw11768step0Labels := by
      have ha : raw11768step0 = (fun i j => raw11768 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11768step0 raw11768; decide +kernel
      have hl : raw11768step0Labels = raw11768Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11768 raw11768Labels permutation164 permutation4
    mixedMoment B raw11768step0 raw11768step0Labels = mixedMoment B raw11768step1 raw11768step1Labels := by
      have ha : raw11768step1 = -raw11768step0 := by apply Matrix.ext; change ∀ i j, raw11768step1 i j = -(raw11768step0 i j); unfold raw11768step1 raw11768step0; decide +kernel
      have hl : raw11768step1Labels = raw11768step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3532 node3532Labels := by rfl

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

theorem canonical12068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12068 raw12068Labels = mixedMoment B node3150 node3150Labels := by
  calc
    mixedMoment B raw12068 raw12068Labels = mixedMoment B raw12068step0 raw12068step0Labels := by
      have ha : raw12068step0 = (fun i j => raw12068 (permutation364 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12068step0 raw12068; decide +kernel
      have hl : raw12068step0Labels = raw12068Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12068 raw12068Labels permutation364 permutation2
    mixedMoment B raw12068step0 raw12068step0Labels = mixedMoment B raw12068step1 raw12068step1Labels := by
      have ha : raw12068step1 = -raw12068step0 := by apply Matrix.ext; change ∀ i j, raw12068step1 i j = -(raw12068step0 i j); unfold raw12068step1 raw12068step0; decide +kernel
      have hl : raw12068step1Labels = raw12068step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3150 node3150Labels := by rfl

theorem canonical12069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12069 raw12069Labels = mixedMoment B node3378 node3378Labels := by
  calc
    mixedMoment B raw12069 raw12069Labels = mixedMoment B raw12069step0 raw12069step0Labels := by
      have ha : raw12069step0 = (fun i j => raw12069 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12069step0 raw12069; decide +kernel
      have hl : raw12069step0Labels = raw12069Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12069 raw12069Labels permutation167 permutation4
    mixedMoment B raw12069step0 raw12069step0Labels = mixedMoment B raw12069step1 raw12069step1Labels := by
      have ha : raw12069step1 = -raw12069step0 := by apply Matrix.ext; change ∀ i j, raw12069step1 i j = -(raw12069step0 i j); unfold raw12069step1 raw12069step0; decide +kernel
      have hl : raw12069step1Labels = raw12069step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3378 node3378Labels := by rfl

theorem canonical12070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12070 raw12070Labels = mixedMoment B node3378 node3378Labels := by
  calc
    mixedMoment B raw12070 raw12070Labels = mixedMoment B raw12070step0 raw12070step0Labels := by
      have ha : raw12070step0 = (fun i j => raw12070 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12070step0 raw12070; decide +kernel
      have hl : raw12070step0Labels = raw12070Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12070 raw12070Labels permutation161 permutation4
    mixedMoment B raw12070step0 raw12070step0Labels = mixedMoment B raw12070step1 raw12070step1Labels := by
      have ha : raw12070step1 = -raw12070step0 := by apply Matrix.ext; change ∀ i j, raw12070step1 i j = -(raw12070step0 i j); unfold raw12070step1 raw12070step0; decide +kernel
      have hl : raw12070step1Labels = raw12070step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3378 node3378Labels := by rfl

theorem canonical12071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12071 raw12071Labels = mixedMoment B node2010 node2010Labels := by
  calc
    mixedMoment B raw12071 raw12071Labels = mixedMoment B raw12071step0 raw12071step0Labels := by
      have ha : raw12071step0 = (fun i j => raw12071 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12071step0 raw12071; decide +kernel
      have hl : raw12071step0Labels = raw12071Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12071 raw12071Labels permutation161 permutation4
    mixedMoment B raw12071step0 raw12071step0Labels = mixedMoment B raw12071step1 raw12071step1Labels := by
      have ha : raw12071step1 = -raw12071step0 := by apply Matrix.ext; change ∀ i j, raw12071step1 i j = -(raw12071step0 i j); unfold raw12071step1 raw12071step0; decide +kernel
      have hl : raw12071step1Labels = raw12071step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2010 node2010Labels := by rfl

theorem canonical12072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12072 raw12072Labels = mixedMoment B node3149 node3149Labels := by
  calc
    mixedMoment B raw12072 raw12072Labels = mixedMoment B raw12072step0 raw12072step0Labels := by
      have ha : raw12072step0 = (fun i j => raw12072 (permutation362 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12072step0 raw12072; decide +kernel
      have hl : raw12072step0Labels = raw12072Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12072 raw12072Labels permutation362 permutation2
    mixedMoment B raw12072step0 raw12072step0Labels = mixedMoment B raw12072step1 raw12072step1Labels := by
      have ha : raw12072step1 = -raw12072step0 := by apply Matrix.ext; change ∀ i j, raw12072step1 i j = -(raw12072step0 i j); unfold raw12072step1 raw12072step0; decide +kernel
      have hl : raw12072step1Labels = raw12072step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3149 node3149Labels := by rfl

theorem canonical12073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12073 raw12073Labels = mixedMoment B node3149 node3149Labels := by
  calc
    mixedMoment B raw12073 raw12073Labels = mixedMoment B raw12073step0 raw12073step0Labels := by
      have ha : raw12073step0 = (fun i j => raw12073 (permutation361 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12073step0 raw12073; decide +kernel
      have hl : raw12073step0Labels = raw12073Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12073 raw12073Labels permutation361 permutation2
    mixedMoment B raw12073step0 raw12073step0Labels = mixedMoment B raw12073step1 raw12073step1Labels := by
      have ha : raw12073step1 = -raw12073step0 := by apply Matrix.ext; change ∀ i j, raw12073step1 i j = -(raw12073step0 i j); unfold raw12073step1 raw12073step0; decide +kernel
      have hl : raw12073step1Labels = raw12073step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3149 node3149Labels := by rfl

theorem canonical12074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12074 raw12074Labels = mixedMoment B node3155 node3155Labels := by
  calc
    mixedMoment B raw12074 raw12074Labels = mixedMoment B raw12074step0 raw12074step0Labels := by
      have ha : raw12074step0 = (fun i j => raw12074 (permutation346 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12074step0 raw12074; decide +kernel
      have hl : raw12074step0Labels = raw12074Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12074 raw12074Labels permutation346 permutation2
    mixedMoment B raw12074step0 raw12074step0Labels = mixedMoment B raw12074step1 raw12074step1Labels := by
      have ha : raw12074step1 = -raw12074step0 := by apply Matrix.ext; change ∀ i j, raw12074step1 i j = -(raw12074step0 i j); unfold raw12074step1 raw12074step0; decide +kernel
      have hl : raw12074step1Labels = raw12074step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3155 node3155Labels := by rfl

theorem canonical12075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12075 raw12075Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw12075 raw12075Labels = mixedMoment B raw12075step0 raw12075step0Labels := by
      have ha : raw12075step0 = (fun i j => raw12075 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12075step0 raw12075; decide +kernel
      have hl : raw12075step0Labels = raw12075Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12075 raw12075Labels permutation167 permutation4
    mixedMoment B raw12075step0 raw12075step0Labels = mixedMoment B raw12075step1 raw12075step1Labels := by
      have ha : raw12075step1 = -raw12075step0 := by apply Matrix.ext; change ∀ i j, raw12075step1 i j = -(raw12075step0 i j); unfold raw12075step1 raw12075step0; decide +kernel
      have hl : raw12075step1Labels = raw12075step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2023 node2023Labels := by rfl

theorem canonical12076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12076 raw12076Labels = mixedMoment B node3505 node3505Labels := by
  calc
    mixedMoment B raw12076 raw12076Labels = mixedMoment B raw12076step0 raw12076step0Labels := by
      have ha : raw12076step0 = (fun i j => raw12076 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12076step0 raw12076; decide +kernel
      have hl : raw12076step0Labels = raw12076Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12076 raw12076Labels permutation167 permutation4
    mixedMoment B raw12076step0 raw12076step0Labels = mixedMoment B raw12076step1 raw12076step1Labels := by
      have ha : raw12076step1 = -raw12076step0 := by apply Matrix.ext; change ∀ i j, raw12076step1 i j = -(raw12076step0 i j); unfold raw12076step1 raw12076step0; decide +kernel
      have hl : raw12076step1Labels = raw12076step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3505 node3505Labels := by rfl

theorem canonical12077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12077 raw12077Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw12077 raw12077Labels = mixedMoment B raw12077step0 raw12077step0Labels := by
      have ha : raw12077step0 = (fun i j => raw12077 (permutation169 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12077step0 raw12077; decide +kernel
      have hl : raw12077step0Labels = raw12077Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12077 raw12077Labels permutation169 permutation4
    mixedMoment B raw12077step0 raw12077step0Labels = mixedMoment B raw12077step1 raw12077step1Labels := by
      have ha : raw12077step1 = -raw12077step0 := by apply Matrix.ext; change ∀ i j, raw12077step1 i j = -(raw12077step0 i j); unfold raw12077step1 raw12077step0; decide +kernel
      have hl : raw12077step1Labels = raw12077step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3526 node3526Labels := by rfl

theorem canonical12078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12078 raw12078Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw12078 raw12078Labels = mixedMoment B raw12078step0 raw12078step0Labels := by
      have hz : ∀ j, raw12078 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12078step0 = (fun i j => raw12078 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12078step0 raw12078; decide +kernel
      have hl : raw12078step0Labels = raw12078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12078 raw12078Labels permutation265 hz
    mixedMoment B raw12078step0 raw12078step0Labels = mixedMoment B raw12078step1 raw12078step1Labels := by
      have ha : raw12078step1 = (fun i j => raw12078step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12078step1 raw12078step0; decide +kernel
      have hl : raw12078step1Labels = raw12078step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12078step0 raw12078step0Labels permutation41 permutation4
    mixedMoment B raw12078step1 raw12078step1Labels = mixedMoment B raw12078step2 raw12078step2Labels := by
      have ha : raw12078step2 = -raw12078step1 := by apply Matrix.ext; change ∀ i j, raw12078step2 i j = -(raw12078step1 i j); unfold raw12078step2 raw12078step1; decide +kernel
      have hl : raw12078step2Labels = raw12078step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3573 node3573Labels := by rfl

theorem canonical12079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12079 raw12079Labels = mixedMoment B node3505 node3505Labels := by
  calc
    mixedMoment B raw12079 raw12079Labels = mixedMoment B raw12079step0 raw12079step0Labels := by
      have ha : raw12079step0 = (fun i j => raw12079 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12079step0 raw12079; decide +kernel
      have hl : raw12079step0Labels = raw12079Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12079 raw12079Labels permutation161 permutation4
    mixedMoment B raw12079step0 raw12079step0Labels = mixedMoment B raw12079step1 raw12079step1Labels := by
      have ha : raw12079step1 = -raw12079step0 := by apply Matrix.ext; change ∀ i j, raw12079step1 i j = -(raw12079step0 i j); unfold raw12079step1 raw12079step0; decide +kernel
      have hl : raw12079step1Labels = raw12079step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3505 node3505Labels := by rfl

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

theorem canonical12183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12183 raw12183Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw12183 raw12183Labels = mixedMoment B raw12183step0 raw12183step0Labels := by
      have hz : ∀ j, raw12183 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12183step0 = (fun i j => raw12183 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12183step0 raw12183; decide +kernel
      have hl : raw12183step0Labels = raw12183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12183 raw12183Labels permutation265 hz
    mixedMoment B raw12183step0 raw12183step0Labels = mixedMoment B raw12183step1 raw12183step1Labels := by
      have ha : raw12183step1 = (fun i j => raw12183step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12183step1 raw12183step0; decide +kernel
      have hl : raw12183step1Labels = raw12183step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12183step0 raw12183step0Labels permutation36 permutation7
    mixedMoment B raw12183step1 raw12183step1Labels = mixedMoment B raw12183step2 raw12183step2Labels := by
      have ha : raw12183step2 = raw12183step1 := by apply Matrix.ext; unfold raw12183step2 raw12183step1; decide +kernel
      have hl : raw12183step1Labels = labelEmbedding10 ∘ raw12183step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12183step1 raw12183step1Labels raw12183step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical12184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12184 raw12184Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw12184 raw12184Labels = mixedMoment B raw12184step0 raw12184step0Labels := by
      have hz : ∀ j, raw12184 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12184step0 = (fun i j => raw12184 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12184step0 raw12184; decide +kernel
      have hl : raw12184step0Labels = raw12184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12184 raw12184Labels permutation346 hz
    mixedMoment B raw12184step0 raw12184step0Labels = mixedMoment B raw12184step1 raw12184step1Labels := by
      have hz : ∀ j, raw12184step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12184step1 = (fun i j => raw12184step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12184step1 raw12184step0; decide +kernel
      have hl : raw12184step1Labels = raw12184step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12184step0 raw12184step0Labels permutation56 hz
    mixedMoment B raw12184step1 raw12184step1Labels = mixedMoment B raw12184step2 raw12184step2Labels := by
      have ha : raw12184step2 = (fun i j => raw12184step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12184step2 raw12184step1; decide +kernel
      have hl : raw12184step2Labels = raw12184step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12184step1 raw12184step1Labels permutation13 permutation7
    mixedMoment B raw12184step2 raw12184step2Labels = mixedMoment B raw12184step3 raw12184step3Labels := by
      have ha : raw12184step3 = raw12184step2 := by apply Matrix.ext; unfold raw12184step3 raw12184step2; decide +kernel
      have hl : raw12184step2Labels = labelEmbedding10 ∘ raw12184step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12184step2 raw12184step2Labels raw12184step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

theorem canonical12185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12185 raw12185Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw12185 raw12185Labels = mixedMoment B raw12185step0 raw12185step0Labels := by
      have hz : ∀ j, raw12185 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12185step0 = (fun i j => raw12185 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12185step0 raw12185; decide +kernel
      have hl : raw12185step0Labels = raw12185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12185 raw12185Labels permutation346 hz
    mixedMoment B raw12185step0 raw12185step0Labels = mixedMoment B raw12185step1 raw12185step1Labels := by
      have hz : ∀ j, raw12185step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12185step1 = (fun i j => raw12185step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12185step1 raw12185step0; decide +kernel
      have hl : raw12185step1Labels = raw12185step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12185step0 raw12185step0Labels permutation56 hz
    mixedMoment B raw12185step1 raw12185step1Labels = mixedMoment B raw12185step2 raw12185step2Labels := by
      have ha : raw12185step2 = (fun i j => raw12185step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12185step2 raw12185step1; decide +kernel
      have hl : raw12185step2Labels = raw12185step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12185step1 raw12185step1Labels permutation12 permutation7
    mixedMoment B raw12185step2 raw12185step2Labels = mixedMoment B raw12185step3 raw12185step3Labels := by
      have ha : raw12185step3 = raw12185step2 := by apply Matrix.ext; unfold raw12185step3 raw12185step2; decide +kernel
      have hl : raw12185step2Labels = labelEmbedding10 ∘ raw12185step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12185step2 raw12185step2Labels raw12185step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

theorem canonical12186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12186 raw12186Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw12186 raw12186Labels = mixedMoment B raw12186step0 raw12186step0Labels := by
      have hz : ∀ j, raw12186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12186step0 = (fun i j => raw12186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12186step0 raw12186; decide +kernel
      have hl : raw12186step0Labels = raw12186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12186 raw12186Labels permutation346 hz
    mixedMoment B raw12186step0 raw12186step0Labels = mixedMoment B raw12186step1 raw12186step1Labels := by
      have hz : ∀ j, raw12186step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12186step1 = (fun i j => raw12186step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12186step1 raw12186step0; decide +kernel
      have hl : raw12186step1Labels = raw12186step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12186step0 raw12186step0Labels permutation56 hz
    mixedMoment B raw12186step1 raw12186step1Labels = mixedMoment B raw12186step2 raw12186step2Labels := by
      have ha : raw12186step2 = (fun i j => raw12186step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12186step2 raw12186step1; decide +kernel
      have hl : raw12186step2Labels = raw12186step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12186step1 raw12186step1Labels permutation12 permutation7
    mixedMoment B raw12186step2 raw12186step2Labels = mixedMoment B raw12186step3 raw12186step3Labels := by
      have ha : raw12186step3 = raw12186step2 := by apply Matrix.ext; unfold raw12186step3 raw12186step2; decide +kernel
      have hl : raw12186step2Labels = labelEmbedding10 ∘ raw12186step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12186step2 raw12186step2Labels raw12186step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5307 node5307Labels := by rfl

theorem canonical12187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12187 raw12187Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw12187 raw12187Labels = mixedMoment B raw12187step0 raw12187step0Labels := by
      have hz : ∀ j, raw12187 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12187step0 = (fun i j => raw12187 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12187step0 raw12187; decide +kernel
      have hl : raw12187step0Labels = raw12187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12187 raw12187Labels permutation346 hz
    mixedMoment B raw12187step0 raw12187step0Labels = mixedMoment B raw12187step1 raw12187step1Labels := by
      have ha : raw12187step1 = (fun i j => raw12187step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12187step1 raw12187step0; decide +kernel
      have hl : raw12187step1Labels = raw12187step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12187step0 raw12187step0Labels permutation40 permutation4
    mixedMoment B raw12187step1 raw12187step1Labels = mixedMoment B raw12187step2 raw12187step2Labels := by
      have ha : raw12187step2 = -raw12187step1 := by apply Matrix.ext; change ∀ i j, raw12187step2 i j = -(raw12187step1 i j); unfold raw12187step2 raw12187step1; decide +kernel
      have hl : raw12187step2Labels = raw12187step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12187step2 raw12187step2Labels = mixedMoment B raw12187step3 raw12187step3Labels := by
      have ha : raw12187step3 = raw12187step2 := by apply Matrix.ext; unfold raw12187step3 raw12187step2; decide +kernel
      have hl : raw12187step2Labels = labelEmbedding7 ∘ raw12187step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12187step2 raw12187step2Labels raw12187step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical12188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12188 raw12188Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw12188 raw12188Labels = mixedMoment B raw12188step0 raw12188step0Labels := by
      have ha : raw12188step0 = (fun i j => raw12188 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12188step0 raw12188; decide +kernel
      have hl : raw12188step0Labels = raw12188Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12188 raw12188Labels permutation176 permutation6
    mixedMoment B raw12188step0 raw12188step0Labels = mixedMoment B raw12188step1 raw12188step1Labels := by
      have ha : raw12188step1 = raw12188step0 := by apply Matrix.ext; unfold raw12188step1 raw12188step0; decide +kernel
      have hl : raw12188step0Labels = labelEmbedding9 ∘ raw12188step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12188step0 raw12188step0Labels raw12188step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5256 node5256Labels := by rfl

theorem canonical12189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12189 raw12189Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw12189 raw12189Labels = mixedMoment B raw12189step0 raw12189step0Labels := by
      have hz : ∀ j, raw12189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12189step0 = (fun i j => raw12189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12189step0 raw12189; decide +kernel
      have hl : raw12189step0Labels = raw12189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12189 raw12189Labels permutation346 hz
    mixedMoment B raw12189step0 raw12189step0Labels = mixedMoment B raw12189step1 raw12189step1Labels := by
      have ha : raw12189step1 = (fun i j => raw12189step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12189step1 raw12189step0; decide +kernel
      have hl : raw12189step1Labels = raw12189step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12189step0 raw12189step0Labels permutation32 permutation6
    mixedMoment B raw12189step1 raw12189step1Labels = mixedMoment B raw12189step2 raw12189step2Labels := by
      have ha : raw12189step2 = raw12189step1 := by apply Matrix.ext; unfold raw12189step2 raw12189step1; decide +kernel
      have hl : raw12189step1Labels = labelEmbedding9 ∘ raw12189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12189step1 raw12189step1Labels raw12189step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

theorem canonical12190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12190 raw12190Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw12190 raw12190Labels = mixedMoment B raw12190step0 raw12190step0Labels := by
      have hz : ∀ j, raw12190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12190step0 = (fun i j => raw12190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12190step0 raw12190; decide +kernel
      have hl : raw12190step0Labels = raw12190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12190 raw12190Labels permutation346 hz
    mixedMoment B raw12190step0 raw12190step0Labels = mixedMoment B raw12190step1 raw12190step1Labels := by
      have ha : raw12190step1 = (fun i j => raw12190step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12190step1 raw12190step0; decide +kernel
      have hl : raw12190step1Labels = raw12190step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12190step0 raw12190step0Labels permutation34 permutation6
    mixedMoment B raw12190step1 raw12190step1Labels = mixedMoment B raw12190step2 raw12190step2Labels := by
      have ha : raw12190step2 = raw12190step1 := by apply Matrix.ext; unfold raw12190step2 raw12190step1; decide +kernel
      have hl : raw12190step1Labels = labelEmbedding9 ∘ raw12190step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12190step1 raw12190step1Labels raw12190step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

theorem canonical12191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12191 raw12191Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw12191 raw12191Labels = mixedMoment B raw12191step0 raw12191step0Labels := by
      have hz : ∀ j, raw12191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12191step0 = (fun i j => raw12191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12191step0 raw12191; decide +kernel
      have hl : raw12191step0Labels = raw12191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12191 raw12191Labels permutation346 hz
    mixedMoment B raw12191step0 raw12191step0Labels = mixedMoment B raw12191step1 raw12191step1Labels := by
      have ha : raw12191step1 = (fun i j => raw12191step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12191step1 raw12191step0; decide +kernel
      have hl : raw12191step1Labels = raw12191step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12191step0 raw12191step0Labels permutation32 permutation6
    mixedMoment B raw12191step1 raw12191step1Labels = mixedMoment B raw12191step2 raw12191step2Labels := by
      have ha : raw12191step2 = raw12191step1 := by apply Matrix.ext; unfold raw12191step2 raw12191step1; decide +kernel
      have hl : raw12191step1Labels = labelEmbedding9 ∘ raw12191step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12191step1 raw12191step1Labels raw12191step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical12192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12192 raw12192Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw12192 raw12192Labels = mixedMoment B raw12192step0 raw12192step0Labels := by
      have hz : ∀ j, raw12192 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12192step0 = (fun i j => raw12192 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12192step0 raw12192; decide +kernel
      have hl : raw12192step0Labels = raw12192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12192 raw12192Labels permutation346 hz
    mixedMoment B raw12192step0 raw12192step0Labels = mixedMoment B raw12192step1 raw12192step1Labels := by
      have hz : ∀ j, raw12192step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12192step1 = (fun i j => raw12192step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12192step1 raw12192step0; decide +kernel
      have hl : raw12192step1Labels = raw12192step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12192step0 raw12192step0Labels permutation56 hz
    mixedMoment B raw12192step1 raw12192step1Labels = mixedMoment B raw12192step2 raw12192step2Labels := by
      have ha : raw12192step2 = (fun i j => raw12192step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12192step2 raw12192step1; decide +kernel
      have hl : raw12192step2Labels = raw12192step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12192step1 raw12192step1Labels permutation10 permutation4
    mixedMoment B raw12192step2 raw12192step2Labels = mixedMoment B raw12192step3 raw12192step3Labels := by
      have ha : raw12192step3 = -raw12192step2 := by apply Matrix.ext; change ∀ i j, raw12192step3 i j = -(raw12192step2 i j); unfold raw12192step3 raw12192step2; decide +kernel
      have hl : raw12192step3Labels = raw12192step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12192step3 raw12192step3Labels = mixedMoment B raw12192step4 raw12192step4Labels := by
      have ha : raw12192step4 = raw12192step3 := by apply Matrix.ext; unfold raw12192step4 raw12192step3; decide +kernel
      have hl : raw12192step3Labels = labelEmbedding7 ∘ raw12192step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12192step3 raw12192step3Labels raw12192step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

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

theorem canonical12194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12194 raw12194Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw12194 raw12194Labels = mixedMoment B raw12194step0 raw12194step0Labels := by
      have hz : ∀ j, raw12194 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12194step0 = (fun i j => raw12194 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12194step0 raw12194; decide +kernel
      have hl : raw12194step0Labels = raw12194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12194 raw12194Labels permutation346 hz
    mixedMoment B raw12194step0 raw12194step0Labels = mixedMoment B raw12194step1 raw12194step1Labels := by
      have hz : ∀ j, raw12194step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12194step1 = (fun i j => raw12194step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12194step1 raw12194step0; decide +kernel
      have hl : raw12194step1Labels = raw12194step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12194step0 raw12194step0Labels permutation56 hz
    mixedMoment B raw12194step1 raw12194step1Labels = mixedMoment B raw12194step2 raw12194step2Labels := by
      have ha : raw12194step2 = (fun i j => raw12194step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12194step2 raw12194step1; decide +kernel
      have hl : raw12194step2Labels = raw12194step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12194step1 raw12194step1Labels permutation10 permutation6
    mixedMoment B raw12194step2 raw12194step2Labels = mixedMoment B raw12194step3 raw12194step3Labels := by
      have ha : raw12194step3 = raw12194step2 := by apply Matrix.ext; unfold raw12194step3 raw12194step2; decide +kernel
      have hl : raw12194step2Labels = labelEmbedding9 ∘ raw12194step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12194step2 raw12194step2Labels raw12194step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

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

theorem canonical12196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12196 raw12196Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw12196 raw12196Labels = mixedMoment B raw12196step0 raw12196step0Labels := by
      have hz : ∀ j, raw12196 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12196step0 = (fun i j => raw12196 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12196step0 raw12196; decide +kernel
      have hl : raw12196step0Labels = raw12196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12196 raw12196Labels permutation346 hz
    mixedMoment B raw12196step0 raw12196step0Labels = mixedMoment B raw12196step1 raw12196step1Labels := by
      have hz : ∀ j, raw12196step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12196step1 = (fun i j => raw12196step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12196step1 raw12196step0; decide +kernel
      have hl : raw12196step1Labels = raw12196step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12196step0 raw12196step0Labels permutation56 hz
    mixedMoment B raw12196step1 raw12196step1Labels = mixedMoment B raw12196step2 raw12196step2Labels := by
      have ha : raw12196step2 = (fun i j => raw12196step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12196step2 raw12196step1; decide +kernel
      have hl : raw12196step2Labels = raw12196step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12196step1 raw12196step1Labels permutation8 permutation4
    mixedMoment B raw12196step2 raw12196step2Labels = mixedMoment B raw12196step3 raw12196step3Labels := by
      have ha : raw12196step3 = -raw12196step2 := by apply Matrix.ext; change ∀ i j, raw12196step3 i j = -(raw12196step2 i j); unfold raw12196step3 raw12196step2; decide +kernel
      have hl : raw12196step3Labels = raw12196step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12196step3 raw12196step3Labels = mixedMoment B raw12196step4 raw12196step4Labels := by
      have ha : raw12196step4 = raw12196step3 := by apply Matrix.ext; unfold raw12196step4 raw12196step3; decide +kernel
      have hl : raw12196step3Labels = labelEmbedding7 ∘ raw12196step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12196step3 raw12196step3Labels raw12196step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

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

theorem canonical12198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12198 raw12198Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw12198 raw12198Labels = mixedMoment B raw12198step0 raw12198step0Labels := by
      have hz : ∀ j, raw12198 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12198step0 = (fun i j => raw12198 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12198step0 raw12198; decide +kernel
      have hl : raw12198step0Labels = raw12198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12198 raw12198Labels permutation346 hz
    mixedMoment B raw12198step0 raw12198step0Labels = mixedMoment B raw12198step1 raw12198step1Labels := by
      have hz : ∀ j, raw12198step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12198step1 = (fun i j => raw12198step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12198step1 raw12198step0; decide +kernel
      have hl : raw12198step1Labels = raw12198step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12198step0 raw12198step0Labels permutation56 hz
    mixedMoment B raw12198step1 raw12198step1Labels = mixedMoment B raw12198step2 raw12198step2Labels := by
      have ha : raw12198step2 = (fun i j => raw12198step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12198step2 raw12198step1; decide +kernel
      have hl : raw12198step2Labels = raw12198step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12198step1 raw12198step1Labels permutation8 permutation6
    mixedMoment B raw12198step2 raw12198step2Labels = mixedMoment B raw12198step3 raw12198step3Labels := by
      have ha : raw12198step3 = raw12198step2 := by apply Matrix.ext; unfold raw12198step3 raw12198step2; decide +kernel
      have hl : raw12198step2Labels = labelEmbedding9 ∘ raw12198step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12198step2 raw12198step2Labels raw12198step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

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

theorem canonical12200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12200 raw12200Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw12200 raw12200Labels = mixedMoment B raw12200step0 raw12200step0Labels := by
      have hz : ∀ j, raw12200 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12200step0 = (fun i j => raw12200 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12200step0 raw12200; decide +kernel
      have hl : raw12200step0Labels = raw12200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12200 raw12200Labels permutation346 hz
    mixedMoment B raw12200step0 raw12200step0Labels = mixedMoment B raw12200step1 raw12200step1Labels := by
      have hz : ∀ j, raw12200step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12200step1 = (fun i j => raw12200step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12200step1 raw12200step0; decide +kernel
      have hl : raw12200step1Labels = raw12200step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12200step0 raw12200step0Labels permutation56 hz
    mixedMoment B raw12200step1 raw12200step1Labels = mixedMoment B raw12200step2 raw12200step2Labels := by
      have ha : raw12200step2 = (fun i j => raw12200step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12200step2 raw12200step1; decide +kernel
      have hl : raw12200step2Labels = raw12200step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12200step1 raw12200step1Labels permutation8 permutation4
    mixedMoment B raw12200step2 raw12200step2Labels = mixedMoment B raw12200step3 raw12200step3Labels := by
      have ha : raw12200step3 = -raw12200step2 := by apply Matrix.ext; change ∀ i j, raw12200step3 i j = -(raw12200step2 i j); unfold raw12200step3 raw12200step2; decide +kernel
      have hl : raw12200step3Labels = raw12200step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12200step3 raw12200step3Labels = mixedMoment B raw12200step4 raw12200step4Labels := by
      have ha : raw12200step4 = raw12200step3 := by apply Matrix.ext; unfold raw12200step4 raw12200step3; decide +kernel
      have hl : raw12200step3Labels = labelEmbedding7 ∘ raw12200step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12200step3 raw12200step3Labels raw12200step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical12201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12201 raw12201Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw12201 raw12201Labels = mixedMoment B raw12201step0 raw12201step0Labels := by
      have hz : ∀ j, raw12201 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12201step0 = (fun i j => raw12201 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12201step0 raw12201; decide +kernel
      have hl : raw12201step0Labels = raw12201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12201 raw12201Labels permutation265 hz
    mixedMoment B raw12201step0 raw12201step0Labels = mixedMoment B raw12201step1 raw12201step1Labels := by
      have ha : raw12201step1 = (fun i j => raw12201step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12201step1 raw12201step0; decide +kernel
      have hl : raw12201step1Labels = raw12201step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12201step0 raw12201step0Labels permutation32 permutation6
    mixedMoment B raw12201step1 raw12201step1Labels = mixedMoment B raw12201step2 raw12201step2Labels := by
      have ha : raw12201step2 = raw12201step1 := by apply Matrix.ext; unfold raw12201step2 raw12201step1; decide +kernel
      have hl : raw12201step1Labels = labelEmbedding9 ∘ raw12201step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12201step1 raw12201step1Labels raw12201step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

theorem canonical12202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12202 raw12202Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw12202 raw12202Labels = mixedMoment B raw12202step0 raw12202step0Labels := by
      have hz : ∀ j, raw12202 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12202step0 = (fun i j => raw12202 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12202step0 raw12202; decide +kernel
      have hl : raw12202step0Labels = raw12202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12202 raw12202Labels permutation346 hz
    mixedMoment B raw12202step0 raw12202step0Labels = mixedMoment B raw12202step1 raw12202step1Labels := by
      have hz : ∀ j, raw12202step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12202step1 = (fun i j => raw12202step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12202step1 raw12202step0; decide +kernel
      have hl : raw12202step1Labels = raw12202step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12202step0 raw12202step0Labels permutation56 hz
    mixedMoment B raw12202step1 raw12202step1Labels = mixedMoment B raw12202step2 raw12202step2Labels := by
      have ha : raw12202step2 = (fun i j => raw12202step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12202step2 raw12202step1; decide +kernel
      have hl : raw12202step2Labels = raw12202step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12202step1 raw12202step1Labels permutation31 permutation5
    mixedMoment B raw12202step2 raw12202step2Labels = mixedMoment B raw12202step3 raw12202step3Labels := by
      have ha : raw12202step3 = raw12202step2 := by apply Matrix.ext; unfold raw12202step3 raw12202step2; decide +kernel
      have hl : raw12202step2Labels = labelEmbedding8 ∘ raw12202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12202step2 raw12202step2Labels raw12202step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

theorem canonical12203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12203 raw12203Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw12203 raw12203Labels = mixedMoment B raw12203step0 raw12203step0Labels := by
      have hz : ∀ j, raw12203 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12203step0 = (fun i j => raw12203 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12203step0 raw12203; decide +kernel
      have hl : raw12203step0Labels = raw12203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12203 raw12203Labels permutation346 hz
    mixedMoment B raw12203step0 raw12203step0Labels = mixedMoment B raw12203step1 raw12203step1Labels := by
      have hz : ∀ j, raw12203step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12203step1 = (fun i j => raw12203step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12203step1 raw12203step0; decide +kernel
      have hl : raw12203step1Labels = raw12203step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12203step0 raw12203step0Labels permutation56 hz
    mixedMoment B raw12203step1 raw12203step1Labels = mixedMoment B raw12203step2 raw12203step2Labels := by
      have ha : raw12203step2 = (fun i j => raw12203step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12203step2 raw12203step1; decide +kernel
      have hl : raw12203step2Labels = raw12203step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12203step1 raw12203step1Labels permutation29 permutation5
    mixedMoment B raw12203step2 raw12203step2Labels = mixedMoment B raw12203step3 raw12203step3Labels := by
      have ha : raw12203step3 = raw12203step2 := by apply Matrix.ext; unfold raw12203step3 raw12203step2; decide +kernel
      have hl : raw12203step2Labels = labelEmbedding8 ∘ raw12203step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12203step2 raw12203step2Labels raw12203step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

theorem canonical12225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12225 raw12225Labels = mixedMoment B node3623 node3623Labels := by
  calc
    mixedMoment B raw12225 raw12225Labels = mixedMoment B raw12225step0 raw12225step0Labels := by
      have hz : ∀ j, raw12225 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12225step0 = (fun i j => raw12225 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12225step0 raw12225; decide +kernel
      have hl : raw12225step0Labels = raw12225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12225 raw12225Labels permutation346 hz
    mixedMoment B raw12225step0 raw12225step0Labels = mixedMoment B raw12225step1 raw12225step1Labels := by
      have hz : ∀ j, raw12225step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12225step1 = (fun i j => raw12225step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12225step1 raw12225step0; decide +kernel
      have hl : raw12225step1Labels = raw12225step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12225step0 raw12225step0Labels permutation56 hz
    mixedMoment B raw12225step1 raw12225step1Labels = mixedMoment B raw12225step2 raw12225step2Labels := by
      have ha : raw12225step2 = (fun i j => raw12225step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12225step2 raw12225step1; decide +kernel
      have hl : raw12225step2Labels = raw12225step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12225step1 raw12225step1Labels permutation8 permutation4
    mixedMoment B raw12225step2 raw12225step2Labels = mixedMoment B raw12225step3 raw12225step3Labels := by
      have ha : raw12225step3 = -raw12225step2 := by apply Matrix.ext; change ∀ i j, raw12225step3 i j = -(raw12225step2 i j); unfold raw12225step3 raw12225step2; decide +kernel
      have hl : raw12225step3Labels = raw12225step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3623 node3623Labels := by rfl

theorem canonical12226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12226 raw12226Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw12226 raw12226Labels = mixedMoment B raw12226step0 raw12226step0Labels := by
      have hz : ∀ j, raw12226 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12226step0 = (fun i j => raw12226 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12226step0 raw12226; decide +kernel
      have hl : raw12226step0Labels = raw12226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12226 raw12226Labels permutation265 hz
    mixedMoment B raw12226step0 raw12226step0Labels = mixedMoment B raw12226step1 raw12226step1Labels := by
      have ha : raw12226step1 = (fun i j => raw12226step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12226step1 raw12226step0; decide +kernel
      have hl : raw12226step1Labels = raw12226step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12226step0 raw12226step0Labels permutation50 permutation2
    mixedMoment B raw12226step1 raw12226step1Labels = mixedMoment B raw12226step2 raw12226step2Labels := by
      have ha : raw12226step2 = -raw12226step1 := by apply Matrix.ext; change ∀ i j, raw12226step2 i j = -(raw12226step1 i j); unfold raw12226step2 raw12226step1; decide +kernel
      have hl : raw12226step2Labels = raw12226step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3581 node3581Labels := by rfl

theorem canonical12227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12227 raw12227Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw12227 raw12227Labels = mixedMoment B raw12227step0 raw12227step0Labels := by
      have hz : ∀ j, raw12227 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12227step0 = (fun i j => raw12227 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12227step0 raw12227; decide +kernel
      have hl : raw12227step0Labels = raw12227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12227 raw12227Labels permutation346 hz
    mixedMoment B raw12227step0 raw12227step0Labels = mixedMoment B raw12227step1 raw12227step1Labels := by
      have hz : ∀ j, raw12227step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12227step1 = (fun i j => raw12227step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12227step1 raw12227step0; decide +kernel
      have hl : raw12227step1Labels = raw12227step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12227step0 raw12227step0Labels permutation56 hz
    mixedMoment B raw12227step1 raw12227step1Labels = mixedMoment B raw12227step2 raw12227step2Labels := by
      have ha : raw12227step2 = (fun i j => raw12227step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12227step2 raw12227step1; decide +kernel
      have hl : raw12227step2Labels = raw12227step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12227step1 raw12227step1Labels permutation13 permutation2
    mixedMoment B raw12227step2 raw12227step2Labels = mixedMoment B raw12227step3 raw12227step3Labels := by
      have ha : raw12227step3 = -raw12227step2 := by apply Matrix.ext; change ∀ i j, raw12227step3 i j = -(raw12227step2 i j); unfold raw12227step3 raw12227step2; decide +kernel
      have hl : raw12227step3Labels = raw12227step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3583 node3583Labels := by rfl

theorem canonical12228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12228 raw12228Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw12228 raw12228Labels = mixedMoment B raw12228step0 raw12228step0Labels := by
      have hz : ∀ j, raw12228 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12228step0 = (fun i j => raw12228 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12228step0 raw12228; decide +kernel
      have hl : raw12228step0Labels = raw12228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12228 raw12228Labels permutation346 hz
    mixedMoment B raw12228step0 raw12228step0Labels = mixedMoment B raw12228step1 raw12228step1Labels := by
      have hz : ∀ j, raw12228step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12228step1 = (fun i j => raw12228step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12228step1 raw12228step0; decide +kernel
      have hl : raw12228step1Labels = raw12228step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12228step0 raw12228step0Labels permutation56 hz
    mixedMoment B raw12228step1 raw12228step1Labels = mixedMoment B raw12228step2 raw12228step2Labels := by
      have ha : raw12228step2 = (fun i j => raw12228step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12228step2 raw12228step1; decide +kernel
      have hl : raw12228step2Labels = raw12228step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12228step1 raw12228step1Labels permutation12 permutation2
    mixedMoment B raw12228step2 raw12228step2Labels = mixedMoment B raw12228step3 raw12228step3Labels := by
      have ha : raw12228step3 = -raw12228step2 := by apply Matrix.ext; change ∀ i j, raw12228step3 i j = -(raw12228step2 i j); unfold raw12228step3 raw12228step2; decide +kernel
      have hl : raw12228step3Labels = raw12228step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3583 node3583Labels := by rfl

theorem canonical12229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12229 raw12229Labels = mixedMoment B node3628 node3628Labels := by
  calc
    mixedMoment B raw12229 raw12229Labels = mixedMoment B raw12229step0 raw12229step0Labels := by
      have hz : ∀ j, raw12229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12229step0 = (fun i j => raw12229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12229step0 raw12229; decide +kernel
      have hl : raw12229step0Labels = raw12229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12229 raw12229Labels permutation346 hz
    mixedMoment B raw12229step0 raw12229step0Labels = mixedMoment B raw12229step1 raw12229step1Labels := by
      have hz : ∀ j, raw12229step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12229step1 = (fun i j => raw12229step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12229step1 raw12229step0; decide +kernel
      have hl : raw12229step1Labels = raw12229step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12229step0 raw12229step0Labels permutation56 hz
    mixedMoment B raw12229step1 raw12229step1Labels = mixedMoment B raw12229step2 raw12229step2Labels := by
      have ha : raw12229step2 = (fun i j => raw12229step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12229step2 raw12229step1; decide +kernel
      have hl : raw12229step2Labels = raw12229step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12229step1 raw12229step1Labels permutation12 permutation2
    mixedMoment B raw12229step2 raw12229step2Labels = mixedMoment B raw12229step3 raw12229step3Labels := by
      have ha : raw12229step3 = -raw12229step2 := by apply Matrix.ext; change ∀ i j, raw12229step3 i j = -(raw12229step2 i j); unfold raw12229step3 raw12229step2; decide +kernel
      have hl : raw12229step3Labels = raw12229step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3628 node3628Labels := by rfl

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

theorem canonical12320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12320 raw12320Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw12320 raw12320Labels = mixedMoment B raw12320step0 raw12320step0Labels := by
      have hz : ∀ j, raw12320 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12320step0 = (fun i j => raw12320 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12320step0 raw12320; decide +kernel
      have hl : raw12320step0Labels = raw12320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12320 raw12320Labels permutation265 hz
    _ = mixedMoment B node2763 node2763Labels := by rfl

theorem canonical12321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12321 raw12321Labels = mixedMoment B node3848 node3848Labels := by
  calc
    _ = mixedMoment B node3848 node3848Labels := by rfl

theorem canonical12322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12322 raw12322Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw12322 raw12322Labels = mixedMoment B raw12322step0 raw12322step0Labels := by
      have hz : ∀ j, raw12322 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12322step0 = (fun i j => raw12322 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12322step0 raw12322; decide +kernel
      have hl : raw12322step0Labels = raw12322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12322 raw12322Labels permutation265 hz
    _ = mixedMoment B node3884 node3884Labels := by rfl

theorem canonical12323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12323 raw12323Labels = mixedMoment B node3903 node3903Labels := by
  calc
    mixedMoment B raw12323 raw12323Labels = mixedMoment B raw12323step0 raw12323step0Labels := by
      have hz : ∀ j, raw12323 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12323step0 = (fun i j => raw12323 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12323step0 raw12323; decide +kernel
      have hl : raw12323step0Labels = raw12323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12323 raw12323Labels permutation265 hz
    mixedMoment B raw12323step0 raw12323step0Labels = mixedMoment B raw12323step1 raw12323step1Labels := by
      have ha : raw12323step1 = (fun i j => raw12323step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12323step1 raw12323step0; decide +kernel
      have hl : raw12323step1Labels = raw12323step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12323step0 raw12323step0Labels permutation38 permutation2
    _ = mixedMoment B node3903 node3903Labels := by rfl

theorem canonical12324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12324 raw12324Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw12324 raw12324Labels = mixedMoment B raw12324step0 raw12324step0Labels := by
      have hz : ∀ j, raw12324 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12324step0 = (fun i j => raw12324 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12324step0 raw12324; decide +kernel
      have hl : raw12324step0Labels = raw12324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12324 raw12324Labels permutation520 hz
    mixedMoment B raw12324step0 raw12324step0Labels = mixedMoment B raw12324step1 raw12324step1Labels := by
      have hz : ∀ j, raw12324step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12324step1 = (fun i j => raw12324step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12324step1 raw12324step0; decide +kernel
      have hl : raw12324step1Labels = raw12324step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12324step0 raw12324step0Labels permutation56 hz
    _ = mixedMoment B node3913 node3913Labels := by rfl

theorem canonical12325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12325 raw12325Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw12325 raw12325Labels = mixedMoment B raw12325step0 raw12325step0Labels := by
      have hz : ∀ j, raw12325 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12325step0 = (fun i j => raw12325 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12325step0 raw12325; decide +kernel
      have hl : raw12325step0Labels = raw12325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12325 raw12325Labels permutation265 hz
    mixedMoment B raw12325step0 raw12325step0Labels = mixedMoment B raw12325step1 raw12325step1Labels := by
      have ha : raw12325step1 = (fun i j => raw12325step0 (permutation135 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12325step1 raw12325step0; decide +kernel
      have hl : raw12325step1Labels = raw12325step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12325step0 raw12325step0Labels permutation135 permutation4
    mixedMoment B raw12325step1 raw12325step1Labels = mixedMoment B raw12325step2 raw12325step2Labels := by
      have ha : raw12325step2 = -raw12325step1 := by apply Matrix.ext; change ∀ i j, raw12325step2 i j = -(raw12325step1 i j); unfold raw12325step2 raw12325step1; decide +kernel
      have hl : raw12325step2Labels = raw12325step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3813 node3813Labels := by rfl

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

theorem canonical12327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12327 raw12327Labels = mixedMoment B node1259 node1259Labels := by
  calc
    mixedMoment B raw12327 raw12327Labels = mixedMoment B raw12327step0 raw12327step0Labels := by
      have ha : raw12327step0 = (fun i j => raw12327 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12327step0 raw12327; decide +kernel
      have hl : raw12327step0Labels = raw12327Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12327 raw12327Labels permutation182 permutation2
    _ = mixedMoment B node1259 node1259Labels := by rfl

theorem canonical12328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12328 raw12328Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw12328 raw12328Labels = mixedMoment B raw12328step0 raw12328step0Labels := by
      have hz : ∀ j, raw12328 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12328step0 = (fun i j => raw12328 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12328step0 raw12328; decide +kernel
      have hl : raw12328step0Labels = raw12328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12328 raw12328Labels permutation265 hz
    mixedMoment B raw12328step0 raw12328step0Labels = mixedMoment B raw12328step1 raw12328step1Labels := by
      have ha : raw12328step1 = (fun i j => raw12328step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12328step1 raw12328step0; decide +kernel
      have hl : raw12328step1Labels = raw12328step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12328step0 raw12328step0Labels permutation40 permutation2
    _ = mixedMoment B node1291 node1291Labels := by rfl

theorem canonical12329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12329 raw12329Labels = mixedMoment B node1268 node1268Labels := by
  calc
    mixedMoment B raw12329 raw12329Labels = mixedMoment B raw12329step0 raw12329step0Labels := by
      have hz : ∀ j, raw12329 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12329step0 = (fun i j => raw12329 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12329step0 raw12329; decide +kernel
      have hl : raw12329step0Labels = raw12329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12329 raw12329Labels permutation265 hz
    mixedMoment B raw12329step0 raw12329step0Labels = mixedMoment B raw12329step1 raw12329step1Labels := by
      have ha : raw12329step1 = (fun i j => raw12329step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12329step1 raw12329step0; decide +kernel
      have hl : raw12329step1Labels = raw12329step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12329step0 raw12329step0Labels permutation35 permutation2
    _ = mixedMoment B node1268 node1268Labels := by rfl

theorem canonical12330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12330 raw12330Labels = mixedMoment B node1263 node1263Labels := by
  calc
    mixedMoment B raw12330 raw12330Labels = mixedMoment B raw12330step0 raw12330step0Labels := by
      have hz : ∀ j, raw12330 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12330step0 = (fun i j => raw12330 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12330step0 raw12330; decide +kernel
      have hl : raw12330step0Labels = raw12330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12330 raw12330Labels permutation265 hz
    mixedMoment B raw12330step0 raw12330step0Labels = mixedMoment B raw12330step1 raw12330step1Labels := by
      have ha : raw12330step1 = (fun i j => raw12330step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12330step1 raw12330step0; decide +kernel
      have hl : raw12330step1Labels = raw12330step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12330step0 raw12330step0Labels permutation33 permutation2
    _ = mixedMoment B node1263 node1263Labels := by rfl

theorem canonical12331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12331 raw12331Labels = mixedMoment B node1261 node1261Labels := by
  calc
    mixedMoment B raw12331 raw12331Labels = mixedMoment B raw12331step0 raw12331step0Labels := by
      have hz : ∀ j, raw12331 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12331step0 = (fun i j => raw12331 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12331step0 raw12331; decide +kernel
      have hl : raw12331step0Labels = raw12331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12331 raw12331Labels permutation265 hz
    _ = mixedMoment B node1261 node1261Labels := by rfl

theorem canonical12332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12332 raw12332Labels = mixedMoment B node2587 node2587Labels := by
  calc
    mixedMoment B raw12332 raw12332Labels = mixedMoment B raw12332step0 raw12332step0Labels := by
      have ha : raw12332step0 = (fun i j => raw12332 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12332step0 raw12332; decide +kernel
      have hl : raw12332step0Labels = raw12332Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12332 raw12332Labels permutation160 permutation2
    _ = mixedMoment B node2587 node2587Labels := by rfl

theorem canonical12333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12333 raw12333Labels = mixedMoment B node2571 node2571Labels := by
  calc
    mixedMoment B raw12333 raw12333Labels = mixedMoment B raw12333step0 raw12333step0Labels := by
      have ha : raw12333step0 = (fun i j => raw12333 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12333step0 raw12333; decide +kernel
      have hl : raw12333step0Labels = raw12333Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12333 raw12333Labels permutation155 permutation2
    _ = mixedMoment B node2571 node2571Labels := by rfl

theorem canonical12334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12334 raw12334Labels = mixedMoment B node2568 node2568Labels := by
  calc
    mixedMoment B raw12334 raw12334Labels = mixedMoment B raw12334step0 raw12334step0Labels := by
      have ha : raw12334step0 = (fun i j => raw12334 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12334step0 raw12334; decide +kernel
      have hl : raw12334step0Labels = raw12334Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12334 raw12334Labels permutation153 permutation2
    _ = mixedMoment B node2568 node2568Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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

theorem singleton4890 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4890 node4890Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2247 node2247Labels + mixedMoment B node2290 node2290Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1821 singletonSmall4890
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4890) = raw1821Labels := by decide +kernel
  rw [hl, canonical1821 B hB] at h
  have hc0 : mixedMoment B raw1821 (Fin.cases (0 : Fin 2) singletonSmall4890) =
      mixedMoment B node2247 node2247Labels := by
    have ha : raw1821 = raw1822 := by apply Matrix.ext; unfold raw1821 raw1822; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4890 = raw1822Labels := by decide +kernel
    rw [ha, hj, canonical1822 B hB]
  have hc1 : mixedMoment B raw1821 (Fin.cases (1 : Fin 2) singletonSmall4890) =
      mixedMoment B node2290 node2290Labels := by
    have ha : raw1821 = raw1823 := by apply Matrix.ext; unfold raw1821 raw1823; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4890 = raw1823Labels := by decide +kernel
    rw [ha, hj, canonical1823 B hB]
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

theorem singleton5304 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5304 node5304Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2782 node2782Labels + mixedMoment B node3583 node3583Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2316 singletonSmall5304
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5304) = raw2316Labels := by decide +kernel
  rw [hl, canonical2316 B hB] at h
  have hc0 : mixedMoment B raw2316 (Fin.cases (0 : Fin 2) singletonSmall5304) =
      mixedMoment B node2782 node2782Labels := by
    have ha : raw2316 = raw2317 := by apply Matrix.ext; unfold raw2316 raw2317; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5304 = raw2317Labels := by decide +kernel
    rw [ha, hj, canonical2317 B hB]
  have hc1 : mixedMoment B raw2316 (Fin.cases (1 : Fin 2) singletonSmall5304) =
      mixedMoment B node3583 node3583Labels := by
    have ha : raw2316 = raw2318 := by apply Matrix.ext; unfold raw2316 raw2318; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5304 = raw2318Labels := by decide +kernel
    rw [ha, hj, canonical2318 B hB]
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

theorem sound1259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1259 node1259Labels = Sparse.eval nodeValue1259 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1259) = mixedMoment B node1259 node1259Labels := rfl
  simpa [nodeValue1259, Sparse.eval] using hc.symm

theorem sound1261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1261 node1261Labels = Sparse.eval nodeValue1261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1261) = mixedMoment B node1261 node1261Labels := rfl
  simpa [nodeValue1261, Sparse.eval] using hc.symm

theorem sound1263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1263 node1263Labels = Sparse.eval nodeValue1263 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1263) = mixedMoment B node1263 node1263Labels := rfl
  simpa [nodeValue1263, Sparse.eval] using hc.symm

theorem sound1268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1268 node1268Labels = Sparse.eval nodeValue1268 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1268) = mixedMoment B node1268 node1268Labels := rfl
  simpa [nodeValue1268, Sparse.eval] using hc.symm

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

theorem sound1291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1291 node1291Labels = Sparse.eval nodeValue1291 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1291) = mixedMoment B node1291 node1291Labels := rfl
  simpa [nodeValue1291, Sparse.eval] using hc.symm

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

theorem sound2023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2023 node2023Labels = Sparse.eval nodeValue2023 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2023) = mixedMoment B node2023 node2023Labels := rfl
  simpa [nodeValue2023, Sparse.eval] using hc.symm

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

theorem sound2244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2244 node2244Labels = Sparse.eval nodeValue2244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2244) = mixedMoment B node2244 node2244Labels := rfl
  simpa [nodeValue2244, Sparse.eval] using hc.symm

theorem sound2247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2247 node2247Labels = Sparse.eval nodeValue2247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2247) = mixedMoment B node2247 node2247Labels := rfl
  simpa [nodeValue2247, Sparse.eval] using hc.symm

theorem sound2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2262 node2262Labels = Sparse.eval nodeValue2262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2262) = mixedMoment B node2262 node2262Labels := rfl
  simpa [nodeValue2262, Sparse.eval] using hc.symm

theorem sound2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2290 node2290Labels = Sparse.eval nodeValue2290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2290) = mixedMoment B node2290 node2290Labels := rfl
  simpa [nodeValue2290, Sparse.eval] using hc.symm

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

theorem sound2568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2568 node2568Labels = Sparse.eval nodeValue2568 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2568) = mixedMoment B node2568 node2568Labels := rfl
  simpa [nodeValue2568, Sparse.eval] using hc.symm

theorem sound2571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2571 node2571Labels = Sparse.eval nodeValue2571 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2571) = mixedMoment B node2571 node2571Labels := rfl
  simpa [nodeValue2571, Sparse.eval] using hc.symm

theorem sound2587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2587 node2587Labels = Sparse.eval nodeValue2587 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2587) = mixedMoment B node2587 node2587Labels := rfl
  simpa [nodeValue2587, Sparse.eval] using hc.symm

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

theorem sound2739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2739 node2739Labels = Sparse.eval nodeValue2739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2739) = mixedMoment B node2739 node2739Labels := rfl
  simpa [nodeValue2739, Sparse.eval] using hc.symm

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

theorem sound2763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2763 node2763Labels = Sparse.eval nodeValue2763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2763) = mixedMoment B node2763 node2763Labels := rfl
  simpa [nodeValue2763, Sparse.eval] using hc.symm

theorem sound2764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2764 node2764Labels = Sparse.eval nodeValue2764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2764) = mixedMoment B node2764 node2764Labels := rfl
  simpa [nodeValue2764, Sparse.eval] using hc.symm

theorem sound2782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2782 node2782Labels = Sparse.eval nodeValue2782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2782) = mixedMoment B node2782 node2782Labels := rfl
  simpa [nodeValue2782, Sparse.eval] using hc.symm

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

theorem sound3149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3149 node3149Labels = Sparse.eval nodeValue3149 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3149) = mixedMoment B node3149 node3149Labels := rfl
  simpa [nodeValue3149, Sparse.eval] using hc.symm

theorem sound3150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3150 node3150Labels = Sparse.eval nodeValue3150 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3150) = mixedMoment B node3150 node3150Labels := rfl
  simpa [nodeValue3150, Sparse.eval] using hc.symm

theorem sound3155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3155 node3155Labels = Sparse.eval nodeValue3155 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3155) = mixedMoment B node3155 node3155Labels := rfl
  simpa [nodeValue3155, Sparse.eval] using hc.symm

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

theorem sound3373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3373 node3373Labels = Sparse.eval nodeValue3373 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3373) = mixedMoment B node3373 node3373Labels := rfl
  simpa [nodeValue3373, Sparse.eval] using hc.symm

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

theorem sound3500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3500 node3500Labels = Sparse.eval nodeValue3500 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3500) = mixedMoment B node3500 node3500Labels := rfl
  simpa [nodeValue3500, Sparse.eval] using hc.symm

theorem sound3505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3505 node3505Labels = Sparse.eval nodeValue3505 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3505) = mixedMoment B node3505 node3505Labels := rfl
  simpa [nodeValue3505, Sparse.eval] using hc.symm

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

theorem sound3534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3534 node3534Labels = Sparse.eval nodeValue3534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3534) = mixedMoment B node3534 node3534Labels := rfl
  simpa [nodeValue3534, Sparse.eval] using hc.symm

theorem sound3573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3573 node3573Labels = Sparse.eval nodeValue3573 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3573) = mixedMoment B node3573 node3573Labels := rfl
  simpa [nodeValue3573, Sparse.eval] using hc.symm

theorem sound3581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3581 node3581Labels = Sparse.eval nodeValue3581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3581) = mixedMoment B node3581 node3581Labels := rfl
  simpa [nodeValue3581, Sparse.eval] using hc.symm

theorem sound3583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3583 node3583Labels = Sparse.eval nodeValue3583 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3583) = mixedMoment B node3583 node3583Labels := rfl
  simpa [nodeValue3583, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3628 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3628 node3628Labels = 0 := by
  exact mixedMoment_order_one B hB node3628 node3628Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound3623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3623 node3623Labels = Sparse.eval nodeValue3623 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3623) = mixedMoment B node3623 node3623Labels := rfl
  simpa [nodeValue3623, Sparse.eval] using hc.symm

theorem sound3628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3628 node3628Labels = Sparse.eval nodeValue3628 (mixedVector B) := by
  simpa only [nodeValue3628, Sparse.eval_nil] using zero3628 B _hB _hF

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

theorem sound3813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3813 node3813Labels = Sparse.eval nodeValue3813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3813) = mixedMoment B node3813 node3813Labels := rfl
  simpa [nodeValue3813, Sparse.eval] using hc.symm

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

theorem sound3848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3848 node3848Labels = Sparse.eval nodeValue3848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3848) = mixedMoment B node3848 node3848Labels := rfl
  simpa [nodeValue3848, Sparse.eval] using hc.symm

theorem sound3884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3884 node3884Labels = Sparse.eval nodeValue3884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3884) = mixedMoment B node3884 node3884Labels := rfl
  simpa [nodeValue3884, Sparse.eval] using hc.symm

theorem sound3903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3903 node3903Labels = Sparse.eval nodeValue3903 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3903) = mixedMoment B node3903 node3903Labels := rfl
  simpa [nodeValue3903, Sparse.eval] using hc.symm

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

theorem sound3913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3913 node3913Labels = Sparse.eval nodeValue3913 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3913) = mixedMoment B node3913 node3913Labels := rfl
  simpa [nodeValue3913, Sparse.eval] using hc.symm

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

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

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

theorem sound4888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4888 node4888Labels = Sparse.eval nodeValue4888 (mixedVector B) := by
  have h := singleton4888 B _hB
  rw [sound2244 B _hB _hF, sound2262 B _hB _hF] at h
  norm_num [nodeValue4888, nodeValue2244, nodeValue2262, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4890 node4890Labels = Sparse.eval nodeValue4890 (mixedVector B) := by
  have h := singleton4890 B _hB
  rw [sound2247 B _hB _hF, sound2290 B _hB _hF] at h
  norm_num [nodeValue4890, nodeValue2247, nodeValue2290, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4895 node4895Labels = Sparse.eval nodeValue4895 (mixedVector B) := by
  simpa only [nodeValue4895, Sparse.eval_nil] using zero4895 B _hB _hF

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

theorem sound5256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5256 node5256Labels = Sparse.eval nodeValue5256 (mixedVector B) := by
  simpa only [nodeValue5256, Sparse.eval_nil] using zero5256 B _hB _hF

theorem sound5270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5270 node5270Labels = Sparse.eval nodeValue5270 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5270) = mixedMoment B node5270 node5270Labels := rfl
  simpa [nodeValue5270, Sparse.eval] using hc.symm

theorem sound5271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5271 node5271Labels = Sparse.eval nodeValue5271 (mixedVector B) := by
  have h := singleton5271 B _hB
  rw [sound2739 B _hB _hF, sound3534 B _hB _hF] at h
  norm_num [nodeValue5271, nodeValue2739, nodeValue3534, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5289 node5289Labels = Sparse.eval nodeValue5289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5289) = mixedMoment B node5289 node5289Labels := rfl
  simpa [nodeValue5289, Sparse.eval] using hc.symm

theorem sound5290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5290 node5290Labels = Sparse.eval nodeValue5290 (mixedVector B) := by
  have h := singleton5290 B _hB
  rw [sound2764 B _hB _hF, sound3581 B _hB _hF] at h
  norm_num [nodeValue5290, nodeValue2764, nodeValue3581, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5295 node5295Labels = Sparse.eval nodeValue5295 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5295) = mixedMoment B node5295 node5295Labels := rfl
  simpa [nodeValue5295, Sparse.eval] using hc.symm

theorem sound5304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5304 node5304Labels = Sparse.eval nodeValue5304 (mixedVector B) := by
  have h := singleton5304 B _hB
  rw [sound2782 B _hB _hF, sound3583 B _hB _hF] at h
  norm_num [nodeValue5304, nodeValue2782, nodeValue3583, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources22
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq719 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm719 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA719 + difference 0 1) (sourceB719 + difference 1 0) sourceC719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3378) := by
    have ha : (tripleCharges (sourceA719 + difference 0 1) (sourceB719 + difference 1 0) sourceC719) = raw12064 := by
      apply Matrix.ext; unfold tripleCharges sourceA719 sourceB719 sourceC719 difference raw12064; decide +kernel
    rw [ha]
    exact (canonical12064 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA719 + difference 1 1) (sourceB719 + difference 1 1) sourceC719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA719 + difference 1 1) (sourceB719 + difference 1 1) sourceC719) = raw11764 := by
      apply Matrix.ext; unfold tripleCharges sourceA719 sourceB719 sourceC719 difference raw11764; decide +kernel
    rw [ha]
    exact (canonical11764 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA719 + difference 2 1) (sourceB719 + difference 1 2) sourceC719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3150) := by
    have ha : (tripleCharges (sourceA719 + difference 2 1) (sourceB719 + difference 1 2) sourceC719) = raw12068 := by
      apply Matrix.ext; unfold tripleCharges sourceA719 sourceB719 sourceC719 difference raw12068; decide +kernel
    rw [ha]
    exact (canonical12068 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA719 + difference 3 1) (sourceB719 + difference 1 3) sourceC719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3378) := by
    have ha : (tripleCharges (sourceA719 + difference 3 1) (sourceB719 + difference 1 3) sourceC719) = raw12069 := by
      apply Matrix.ext; unfold tripleCharges sourceA719 sourceB719 sourceC719 difference raw12069; decide +kernel
    rw [ha]
    exact (canonical12069 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA719 + difference 4 1) (sourceB719 + difference 1 4) sourceC719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3378) := by
    have ha : (tripleCharges (sourceA719 + difference 4 1) (sourceB719 + difference 1 4) sourceC719) = raw12070 := by
      apply Matrix.ext; unfold tripleCharges sourceA719 sourceB719 sourceC719 difference raw12070; decide +kernel
    rw [ha]
    exact (canonical12070 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA719 + difference 5 1) (sourceB719 + difference 1 5) sourceC719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3373) := by
    have ha : (tripleCharges (sourceA719 + difference 5 1) (sourceB719 + difference 1 5) sourceC719) = raw11757 := by
      apply Matrix.ext; unfold tripleCharges sourceA719 sourceB719 sourceC719 difference raw11757; decide +kernel
    rw [ha]
    exact (canonical11757 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA719 + sourceB719) sourceC719) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA719 + sourceB719) sourceC719) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA719 sourceB719 sourceC719 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA719 sourceB719 sourceC719
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm719, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq720 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm720 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA720 + difference 2 0) (sourceB720 + difference 0 2) sourceC720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA720 + difference 2 0) (sourceB720 + difference 0 2) sourceC720) = raw12071 := by
      apply Matrix.ext; unfold tripleCharges sourceA720 sourceB720 sourceC720 difference raw12071; decide +kernel
    rw [ha]
    exact (canonical12071 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA720 + difference 2 1) (sourceB720 + difference 1 2) sourceC720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3150) := by
    have ha : (tripleCharges (sourceA720 + difference 2 1) (sourceB720 + difference 1 2) sourceC720) = raw12068 := by
      apply Matrix.ext; unfold tripleCharges sourceA720 sourceB720 sourceC720 difference raw12068; decide +kernel
    rw [ha]
    exact (canonical12068 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA720 + difference 2 2) (sourceB720 + difference 2 2) sourceC720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA720 + difference 2 2) (sourceB720 + difference 2 2) sourceC720) = raw11764 := by
      apply Matrix.ext; unfold tripleCharges sourceA720 sourceB720 sourceC720 difference raw11764; decide +kernel
    rw [ha]
    exact (canonical11764 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA720 + difference 2 3) (sourceB720 + difference 3 2) sourceC720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3149) := by
    have ha : (tripleCharges (sourceA720 + difference 2 3) (sourceB720 + difference 3 2) sourceC720) = raw12072 := by
      apply Matrix.ext; unfold tripleCharges sourceA720 sourceB720 sourceC720 difference raw12072; decide +kernel
    rw [ha]
    exact (canonical12072 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA720 + difference 2 4) (sourceB720 + difference 4 2) sourceC720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3149) := by
    have ha : (tripleCharges (sourceA720 + difference 2 4) (sourceB720 + difference 4 2) sourceC720) = raw12073 := by
      apply Matrix.ext; unfold tripleCharges sourceA720 sourceB720 sourceC720 difference raw12073; decide +kernel
    rw [ha]
    exact (canonical12073 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA720 + difference 2 5) (sourceB720 + difference 5 2) sourceC720) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3155) := by
    have ha : (tripleCharges (sourceA720 + difference 2 5) (sourceB720 + difference 5 2) sourceC720) = raw12074 := by
      apply Matrix.ext; unfold tripleCharges sourceA720 sourceB720 sourceC720 difference raw12074; decide +kernel
    rw [ha]
    exact (canonical12074 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA720 + sourceB720) sourceC720) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA720 + sourceB720) sourceC720) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA720 sourceB720 sourceC720 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA720 sourceB720 sourceC720
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm720, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq721 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm721 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA721 + difference 3 0) (sourceB721 + difference 0 3) sourceC721) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2023) := by
    have ha : (tripleCharges (sourceA721 + difference 3 0) (sourceB721 + difference 0 3) sourceC721) = raw12075 := by
      apply Matrix.ext; unfold tripleCharges sourceA721 sourceB721 sourceC721 difference raw12075; decide +kernel
    rw [ha]
    exact (canonical12075 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA721 + difference 3 1) (sourceB721 + difference 1 3) sourceC721) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3378) := by
    have ha : (tripleCharges (sourceA721 + difference 3 1) (sourceB721 + difference 1 3) sourceC721) = raw12069 := by
      apply Matrix.ext; unfold tripleCharges sourceA721 sourceB721 sourceC721 difference raw12069; decide +kernel
    rw [ha]
    exact (canonical12069 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA721 + difference 3 2) (sourceB721 + difference 2 3) sourceC721) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA721 + difference 3 2) (sourceB721 + difference 2 3) sourceC721) = raw11768 := by
      apply Matrix.ext; unfold tripleCharges sourceA721 sourceB721 sourceC721 difference raw11768; decide +kernel
    rw [ha]
    exact (canonical11768 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA721 + difference 3 3) (sourceB721 + difference 3 3) sourceC721) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA721 + difference 3 3) (sourceB721 + difference 3 3) sourceC721) = raw11764 := by
      apply Matrix.ext; unfold tripleCharges sourceA721 sourceB721 sourceC721 difference raw11764; decide +kernel
    rw [ha]
    exact (canonical11764 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA721 + difference 3 4) (sourceB721 + difference 4 3) sourceC721) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3505) := by
    have ha : (tripleCharges (sourceA721 + difference 3 4) (sourceB721 + difference 4 3) sourceC721) = raw12076 := by
      apply Matrix.ext; unfold tripleCharges sourceA721 sourceB721 sourceC721 difference raw12076; decide +kernel
    rw [ha]
    exact (canonical12076 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA721 + difference 3 5) (sourceB721 + difference 5 3) sourceC721) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA721 + difference 3 5) (sourceB721 + difference 5 3) sourceC721) = raw12077 := by
      apply Matrix.ext; unfold tripleCharges sourceA721 sourceB721 sourceC721 difference raw12077; decide +kernel
    rw [ha]
    exact (canonical12077 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA721 + sourceB721) sourceC721) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA721 + sourceB721) sourceC721) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA721 sourceB721 sourceC721 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA721 sourceB721 sourceC721
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm721, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq722 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm722 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA722 + difference 0 3) (sourceB722 + difference 3 0) sourceC722) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA722 + difference 0 3) (sourceB722 + difference 3 0) sourceC722) = raw12065 := by
      apply Matrix.ext; unfold tripleCharges sourceA722 sourceB722 sourceC722 difference raw12065; decide +kernel
    rw [ha]
    exact (canonical12065 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA722 + difference 1 3) (sourceB722 + difference 3 1) sourceC722) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA722 + difference 1 3) (sourceB722 + difference 3 1) sourceC722) = raw12078 := by
      apply Matrix.ext; unfold tripleCharges sourceA722 sourceB722 sourceC722 difference raw12078; decide +kernel
    rw [ha]
    exact (canonical12078 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA722 + difference 2 3) (sourceB722 + difference 3 2) sourceC722) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3149) := by
    have ha : (tripleCharges (sourceA722 + difference 2 3) (sourceB722 + difference 3 2) sourceC722) = raw12072 := by
      apply Matrix.ext; unfold tripleCharges sourceA722 sourceB722 sourceC722 difference raw12072; decide +kernel
    rw [ha]
    exact (canonical12072 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA722 + difference 3 3) (sourceB722 + difference 3 3) sourceC722) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA722 + difference 3 3) (sourceB722 + difference 3 3) sourceC722) = raw11764 := by
      apply Matrix.ext; unfold tripleCharges sourceA722 sourceB722 sourceC722 difference raw11764; decide +kernel
    rw [ha]
    exact (canonical11764 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA722 + difference 4 3) (sourceB722 + difference 3 4) sourceC722) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3505) := by
    have ha : (tripleCharges (sourceA722 + difference 4 3) (sourceB722 + difference 3 4) sourceC722) = raw12079 := by
      apply Matrix.ext; unfold tripleCharges sourceA722 sourceB722 sourceC722 difference raw12079; decide +kernel
    rw [ha]
    exact (canonical12079 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA722 + difference 5 3) (sourceB722 + difference 3 5) sourceC722) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3500) := by
    have ha : (tripleCharges (sourceA722 + difference 5 3) (sourceB722 + difference 3 5) sourceC722) = raw11762 := by
      apply Matrix.ext; unfold tripleCharges sourceA722 sourceB722 sourceC722 difference raw11762; decide +kernel
    rw [ha]
    exact (canonical11762 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA722 + sourceB722) sourceC722) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA722 + sourceB722) sourceC722) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA722 sourceB722 sourceC722 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA722 sourceB722 sourceC722
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm722, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq727 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm727 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA727 + difference 0 1) (sourceB727 + difference 1 0) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA727 + difference 0 1) (sourceB727 + difference 1 0) sourceC727) = raw11661 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw11661; decide +kernel
    rw [ha]
    exact (canonical11661 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA727 + difference 0 2) (sourceB727 + difference 2 0) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA727 + difference 0 2) (sourceB727 + difference 2 0) sourceC727) = raw12183 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12183; decide +kernel
    rw [ha]
    exact (canonical12183 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA727 + difference 0 3) (sourceB727 + difference 3 0) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA727 + difference 0 3) (sourceB727 + difference 3 0) sourceC727) = raw12184 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12184; decide +kernel
    rw [ha]
    exact (canonical12184 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA727 + difference 0 4) (sourceB727 + difference 4 0) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA727 + difference 0 4) (sourceB727 + difference 4 0) sourceC727) = raw12185 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12185; decide +kernel
    rw [ha]
    exact (canonical12185 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA727 + difference 0 5) (sourceB727 + difference 5 0) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA727 + difference 0 5) (sourceB727 + difference 5 0) sourceC727) = raw12186 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12186; decide +kernel
    rw [ha]
    exact (canonical12186 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA727 + difference 1 0) (sourceB727 + difference 0 1) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA727 + difference 1 0) (sourceB727 + difference 0 1) sourceC727) = raw12187 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12187; decide +kernel
    rw [ha]
    exact (canonical12187 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA727 + difference 1 2) (sourceB727 + difference 2 1) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA727 + difference 1 2) (sourceB727 + difference 2 1) sourceC727) = raw12188 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12188; decide +kernel
    rw [ha]
    exact (canonical12188 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA727 + difference 1 3) (sourceB727 + difference 3 1) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA727 + difference 1 3) (sourceB727 + difference 3 1) sourceC727) = raw12189 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12189; decide +kernel
    rw [ha]
    exact (canonical12189 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA727 + difference 1 4) (sourceB727 + difference 4 1) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA727 + difference 1 4) (sourceB727 + difference 4 1) sourceC727) = raw12190 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12190; decide +kernel
    rw [ha]
    exact (canonical12190 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA727 + difference 1 5) (sourceB727 + difference 5 1) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA727 + difference 1 5) (sourceB727 + difference 5 1) sourceC727) = raw12191 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12191; decide +kernel
    rw [ha]
    exact (canonical12191 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA727 + difference 2 0) (sourceB727 + difference 0 2) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA727 + difference 2 0) (sourceB727 + difference 0 2) sourceC727) = raw11665 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw11665; decide +kernel
    rw [ha]
    exact (canonical11665 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA727 + difference 2 1) (sourceB727 + difference 1 2) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA727 + difference 2 1) (sourceB727 + difference 1 2) sourceC727) = raw12019 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12019; decide +kernel
    rw [ha]
    exact (canonical12019 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA727 + difference 2 3) (sourceB727 + difference 3 2) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA727 + difference 2 3) (sourceB727 + difference 3 2) sourceC727) = raw11667 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw11667; decide +kernel
    rw [ha]
    exact (canonical11667 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA727 + difference 2 4) (sourceB727 + difference 4 2) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA727 + difference 2 4) (sourceB727 + difference 4 2) sourceC727) = raw11668 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw11668; decide +kernel
    rw [ha]
    exact (canonical11668 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA727 + difference 2 5) (sourceB727 + difference 5 2) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA727 + difference 2 5) (sourceB727 + difference 5 2) sourceC727) = raw11669 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw11669; decide +kernel
    rw [ha]
    exact (canonical11669 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA727 + difference 3 0) (sourceB727 + difference 0 3) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA727 + difference 3 0) (sourceB727 + difference 0 3) sourceC727) = raw12192 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12192; decide +kernel
    rw [ha]
    exact (canonical12192 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA727 + difference 3 1) (sourceB727 + difference 1 3) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA727 + difference 3 1) (sourceB727 + difference 1 3) sourceC727) = raw11677 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw11677; decide +kernel
    rw [ha]
    exact (canonical11677 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA727 + difference 3 2) (sourceB727 + difference 2 3) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA727 + difference 3 2) (sourceB727 + difference 2 3) sourceC727) = raw12193 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12193; decide +kernel
    rw [ha]
    exact (canonical12193 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA727 + difference 3 4) (sourceB727 + difference 4 3) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA727 + difference 3 4) (sourceB727 + difference 4 3) sourceC727) = raw12194 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12194; decide +kernel
    rw [ha]
    exact (canonical12194 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA727 + difference 3 5) (sourceB727 + difference 5 3) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA727 + difference 3 5) (sourceB727 + difference 5 3) sourceC727) = raw12195 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12195; decide +kernel
    rw [ha]
    exact (canonical12195 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA727 + difference 4 0) (sourceB727 + difference 0 4) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA727 + difference 4 0) (sourceB727 + difference 0 4) sourceC727) = raw12196 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12196; decide +kernel
    rw [ha]
    exact (canonical12196 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA727 + difference 4 1) (sourceB727 + difference 1 4) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA727 + difference 4 1) (sourceB727 + difference 1 4) sourceC727) = raw11682 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw11682; decide +kernel
    rw [ha]
    exact (canonical11682 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA727 + difference 4 2) (sourceB727 + difference 2 4) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA727 + difference 4 2) (sourceB727 + difference 2 4) sourceC727) = raw12197 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12197; decide +kernel
    rw [ha]
    exact (canonical12197 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA727 + difference 4 3) (sourceB727 + difference 3 4) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA727 + difference 4 3) (sourceB727 + difference 3 4) sourceC727) = raw12198 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12198; decide +kernel
    rw [ha]
    exact (canonical12198 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA727 + difference 4 5) (sourceB727 + difference 5 4) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA727 + difference 4 5) (sourceB727 + difference 5 4) sourceC727) = raw12199 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12199; decide +kernel
    rw [ha]
    exact (canonical12199 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA727 + difference 5 0) (sourceB727 + difference 0 5) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA727 + difference 5 0) (sourceB727 + difference 0 5) sourceC727) = raw12200 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12200; decide +kernel
    rw [ha]
    exact (canonical12200 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA727 + difference 5 1) (sourceB727 + difference 1 5) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA727 + difference 5 1) (sourceB727 + difference 1 5) sourceC727) = raw11687 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw11687; decide +kernel
    rw [ha]
    exact (canonical11687 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA727 + difference 5 2) (sourceB727 + difference 2 5) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA727 + difference 5 2) (sourceB727 + difference 2 5) sourceC727) = raw12201 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12201; decide +kernel
    rw [ha]
    exact (canonical12201 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA727 + difference 5 3) (sourceB727 + difference 3 5) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA727 + difference 5 3) (sourceB727 + difference 3 5) sourceC727) = raw12202 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12202; decide +kernel
    rw [ha]
    exact (canonical12202 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA727 + difference 5 4) (sourceB727 + difference 4 5) sourceC727) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA727 + difference 5 4) (sourceB727 + difference 4 5) sourceC727) = raw12203 := by
      apply Matrix.ext; unfold tripleCharges sourceA727 sourceB727 sourceC727 difference raw12203; decide +kernel
    rw [ha]
    exact (canonical12203 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA727 sourceB727 sourceC727
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm727, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq729 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm729 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA729 + difference 0 0) (sourceB729 + difference 0 0) sourceC729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3623) := by
    have ha : (tripleCharges (sourceA729 + difference 0 0) (sourceB729 + difference 0 0) sourceC729) = raw12225 := by
      apply Matrix.ext; unfold tripleCharges sourceA729 sourceB729 sourceC729 difference raw12225; decide +kernel
    rw [ha]
    exact (canonical12225 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA729 + difference 0 1) (sourceB729 + difference 1 0) sourceC729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA729 + difference 0 1) (sourceB729 + difference 1 0) sourceC729) = raw11752 := by
      apply Matrix.ext; unfold tripleCharges sourceA729 sourceB729 sourceC729 difference raw11752; decide +kernel
    rw [ha]
    exact (canonical11752 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA729 + difference 0 2) (sourceB729 + difference 2 0) sourceC729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA729 + difference 0 2) (sourceB729 + difference 2 0) sourceC729) = raw12226 := by
      apply Matrix.ext; unfold tripleCharges sourceA729 sourceB729 sourceC729 difference raw12226; decide +kernel
    rw [ha]
    exact (canonical12226 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA729 + difference 0 3) (sourceB729 + difference 3 0) sourceC729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA729 + difference 0 3) (sourceB729 + difference 3 0) sourceC729) = raw12227 := by
      apply Matrix.ext; unfold tripleCharges sourceA729 sourceB729 sourceC729 difference raw12227; decide +kernel
    rw [ha]
    exact (canonical12227 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA729 + difference 0 4) (sourceB729 + difference 4 0) sourceC729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA729 + difference 0 4) (sourceB729 + difference 4 0) sourceC729) = raw12228 := by
      apply Matrix.ext; unfold tripleCharges sourceA729 sourceB729 sourceC729 difference raw12228; decide +kernel
    rw [ha]
    exact (canonical12228 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA729 + difference 0 5) (sourceB729 + difference 5 0) sourceC729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3628) := by
    have ha : (tripleCharges (sourceA729 + difference 0 5) (sourceB729 + difference 5 0) sourceC729) = raw12229 := by
      apply Matrix.ext; unfold tripleCharges sourceA729 sourceB729 sourceC729 difference raw12229; decide +kernel
    rw [ha]
    exact (canonical12229 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA729 + sourceB729) sourceC729) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA729 + sourceB729) sourceC729) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA729 sourceB729 sourceC729 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA729 sourceB729 sourceC729
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm729, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq733 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm733 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA733 + difference 0 0) (sourceB733 + difference 0 0) sourceC733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA733 + difference 0 0) (sourceB733 + difference 0 0) sourceC733) = raw12320 := by
      apply Matrix.ext; unfold tripleCharges sourceA733 sourceB733 sourceC733 difference raw12320; decide +kernel
    rw [ha]
    exact (canonical12320 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA733 + difference 0 1) (sourceB733 + difference 1 0) sourceC733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA733 + difference 0 1) (sourceB733 + difference 1 0) sourceC733) = raw12321 := by
      apply Matrix.ext; unfold tripleCharges sourceA733 sourceB733 sourceC733 difference raw12321; decide +kernel
    rw [ha]
    exact (canonical12321 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA733 + difference 0 2) (sourceB733 + difference 2 0) sourceC733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA733 + difference 0 2) (sourceB733 + difference 2 0) sourceC733) = raw12322 := by
      apply Matrix.ext; unfold tripleCharges sourceA733 sourceB733 sourceC733 difference raw12322; decide +kernel
    rw [ha]
    exact (canonical12322 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA733 + difference 0 3) (sourceB733 + difference 3 0) sourceC733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3903) := by
    have ha : (tripleCharges (sourceA733 + difference 0 3) (sourceB733 + difference 3 0) sourceC733) = raw12323 := by
      apply Matrix.ext; unfold tripleCharges sourceA733 sourceB733 sourceC733 difference raw12323; decide +kernel
    rw [ha]
    exact (canonical12323 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA733 + difference 0 4) (sourceB733 + difference 4 0) sourceC733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3913) := by
    have ha : (tripleCharges (sourceA733 + difference 0 4) (sourceB733 + difference 4 0) sourceC733) = raw12324 := by
      apply Matrix.ext; unfold tripleCharges sourceA733 sourceB733 sourceC733 difference raw12324; decide +kernel
    rw [ha]
    exact (canonical12324 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA733 + difference 0 5) (sourceB733 + difference 5 0) sourceC733) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA733 + difference 0 5) (sourceB733 + difference 5 0) sourceC733) = raw12325 := by
      apply Matrix.ext; unfold tripleCharges sourceA733 sourceB733 sourceC733 difference raw12325; decide +kernel
    rw [ha]
    exact (canonical12325 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA733 + sourceB733) sourceC733) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA733 + sourceB733) sourceC733) = raw12326 := by
      apply Matrix.ext; unfold doubleCharges sourceA733 sourceB733 sourceC733 raw12326; decide +kernel
    rw [ha]
    exact (canonical12326 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA733 sourceB733 sourceC733
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm733, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq734 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm734 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA734 + difference 0 0) (sourceB734 + difference 0 0) sourceC734) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA734 + difference 0 0) (sourceB734 + difference 0 0) sourceC734) = raw12320 := by
      apply Matrix.ext; unfold tripleCharges sourceA734 sourceB734 sourceC734 difference raw12320; decide +kernel
    rw [ha]
    exact (canonical12320 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA734 + difference 1 0) (sourceB734 + difference 0 1) sourceC734) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1259) := by
    have ha : (tripleCharges (sourceA734 + difference 1 0) (sourceB734 + difference 0 1) sourceC734) = raw12327 := by
      apply Matrix.ext; unfold tripleCharges sourceA734 sourceB734 sourceC734 difference raw12327; decide +kernel
    rw [ha]
    exact (canonical12327 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA734 + difference 2 0) (sourceB734 + difference 0 2) sourceC734) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA734 + difference 2 0) (sourceB734 + difference 0 2) sourceC734) = raw12328 := by
      apply Matrix.ext; unfold tripleCharges sourceA734 sourceB734 sourceC734 difference raw12328; decide +kernel
    rw [ha]
    exact (canonical12328 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA734 + difference 3 0) (sourceB734 + difference 0 3) sourceC734) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1268) := by
    have ha : (tripleCharges (sourceA734 + difference 3 0) (sourceB734 + difference 0 3) sourceC734) = raw12329 := by
      apply Matrix.ext; unfold tripleCharges sourceA734 sourceB734 sourceC734 difference raw12329; decide +kernel
    rw [ha]
    exact (canonical12329 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA734 + difference 4 0) (sourceB734 + difference 0 4) sourceC734) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1263) := by
    have ha : (tripleCharges (sourceA734 + difference 4 0) (sourceB734 + difference 0 4) sourceC734) = raw12330 := by
      apply Matrix.ext; unfold tripleCharges sourceA734 sourceB734 sourceC734 difference raw12330; decide +kernel
    rw [ha]
    exact (canonical12330 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA734 + difference 5 0) (sourceB734 + difference 0 5) sourceC734) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1261) := by
    have ha : (tripleCharges (sourceA734 + difference 5 0) (sourceB734 + difference 0 5) sourceC734) = raw12331 := by
      apply Matrix.ext; unfold tripleCharges sourceA734 sourceB734 sourceC734 difference raw12331; decide +kernel
    rw [ha]
    exact (canonical12331 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA734 + sourceB734) sourceC734) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA734 + sourceB734) sourceC734) = raw12326 := by
      apply Matrix.ext; unfold doubleCharges sourceA734 sourceB734 sourceC734 raw12326; decide +kernel
    rw [ha]
    exact (canonical12326 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA734 sourceB734 sourceC734
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm734, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq735 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm735 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA735 + difference 0 1) (sourceB735 + difference 1 0) sourceC735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA735 + difference 0 1) (sourceB735 + difference 1 0) sourceC735) = raw12321 := by
      apply Matrix.ext; unfold tripleCharges sourceA735 sourceB735 sourceC735 difference raw12321; decide +kernel
    rw [ha]
    exact (canonical12321 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA735 + difference 1 1) (sourceB735 + difference 1 1) sourceC735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA735 + difference 1 1) (sourceB735 + difference 1 1) sourceC735) = raw12320 := by
      apply Matrix.ext; unfold tripleCharges sourceA735 sourceB735 sourceC735 difference raw12320; decide +kernel
    rw [ha]
    exact (canonical12320 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA735 + difference 2 1) (sourceB735 + difference 1 2) sourceC735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2587) := by
    have ha : (tripleCharges (sourceA735 + difference 2 1) (sourceB735 + difference 1 2) sourceC735) = raw12332 := by
      apply Matrix.ext; unfold tripleCharges sourceA735 sourceB735 sourceC735 difference raw12332; decide +kernel
    rw [ha]
    exact (canonical12332 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA735 + difference 3 1) (sourceB735 + difference 1 3) sourceC735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2571) := by
    have ha : (tripleCharges (sourceA735 + difference 3 1) (sourceB735 + difference 1 3) sourceC735) = raw12333 := by
      apply Matrix.ext; unfold tripleCharges sourceA735 sourceB735 sourceC735 difference raw12333; decide +kernel
    rw [ha]
    exact (canonical12333 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA735 + difference 4 1) (sourceB735 + difference 1 4) sourceC735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2568) := by
    have ha : (tripleCharges (sourceA735 + difference 4 1) (sourceB735 + difference 1 4) sourceC735) = raw12334 := by
      apply Matrix.ext; unfold tripleCharges sourceA735 sourceB735 sourceC735 difference raw12334; decide +kernel
    rw [ha]
    exact (canonical12334 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA735 + difference 5 1) (sourceB735 + difference 1 5) sourceC735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2566) := by
    have ha : (tripleCharges (sourceA735 + difference 5 1) (sourceB735 + difference 1 5) sourceC735) = raw12335 := by
      apply Matrix.ext; unfold tripleCharges sourceA735 sourceB735 sourceC735 difference raw12335; decide +kernel
    rw [ha]
    exact (canonical12335 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA735 + sourceB735) sourceC735) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA735 + sourceB735) sourceC735) = raw12326 := by
      apply Matrix.ext; unfold doubleCharges sourceA735 sourceB735 sourceC735 raw12326; decide +kernel
    rw [ha]
    exact (canonical12326 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA735 sourceB735 sourceC735
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm735, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck624 : Integer.Sparse.reindex keyMap MixedData.row624 = numericRow624 := by decide +kernel

theorem numericCheck624 (x : Master → ℝ) : Integer.Sparse.eval numericRow624 x =
    (1 : ℝ) * reducedSource624 x := by
  norm_num [numericRow624, reducedSource624, Integer.Sparse.eval, Sparse.eval, nodeValue3150, nodeValue3373, nodeValue3378, nodeValue3526, nodeValue4083]

theorem reindexCheck625 : Integer.Sparse.reindex keyMap MixedData.row625 = numericRow625 := by decide +kernel

theorem numericCheck625 (x : Master → ℝ) : Integer.Sparse.eval numericRow625 x =
    (1 : ℝ) * reducedSource625 x := by
  norm_num [numericRow625, reducedSource625, Integer.Sparse.eval, Sparse.eval, nodeValue2010, nodeValue3149, nodeValue3150, nodeValue3155, nodeValue3526, nodeValue4083]

theorem reindexCheck626 : Integer.Sparse.reindex keyMap MixedData.row626 = numericRow626 := by decide +kernel

theorem numericCheck626 (x : Master → ℝ) : Integer.Sparse.eval numericRow626 x =
    (1 : ℝ) * reducedSource626 x := by
  norm_num [numericRow626, reducedSource626, Integer.Sparse.eval, Sparse.eval, nodeValue2023, nodeValue3378, nodeValue3505, nodeValue3526, nodeValue3532, nodeValue4083]

theorem reindexCheck627 : Integer.Sparse.reindex keyMap MixedData.row627 = numericRow627 := by decide +kernel

theorem numericCheck627 (x : Master → ℝ) : Integer.Sparse.eval numericRow627 x =
    (1 : ℝ) * reducedSource627 x := by
  norm_num [numericRow627, reducedSource627, Integer.Sparse.eval, Sparse.eval, nodeValue3149, nodeValue3376, nodeValue3500, nodeValue3505, nodeValue3526, nodeValue3573, nodeValue4083]

theorem reindexCheck632 : Integer.Sparse.reindex keyMap MixedData.row632 = numericRow632 := by decide +kernel

theorem numericCheck632 (x : Master → ℝ) : Integer.Sparse.eval numericRow632 x =
    (8640 : ℝ) * reducedSource632 x := by
  norm_num [numericRow632, reducedSource632, Integer.Sparse.eval, Sparse.eval, nodeValue4888, nodeValue4890, nodeValue4895, nodeValue5256, nodeValue5270, nodeValue5271, nodeValue5289, nodeValue5290, nodeValue5292, nodeValue5295, nodeValue5304, nodeValue5307]
  ring

theorem reindexCheck634 : Integer.Sparse.reindex keyMap MixedData.row634 = numericRow634 := by decide +kernel

theorem numericCheck634 (x : Master → ℝ) : Integer.Sparse.eval numericRow634 x =
    (1 : ℝ) * reducedSource634 x := by
  norm_num [numericRow634, reducedSource634, Integer.Sparse.eval, Sparse.eval, nodeValue3581, nodeValue3583, nodeValue3623, nodeValue3628, nodeValue4083]

theorem reindexCheck637 : Integer.Sparse.reindex keyMap MixedData.row637 = numericRow637 := by decide +kernel

theorem numericCheck637 (x : Master → ℝ) : Integer.Sparse.eval numericRow637 x =
    (1 : ℝ) * reducedSource637 x := by
  norm_num [numericRow637, reducedSource637, Integer.Sparse.eval, Sparse.eval, nodeValue2763, nodeValue3813, nodeValue3848, nodeValue3884, nodeValue3903, nodeValue3913, nodeValue4092]

theorem reindexCheck638 : Integer.Sparse.reindex keyMap MixedData.row638 = numericRow638 := by decide +kernel

theorem numericCheck638 (x : Master → ℝ) : Integer.Sparse.eval numericRow638 x =
    (1 : ℝ) * reducedSource638 x := by
  norm_num [numericRow638, reducedSource638, Integer.Sparse.eval, Sparse.eval, nodeValue1259, nodeValue1261, nodeValue1263, nodeValue1268, nodeValue1291, nodeValue2763, nodeValue4092]

theorem reindexCheck639 : Integer.Sparse.reindex keyMap MixedData.row639 = numericRow639 := by decide +kernel

theorem numericCheck639 (x : Master → ℝ) : Integer.Sparse.eval numericRow639 x =
    (1 : ℝ) * reducedSource639 x := by
  norm_num [numericRow639, reducedSource639, Integer.Sparse.eval, Sparse.eval, nodeValue2566, nodeValue2568, nodeValue2571, nodeValue2587, nodeValue2763, nodeValue3848, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero624 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource624 (mixedVector B) = 0 := by
  have h3150 : mixedVector B (Sum.inr 3150) = Sparse.eval nodeValue3150 (mixedVector B) := by
    change mixedMoment B node3150 node3150Labels = _
    exact sound3150 B hB hF
  have h3373 : mixedVector B (Sum.inr 3373) = Sparse.eval nodeValue3373 (mixedVector B) := by
    change mixedMoment B node3373 node3373Labels = _
    exact sound3373 B hB hF
  have h3378 : mixedVector B (Sum.inr 3378) = Sparse.eval nodeValue3378 (mixedVector B) := by
    change mixedMoment B node3378 node3378Labels = _
    exact sound3378 B hB hF
  have h3526 : mixedVector B (Sum.inr 3526) = Sparse.eval nodeValue3526 (mixedVector B) := by
    change mixedMoment B node3526 node3526Labels = _
    exact sound3526 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm719, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3150, h3373, h3378, h3526, h4083, reducedSource624] using sourceEq719 B hB

theorem rowSound624 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row624 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck624, numericCheck624, reducedZero624 B hB hF, mul_zero]

theorem reducedZero625 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource625 (mixedVector B) = 0 := by
  have h2010 : mixedVector B (Sum.inr 2010) = Sparse.eval nodeValue2010 (mixedVector B) := by
    change mixedMoment B node2010 node2010Labels = _
    exact sound2010 B hB hF
  have h3149 : mixedVector B (Sum.inr 3149) = Sparse.eval nodeValue3149 (mixedVector B) := by
    change mixedMoment B node3149 node3149Labels = _
    exact sound3149 B hB hF
  have h3150 : mixedVector B (Sum.inr 3150) = Sparse.eval nodeValue3150 (mixedVector B) := by
    change mixedMoment B node3150 node3150Labels = _
    exact sound3150 B hB hF
  have h3155 : mixedVector B (Sum.inr 3155) = Sparse.eval nodeValue3155 (mixedVector B) := by
    change mixedMoment B node3155 node3155Labels = _
    exact sound3155 B hB hF
  have h3526 : mixedVector B (Sum.inr 3526) = Sparse.eval nodeValue3526 (mixedVector B) := by
    change mixedMoment B node3526 node3526Labels = _
    exact sound3526 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm720, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2010, h3149, h3150, h3155, h3526, h4083, reducedSource625] using sourceEq720 B hB

theorem rowSound625 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row625 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck625, numericCheck625, reducedZero625 B hB hF, mul_zero]

theorem reducedZero626 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource626 (mixedVector B) = 0 := by
  have h2023 : mixedVector B (Sum.inr 2023) = Sparse.eval nodeValue2023 (mixedVector B) := by
    change mixedMoment B node2023 node2023Labels = _
    exact sound2023 B hB hF
  have h3378 : mixedVector B (Sum.inr 3378) = Sparse.eval nodeValue3378 (mixedVector B) := by
    change mixedMoment B node3378 node3378Labels = _
    exact sound3378 B hB hF
  have h3505 : mixedVector B (Sum.inr 3505) = Sparse.eval nodeValue3505 (mixedVector B) := by
    change mixedMoment B node3505 node3505Labels = _
    exact sound3505 B hB hF
  have h3526 : mixedVector B (Sum.inr 3526) = Sparse.eval nodeValue3526 (mixedVector B) := by
    change mixedMoment B node3526 node3526Labels = _
    exact sound3526 B hB hF
  have h3532 : mixedVector B (Sum.inr 3532) = Sparse.eval nodeValue3532 (mixedVector B) := by
    change mixedMoment B node3532 node3532Labels = _
    exact sound3532 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm721, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2023, h3378, h3505, h3526, h3532, h4083, reducedSource626] using sourceEq721 B hB

theorem rowSound626 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row626 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck626, numericCheck626, reducedZero626 B hB hF, mul_zero]

theorem reducedZero627 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource627 (mixedVector B) = 0 := by
  have h3149 : mixedVector B (Sum.inr 3149) = Sparse.eval nodeValue3149 (mixedVector B) := by
    change mixedMoment B node3149 node3149Labels = _
    exact sound3149 B hB hF
  have h3376 : mixedVector B (Sum.inr 3376) = Sparse.eval nodeValue3376 (mixedVector B) := by
    change mixedMoment B node3376 node3376Labels = _
    exact sound3376 B hB hF
  have h3500 : mixedVector B (Sum.inr 3500) = Sparse.eval nodeValue3500 (mixedVector B) := by
    change mixedMoment B node3500 node3500Labels = _
    exact sound3500 B hB hF
  have h3505 : mixedVector B (Sum.inr 3505) = Sparse.eval nodeValue3505 (mixedVector B) := by
    change mixedMoment B node3505 node3505Labels = _
    exact sound3505 B hB hF
  have h3526 : mixedVector B (Sum.inr 3526) = Sparse.eval nodeValue3526 (mixedVector B) := by
    change mixedMoment B node3526 node3526Labels = _
    exact sound3526 B hB hF
  have h3573 : mixedVector B (Sum.inr 3573) = Sparse.eval nodeValue3573 (mixedVector B) := by
    change mixedMoment B node3573 node3573Labels = _
    exact sound3573 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm722, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3149, h3376, h3500, h3505, h3526, h3573, h4083, reducedSource627] using sourceEq722 B hB

theorem rowSound627 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row627 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck627, numericCheck627, reducedZero627 B hB hF, mul_zero]

theorem reducedZero632 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource632 (mixedVector B) = 0 := by
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  have h5256 : mixedVector B (Sum.inr 5256) = Sparse.eval nodeValue5256 (mixedVector B) := by
    change mixedMoment B node5256 node5256Labels = _
    exact sound5256 B hB hF
  have h5270 : mixedVector B (Sum.inr 5270) = Sparse.eval nodeValue5270 (mixedVector B) := by
    change mixedMoment B node5270 node5270Labels = _
    exact sound5270 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  have h5289 : mixedVector B (Sum.inr 5289) = Sparse.eval nodeValue5289 (mixedVector B) := by
    change mixedMoment B node5289 node5289Labels = _
    exact sound5289 B hB hF
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292_e B hB hF
  have h5295 : mixedVector B (Sum.inr 5295) = Sparse.eval nodeValue5295 (mixedVector B) := by
    change mixedMoment B node5295 node5295Labels = _
    exact sound5295 B hB hF
  have h5304 : mixedVector B (Sum.inr 5304) = Sparse.eval nodeValue5304 (mixedVector B) := by
    change mixedMoment B node5304 node5304Labels = _
    exact sound5304 B hB hF
  have h5307 : mixedVector B (Sum.inr 5307) = Sparse.eval nodeValue5307 (mixedVector B) := by
    change mixedMoment B node5307 node5307Labels = _
    exact sound5307 B hB hF
  simpa only [sourceForm727, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4888, h4890, h4895, h5256, h5270, h5271, h5289, h5290, h5292, h5295, h5304, h5307, reducedSource632] using sourceEq727 B hB

theorem rowSound632 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row632 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck632, numericCheck632, reducedZero632 B hB hF, mul_zero]

theorem reducedZero634 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource634 (mixedVector B) = 0 := by
  have h3581 : mixedVector B (Sum.inr 3581) = Sparse.eval nodeValue3581 (mixedVector B) := by
    change mixedMoment B node3581 node3581Labels = _
    exact sound3581 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  have h3623 : mixedVector B (Sum.inr 3623) = Sparse.eval nodeValue3623 (mixedVector B) := by
    change mixedMoment B node3623 node3623Labels = _
    exact sound3623 B hB hF
  have h3628 : mixedVector B (Sum.inr 3628) = Sparse.eval nodeValue3628 (mixedVector B) := by
    change mixedMoment B node3628 node3628Labels = _
    exact sound3628 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm729, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3581, h3583, h3623, h3628, h4083, reducedSource634] using sourceEq729 B hB

theorem rowSound634 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row634 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck634, numericCheck634, reducedZero634 B hB hF, mul_zero]

theorem reducedZero637 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource637 (mixedVector B) = 0 := by
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h3903 : mixedVector B (Sum.inr 3903) = Sparse.eval nodeValue3903 (mixedVector B) := by
    change mixedMoment B node3903 node3903Labels = _
    exact sound3903 B hB hF
  have h3913 : mixedVector B (Sum.inr 3913) = Sparse.eval nodeValue3913 (mixedVector B) := by
    change mixedMoment B node3913 node3913Labels = _
    exact sound3913 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm733, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2763, h3813, h3848, h3884, h3903, h3913, h4092, reducedSource637] using sourceEq733 B hB

theorem rowSound637 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row637 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck637, numericCheck637, reducedZero637 B hB hF, mul_zero]

theorem reducedZero638 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource638 (mixedVector B) = 0 := by
  have h1259 : mixedVector B (Sum.inr 1259) = Sparse.eval nodeValue1259 (mixedVector B) := by
    change mixedMoment B node1259 node1259Labels = _
    exact sound1259 B hB hF
  have h1261 : mixedVector B (Sum.inr 1261) = Sparse.eval nodeValue1261 (mixedVector B) := by
    change mixedMoment B node1261 node1261Labels = _
    exact sound1261 B hB hF
  have h1263 : mixedVector B (Sum.inr 1263) = Sparse.eval nodeValue1263 (mixedVector B) := by
    change mixedMoment B node1263 node1263Labels = _
    exact sound1263 B hB hF
  have h1268 : mixedVector B (Sum.inr 1268) = Sparse.eval nodeValue1268 (mixedVector B) := by
    change mixedMoment B node1268 node1268Labels = _
    exact sound1268 B hB hF
  have h1291 : mixedVector B (Sum.inr 1291) = Sparse.eval nodeValue1291 (mixedVector B) := by
    change mixedMoment B node1291 node1291Labels = _
    exact sound1291 B hB hF
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm734, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1259, h1261, h1263, h1268, h1291, h2763, h4092, reducedSource638] using sourceEq734 B hB

theorem rowSound638 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row638 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck638, numericCheck638, reducedZero638 B hB hF, mul_zero]

theorem reducedZero639 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource639 (mixedVector B) = 0 := by
  have h2566 : mixedVector B (Sum.inr 2566) = Sparse.eval nodeValue2566 (mixedVector B) := by
    change mixedMoment B node2566 node2566Labels = _
    exact sound2566 B hB hF
  have h2568 : mixedVector B (Sum.inr 2568) = Sparse.eval nodeValue2568 (mixedVector B) := by
    change mixedMoment B node2568 node2568Labels = _
    exact sound2568 B hB hF
  have h2571 : mixedVector B (Sum.inr 2571) = Sparse.eval nodeValue2571 (mixedVector B) := by
    change mixedMoment B node2571 node2571Labels = _
    exact sound2571 B hB hF
  have h2587 : mixedVector B (Sum.inr 2587) = Sparse.eval nodeValue2587 (mixedVector B) := by
    change mixedMoment B node2587 node2587Labels = _
    exact sound2587 B hB hF
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm735, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2566, h2568, h2571, h2587, h2763, h3848, h4092, reducedSource639] using sourceEq735 B hB

theorem rowSound639 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row639 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck639, numericCheck639, reducedZero639 B hB hF, mul_zero]

theorem sourceRowsAt624 : MixedData.sourceRows (624 : Fin 2425) =
    MixedData.row624 := by decide +kernel

theorem sourceRowsAt625 : MixedData.sourceRows (625 : Fin 2425) =
    MixedData.row625 := by decide +kernel

theorem sourceRowsAt626 : MixedData.sourceRows (626 : Fin 2425) =
    MixedData.row626 := by decide +kernel

theorem sourceRowsAt627 : MixedData.sourceRows (627 : Fin 2425) =
    MixedData.row627 := by decide +kernel

theorem sourceRowsAt628 : MixedData.sourceRows (628 : Fin 2425) =
    MixedData.row628 := by decide +kernel

theorem sourceRowsAt629 : MixedData.sourceRows (629 : Fin 2425) =
    MixedData.row629 := by decide +kernel

theorem sourceRowsAt630 : MixedData.sourceRows (630 : Fin 2425) =
    MixedData.row630 := by decide +kernel

theorem sourceRowsAt631 : MixedData.sourceRows (631 : Fin 2425) =
    MixedData.row631 := by decide +kernel

theorem sourceRowsAt632 : MixedData.sourceRows (632 : Fin 2425) =
    MixedData.row632 := by decide +kernel

theorem sourceRowsAt633 : MixedData.sourceRows (633 : Fin 2425) =
    MixedData.row633 := by decide +kernel

theorem sourceRowsAt634 : MixedData.sourceRows (634 : Fin 2425) =
    MixedData.row634 := by decide +kernel

theorem sourceRowsAt635 : MixedData.sourceRows (635 : Fin 2425) =
    MixedData.row635 := by decide +kernel

theorem sourceRowsAt636 : MixedData.sourceRows (636 : Fin 2425) =
    MixedData.row636 := by decide +kernel

theorem sourceRowsAt637 : MixedData.sourceRows (637 : Fin 2425) =
    MixedData.row637 := by decide +kernel

theorem sourceRowsAt638 : MixedData.sourceRows (638 : Fin 2425) =
    MixedData.row638 := by decide +kernel

theorem sourceRowsAt639 : MixedData.sourceRows (639 : Fin 2425) =
    MixedData.row639 := by decide +kernel

theorem chunkSound39_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 39) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 624 ∨ k.val = 625 ∨ k.val = 626 ∨ k.val = 627 ∨ k.val = 628 ∨ k.val = 629 ∨ k.val = 630 ∨ k.val = 631 ∨ k.val = 632 ∨ k.val = 633 ∨ k.val = 634 ∨ k.val = 635 ∨ k.val = 636 ∨ k.val = 637 ∨ k.val = 638 ∨ k.val = 639 := by omega
  rcases heq with h624 | h625 | h626 | h627 | h628 | h629 | h630 | h631 | h632 | h633 | h634 | h635 | h636 | h637 | h638 | h639
  · have he : k = (624 : Fin 2425) := Fin.ext h624
    subst k
    rw [sourceRowsAt624]
    exact rowSound624 B hB hF
  · have he : k = (625 : Fin 2425) := Fin.ext h625
    subst k
    rw [sourceRowsAt625]
    exact rowSound625 B hB hF
  · have he : k = (626 : Fin 2425) := Fin.ext h626
    subst k
    rw [sourceRowsAt626]
    exact rowSound626 B hB hF
  · have he : k = (627 : Fin 2425) := Fin.ext h627
    subst k
    rw [sourceRowsAt627]
    exact rowSound627 B hB hF
  · have he : k = (628 : Fin 2425) := Fin.ext h628
    subst k
    rw [sourceRowsAt628]
    exact rowSound628_e B hB hF
  · have he : k = (629 : Fin 2425) := Fin.ext h629
    subst k
    rw [sourceRowsAt629]
    exact rowSound629_e B hB hF
  · have he : k = (630 : Fin 2425) := Fin.ext h630
    subst k
    rw [sourceRowsAt630]
    exact rowSound630_e B hB hF
  · have he : k = (631 : Fin 2425) := Fin.ext h631
    subst k
    rw [sourceRowsAt631]
    exact rowSound631_e B hB hF
  · have he : k = (632 : Fin 2425) := Fin.ext h632
    subst k
    rw [sourceRowsAt632]
    exact rowSound632 B hB hF
  · have he : k = (633 : Fin 2425) := Fin.ext h633
    subst k
    rw [sourceRowsAt633]
    exact rowSound633_e B hB hF
  · have he : k = (634 : Fin 2425) := Fin.ext h634
    subst k
    rw [sourceRowsAt634]
    exact rowSound634 B hB hF
  · have he : k = (635 : Fin 2425) := Fin.ext h635
    subst k
    rw [sourceRowsAt635]
    exact rowSound635_e B hB hF
  · have he : k = (636 : Fin 2425) := Fin.ext h636
    subst k
    rw [sourceRowsAt636]
    exact rowSound636_e B hB hF
  · have he : k = (637 : Fin 2425) := Fin.ext h637
    subst k
    rw [sourceRowsAt637]
    exact rowSound637 B hB hF
  · have he : k = (638 : Fin 2425) := Fin.ext h638
    subst k
    rw [sourceRowsAt638]
    exact rowSound638 B hB hF
  · have he : k = (639 : Fin 2425) := Fin.ext h639
    subst k
    rw [sourceRowsAt639]
    exact rowSound639 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound39_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound39_e_oai
