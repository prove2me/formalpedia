-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound970_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:09:41.372533+00:00
-- url     : https://prove2.me/submissions/93b26a1e-fbcf-4d75-9779-4504c0289f90

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E129
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5416_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5433_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5450_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5485_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5490_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5492_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical146
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18803 raw18803Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw18803 raw18803Labels = mixedMoment B raw18803step0 raw18803step0Labels := by
      have ha : raw18803step0 = (fun i j => raw18803 (permutation269 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18803step0 raw18803; decide +kernel
      have hl : raw18803step0Labels = raw18803Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18803 raw18803Labels permutation269 permutation3
    mixedMoment B raw18803step0 raw18803step0Labels = mixedMoment B raw18803step1 raw18803step1Labels := by
      have ha : raw18803step1 = raw18803step0 := by apply Matrix.ext; unfold raw18803step1 raw18803step0; decide +kernel
      have hl : raw18803step0Labels = labelEmbedding6 ∘ raw18803step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18803step0 raw18803step0Labels raw18803step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical18804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18804 raw18804Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw18804 raw18804Labels = mixedMoment B raw18804step0 raw18804step0Labels := by
      have ha : raw18804step0 = (fun i j => raw18804 (permutation661 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18804step0 raw18804; decide +kernel
      have hl : raw18804step0Labels = raw18804Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18804 raw18804Labels permutation661 permutation7
    mixedMoment B raw18804step0 raw18804step0Labels = mixedMoment B raw18804step1 raw18804step1Labels := by
      have ha : raw18804step1 = raw18804step0 := by apply Matrix.ext; unfold raw18804step1 raw18804step0; decide +kernel
      have hl : raw18804step0Labels = labelEmbedding10 ∘ raw18804step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18804step0 raw18804step0Labels raw18804step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

theorem canonical18805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18805 raw18805Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw18805 raw18805Labels = mixedMoment B raw18805step0 raw18805step0Labels := by
      have hz : ∀ j, raw18805 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18805step0 = (fun i j => raw18805 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18805step0 raw18805; decide +kernel
      have hl : raw18805step0Labels = raw18805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18805 raw18805Labels permutation434 hz
    mixedMoment B raw18805step0 raw18805step0Labels = mixedMoment B raw18805step1 raw18805step1Labels := by
      have ha : raw18805step1 = (fun i j => raw18805step0 (permutation138 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18805step1 raw18805step0; decide +kernel
      have hl : raw18805step1Labels = raw18805step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18805step0 raw18805step0Labels permutation138 permutation6
    mixedMoment B raw18805step1 raw18805step1Labels = mixedMoment B raw18805step2 raw18805step2Labels := by
      have ha : raw18805step2 = raw18805step1 := by apply Matrix.ext; unfold raw18805step2 raw18805step1; decide +kernel
      have hl : raw18805step1Labels = labelEmbedding9 ∘ raw18805step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18805step1 raw18805step1Labels raw18805step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical18806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18806 raw18806Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw18806 raw18806Labels = mixedMoment B raw18806step0 raw18806step0Labels := by
      have hz : ∀ j, raw18806 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18806step0 = (fun i j => raw18806 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18806step0 raw18806; decide +kernel
      have hl : raw18806step0Labels = raw18806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18806 raw18806Labels permutation520 hz
    mixedMoment B raw18806step0 raw18806step0Labels = mixedMoment B raw18806step1 raw18806step1Labels := by
      have ha : raw18806step1 = (fun i j => raw18806step0 (permutation138 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18806step1 raw18806step0; decide +kernel
      have hl : raw18806step1Labels = raw18806step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18806step0 raw18806step0Labels permutation138 permutation6
    mixedMoment B raw18806step1 raw18806step1Labels = mixedMoment B raw18806step2 raw18806step2Labels := by
      have ha : raw18806step2 = raw18806step1 := by apply Matrix.ext; unfold raw18806step2 raw18806step1; decide +kernel
      have hl : raw18806step1Labels = labelEmbedding9 ∘ raw18806step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18806step1 raw18806step1Labels raw18806step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical18807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18807 raw18807Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18807 raw18807Labels = mixedMoment B raw18807step0 raw18807step0Labels := by
      have ha : raw18807step0 = (fun i j => raw18807 (permutation605 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18807step0 raw18807; decide +kernel
      have hl : raw18807step0Labels = raw18807Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18807 raw18807Labels permutation605 permutation4
    mixedMoment B raw18807step0 raw18807step0Labels = mixedMoment B raw18807step1 raw18807step1Labels := by
      have ha : raw18807step1 = -raw18807step0 := by apply Matrix.ext; change ∀ i j, raw18807step1 i j = -(raw18807step0 i j); unfold raw18807step1 raw18807step0; decide +kernel
      have hl : raw18807step1Labels = raw18807step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18807step1 raw18807step1Labels = mixedMoment B raw18807step2 raw18807step2Labels := by
      have ha : raw18807step2 = raw18807step1 := by apply Matrix.ext; unfold raw18807step2 raw18807step1; decide +kernel
      have hl : raw18807step1Labels = labelEmbedding7 ∘ raw18807step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18807step1 raw18807step1Labels raw18807step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical18808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18808 raw18808Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw18808 raw18808Labels = mixedMoment B raw18808step0 raw18808step0Labels := by
      have hz : ∀ j, raw18808 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18808step0 = (fun i j => raw18808 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18808step0 raw18808; decide +kernel
      have hl : raw18808step0Labels = raw18808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18808 raw18808Labels permutation265 hz
    mixedMoment B raw18808step0 raw18808step0Labels = mixedMoment B raw18808step1 raw18808step1Labels := by
      have ha : raw18808step1 = (fun i j => raw18808step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18808step1 raw18808step0; decide +kernel
      have hl : raw18808step1Labels = raw18808step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18808step0 raw18808step0Labels permutation36 permutation3
    mixedMoment B raw18808step1 raw18808step1Labels = mixedMoment B raw18808step2 raw18808step2Labels := by
      have ha : raw18808step2 = raw18808step1 := by apply Matrix.ext; unfold raw18808step2 raw18808step1; decide +kernel
      have hl : raw18808step1Labels = labelEmbedding6 ∘ raw18808step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18808step1 raw18808step1Labels raw18808step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical18809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18809 raw18809Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw18809 raw18809Labels = mixedMoment B raw18809step0 raw18809step0Labels := by
      have hz : ∀ j, raw18809 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18809step0 = (fun i j => raw18809 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18809step0 raw18809; decide +kernel
      have hl : raw18809step0Labels = raw18809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18809 raw18809Labels permutation265 hz
    _ = mixedMoment B node5485 node5485Labels := by rfl

theorem canonical18810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18810 raw18810Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw18810 raw18810Labels = mixedMoment B raw18810step0 raw18810step0Labels := by
      have hz : ∀ j, raw18810 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18810step0 = (fun i j => raw18810 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18810step0 raw18810; decide +kernel
      have hl : raw18810step0Labels = raw18810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18810 raw18810Labels permutation434 hz
    mixedMoment B raw18810step0 raw18810step0Labels = mixedMoment B raw18810step1 raw18810step1Labels := by
      have hz : ∀ j, raw18810step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw18810step1 = (fun i j => raw18810step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw18810step1 raw18810step0; decide +kernel
      have hl : raw18810step1Labels = raw18810step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18810step0 raw18810step0Labels permutation56 hz
    _ = mixedMoment B node5492 node5492Labels := by rfl

theorem canonical18811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18811 raw18811Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw18811 raw18811Labels = mixedMoment B raw18811step0 raw18811step0Labels := by
      have hz : ∀ j, raw18811 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18811step0 = (fun i j => raw18811 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18811step0 raw18811; decide +kernel
      have hl : raw18811step0Labels = raw18811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18811 raw18811Labels permutation520 hz
    mixedMoment B raw18811step0 raw18811step0Labels = mixedMoment B raw18811step1 raw18811step1Labels := by
      have hz : ∀ j, raw18811step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw18811step1 = (fun i j => raw18811step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw18811step1 raw18811step0; decide +kernel
      have hl : raw18811step1Labels = raw18811step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18811step0 raw18811step0Labels permutation56 hz
    _ = mixedMoment B node5492 node5492Labels := by rfl

theorem canonical18812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18812 raw18812Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18812 raw18812Labels = mixedMoment B raw18812step0 raw18812step0Labels := by
      have hz : ∀ j, raw18812 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18812step0 = (fun i j => raw18812 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18812step0 raw18812; decide +kernel
      have hl : raw18812step0Labels = raw18812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18812 raw18812Labels permutation265 hz
    mixedMoment B raw18812step0 raw18812step0Labels = mixedMoment B raw18812step1 raw18812step1Labels := by
      have ha : raw18812step1 = (fun i j => raw18812step0 (permutation131 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18812step1 raw18812step0; decide +kernel
      have hl : raw18812step1Labels = raw18812step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18812step0 raw18812step0Labels permutation131 permutation4
    mixedMoment B raw18812step1 raw18812step1Labels = mixedMoment B raw18812step2 raw18812step2Labels := by
      have ha : raw18812step2 = -raw18812step1 := by apply Matrix.ext; change ∀ i j, raw18812step2 i j = -(raw18812step1 i j); unfold raw18812step2 raw18812step1; decide +kernel
      have hl : raw18812step2Labels = raw18812step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18812step2 raw18812step2Labels = mixedMoment B raw18812step3 raw18812step3Labels := by
      have ha : raw18812step3 = raw18812step2 := by apply Matrix.ext; unfold raw18812step3 raw18812step2; decide +kernel
      have hl : raw18812step2Labels = labelEmbedding7 ∘ raw18812step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18812step2 raw18812step2Labels raw18812step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical18813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18813 raw18813Labels = mixedMoment B node5093 node5093Labels := by
  calc
    mixedMoment B raw18813 raw18813Labels = mixedMoment B raw18813step0 raw18813step0Labels := by
      have ha : raw18813step0 = (fun i j => raw18813 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18813step0 raw18813; decide +kernel
      have hl : raw18813step0Labels = raw18813Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18813 raw18813Labels permutation173 permutation3
    mixedMoment B raw18813step0 raw18813step0Labels = mixedMoment B raw18813step1 raw18813step1Labels := by
      have ha : raw18813step1 = raw18813step0 := by apply Matrix.ext; unfold raw18813step1 raw18813step0; decide +kernel
      have hl : raw18813step0Labels = labelEmbedding6 ∘ raw18813step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18813step0 raw18813step0Labels raw18813step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5093 node5093Labels := by rfl

theorem canonical18814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18814 raw18814Labels = mixedMoment B node5363 node5363Labels := by
  calc
    mixedMoment B raw18814 raw18814Labels = mixedMoment B raw18814step0 raw18814step0Labels := by
      have ha : raw18814step0 = (fun i j => raw18814 (permutation286 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18814step0 raw18814; decide +kernel
      have hl : raw18814step0Labels = raw18814Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18814 raw18814Labels permutation286 permutation3
    mixedMoment B raw18814step0 raw18814step0Labels = mixedMoment B raw18814step1 raw18814step1Labels := by
      have ha : raw18814step1 = raw18814step0 := by apply Matrix.ext; unfold raw18814step1 raw18814step0; decide +kernel
      have hl : raw18814step0Labels = labelEmbedding6 ∘ raw18814step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18814step0 raw18814step0Labels raw18814step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5363 node5363Labels := by rfl

theorem canonical18815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18815 raw18815Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw18815 raw18815Labels = mixedMoment B raw18815step0 raw18815step0Labels := by
      have hz : ∀ j, raw18815 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18815step0 = (fun i j => raw18815 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18815step0 raw18815; decide +kernel
      have hl : raw18815step0Labels = raw18815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18815 raw18815Labels permutation434 hz
    mixedMoment B raw18815step0 raw18815step0Labels = mixedMoment B raw18815step1 raw18815step1Labels := by
      have ha : raw18815step1 = (fun i j => raw18815step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18815step1 raw18815step0; decide +kernel
      have hl : raw18815step1Labels = raw18815step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18815step0 raw18815step0Labels permutation37 permutation3
    mixedMoment B raw18815step1 raw18815step1Labels = mixedMoment B raw18815step2 raw18815step2Labels := by
      have ha : raw18815step2 = raw18815step1 := by apply Matrix.ext; unfold raw18815step2 raw18815step1; decide +kernel
      have hl : raw18815step1Labels = labelEmbedding6 ∘ raw18815step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18815step1 raw18815step1Labels raw18815step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical147
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18816 raw18816Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw18816 raw18816Labels = mixedMoment B raw18816step0 raw18816step0Labels := by
      have hz : ∀ j, raw18816 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18816step0 = (fun i j => raw18816 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18816step0 raw18816; decide +kernel
      have hl : raw18816step0Labels = raw18816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18816 raw18816Labels permutation520 hz
    mixedMoment B raw18816step0 raw18816step0Labels = mixedMoment B raw18816step1 raw18816step1Labels := by
      have ha : raw18816step1 = (fun i j => raw18816step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18816step1 raw18816step0; decide +kernel
      have hl : raw18816step1Labels = raw18816step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18816step0 raw18816step0Labels permutation37 permutation3
    mixedMoment B raw18816step1 raw18816step1Labels = mixedMoment B raw18816step2 raw18816step2Labels := by
      have ha : raw18816step2 = raw18816step1 := by apply Matrix.ext; unfold raw18816step2 raw18816step1; decide +kernel
      have hl : raw18816step1Labels = labelEmbedding6 ∘ raw18816step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18816step1 raw18816step1Labels raw18816step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

theorem canonical18817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18817 raw18817Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw18817 raw18817Labels = mixedMoment B raw18817step0 raw18817step0Labels := by
      have ha : raw18817step0 = (fun i j => raw18817 (permutation605 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18817step0 raw18817; decide +kernel
      have hl : raw18817step0Labels = raw18817Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18817 raw18817Labels permutation605 permutation4
    mixedMoment B raw18817step0 raw18817step0Labels = mixedMoment B raw18817step1 raw18817step1Labels := by
      have ha : raw18817step1 = -raw18817step0 := by apply Matrix.ext; change ∀ i j, raw18817step1 i j = -(raw18817step0 i j); unfold raw18817step1 raw18817step0; decide +kernel
      have hl : raw18817step1Labels = raw18817step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18817step1 raw18817step1Labels = mixedMoment B raw18817step2 raw18817step2Labels := by
      have ha : raw18817step2 = raw18817step1 := by apply Matrix.ext; unfold raw18817step2 raw18817step1; decide +kernel
      have hl : raw18817step1Labels = labelEmbedding7 ∘ raw18817step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18817step1 raw18817step1Labels raw18817step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

theorem canonical18818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18818 raw18818Labels = mixedMoment B node5070 node5070Labels := by
  calc
    mixedMoment B raw18818 raw18818Labels = mixedMoment B raw18818step0 raw18818step0Labels := by
      have ha : raw18818step0 = (fun i j => raw18818 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18818step0 raw18818; decide +kernel
      have hl : raw18818step0Labels = raw18818Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18818 raw18818Labels permutation157 permutation3
    mixedMoment B raw18818step0 raw18818step0Labels = mixedMoment B raw18818step1 raw18818step1Labels := by
      have ha : raw18818step1 = raw18818step0 := by apply Matrix.ext; unfold raw18818step1 raw18818step0; decide +kernel
      have hl : raw18818step0Labels = labelEmbedding6 ∘ raw18818step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18818step0 raw18818step0Labels raw18818step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5070 node5070Labels := by rfl

theorem canonical18819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18819 raw18819Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw18819 raw18819Labels = mixedMoment B raw18819step0 raw18819step0Labels := by
      have ha : raw18819step0 = (fun i j => raw18819 (permutation270 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18819step0 raw18819; decide +kernel
      have hl : raw18819step0Labels = raw18819Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18819 raw18819Labels permutation270 permutation3
    mixedMoment B raw18819step0 raw18819step0Labels = mixedMoment B raw18819step1 raw18819step1Labels := by
      have ha : raw18819step1 = raw18819step0 := by apply Matrix.ext; unfold raw18819step1 raw18819step0; decide +kernel
      have hl : raw18819step0Labels = labelEmbedding6 ∘ raw18819step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18819step0 raw18819step0Labels raw18819step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

theorem canonical18820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18820 raw18820Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw18820 raw18820Labels = mixedMoment B raw18820step0 raw18820step0Labels := by
      have ha : raw18820step0 = (fun i j => raw18820 (permutation504 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18820step0 raw18820; decide +kernel
      have hl : raw18820step0Labels = raw18820Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18820 raw18820Labels permutation504 permutation3
    mixedMoment B raw18820step0 raw18820step0Labels = mixedMoment B raw18820step1 raw18820step1Labels := by
      have ha : raw18820step1 = -raw18820step0 := by apply Matrix.ext; change ∀ i j, raw18820step1 i j = -(raw18820step0 i j); unfold raw18820step1 raw18820step0; decide +kernel
      have hl : raw18820step1Labels = raw18820step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18820step1 raw18820step1Labels = mixedMoment B raw18820step2 raw18820step2Labels := by
      have ha : raw18820step2 = raw18820step1 := by apply Matrix.ext; unfold raw18820step2 raw18820step1; decide +kernel
      have hl : raw18820step1Labels = labelEmbedding6 ∘ raw18820step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18820step1 raw18820step1Labels raw18820step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

theorem canonical18821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18821 raw18821Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw18821 raw18821Labels = mixedMoment B raw18821step0 raw18821step0Labels := by
      have hz : ∀ j, raw18821 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18821step0 = (fun i j => raw18821 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18821step0 raw18821; decide +kernel
      have hl : raw18821step0Labels = raw18821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18821 raw18821Labels permutation520 hz
    mixedMoment B raw18821step0 raw18821step0Labels = mixedMoment B raw18821step1 raw18821step1Labels := by
      have ha : raw18821step1 = (fun i j => raw18821step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18821step1 raw18821step0; decide +kernel
      have hl : raw18821step1Labels = raw18821step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18821step0 raw18821step0Labels permutation121 permutation5
    mixedMoment B raw18821step1 raw18821step1Labels = mixedMoment B raw18821step2 raw18821step2Labels := by
      have ha : raw18821step2 = raw18821step1 := by apply Matrix.ext; unfold raw18821step2 raw18821step1; decide +kernel
      have hl : raw18821step1Labels = labelEmbedding8 ∘ raw18821step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18821step1 raw18821step1Labels raw18821step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical18822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18822 raw18822Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw18822 raw18822Labels = mixedMoment B raw18822step0 raw18822step0Labels := by
      have ha : raw18822step0 = (fun i j => raw18822 (permutation496 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18822step0 raw18822; decide +kernel
      have hl : raw18822step0Labels = raw18822Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18822 raw18822Labels permutation496 permutation5
    mixedMoment B raw18822step0 raw18822step0Labels = mixedMoment B raw18822step1 raw18822step1Labels := by
      have ha : raw18822step1 = raw18822step0 := by apply Matrix.ext; unfold raw18822step1 raw18822step0; decide +kernel
      have hl : raw18822step0Labels = labelEmbedding8 ∘ raw18822step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18822step0 raw18822step0Labels raw18822step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

theorem canonical18823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18823 raw18823Labels = mixedMoment B node5070 node5070Labels := by
  calc
    mixedMoment B raw18823 raw18823Labels = mixedMoment B raw18823step0 raw18823step0Labels := by
      have ha : raw18823step0 = (fun i j => raw18823 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18823step0 raw18823; decide +kernel
      have hl : raw18823step0Labels = raw18823Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18823 raw18823Labels permutation156 permutation3
    mixedMoment B raw18823step0 raw18823step0Labels = mixedMoment B raw18823step1 raw18823step1Labels := by
      have ha : raw18823step1 = raw18823step0 := by apply Matrix.ext; unfold raw18823step1 raw18823step0; decide +kernel
      have hl : raw18823step0Labels = labelEmbedding6 ∘ raw18823step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18823step0 raw18823step0Labels raw18823step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5070 node5070Labels := by rfl

theorem canonical18824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18824 raw18824Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw18824 raw18824Labels = mixedMoment B raw18824step0 raw18824step0Labels := by
      have ha : raw18824step0 = (fun i j => raw18824 (permutation269 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18824step0 raw18824; decide +kernel
      have hl : raw18824step0Labels = raw18824Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18824 raw18824Labels permutation269 permutation3
    mixedMoment B raw18824step0 raw18824step0Labels = mixedMoment B raw18824step1 raw18824step1Labels := by
      have ha : raw18824step1 = raw18824step0 := by apply Matrix.ext; unfold raw18824step1 raw18824step0; decide +kernel
      have hl : raw18824step0Labels = labelEmbedding6 ∘ raw18824step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18824step0 raw18824step0Labels raw18824step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

theorem canonical18825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18825 raw18825Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw18825 raw18825Labels = mixedMoment B raw18825step0 raw18825step0Labels := by
      have ha : raw18825step0 = (fun i j => raw18825 (permutation568 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18825step0 raw18825; decide +kernel
      have hl : raw18825step0Labels = raw18825Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18825 raw18825Labels permutation568 permutation3
    mixedMoment B raw18825step0 raw18825step0Labels = mixedMoment B raw18825step1 raw18825step1Labels := by
      have ha : raw18825step1 = -raw18825step0 := by apply Matrix.ext; change ∀ i j, raw18825step1 i j = -(raw18825step0 i j); unfold raw18825step1 raw18825step0; decide +kernel
      have hl : raw18825step1Labels = raw18825step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18825step1 raw18825step1Labels = mixedMoment B raw18825step2 raw18825step2Labels := by
      have ha : raw18825step2 = raw18825step1 := by apply Matrix.ext; unfold raw18825step2 raw18825step1; decide +kernel
      have hl : raw18825step1Labels = labelEmbedding6 ∘ raw18825step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18825step1 raw18825step1Labels raw18825step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

theorem canonical18826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18826 raw18826Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw18826 raw18826Labels = mixedMoment B raw18826step0 raw18826step0Labels := by
      have hz : ∀ j, raw18826 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18826step0 = (fun i j => raw18826 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18826step0 raw18826; decide +kernel
      have hl : raw18826step0Labels = raw18826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18826 raw18826Labels permutation434 hz
    mixedMoment B raw18826step0 raw18826step0Labels = mixedMoment B raw18826step1 raw18826step1Labels := by
      have ha : raw18826step1 = (fun i j => raw18826step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18826step1 raw18826step0; decide +kernel
      have hl : raw18826step1Labels = raw18826step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18826step0 raw18826step0Labels permutation121 permutation5
    mixedMoment B raw18826step1 raw18826step1Labels = mixedMoment B raw18826step2 raw18826step2Labels := by
      have ha : raw18826step2 = raw18826step1 := by apply Matrix.ext; unfold raw18826step2 raw18826step1; decide +kernel
      have hl : raw18826step1Labels = labelEmbedding8 ∘ raw18826step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18826step1 raw18826step1Labels raw18826step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical18827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18827 raw18827Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw18827 raw18827Labels = mixedMoment B raw18827step0 raw18827step0Labels := by
      have ha : raw18827step0 = (fun i j => raw18827 (permutation560 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18827step0 raw18827; decide +kernel
      have hl : raw18827step0Labels = raw18827Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18827 raw18827Labels permutation560 permutation5
    mixedMoment B raw18827step0 raw18827step0Labels = mixedMoment B raw18827step1 raw18827step1Labels := by
      have ha : raw18827step1 = raw18827step0 := by apply Matrix.ext; unfold raw18827step1 raw18827step0; decide +kernel
      have hl : raw18827step0Labels = labelEmbedding8 ∘ raw18827step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18827step0 raw18827step0Labels raw18827step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

theorem canonical18828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18828 raw18828Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw18828 raw18828Labels = mixedMoment B raw18828step0 raw18828step0Labels := by
      have ha : raw18828step0 = (fun i j => raw18828 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18828step0 raw18828; decide +kernel
      have hl : raw18828step0Labels = raw18828Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18828 raw18828Labels permutation152 permutation3
    mixedMoment B raw18828step0 raw18828step0Labels = mixedMoment B raw18828step1 raw18828step1Labels := by
      have ha : raw18828step1 = raw18828step0 := by apply Matrix.ext; unfold raw18828step1 raw18828step0; decide +kernel
      have hl : raw18828step0Labels = labelEmbedding6 ∘ raw18828step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18828step0 raw18828step0Labels raw18828step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5076 node5076Labels := by rfl

theorem canonical18829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18829 raw18829Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw18829 raw18829Labels = mixedMoment B raw18829step0 raw18829step0Labels := by
      have ha : raw18829step0 = (fun i j => raw18829 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18829step0 raw18829; decide +kernel
      have hl : raw18829step0Labels = raw18829Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18829 raw18829Labels permutation265 permutation3
    mixedMoment B raw18829step0 raw18829step0Labels = mixedMoment B raw18829step1 raw18829step1Labels := by
      have ha : raw18829step1 = raw18829step0 := by apply Matrix.ext; unfold raw18829step1 raw18829step0; decide +kernel
      have hl : raw18829step0Labels = labelEmbedding6 ∘ raw18829step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18829step0 raw18829step0Labels raw18829step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5354 node5354Labels := by rfl

theorem canonical18830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18830 raw18830Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw18830 raw18830Labels = mixedMoment B raw18830step0 raw18830step0Labels := by
      have ha : raw18830step0 = (fun i j => raw18830 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18830step0 raw18830; decide +kernel
      have hl : raw18830step0Labels = raw18830Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18830 raw18830Labels permutation662 permutation2
    mixedMoment B raw18830step0 raw18830step0Labels = mixedMoment B raw18830step1 raw18830step1Labels := by
      have ha : raw18830step1 = -raw18830step0 := by apply Matrix.ext; change ∀ i j, raw18830step1 i j = -(raw18830step0 i j); unfold raw18830step1 raw18830step0; decide +kernel
      have hl : raw18830step1Labels = raw18830step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5416 node5416Labels := by rfl

theorem canonical18831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18831 raw18831Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw18831 raw18831Labels = mixedMoment B raw18831step0 raw18831step0Labels := by
      have hz : ∀ j, raw18831 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18831step0 = (fun i j => raw18831 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18831step0 raw18831; decide +kernel
      have hl : raw18831step0Labels = raw18831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18831 raw18831Labels permutation434 hz
    mixedMoment B raw18831step0 raw18831step0Labels = mixedMoment B raw18831step1 raw18831step1Labels := by
      have ha : raw18831step1 = (fun i j => raw18831step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18831step1 raw18831step0; decide +kernel
      have hl : raw18831step1Labels = raw18831step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18831step0 raw18831step0Labels permutation151 permutation2
    mixedMoment B raw18831step1 raw18831step1Labels = mixedMoment B raw18831step2 raw18831step2Labels := by
      have ha : raw18831step2 = -raw18831step1 := by apply Matrix.ext; change ∀ i j, raw18831step2 i j = -(raw18831step1 i j); unfold raw18831step2 raw18831step1; decide +kernel
      have hl : raw18831step2Labels = raw18831step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical18832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18832 raw18832Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw18832 raw18832Labels = mixedMoment B raw18832step0 raw18832step0Labels := by
      have hz : ∀ j, raw18832 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18832step0 = (fun i j => raw18832 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18832step0 raw18832; decide +kernel
      have hl : raw18832step0Labels = raw18832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18832 raw18832Labels permutation520 hz
    mixedMoment B raw18832step0 raw18832step0Labels = mixedMoment B raw18832step1 raw18832step1Labels := by
      have ha : raw18832step1 = (fun i j => raw18832step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18832step1 raw18832step0; decide +kernel
      have hl : raw18832step1Labels = raw18832step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18832step0 raw18832step0Labels permutation151 permutation2
    mixedMoment B raw18832step1 raw18832step1Labels = mixedMoment B raw18832step2 raw18832step2Labels := by
      have ha : raw18832step2 = -raw18832step1 := by apply Matrix.ext; change ∀ i j, raw18832step2 i j = -(raw18832step1 i j); unfold raw18832step2 raw18832step1; decide +kernel
      have hl : raw18832step2Labels = raw18832step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5434 node5434Labels := by rfl

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

theorem canonical2088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2088 raw2088Labels = mixedMoment B node5070 node5070Labels := by
  calc
    mixedMoment B raw2088 raw2088Labels = mixedMoment B raw2088step0 raw2088step0Labels := by
      have ha : raw2088step0 = (fun i j => raw2088 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2088step0 raw2088; decide +kernel
      have hl : raw2088step0Labels = raw2088Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2088 raw2088Labels permutation152 permutation4
    mixedMoment B raw2088step0 raw2088step0Labels = mixedMoment B raw2088step1 raw2088step1Labels := by
      have ha : raw2088step1 = raw2088step0 := by apply Matrix.ext; unfold raw2088step1 raw2088step0; decide +kernel
      have hl : raw2088step0Labels = labelEmbedding7 ∘ raw2088step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2088step0 raw2088step0Labels raw2088step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5070 node5070Labels := by rfl

theorem canonical2089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2089 raw2089Labels = mixedMoment B node2477 node2477Labels := by
  calc
    mixedMoment B raw2089 raw2089Labels = mixedMoment B raw2089step0 raw2089step0Labels := by
      have ha : raw2089step0 = (fun i j => raw2089 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2089step0 raw2089; decide +kernel
      have hl : raw2089step0Labels = raw2089Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2089 raw2089Labels permutation152 permutation4
    _ = mixedMoment B node2477 node2477Labels := by rfl

theorem canonical2090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2090 raw2090Labels = mixedMoment B node3444 node3444Labels := by
  calc
    mixedMoment B raw2090 raw2090Labels = mixedMoment B raw2090step0 raw2090step0Labels := by
      have ha : raw2090step0 = (fun i j => raw2090 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2090step0 raw2090; decide +kernel
      have hl : raw2090step0Labels = raw2090Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2090 raw2090Labels permutation158 permutation6
    mixedMoment B raw2090step0 raw2090step0Labels = mixedMoment B raw2090step1 raw2090step1Labels := by
      have ha : raw2090step1 = -raw2090step0 := by apply Matrix.ext; change ∀ i j, raw2090step1 i j = -(raw2090step0 i j); unfold raw2090step1 raw2090step0; decide +kernel
      have hl : raw2090step1Labels = raw2090step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2090step1 raw2090step1Labels = mixedMoment B raw2090step2 raw2090step2Labels := by
      have ha : raw2090step2 = raw2090step1 := by apply Matrix.ext; unfold raw2090step2 raw2090step1; decide +kernel
      have hl : raw2090step1Labels = labelEmbedding1 ∘ raw2090step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2090step1 raw2090step1Labels raw2090step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3444 node3444Labels := by rfl

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

theorem canonical2112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2112 raw2112Labels = mixedMoment B node5093 node5093Labels := by
  calc
    mixedMoment B raw2112 raw2112Labels = mixedMoment B raw2112step0 raw2112step0Labels := by
      have ha : raw2112step0 = (fun i j => raw2112 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2112step0 raw2112; decide +kernel
      have hl : raw2112step0Labels = raw2112Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2112 raw2112Labels permutation152 permutation4
    mixedMoment B raw2112step0 raw2112step0Labels = mixedMoment B raw2112step1 raw2112step1Labels := by
      have ha : raw2112step1 = raw2112step0 := by apply Matrix.ext; unfold raw2112step1 raw2112step0; decide +kernel
      have hl : raw2112step0Labels = labelEmbedding7 ∘ raw2112step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2112step0 raw2112step0Labels raw2112step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5093 node5093Labels := by rfl

theorem canonical2113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2113 raw2113Labels = mixedMoment B node2503 node2503Labels := by
  calc
    mixedMoment B raw2113 raw2113Labels = mixedMoment B raw2113step0 raw2113step0Labels := by
      have ha : raw2113step0 = (fun i j => raw2113 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2113step0 raw2113; decide +kernel
      have hl : raw2113step0Labels = raw2113Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2113 raw2113Labels permutation152 permutation4
    _ = mixedMoment B node2503 node2503Labels := by rfl

theorem canonical2114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2114 raw2114Labels = mixedMoment B node3446 node3446Labels := by
  calc
    mixedMoment B raw2114 raw2114Labels = mixedMoment B raw2114step0 raw2114step0Labels := by
      have ha : raw2114step0 = (fun i j => raw2114 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2114step0 raw2114; decide +kernel
      have hl : raw2114step0Labels = raw2114Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2114 raw2114Labels permutation152 permutation6
    mixedMoment B raw2114step0 raw2114step0Labels = mixedMoment B raw2114step1 raw2114step1Labels := by
      have ha : raw2114step1 = -raw2114step0 := by apply Matrix.ext; change ∀ i j, raw2114step1 i j = -(raw2114step0 i j); unfold raw2114step1 raw2114step0; decide +kernel
      have hl : raw2114step1Labels = raw2114step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2114step1 raw2114step1Labels = mixedMoment B raw2114step2 raw2114step2Labels := by
      have ha : raw2114step2 = raw2114step1 := by apply Matrix.ext; unfold raw2114step2 raw2114step1; decide +kernel
      have hl : raw2114step1Labels = labelEmbedding1 ∘ raw2114step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2114step1 raw2114step1Labels raw2114step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3446 node3446Labels := by rfl

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

theorem canonical2397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2397 raw2397Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw2397 raw2397Labels = mixedMoment B raw2397step0 raw2397step0Labels := by
      have ha : raw2397step0 = (fun i j => raw2397 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2397step0 raw2397; decide +kernel
      have hl : raw2397step0Labels = raw2397Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2397 raw2397Labels permutation152 permutation4
    mixedMoment B raw2397step0 raw2397step0Labels = mixedMoment B raw2397step1 raw2397step1Labels := by
      have ha : raw2397step1 = raw2397step0 := by apply Matrix.ext; unfold raw2397step1 raw2397step0; decide +kernel
      have hl : raw2397step0Labels = labelEmbedding7 ∘ raw2397step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2397step0 raw2397step0Labels raw2397step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5354 node5354Labels := by rfl

theorem canonical2398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2398 raw2398Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw2398 raw2398Labels = mixedMoment B raw2398step0 raw2398step0Labels := by
      have ha : raw2398step0 = (fun i j => raw2398 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2398step0 raw2398; decide +kernel
      have hl : raw2398step0Labels = raw2398Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2398 raw2398Labels permutation152 permutation4
    _ = mixedMoment B node3692 node3692Labels := by rfl

theorem canonical2399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2399 raw2399Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw2399 raw2399Labels = mixedMoment B raw2399step0 raw2399step0Labels := by
      have ha : raw2399step0 = (fun i j => raw2399 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2399step0 raw2399; decide +kernel
      have hl : raw2399step0Labels = raw2399Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2399 raw2399Labels permutation170 permutation6
    mixedMoment B raw2399step0 raw2399step0Labels = mixedMoment B raw2399step1 raw2399step1Labels := by
      have ha : raw2399step1 = -raw2399step0 := by apply Matrix.ext; change ∀ i j, raw2399step1 i j = -(raw2399step0 i j); unfold raw2399step1 raw2399step0; decide +kernel
      have hl : raw2399step1Labels = raw2399step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2399step1 raw2399step1Labels = mixedMoment B raw2399step2 raw2399step2Labels := by
      have ha : raw2399step2 = raw2399step1 := by apply Matrix.ext; unfold raw2399step2 raw2399step1; decide +kernel
      have hl : raw2399step1Labels = labelEmbedding1 ∘ raw2399step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2399step1 raw2399step1Labels raw2399step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3769 node3769Labels := by rfl

theorem canonical2406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2406 raw2406Labels = mixedMoment B node5363 node5363Labels := by
  calc
    mixedMoment B raw2406 raw2406Labels = mixedMoment B raw2406step0 raw2406step0Labels := by
      have ha : raw2406step0 = (fun i j => raw2406 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2406step0 raw2406; decide +kernel
      have hl : raw2406step0Labels = raw2406Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2406 raw2406Labels permutation152 permutation4
    mixedMoment B raw2406step0 raw2406step0Labels = mixedMoment B raw2406step1 raw2406step1Labels := by
      have ha : raw2406step1 = raw2406step0 := by apply Matrix.ext; unfold raw2406step1 raw2406step0; decide +kernel
      have hl : raw2406step0Labels = labelEmbedding7 ∘ raw2406step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2406step0 raw2406step0Labels raw2406step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5363 node5363Labels := by rfl

theorem canonical2407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2407 raw2407Labels = mixedMoment B node3701 node3701Labels := by
  calc
    mixedMoment B raw2407 raw2407Labels = mixedMoment B raw2407step0 raw2407step0Labels := by
      have ha : raw2407step0 = (fun i j => raw2407 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2407step0 raw2407; decide +kernel
      have hl : raw2407step0Labels = raw2407Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2407 raw2407Labels permutation152 permutation4
    _ = mixedMoment B node3701 node3701Labels := by rfl

theorem canonical2408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2408 raw2408Labels = mixedMoment B node3751 node3751Labels := by
  calc
    mixedMoment B raw2408 raw2408Labels = mixedMoment B raw2408step0 raw2408step0Labels := by
      have ha : raw2408step0 = (fun i j => raw2408 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2408step0 raw2408; decide +kernel
      have hl : raw2408step0Labels = raw2408Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2408 raw2408Labels permutation152 permutation6
    mixedMoment B raw2408step0 raw2408step0Labels = mixedMoment B raw2408step1 raw2408step1Labels := by
      have ha : raw2408step1 = -raw2408step0 := by apply Matrix.ext; change ∀ i j, raw2408step1 i j = -(raw2408step0 i j); unfold raw2408step1 raw2408step0; decide +kernel
      have hl : raw2408step1Labels = raw2408step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2408step1 raw2408step1Labels = mixedMoment B raw2408step2 raw2408step2Labels := by
      have ha : raw2408step2 = raw2408step1 := by apply Matrix.ext; unfold raw2408step2 raw2408step1; decide +kernel
      have hl : raw2408step1Labels = labelEmbedding1 ∘ raw2408step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2408step1 raw2408step1Labels raw2408step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3751 node3751Labels := by rfl

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

theorem canonical2508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2508 raw2508Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw2508 raw2508Labels = mixedMoment B raw2508step0 raw2508step0Labels := by
      have ha : raw2508step0 = (fun i j => raw2508 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2508step0 raw2508; decide +kernel
      have hl : raw2508step0Labels = raw2508Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2508 raw2508Labels permutation152 permutation5
    mixedMoment B raw2508step0 raw2508step0Labels = mixedMoment B raw2508step1 raw2508step1Labels := by
      have ha : raw2508step1 = raw2508step0 := by apply Matrix.ext; unfold raw2508step1 raw2508step0; decide +kernel
      have hl : raw2508step0Labels = labelEmbedding8 ∘ raw2508step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2508step0 raw2508step0Labels raw2508step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

theorem canonical2509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2509 raw2509Labels = mixedMoment B node3964 node3964Labels := by
  calc
    mixedMoment B raw2509 raw2509Labels = mixedMoment B raw2509step0 raw2509step0Labels := by
      have ha : raw2509step0 = (fun i j => raw2509 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2509step0 raw2509; decide +kernel
      have hl : raw2509step0Labels = raw2509Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2509 raw2509Labels permutation662 permutation4
    mixedMoment B raw2509step0 raw2509step0Labels = mixedMoment B raw2509step1 raw2509step1Labels := by
      have ha : raw2509step1 = -raw2509step0 := by apply Matrix.ext; change ∀ i j, raw2509step1 i j = -(raw2509step0 i j); unfold raw2509step1 raw2509step0; decide +kernel
      have hl : raw2509step1Labels = raw2509step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3964 node3964Labels := by rfl

theorem canonical2510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2510 raw2510Labels = mixedMoment B node3900 node3900Labels := by
  calc
    mixedMoment B raw2510 raw2510Labels = mixedMoment B raw2510step0 raw2510step0Labels := by
      have ha : raw2510step0 = (fun i j => raw2510 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2510step0 raw2510; decide +kernel
      have hl : raw2510step0Labels = raw2510Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2510 raw2510Labels permutation160 permutation3
    mixedMoment B raw2510step0 raw2510step0Labels = mixedMoment B raw2510step1 raw2510step1Labels := by
      have ha : raw2510step1 = -raw2510step0 := by apply Matrix.ext; change ∀ i j, raw2510step1 i j = -(raw2510step0 i j); unfold raw2510step1 raw2510step0; decide +kernel
      have hl : raw2510step1Labels = raw2510step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2510step1 raw2510step1Labels = mixedMoment B raw2510step2 raw2510step2Labels := by
      have ha : raw2510step2 = raw2510step1 := by apply Matrix.ext; unfold raw2510step2 raw2510step1; decide +kernel
      have hl : raw2510step1Labels = labelEmbedding1 ∘ raw2510step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2510step1 raw2510step1Labels raw2510step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3900 node3900Labels := by rfl

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

theorem canonical2607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2607 raw2607Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw2607 raw2607Labels = mixedMoment B raw2607step0 raw2607step0Labels := by
      have ha : raw2607step0 = (fun i j => raw2607 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2607step0 raw2607; decide +kernel
      have hl : raw2607step0Labels = raw2607Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2607 raw2607Labels permutation32 permutation4
    mixedMoment B raw2607step0 raw2607step0Labels = mixedMoment B raw2607step1 raw2607step1Labels := by
      have ha : raw2607step1 = raw2607step0 := by apply Matrix.ext; unfold raw2607step1 raw2607step0; decide +kernel
      have hl : raw2607step0Labels = labelEmbedding7 ∘ raw2607step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2607step0 raw2607step0Labels raw2607step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

theorem canonical2608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2608 raw2608Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw2608 raw2608Labels = mixedMoment B raw2608step0 raw2608step0Labels := by
      have ha : raw2608step0 = (fun i j => raw2608 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2608step0 raw2608; decide +kernel
      have hl : raw2608step0Labels = raw2608Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2608 raw2608Labels permutation32 permutation4
    _ = mixedMoment B node3983 node3983Labels := by rfl

theorem canonical2609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2609 raw2609Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw2609 raw2609Labels = mixedMoment B raw2609step0 raw2609step0Labels := by
      have ha : raw2609step0 = (fun i j => raw2609 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2609step0 raw2609; decide +kernel
      have hl : raw2609step0Labels = raw2609Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2609 raw2609Labels permutation151 permutation6
    mixedMoment B raw2609step0 raw2609step0Labels = mixedMoment B raw2609step1 raw2609step1Labels := by
      have ha : raw2609step1 = raw2609step0 := by apply Matrix.ext; unfold raw2609step1 raw2609step0; decide +kernel
      have hl : raw2609step0Labels = labelEmbedding1 ∘ raw2609step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2609step0 raw2609step0Labels raw2609step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3983 node3983Labels := by rfl

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

theorem singleton5070 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5070 node5070Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2477 node2477Labels + mixedMoment B node3444 node3444Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2088 singletonSmall5070
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5070) = raw2088Labels := by decide +kernel
  rw [hl, canonical2088 B hB] at h
  have hc0 : mixedMoment B raw2088 (Fin.cases (0 : Fin 2) singletonSmall5070) =
      mixedMoment B node2477 node2477Labels := by
    have ha : raw2088 = raw2089 := by apply Matrix.ext; unfold raw2088 raw2089; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5070 = raw2089Labels := by decide +kernel
    rw [ha, hj, canonical2089 B hB]
  have hc1 : mixedMoment B raw2088 (Fin.cases (1 : Fin 2) singletonSmall5070) =
      mixedMoment B node3444 node3444Labels := by
    have ha : raw2088 = raw2090 := by apply Matrix.ext; unfold raw2088 raw2090; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5070 = raw2090Labels := by decide +kernel
    rw [ha, hj, canonical2090 B hB]
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

theorem singleton5093 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5093 node5093Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2503 node2503Labels + mixedMoment B node3446 node3446Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2112 singletonSmall5093
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5093) = raw2112Labels := by decide +kernel
  rw [hl, canonical2112 B hB] at h
  have hc0 : mixedMoment B raw2112 (Fin.cases (0 : Fin 2) singletonSmall5093) =
      mixedMoment B node2503 node2503Labels := by
    have ha : raw2112 = raw2113 := by apply Matrix.ext; unfold raw2112 raw2113; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5093 = raw2113Labels := by decide +kernel
    rw [ha, hj, canonical2113 B hB]
  have hc1 : mixedMoment B raw2112 (Fin.cases (1 : Fin 2) singletonSmall5093) =
      mixedMoment B node3446 node3446Labels := by
    have ha : raw2112 = raw2114 := by apply Matrix.ext; unfold raw2112 raw2114; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5093 = raw2114Labels := by decide +kernel
    rw [ha, hj, canonical2114 B hB]
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

theorem singleton5354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5354 node5354Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3692 node3692Labels + mixedMoment B node3769 node3769Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2397 singletonSmall5354
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5354) = raw2397Labels := by decide +kernel
  rw [hl, canonical2397 B hB] at h
  have hc0 : mixedMoment B raw2397 (Fin.cases (0 : Fin 2) singletonSmall5354) =
      mixedMoment B node3692 node3692Labels := by
    have ha : raw2397 = raw2398 := by apply Matrix.ext; unfold raw2397 raw2398; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5354 = raw2398Labels := by decide +kernel
    rw [ha, hj, canonical2398 B hB]
  have hc1 : mixedMoment B raw2397 (Fin.cases (1 : Fin 2) singletonSmall5354) =
      mixedMoment B node3769 node3769Labels := by
    have ha : raw2397 = raw2399 := by apply Matrix.ext; unfold raw2397 raw2399; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5354 = raw2399Labels := by decide +kernel
    rw [ha, hj, canonical2399 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5363 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5363 node5363Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3701 node3701Labels + mixedMoment B node3751 node3751Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2406 singletonSmall5363
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5363) = raw2406Labels := by decide +kernel
  rw [hl, canonical2406 B hB] at h
  have hc0 : mixedMoment B raw2406 (Fin.cases (0 : Fin 2) singletonSmall5363) =
      mixedMoment B node3701 node3701Labels := by
    have ha : raw2406 = raw2407 := by apply Matrix.ext; unfold raw2406 raw2407; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5363 = raw2407Labels := by decide +kernel
    rw [ha, hj, canonical2407 B hB]
  have hc1 : mixedMoment B raw2406 (Fin.cases (1 : Fin 2) singletonSmall5363) =
      mixedMoment B node3751 node3751Labels := by
    have ha : raw2406 = raw2408 := by apply Matrix.ext; unfold raw2406 raw2408; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5363 = raw2408Labels := by decide +kernel
    rw [ha, hj, canonical2408 B hB]
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

theorem singleton5422 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5422 node5422Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3964 node3964Labels + mixedMoment B node3900 node3900Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2508 singletonSmall5422
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5422) = raw2508Labels := by decide +kernel
  rw [hl, canonical2508 B hB] at h
  have hc0 : mixedMoment B raw2508 (Fin.cases (0 : Fin 2) singletonSmall5422) =
      mixedMoment B node3964 node3964Labels := by
    have ha : raw2508 = raw2509 := by apply Matrix.ext; unfold raw2508 raw2509; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5422 = raw2509Labels := by decide +kernel
    rw [ha, hj, canonical2509 B hB]
  have hc1 : mixedMoment B raw2508 (Fin.cases (1 : Fin 2) singletonSmall5422) =
      mixedMoment B node3900 node3900Labels := by
    have ha : raw2508 = raw2510 := by apply Matrix.ext; unfold raw2508 raw2510; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5422 = raw2510Labels := by decide +kernel
    rw [ha, hj, canonical2510 B hB]
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

theorem singleton5484 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5484 node5484Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3983 node3983Labels + mixedMoment B node3983 node3983Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2607 singletonSmall5484
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5484) = raw2607Labels := by decide +kernel
  rw [hl, canonical2607 B hB] at h
  have hc0 : mixedMoment B raw2607 (Fin.cases (0 : Fin 2) singletonSmall5484) =
      mixedMoment B node3983 node3983Labels := by
    have ha : raw2607 = raw2608 := by apply Matrix.ext; unfold raw2607 raw2608; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5484 = raw2608Labels := by decide +kernel
    rw [ha, hj, canonical2608 B hB]
  have hc1 : mixedMoment B raw2607 (Fin.cases (1 : Fin 2) singletonSmall5484) =
      mixedMoment B node3983 node3983Labels := by
    have ha : raw2607 = raw2609 := by apply Matrix.ext; unfold raw2607 raw2609; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5484 = raw2609Labels := by decide +kernel
    rw [ha, hj, canonical2609 B hB]
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

theorem zero5489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5489 node5489Labels = 0 := by
  exact mixedMoment_alpha B hF node5489 node5489Labels 2 permutation152
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

theorem sound2477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2477 node2477Labels = Sparse.eval nodeValue2477 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2477) = mixedMoment B node2477 node2477Labels := rfl
  simpa [nodeValue2477, Sparse.eval] using hc.symm

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

theorem sound2503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2503 node2503Labels = Sparse.eval nodeValue2503 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2503) = mixedMoment B node2503 node2503Labels := rfl
  simpa [nodeValue2503, Sparse.eval] using hc.symm

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

theorem sound2764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2764 node2764Labels = Sparse.eval nodeValue2764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2764) = mixedMoment B node2764 node2764Labels := rfl
  simpa [nodeValue2764, Sparse.eval] using hc.symm

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

theorem sound3444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3444 node3444Labels = Sparse.eval nodeValue3444 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3444) = mixedMoment B node3444 node3444Labels := rfl
  simpa [nodeValue3444, Sparse.eval] using hc.symm

theorem sound3446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3446 node3446Labels = Sparse.eval nodeValue3446 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3446) = mixedMoment B node3446 node3446Labels := rfl
  simpa [nodeValue3446, Sparse.eval] using hc.symm

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

theorem sound3477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3477 node3477Labels = Sparse.eval nodeValue3477 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3477) = mixedMoment B node3477 node3477Labels := rfl
  simpa [nodeValue3477, Sparse.eval] using hc.symm

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

theorem sound3581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3581 node3581Labels = Sparse.eval nodeValue3581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3581) = mixedMoment B node3581 node3581Labels := rfl
  simpa [nodeValue3581, Sparse.eval] using hc.symm

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

theorem sound3687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3687 node3687Labels = Sparse.eval nodeValue3687 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3687) = mixedMoment B node3687 node3687Labels := rfl
  simpa [nodeValue3687, Sparse.eval] using hc.symm

theorem sound3692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3692 node3692Labels = Sparse.eval nodeValue3692 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3692) = mixedMoment B node3692 node3692Labels := rfl
  simpa [nodeValue3692, Sparse.eval] using hc.symm

theorem sound3701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3701 node3701Labels = Sparse.eval nodeValue3701 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3701) = mixedMoment B node3701 node3701Labels := rfl
  simpa [nodeValue3701, Sparse.eval] using hc.symm

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

theorem sound3749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3749 node3749Labels = Sparse.eval nodeValue3749 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3749) = mixedMoment B node3749 node3749Labels := rfl
  simpa [nodeValue3749, Sparse.eval] using hc.symm

theorem sound3751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3751 node3751Labels = Sparse.eval nodeValue3751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3751) = mixedMoment B node3751 node3751Labels := rfl
  simpa [nodeValue3751, Sparse.eval] using hc.symm

theorem sound3769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3769 node3769Labels = Sparse.eval nodeValue3769 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3769) = mixedMoment B node3769 node3769Labels := rfl
  simpa [nodeValue3769, Sparse.eval] using hc.symm

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

theorem sound3796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3796 node3796Labels = Sparse.eval nodeValue3796 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3796) = mixedMoment B node3796 node3796Labels := rfl
  simpa [nodeValue3796, Sparse.eval] using hc.symm

theorem sound3804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3804 node3804Labels = Sparse.eval nodeValue3804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3804) = mixedMoment B node3804 node3804Labels := rfl
  simpa [nodeValue3804, Sparse.eval] using hc.symm

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

theorem sound3849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3849 node3849Labels = Sparse.eval nodeValue3849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3849) = mixedMoment B node3849 node3849Labels := rfl
  simpa [nodeValue3849, Sparse.eval] using hc.symm

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

theorem sound3900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3900 node3900Labels = Sparse.eval nodeValue3900 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3900) = mixedMoment B node3900 node3900Labels := rfl
  simpa [nodeValue3900, Sparse.eval] using hc.symm

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

theorem sound3964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3964 node3964Labels = Sparse.eval nodeValue3964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3964) = mixedMoment B node3964 node3964Labels := rfl
  simpa [nodeValue3964, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5070 node5070Labels = Sparse.eval nodeValue5070 (mixedVector B) := by
  have h := singleton5070 B _hB
  rw [sound2477 B _hB _hF, sound3444 B _hB _hF] at h
  norm_num [nodeValue5070, nodeValue2477, nodeValue3444, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5076 node5076Labels = Sparse.eval nodeValue5076 (mixedVector B) := by
  have h := singleton5076 B _hB
  rw [sound2483 B _hB _hF, sound3477 B _hB _hF] at h
  norm_num [nodeValue5076, nodeValue2483, nodeValue3477, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5093 node5093Labels = Sparse.eval nodeValue5093 (mixedVector B) := by
  have h := singleton5093 B _hB
  rw [sound2503 B _hB _hF, sound3446 B _hB _hF] at h
  norm_num [nodeValue5093, nodeValue2503, nodeValue3446, Sparse.eval] at h ⊢
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

theorem sound5290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5290 node5290Labels = Sparse.eval nodeValue5290 (mixedVector B) := by
  have h := singleton5290 B _hB
  rw [sound2764 B _hB _hF, sound3581 B _hB _hF] at h
  norm_num [nodeValue5290, nodeValue2764, nodeValue3581, Sparse.eval] at h ⊢
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

theorem sound5349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5349 node5349Labels = Sparse.eval nodeValue5349 (mixedVector B) := by
  have h := singleton5349 B _hB
  rw [sound3687 B _hB _hF, sound3749 B _hB _hF] at h
  norm_num [nodeValue5349, nodeValue3687, nodeValue3749, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5354 node5354Labels = Sparse.eval nodeValue5354 (mixedVector B) := by
  have h := singleton5354 B _hB
  rw [sound3692 B _hB _hF, sound3769 B _hB _hF] at h
  norm_num [nodeValue5354, nodeValue3692, nodeValue3769, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5363 node5363Labels = Sparse.eval nodeValue5363 (mixedVector B) := by
  have h := singleton5363 B _hB
  rw [sound3701 B _hB _hF, sound3751 B _hB _hF] at h
  norm_num [nodeValue5363, nodeValue3701, nodeValue3751, Sparse.eval] at h ⊢
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

theorem sound5422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5422 node5422Labels = Sparse.eval nodeValue5422 (mixedVector B) := by
  have h := singleton5422 B _hB
  rw [sound3900 B _hB _hF, sound3964 B _hB _hF] at h
  norm_num [nodeValue5422, nodeValue3900, nodeValue3964, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5431 node5431Labels = Sparse.eval nodeValue5431 (mixedVector B) := by
  have h := singleton5431 B _hB
  rw [sound3849 B _hB _hF, sound3875 B _hB _hF] at h
  norm_num [nodeValue5431, nodeValue3849, nodeValue3875, Sparse.eval] at h ⊢
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

theorem sound5484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5484 node5484Labels = Sparse.eval nodeValue5484 (mixedVector B) := by
  have h := singleton5484 B _hB
  rw [sound3983 B _hB _hF] at h
  norm_num [nodeValue5484, nodeValue3983, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5489 node5489Labels = Sparse.eval nodeValue5489 (mixedVector B) := by
  simpa only [nodeValue5489, Sparse.eval_nil] using zero5489 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources34
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1118 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1118 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1118 + difference 0 1) (sourceB1118 + difference 1 0) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1118 + difference 0 1) (sourceB1118 + difference 1 0) sourceC1118) = raw18803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18803; decide +kernel
    rw [ha]
    exact (canonical18803 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1118 + difference 0 2) (sourceB1118 + difference 2 0) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA1118 + difference 0 2) (sourceB1118 + difference 2 0) sourceC1118) = raw18804 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18804; decide +kernel
    rw [ha]
    exact (canonical18804 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1118 + difference 0 3) (sourceB1118 + difference 3 0) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1118 + difference 0 3) (sourceB1118 + difference 3 0) sourceC1118) = raw18805 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18805; decide +kernel
    rw [ha]
    exact (canonical18805 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1118 + difference 0 4) (sourceB1118 + difference 4 0) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1118 + difference 0 4) (sourceB1118 + difference 4 0) sourceC1118) = raw18806 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18806; decide +kernel
    rw [ha]
    exact (canonical18806 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1118 + difference 0 5) (sourceB1118 + difference 5 0) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1118 + difference 0 5) (sourceB1118 + difference 5 0) sourceC1118) = raw18807 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18807; decide +kernel
    rw [ha]
    exact (canonical18807 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1118 + difference 1 0) (sourceB1118 + difference 0 1) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA1118 + difference 1 0) (sourceB1118 + difference 0 1) sourceC1118) = raw18808 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18808; decide +kernel
    rw [ha]
    exact (canonical18808 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1118 + difference 1 2) (sourceB1118 + difference 2 1) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1118 + difference 1 2) (sourceB1118 + difference 2 1) sourceC1118) = raw18809 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18809; decide +kernel
    rw [ha]
    exact (canonical18809 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1118 + difference 1 3) (sourceB1118 + difference 3 1) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA1118 + difference 1 3) (sourceB1118 + difference 3 1) sourceC1118) = raw18810 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18810; decide +kernel
    rw [ha]
    exact (canonical18810 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1118 + difference 1 4) (sourceB1118 + difference 4 1) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA1118 + difference 1 4) (sourceB1118 + difference 4 1) sourceC1118) = raw18811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18811; decide +kernel
    rw [ha]
    exact (canonical18811 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1118 + difference 1 5) (sourceB1118 + difference 5 1) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1118 + difference 1 5) (sourceB1118 + difference 5 1) sourceC1118) = raw18812 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18812; decide +kernel
    rw [ha]
    exact (canonical18812 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1118 + difference 2 0) (sourceB1118 + difference 0 2) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5093) := by
    have ha : (tripleCharges (sourceA1118 + difference 2 0) (sourceB1118 + difference 0 2) sourceC1118) = raw18813 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18813; decide +kernel
    rw [ha]
    exact (canonical18813 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1118 + difference 2 1) (sourceB1118 + difference 1 2) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5363) := by
    have ha : (tripleCharges (sourceA1118 + difference 2 1) (sourceB1118 + difference 1 2) sourceC1118) = raw18814 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18814; decide +kernel
    rw [ha]
    exact (canonical18814 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1118 + difference 2 3) (sourceB1118 + difference 3 2) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA1118 + difference 2 3) (sourceB1118 + difference 3 2) sourceC1118) = raw18815 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18815; decide +kernel
    rw [ha]
    exact (canonical18815 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1118 + difference 2 4) (sourceB1118 + difference 4 2) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA1118 + difference 2 4) (sourceB1118 + difference 4 2) sourceC1118) = raw18816 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18816; decide +kernel
    rw [ha]
    exact (canonical18816 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1118 + difference 2 5) (sourceB1118 + difference 5 2) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1118 + difference 2 5) (sourceB1118 + difference 5 2) sourceC1118) = raw18817 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18817; decide +kernel
    rw [ha]
    exact (canonical18817 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1118 + difference 3 0) (sourceB1118 + difference 0 3) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5070) := by
    have ha : (tripleCharges (sourceA1118 + difference 3 0) (sourceB1118 + difference 0 3) sourceC1118) = raw18818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18818; decide +kernel
    rw [ha]
    exact (canonical18818 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1118 + difference 3 1) (sourceB1118 + difference 1 3) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA1118 + difference 3 1) (sourceB1118 + difference 1 3) sourceC1118) = raw18819 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18819; decide +kernel
    rw [ha]
    exact (canonical18819 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1118 + difference 3 2) (sourceB1118 + difference 2 3) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1118 + difference 3 2) (sourceB1118 + difference 2 3) sourceC1118) = raw18820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18820; decide +kernel
    rw [ha]
    exact (canonical18820 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1118 + difference 3 4) (sourceB1118 + difference 4 3) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1118 + difference 3 4) (sourceB1118 + difference 4 3) sourceC1118) = raw18821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18821; decide +kernel
    rw [ha]
    exact (canonical18821 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1118 + difference 3 5) (sourceB1118 + difference 5 3) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1118 + difference 3 5) (sourceB1118 + difference 5 3) sourceC1118) = raw18822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18822; decide +kernel
    rw [ha]
    exact (canonical18822 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1118 + difference 4 0) (sourceB1118 + difference 0 4) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5070) := by
    have ha : (tripleCharges (sourceA1118 + difference 4 0) (sourceB1118 + difference 0 4) sourceC1118) = raw18823 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18823; decide +kernel
    rw [ha]
    exact (canonical18823 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1118 + difference 4 1) (sourceB1118 + difference 1 4) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA1118 + difference 4 1) (sourceB1118 + difference 1 4) sourceC1118) = raw18824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18824; decide +kernel
    rw [ha]
    exact (canonical18824 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1118 + difference 4 2) (sourceB1118 + difference 2 4) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1118 + difference 4 2) (sourceB1118 + difference 2 4) sourceC1118) = raw18825 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18825; decide +kernel
    rw [ha]
    exact (canonical18825 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1118 + difference 4 3) (sourceB1118 + difference 3 4) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1118 + difference 4 3) (sourceB1118 + difference 3 4) sourceC1118) = raw18826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18826; decide +kernel
    rw [ha]
    exact (canonical18826 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1118 + difference 4 5) (sourceB1118 + difference 5 4) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1118 + difference 4 5) (sourceB1118 + difference 5 4) sourceC1118) = raw18827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18827; decide +kernel
    rw [ha]
    exact (canonical18827 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1118 + difference 5 0) (sourceB1118 + difference 0 5) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA1118 + difference 5 0) (sourceB1118 + difference 0 5) sourceC1118) = raw18828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18828; decide +kernel
    rw [ha]
    exact (canonical18828 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1118 + difference 5 1) (sourceB1118 + difference 1 5) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA1118 + difference 5 1) (sourceB1118 + difference 1 5) sourceC1118) = raw18829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18829; decide +kernel
    rw [ha]
    exact (canonical18829 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1118 + difference 5 2) (sourceB1118 + difference 2 5) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA1118 + difference 5 2) (sourceB1118 + difference 2 5) sourceC1118) = raw18830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18830; decide +kernel
    rw [ha]
    exact (canonical18830 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1118 + difference 5 3) (sourceB1118 + difference 3 5) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1118 + difference 5 3) (sourceB1118 + difference 3 5) sourceC1118) = raw18831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18831; decide +kernel
    rw [ha]
    exact (canonical18831 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1118 + difference 5 4) (sourceB1118 + difference 4 5) sourceC1118) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1118 + difference 5 4) (sourceB1118 + difference 4 5) sourceC1118) = raw18832 := by
      apply Matrix.ext; unfold tripleCharges sourceA1118 sourceB1118 sourceC1118 difference raw18832; decide +kernel
    rw [ha]
    exact (canonical18832 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1118 sourceB1118 sourceC1118
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1118, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck970 : Integer.Sparse.reindex keyMap MixedData.row970 = numericRow970 := by decide +kernel

theorem numericCheck970 (x : Master → ℝ) : Integer.Sparse.eval numericRow970 x =
    (51840 : ℝ) * reducedSource970 x := by
  norm_num [numericRow970, reducedSource970, Integer.Sparse.eval, Sparse.eval, nodeValue5070, nodeValue5076, nodeValue5093, nodeValue5290, nodeValue5349, nodeValue5354, nodeValue5363, nodeValue5397, nodeValue5401, nodeValue5416, nodeValue5422, nodeValue5431, nodeValue5433, nodeValue5434, nodeValue5438, nodeValue5450, nodeValue5484, nodeValue5485, nodeValue5489, nodeValue5490, nodeValue5492]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero970 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource970 (mixedVector B) = 0 := by
  have h5070 : mixedVector B (Sum.inr 5070) = Sparse.eval nodeValue5070 (mixedVector B) := by
    change mixedMoment B node5070 node5070Labels = _
    exact sound5070 B hB hF
  have h5076 : mixedVector B (Sum.inr 5076) = Sparse.eval nodeValue5076 (mixedVector B) := by
    change mixedMoment B node5076 node5076Labels = _
    exact sound5076 B hB hF
  have h5093 : mixedVector B (Sum.inr 5093) = Sparse.eval nodeValue5093 (mixedVector B) := by
    change mixedMoment B node5093 node5093Labels = _
    exact sound5093 B hB hF
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  have h5349 : mixedVector B (Sum.inr 5349) = Sparse.eval nodeValue5349 (mixedVector B) := by
    change mixedMoment B node5349 node5349Labels = _
    exact sound5349 B hB hF
  have h5354 : mixedVector B (Sum.inr 5354) = Sparse.eval nodeValue5354 (mixedVector B) := by
    change mixedMoment B node5354 node5354Labels = _
    exact sound5354 B hB hF
  have h5363 : mixedVector B (Sum.inr 5363) = Sparse.eval nodeValue5363 (mixedVector B) := by
    change mixedMoment B node5363 node5363Labels = _
    exact sound5363 B hB hF
  have h5397 : mixedVector B (Sum.inr 5397) = Sparse.eval nodeValue5397 (mixedVector B) := by
    change mixedMoment B node5397 node5397Labels = _
    exact sound5397 B hB hF
  have h5401 : mixedVector B (Sum.inr 5401) = Sparse.eval nodeValue5401 (mixedVector B) := by
    change mixedMoment B node5401 node5401Labels = _
    exact sound5401 B hB hF
  have h5416 : mixedVector B (Sum.inr 5416) = Sparse.eval nodeValue5416 (mixedVector B) := by
    change mixedMoment B node5416 node5416Labels = _
    exact sound5416_e B hB hF
  have h5422 : mixedVector B (Sum.inr 5422) = Sparse.eval nodeValue5422 (mixedVector B) := by
    change mixedMoment B node5422 node5422Labels = _
    exact sound5422 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433_e B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  have h5438 : mixedVector B (Sum.inr 5438) = Sparse.eval nodeValue5438 (mixedVector B) := by
    change mixedMoment B node5438 node5438Labels = _
    exact sound5438 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450_e B hB hF
  have h5484 : mixedVector B (Sum.inr 5484) = Sparse.eval nodeValue5484 (mixedVector B) := by
    change mixedMoment B node5484 node5484Labels = _
    exact sound5484 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485_e B hB hF
  have h5489 : mixedVector B (Sum.inr 5489) = Sparse.eval nodeValue5489 (mixedVector B) := by
    change mixedMoment B node5489 node5489Labels = _
    exact sound5489 B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490_e B hB hF
  have h5492 : mixedVector B (Sum.inr 5492) = Sparse.eval nodeValue5492 (mixedVector B) := by
    change mixedMoment B node5492 node5492Labels = _
    exact sound5492_e B hB hF
  simpa only [sourceForm1118, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5070, h5076, h5093, h5290, h5349, h5354, h5363, h5397, h5401, h5416, h5422, h5431, h5433, h5434, h5438, h5450, h5484, h5485, h5489, h5490, h5492, reducedSource970] using sourceEq1118 B hB

theorem rowSound970_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row970 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck970, numericCheck970, reducedZero970 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound970_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound970_e_oai
