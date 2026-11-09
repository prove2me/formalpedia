-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound951_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:01:41.601771+00:00
-- url     : https://prove2.me/submissions/808ea7d3-1648-40fc-98dc-8ad823004e68

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E129
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5167_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5292_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5386_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5433_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5435_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5450_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5452_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5490_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical143
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18359 raw18359Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw18359 raw18359Labels = mixedMoment B raw18359step0 raw18359step0Labels := by
      have ha : raw18359step0 = (fun i j => raw18359 (permutation303 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18359step0 raw18359; decide +kernel
      have hl : raw18359step0Labels = raw18359Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18359 raw18359Labels permutation303 permutation5
    mixedMoment B raw18359step0 raw18359step0Labels = mixedMoment B raw18359step1 raw18359step1Labels := by
      have ha : raw18359step1 = -raw18359step0 := by apply Matrix.ext; change ∀ i j, raw18359step1 i j = -(raw18359step0 i j); unfold raw18359step1 raw18359step0; decide +kernel
      have hl : raw18359step1Labels = raw18359step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18359step1 raw18359step1Labels = mixedMoment B raw18359step2 raw18359step2Labels := by
      have ha : raw18359step2 = raw18359step1 := by apply Matrix.ext; unfold raw18359step2 raw18359step1; decide +kernel
      have hl : raw18359step1Labels = labelEmbedding8 ∘ raw18359step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18359step1 raw18359step1Labels raw18359step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical18360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18360 raw18360Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw18360 raw18360Labels = mixedMoment B raw18360step0 raw18360step0Labels := by
      have ha : raw18360step0 = (fun i j => raw18360 (permutation379 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18360step0 raw18360; decide +kernel
      have hl : raw18360step0Labels = raw18360Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18360 raw18360Labels permutation379 permutation5
    mixedMoment B raw18360step0 raw18360step0Labels = mixedMoment B raw18360step1 raw18360step1Labels := by
      have ha : raw18360step1 = -raw18360step0 := by apply Matrix.ext; change ∀ i j, raw18360step1 i j = -(raw18360step0 i j); unfold raw18360step1 raw18360step0; decide +kernel
      have hl : raw18360step1Labels = raw18360step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18360step1 raw18360step1Labels = mixedMoment B raw18360step2 raw18360step2Labels := by
      have ha : raw18360step2 = raw18360step1 := by apply Matrix.ext; unfold raw18360step2 raw18360step1; decide +kernel
      have hl : raw18360step1Labels = labelEmbedding8 ∘ raw18360step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18360step1 raw18360step1Labels raw18360step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

theorem canonical18361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18361 raw18361Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw18361 raw18361Labels = mixedMoment B raw18361step0 raw18361step0Labels := by
      have hz : ∀ j, raw18361 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18361step0 = (fun i j => raw18361 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18361step0 raw18361; decide +kernel
      have hl : raw18361step0Labels = raw18361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18361 raw18361Labels permutation434 hz
    mixedMoment B raw18361step0 raw18361step0Labels = mixedMoment B raw18361step1 raw18361step1Labels := by
      have ha : raw18361step1 = (fun i j => raw18361step0 (permutation45 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18361step1 raw18361step0; decide +kernel
      have hl : raw18361step1Labels = raw18361step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18361step0 raw18361step0Labels permutation45 permutation6
    mixedMoment B raw18361step1 raw18361step1Labels = mixedMoment B raw18361step2 raw18361step2Labels := by
      have ha : raw18361step2 = -raw18361step1 := by apply Matrix.ext; change ∀ i j, raw18361step2 i j = -(raw18361step1 i j); unfold raw18361step2 raw18361step1; decide +kernel
      have hl : raw18361step2Labels = raw18361step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18361step2 raw18361step2Labels = mixedMoment B raw18361step3 raw18361step3Labels := by
      have ha : raw18361step3 = raw18361step2 := by apply Matrix.ext; unfold raw18361step3 raw18361step2; decide +kernel
      have hl : raw18361step2Labels = labelEmbedding9 ∘ raw18361step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18361step2 raw18361step2Labels raw18361step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical18362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18362 raw18362Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw18362 raw18362Labels = mixedMoment B raw18362step0 raw18362step0Labels := by
      have hz : ∀ j, raw18362 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18362step0 = (fun i j => raw18362 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18362step0 raw18362; decide +kernel
      have hl : raw18362step0Labels = raw18362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18362 raw18362Labels permutation520 hz
    mixedMoment B raw18362step0 raw18362step0Labels = mixedMoment B raw18362step1 raw18362step1Labels := by
      have ha : raw18362step1 = (fun i j => raw18362step0 (permutation45 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18362step1 raw18362step0; decide +kernel
      have hl : raw18362step1Labels = raw18362step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18362step0 raw18362step0Labels permutation45 permutation6
    mixedMoment B raw18362step1 raw18362step1Labels = mixedMoment B raw18362step2 raw18362step2Labels := by
      have ha : raw18362step2 = -raw18362step1 := by apply Matrix.ext; change ∀ i j, raw18362step2 i j = -(raw18362step1 i j); unfold raw18362step2 raw18362step1; decide +kernel
      have hl : raw18362step2Labels = raw18362step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18362step2 raw18362step2Labels = mixedMoment B raw18362step3 raw18362step3Labels := by
      have ha : raw18362step3 = raw18362step2 := by apply Matrix.ext; unfold raw18362step3 raw18362step2; decide +kernel
      have hl : raw18362step2Labels = labelEmbedding9 ∘ raw18362step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18362step2 raw18362step2Labels raw18362step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

theorem canonical18363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18363 raw18363Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw18363 raw18363Labels = mixedMoment B raw18363step0 raw18363step0Labels := by
      have ha : raw18363step0 = (fun i j => raw18363 (permutation212 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18363step0 raw18363; decide +kernel
      have hl : raw18363step0Labels = raw18363Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18363 raw18363Labels permutation212 permutation6
    mixedMoment B raw18363step0 raw18363step0Labels = mixedMoment B raw18363step1 raw18363step1Labels := by
      have ha : raw18363step1 = -raw18363step0 := by apply Matrix.ext; change ∀ i j, raw18363step1 i j = -(raw18363step0 i j); unfold raw18363step1 raw18363step0; decide +kernel
      have hl : raw18363step1Labels = raw18363step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18363step1 raw18363step1Labels = mixedMoment B raw18363step2 raw18363step2Labels := by
      have ha : raw18363step2 = raw18363step1 := by apply Matrix.ext; unfold raw18363step2 raw18363step1; decide +kernel
      have hl : raw18363step1Labels = labelEmbedding9 ∘ raw18363step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18363step1 raw18363step1Labels raw18363step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

theorem canonical18364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18364 raw18364Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw18364 raw18364Labels = mixedMoment B raw18364step0 raw18364step0Labels := by
      have hz : ∀ j, raw18364 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18364step0 = (fun i j => raw18364 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18364step0 raw18364; decide +kernel
      have hl : raw18364step0Labels = raw18364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18364 raw18364Labels permutation265 hz
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical18365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18365 raw18365Labels = mixedMoment B node5386 node5386Labels := by
  calc
    mixedMoment B raw18365 raw18365Labels = mixedMoment B raw18365step0 raw18365step0Labels := by
      have ha : raw18365step0 = (fun i j => raw18365 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18365step0 raw18365; decide +kernel
      have hl : raw18365step0Labels = raw18365Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18365 raw18365Labels permutation160 permutation2
    _ = mixedMoment B node5386 node5386Labels := by rfl

theorem canonical18366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18366 raw18366Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw18366 raw18366Labels = mixedMoment B raw18366step0 raw18366step0Labels := by
      have hz : ∀ j, raw18366 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18366step0 = (fun i j => raw18366 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18366step0 raw18366; decide +kernel
      have hl : raw18366step0Labels = raw18366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18366 raw18366Labels permutation434 hz
    mixedMoment B raw18366step0 raw18366step0Labels = mixedMoment B raw18366step1 raw18366step1Labels := by
      have ha : raw18366step1 = (fun i j => raw18366step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18366step1 raw18366step0; decide +kernel
      have hl : raw18366step1Labels = raw18366step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18366step0 raw18366step0Labels permutation34 permutation2
    _ = mixedMoment B node5440 node5440Labels := by rfl

theorem canonical18367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18367 raw18367Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw18367 raw18367Labels = mixedMoment B raw18367step0 raw18367step0Labels := by
      have hz : ∀ j, raw18367 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18367step0 = (fun i j => raw18367 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18367step0 raw18367; decide +kernel
      have hl : raw18367step0Labels = raw18367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18367 raw18367Labels permutation520 hz
    mixedMoment B raw18367step0 raw18367step0Labels = mixedMoment B raw18367step1 raw18367step1Labels := by
      have ha : raw18367step1 = (fun i j => raw18367step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18367step1 raw18367step0; decide +kernel
      have hl : raw18367step1Labels = raw18367step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18367step0 raw18367step0Labels permutation34 permutation2
    _ = mixedMoment B node5440 node5440Labels := by rfl

theorem canonical18368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18368 raw18368Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18368 raw18368Labels = mixedMoment B raw18368step0 raw18368step0Labels := by
      have ha : raw18368step0 = (fun i j => raw18368 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18368step0 raw18368; decide +kernel
      have hl : raw18368step0Labels = raw18368Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18368 raw18368Labels permutation173 permutation2
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical18369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18369 raw18369Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw18369 raw18369Labels = mixedMoment B raw18369step0 raw18369step0Labels := by
      have ha : raw18369step0 = (fun i j => raw18369 (permutation270 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18369step0 raw18369; decide +kernel
      have hl : raw18369step0Labels = raw18369Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18369 raw18369Labels permutation270 permutation3
    mixedMoment B raw18369step0 raw18369step0Labels = mixedMoment B raw18369step1 raw18369step1Labels := by
      have ha : raw18369step1 = raw18369step0 := by apply Matrix.ext; unfold raw18369step1 raw18369step0; decide +kernel
      have hl : raw18369step0Labels = labelEmbedding6 ∘ raw18369step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18369step0 raw18369step0Labels raw18369step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical18370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18370 raw18370Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw18370 raw18370Labels = mixedMoment B raw18370step0 raw18370step0Labels := by
      have ha : raw18370step0 = (fun i j => raw18370 (permutation502 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18370step0 raw18370; decide +kernel
      have hl : raw18370step0Labels = raw18370Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18370 raw18370Labels permutation502 permutation3
    mixedMoment B raw18370step0 raw18370step0Labels = mixedMoment B raw18370step1 raw18370step1Labels := by
      have ha : raw18370step1 = -raw18370step0 := by apply Matrix.ext; change ∀ i j, raw18370step1 i j = -(raw18370step0 i j); unfold raw18370step1 raw18370step0; decide +kernel
      have hl : raw18370step1Labels = raw18370step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18370step1 raw18370step1Labels = mixedMoment B raw18370step2 raw18370step2Labels := by
      have ha : raw18370step2 = raw18370step1 := by apply Matrix.ext; unfold raw18370step2 raw18370step1; decide +kernel
      have hl : raw18370step1Labels = labelEmbedding6 ∘ raw18370step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18370step1 raw18370step1Labels raw18370step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

theorem canonical18371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18371 raw18371Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw18371 raw18371Labels = mixedMoment B raw18371step0 raw18371step0Labels := by
      have hz : ∀ j, raw18371 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18371step0 = (fun i j => raw18371 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18371step0 raw18371; decide +kernel
      have hl : raw18371step0Labels = raw18371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18371 raw18371Labels permutation520 hz
    mixedMoment B raw18371step0 raw18371step0Labels = mixedMoment B raw18371step1 raw18371step1Labels := by
      have ha : raw18371step1 = (fun i j => raw18371step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18371step1 raw18371step0; decide +kernel
      have hl : raw18371step1Labels = raw18371step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18371step0 raw18371step0Labels permutation33 permutation2
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical18372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18372 raw18372Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw18372 raw18372Labels = mixedMoment B raw18372step0 raw18372step0Labels := by
      have ha : raw18372step0 = (fun i j => raw18372 (permutation498 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18372step0 raw18372; decide +kernel
      have hl : raw18372step0Labels = raw18372Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18372 raw18372Labels permutation498 permutation3
    mixedMoment B raw18372step0 raw18372step0Labels = mixedMoment B raw18372step1 raw18372step1Labels := by
      have ha : raw18372step1 = -raw18372step0 := by apply Matrix.ext; change ∀ i j, raw18372step1 i j = -(raw18372step0 i j); unfold raw18372step1 raw18372step0; decide +kernel
      have hl : raw18372step1Labels = raw18372step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18372step1 raw18372step1Labels = mixedMoment B raw18372step2 raw18372step2Labels := by
      have ha : raw18372step2 = raw18372step1 := by apply Matrix.ext; unfold raw18372step2 raw18372step1; decide +kernel
      have hl : raw18372step1Labels = labelEmbedding6 ∘ raw18372step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18372step1 raw18372step1Labels raw18372step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical18373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18373 raw18373Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw18373 raw18373Labels = mixedMoment B raw18373step0 raw18373step0Labels := by
      have ha : raw18373step0 = (fun i j => raw18373 (permutation269 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18373step0 raw18373; decide +kernel
      have hl : raw18373step0Labels = raw18373Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18373 raw18373Labels permutation269 permutation3
    mixedMoment B raw18373step0 raw18373step0Labels = mixedMoment B raw18373step1 raw18373step1Labels := by
      have ha : raw18373step1 = raw18373step0 := by apply Matrix.ext; unfold raw18373step1 raw18373step0; decide +kernel
      have hl : raw18373step0Labels = labelEmbedding6 ∘ raw18373step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18373step0 raw18373step0Labels raw18373step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

theorem canonical18374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18374 raw18374Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw18374 raw18374Labels = mixedMoment B raw18374step0 raw18374step0Labels := by
      have ha : raw18374step0 = (fun i j => raw18374 (permutation566 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18374step0 raw18374; decide +kernel
      have hl : raw18374step0Labels = raw18374Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18374 raw18374Labels permutation566 permutation3
    mixedMoment B raw18374step0 raw18374step0Labels = mixedMoment B raw18374step1 raw18374step1Labels := by
      have ha : raw18374step1 = -raw18374step0 := by apply Matrix.ext; change ∀ i j, raw18374step1 i j = -(raw18374step0 i j); unfold raw18374step1 raw18374step0; decide +kernel
      have hl : raw18374step1Labels = raw18374step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18374step1 raw18374step1Labels = mixedMoment B raw18374step2 raw18374step2Labels := by
      have ha : raw18374step2 = raw18374step1 := by apply Matrix.ext; unfold raw18374step2 raw18374step1; decide +kernel
      have hl : raw18374step1Labels = labelEmbedding6 ∘ raw18374step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18374step1 raw18374step1Labels raw18374step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

theorem canonical18375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18375 raw18375Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw18375 raw18375Labels = mixedMoment B raw18375step0 raw18375step0Labels := by
      have hz : ∀ j, raw18375 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18375step0 = (fun i j => raw18375 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18375step0 raw18375; decide +kernel
      have hl : raw18375step0Labels = raw18375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18375 raw18375Labels permutation434 hz
    mixedMoment B raw18375step0 raw18375step0Labels = mixedMoment B raw18375step1 raw18375step1Labels := by
      have ha : raw18375step1 = (fun i j => raw18375step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18375step1 raw18375step0; decide +kernel
      have hl : raw18375step1Labels = raw18375step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18375step0 raw18375step0Labels permutation33 permutation2
    _ = mixedMoment B node5435 node5435Labels := by rfl

theorem canonical18376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18376 raw18376Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw18376 raw18376Labels = mixedMoment B raw18376step0 raw18376step0Labels := by
      have ha : raw18376step0 = (fun i j => raw18376 (permutation562 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18376step0 raw18376; decide +kernel
      have hl : raw18376step0Labels = raw18376Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18376 raw18376Labels permutation562 permutation3
    mixedMoment B raw18376step0 raw18376step0Labels = mixedMoment B raw18376step1 raw18376step1Labels := by
      have ha : raw18376step1 = -raw18376step0 := by apply Matrix.ext; change ∀ i j, raw18376step1 i j = -(raw18376step0 i j); unfold raw18376step1 raw18376step0; decide +kernel
      have hl : raw18376step1Labels = raw18376step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18376step1 raw18376step1Labels = mixedMoment B raw18376step2 raw18376step2Labels := by
      have ha : raw18376step2 = raw18376step1 := by apply Matrix.ext; unfold raw18376step2 raw18376step1; decide +kernel
      have hl : raw18376step1Labels = labelEmbedding6 ∘ raw18376step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18376step1 raw18376step1Labels raw18376step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical18377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18377 raw18377Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw18377 raw18377Labels = mixedMoment B raw18377step0 raw18377step0Labels := by
      have ha : raw18377step0 = (fun i j => raw18377 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18377step0 raw18377; decide +kernel
      have hl : raw18377step0Labels = raw18377Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18377 raw18377Labels permutation265 permutation3
    mixedMoment B raw18377step0 raw18377step0Labels = mixedMoment B raw18377step1 raw18377step1Labels := by
      have ha : raw18377step1 = raw18377step0 := by apply Matrix.ext; unfold raw18377step1 raw18377step0; decide +kernel
      have hl : raw18377step0Labels = labelEmbedding6 ∘ raw18377step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18377step0 raw18377step0Labels raw18377step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

theorem canonical18378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18378 raw18378Labels = mixedMoment B node5422 node5422Labels := by
  calc
    _ = mixedMoment B node5422 node5422Labels := by rfl

theorem canonical18379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18379 raw18379Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw18379 raw18379Labels = mixedMoment B raw18379step0 raw18379step0Labels := by
      have hz : ∀ j, raw18379 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18379step0 = (fun i j => raw18379 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18379step0 raw18379; decide +kernel
      have hl : raw18379step0Labels = raw18379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18379 raw18379Labels permutation434 hz
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical18380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18380 raw18380Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw18380 raw18380Labels = mixedMoment B raw18380step0 raw18380step0Labels := by
      have hz : ∀ j, raw18380 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18380step0 = (fun i j => raw18380 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18380step0 raw18380; decide +kernel
      have hl : raw18380step0Labels = raw18380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18380 raw18380Labels permutation520 hz
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

theorem canonical2433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2433 raw2433Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw2433 raw2433Labels = mixedMoment B raw2433step0 raw2433step0Labels := by
      have ha : raw2433step0 = (fun i j => raw2433 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2433step0 raw2433; decide +kernel
      have hl : raw2433step0Labels = raw2433Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2433 raw2433Labels permutation152 permutation4
    mixedMoment B raw2433step0 raw2433step0Labels = mixedMoment B raw2433step1 raw2433step1Labels := by
      have ha : raw2433step1 = raw2433step0 := by apply Matrix.ext; unfold raw2433step1 raw2433step0; decide +kernel
      have hl : raw2433step0Labels = labelEmbedding7 ∘ raw2433step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2433step0 raw2433step0Labels raw2433step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

theorem canonical2434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2434 raw2434Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw2434 raw2434Labels = mixedMoment B raw2434step0 raw2434step0Labels := by
      have ha : raw2434step0 = (fun i j => raw2434 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2434step0 raw2434; decide +kernel
      have hl : raw2434step0Labels = raw2434Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2434 raw2434Labels permutation152 permutation4
    _ = mixedMoment B node3721 node3721Labels := by rfl

theorem canonical2435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2435 raw2435Labels = mixedMoment B node3836 node3836Labels := by
  calc
    mixedMoment B raw2435 raw2435Labels = mixedMoment B raw2435step0 raw2435step0Labels := by
      have ha : raw2435step0 = (fun i j => raw2435 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2435step0 raw2435; decide +kernel
      have hl : raw2435step0Labels = raw2435Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2435 raw2435Labels permutation176 permutation6
    mixedMoment B raw2435step0 raw2435step0Labels = mixedMoment B raw2435step1 raw2435step1Labels := by
      have ha : raw2435step1 = -raw2435step0 := by apply Matrix.ext; change ∀ i j, raw2435step1 i j = -(raw2435step0 i j); unfold raw2435step1 raw2435step0; decide +kernel
      have hl : raw2435step1Labels = raw2435step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2435step1 raw2435step1Labels = mixedMoment B raw2435step2 raw2435step2Labels := by
      have ha : raw2435step2 = raw2435step1 := by apply Matrix.ext; unfold raw2435step2 raw2435step1; decide +kernel
      have hl : raw2435step1Labels = labelEmbedding1 ∘ raw2435step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2435step1 raw2435step1Labels raw2435step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3836 node3836Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical97
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12532 raw12532Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw12532 raw12532Labels = mixedMoment B raw12532step0 raw12532step0Labels := by
      have hz : ∀ j, raw12532 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12532step0 = (fun i j => raw12532 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12532step0 raw12532; decide +kernel
      have hl : raw12532step0Labels = raw12532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12532 raw12532Labels permutation265 hz
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical12533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12533 raw12533Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw12533 raw12533Labels = mixedMoment B raw12533step0 raw12533step0Labels := by
      have hz : ∀ j, raw12533 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12533step0 = (fun i j => raw12533 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12533step0 raw12533; decide +kernel
      have hl : raw12533step0Labels = raw12533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12533 raw12533Labels permutation434 hz
    mixedMoment B raw12533step0 raw12533step0Labels = mixedMoment B raw12533step1 raw12533step1Labels := by
      have hz : ∀ j, raw12533step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12533step1 = (fun i j => raw12533step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12533step1 raw12533step0; decide +kernel
      have hl : raw12533step1Labels = raw12533step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12533step0 raw12533step0Labels permutation56 hz
    _ = mixedMoment B node5454 node5454Labels := by rfl

theorem canonical12534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12534 raw12534Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw12534 raw12534Labels = mixedMoment B raw12534step0 raw12534step0Labels := by
      have hz : ∀ j, raw12534 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12534step0 = (fun i j => raw12534 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12534step0 raw12534; decide +kernel
      have hl : raw12534step0Labels = raw12534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12534 raw12534Labels permutation520 hz
    mixedMoment B raw12534step0 raw12534step0Labels = mixedMoment B raw12534step1 raw12534step1Labels := by
      have hz : ∀ j, raw12534step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12534step1 = (fun i j => raw12534step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12534step1 raw12534step0; decide +kernel
      have hl : raw12534step1Labels = raw12534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12534step0 raw12534step0Labels permutation56 hz
    _ = mixedMoment B node5454 node5454Labels := by rfl

theorem canonical12535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12535 raw12535Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw12535 raw12535Labels = mixedMoment B raw12535step0 raw12535step0Labels := by
      have hz : ∀ j, raw12535 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12535step0 = (fun i j => raw12535 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12535step0 raw12535; decide +kernel
      have hl : raw12535step0Labels = raw12535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12535 raw12535Labels permutation265 hz
    mixedMoment B raw12535step0 raw12535step0Labels = mixedMoment B raw12535step1 raw12535step1Labels := by
      have ha : raw12535step1 = (fun i j => raw12535step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12535step1 raw12535step0; decide +kernel
      have hl : raw12535step1Labels = raw12535step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12535step0 raw12535step0Labels permutation36 permutation2
    _ = mixedMoment B node5452 node5452Labels := by rfl

theorem canonical12542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12542 raw12542Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw12542 raw12542Labels = mixedMoment B raw12542step0 raw12542step0Labels := by
      have ha : raw12542step0 = (fun i j => raw12542 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12542step0 raw12542; decide +kernel
      have hl : raw12542step0Labels = raw12542Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12542 raw12542Labels permutation160 permutation2
    _ = mixedMoment B node5167 node5167Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12547 raw12547Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw12547 raw12547Labels = mixedMoment B raw12547step0 raw12547step0Labels := by
      have ha : raw12547step0 = (fun i j => raw12547 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12547step0 raw12547; decide +kernel
      have hl : raw12547step0Labels = raw12547Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12547 raw12547Labels permutation155 permutation2
    _ = mixedMoment B node5149 node5149Labels := by rfl

theorem canonical12552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12552 raw12552Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw12552 raw12552Labels = mixedMoment B raw12552step0 raw12552step0Labels := by
      have ha : raw12552step0 = (fun i j => raw12552 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12552step0 raw12552; decide +kernel
      have hl : raw12552step0Labels = raw12552Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12552 raw12552Labels permutation153 permutation2
    _ = mixedMoment B node5149 node5149Labels := by rfl

theorem canonical12557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12557 raw12557Labels = mixedMoment B node5148 node5148Labels := by
  calc
    _ = mixedMoment B node5148 node5148Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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

theorem singleton5380 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5380 node5380Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3721 node3721Labels + mixedMoment B node3836 node3836Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2433 singletonSmall5380
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5380) = raw2433Labels := by decide +kernel
  rw [hl, canonical2433 B hB] at h
  have hc0 : mixedMoment B raw2433 (Fin.cases (0 : Fin 2) singletonSmall5380) =
      mixedMoment B node3721 node3721Labels := by
    have ha : raw2433 = raw2434 := by apply Matrix.ext; unfold raw2433 raw2434; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5380 = raw2434Labels := by decide +kernel
    rw [ha, hj, canonical2434 B hB]
  have hc1 : mixedMoment B raw2433 (Fin.cases (1 : Fin 2) singletonSmall5380) =
      mixedMoment B node3836 node3836Labels := by
    have ha : raw2433 = raw2435 := by apply Matrix.ext; unfold raw2433 raw2435; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5380 = raw2435Labels := by decide +kernel
    rw [ha, hj, canonical2435 B hB]
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

theorem zero5440 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5440 node5440Labels = 0 := by
  exact mixedMoment_order_one B hB node5440 node5440Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5454 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5454 node5454Labels = 0 := by
  exact mixedMoment_order_one B hB node5454 node5454Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5481 node5481Labels = 0 := by
  exact mixedMoment_alpha B hF node5481 node5481Labels 2 permutation158
    (by decide +kernel)

theorem zero5489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5489 node5489Labels = 0 := by
  exact mixedMoment_alpha B hF node5489 node5489Labels 2 permutation152
    (by decide +kernel)

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

theorem sound2924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2924 node2924Labels = Sparse.eval nodeValue2924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2924) = mixedMoment B node2924 node2924Labels := rfl
  simpa [nodeValue2924, Sparse.eval] using hc.symm

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

theorem sound3721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3721 node3721Labels = Sparse.eval nodeValue3721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3721) = mixedMoment B node3721 node3721Labels := rfl
  simpa [nodeValue3721, Sparse.eval] using hc.symm

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

theorem sound3801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3801 node3801Labels = Sparse.eval nodeValue3801 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3801) = mixedMoment B node3801 node3801Labels := rfl
  simpa [nodeValue3801, Sparse.eval] using hc.symm

theorem sound3812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3812 node3812Labels = Sparse.eval nodeValue3812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3812) = mixedMoment B node3812 node3812Labels := rfl
  simpa [nodeValue3812, Sparse.eval] using hc.symm

theorem sound3836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3836 node3836Labels = Sparse.eval nodeValue3836 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3836) = mixedMoment B node3836 node3836Labels := rfl
  simpa [nodeValue3836, Sparse.eval] using hc.symm

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

theorem sound3875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3875 node3875Labels = Sparse.eval nodeValue3875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3875) = mixedMoment B node3875 node3875Labels := rfl
  simpa [nodeValue3875, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5148 node5148Labels = 0 := by
  exact mixedMoment_alpha B hF node5148 node5148Labels 1 permutation152
    (by decide +kernel)

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

theorem sound5148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5148 node5148Labels = Sparse.eval nodeValue5148 (mixedVector B) := by
  simpa only [nodeValue5148, Sparse.eval_nil] using zero5148 B _hB _hF

theorem sound5149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5149 node5149Labels = Sparse.eval nodeValue5149 (mixedVector B) := by
  have h := singleton5149 B _hB
  rw [sound2924 B _hB _hF, sound3605 B _hB _hF] at h
  norm_num [nodeValue5149, nodeValue2924, nodeValue3605, Sparse.eval] at h ⊢
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

theorem sound5380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5380 node5380Labels = Sparse.eval nodeValue5380 (mixedVector B) := by
  have h := singleton5380 B _hB
  rw [sound3721 B _hB _hF, sound3836 B _hB _hF] at h
  norm_num [nodeValue5380, nodeValue3721, nodeValue3836, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5397 node5397Labels = Sparse.eval nodeValue5397 (mixedVector B) := by
  have h := singleton5397 B _hB
  rw [sound3782 B _hB _hF, sound3796 B _hB _hF] at h
  norm_num [nodeValue5397, nodeValue3782, nodeValue3796, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5406 node5406Labels = Sparse.eval nodeValue5406 (mixedVector B) := by
  have h := singleton5406 B _hB
  rw [sound3801 B _hB _hF, sound3812 B _hB _hF] at h
  norm_num [nodeValue5406, nodeValue3801, nodeValue3812, Sparse.eval] at h ⊢
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

theorem sound5440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5440 node5440Labels = Sparse.eval nodeValue5440 (mixedVector B) := by
  simpa only [nodeValue5440, Sparse.eval_nil] using zero5440 B _hB _hF

theorem sound5454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5454 node5454Labels = Sparse.eval nodeValue5454 (mixedVector B) := by
  simpa only [nodeValue5454, Sparse.eval_nil] using zero5454 B _hB _hF

theorem sound5481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5481 node5481Labels = Sparse.eval nodeValue5481 (mixedVector B) := by
  simpa only [nodeValue5481, Sparse.eval_nil] using zero5481 B _hB _hF

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

theorem sourceEq1098 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1098 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1098 + difference 0 1) (sourceB1098 + difference 1 0) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1098 + difference 0 1) (sourceB1098 + difference 1 0) sourceC1098) = raw18359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18359; decide +kernel
    rw [ha]
    exact (canonical18359 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1098 + difference 0 2) (sourceB1098 + difference 2 0) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA1098 + difference 0 2) (sourceB1098 + difference 2 0) sourceC1098) = raw18360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18360; decide +kernel
    rw [ha]
    exact (canonical18360 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1098 + difference 0 3) (sourceB1098 + difference 3 0) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1098 + difference 0 3) (sourceB1098 + difference 3 0) sourceC1098) = raw18361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18361; decide +kernel
    rw [ha]
    exact (canonical18361 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1098 + difference 0 4) (sourceB1098 + difference 4 0) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA1098 + difference 0 4) (sourceB1098 + difference 4 0) sourceC1098) = raw18362 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18362; decide +kernel
    rw [ha]
    exact (canonical18362 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1098 + difference 0 5) (sourceB1098 + difference 5 0) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5489) := by
    have ha : (tripleCharges (sourceA1098 + difference 0 5) (sourceB1098 + difference 5 0) sourceC1098) = raw18363 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18363; decide +kernel
    rw [ha]
    exact (canonical18363 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1098 + difference 1 0) (sourceB1098 + difference 0 1) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1098 + difference 1 0) (sourceB1098 + difference 0 1) sourceC1098) = raw18364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18364; decide +kernel
    rw [ha]
    exact (canonical18364 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1098 + difference 1 2) (sourceB1098 + difference 2 1) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1098 + difference 1 2) (sourceB1098 + difference 2 1) sourceC1098) = raw12532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw12532; decide +kernel
    rw [ha]
    exact (canonical12532 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1098 + difference 1 3) (sourceB1098 + difference 3 1) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA1098 + difference 1 3) (sourceB1098 + difference 3 1) sourceC1098) = raw12533 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw12533; decide +kernel
    rw [ha]
    exact (canonical12533 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1098 + difference 1 4) (sourceB1098 + difference 4 1) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA1098 + difference 1 4) (sourceB1098 + difference 4 1) sourceC1098) = raw12534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw12534; decide +kernel
    rw [ha]
    exact (canonical12534 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1098 + difference 1 5) (sourceB1098 + difference 5 1) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA1098 + difference 1 5) (sourceB1098 + difference 5 1) sourceC1098) = raw12535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw12535; decide +kernel
    rw [ha]
    exact (canonical12535 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1098 + difference 2 0) (sourceB1098 + difference 0 2) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA1098 + difference 2 0) (sourceB1098 + difference 0 2) sourceC1098) = raw12542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw12542; decide +kernel
    rw [ha]
    exact (canonical12542 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1098 + difference 2 1) (sourceB1098 + difference 1 2) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5386) := by
    have ha : (tripleCharges (sourceA1098 + difference 2 1) (sourceB1098 + difference 1 2) sourceC1098) = raw18365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18365; decide +kernel
    rw [ha]
    exact (canonical18365 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1098 + difference 2 3) (sourceB1098 + difference 3 2) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1098 + difference 2 3) (sourceB1098 + difference 3 2) sourceC1098) = raw18366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18366; decide +kernel
    rw [ha]
    exact (canonical18366 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1098 + difference 2 4) (sourceB1098 + difference 4 2) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1098 + difference 2 4) (sourceB1098 + difference 4 2) sourceC1098) = raw18367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18367; decide +kernel
    rw [ha]
    exact (canonical18367 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1098 + difference 2 5) (sourceB1098 + difference 5 2) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1098 + difference 2 5) (sourceB1098 + difference 5 2) sourceC1098) = raw18368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18368; decide +kernel
    rw [ha]
    exact (canonical18368 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1098 + difference 3 0) (sourceB1098 + difference 0 3) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA1098 + difference 3 0) (sourceB1098 + difference 0 3) sourceC1098) = raw12547 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw12547; decide +kernel
    rw [ha]
    exact (canonical12547 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1098 + difference 3 1) (sourceB1098 + difference 1 3) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1098 + difference 3 1) (sourceB1098 + difference 1 3) sourceC1098) = raw18369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18369; decide +kernel
    rw [ha]
    exact (canonical18369 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1098 + difference 3 2) (sourceB1098 + difference 2 3) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1098 + difference 3 2) (sourceB1098 + difference 2 3) sourceC1098) = raw18370 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18370; decide +kernel
    rw [ha]
    exact (canonical18370 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1098 + difference 3 4) (sourceB1098 + difference 4 3) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1098 + difference 3 4) (sourceB1098 + difference 4 3) sourceC1098) = raw18371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18371; decide +kernel
    rw [ha]
    exact (canonical18371 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1098 + difference 3 5) (sourceB1098 + difference 5 3) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1098 + difference 3 5) (sourceB1098 + difference 5 3) sourceC1098) = raw18372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18372; decide +kernel
    rw [ha]
    exact (canonical18372 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1098 + difference 4 0) (sourceB1098 + difference 0 4) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA1098 + difference 4 0) (sourceB1098 + difference 0 4) sourceC1098) = raw12552 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw12552; decide +kernel
    rw [ha]
    exact (canonical12552 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1098 + difference 4 1) (sourceB1098 + difference 1 4) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA1098 + difference 4 1) (sourceB1098 + difference 1 4) sourceC1098) = raw18373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18373; decide +kernel
    rw [ha]
    exact (canonical18373 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1098 + difference 4 2) (sourceB1098 + difference 2 4) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA1098 + difference 4 2) (sourceB1098 + difference 2 4) sourceC1098) = raw18374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18374; decide +kernel
    rw [ha]
    exact (canonical18374 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1098 + difference 4 3) (sourceB1098 + difference 3 4) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA1098 + difference 4 3) (sourceB1098 + difference 3 4) sourceC1098) = raw18375 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18375; decide +kernel
    rw [ha]
    exact (canonical18375 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1098 + difference 4 5) (sourceB1098 + difference 5 4) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA1098 + difference 4 5) (sourceB1098 + difference 5 4) sourceC1098) = raw18376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18376; decide +kernel
    rw [ha]
    exact (canonical18376 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1098 + difference 5 0) (sourceB1098 + difference 0 5) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA1098 + difference 5 0) (sourceB1098 + difference 0 5) sourceC1098) = raw12557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw12557; decide +kernel
    rw [ha]
    exact (canonical12557 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1098 + difference 5 1) (sourceB1098 + difference 1 5) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA1098 + difference 5 1) (sourceB1098 + difference 1 5) sourceC1098) = raw18377 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18377; decide +kernel
    rw [ha]
    exact (canonical18377 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1098 + difference 5 2) (sourceB1098 + difference 2 5) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA1098 + difference 5 2) (sourceB1098 + difference 2 5) sourceC1098) = raw18378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18378; decide +kernel
    rw [ha]
    exact (canonical18378 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1098 + difference 5 3) (sourceB1098 + difference 3 5) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1098 + difference 5 3) (sourceB1098 + difference 3 5) sourceC1098) = raw18379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18379; decide +kernel
    rw [ha]
    exact (canonical18379 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1098 + difference 5 4) (sourceB1098 + difference 4 5) sourceC1098) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA1098 + difference 5 4) (sourceB1098 + difference 4 5) sourceC1098) = raw18380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1098 sourceB1098 sourceC1098 difference raw18380; decide +kernel
    rw [ha]
    exact (canonical18380 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1098 sourceB1098 sourceC1098
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1098, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck951 : Integer.Sparse.reindex keyMap MixedData.row951 = numericRow951 := by decide +kernel

theorem numericCheck951 (x : Master → ℝ) : Integer.Sparse.eval numericRow951 x =
    (17280 : ℝ) * reducedSource951 x := by
  norm_num [numericRow951, reducedSource951, Integer.Sparse.eval, Sparse.eval, nodeValue5148, nodeValue5149, nodeValue5167, nodeValue5292, nodeValue5378, nodeValue5380, nodeValue5386, nodeValue5397, nodeValue5406, nodeValue5422, nodeValue5431, nodeValue5433, nodeValue5434, nodeValue5435, nodeValue5440, nodeValue5450, nodeValue5452, nodeValue5454, nodeValue5481, nodeValue5489, nodeValue5490] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero951 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource951 (mixedVector B) = 0 := by
  have h5148 : mixedVector B (Sum.inr 5148) = Sparse.eval nodeValue5148 (mixedVector B) := by
    change mixedMoment B node5148 node5148Labels = _
    exact sound5148 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5167 : mixedVector B (Sum.inr 5167) = Sparse.eval nodeValue5167 (mixedVector B) := by
    change mixedMoment B node5167 node5167Labels = _
    exact sound5167_e B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292_e B hB hF
  have h5378 : mixedVector B (Sum.inr 5378) = Sparse.eval nodeValue5378 (mixedVector B) := by
    change mixedMoment B node5378 node5378Labels = _
    exact sound5378 B hB hF
  have h5380 : mixedVector B (Sum.inr 5380) = Sparse.eval nodeValue5380 (mixedVector B) := by
    change mixedMoment B node5380 node5380Labels = _
    exact sound5380 B hB hF
  have h5386 : mixedVector B (Sum.inr 5386) = Sparse.eval nodeValue5386 (mixedVector B) := by
    change mixedMoment B node5386 node5386Labels = _
    exact sound5386_e B hB hF
  have h5397 : mixedVector B (Sum.inr 5397) = Sparse.eval nodeValue5397 (mixedVector B) := by
    change mixedMoment B node5397 node5397Labels = _
    exact sound5397 B hB hF
  have h5406 : mixedVector B (Sum.inr 5406) = Sparse.eval nodeValue5406 (mixedVector B) := by
    change mixedMoment B node5406 node5406Labels = _
    exact sound5406 B hB hF
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
  have h5435 : mixedVector B (Sum.inr 5435) = Sparse.eval nodeValue5435 (mixedVector B) := by
    change mixedMoment B node5435 node5435Labels = _
    exact sound5435_e B hB hF
  have h5440 : mixedVector B (Sum.inr 5440) = Sparse.eval nodeValue5440 (mixedVector B) := by
    change mixedMoment B node5440 node5440Labels = _
    exact sound5440 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450_e B hB hF
  have h5452 : mixedVector B (Sum.inr 5452) = Sparse.eval nodeValue5452 (mixedVector B) := by
    change mixedMoment B node5452 node5452Labels = _
    exact sound5452_e B hB hF
  have h5454 : mixedVector B (Sum.inr 5454) = Sparse.eval nodeValue5454 (mixedVector B) := by
    change mixedMoment B node5454 node5454Labels = _
    exact sound5454 B hB hF
  have h5481 : mixedVector B (Sum.inr 5481) = Sparse.eval nodeValue5481 (mixedVector B) := by
    change mixedMoment B node5481 node5481Labels = _
    exact sound5481 B hB hF
  have h5489 : mixedVector B (Sum.inr 5489) = Sparse.eval nodeValue5489 (mixedVector B) := by
    change mixedMoment B node5489 node5489Labels = _
    exact sound5489 B hB hF
  have h5490 : mixedVector B (Sum.inr 5490) = Sparse.eval nodeValue5490 (mixedVector B) := by
    change mixedMoment B node5490 node5490Labels = _
    exact sound5490_e B hB hF
  simpa only [sourceForm1098, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5148, h5149, h5167, h5292, h5378, h5380, h5386, h5397, h5406, h5422, h5431, h5433, h5434, h5435, h5440, h5450, h5452, h5454, h5481, h5489, h5490, reducedSource951] using sourceEq1098 B hB

theorem rowSound951_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row951 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck951, numericCheck951, reducedZero951 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound951_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound951_e_oai
