-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T23:00:18.581633+00:00
-- url     : https://prove2.me/submissions/47247aeb-1e1f-4c35-ae4c-a04372cca33d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E109
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5168_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5416_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5464_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5465_e

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

theorem canonical1701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1701 raw1701Labels = mixedMoment B node4767 node4767Labels := by
  calc
    mixedMoment B raw1701 raw1701Labels = mixedMoment B raw1701step0 raw1701step0Labels := by
      have ha : raw1701step0 = (fun i j => raw1701 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1701step0 raw1701; decide +kernel
      have hl : raw1701step0Labels = raw1701Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1701 raw1701Labels permutation152 permutation4
    mixedMoment B raw1701step0 raw1701step0Labels = mixedMoment B raw1701step1 raw1701step1Labels := by
      have ha : raw1701step1 = raw1701step0 := by apply Matrix.ext; unfold raw1701step1 raw1701step0; decide +kernel
      have hl : raw1701step0Labels = labelEmbedding7 ∘ raw1701step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1701step0 raw1701step0Labels raw1701step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4767 node4767Labels := by rfl

theorem canonical1702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1702 raw1702Labels = mixedMoment B node1967 node1967Labels := by
  calc
    mixedMoment B raw1702 raw1702Labels = mixedMoment B raw1702step0 raw1702step0Labels := by
      have ha : raw1702step0 = (fun i j => raw1702 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1702step0 raw1702; decide +kernel
      have hl : raw1702step0Labels = raw1702Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1702 raw1702Labels permutation152 permutation4
    _ = mixedMoment B node1967 node1967Labels := by rfl

theorem canonical1703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1703 raw1703Labels = mixedMoment B node2183 node2183Labels := by
  calc
    mixedMoment B raw1703 raw1703Labels = mixedMoment B raw1703step0 raw1703step0Labels := by
      have ha : raw1703step0 = (fun i j => raw1703 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1703step0 raw1703; decide +kernel
      have hl : raw1703step0Labels = raw1703Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1703 raw1703Labels permutation152 permutation6
    mixedMoment B raw1703step0 raw1703step0Labels = mixedMoment B raw1703step1 raw1703step1Labels := by
      have ha : raw1703step1 = -raw1703step0 := by apply Matrix.ext; change ∀ i j, raw1703step1 i j = -(raw1703step0 i j); unfold raw1703step1 raw1703step0; decide +kernel
      have hl : raw1703step1Labels = raw1703step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1703step1 raw1703step1Labels = mixedMoment B raw1703step2 raw1703step2Labels := by
      have ha : raw1703step2 = raw1703step1 := by apply Matrix.ext; unfold raw1703step2 raw1703step1; decide +kernel
      have hl : raw1703step1Labels = labelEmbedding1 ∘ raw1703step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1703step1 raw1703step1Labels raw1703step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2183 node2183Labels := by rfl

theorem canonical1704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1704 raw1704Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw1704 raw1704Labels = mixedMoment B raw1704step0 raw1704step0Labels := by
      have ha : raw1704step0 = (fun i j => raw1704 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1704step0 raw1704; decide +kernel
      have hl : raw1704step0Labels = raw1704Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1704 raw1704Labels permutation32 permutation4
    mixedMoment B raw1704step0 raw1704step0Labels = mixedMoment B raw1704step1 raw1704step1Labels := by
      have ha : raw1704step1 = raw1704step0 := by apply Matrix.ext; unfold raw1704step1 raw1704step0; decide +kernel
      have hl : raw1704step0Labels = labelEmbedding7 ∘ raw1704step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1704step0 raw1704step0Labels raw1704step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4769 node4769Labels := by rfl

theorem canonical1705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1705 raw1705Labels = mixedMoment B node1969 node1969Labels := by
  calc
    mixedMoment B raw1705 raw1705Labels = mixedMoment B raw1705step0 raw1705step0Labels := by
      have ha : raw1705step0 = (fun i j => raw1705 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1705step0 raw1705; decide +kernel
      have hl : raw1705step0Labels = raw1705Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1705 raw1705Labels permutation32 permutation4
    _ = mixedMoment B node1969 node1969Labels := by rfl

theorem canonical1706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1706 raw1706Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw1706 raw1706Labels = mixedMoment B raw1706step0 raw1706step0Labels := by
      have ha : raw1706step0 = (fun i j => raw1706 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1706step0 raw1706; decide +kernel
      have hl : raw1706step0Labels = raw1706Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1706 raw1706Labels permutation32 permutation6
    mixedMoment B raw1706step0 raw1706step0Labels = mixedMoment B raw1706step1 raw1706step1Labels := by
      have ha : raw1706step1 = -raw1706step0 := by apply Matrix.ext; change ∀ i j, raw1706step1 i j = -(raw1706step0 i j); unfold raw1706step1 raw1706step0; decide +kernel
      have hl : raw1706step1Labels = raw1706step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1706step1 raw1706step1Labels = mixedMoment B raw1706step2 raw1706step2Labels := by
      have ha : raw1706step2 = raw1706step1 := by apply Matrix.ext; unfold raw1706step2 raw1706step1; decide +kernel
      have hl : raw1706step1Labels = labelEmbedding1 ∘ raw1706step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1706step1 raw1706step1Labels raw1706step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2185 node2185Labels := by rfl

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

theorem canonical1902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1902 raw1902Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw1902 raw1902Labels = mixedMoment B raw1902step0 raw1902step0Labels := by
      have ha : raw1902step0 = (fun i j => raw1902 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1902step0 raw1902; decide +kernel
      have hl : raw1902step0Labels = raw1902Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1902 raw1902Labels permutation152 permutation4
    mixedMoment B raw1902step0 raw1902step0Labels = mixedMoment B raw1902step1 raw1902step1Labels := by
      have ha : raw1902step1 = raw1902step0 := by apply Matrix.ext; unfold raw1902step1 raw1902step0; decide +kernel
      have hl : raw1902step0Labels = labelEmbedding7 ∘ raw1902step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1902step0 raw1902step0Labels raw1902step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

theorem canonical1903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1903 raw1903Labels = mixedMoment B node2330 node2330Labels := by
  calc
    mixedMoment B raw1903 raw1903Labels = mixedMoment B raw1903step0 raw1903step0Labels := by
      have ha : raw1903step0 = (fun i j => raw1903 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1903step0 raw1903; decide +kernel
      have hl : raw1903step0Labels = raw1903Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1903 raw1903Labels permutation152 permutation4
    _ = mixedMoment B node2330 node2330Labels := by rfl

theorem canonical1904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1904 raw1904Labels = mixedMoment B node3404 node3404Labels := by
  calc
    mixedMoment B raw1904 raw1904Labels = mixedMoment B raw1904step0 raw1904step0Labels := by
      have ha : raw1904step0 = (fun i j => raw1904 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1904step0 raw1904; decide +kernel
      have hl : raw1904step0Labels = raw1904Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1904 raw1904Labels permutation152 permutation6
    mixedMoment B raw1904step0 raw1904step0Labels = mixedMoment B raw1904step1 raw1904step1Labels := by
      have ha : raw1904step1 = -raw1904step0 := by apply Matrix.ext; change ∀ i j, raw1904step1 i j = -(raw1904step0 i j); unfold raw1904step1 raw1904step0; decide +kernel
      have hl : raw1904step1Labels = raw1904step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1904step1 raw1904step1Labels = mixedMoment B raw1904step2 raw1904step2Labels := by
      have ha : raw1904step2 = raw1904step1 := by apply Matrix.ext; unfold raw1904step2 raw1904step1; decide +kernel
      have hl : raw1904step1Labels = labelEmbedding1 ∘ raw1904step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1904step1 raw1904step1Labels raw1904step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3404 node3404Labels := by rfl

theorem canonical1911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1911 raw1911Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw1911 raw1911Labels = mixedMoment B raw1911step0 raw1911step0Labels := by
      have ha : raw1911step0 = (fun i j => raw1911 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1911step0 raw1911; decide +kernel
      have hl : raw1911step0Labels = raw1911Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1911 raw1911Labels permutation32 permutation4
    mixedMoment B raw1911step0 raw1911step0Labels = mixedMoment B raw1911step1 raw1911step1Labels := by
      have ha : raw1911step1 = raw1911step0 := by apply Matrix.ext; unfold raw1911step1 raw1911step0; decide +kernel
      have hl : raw1911step0Labels = labelEmbedding7 ∘ raw1911step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1911step0 raw1911step0Labels raw1911step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4946 node4946Labels := by rfl

theorem canonical1912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1912 raw1912Labels = mixedMoment B node2337 node2337Labels := by
  calc
    mixedMoment B raw1912 raw1912Labels = mixedMoment B raw1912step0 raw1912step0Labels := by
      have ha : raw1912step0 = (fun i j => raw1912 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1912step0 raw1912; decide +kernel
      have hl : raw1912step0Labels = raw1912Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1912 raw1912Labels permutation32 permutation4
    _ = mixedMoment B node2337 node2337Labels := by rfl

theorem canonical1913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1913 raw1913Labels = mixedMoment B node3412 node3412Labels := by
  calc
    mixedMoment B raw1913 raw1913Labels = mixedMoment B raw1913step0 raw1913step0Labels := by
      have ha : raw1913step0 = (fun i j => raw1913 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1913step0 raw1913; decide +kernel
      have hl : raw1913step0Labels = raw1913Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1913 raw1913Labels permutation32 permutation6
    mixedMoment B raw1913step0 raw1913step0Labels = mixedMoment B raw1913step1 raw1913step1Labels := by
      have ha : raw1913step1 = -raw1913step0 := by apply Matrix.ext; change ∀ i j, raw1913step1 i j = -(raw1913step0 i j); unfold raw1913step1 raw1913step0; decide +kernel
      have hl : raw1913step1Labels = raw1913step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1913step1 raw1913step1Labels = mixedMoment B raw1913step2 raw1913step2Labels := by
      have ha : raw1913step2 = raw1913step1 := by apply Matrix.ext; unfold raw1913step2 raw1913step1; decide +kernel
      have hl : raw1913step1Labels = labelEmbedding1 ∘ raw1913step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1913step1 raw1913step1Labels raw1913step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3412 node3412Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical148
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19003 raw19003Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw19003 raw19003Labels = mixedMoment B raw19003step0 raw19003step0Labels := by
      have hz : ∀ j, raw19003 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19003step0 = (fun i j => raw19003 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19003step0 raw19003; decide +kernel
      have hl : raw19003step0Labels = raw19003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19003 raw19003Labels permutation346 hz
    mixedMoment B raw19003step0 raw19003step0Labels = mixedMoment B raw19003step1 raw19003step1Labels := by
      have ha : raw19003step1 = (fun i j => raw19003step0 (permutation60 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19003step1 raw19003step0; decide +kernel
      have hl : raw19003step1Labels = raw19003step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19003step0 raw19003step0Labels permutation60 permutation2
    _ = mixedMoment B node5486 node5486Labels := by rfl

theorem canonical19012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19012 raw19012Labels = mixedMoment B node5464 node5464Labels := by
  calc
    mixedMoment B raw19012 raw19012Labels = mixedMoment B raw19012step0 raw19012step0Labels := by
      have ha : raw19012step0 = (fun i j => raw19012 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19012step0 raw19012; decide +kernel
      have hl : raw19012step0Labels = raw19012Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19012 raw19012Labels permutation156 permutation2
    _ = mixedMoment B node5464 node5464Labels := by rfl

theorem canonical19017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19017 raw19017Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw19017 raw19017Labels = mixedMoment B raw19017step0 raw19017step0Labels := by
      have hz : ∀ j, raw19017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19017step0 = (fun i j => raw19017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19017step0 raw19017; decide +kernel
      have hl : raw19017step0Labels = raw19017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19017 raw19017Labels permutation346 hz
    mixedMoment B raw19017step0 raw19017step0Labels = mixedMoment B raw19017step1 raw19017step1Labels := by
      have ha : raw19017step1 = (fun i j => raw19017step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19017step1 raw19017step0; decide +kernel
      have hl : raw19017step1Labels = raw19017step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19017step0 raw19017step0Labels permutation37 permutation2
    _ = mixedMoment B node5465 node5465Labels := by rfl

theorem canonical19022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19022 raw19022Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw19022 raw19022Labels = mixedMoment B raw19022step0 raw19022step0Labels := by
      have hz : ∀ j, raw19022 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19022step0 = (fun i j => raw19022 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19022step0 raw19022; decide +kernel
      have hl : raw19022step0Labels = raw19022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19022 raw19022Labels permutation346 hz
    mixedMoment B raw19022step0 raw19022step0Labels = mixedMoment B raw19022step1 raw19022step1Labels := by
      have ha : raw19022step1 = (fun i j => raw19022step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19022step1 raw19022step0; decide +kernel
      have hl : raw19022step1Labels = raw19022step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19022step0 raw19022step0Labels permutation36 permutation2
    _ = mixedMoment B node5465 node5465Labels := by rfl

theorem canonical19027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19027 raw19027Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw19027 raw19027Labels = mixedMoment B raw19027step0 raw19027step0Labels := by
      have ha : raw19027step0 = (fun i j => raw19027 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19027step0 raw19027; decide +kernel
      have hl : raw19027step0Labels = raw19027Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19027 raw19027Labels permutation662 permutation3
    mixedMoment B raw19027step0 raw19027step0Labels = mixedMoment B raw19027step1 raw19027step1Labels := by
      have ha : raw19027step1 = -raw19027step0 := by apply Matrix.ext; change ∀ i j, raw19027step1 i j = -(raw19027step0 i j); unfold raw19027step1 raw19027step0; decide +kernel
      have hl : raw19027step1Labels = raw19027step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19027step1 raw19027step1Labels = mixedMoment B raw19027step2 raw19027step2Labels := by
      have ha : raw19027step2 = raw19027step1 := by apply Matrix.ext; unfold raw19027step2 raw19027step1; decide +kernel
      have hl : raw19027step1Labels = labelEmbedding6 ∘ raw19027step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19027step1 raw19027step1Labels raw19027step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5416 node5416Labels := by rfl

theorem canonical19028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19028 raw19028Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw19028 raw19028Labels = mixedMoment B raw19028step0 raw19028step0Labels := by
      have hz : ∀ j, raw19028 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19028step0 = (fun i j => raw19028 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19028step0 raw19028; decide +kernel
      have hl : raw19028step0Labels = raw19028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19028 raw19028Labels permutation346 hz
    mixedMoment B raw19028step0 raw19028step0Labels = mixedMoment B raw19028step1 raw19028step1Labels := by
      have ha : raw19028step1 = (fun i j => raw19028step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19028step1 raw19028step0; decide +kernel
      have hl : raw19028step1Labels = raw19028step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19028step0 raw19028step0Labels permutation145 permutation3
    mixedMoment B raw19028step1 raw19028step1Labels = mixedMoment B raw19028step2 raw19028step2Labels := by
      have ha : raw19028step2 = -raw19028step1 := by apply Matrix.ext; change ∀ i j, raw19028step2 i j = -(raw19028step1 i j); unfold raw19028step2 raw19028step1; decide +kernel
      have hl : raw19028step2Labels = raw19028step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19028step2 raw19028step2Labels = mixedMoment B raw19028step3 raw19028step3Labels := by
      have ha : raw19028step3 = raw19028step2 := by apply Matrix.ext; unfold raw19028step3 raw19028step2; decide +kernel
      have hl : raw19028step2Labels = labelEmbedding6 ∘ raw19028step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19028step2 raw19028step2Labels raw19028step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

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

theorem canonical2376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2376 raw2376Labels = mixedMoment B node5337 node5337Labels := by
  calc
    mixedMoment B raw2376 raw2376Labels = mixedMoment B raw2376step0 raw2376step0Labels := by
      have ha : raw2376step0 = (fun i j => raw2376 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2376step0 raw2376; decide +kernel
      have hl : raw2376step0Labels = raw2376Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2376 raw2376Labels permutation152 permutation4
    mixedMoment B raw2376step0 raw2376step0Labels = mixedMoment B raw2376step1 raw2376step1Labels := by
      have ha : raw2376step1 = raw2376step0 := by apply Matrix.ext; unfold raw2376step1 raw2376step0; decide +kernel
      have hl : raw2376step0Labels = labelEmbedding7 ∘ raw2376step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2376step0 raw2376step0Labels raw2376step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5337 node5337Labels := by rfl

theorem canonical2377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2377 raw2377Labels = mixedMoment B node3672 node3672Labels := by
  calc
    mixedMoment B raw2377 raw2377Labels = mixedMoment B raw2377step0 raw2377step0Labels := by
      have ha : raw2377step0 = (fun i j => raw2377 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2377step0 raw2377; decide +kernel
      have hl : raw2377step0Labels = raw2377Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2377 raw2377Labels permutation152 permutation4
    _ = mixedMoment B node3672 node3672Labels := by rfl

theorem canonical2378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2378 raw2378Labels = mixedMoment B node3756 node3756Labels := by
  calc
    mixedMoment B raw2378 raw2378Labels = mixedMoment B raw2378step0 raw2378step0Labels := by
      have ha : raw2378step0 = (fun i j => raw2378 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2378step0 raw2378; decide +kernel
      have hl : raw2378step0Labels = raw2378Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2378 raw2378Labels permutation152 permutation6
    mixedMoment B raw2378step0 raw2378step0Labels = mixedMoment B raw2378step1 raw2378step1Labels := by
      have ha : raw2378step1 = -raw2378step0 := by apply Matrix.ext; change ∀ i j, raw2378step1 i j = -(raw2378step0 i j); unfold raw2378step1 raw2378step0; decide +kernel
      have hl : raw2378step1Labels = raw2378step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2378step1 raw2378step1Labels = mixedMoment B raw2378step2 raw2378step2Labels := by
      have ha : raw2378step2 = raw2378step1 := by apply Matrix.ext; unfold raw2378step2 raw2378step1; decide +kernel
      have hl : raw2378step1Labels = labelEmbedding1 ∘ raw2378step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2378step1 raw2378step1Labels raw2378step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3756 node3756Labels := by rfl

theorem canonical2403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2403 raw2403Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw2403 raw2403Labels = mixedMoment B raw2403step0 raw2403step0Labels := by
      have ha : raw2403step0 = (fun i j => raw2403 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2403step0 raw2403; decide +kernel
      have hl : raw2403step0Labels = raw2403Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2403 raw2403Labels permutation32 permutation4
    mixedMoment B raw2403step0 raw2403step0Labels = mixedMoment B raw2403step1 raw2403step1Labels := by
      have ha : raw2403step1 = raw2403step0 := by apply Matrix.ext; unfold raw2403step1 raw2403step0; decide +kernel
      have hl : raw2403step0Labels = labelEmbedding7 ∘ raw2403step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2403step0 raw2403step0Labels raw2403step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

theorem canonical2404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2404 raw2404Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw2404 raw2404Labels = mixedMoment B raw2404step0 raw2404step0Labels := by
      have ha : raw2404step0 = (fun i j => raw2404 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2404step0 raw2404; decide +kernel
      have hl : raw2404step0Labels = raw2404Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2404 raw2404Labels permutation32 permutation4
    _ = mixedMoment B node3694 node3694Labels := by rfl

theorem canonical2405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2405 raw2405Labels = mixedMoment B node3773 node3773Labels := by
  calc
    mixedMoment B raw2405 raw2405Labels = mixedMoment B raw2405step0 raw2405step0Labels := by
      have ha : raw2405step0 = (fun i j => raw2405 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2405step0 raw2405; decide +kernel
      have hl : raw2405step0Labels = raw2405Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2405 raw2405Labels permutation32 permutation6
    mixedMoment B raw2405step0 raw2405step0Labels = mixedMoment B raw2405step1 raw2405step1Labels := by
      have ha : raw2405step1 = -raw2405step0 := by apply Matrix.ext; change ∀ i j, raw2405step1 i j = -(raw2405step0 i j); unfold raw2405step1 raw2405step0; decide +kernel
      have hl : raw2405step1Labels = raw2405step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2405step1 raw2405step1Labels = mixedMoment B raw2405step2 raw2405step2Labels := by
      have ha : raw2405step2 = raw2405step1 := by apply Matrix.ext; unfold raw2405step2 raw2405step1; decide +kernel
      have hl : raw2405step1Labels = labelEmbedding1 ∘ raw2405step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2405step1 raw2405step1Labels raw2405step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3773 node3773Labels := by rfl

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

theorem canonical2460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2460 raw2460Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw2460 raw2460Labels = mixedMoment B raw2460step0 raw2460step0Labels := by
      have ha : raw2460step0 = (fun i j => raw2460 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2460step0 raw2460; decide +kernel
      have hl : raw2460step0Labels = raw2460Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2460 raw2460Labels permutation152 permutation4
    mixedMoment B raw2460step0 raw2460step0Labels = mixedMoment B raw2460step1 raw2460step1Labels := by
      have ha : raw2460step1 = raw2460step0 := by apply Matrix.ext; unfold raw2460step1 raw2460step0; decide +kernel
      have hl : raw2460step0Labels = labelEmbedding7 ∘ raw2460step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2460step0 raw2460step0Labels raw2460step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

theorem canonical2461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2461 raw2461Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw2461 raw2461Labels = mixedMoment B raw2461step0 raw2461step0Labels := by
      have ha : raw2461step0 = (fun i j => raw2461 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2461step0 raw2461; decide +kernel
      have hl : raw2461step0Labels = raw2461Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2461 raw2461Labels permutation152 permutation4
    _ = mixedMoment B node3779 node3779Labels := by rfl

theorem canonical2462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2462 raw2462Labels = mixedMoment B node3797 node3797Labels := by
  calc
    mixedMoment B raw2462 raw2462Labels = mixedMoment B raw2462step0 raw2462step0Labels := by
      have ha : raw2462step0 = (fun i j => raw2462 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2462step0 raw2462; decide +kernel
      have hl : raw2462step0Labels = raw2462Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2462 raw2462Labels permutation152 permutation6
    mixedMoment B raw2462step0 raw2462step0Labels = mixedMoment B raw2462step1 raw2462step1Labels := by
      have ha : raw2462step1 = -raw2462step0 := by apply Matrix.ext; change ∀ i j, raw2462step1 i j = -(raw2462step0 i j); unfold raw2462step1 raw2462step0; decide +kernel
      have hl : raw2462step1Labels = raw2462step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2462step1 raw2462step1Labels = mixedMoment B raw2462step2 raw2462step2Labels := by
      have ha : raw2462step2 = raw2462step1 := by apply Matrix.ext; unfold raw2462step2 raw2462step1; decide +kernel
      have hl : raw2462step1Labels = labelEmbedding1 ∘ raw2462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2462step1 raw2462step1Labels raw2462step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3797 node3797Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical225
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28885 raw28885Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw28885 raw28885Labels = mixedMoment B raw28885step0 raw28885step0Labels := by
      have hz : ∀ j, raw28885 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28885step0 = (fun i j => raw28885 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28885step0 raw28885; decide +kernel
      have hl : raw28885step0Labels = raw28885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28885 raw28885Labels permutation346 hz
    mixedMoment B raw28885step0 raw28885step0Labels = mixedMoment B raw28885step1 raw28885step1Labels := by
      have ha : raw28885step1 = (fun i j => raw28885step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28885step1 raw28885step0; decide +kernel
      have hl : raw28885step1Labels = raw28885step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28885step0 raw28885step0Labels permutation150 permutation3
    mixedMoment B raw28885step1 raw28885step1Labels = mixedMoment B raw28885step2 raw28885step2Labels := by
      have ha : raw28885step2 = -raw28885step1 := by apply Matrix.ext; change ∀ i j, raw28885step2 i j = -(raw28885step1 i j); unfold raw28885step2 raw28885step1; decide +kernel
      have hl : raw28885step2Labels = raw28885step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28885step2 raw28885step2Labels = mixedMoment B raw28885step3 raw28885step3Labels := by
      have ha : raw28885step3 = raw28885step2 := by apply Matrix.ext; unfold raw28885step3 raw28885step2; decide +kernel
      have hl : raw28885step2Labels = labelEmbedding6 ∘ raw28885step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28885step2 raw28885step2Labels raw28885step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

theorem canonical28893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28893 raw28893Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw28893 raw28893Labels = mixedMoment B raw28893step0 raw28893step0Labels := by
      have hz : ∀ j, raw28893 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28893step0 = (fun i j => raw28893 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28893step0 raw28893; decide +kernel
      have hl : raw28893step0Labels = raw28893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28893 raw28893Labels permutation346 hz
    mixedMoment B raw28893step0 raw28893step0Labels = mixedMoment B raw28893step1 raw28893step1Labels := by
      have ha : raw28893step1 = (fun i j => raw28893step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28893step1 raw28893step0; decide +kernel
      have hl : raw28893step1Labels = raw28893step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28893step0 raw28893step0Labels permutation145 permutation3
    mixedMoment B raw28893step1 raw28893step1Labels = mixedMoment B raw28893step2 raw28893step2Labels := by
      have ha : raw28893step2 = -raw28893step1 := by apply Matrix.ext; change ∀ i j, raw28893step2 i j = -(raw28893step1 i j); unfold raw28893step2 raw28893step1; decide +kernel
      have hl : raw28893step2Labels = raw28893step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28893step2 raw28893step2Labels = mixedMoment B raw28893step3 raw28893step3Labels := by
      have ha : raw28893step3 = raw28893step2 := by apply Matrix.ext; unfold raw28893step3 raw28893step2; decide +kernel
      have hl : raw28893step2Labels = labelEmbedding6 ∘ raw28893step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28893step2 raw28893step2Labels raw28893step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4769 node4769Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical250
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32044 raw32044Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw32044 raw32044Labels = mixedMoment B raw32044step0 raw32044step0Labels := by
      have hz : ∀ j, raw32044 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32044step0 = (fun i j => raw32044 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32044step0 raw32044; decide +kernel
      have hl : raw32044step0Labels = raw32044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32044 raw32044Labels permutation346 hz
    mixedMoment B raw32044step0 raw32044step0Labels = mixedMoment B raw32044step1 raw32044step1Labels := by
      have ha : raw32044step1 = (fun i j => raw32044step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32044step1 raw32044step0; decide +kernel
      have hl : raw32044step1Labels = raw32044step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32044step0 raw32044step0Labels permutation36 permutation2
    _ = mixedMoment B node5486 node5486Labels := by rfl

theorem canonical32045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32045 raw32045Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw32045 raw32045Labels = mixedMoment B raw32045step0 raw32045step0Labels := by
      have ha : raw32045step0 = (fun i j => raw32045 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32045step0 raw32045; decide +kernel
      have hl : raw32045step0Labels = raw32045Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32045 raw32045Labels permutation160 permutation3
    mixedMoment B raw32045step0 raw32045step0Labels = mixedMoment B raw32045step1 raw32045step1Labels := by
      have ha : raw32045step1 = raw32045step0 := by apply Matrix.ext; unfold raw32045step1 raw32045step0; decide +kernel
      have hl : raw32045step0Labels = labelEmbedding6 ∘ raw32045step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32045step0 raw32045step0Labels raw32045step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

theorem canonical32047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32047 raw32047Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw32047 raw32047Labels = mixedMoment B raw32047step0 raw32047step0Labels := by
      have hz : ∀ j, raw32047 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32047step0 = (fun i j => raw32047 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32047step0 raw32047; decide +kernel
      have hl : raw32047step0Labels = raw32047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32047 raw32047Labels permutation346 hz
    mixedMoment B raw32047step0 raw32047step0Labels = mixedMoment B raw32047step1 raw32047step1Labels := by
      have ha : raw32047step1 = (fun i j => raw32047step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32047step1 raw32047step0; decide +kernel
      have hl : raw32047step1Labels = raw32047step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32047step0 raw32047step0Labels permutation34 permutation3
    mixedMoment B raw32047step1 raw32047step1Labels = mixedMoment B raw32047step2 raw32047step2Labels := by
      have ha : raw32047step2 = raw32047step1 := by apply Matrix.ext; unfold raw32047step2 raw32047step1; decide +kernel
      have hl : raw32047step1Labels = labelEmbedding6 ∘ raw32047step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32047step1 raw32047step1Labels raw32047step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4946 node4946Labels := by rfl

theorem canonical32050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32050 raw32050Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw32050 raw32050Labels = mixedMoment B raw32050step0 raw32050step0Labels := by
      have hz : ∀ j, raw32050 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32050step0 = (fun i j => raw32050 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32050step0 raw32050; decide +kernel
      have hl : raw32050step0Labels = raw32050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32050 raw32050Labels permutation346 hz
    mixedMoment B raw32050step0 raw32050step0Labels = mixedMoment B raw32050step1 raw32050step1Labels := by
      have ha : raw32050step1 = (fun i j => raw32050step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32050step1 raw32050step0; decide +kernel
      have hl : raw32050step1Labels = raw32050step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32050step0 raw32050step0Labels permutation32 permutation3
    mixedMoment B raw32050step1 raw32050step1Labels = mixedMoment B raw32050step2 raw32050step2Labels := by
      have ha : raw32050step2 = raw32050step1 := by apply Matrix.ext; unfold raw32050step2 raw32050step1; decide +kernel
      have hl : raw32050step1Labels = labelEmbedding6 ∘ raw32050step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32050step1 raw32050step1Labels raw32050step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4946 node4946Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical282
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36111 raw36111Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw36111 raw36111Labels = mixedMoment B raw36111step0 raw36111step0Labels := by
      have hz : ∀ j, raw36111 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36111step0 = (fun i j => raw36111 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36111step0 raw36111; decide +kernel
      have hl : raw36111step0Labels = raw36111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36111 raw36111Labels permutation346 hz
    mixedMoment B raw36111step0 raw36111step0Labels = mixedMoment B raw36111step1 raw36111step1Labels := by
      have ha : raw36111step1 = (fun i j => raw36111step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36111step1 raw36111step0; decide +kernel
      have hl : raw36111step1Labels = raw36111step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36111step0 raw36111step0Labels permutation56 permutation3
    mixedMoment B raw36111step1 raw36111step1Labels = mixedMoment B raw36111step2 raw36111step2Labels := by
      have ha : raw36111step2 = raw36111step1 := by apply Matrix.ext; unfold raw36111step2 raw36111step1; decide +kernel
      have hl : raw36111step1Labels = labelEmbedding6 ∘ raw36111step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36111step1 raw36111step1Labels raw36111step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5168 node5168Labels := by rfl

theorem canonical36112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36112 raw36112Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw36112 raw36112Labels = mixedMoment B raw36112step0 raw36112step0Labels := by
      have ha : raw36112step0 = (fun i j => raw36112 (permutation660 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36112step0 raw36112; decide +kernel
      have hl : raw36112step0Labels = raw36112Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36112 raw36112Labels permutation660 permutation3
    mixedMoment B raw36112step0 raw36112step0Labels = mixedMoment B raw36112step1 raw36112step1Labels := by
      have ha : raw36112step1 = -raw36112step0 := by apply Matrix.ext; change ∀ i j, raw36112step1 i j = -(raw36112step0 i j); unfold raw36112step1 raw36112step0; decide +kernel
      have hl : raw36112step1Labels = raw36112step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36112step1 raw36112step1Labels = mixedMoment B raw36112step2 raw36112step2Labels := by
      have ha : raw36112step2 = raw36112step1 := by apply Matrix.ext; unfold raw36112step2 raw36112step1; decide +kernel
      have hl : raw36112step1Labels = labelEmbedding6 ∘ raw36112step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36112step1 raw36112step1Labels raw36112step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5416 node5416Labels := by rfl

theorem canonical36113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36113 raw36113Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw36113 raw36113Labels = mixedMoment B raw36113step0 raw36113step0Labels := by
      have hz : ∀ j, raw36113 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36113step0 = (fun i j => raw36113 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36113step0 raw36113; decide +kernel
      have hl : raw36113step0Labels = raw36113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36113 raw36113Labels permutation346 hz
    mixedMoment B raw36113step0 raw36113step0Labels = mixedMoment B raw36113step1 raw36113step1Labels := by
      have ha : raw36113step1 = (fun i j => raw36113step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36113step1 raw36113step0; decide +kernel
      have hl : raw36113step1Labels = raw36113step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36113step0 raw36113step0Labels permutation150 permutation3
    mixedMoment B raw36113step1 raw36113step1Labels = mixedMoment B raw36113step2 raw36113step2Labels := by
      have ha : raw36113step2 = -raw36113step1 := by apply Matrix.ext; change ∀ i j, raw36113step2 i j = -(raw36113step1 i j); unfold raw36113step2 raw36113step1; decide +kernel
      have hl : raw36113step2Labels = raw36113step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36113step2 raw36113step2Labels = mixedMoment B raw36113step3 raw36113step3Labels := by
      have ha : raw36113step3 = raw36113step2 := by apply Matrix.ext; unfold raw36113step3 raw36113step2; decide +kernel
      have hl : raw36113step2Labels = labelEmbedding6 ∘ raw36113step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36113step2 raw36113step2Labels raw36113step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical36114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36114 raw36114Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw36114 raw36114Labels = mixedMoment B raw36114step0 raw36114step0Labels := by
      have hz : ∀ j, raw36114 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36114step0 = (fun i j => raw36114 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36114step0 raw36114; decide +kernel
      have hl : raw36114step0Labels = raw36114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36114 raw36114Labels permutation346 hz
    mixedMoment B raw36114step0 raw36114step0Labels = mixedMoment B raw36114step1 raw36114step1Labels := by
      have ha : raw36114step1 = (fun i j => raw36114step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36114step1 raw36114step0; decide +kernel
      have hl : raw36114step1Labels = raw36114step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36114step0 raw36114step0Labels permutation144 permutation3
    mixedMoment B raw36114step1 raw36114step1Labels = mixedMoment B raw36114step2 raw36114step2Labels := by
      have ha : raw36114step2 = -raw36114step1 := by apply Matrix.ext; change ∀ i j, raw36114step2 i j = -(raw36114step1 i j); unfold raw36114step2 raw36114step1; decide +kernel
      have hl : raw36114step2Labels = raw36114step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36114step2 raw36114step2Labels = mixedMoment B raw36114step3 raw36114step3Labels := by
      have ha : raw36114step3 = raw36114step2 := by apply Matrix.ext; unfold raw36114step3 raw36114step2; decide +kernel
      have hl : raw36114step2Labels = labelEmbedding6 ∘ raw36114step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36114step2 raw36114step2Labels raw36114step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical36115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36115 raw36115Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw36115 raw36115Labels = mixedMoment B raw36115step0 raw36115step0Labels := by
      have ha : raw36115step0 = (fun i j => raw36115 (permutation273 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36115step0 raw36115; decide +kernel
      have hl : raw36115step0Labels = raw36115Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36115 raw36115Labels permutation273 permutation3
    mixedMoment B raw36115step0 raw36115step0Labels = mixedMoment B raw36115step1 raw36115step1Labels := by
      have ha : raw36115step1 = raw36115step0 := by apply Matrix.ext; unfold raw36115step1 raw36115step0; decide +kernel
      have hl : raw36115step0Labels = labelEmbedding6 ∘ raw36115step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36115step0 raw36115step0Labels raw36115step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

theorem canonical36116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36116 raw36116Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw36116 raw36116Labels = mixedMoment B raw36116step0 raw36116step0Labels := by
      have ha : raw36116step0 = (fun i j => raw36116 (permutation645 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36116step0 raw36116; decide +kernel
      have hl : raw36116step0Labels = raw36116Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36116 raw36116Labels permutation645 permutation3
    mixedMoment B raw36116step0 raw36116step0Labels = mixedMoment B raw36116step1 raw36116step1Labels := by
      have ha : raw36116step1 = -raw36116step0 := by apply Matrix.ext; change ∀ i j, raw36116step1 i j = -(raw36116step0 i j); unfold raw36116step1 raw36116step0; decide +kernel
      have hl : raw36116step1Labels = raw36116step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36116step1 raw36116step1Labels = mixedMoment B raw36116step2 raw36116step2Labels := by
      have ha : raw36116step2 = raw36116step1 := by apply Matrix.ext; unfold raw36116step2 raw36116step1; decide +kernel
      have hl : raw36116step1Labels = labelEmbedding6 ∘ raw36116step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36116step1 raw36116step1Labels raw36116step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

theorem canonical36117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36117 raw36117Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw36117 raw36117Labels = mixedMoment B raw36117step0 raw36117step0Labels := by
      have ha : raw36117step0 = (fun i j => raw36117 (permutation639 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36117step0 raw36117; decide +kernel
      have hl : raw36117step0Labels = raw36117Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36117 raw36117Labels permutation639 permutation3
    mixedMoment B raw36117step0 raw36117step0Labels = mixedMoment B raw36117step1 raw36117step1Labels := by
      have ha : raw36117step1 = -raw36117step0 := by apply Matrix.ext; change ∀ i j, raw36117step1 i j = -(raw36117step0 i j); unfold raw36117step1 raw36117step0; decide +kernel
      have hl : raw36117step1Labels = raw36117step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36117step1 raw36117step1Labels = mixedMoment B raw36117step2 raw36117step2Labels := by
      have ha : raw36117step2 = raw36117step1 := by apply Matrix.ext; unfold raw36117step2 raw36117step1; decide +kernel
      have hl : raw36117step1Labels = labelEmbedding6 ∘ raw36117step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36117step1 raw36117step1Labels raw36117step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

theorem canonical36118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36118 raw36118Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw36118 raw36118Labels = mixedMoment B raw36118step0 raw36118step0Labels := by
      have hz : ∀ j, raw36118 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36118step0 = (fun i j => raw36118 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36118step0 raw36118; decide +kernel
      have hl : raw36118step0Labels = raw36118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36118 raw36118Labels permutation346 hz
    mixedMoment B raw36118step0 raw36118step0Labels = mixedMoment B raw36118step1 raw36118step1Labels := by
      have ha : raw36118step1 = (fun i j => raw36118step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36118step1 raw36118step0; decide +kernel
      have hl : raw36118step1Labels = raw36118step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36118step0 raw36118step0Labels permutation58 permutation3
    mixedMoment B raw36118step1 raw36118step1Labels = mixedMoment B raw36118step2 raw36118step2Labels := by
      have ha : raw36118step2 = raw36118step1 := by apply Matrix.ext; unfold raw36118step2 raw36118step1; decide +kernel
      have hl : raw36118step1Labels = labelEmbedding6 ∘ raw36118step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36118step1 raw36118step1Labels raw36118step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4946 node4946Labels := by rfl

theorem canonical36119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36119 raw36119Labels = mixedMoment B node5337 node5337Labels := by
  calc
    mixedMoment B raw36119 raw36119Labels = mixedMoment B raw36119step0 raw36119step0Labels := by
      have ha : raw36119step0 = (fun i j => raw36119 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36119step0 raw36119; decide +kernel
      have hl : raw36119step0Labels = raw36119Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36119 raw36119Labels permutation663 permutation3
    mixedMoment B raw36119step0 raw36119step0Labels = mixedMoment B raw36119step1 raw36119step1Labels := by
      have ha : raw36119step1 = -raw36119step0 := by apply Matrix.ext; change ∀ i j, raw36119step1 i j = -(raw36119step0 i j); unfold raw36119step1 raw36119step0; decide +kernel
      have hl : raw36119step1Labels = raw36119step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36119step1 raw36119step1Labels = mixedMoment B raw36119step2 raw36119step2Labels := by
      have ha : raw36119step2 = raw36119step1 := by apply Matrix.ext; unfold raw36119step2 raw36119step1; decide +kernel
      have hl : raw36119step1Labels = labelEmbedding6 ∘ raw36119step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36119step1 raw36119step1Labels raw36119step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5337 node5337Labels := by rfl

theorem canonical36120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36120 raw36120Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw36120 raw36120Labels = mixedMoment B raw36120step0 raw36120step0Labels := by
      have hz : ∀ j, raw36120 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36120step0 = (fun i j => raw36120 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36120step0 raw36120; decide +kernel
      have hl : raw36120step0Labels = raw36120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36120 raw36120Labels permutation346 hz
    mixedMoment B raw36120step0 raw36120step0Labels = mixedMoment B raw36120step1 raw36120step1Labels := by
      have ha : raw36120step1 = (fun i j => raw36120step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36120step1 raw36120step0; decide +kernel
      have hl : raw36120step1Labels = raw36120step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36120step0 raw36120step0Labels permutation144 permutation3
    mixedMoment B raw36120step1 raw36120step1Labels = mixedMoment B raw36120step2 raw36120step2Labels := by
      have ha : raw36120step2 = -raw36120step1 := by apply Matrix.ext; change ∀ i j, raw36120step2 i j = -(raw36120step1 i j); unfold raw36120step2 raw36120step1; decide +kernel
      have hl : raw36120step2Labels = raw36120step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36120step2 raw36120step2Labels = mixedMoment B raw36120step3 raw36120step3Labels := by
      have ha : raw36120step3 = raw36120step2 := by apply Matrix.ext; unfold raw36120step3 raw36120step2; decide +kernel
      have hl : raw36120step2Labels = labelEmbedding6 ∘ raw36120step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36120step2 raw36120step2Labels raw36120step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

theorem canonical36121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36121 raw36121Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw36121 raw36121Labels = mixedMoment B raw36121step0 raw36121step0Labels := by
      have hz : ∀ j, raw36121 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36121step0 = (fun i j => raw36121 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36121step0 raw36121; decide +kernel
      have hl : raw36121step0Labels = raw36121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36121 raw36121Labels permutation346 hz
    mixedMoment B raw36121step0 raw36121step0Labels = mixedMoment B raw36121step1 raw36121step1Labels := by
      have ha : raw36121step1 = (fun i j => raw36121step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36121step1 raw36121step0; decide +kernel
      have hl : raw36121step1Labels = raw36121step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36121step0 raw36121step0Labels permutation56 permutation3
    mixedMoment B raw36121step1 raw36121step1Labels = mixedMoment B raw36121step2 raw36121step2Labels := by
      have ha : raw36121step2 = raw36121step1 := by apply Matrix.ext; unfold raw36121step2 raw36121step1; decide +kernel
      have hl : raw36121step1Labels = labelEmbedding6 ∘ raw36121step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36121step1 raw36121step1Labels raw36121step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4946 node4946Labels := by rfl

theorem canonical36122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36122 raw36122Labels = mixedMoment B node5337 node5337Labels := by
  calc
    mixedMoment B raw36122 raw36122Labels = mixedMoment B raw36122step0 raw36122step0Labels := by
      have ha : raw36122step0 = (fun i j => raw36122 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36122step0 raw36122; decide +kernel
      have hl : raw36122step0Labels = raw36122Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36122 raw36122Labels permutation687 permutation3
    mixedMoment B raw36122step0 raw36122step0Labels = mixedMoment B raw36122step1 raw36122step1Labels := by
      have ha : raw36122step1 = -raw36122step0 := by apply Matrix.ext; change ∀ i j, raw36122step1 i j = -(raw36122step0 i j); unfold raw36122step1 raw36122step0; decide +kernel
      have hl : raw36122step1Labels = raw36122step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36122step1 raw36122step1Labels = mixedMoment B raw36122step2 raw36122step2Labels := by
      have ha : raw36122step2 = raw36122step1 := by apply Matrix.ext; unfold raw36122step2 raw36122step1; decide +kernel
      have hl : raw36122step1Labels = labelEmbedding6 ∘ raw36122step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36122step1 raw36122step1Labels raw36122step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5337 node5337Labels := by rfl

theorem canonical36123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36123 raw36123Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw36123 raw36123Labels = mixedMoment B raw36123step0 raw36123step0Labels := by
      have hz : ∀ j, raw36123 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36123step0 = (fun i j => raw36123 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36123step0 raw36123; decide +kernel
      have hl : raw36123step0Labels = raw36123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36123 raw36123Labels permutation346 hz
    mixedMoment B raw36123step0 raw36123step0Labels = mixedMoment B raw36123step1 raw36123step1Labels := by
      have ha : raw36123step1 = (fun i j => raw36123step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36123step1 raw36123step0; decide +kernel
      have hl : raw36123step1Labels = raw36123step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36123step0 raw36123step0Labels permutation150 permutation3
    mixedMoment B raw36123step1 raw36123step1Labels = mixedMoment B raw36123step2 raw36123step2Labels := by
      have ha : raw36123step2 = -raw36123step1 := by apply Matrix.ext; change ∀ i j, raw36123step2 i j = -(raw36123step1 i j); unfold raw36123step2 raw36123step1; decide +kernel
      have hl : raw36123step2Labels = raw36123step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36123step2 raw36123step2Labels = mixedMoment B raw36123step3 raw36123step3Labels := by
      have ha : raw36123step3 = raw36123step2 := by apply Matrix.ext; unfold raw36123step3 raw36123step2; decide +kernel
      have hl : raw36123step2Labels = labelEmbedding6 ∘ raw36123step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36123step2 raw36123step2Labels raw36123step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

theorem canonical36124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36124 raw36124Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw36124 raw36124Labels = mixedMoment B raw36124step0 raw36124step0Labels := by
      have hz : ∀ j, raw36124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36124step0 = (fun i j => raw36124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36124step0 raw36124; decide +kernel
      have hl : raw36124step0Labels = raw36124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36124 raw36124Labels permutation346 hz
    mixedMoment B raw36124step0 raw36124step0Labels = mixedMoment B raw36124step1 raw36124step1Labels := by
      have ha : raw36124step1 = (fun i j => raw36124step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36124step1 raw36124step0; decide +kernel
      have hl : raw36124step1Labels = raw36124step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36124step0 raw36124step0Labels permutation144 permutation3
    mixedMoment B raw36124step1 raw36124step1Labels = mixedMoment B raw36124step2 raw36124step2Labels := by
      have ha : raw36124step2 = -raw36124step1 := by apply Matrix.ext; change ∀ i j, raw36124step2 i j = -(raw36124step1 i j); unfold raw36124step2 raw36124step1; decide +kernel
      have hl : raw36124step2Labels = raw36124step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36124step2 raw36124step2Labels = mixedMoment B raw36124step3 raw36124step3Labels := by
      have ha : raw36124step3 = raw36124step2 := by apply Matrix.ext; unfold raw36124step3 raw36124step2; decide +kernel
      have hl : raw36124step2Labels = labelEmbedding6 ∘ raw36124step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36124step2 raw36124step2Labels raw36124step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4769 node4769Labels := by rfl

theorem canonical36125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36125 raw36125Labels = mixedMoment B node4767 node4767Labels := by
  calc
    mixedMoment B raw36125 raw36125Labels = mixedMoment B raw36125step0 raw36125step0Labels := by
      have ha : raw36125step0 = (fun i j => raw36125 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36125step0 raw36125; decide +kernel
      have hl : raw36125step0Labels = raw36125Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36125 raw36125Labels permutation663 permutation3
    mixedMoment B raw36125step0 raw36125step0Labels = mixedMoment B raw36125step1 raw36125step1Labels := by
      have ha : raw36125step1 = -raw36125step0 := by apply Matrix.ext; change ∀ i j, raw36125step1 i j = -(raw36125step0 i j); unfold raw36125step1 raw36125step0; decide +kernel
      have hl : raw36125step1Labels = raw36125step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36125step1 raw36125step1Labels = mixedMoment B raw36125step2 raw36125step2Labels := by
      have ha : raw36125step2 = raw36125step1 := by apply Matrix.ext; unfold raw36125step2 raw36125step1; decide +kernel
      have hl : raw36125step1Labels = labelEmbedding6 ∘ raw36125step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36125step1 raw36125step1Labels raw36125step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4767 node4767Labels := by rfl

theorem canonical36126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36126 raw36126Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw36126 raw36126Labels = mixedMoment B raw36126step0 raw36126step0Labels := by
      have hz : ∀ j, raw36126 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36126step0 = (fun i j => raw36126 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36126step0 raw36126; decide +kernel
      have hl : raw36126step0Labels = raw36126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36126 raw36126Labels permutation346 hz
    mixedMoment B raw36126step0 raw36126step0Labels = mixedMoment B raw36126step1 raw36126step1Labels := by
      have ha : raw36126step1 = (fun i j => raw36126step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36126step1 raw36126step0; decide +kernel
      have hl : raw36126step1Labels = raw36126step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36126step0 raw36126step0Labels permutation144 permutation3
    mixedMoment B raw36126step1 raw36126step1Labels = mixedMoment B raw36126step2 raw36126step2Labels := by
      have ha : raw36126step2 = -raw36126step1 := by apply Matrix.ext; change ∀ i j, raw36126step2 i j = -(raw36126step1 i j); unfold raw36126step2 raw36126step1; decide +kernel
      have hl : raw36126step2Labels = raw36126step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36126step2 raw36126step2Labels = mixedMoment B raw36126step3 raw36126step3Labels := by
      have ha : raw36126step3 = raw36126step2 := by apply Matrix.ext; unfold raw36126step3 raw36126step2; decide +kernel
      have hl : raw36126step2Labels = labelEmbedding6 ∘ raw36126step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36126step2 raw36126step2Labels raw36126step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10085 raw10085Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw10085 raw10085Labels = mixedMoment B raw10085step0 raw10085step0Labels := by
      have hz : ∀ j, raw10085 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10085step0 = (fun i j => raw10085 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10085step0 raw10085; decide +kernel
      have hl : raw10085step0Labels = raw10085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10085 raw10085Labels permutation346 hz
    mixedMoment B raw10085step0 raw10085step0Labels = mixedMoment B raw10085step1 raw10085step1Labels := by
      have ha : raw10085step1 = (fun i j => raw10085step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10085step1 raw10085step0; decide +kernel
      have hl : raw10085step1Labels = raw10085step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10085step0 raw10085step0Labels permutation151 permutation3
    mixedMoment B raw10085step1 raw10085step1Labels = mixedMoment B raw10085step2 raw10085step2Labels := by
      have ha : raw10085step2 = -raw10085step1 := by apply Matrix.ext; change ∀ i j, raw10085step2 i j = -(raw10085step1 i j); unfold raw10085step2 raw10085step1; decide +kernel
      have hl : raw10085step2Labels = raw10085step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10085step2 raw10085step2Labels = mixedMoment B raw10085step3 raw10085step3Labels := by
      have ha : raw10085step3 = raw10085step2 := by apply Matrix.ext; unfold raw10085step3 raw10085step2; decide +kernel
      have hl : raw10085step2Labels = labelEmbedding6 ∘ raw10085step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10085step2 raw10085step2Labels raw10085step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

theorem canonical10101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10101 raw10101Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw10101 raw10101Labels = mixedMoment B raw10101step0 raw10101step0Labels := by
      have hz : ∀ j, raw10101 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10101step0 = (fun i j => raw10101 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10101step0 raw10101; decide +kernel
      have hl : raw10101step0Labels = raw10101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10101 raw10101Labels permutation346 hz
    mixedMoment B raw10101step0 raw10101step0Labels = mixedMoment B raw10101step1 raw10101step1Labels := by
      have ha : raw10101step1 = (fun i j => raw10101step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10101step1 raw10101step0; decide +kernel
      have hl : raw10101step1Labels = raw10101step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10101step0 raw10101step0Labels permutation32 permutation3
    mixedMoment B raw10101step1 raw10101step1Labels = mixedMoment B raw10101step2 raw10101step2Labels := by
      have ha : raw10101step2 = raw10101step1 := by apply Matrix.ext; unfold raw10101step2 raw10101step1; decide +kernel
      have hl : raw10101step1Labels = labelEmbedding6 ∘ raw10101step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10101step1 raw10101step1Labels raw10101step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5168 node5168Labels := by rfl

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

theorem singleton4767 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4767 node4767Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1967 node1967Labels + mixedMoment B node2183 node2183Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1701 singletonSmall4767
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4767) = raw1701Labels := by decide +kernel
  rw [hl, canonical1701 B hB] at h
  have hc0 : mixedMoment B raw1701 (Fin.cases (0 : Fin 2) singletonSmall4767) =
      mixedMoment B node1967 node1967Labels := by
    have ha : raw1701 = raw1702 := by apply Matrix.ext; unfold raw1701 raw1702; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4767 = raw1702Labels := by decide +kernel
    rw [ha, hj, canonical1702 B hB]
  have hc1 : mixedMoment B raw1701 (Fin.cases (1 : Fin 2) singletonSmall4767) =
      mixedMoment B node2183 node2183Labels := by
    have ha : raw1701 = raw1703 := by apply Matrix.ext; unfold raw1701 raw1703; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4767 = raw1703Labels := by decide +kernel
    rw [ha, hj, canonical1703 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4769 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4769 node4769Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1969 node1969Labels + mixedMoment B node2185 node2185Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1704 singletonSmall4769
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4769) = raw1704Labels := by decide +kernel
  rw [hl, canonical1704 B hB] at h
  have hc0 : mixedMoment B raw1704 (Fin.cases (0 : Fin 2) singletonSmall4769) =
      mixedMoment B node1969 node1969Labels := by
    have ha : raw1704 = raw1705 := by apply Matrix.ext; unfold raw1704 raw1705; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4769 = raw1705Labels := by decide +kernel
    rw [ha, hj, canonical1705 B hB]
  have hc1 : mixedMoment B raw1704 (Fin.cases (1 : Fin 2) singletonSmall4769) =
      mixedMoment B node2185 node2185Labels := by
    have ha : raw1704 = raw1706 := by apply Matrix.ext; unfold raw1704 raw1706; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4769 = raw1706Labels := by decide +kernel
    rw [ha, hj, canonical1706 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4939 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4939 node4939Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2330 node2330Labels + mixedMoment B node3404 node3404Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1902 singletonSmall4939
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4939) = raw1902Labels := by decide +kernel
  rw [hl, canonical1902 B hB] at h
  have hc0 : mixedMoment B raw1902 (Fin.cases (0 : Fin 2) singletonSmall4939) =
      mixedMoment B node2330 node2330Labels := by
    have ha : raw1902 = raw1903 := by apply Matrix.ext; unfold raw1902 raw1903; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4939 = raw1903Labels := by decide +kernel
    rw [ha, hj, canonical1903 B hB]
  have hc1 : mixedMoment B raw1902 (Fin.cases (1 : Fin 2) singletonSmall4939) =
      mixedMoment B node3404 node3404Labels := by
    have ha : raw1902 = raw1904 := by apply Matrix.ext; unfold raw1902 raw1904; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4939 = raw1904Labels := by decide +kernel
    rw [ha, hj, canonical1904 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4946 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4946 node4946Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2337 node2337Labels + mixedMoment B node3412 node3412Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1911 singletonSmall4946
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4946) = raw1911Labels := by decide +kernel
  rw [hl, canonical1911 B hB] at h
  have hc0 : mixedMoment B raw1911 (Fin.cases (0 : Fin 2) singletonSmall4946) =
      mixedMoment B node2337 node2337Labels := by
    have ha : raw1911 = raw1912 := by apply Matrix.ext; unfold raw1911 raw1912; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4946 = raw1912Labels := by decide +kernel
    rw [ha, hj, canonical1912 B hB]
  have hc1 : mixedMoment B raw1911 (Fin.cases (1 : Fin 2) singletonSmall4946) =
      mixedMoment B node3412 node3412Labels := by
    have ha : raw1911 = raw1913 := by apply Matrix.ext; unfold raw1911 raw1913; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4946 = raw1913Labels := by decide +kernel
    rw [ha, hj, canonical1913 B hB]
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

theorem singleton5337 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5337 node5337Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3672 node3672Labels + mixedMoment B node3756 node3756Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2376 singletonSmall5337
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5337) = raw2376Labels := by decide +kernel
  rw [hl, canonical2376 B hB] at h
  have hc0 : mixedMoment B raw2376 (Fin.cases (0 : Fin 2) singletonSmall5337) =
      mixedMoment B node3672 node3672Labels := by
    have ha : raw2376 = raw2377 := by apply Matrix.ext; unfold raw2376 raw2377; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5337 = raw2377Labels := by decide +kernel
    rw [ha, hj, canonical2377 B hB]
  have hc1 : mixedMoment B raw2376 (Fin.cases (1 : Fin 2) singletonSmall5337) =
      mixedMoment B node3756 node3756Labels := by
    have ha : raw2376 = raw2378 := by apply Matrix.ext; unfold raw2376 raw2378; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5337 = raw2378Labels := by decide +kernel
    rw [ha, hj, canonical2378 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5356 node5356Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3694 node3694Labels + mixedMoment B node3773 node3773Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2403 singletonSmall5356
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5356) = raw2403Labels := by decide +kernel
  rw [hl, canonical2403 B hB] at h
  have hc0 : mixedMoment B raw2403 (Fin.cases (0 : Fin 2) singletonSmall5356) =
      mixedMoment B node3694 node3694Labels := by
    have ha : raw2403 = raw2404 := by apply Matrix.ext; unfold raw2403 raw2404; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5356 = raw2404Labels := by decide +kernel
    rw [ha, hj, canonical2404 B hB]
  have hc1 : mixedMoment B raw2403 (Fin.cases (1 : Fin 2) singletonSmall5356) =
      mixedMoment B node3773 node3773Labels := by
    have ha : raw2403 = raw2405 := by apply Matrix.ext; unfold raw2403 raw2405; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5356 = raw2405Labels := by decide +kernel
    rw [ha, hj, canonical2405 B hB]
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

theorem singleton5393 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5393 node5393Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3779 node3779Labels + mixedMoment B node3797 node3797Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2460 singletonSmall5393
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5393) = raw2460Labels := by decide +kernel
  rw [hl, canonical2460 B hB] at h
  have hc0 : mixedMoment B raw2460 (Fin.cases (0 : Fin 2) singletonSmall5393) =
      mixedMoment B node3779 node3779Labels := by
    have ha : raw2460 = raw2461 := by apply Matrix.ext; unfold raw2460 raw2461; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5393 = raw2461Labels := by decide +kernel
    rw [ha, hj, canonical2461 B hB]
  have hc1 : mixedMoment B raw2460 (Fin.cases (1 : Fin 2) singletonSmall5393) =
      mixedMoment B node3797 node3797Labels := by
    have ha : raw2460 = raw2462 := by apply Matrix.ext; unfold raw2460 raw2462; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5393 = raw2462Labels := by decide +kernel
    rw [ha, hj, canonical2462 B hB]
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

theorem zero5486 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5486 node5486Labels = 0 := by
  exact mixedMoment_order_one B hB node5486 node5486Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1967 node1967Labels = Sparse.eval nodeValue1967 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1967) = mixedMoment B node1967 node1967Labels := rfl
  simpa [nodeValue1967, Sparse.eval] using hc.symm

theorem sound1969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1969 node1969Labels = Sparse.eval nodeValue1969 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1969) = mixedMoment B node1969 node1969Labels := rfl
  simpa [nodeValue1969, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2183 node2183Labels = Sparse.eval nodeValue2183 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2183) = mixedMoment B node2183 node2183Labels := rfl
  simpa [nodeValue2183, Sparse.eval] using hc.symm

theorem sound2185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2185 node2185Labels = Sparse.eval nodeValue2185 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2185) = mixedMoment B node2185 node2185Labels := rfl
  simpa [nodeValue2185, Sparse.eval] using hc.symm

theorem sound2225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2225 node2225Labels = Sparse.eval nodeValue2225 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2225) = mixedMoment B node2225 node2225Labels := rfl
  simpa [nodeValue2225, Sparse.eval] using hc.symm

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

theorem sound2330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2330 node2330Labels = Sparse.eval nodeValue2330 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2330) = mixedMoment B node2330 node2330Labels := rfl
  simpa [nodeValue2330, Sparse.eval] using hc.symm

theorem sound2337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2337 node2337Labels = Sparse.eval nodeValue2337 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2337) = mixedMoment B node2337 node2337Labels := rfl
  simpa [nodeValue2337, Sparse.eval] using hc.symm

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

theorem sound3404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3404 node3404Labels = Sparse.eval nodeValue3404 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3404) = mixedMoment B node3404 node3404Labels := rfl
  simpa [nodeValue3404, Sparse.eval] using hc.symm

theorem sound3412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3412 node3412Labels = Sparse.eval nodeValue3412 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3412) = mixedMoment B node3412 node3412Labels := rfl
  simpa [nodeValue3412, Sparse.eval] using hc.symm

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

theorem sound3672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3672 node3672Labels = Sparse.eval nodeValue3672 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3672) = mixedMoment B node3672 node3672Labels := rfl
  simpa [nodeValue3672, Sparse.eval] using hc.symm

theorem sound3694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3694 node3694Labels = Sparse.eval nodeValue3694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3694) = mixedMoment B node3694 node3694Labels := rfl
  simpa [nodeValue3694, Sparse.eval] using hc.symm

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

theorem sound3756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3756 node3756Labels = Sparse.eval nodeValue3756 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3756) = mixedMoment B node3756 node3756Labels := rfl
  simpa [nodeValue3756, Sparse.eval] using hc.symm

theorem sound3773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3773 node3773Labels = Sparse.eval nodeValue3773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3773) = mixedMoment B node3773 node3773Labels := rfl
  simpa [nodeValue3773, Sparse.eval] using hc.symm

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

theorem sound3779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3779 node3779Labels = Sparse.eval nodeValue3779 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3779) = mixedMoment B node3779 node3779Labels := rfl
  simpa [nodeValue3779, Sparse.eval] using hc.symm

theorem sound3797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3797 node3797Labels = Sparse.eval nodeValue3797 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3797) = mixedMoment B node3797 node3797Labels := rfl
  simpa [nodeValue3797, Sparse.eval] using hc.symm

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

theorem sound4767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4767 node4767Labels = Sparse.eval nodeValue4767 (mixedVector B) := by
  have h := singleton4767 B _hB
  rw [sound1967 B _hB _hF, sound2183 B _hB _hF] at h
  norm_num [nodeValue4767, nodeValue1967, nodeValue2183, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4769 node4769Labels = Sparse.eval nodeValue4769 (mixedVector B) := by
  have h := singleton4769 B _hB
  rw [sound1969 B _hB _hF, sound2185 B _hB _hF] at h
  norm_num [nodeValue4769, nodeValue1969, nodeValue2185, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4939 node4939Labels = Sparse.eval nodeValue4939 (mixedVector B) := by
  have h := singleton4939 B _hB
  rw [sound2330 B _hB _hF, sound3404 B _hB _hF] at h
  norm_num [nodeValue4939, nodeValue2330, nodeValue3404, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4946 node4946Labels = Sparse.eval nodeValue4946 (mixedVector B) := by
  have h := singleton4946 B _hB
  rw [sound2337 B _hB _hF, sound3412 B _hB _hF] at h
  norm_num [nodeValue4946, nodeValue2337, nodeValue3412, Sparse.eval] at h ⊢
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

theorem sound5337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5337 node5337Labels = Sparse.eval nodeValue5337 (mixedVector B) := by
  have h := singleton5337 B _hB
  rw [sound3672 B _hB _hF, sound3756 B _hB _hF] at h
  norm_num [nodeValue5337, nodeValue3672, nodeValue3756, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5356 node5356Labels = Sparse.eval nodeValue5356 (mixedVector B) := by
  have h := singleton5356 B _hB
  rw [sound3694 B _hB _hF, sound3773 B _hB _hF] at h
  norm_num [nodeValue5356, nodeValue3694, nodeValue3773, Sparse.eval] at h ⊢
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

theorem sound5393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5393 node5393Labels = Sparse.eval nodeValue5393 (mixedVector B) := by
  have h := singleton5393 B _hB
  rw [sound3779 B _hB _hF, sound3797 B _hB _hF] at h
  norm_num [nodeValue5393, nodeValue3779, nodeValue3797, Sparse.eval] at h ⊢
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

theorem sound5486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5486 node5486Labels = Sparse.eval nodeValue5486 (mixedVector B) := by
  simpa only [nodeValue5486, Sparse.eval_nil] using zero5486 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources81
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2598 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2598 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2598 + difference 0 1) (sourceB2598 + difference 1 0) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2598 + difference 0 1) (sourceB2598 + difference 1 0) sourceC2598) = raw36111 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36111; decide +kernel
    rw [ha]
    exact (canonical36111 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2598 + difference 0 2) (sourceB2598 + difference 2 0) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2598 + difference 0 2) (sourceB2598 + difference 2 0) sourceC2598) = raw36112 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36112; decide +kernel
    rw [ha]
    exact (canonical36112 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2598 + difference 0 3) (sourceB2598 + difference 3 0) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2598 + difference 0 3) (sourceB2598 + difference 3 0) sourceC2598) = raw36113 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36113; decide +kernel
    rw [ha]
    exact (canonical36113 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2598 + difference 0 4) (sourceB2598 + difference 4 0) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2598 + difference 0 4) (sourceB2598 + difference 4 0) sourceC2598) = raw36114 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36114; decide +kernel
    rw [ha]
    exact (canonical36114 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2598 + difference 0 5) (sourceB2598 + difference 5 0) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA2598 + difference 0 5) (sourceB2598 + difference 5 0) sourceC2598) = raw19003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw19003; decide +kernel
    rw [ha]
    exact (canonical19003 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2598 + difference 1 0) (sourceB2598 + difference 0 1) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2598 + difference 1 0) (sourceB2598 + difference 0 1) sourceC2598) = raw10101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw10101; decide +kernel
    rw [ha]
    exact (canonical10101 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2598 + difference 1 2) (sourceB2598 + difference 2 1) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2598 + difference 1 2) (sourceB2598 + difference 2 1) sourceC2598) = raw19027 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw19027; decide +kernel
    rw [ha]
    exact (canonical19027 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2598 + difference 1 3) (sourceB2598 + difference 3 1) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2598 + difference 1 3) (sourceB2598 + difference 3 1) sourceC2598) = raw10085 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw10085; decide +kernel
    rw [ha]
    exact (canonical10085 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2598 + difference 1 4) (sourceB2598 + difference 4 1) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2598 + difference 1 4) (sourceB2598 + difference 4 1) sourceC2598) = raw19028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw19028; decide +kernel
    rw [ha]
    exact (canonical19028 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2598 + difference 1 5) (sourceB2598 + difference 5 1) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA2598 + difference 1 5) (sourceB2598 + difference 5 1) sourceC2598) = raw32044 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw32044; decide +kernel
    rw [ha]
    exact (canonical32044 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2598 + difference 2 0) (sourceB2598 + difference 0 2) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4939) := by
    have ha : (tripleCharges (sourceA2598 + difference 2 0) (sourceB2598 + difference 0 2) sourceC2598) = raw32045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw32045; decide +kernel
    rw [ha]
    exact (canonical32045 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2598 + difference 2 1) (sourceB2598 + difference 1 2) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4939) := by
    have ha : (tripleCharges (sourceA2598 + difference 2 1) (sourceB2598 + difference 1 2) sourceC2598) = raw36115 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36115; decide +kernel
    rw [ha]
    exact (canonical36115 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2598 + difference 2 3) (sourceB2598 + difference 3 2) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2598 + difference 2 3) (sourceB2598 + difference 3 2) sourceC2598) = raw36116 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36116; decide +kernel
    rw [ha]
    exact (canonical36116 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2598 + difference 2 4) (sourceB2598 + difference 4 2) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2598 + difference 2 4) (sourceB2598 + difference 4 2) sourceC2598) = raw36117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36117; decide +kernel
    rw [ha]
    exact (canonical36117 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2598 + difference 2 5) (sourceB2598 + difference 5 2) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5464) := by
    have ha : (tripleCharges (sourceA2598 + difference 2 5) (sourceB2598 + difference 5 2) sourceC2598) = raw19012 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw19012; decide +kernel
    rw [ha]
    exact (canonical19012 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2598 + difference 3 0) (sourceB2598 + difference 0 3) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2598 + difference 3 0) (sourceB2598 + difference 0 3) sourceC2598) = raw32047 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw32047; decide +kernel
    rw [ha]
    exact (canonical32047 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2598 + difference 3 1) (sourceB2598 + difference 1 3) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2598 + difference 3 1) (sourceB2598 + difference 1 3) sourceC2598) = raw36118 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36118; decide +kernel
    rw [ha]
    exact (canonical36118 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2598 + difference 3 2) (sourceB2598 + difference 2 3) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5337) := by
    have ha : (tripleCharges (sourceA2598 + difference 3 2) (sourceB2598 + difference 2 3) sourceC2598) = raw36119 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36119; decide +kernel
    rw [ha]
    exact (canonical36119 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2598 + difference 3 4) (sourceB2598 + difference 4 3) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2598 + difference 3 4) (sourceB2598 + difference 4 3) sourceC2598) = raw36120 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36120; decide +kernel
    rw [ha]
    exact (canonical36120 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2598 + difference 3 5) (sourceB2598 + difference 5 3) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2598 + difference 3 5) (sourceB2598 + difference 5 3) sourceC2598) = raw19017 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw19017; decide +kernel
    rw [ha]
    exact (canonical19017 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2598 + difference 4 0) (sourceB2598 + difference 0 4) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2598 + difference 4 0) (sourceB2598 + difference 0 4) sourceC2598) = raw32050 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw32050; decide +kernel
    rw [ha]
    exact (canonical32050 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2598 + difference 4 1) (sourceB2598 + difference 1 4) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2598 + difference 4 1) (sourceB2598 + difference 1 4) sourceC2598) = raw36121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36121; decide +kernel
    rw [ha]
    exact (canonical36121 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2598 + difference 4 2) (sourceB2598 + difference 2 4) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5337) := by
    have ha : (tripleCharges (sourceA2598 + difference 4 2) (sourceB2598 + difference 2 4) sourceC2598) = raw36122 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36122; decide +kernel
    rw [ha]
    exact (canonical36122 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2598 + difference 4 3) (sourceB2598 + difference 3 4) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2598 + difference 4 3) (sourceB2598 + difference 3 4) sourceC2598) = raw36123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36123; decide +kernel
    rw [ha]
    exact (canonical36123 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2598 + difference 4 5) (sourceB2598 + difference 5 4) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2598 + difference 4 5) (sourceB2598 + difference 5 4) sourceC2598) = raw19022 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw19022; decide +kernel
    rw [ha]
    exact (canonical19022 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2598 + difference 5 0) (sourceB2598 + difference 0 5) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2598 + difference 5 0) (sourceB2598 + difference 0 5) sourceC2598) = raw28893 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw28893; decide +kernel
    rw [ha]
    exact (canonical28893 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2598 + difference 5 1) (sourceB2598 + difference 1 5) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2598 + difference 5 1) (sourceB2598 + difference 1 5) sourceC2598) = raw36124 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36124; decide +kernel
    rw [ha]
    exact (canonical36124 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2598 + difference 5 2) (sourceB2598 + difference 2 5) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4767) := by
    have ha : (tripleCharges (sourceA2598 + difference 5 2) (sourceB2598 + difference 2 5) sourceC2598) = raw36125 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36125; decide +kernel
    rw [ha]
    exact (canonical36125 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2598 + difference 5 3) (sourceB2598 + difference 3 5) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2598 + difference 5 3) (sourceB2598 + difference 3 5) sourceC2598) = raw28885 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw28885; decide +kernel
    rw [ha]
    exact (canonical28885 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2598 + difference 5 4) (sourceB2598 + difference 4 5) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2598 + difference 5 4) (sourceB2598 + difference 4 5) sourceC2598) = raw36126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36126; decide +kernel
    rw [ha]
    exact (canonical36126 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2598 sourceB2598 sourceC2598
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2598, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2076 : Integer.Sparse.reindex keyMap MixedData.row2076 = numericRow2076 := by decide +kernel

theorem numericCheck2076 (x : Master → ℝ) : Integer.Sparse.eval numericRow2076 x =
    (1728 : ℝ) * reducedSource2076 x := by
  norm_num [numericRow2076, reducedSource2076, Integer.Sparse.eval, Sparse.eval, nodeValue4767, nodeValue4769, nodeValue4811, nodeValue4939, nodeValue4946, nodeValue5168, nodeValue5337, nodeValue5356, nodeValue5393, nodeValue5416, nodeValue5434, nodeValue5464, nodeValue5465, nodeValue5486]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2076 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2076 (mixedVector B) = 0 := by
  have h4767 : mixedVector B (Sum.inr 4767) = Sparse.eval nodeValue4767 (mixedVector B) := by
    change mixedMoment B node4767 node4767Labels = _
    exact sound4767 B hB hF
  have h4769 : mixedVector B (Sum.inr 4769) = Sparse.eval nodeValue4769 (mixedVector B) := by
    change mixedMoment B node4769 node4769Labels = _
    exact sound4769 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4939 : mixedVector B (Sum.inr 4939) = Sparse.eval nodeValue4939 (mixedVector B) := by
    change mixedMoment B node4939 node4939Labels = _
    exact sound4939 B hB hF
  have h4946 : mixedVector B (Sum.inr 4946) = Sparse.eval nodeValue4946 (mixedVector B) := by
    change mixedMoment B node4946 node4946Labels = _
    exact sound4946 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168_e B hB hF
  have h5337 : mixedVector B (Sum.inr 5337) = Sparse.eval nodeValue5337 (mixedVector B) := by
    change mixedMoment B node5337 node5337Labels = _
    exact sound5337 B hB hF
  have h5356 : mixedVector B (Sum.inr 5356) = Sparse.eval nodeValue5356 (mixedVector B) := by
    change mixedMoment B node5356 node5356Labels = _
    exact sound5356 B hB hF
  have h5393 : mixedVector B (Sum.inr 5393) = Sparse.eval nodeValue5393 (mixedVector B) := by
    change mixedMoment B node5393 node5393Labels = _
    exact sound5393 B hB hF
  have h5416 : mixedVector B (Sum.inr 5416) = Sparse.eval nodeValue5416 (mixedVector B) := by
    change mixedMoment B node5416 node5416Labels = _
    exact sound5416_e B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  have h5464 : mixedVector B (Sum.inr 5464) = Sparse.eval nodeValue5464 (mixedVector B) := by
    change mixedMoment B node5464 node5464Labels = _
    exact sound5464_e B hB hF
  have h5465 : mixedVector B (Sum.inr 5465) = Sparse.eval nodeValue5465 (mixedVector B) := by
    change mixedMoment B node5465 node5465Labels = _
    exact sound5465_e B hB hF
  have h5486 : mixedVector B (Sum.inr 5486) = Sparse.eval nodeValue5486 (mixedVector B) := by
    change mixedMoment B node5486 node5486Labels = _
    exact sound5486 B hB hF
  simpa only [sourceForm2598, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4767, h4769, h4811, h4939, h4946, h5168, h5337, h5356, h5393, h5416, h5434, h5464, h5465, h5486, reducedSource2076] using sourceEq2598 B hB

theorem rowSound2076_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2076 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2076, numericCheck2076, reducedZero2076 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076_e_oai
