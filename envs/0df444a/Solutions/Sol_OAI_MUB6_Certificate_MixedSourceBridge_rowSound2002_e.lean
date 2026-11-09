-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:41:20.147651+00:00
-- url     : https://prove2.me/submissions/7ecfb70a-327d-4228-be2d-f4110bee1dfa

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5434_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5439_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1503 raw1503Labels = mixedMoment B node4642 node4642Labels := by
  calc
    mixedMoment B raw1503 raw1503Labels = mixedMoment B raw1503step0 raw1503step0Labels := by
      have ha : raw1503step0 = (fun i j => raw1503 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1503step0 raw1503; decide +kernel
      have hl : raw1503step0Labels = raw1503Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1503 raw1503Labels permutation152 permutation4
    mixedMoment B raw1503step0 raw1503step0Labels = mixedMoment B raw1503step1 raw1503step1Labels := by
      have ha : raw1503step1 = raw1503step0 := by apply Matrix.ext; unfold raw1503step1 raw1503step0; decide +kernel
      have hl : raw1503step0Labels = labelEmbedding7 ∘ raw1503step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1503step0 raw1503step0Labels raw1503step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4642 node4642Labels := by rfl

theorem canonical1504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1504 raw1504Labels = mixedMoment B node1771 node1771Labels := by
  calc
    mixedMoment B raw1504 raw1504Labels = mixedMoment B raw1504step0 raw1504step0Labels := by
      have ha : raw1504step0 = (fun i j => raw1504 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1504step0 raw1504; decide +kernel
      have hl : raw1504step0Labels = raw1504Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1504 raw1504Labels permutation152 permutation4
    _ = mixedMoment B node1771 node1771Labels := by rfl

theorem canonical1505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1505 raw1505Labels = mixedMoment B node1838 node1838Labels := by
  calc
    mixedMoment B raw1505 raw1505Labels = mixedMoment B raw1505step0 raw1505step0Labels := by
      have ha : raw1505step0 = (fun i j => raw1505 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1505step0 raw1505; decide +kernel
      have hl : raw1505step0Labels = raw1505Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1505 raw1505Labels permutation153 permutation6
    mixedMoment B raw1505step0 raw1505step0Labels = mixedMoment B raw1505step1 raw1505step1Labels := by
      have ha : raw1505step1 = -raw1505step0 := by apply Matrix.ext; change ∀ i j, raw1505step1 i j = -(raw1505step0 i j); unfold raw1505step1 raw1505step0; decide +kernel
      have hl : raw1505step1Labels = raw1505step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1505step1 raw1505step1Labels = mixedMoment B raw1505step2 raw1505step2Labels := by
      have ha : raw1505step2 = raw1505step1 := by apply Matrix.ext; unfold raw1505step2 raw1505step1; decide +kernel
      have hl : raw1505step1Labels = labelEmbedding1 ∘ raw1505step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1505step1 raw1505step1Labels raw1505step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1838 node1838Labels := by rfl

theorem canonical1506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1506 raw1506Labels = mixedMoment B node4644 node4644Labels := by
  calc
    mixedMoment B raw1506 raw1506Labels = mixedMoment B raw1506step0 raw1506step0Labels := by
      have ha : raw1506step0 = (fun i j => raw1506 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1506step0 raw1506; decide +kernel
      have hl : raw1506step0Labels = raw1506Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1506 raw1506Labels permutation32 permutation4
    mixedMoment B raw1506step0 raw1506step0Labels = mixedMoment B raw1506step1 raw1506step1Labels := by
      have ha : raw1506step1 = raw1506step0 := by apply Matrix.ext; unfold raw1506step1 raw1506step0; decide +kernel
      have hl : raw1506step0Labels = labelEmbedding7 ∘ raw1506step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1506step0 raw1506step0Labels raw1506step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4644 node4644Labels := by rfl

theorem canonical1507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1507 raw1507Labels = mixedMoment B node1773 node1773Labels := by
  calc
    mixedMoment B raw1507 raw1507Labels = mixedMoment B raw1507step0 raw1507step0Labels := by
      have ha : raw1507step0 = (fun i j => raw1507 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1507step0 raw1507; decide +kernel
      have hl : raw1507step0Labels = raw1507Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1507 raw1507Labels permutation32 permutation4
    _ = mixedMoment B node1773 node1773Labels := by rfl

theorem canonical1508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1508 raw1508Labels = mixedMoment B node1841 node1841Labels := by
  calc
    mixedMoment B raw1508 raw1508Labels = mixedMoment B raw1508step0 raw1508step0Labels := by
      have ha : raw1508step0 = (fun i j => raw1508 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1508step0 raw1508; decide +kernel
      have hl : raw1508step0Labels = raw1508Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1508 raw1508Labels permutation32 permutation6
    mixedMoment B raw1508step0 raw1508step0Labels = mixedMoment B raw1508step1 raw1508step1Labels := by
      have ha : raw1508step1 = -raw1508step0 := by apply Matrix.ext; change ∀ i j, raw1508step1 i j = -(raw1508step0 i j); unfold raw1508step1 raw1508step0; decide +kernel
      have hl : raw1508step1Labels = raw1508step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1508step1 raw1508step1Labels = mixedMoment B raw1508step2 raw1508step2Labels := by
      have ha : raw1508step2 = raw1508step1 := by apply Matrix.ext; unfold raw1508step2 raw1508step1; decide +kernel
      have hl : raw1508step1Labels = labelEmbedding1 ∘ raw1508step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1508step1 raw1508step1Labels raw1508step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1841 node1841Labels := by rfl

theorem canonical1509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1509 raw1509Labels = mixedMoment B node4645 node4645Labels := by
  calc
    mixedMoment B raw1509 raw1509Labels = mixedMoment B raw1509step0 raw1509step0Labels := by
      have ha : raw1509step0 = (fun i j => raw1509 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1509step0 raw1509; decide +kernel
      have hl : raw1509step0Labels = raw1509Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1509 raw1509Labels permutation32 permutation4
    mixedMoment B raw1509step0 raw1509step0Labels = mixedMoment B raw1509step1 raw1509step1Labels := by
      have ha : raw1509step1 = raw1509step0 := by apply Matrix.ext; unfold raw1509step1 raw1509step0; decide +kernel
      have hl : raw1509step0Labels = labelEmbedding7 ∘ raw1509step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1509step0 raw1509step0Labels raw1509step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4645 node4645Labels := by rfl

theorem canonical1510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1510 raw1510Labels = mixedMoment B node1774 node1774Labels := by
  calc
    mixedMoment B raw1510 raw1510Labels = mixedMoment B raw1510step0 raw1510step0Labels := by
      have ha : raw1510step0 = (fun i j => raw1510 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1510step0 raw1510; decide +kernel
      have hl : raw1510step0Labels = raw1510Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1510 raw1510Labels permutation32 permutation4
    _ = mixedMoment B node1774 node1774Labels := by rfl

theorem canonical1511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1511 raw1511Labels = mixedMoment B node1840 node1840Labels := by
  calc
    mixedMoment B raw1511 raw1511Labels = mixedMoment B raw1511step0 raw1511step0Labels := by
      have ha : raw1511step0 = (fun i j => raw1511 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1511step0 raw1511; decide +kernel
      have hl : raw1511step0Labels = raw1511Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1511 raw1511Labels permutation32 permutation6
    mixedMoment B raw1511step0 raw1511step0Labels = mixedMoment B raw1511step1 raw1511step1Labels := by
      have ha : raw1511step1 = -raw1511step0 := by apply Matrix.ext; change ∀ i j, raw1511step1 i j = -(raw1511step0 i j); unfold raw1511step1 raw1511step0; decide +kernel
      have hl : raw1511step1Labels = raw1511step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1511step1 raw1511step1Labels = mixedMoment B raw1511step2 raw1511step2Labels := by
      have ha : raw1511step2 = raw1511step1 := by apply Matrix.ext; unfold raw1511step2 raw1511step1; decide +kernel
      have hl : raw1511step1Labels = labelEmbedding1 ∘ raw1511step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1511step1 raw1511step1Labels raw1511step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1840 node1840Labels := by rfl

theorem canonical1524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1524 raw1524Labels = mixedMoment B node4654 node4654Labels := by
  calc
    mixedMoment B raw1524 raw1524Labels = mixedMoment B raw1524step0 raw1524step0Labels := by
      have ha : raw1524step0 = (fun i j => raw1524 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1524step0 raw1524; decide +kernel
      have hl : raw1524step0Labels = raw1524Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1524 raw1524Labels permutation32 permutation4
    mixedMoment B raw1524step0 raw1524step0Labels = mixedMoment B raw1524step1 raw1524step1Labels := by
      have ha : raw1524step1 = raw1524step0 := by apply Matrix.ext; unfold raw1524step1 raw1524step0; decide +kernel
      have hl : raw1524step0Labels = labelEmbedding7 ∘ raw1524step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1524step0 raw1524step0Labels raw1524step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4654 node4654Labels := by rfl

theorem canonical1525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1525 raw1525Labels = mixedMoment B node1782 node1782Labels := by
  calc
    mixedMoment B raw1525 raw1525Labels = mixedMoment B raw1525step0 raw1525step0Labels := by
      have ha : raw1525step0 = (fun i j => raw1525 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1525step0 raw1525; decide +kernel
      have hl : raw1525step0Labels = raw1525Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1525 raw1525Labels permutation32 permutation4
    _ = mixedMoment B node1782 node1782Labels := by rfl

theorem canonical1526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1526 raw1526Labels = mixedMoment B node1855 node1855Labels := by
  calc
    mixedMoment B raw1526 raw1526Labels = mixedMoment B raw1526step0 raw1526step0Labels := by
      have ha : raw1526step0 = (fun i j => raw1526 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1526step0 raw1526; decide +kernel
      have hl : raw1526step0Labels = raw1526Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1526 raw1526Labels permutation35 permutation6
    mixedMoment B raw1526step0 raw1526step0Labels = mixedMoment B raw1526step1 raw1526step1Labels := by
      have ha : raw1526step1 = -raw1526step0 := by apply Matrix.ext; change ∀ i j, raw1526step1 i j = -(raw1526step0 i j); unfold raw1526step1 raw1526step0; decide +kernel
      have hl : raw1526step1Labels = raw1526step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1526step1 raw1526step1Labels = mixedMoment B raw1526step2 raw1526step2Labels := by
      have ha : raw1526step2 = raw1526step1 := by apply Matrix.ext; unfold raw1526step2 raw1526step1; decide +kernel
      have hl : raw1526step1Labels = labelEmbedding1 ∘ raw1526step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1526step1 raw1526step1Labels raw1526step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1855 node1855Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical117
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15062 raw15062Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw15062 raw15062Labels = mixedMoment B raw15062step0 raw15062step0Labels := by
      have hz : ∀ j, raw15062 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15062step0 = (fun i j => raw15062 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15062step0 raw15062; decide +kernel
      have hl : raw15062step0Labels = raw15062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15062 raw15062Labels permutation346 hz
    mixedMoment B raw15062step0 raw15062step0Labels = mixedMoment B raw15062step1 raw15062step1Labels := by
      have ha : raw15062step1 = (fun i j => raw15062step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15062step1 raw15062step0; decide +kernel
      have hl : raw15062step1Labels = raw15062step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15062step0 raw15062step0Labels permutation32 permutation3
    mixedMoment B raw15062step1 raw15062step1Labels = mixedMoment B raw15062step2 raw15062step2Labels := by
      have ha : raw15062step2 = raw15062step1 := by apply Matrix.ext; unfold raw15062step2 raw15062step1; decide +kernel
      have hl : raw15062step1Labels = labelEmbedding6 ∘ raw15062step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15062step1 raw15062step1Labels raw15062step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical15066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15066 raw15066Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw15066 raw15066Labels = mixedMoment B raw15066step0 raw15066step0Labels := by
      have ha : raw15066step0 = (fun i j => raw15066 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15066step0 raw15066; decide +kernel
      have hl : raw15066step0Labels = raw15066Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15066 raw15066Labels permutation160 permutation3
    mixedMoment B raw15066step0 raw15066step0Labels = mixedMoment B raw15066step1 raw15066step1Labels := by
      have ha : raw15066step1 = raw15066step0 := by apply Matrix.ext; unfold raw15066step1 raw15066step0; decide +kernel
      have hl : raw15066step0Labels = labelEmbedding6 ∘ raw15066step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15066step0 raw15066step0Labels raw15066step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical15071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15071 raw15071Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw15071 raw15071Labels = mixedMoment B raw15071step0 raw15071step0Labels := by
      have hz : ∀ j, raw15071 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15071step0 = (fun i j => raw15071 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15071step0 raw15071; decide +kernel
      have hl : raw15071step0Labels = raw15071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15071 raw15071Labels permutation346 hz
    mixedMoment B raw15071step0 raw15071step0Labels = mixedMoment B raw15071step1 raw15071step1Labels := by
      have ha : raw15071step1 = (fun i j => raw15071step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15071step1 raw15071step0; decide +kernel
      have hl : raw15071step1Labels = raw15071step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15071step0 raw15071step0Labels permutation34 permutation3
    mixedMoment B raw15071step1 raw15071step1Labels = mixedMoment B raw15071step2 raw15071step2Labels := by
      have ha : raw15071step2 = raw15071step1 := by apply Matrix.ext; unfold raw15071step2 raw15071step1; decide +kernel
      have hl : raw15071step1Labels = labelEmbedding6 ∘ raw15071step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15071step1 raw15071step1Labels raw15071step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

theorem canonical15072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15072 raw15072Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw15072 raw15072Labels = mixedMoment B raw15072step0 raw15072step0Labels := by
      have ha : raw15072step0 = (fun i j => raw15072 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15072step0 raw15072; decide +kernel
      have hl : raw15072step0Labels = raw15072Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15072 raw15072Labels permutation178 permutation3
    mixedMoment B raw15072step0 raw15072step0Labels = mixedMoment B raw15072step1 raw15072step1Labels := by
      have ha : raw15072step1 = raw15072step0 := by apply Matrix.ext; unfold raw15072step1 raw15072step0; decide +kernel
      have hl : raw15072step0Labels = labelEmbedding6 ∘ raw15072step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15072step0 raw15072step0Labels raw15072step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

theorem canonical15073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15073 raw15073Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw15073 raw15073Labels = mixedMoment B raw15073step0 raw15073step0Labels := by
      have hz : ∀ j, raw15073 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15073step0 = (fun i j => raw15073 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15073step0 raw15073; decide +kernel
      have hl : raw15073step0Labels = raw15073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15073 raw15073Labels permutation346 hz
    mixedMoment B raw15073step0 raw15073step0Labels = mixedMoment B raw15073step1 raw15073step1Labels := by
      have ha : raw15073step1 = (fun i j => raw15073step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15073step1 raw15073step0; decide +kernel
      have hl : raw15073step1Labels = raw15073step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15073step0 raw15073step0Labels permutation34 permutation3
    mixedMoment B raw15073step1 raw15073step1Labels = mixedMoment B raw15073step2 raw15073step2Labels := by
      have ha : raw15073step2 = raw15073step1 := by apply Matrix.ext; unfold raw15073step2 raw15073step1; decide +kernel
      have hl : raw15073step1Labels = labelEmbedding6 ∘ raw15073step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15073step1 raw15073step1Labels raw15073step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

theorem canonical15074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15074 raw15074Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw15074 raw15074Labels = mixedMoment B raw15074step0 raw15074step0Labels := by
      have hz : ∀ j, raw15074 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15074step0 = (fun i j => raw15074 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15074step0 raw15074; decide +kernel
      have hl : raw15074step0Labels = raw15074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15074 raw15074Labels permutation346 hz
    mixedMoment B raw15074step0 raw15074step0Labels = mixedMoment B raw15074step1 raw15074step1Labels := by
      have ha : raw15074step1 = (fun i j => raw15074step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15074step1 raw15074step0; decide +kernel
      have hl : raw15074step1Labels = raw15074step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15074step0 raw15074step0Labels permutation32 permutation3
    mixedMoment B raw15074step1 raw15074step1Labels = mixedMoment B raw15074step2 raw15074step2Labels := by
      have ha : raw15074step2 = raw15074step1 := by apply Matrix.ext; unfold raw15074step2 raw15074step1; decide +kernel
      have hl : raw15074step1Labels = labelEmbedding6 ∘ raw15074step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15074step1 raw15074step1Labels raw15074step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

theorem canonical15078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15078 raw15078Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw15078 raw15078Labels = mixedMoment B raw15078step0 raw15078step0Labels := by
      have hz : ∀ j, raw15078 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15078step0 = (fun i j => raw15078 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15078step0 raw15078; decide +kernel
      have hl : raw15078step0Labels = raw15078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15078 raw15078Labels permutation346 hz
    mixedMoment B raw15078step0 raw15078step0Labels = mixedMoment B raw15078step1 raw15078step1Labels := by
      have ha : raw15078step1 = (fun i j => raw15078step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15078step1 raw15078step0; decide +kernel
      have hl : raw15078step1Labels = raw15078step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15078step0 raw15078step0Labels permutation32 permutation3
    mixedMoment B raw15078step1 raw15078step1Labels = mixedMoment B raw15078step2 raw15078step2Labels := by
      have ha : raw15078step2 = raw15078step1 := by apply Matrix.ext; unfold raw15078step2 raw15078step1; decide +kernel
      have hl : raw15078step1Labels = labelEmbedding6 ∘ raw15078step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15078step1 raw15078step1Labels raw15078step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1596 raw1596Labels = mixedMoment B node4709 node4709Labels := by
  calc
    mixedMoment B raw1596 raw1596Labels = mixedMoment B raw1596step0 raw1596step0Labels := by
      have ha : raw1596step0 = (fun i j => raw1596 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1596step0 raw1596; decide +kernel
      have hl : raw1596step0Labels = raw1596Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1596 raw1596Labels permutation152 permutation4
    mixedMoment B raw1596step0 raw1596step0Labels = mixedMoment B raw1596step1 raw1596step1Labels := by
      have ha : raw1596step1 = raw1596step0 := by apply Matrix.ext; unfold raw1596step1 raw1596step0; decide +kernel
      have hl : raw1596step0Labels = labelEmbedding7 ∘ raw1596step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1596step0 raw1596step0Labels raw1596step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4709 node4709Labels := by rfl

theorem canonical1597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1597 raw1597Labels = mixedMoment B node1863 node1863Labels := by
  calc
    mixedMoment B raw1597 raw1597Labels = mixedMoment B raw1597step0 raw1597step0Labels := by
      have ha : raw1597step0 = (fun i j => raw1597 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1597step0 raw1597; decide +kernel
      have hl : raw1597step0Labels = raw1597Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1597 raw1597Labels permutation152 permutation4
    _ = mixedMoment B node1863 node1863Labels := by rfl

theorem canonical1598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1598 raw1598Labels = mixedMoment B node1883 node1883Labels := by
  calc
    mixedMoment B raw1598 raw1598Labels = mixedMoment B raw1598step0 raw1598step0Labels := by
      have ha : raw1598step0 = (fun i j => raw1598 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1598step0 raw1598; decide +kernel
      have hl : raw1598step0Labels = raw1598Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1598 raw1598Labels permutation152 permutation6
    mixedMoment B raw1598step0 raw1598step0Labels = mixedMoment B raw1598step1 raw1598step1Labels := by
      have ha : raw1598step1 = -raw1598step0 := by apply Matrix.ext; change ∀ i j, raw1598step1 i j = -(raw1598step0 i j); unfold raw1598step1 raw1598step0; decide +kernel
      have hl : raw1598step1Labels = raw1598step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1598step1 raw1598step1Labels = mixedMoment B raw1598step2 raw1598step2Labels := by
      have ha : raw1598step2 = raw1598step1 := by apply Matrix.ext; unfold raw1598step2 raw1598step1; decide +kernel
      have hl : raw1598step1Labels = labelEmbedding1 ∘ raw1598step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1598step1 raw1598step1Labels raw1598step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1883 node1883Labels := by rfl

theorem canonical1599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1599 raw1599Labels = mixedMoment B node4710 node4710Labels := by
  calc
    mixedMoment B raw1599 raw1599Labels = mixedMoment B raw1599step0 raw1599step0Labels := by
      have ha : raw1599step0 = (fun i j => raw1599 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1599step0 raw1599; decide +kernel
      have hl : raw1599step0Labels = raw1599Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1599 raw1599Labels permutation152 permutation4
    mixedMoment B raw1599step0 raw1599step0Labels = mixedMoment B raw1599step1 raw1599step1Labels := by
      have ha : raw1599step1 = raw1599step0 := by apply Matrix.ext; unfold raw1599step1 raw1599step0; decide +kernel
      have hl : raw1599step0Labels = labelEmbedding7 ∘ raw1599step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1599step0 raw1599step0Labels raw1599step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4710 node4710Labels := by rfl

theorem canonical1600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1600 raw1600Labels = mixedMoment B node1864 node1864Labels := by
  calc
    mixedMoment B raw1600 raw1600Labels = mixedMoment B raw1600step0 raw1600step0Labels := by
      have ha : raw1600step0 = (fun i j => raw1600 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1600step0 raw1600; decide +kernel
      have hl : raw1600step0Labels = raw1600Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1600 raw1600Labels permutation152 permutation4
    _ = mixedMoment B node1864 node1864Labels := by rfl

theorem canonical1601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1601 raw1601Labels = mixedMoment B node1882 node1882Labels := by
  calc
    mixedMoment B raw1601 raw1601Labels = mixedMoment B raw1601step0 raw1601step0Labels := by
      have ha : raw1601step0 = (fun i j => raw1601 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1601step0 raw1601; decide +kernel
      have hl : raw1601step0Labels = raw1601Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1601 raw1601Labels permutation152 permutation6
    mixedMoment B raw1601step0 raw1601step0Labels = mixedMoment B raw1601step1 raw1601step1Labels := by
      have ha : raw1601step1 = -raw1601step0 := by apply Matrix.ext; change ∀ i j, raw1601step1 i j = -(raw1601step0 i j); unfold raw1601step1 raw1601step0; decide +kernel
      have hl : raw1601step1Labels = raw1601step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1601step1 raw1601step1Labels = mixedMoment B raw1601step2 raw1601step2Labels := by
      have ha : raw1601step2 = raw1601step1 := by apply Matrix.ext; unfold raw1601step2 raw1601step1; decide +kernel
      have hl : raw1601step1Labels = labelEmbedding1 ∘ raw1601step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1601step1 raw1601step1Labels raw1601step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1882 node1882Labels := by rfl

theorem canonical1611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1611 raw1611Labels = mixedMoment B node4717 node4717Labels := by
  calc
    mixedMoment B raw1611 raw1611Labels = mixedMoment B raw1611step0 raw1611step0Labels := by
      have ha : raw1611step0 = (fun i j => raw1611 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1611step0 raw1611; decide +kernel
      have hl : raw1611step0Labels = raw1611Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1611 raw1611Labels permutation152 permutation4
    mixedMoment B raw1611step0 raw1611step0Labels = mixedMoment B raw1611step1 raw1611step1Labels := by
      have ha : raw1611step1 = raw1611step0 := by apply Matrix.ext; unfold raw1611step1 raw1611step0; decide +kernel
      have hl : raw1611step0Labels = labelEmbedding7 ∘ raw1611step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1611step0 raw1611step0Labels raw1611step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4717 node4717Labels := by rfl

theorem canonical1612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1612 raw1612Labels = mixedMoment B node1871 node1871Labels := by
  calc
    mixedMoment B raw1612 raw1612Labels = mixedMoment B raw1612step0 raw1612step0Labels := by
      have ha : raw1612step0 = (fun i j => raw1612 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1612step0 raw1612; decide +kernel
      have hl : raw1612step0Labels = raw1612Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1612 raw1612Labels permutation152 permutation4
    _ = mixedMoment B node1871 node1871Labels := by rfl

theorem canonical1613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1613 raw1613Labels = mixedMoment B node1892 node1892Labels := by
  calc
    mixedMoment B raw1613 raw1613Labels = mixedMoment B raw1613step0 raw1613step0Labels := by
      have ha : raw1613step0 = (fun i j => raw1613 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1613step0 raw1613; decide +kernel
      have hl : raw1613step0Labels = raw1613Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1613 raw1613Labels permutation155 permutation6
    mixedMoment B raw1613step0 raw1613step0Labels = mixedMoment B raw1613step1 raw1613step1Labels := by
      have ha : raw1613step1 = -raw1613step0 := by apply Matrix.ext; change ∀ i j, raw1613step1 i j = -(raw1613step0 i j); unfold raw1613step1 raw1613step0; decide +kernel
      have hl : raw1613step1Labels = raw1613step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1613step1 raw1613step1Labels = mixedMoment B raw1613step2 raw1613step2Labels := by
      have ha : raw1613step2 = raw1613step1 := by apply Matrix.ext; unfold raw1613step2 raw1613step1; decide +kernel
      have hl : raw1613step1Labels = labelEmbedding1 ∘ raw1613step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1613step1 raw1613step1Labels raw1613step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1892 node1892Labels := by rfl

theorem canonical1653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1653 raw1653Labels = mixedMoment B node4737 node4737Labels := by
  calc
    mixedMoment B raw1653 raw1653Labels = mixedMoment B raw1653step0 raw1653step0Labels := by
      have ha : raw1653step0 = (fun i j => raw1653 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1653step0 raw1653; decide +kernel
      have hl : raw1653step0Labels = raw1653Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1653 raw1653Labels permutation152 permutation4
    mixedMoment B raw1653step0 raw1653step0Labels = mixedMoment B raw1653step1 raw1653step1Labels := by
      have ha : raw1653step1 = raw1653step0 := by apply Matrix.ext; unfold raw1653step1 raw1653step0; decide +kernel
      have hl : raw1653step0Labels = labelEmbedding7 ∘ raw1653step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1653step0 raw1653step0Labels raw1653step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4737 node4737Labels := by rfl

theorem canonical1654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1654 raw1654Labels = mixedMoment B node1909 node1909Labels := by
  calc
    mixedMoment B raw1654 raw1654Labels = mixedMoment B raw1654step0 raw1654step0Labels := by
      have ha : raw1654step0 = (fun i j => raw1654 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1654step0 raw1654; decide +kernel
      have hl : raw1654step0Labels = raw1654Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1654 raw1654Labels permutation152 permutation4
    _ = mixedMoment B node1909 node1909Labels := by rfl

theorem canonical1655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1655 raw1655Labels = mixedMoment B node1909 node1909Labels := by
  calc
    mixedMoment B raw1655 raw1655Labels = mixedMoment B raw1655step0 raw1655step0Labels := by
      have ha : raw1655step0 = (fun i j => raw1655 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1655step0 raw1655; decide +kernel
      have hl : raw1655step0Labels = raw1655Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1655 raw1655Labels permutation159 permutation6
    mixedMoment B raw1655step0 raw1655step0Labels = mixedMoment B raw1655step1 raw1655step1Labels := by
      have ha : raw1655step1 = -raw1655step0 := by apply Matrix.ext; change ∀ i j, raw1655step1 i j = -(raw1655step0 i j); unfold raw1655step1 raw1655step0; decide +kernel
      have hl : raw1655step1Labels = raw1655step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1655step1 raw1655step1Labels = mixedMoment B raw1655step2 raw1655step2Labels := by
      have ha : raw1655step2 = raw1655step1 := by apply Matrix.ext; unfold raw1655step2 raw1655step1; decide +kernel
      have hl : raw1655step1Labels = labelEmbedding1 ∘ raw1655step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1655step1 raw1655step1Labels raw1655step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1909 node1909Labels := by rfl

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

theorem canonical1734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1734 raw1734Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw1734 raw1734Labels = mixedMoment B raw1734step0 raw1734step0Labels := by
      have ha : raw1734step0 = (fun i j => raw1734 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1734step0 raw1734; decide +kernel
      have hl : raw1734step0Labels = raw1734Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1734 raw1734Labels permutation152 permutation4
    mixedMoment B raw1734step0 raw1734step0Labels = mixedMoment B raw1734step1 raw1734step1Labels := by
      have ha : raw1734step1 = raw1734step0 := by apply Matrix.ext; unfold raw1734step1 raw1734step0; decide +kernel
      have hl : raw1734step0Labels = labelEmbedding7 ∘ raw1734step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1734step0 raw1734step0Labels raw1734step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical1735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1735 raw1735Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw1735 raw1735Labels = mixedMoment B raw1735step0 raw1735step0Labels := by
      have ha : raw1735step0 = (fun i j => raw1735 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1735step0 raw1735; decide +kernel
      have hl : raw1735step0Labels = raw1735Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1735 raw1735Labels permutation152 permutation4
    _ = mixedMoment B node2020 node2020Labels := by rfl

theorem canonical1736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1736 raw1736Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw1736 raw1736Labels = mixedMoment B raw1736step0 raw1736step0Labels := by
      have ha : raw1736step0 = (fun i j => raw1736 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1736step0 raw1736; decide +kernel
      have hl : raw1736step0Labels = raw1736Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1736 raw1736Labels permutation158 permutation6
    mixedMoment B raw1736step0 raw1736step0Labels = mixedMoment B raw1736step1 raw1736step1Labels := by
      have ha : raw1736step1 = -raw1736step0 := by apply Matrix.ext; change ∀ i j, raw1736step1 i j = -(raw1736step0 i j); unfold raw1736step1 raw1736step0; decide +kernel
      have hl : raw1736step1Labels = raw1736step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1736step1 raw1736step1Labels = mixedMoment B raw1736step2 raw1736step2Labels := by
      have ha : raw1736step2 = raw1736step1 := by apply Matrix.ext; unfold raw1736step2 raw1736step1; decide +kernel
      have hl : raw1736step1Labels = labelEmbedding1 ∘ raw1736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1736step1 raw1736step1Labels raw1736step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

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

theorem canonical1761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1761 raw1761Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw1761 raw1761Labels = mixedMoment B raw1761step0 raw1761step0Labels := by
      have ha : raw1761step0 = (fun i j => raw1761 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1761step0 raw1761; decide +kernel
      have hl : raw1761step0Labels = raw1761Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1761 raw1761Labels permutation152 permutation4
    mixedMoment B raw1761step0 raw1761step0Labels = mixedMoment B raw1761step1 raw1761step1Labels := by
      have ha : raw1761step1 = raw1761step0 := by apply Matrix.ext; unfold raw1761step1 raw1761step0; decide +kernel
      have hl : raw1761step0Labels = labelEmbedding7 ∘ raw1761step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1761step0 raw1761step0Labels raw1761step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

theorem canonical1762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1762 raw1762Labels = mixedMoment B node2051 node2051Labels := by
  calc
    mixedMoment B raw1762 raw1762Labels = mixedMoment B raw1762step0 raw1762step0Labels := by
      have ha : raw1762step0 = (fun i j => raw1762 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1762step0 raw1762; decide +kernel
      have hl : raw1762step0Labels = raw1762Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1762 raw1762Labels permutation152 permutation4
    _ = mixedMoment B node2051 node2051Labels := by rfl

theorem canonical1763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1763 raw1763Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw1763 raw1763Labels = mixedMoment B raw1763step0 raw1763step0Labels := by
      have ha : raw1763step0 = (fun i j => raw1763 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1763step0 raw1763; decide +kernel
      have hl : raw1763step0Labels = raw1763Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1763 raw1763Labels permutation152 permutation6
    mixedMoment B raw1763step0 raw1763step0Labels = mixedMoment B raw1763step1 raw1763step1Labels := by
      have ha : raw1763step1 = -raw1763step0 := by apply Matrix.ext; change ∀ i j, raw1763step1 i j = -(raw1763step0 i j); unfold raw1763step1 raw1763step0; decide +kernel
      have hl : raw1763step1Labels = raw1763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1763step1 raw1763step1Labels = mixedMoment B raw1763step2 raw1763step2Labels := by
      have ha : raw1763step2 = raw1763step1 := by apply Matrix.ext; unfold raw1763step2 raw1763step1; decide +kernel
      have hl : raw1763step1Labels = labelEmbedding1 ∘ raw1763step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1763step1 raw1763step1Labels raw1763step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2191 node2191Labels := by rfl

theorem canonical1764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1764 raw1764Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw1764 raw1764Labels = mixedMoment B raw1764step0 raw1764step0Labels := by
      have ha : raw1764step0 = (fun i j => raw1764 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1764step0 raw1764; decide +kernel
      have hl : raw1764step0Labels = raw1764Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1764 raw1764Labels permutation32 permutation4
    mixedMoment B raw1764step0 raw1764step0Labels = mixedMoment B raw1764step1 raw1764step1Labels := by
      have ha : raw1764step1 = raw1764step0 := by apply Matrix.ext; unfold raw1764step1 raw1764step0; decide +kernel
      have hl : raw1764step0Labels = labelEmbedding7 ∘ raw1764step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1764step0 raw1764step0Labels raw1764step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

theorem canonical1765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1765 raw1765Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw1765 raw1765Labels = mixedMoment B raw1765step0 raw1765step0Labels := by
      have ha : raw1765step0 = (fun i j => raw1765 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1765step0 raw1765; decide +kernel
      have hl : raw1765step0Labels = raw1765Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1765 raw1765Labels permutation32 permutation4
    _ = mixedMoment B node2052 node2052Labels := by rfl

theorem canonical1766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1766 raw1766Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw1766 raw1766Labels = mixedMoment B raw1766step0 raw1766step0Labels := by
      have ha : raw1766step0 = (fun i j => raw1766 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1766step0 raw1766; decide +kernel
      have hl : raw1766step0Labels = raw1766Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1766 raw1766Labels permutation32 permutation6
    mixedMoment B raw1766step0 raw1766step0Labels = mixedMoment B raw1766step1 raw1766step1Labels := by
      have ha : raw1766step1 = -raw1766step0 := by apply Matrix.ext; change ∀ i j, raw1766step1 i j = -(raw1766step0 i j); unfold raw1766step1 raw1766step0; decide +kernel
      have hl : raw1766step1Labels = raw1766step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1766step1 raw1766step1Labels = mixedMoment B raw1766step2 raw1766step2Labels := by
      have ha : raw1766step2 = raw1766step1 := by apply Matrix.ext; unfold raw1766step2 raw1766step1; decide +kernel
      have hl : raw1766step1Labels = labelEmbedding1 ∘ raw1766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1766step1 raw1766step1Labels raw1766step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

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

theorem canonical2517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2517 raw2517Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw2517 raw2517Labels = mixedMoment B raw2517step0 raw2517step0Labels := by
      have ha : raw2517step0 = (fun i j => raw2517 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2517step0 raw2517; decide +kernel
      have hl : raw2517step0Labels = raw2517Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2517 raw2517Labels permutation32 permutation4
    mixedMoment B raw2517step0 raw2517step0Labels = mixedMoment B raw2517step1 raw2517step1Labels := by
      have ha : raw2517step1 = raw2517step0 := by apply Matrix.ext; unfold raw2517step1 raw2517step0; decide +kernel
      have hl : raw2517step0Labels = labelEmbedding7 ∘ raw2517step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2517step0 raw2517step0Labels raw2517step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

theorem canonical2518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2518 raw2518Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw2518 raw2518Labels = mixedMoment B raw2518step0 raw2518step0Labels := by
      have ha : raw2518step0 = (fun i j => raw2518 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2518step0 raw2518; decide +kernel
      have hl : raw2518step0Labels = raw2518Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2518 raw2518Labels permutation32 permutation4
    _ = mixedMoment B node3845 node3845Labels := by rfl

theorem canonical2519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2519 raw2519Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw2519 raw2519Labels = mixedMoment B raw2519step0 raw2519step0Labels := by
      have ha : raw2519step0 = (fun i j => raw2519 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2519step0 raw2519; decide +kernel
      have hl : raw2519step0Labels = raw2519Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2519 raw2519Labels permutation39 permutation6
    mixedMoment B raw2519step0 raw2519step0Labels = mixedMoment B raw2519step1 raw2519step1Labels := by
      have ha : raw2519step1 = -raw2519step0 := by apply Matrix.ext; change ∀ i j, raw2519step1 i j = -(raw2519step0 i j); unfold raw2519step1 raw2519step0; decide +kernel
      have hl : raw2519step1Labels = raw2519step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2519step1 raw2519step1Labels = mixedMoment B raw2519step2 raw2519step2Labels := by
      have ha : raw2519step2 = raw2519step1 := by apply Matrix.ext; unfold raw2519step2 raw2519step1; decide +kernel
      have hl : raw2519step1Labels = labelEmbedding1 ∘ raw2519step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2519step1 raw2519step1Labels raw2519step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3845 node3845Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3416 raw3416Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw3416 raw3416Labels = mixedMoment B raw3416step0 raw3416step0Labels := by
      have hz : ∀ j, raw3416 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3416step0 = (fun i j => raw3416 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3416step0 raw3416; decide +kernel
      have hl : raw3416step0Labels = raw3416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3416 raw3416Labels permutation346 hz
    mixedMoment B raw3416step0 raw3416step0Labels = mixedMoment B raw3416step1 raw3416step1Labels := by
      have ha : raw3416step1 = (fun i j => raw3416step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3416step1 raw3416step0; decide +kernel
      have hl : raw3416step1Labels = raw3416step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3416step0 raw3416step0Labels permutation35 permutation3
    mixedMoment B raw3416step1 raw3416step1Labels = mixedMoment B raw3416step2 raw3416step2Labels := by
      have ha : raw3416step2 = raw3416step1 := by apply Matrix.ext; unfold raw3416step2 raw3416step1; decide +kernel
      have hl : raw3416step1Labels = labelEmbedding6 ∘ raw3416step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3416step1 raw3416step1Labels raw3416step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

theorem canonical3426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3426 raw3426Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw3426 raw3426Labels = mixedMoment B raw3426step0 raw3426step0Labels := by
      have hz : ∀ j, raw3426 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3426step0 = (fun i j => raw3426 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3426step0 raw3426; decide +kernel
      have hl : raw3426step0Labels = raw3426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3426 raw3426Labels permutation346 hz
    mixedMoment B raw3426step0 raw3426step0Labels = mixedMoment B raw3426step1 raw3426step1Labels := by
      have ha : raw3426step1 = (fun i j => raw3426step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3426step1 raw3426step0; decide +kernel
      have hl : raw3426step1Labels = raw3426step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3426step0 raw3426step0Labels permutation32 permutation3
    mixedMoment B raw3426step1 raw3426step1Labels = mixedMoment B raw3426step2 raw3426step2Labels := by
      have ha : raw3426step2 = raw3426step1 := by apply Matrix.ext; unfold raw3426step2 raw3426step1; decide +kernel
      have hl : raw3426step1Labels = labelEmbedding6 ∘ raw3426step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3426step1 raw3426step1Labels raw3426step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical267
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34243 raw34243Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw34243 raw34243Labels = mixedMoment B raw34243step0 raw34243step0Labels := by
      have hz : ∀ j, raw34243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34243step0 = (fun i j => raw34243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34243step0 raw34243; decide +kernel
      have hl : raw34243step0Labels = raw34243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34243 raw34243Labels permutation346 hz
    mixedMoment B raw34243step0 raw34243step0Labels = mixedMoment B raw34243step1 raw34243step1Labels := by
      have ha : raw34243step1 = (fun i j => raw34243step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34243step1 raw34243step0; decide +kernel
      have hl : raw34243step1Labels = raw34243step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34243step0 raw34243step0Labels permutation34 permutation3
    mixedMoment B raw34243step1 raw34243step1Labels = mixedMoment B raw34243step2 raw34243step2Labels := by
      have ha : raw34243step2 = raw34243step1 := by apply Matrix.ext; unfold raw34243step2 raw34243step1; decide +kernel
      have hl : raw34243step1Labels = labelEmbedding6 ∘ raw34243step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34243step1 raw34243step1Labels raw34243step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4265 node4265Labels := by rfl

theorem canonical34244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34244 raw34244Labels = mixedMoment B node4737 node4737Labels := by
  calc
    mixedMoment B raw34244 raw34244Labels = mixedMoment B raw34244step0 raw34244step0Labels := by
      have ha : raw34244step0 = (fun i j => raw34244 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34244step0 raw34244; decide +kernel
      have hl : raw34244step0Labels = raw34244Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34244 raw34244Labels permutation178 permutation3
    mixedMoment B raw34244step0 raw34244step0Labels = mixedMoment B raw34244step1 raw34244step1Labels := by
      have ha : raw34244step1 = raw34244step0 := by apply Matrix.ext; unfold raw34244step1 raw34244step0; decide +kernel
      have hl : raw34244step0Labels = labelEmbedding6 ∘ raw34244step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34244step0 raw34244step0Labels raw34244step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4737 node4737Labels := by rfl

theorem canonical34245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34245 raw34245Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw34245 raw34245Labels = mixedMoment B raw34245step0 raw34245step0Labels := by
      have hz : ∀ j, raw34245 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34245step0 = (fun i j => raw34245 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34245step0 raw34245; decide +kernel
      have hl : raw34245step0Labels = raw34245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34245 raw34245Labels permutation346 hz
    mixedMoment B raw34245step0 raw34245step0Labels = mixedMoment B raw34245step1 raw34245step1Labels := by
      have ha : raw34245step1 = (fun i j => raw34245step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34245step1 raw34245step0; decide +kernel
      have hl : raw34245step1Labels = raw34245step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34245step0 raw34245step0Labels permutation45 permutation5
    mixedMoment B raw34245step1 raw34245step1Labels = mixedMoment B raw34245step2 raw34245step2Labels := by
      have ha : raw34245step2 = -raw34245step1 := by apply Matrix.ext; change ∀ i j, raw34245step2 i j = -(raw34245step1 i j); unfold raw34245step2 raw34245step1; decide +kernel
      have hl : raw34245step2Labels = raw34245step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34245step2 raw34245step2Labels = mixedMoment B raw34245step3 raw34245step3Labels := by
      have ha : raw34245step3 = raw34245step2 := by apply Matrix.ext; unfold raw34245step3 raw34245step2; decide +kernel
      have hl : raw34245step2Labels = labelEmbedding8 ∘ raw34245step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34245step2 raw34245step2Labels raw34245step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical34246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34246 raw34246Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw34246 raw34246Labels = mixedMoment B raw34246step0 raw34246step0Labels := by
      have hz : ∀ j, raw34246 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34246step0 = (fun i j => raw34246 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34246step0 raw34246; decide +kernel
      have hl : raw34246step0Labels = raw34246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34246 raw34246Labels permutation346 hz
    mixedMoment B raw34246step0 raw34246step0Labels = mixedMoment B raw34246step1 raw34246step1Labels := by
      have ha : raw34246step1 = (fun i j => raw34246step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34246step1 raw34246step0; decide +kernel
      have hl : raw34246step1Labels = raw34246step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34246step0 raw34246step0Labels permutation48 permutation5
    mixedMoment B raw34246step1 raw34246step1Labels = mixedMoment B raw34246step2 raw34246step2Labels := by
      have ha : raw34246step2 = -raw34246step1 := by apply Matrix.ext; change ∀ i j, raw34246step2 i j = -(raw34246step1 i j); unfold raw34246step2 raw34246step1; decide +kernel
      have hl : raw34246step2Labels = raw34246step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34246step2 raw34246step2Labels = mixedMoment B raw34246step3 raw34246step3Labels := by
      have ha : raw34246step3 = raw34246step2 := by apply Matrix.ext; unfold raw34246step3 raw34246step2; decide +kernel
      have hl : raw34246step2Labels = labelEmbedding8 ∘ raw34246step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34246step2 raw34246step2Labels raw34246step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

theorem canonical34247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34247 raw34247Labels = mixedMoment B node4210 node4210Labels := by
  calc
    mixedMoment B raw34247 raw34247Labels = mixedMoment B raw34247step0 raw34247step0Labels := by
      have ha : raw34247step0 = (fun i j => raw34247 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34247step0 raw34247; decide +kernel
      have hl : raw34247step0Labels = raw34247Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34247 raw34247Labels permutation164 permutation3
    mixedMoment B raw34247step0 raw34247step0Labels = mixedMoment B raw34247step1 raw34247step1Labels := by
      have ha : raw34247step1 = raw34247step0 := by apply Matrix.ext; unfold raw34247step1 raw34247step0; decide +kernel
      have hl : raw34247step0Labels = labelEmbedding6 ∘ raw34247step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34247step0 raw34247step0Labels raw34247step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4210 node4210Labels := by rfl

theorem canonical34248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34248 raw34248Labels = mixedMoment B node4642 node4642Labels := by
  calc
    mixedMoment B raw34248 raw34248Labels = mixedMoment B raw34248step0 raw34248step0Labels := by
      have ha : raw34248step0 = (fun i j => raw34248 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34248step0 raw34248; decide +kernel
      have hl : raw34248step0Labels = raw34248Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34248 raw34248Labels permutation164 permutation3
    mixedMoment B raw34248step0 raw34248step0Labels = mixedMoment B raw34248step1 raw34248step1Labels := by
      have ha : raw34248step1 = raw34248step0 := by apply Matrix.ext; unfold raw34248step1 raw34248step0; decide +kernel
      have hl : raw34248step0Labels = labelEmbedding6 ∘ raw34248step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34248step0 raw34248step0Labels raw34248step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4642 node4642Labels := by rfl

theorem canonical34249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34249 raw34249Labels = mixedMoment B node4787 node4787Labels := by
  calc
    mixedMoment B raw34249 raw34249Labels = mixedMoment B raw34249step0 raw34249step0Labels := by
      have ha : raw34249step0 = (fun i j => raw34249 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34249step0 raw34249; decide +kernel
      have hl : raw34249step0Labels = raw34249Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34249 raw34249Labels permutation164 permutation3
    mixedMoment B raw34249step0 raw34249step0Labels = mixedMoment B raw34249step1 raw34249step1Labels := by
      have ha : raw34249step1 = raw34249step0 := by apply Matrix.ext; unfold raw34249step1 raw34249step0; decide +kernel
      have hl : raw34249step0Labels = labelEmbedding6 ∘ raw34249step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34249step0 raw34249step0Labels raw34249step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4787 node4787Labels := by rfl

theorem canonical34250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34250 raw34250Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw34250 raw34250Labels = mixedMoment B raw34250step0 raw34250step0Labels := by
      have ha : raw34250step0 = (fun i j => raw34250 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34250step0 raw34250; decide +kernel
      have hl : raw34250step0Labels = raw34250Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34250 raw34250Labels permutation168 permutation3
    mixedMoment B raw34250step0 raw34250step0Labels = mixedMoment B raw34250step1 raw34250step1Labels := by
      have ha : raw34250step1 = raw34250step0 := by apply Matrix.ext; unfold raw34250step1 raw34250step0; decide +kernel
      have hl : raw34250step0Labels = labelEmbedding6 ∘ raw34250step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34250step0 raw34250step0Labels raw34250step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

theorem canonical34251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34251 raw34251Labels = mixedMoment B node4213 node4213Labels := by
  calc
    mixedMoment B raw34251 raw34251Labels = mixedMoment B raw34251step0 raw34251step0Labels := by
      have hz : ∀ j, raw34251 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34251step0 = (fun i j => raw34251 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34251step0 raw34251; decide +kernel
      have hl : raw34251step0Labels = raw34251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34251 raw34251Labels permutation346 hz
    mixedMoment B raw34251step0 raw34251step0Labels = mixedMoment B raw34251step1 raw34251step1Labels := by
      have ha : raw34251step1 = (fun i j => raw34251step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34251step1 raw34251step0; decide +kernel
      have hl : raw34251step1Labels = raw34251step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34251step0 raw34251step0Labels permutation35 permutation3
    mixedMoment B raw34251step1 raw34251step1Labels = mixedMoment B raw34251step2 raw34251step2Labels := by
      have ha : raw34251step2 = raw34251step1 := by apply Matrix.ext; unfold raw34251step2 raw34251step1; decide +kernel
      have hl : raw34251step1Labels = labelEmbedding6 ∘ raw34251step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34251step1 raw34251step1Labels raw34251step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4213 node4213Labels := by rfl

theorem canonical34252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34252 raw34252Labels = mixedMoment B node4645 node4645Labels := by
  calc
    mixedMoment B raw34252 raw34252Labels = mixedMoment B raw34252step0 raw34252step0Labels := by
      have hz : ∀ j, raw34252 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34252step0 = (fun i j => raw34252 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34252step0 raw34252; decide +kernel
      have hl : raw34252step0Labels = raw34252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34252 raw34252Labels permutation346 hz
    mixedMoment B raw34252step0 raw34252step0Labels = mixedMoment B raw34252step1 raw34252step1Labels := by
      have ha : raw34252step1 = (fun i j => raw34252step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34252step1 raw34252step0; decide +kernel
      have hl : raw34252step1Labels = raw34252step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34252step0 raw34252step0Labels permutation35 permutation3
    mixedMoment B raw34252step1 raw34252step1Labels = mixedMoment B raw34252step2 raw34252step2Labels := by
      have ha : raw34252step2 = raw34252step1 := by apply Matrix.ext; unfold raw34252step2 raw34252step1; decide +kernel
      have hl : raw34252step1Labels = labelEmbedding6 ∘ raw34252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34252step1 raw34252step1Labels raw34252step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4645 node4645Labels := by rfl

theorem canonical34253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34253 raw34253Labels = mixedMoment B node4710 node4710Labels := by
  calc
    mixedMoment B raw34253 raw34253Labels = mixedMoment B raw34253step0 raw34253step0Labels := by
      have ha : raw34253step0 = (fun i j => raw34253 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34253step0 raw34253; decide +kernel
      have hl : raw34253step0Labels = raw34253Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34253 raw34253Labels permutation179 permutation3
    mixedMoment B raw34253step0 raw34253step0Labels = mixedMoment B raw34253step1 raw34253step1Labels := by
      have ha : raw34253step1 = raw34253step0 := by apply Matrix.ext; unfold raw34253step1 raw34253step0; decide +kernel
      have hl : raw34253step0Labels = labelEmbedding6 ∘ raw34253step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34253step0 raw34253step0Labels raw34253step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4710 node4710Labels := by rfl

theorem canonical34254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34254 raw34254Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw34254 raw34254Labels = mixedMoment B raw34254step0 raw34254step0Labels := by
      have hz : ∀ j, raw34254 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34254step0 = (fun i j => raw34254 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34254step0 raw34254; decide +kernel
      have hl : raw34254step0Labels = raw34254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34254 raw34254Labels permutation346 hz
    mixedMoment B raw34254step0 raw34254step0Labels = mixedMoment B raw34254step1 raw34254step1Labels := by
      have ha : raw34254step1 = (fun i j => raw34254step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34254step1 raw34254step0; decide +kernel
      have hl : raw34254step1Labels = raw34254step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34254step0 raw34254step0Labels permutation45 permutation5
    mixedMoment B raw34254step1 raw34254step1Labels = mixedMoment B raw34254step2 raw34254step2Labels := by
      have ha : raw34254step2 = -raw34254step1 := by apply Matrix.ext; change ∀ i j, raw34254step2 i j = -(raw34254step1 i j); unfold raw34254step2 raw34254step1; decide +kernel
      have hl : raw34254step2Labels = raw34254step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34254step2 raw34254step2Labels = mixedMoment B raw34254step3 raw34254step3Labels := by
      have ha : raw34254step3 = raw34254step2 := by apply Matrix.ext; unfold raw34254step3 raw34254step2; decide +kernel
      have hl : raw34254step2Labels = labelEmbedding8 ∘ raw34254step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34254step2 raw34254step2Labels raw34254step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

theorem canonical34255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34255 raw34255Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw34255 raw34255Labels = mixedMoment B raw34255step0 raw34255step0Labels := by
      have hz : ∀ j, raw34255 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34255step0 = (fun i j => raw34255 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34255step0 raw34255; decide +kernel
      have hl : raw34255step0Labels = raw34255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34255 raw34255Labels permutation346 hz
    mixedMoment B raw34255step0 raw34255step0Labels = mixedMoment B raw34255step1 raw34255step1Labels := by
      have ha : raw34255step1 = (fun i j => raw34255step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34255step1 raw34255step0; decide +kernel
      have hl : raw34255step1Labels = raw34255step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34255step0 raw34255step0Labels permutation35 permutation3
    mixedMoment B raw34255step1 raw34255step1Labels = mixedMoment B raw34255step2 raw34255step2Labels := by
      have ha : raw34255step2 = raw34255step1 := by apply Matrix.ext; unfold raw34255step2 raw34255step1; decide +kernel
      have hl : raw34255step1Labels = labelEmbedding6 ∘ raw34255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34255step1 raw34255step1Labels raw34255step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

theorem canonical34256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34256 raw34256Labels = mixedMoment B node4224 node4224Labels := by
  calc
    mixedMoment B raw34256 raw34256Labels = mixedMoment B raw34256step0 raw34256step0Labels := by
      have hz : ∀ j, raw34256 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34256step0 = (fun i j => raw34256 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34256step0 raw34256; decide +kernel
      have hl : raw34256step0Labels = raw34256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34256 raw34256Labels permutation346 hz
    mixedMoment B raw34256step0 raw34256step0Labels = mixedMoment B raw34256step1 raw34256step1Labels := by
      have ha : raw34256step1 = (fun i j => raw34256step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34256step1 raw34256step0; decide +kernel
      have hl : raw34256step1Labels = raw34256step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34256step0 raw34256step0Labels permutation32 permutation3
    mixedMoment B raw34256step1 raw34256step1Labels = mixedMoment B raw34256step2 raw34256step2Labels := by
      have ha : raw34256step2 = raw34256step1 := by apply Matrix.ext; unfold raw34256step2 raw34256step1; decide +kernel
      have hl : raw34256step1Labels = labelEmbedding6 ∘ raw34256step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34256step1 raw34256step1Labels raw34256step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4224 node4224Labels := by rfl

theorem canonical34257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34257 raw34257Labels = mixedMoment B node4654 node4654Labels := by
  calc
    mixedMoment B raw34257 raw34257Labels = mixedMoment B raw34257step0 raw34257step0Labels := by
      have hz : ∀ j, raw34257 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34257step0 = (fun i j => raw34257 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34257step0 raw34257; decide +kernel
      have hl : raw34257step0Labels = raw34257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34257 raw34257Labels permutation346 hz
    mixedMoment B raw34257step0 raw34257step0Labels = mixedMoment B raw34257step1 raw34257step1Labels := by
      have ha : raw34257step1 = (fun i j => raw34257step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34257step1 raw34257step0; decide +kernel
      have hl : raw34257step1Labels = raw34257step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34257step0 raw34257step0Labels permutation32 permutation3
    mixedMoment B raw34257step1 raw34257step1Labels = mixedMoment B raw34257step2 raw34257step2Labels := by
      have ha : raw34257step2 = raw34257step1 := by apply Matrix.ext; unfold raw34257step2 raw34257step1; decide +kernel
      have hl : raw34257step1Labels = labelEmbedding6 ∘ raw34257step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34257step1 raw34257step1Labels raw34257step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4654 node4654Labels := by rfl

theorem canonical34258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34258 raw34258Labels = mixedMoment B node4717 node4717Labels := by
  calc
    mixedMoment B raw34258 raw34258Labels = mixedMoment B raw34258step0 raw34258step0Labels := by
      have ha : raw34258step0 = (fun i j => raw34258 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34258step0 raw34258; decide +kernel
      have hl : raw34258step0Labels = raw34258Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34258 raw34258Labels permutation176 permutation3
    mixedMoment B raw34258step0 raw34258step0Labels = mixedMoment B raw34258step1 raw34258step1Labels := by
      have ha : raw34258step1 = raw34258step0 := by apply Matrix.ext; unfold raw34258step1 raw34258step0; decide +kernel
      have hl : raw34258step0Labels = labelEmbedding6 ∘ raw34258step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34258step0 raw34258step0Labels raw34258step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4717 node4717Labels := by rfl

theorem canonical34259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34259 raw34259Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw34259 raw34259Labels = mixedMoment B raw34259step0 raw34259step0Labels := by
      have hz : ∀ j, raw34259 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34259step0 = (fun i j => raw34259 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34259step0 raw34259; decide +kernel
      have hl : raw34259step0Labels = raw34259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34259 raw34259Labels permutation346 hz
    mixedMoment B raw34259step0 raw34259step0Labels = mixedMoment B raw34259step1 raw34259step1Labels := by
      have ha : raw34259step1 = (fun i j => raw34259step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34259step1 raw34259step0; decide +kernel
      have hl : raw34259step1Labels = raw34259step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34259step0 raw34259step0Labels permutation36 permutation3
    mixedMoment B raw34259step1 raw34259step1Labels = mixedMoment B raw34259step2 raw34259step2Labels := by
      have ha : raw34259step2 = raw34259step1 := by apply Matrix.ext; unfold raw34259step2 raw34259step1; decide +kernel
      have hl : raw34259step1Labels = labelEmbedding6 ∘ raw34259step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34259step1 raw34259step1Labels raw34259step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical34260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34260 raw34260Labels = mixedMoment B node4212 node4212Labels := by
  calc
    mixedMoment B raw34260 raw34260Labels = mixedMoment B raw34260step0 raw34260step0Labels := by
      have hz : ∀ j, raw34260 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34260step0 = (fun i j => raw34260 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34260step0 raw34260; decide +kernel
      have hl : raw34260step0Labels = raw34260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34260 raw34260Labels permutation346 hz
    mixedMoment B raw34260step0 raw34260step0Labels = mixedMoment B raw34260step1 raw34260step1Labels := by
      have ha : raw34260step1 = (fun i j => raw34260step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34260step1 raw34260step0; decide +kernel
      have hl : raw34260step1Labels = raw34260step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34260step0 raw34260step0Labels permutation34 permutation3
    mixedMoment B raw34260step1 raw34260step1Labels = mixedMoment B raw34260step2 raw34260step2Labels := by
      have ha : raw34260step2 = raw34260step1 := by apply Matrix.ext; unfold raw34260step2 raw34260step1; decide +kernel
      have hl : raw34260step1Labels = labelEmbedding6 ∘ raw34260step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34260step1 raw34260step1Labels raw34260step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4212 node4212Labels := by rfl

theorem canonical34261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34261 raw34261Labels = mixedMoment B node4644 node4644Labels := by
  calc
    mixedMoment B raw34261 raw34261Labels = mixedMoment B raw34261step0 raw34261step0Labels := by
      have hz : ∀ j, raw34261 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34261step0 = (fun i j => raw34261 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34261step0 raw34261; decide +kernel
      have hl : raw34261step0Labels = raw34261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34261 raw34261Labels permutation346 hz
    mixedMoment B raw34261step0 raw34261step0Labels = mixedMoment B raw34261step1 raw34261step1Labels := by
      have ha : raw34261step1 = (fun i j => raw34261step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34261step1 raw34261step0; decide +kernel
      have hl : raw34261step1Labels = raw34261step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34261step0 raw34261step0Labels permutation34 permutation3
    mixedMoment B raw34261step1 raw34261step1Labels = mixedMoment B raw34261step2 raw34261step2Labels := by
      have ha : raw34261step2 = raw34261step1 := by apply Matrix.ext; unfold raw34261step2 raw34261step1; decide +kernel
      have hl : raw34261step1Labels = labelEmbedding6 ∘ raw34261step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34261step1 raw34261step1Labels raw34261step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4644 node4644Labels := by rfl

theorem canonical34262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34262 raw34262Labels = mixedMoment B node4709 node4709Labels := by
  calc
    mixedMoment B raw34262 raw34262Labels = mixedMoment B raw34262step0 raw34262step0Labels := by
      have ha : raw34262step0 = (fun i j => raw34262 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34262step0 raw34262; decide +kernel
      have hl : raw34262step0Labels = raw34262Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34262 raw34262Labels permutation178 permutation3
    mixedMoment B raw34262step0 raw34262step0Labels = mixedMoment B raw34262step1 raw34262step1Labels := by
      have ha : raw34262step1 = raw34262step0 := by apply Matrix.ext; unfold raw34262step1 raw34262step0; decide +kernel
      have hl : raw34262step0Labels = labelEmbedding6 ∘ raw34262step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34262step0 raw34262step0Labels raw34262step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4709 node4709Labels := by rfl

theorem canonical34263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34263 raw34263Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw34263 raw34263Labels = mixedMoment B raw34263step0 raw34263step0Labels := by
      have hz : ∀ j, raw34263 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34263step0 = (fun i j => raw34263 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34263step0 raw34263; decide +kernel
      have hl : raw34263step0Labels = raw34263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34263 raw34263Labels permutation346 hz
    mixedMoment B raw34263step0 raw34263step0Labels = mixedMoment B raw34263step1 raw34263step1Labels := by
      have ha : raw34263step1 = (fun i j => raw34263step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34263step1 raw34263step0; decide +kernel
      have hl : raw34263step1Labels = raw34263step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34263step0 raw34263step0Labels permutation34 permutation3
    mixedMoment B raw34263step1 raw34263step1Labels = mixedMoment B raw34263step2 raw34263step2Labels := by
      have ha : raw34263step2 = raw34263step1 := by apply Matrix.ext; unfold raw34263step2 raw34263step1; decide +kernel
      have hl : raw34263step1Labels = labelEmbedding6 ∘ raw34263step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34263step1 raw34263step1Labels raw34263step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

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

theorem canonical891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw891 raw891Labels = mixedMoment B node4210 node4210Labels := by
  calc
    mixedMoment B raw891 raw891Labels = mixedMoment B raw891step0 raw891step0Labels := by
      have ha : raw891step0 = (fun i j => raw891 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw891step0 raw891; decide +kernel
      have hl : raw891step0Labels = raw891Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw891 raw891Labels permutation152 permutation4
    mixedMoment B raw891step0 raw891step0Labels = mixedMoment B raw891step1 raw891step1Labels := by
      have ha : raw891step1 = raw891step0 := by apply Matrix.ext; unfold raw891step1 raw891step0; decide +kernel
      have hl : raw891step0Labels = labelEmbedding7 ∘ raw891step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw891step0 raw891step0Labels raw891step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4210 node4210Labels := by rfl

theorem canonical892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw892 raw892Labels = mixedMoment B node713 node713Labels := by
  calc
    mixedMoment B raw892 raw892Labels = mixedMoment B raw892step0 raw892step0Labels := by
      have ha : raw892step0 = (fun i j => raw892 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw892step0 raw892; decide +kernel
      have hl : raw892step0Labels = raw892Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw892 raw892Labels permutation152 permutation4
    _ = mixedMoment B node713 node713Labels := by rfl

theorem canonical893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw893 raw893Labels = mixedMoment B node751 node751Labels := by
  calc
    mixedMoment B raw893 raw893Labels = mixedMoment B raw893step0 raw893step0Labels := by
      have ha : raw893step0 = (fun i j => raw893 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw893step0 raw893; decide +kernel
      have hl : raw893step0Labels = raw893Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw893 raw893Labels permutation153 permutation6
    mixedMoment B raw893step0 raw893step0Labels = mixedMoment B raw893step1 raw893step1Labels := by
      have ha : raw893step1 = -raw893step0 := by apply Matrix.ext; change ∀ i j, raw893step1 i j = -(raw893step0 i j); unfold raw893step1 raw893step0; decide +kernel
      have hl : raw893step1Labels = raw893step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw893step1 raw893step1Labels = mixedMoment B raw893step2 raw893step2Labels := by
      have ha : raw893step2 = raw893step1 := by apply Matrix.ext; unfold raw893step2 raw893step1; decide +kernel
      have hl : raw893step1Labels = labelEmbedding1 ∘ raw893step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw893step1 raw893step1Labels raw893step2Labels labelEmbedding1 hl
    _ = mixedMoment B node751 node751Labels := by rfl

theorem canonical894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw894 raw894Labels = mixedMoment B node4212 node4212Labels := by
  calc
    mixedMoment B raw894 raw894Labels = mixedMoment B raw894step0 raw894step0Labels := by
      have ha : raw894step0 = (fun i j => raw894 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw894step0 raw894; decide +kernel
      have hl : raw894step0Labels = raw894Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw894 raw894Labels permutation32 permutation4
    mixedMoment B raw894step0 raw894step0Labels = mixedMoment B raw894step1 raw894step1Labels := by
      have ha : raw894step1 = raw894step0 := by apply Matrix.ext; unfold raw894step1 raw894step0; decide +kernel
      have hl : raw894step0Labels = labelEmbedding7 ∘ raw894step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw894step0 raw894step0Labels raw894step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4212 node4212Labels := by rfl

theorem canonical895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw895 raw895Labels = mixedMoment B node715 node715Labels := by
  calc
    mixedMoment B raw895 raw895Labels = mixedMoment B raw895step0 raw895step0Labels := by
      have ha : raw895step0 = (fun i j => raw895 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw895step0 raw895; decide +kernel
      have hl : raw895step0Labels = raw895Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw895 raw895Labels permutation32 permutation4
    _ = mixedMoment B node715 node715Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw896 raw896Labels = mixedMoment B node753 node753Labels := by
  calc
    mixedMoment B raw896 raw896Labels = mixedMoment B raw896step0 raw896step0Labels := by
      have ha : raw896step0 = (fun i j => raw896 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw896step0 raw896; decide +kernel
      have hl : raw896step0Labels = raw896Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw896 raw896Labels permutation32 permutation6
    mixedMoment B raw896step0 raw896step0Labels = mixedMoment B raw896step1 raw896step1Labels := by
      have ha : raw896step1 = -raw896step0 := by apply Matrix.ext; change ∀ i j, raw896step1 i j = -(raw896step0 i j); unfold raw896step1 raw896step0; decide +kernel
      have hl : raw896step1Labels = raw896step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw896step1 raw896step1Labels = mixedMoment B raw896step2 raw896step2Labels := by
      have ha : raw896step2 = raw896step1 := by apply Matrix.ext; unfold raw896step2 raw896step1; decide +kernel
      have hl : raw896step1Labels = labelEmbedding1 ∘ raw896step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw896step1 raw896step1Labels raw896step2Labels labelEmbedding1 hl
    _ = mixedMoment B node753 node753Labels := by rfl

theorem canonical897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw897 raw897Labels = mixedMoment B node4213 node4213Labels := by
  calc
    mixedMoment B raw897 raw897Labels = mixedMoment B raw897step0 raw897step0Labels := by
      have ha : raw897step0 = (fun i j => raw897 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw897step0 raw897; decide +kernel
      have hl : raw897step0Labels = raw897Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw897 raw897Labels permutation32 permutation4
    mixedMoment B raw897step0 raw897step0Labels = mixedMoment B raw897step1 raw897step1Labels := by
      have ha : raw897step1 = raw897step0 := by apply Matrix.ext; unfold raw897step1 raw897step0; decide +kernel
      have hl : raw897step0Labels = labelEmbedding7 ∘ raw897step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw897step0 raw897step0Labels raw897step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4213 node4213Labels := by rfl

theorem canonical898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw898 raw898Labels = mixedMoment B node716 node716Labels := by
  calc
    mixedMoment B raw898 raw898Labels = mixedMoment B raw898step0 raw898step0Labels := by
      have ha : raw898step0 = (fun i j => raw898 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw898step0 raw898; decide +kernel
      have hl : raw898step0Labels = raw898Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw898 raw898Labels permutation32 permutation4
    _ = mixedMoment B node716 node716Labels := by rfl

theorem canonical899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw899 raw899Labels = mixedMoment B node752 node752Labels := by
  calc
    mixedMoment B raw899 raw899Labels = mixedMoment B raw899step0 raw899step0Labels := by
      have ha : raw899step0 = (fun i j => raw899 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw899step0 raw899; decide +kernel
      have hl : raw899step0Labels = raw899Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw899 raw899Labels permutation32 permutation6
    mixedMoment B raw899step0 raw899step0Labels = mixedMoment B raw899step1 raw899step1Labels := by
      have ha : raw899step1 = -raw899step0 := by apply Matrix.ext; change ∀ i j, raw899step1 i j = -(raw899step0 i j); unfold raw899step1 raw899step0; decide +kernel
      have hl : raw899step1Labels = raw899step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw899step1 raw899step1Labels = mixedMoment B raw899step2 raw899step2Labels := by
      have ha : raw899step2 = raw899step1 := by apply Matrix.ext; unfold raw899step2 raw899step1; decide +kernel
      have hl : raw899step1Labels = labelEmbedding1 ∘ raw899step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw899step1 raw899step1Labels raw899step2Labels labelEmbedding1 hl
    _ = mixedMoment B node752 node752Labels := by rfl

theorem canonical912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw912 raw912Labels = mixedMoment B node4224 node4224Labels := by
  calc
    mixedMoment B raw912 raw912Labels = mixedMoment B raw912step0 raw912step0Labels := by
      have ha : raw912step0 = (fun i j => raw912 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw912step0 raw912; decide +kernel
      have hl : raw912step0Labels = raw912Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw912 raw912Labels permutation32 permutation4
    mixedMoment B raw912step0 raw912step0Labels = mixedMoment B raw912step1 raw912step1Labels := by
      have ha : raw912step1 = raw912step0 := by apply Matrix.ext; unfold raw912step1 raw912step0; decide +kernel
      have hl : raw912step0Labels = labelEmbedding7 ∘ raw912step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw912step0 raw912step0Labels raw912step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4224 node4224Labels := by rfl

theorem canonical913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw913 raw913Labels = mixedMoment B node725 node725Labels := by
  calc
    mixedMoment B raw913 raw913Labels = mixedMoment B raw913step0 raw913step0Labels := by
      have ha : raw913step0 = (fun i j => raw913 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw913step0 raw913; decide +kernel
      have hl : raw913step0Labels = raw913Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw913 raw913Labels permutation32 permutation4
    _ = mixedMoment B node725 node725Labels := by rfl

theorem canonical914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw914 raw914Labels = mixedMoment B node771 node771Labels := by
  calc
    mixedMoment B raw914 raw914Labels = mixedMoment B raw914step0 raw914step0Labels := by
      have ha : raw914step0 = (fun i j => raw914 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw914step0 raw914; decide +kernel
      have hl : raw914step0Labels = raw914Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw914 raw914Labels permutation35 permutation6
    mixedMoment B raw914step0 raw914step0Labels = mixedMoment B raw914step1 raw914step1Labels := by
      have ha : raw914step1 = -raw914step0 := by apply Matrix.ext; change ∀ i j, raw914step1 i j = -(raw914step0 i j); unfold raw914step1 raw914step0; decide +kernel
      have hl : raw914step1Labels = raw914step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw914step1 raw914step1Labels = mixedMoment B raw914step2 raw914step2Labels := by
      have ha : raw914step2 = raw914step1 := by apply Matrix.ext; unfold raw914step2 raw914step1; decide +kernel
      have hl : raw914step1Labels = labelEmbedding1 ∘ raw914step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw914step1 raw914step1Labels raw914step2Labels labelEmbedding1 hl
    _ = mixedMoment B node771 node771Labels := by rfl

theorem canonical990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw990 raw990Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw990 raw990Labels = mixedMoment B raw990step0 raw990step0Labels := by
      have ha : raw990step0 = (fun i j => raw990 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw990step0 raw990; decide +kernel
      have hl : raw990step0Labels = raw990Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw990 raw990Labels permutation32 permutation4
    mixedMoment B raw990step0 raw990step0Labels = mixedMoment B raw990step1 raw990step1Labels := by
      have ha : raw990step1 = raw990step0 := by apply Matrix.ext; unfold raw990step1 raw990step0; decide +kernel
      have hl : raw990step0Labels = labelEmbedding7 ∘ raw990step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw990step0 raw990step0Labels raw990step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4265 node4265Labels := by rfl

theorem canonical991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw991 raw991Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw991 raw991Labels = mixedMoment B raw991step0 raw991step0Labels := by
      have ha : raw991step0 = (fun i j => raw991 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw991step0 raw991; decide +kernel
      have hl : raw991step0Labels = raw991Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw991 raw991Labels permutation32 permutation4
    _ = mixedMoment B node807 node807Labels := by rfl

theorem canonical992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw992 raw992Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw992 raw992Labels = mixedMoment B raw992step0 raw992step0Labels := by
      have ha : raw992step0 = (fun i j => raw992 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw992step0 raw992; decide +kernel
      have hl : raw992step0Labels = raw992Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw992 raw992Labels permutation39 permutation6
    mixedMoment B raw992step0 raw992step0Labels = mixedMoment B raw992step1 raw992step1Labels := by
      have ha : raw992step1 = -raw992step0 := by apply Matrix.ext; change ∀ i j, raw992step1 i j = -(raw992step0 i j); unfold raw992step1 raw992step0; decide +kernel
      have hl : raw992step1Labels = raw992step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw992step1 raw992step1Labels = mixedMoment B raw992step2 raw992step2Labels := by
      have ha : raw992step2 = raw992step1 := by apply Matrix.ext; unfold raw992step2 raw992step1; decide +kernel
      have hl : raw992step1Labels = labelEmbedding1 ∘ raw992step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw992step1 raw992step1Labels raw992step2Labels labelEmbedding1 hl
    _ = mixedMoment B node807 node807Labels := by rfl

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

theorem singleton4210 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4210 node4210Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node713 node713Labels + mixedMoment B node751 node751Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw891 singletonSmall4210
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4210) = raw891Labels := by decide +kernel
  rw [hl, canonical891 B hB] at h
  have hc0 : mixedMoment B raw891 (Fin.cases (0 : Fin 2) singletonSmall4210) =
      mixedMoment B node713 node713Labels := by
    have ha : raw891 = raw892 := by apply Matrix.ext; unfold raw891 raw892; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4210 = raw892Labels := by decide +kernel
    rw [ha, hj, canonical892 B hB]
  have hc1 : mixedMoment B raw891 (Fin.cases (1 : Fin 2) singletonSmall4210) =
      mixedMoment B node751 node751Labels := by
    have ha : raw891 = raw893 := by apply Matrix.ext; unfold raw891 raw893; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4210 = raw893Labels := by decide +kernel
    rw [ha, hj, canonical893 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4212 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4212 node4212Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node715 node715Labels + mixedMoment B node753 node753Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw894 singletonSmall4212
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4212) = raw894Labels := by decide +kernel
  rw [hl, canonical894 B hB] at h
  have hc0 : mixedMoment B raw894 (Fin.cases (0 : Fin 2) singletonSmall4212) =
      mixedMoment B node715 node715Labels := by
    have ha : raw894 = raw895 := by apply Matrix.ext; unfold raw894 raw895; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4212 = raw895Labels := by decide +kernel
    rw [ha, hj, canonical895 B hB]
  have hc1 : mixedMoment B raw894 (Fin.cases (1 : Fin 2) singletonSmall4212) =
      mixedMoment B node753 node753Labels := by
    have ha : raw894 = raw896 := by apply Matrix.ext; unfold raw894 raw896; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4212 = raw896Labels := by decide +kernel
    rw [ha, hj, canonical896 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4213 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4213 node4213Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node716 node716Labels + mixedMoment B node752 node752Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw897 singletonSmall4213
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4213) = raw897Labels := by decide +kernel
  rw [hl, canonical897 B hB] at h
  have hc0 : mixedMoment B raw897 (Fin.cases (0 : Fin 2) singletonSmall4213) =
      mixedMoment B node716 node716Labels := by
    have ha : raw897 = raw898 := by apply Matrix.ext; unfold raw897 raw898; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4213 = raw898Labels := by decide +kernel
    rw [ha, hj, canonical898 B hB]
  have hc1 : mixedMoment B raw897 (Fin.cases (1 : Fin 2) singletonSmall4213) =
      mixedMoment B node752 node752Labels := by
    have ha : raw897 = raw899 := by apply Matrix.ext; unfold raw897 raw899; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4213 = raw899Labels := by decide +kernel
    rw [ha, hj, canonical899 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4224 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4224 node4224Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node725 node725Labels + mixedMoment B node771 node771Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw912 singletonSmall4224
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4224) = raw912Labels := by decide +kernel
  rw [hl, canonical912 B hB] at h
  have hc0 : mixedMoment B raw912 (Fin.cases (0 : Fin 2) singletonSmall4224) =
      mixedMoment B node725 node725Labels := by
    have ha : raw912 = raw913 := by apply Matrix.ext; unfold raw912 raw913; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4224 = raw913Labels := by decide +kernel
    rw [ha, hj, canonical913 B hB]
  have hc1 : mixedMoment B raw912 (Fin.cases (1 : Fin 2) singletonSmall4224) =
      mixedMoment B node771 node771Labels := by
    have ha : raw912 = raw914 := by apply Matrix.ext; unfold raw912 raw914; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4224 = raw914Labels := by decide +kernel
    rw [ha, hj, canonical914 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4265 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4265 node4265Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node807 node807Labels + mixedMoment B node807 node807Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw990 singletonSmall4265
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4265) = raw990Labels := by decide +kernel
  rw [hl, canonical990 B hB] at h
  have hc0 : mixedMoment B raw990 (Fin.cases (0 : Fin 2) singletonSmall4265) =
      mixedMoment B node807 node807Labels := by
    have ha : raw990 = raw991 := by apply Matrix.ext; unfold raw990 raw991; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4265 = raw991Labels := by decide +kernel
    rw [ha, hj, canonical991 B hB]
  have hc1 : mixedMoment B raw990 (Fin.cases (1 : Fin 2) singletonSmall4265) =
      mixedMoment B node807 node807Labels := by
    have ha : raw990 = raw992 := by apply Matrix.ext; unfold raw990 raw992; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4265 = raw992Labels := by decide +kernel
    rw [ha, hj, canonical992 B hB]
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

theorem singleton4642 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4642 node4642Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1771 node1771Labels + mixedMoment B node1838 node1838Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1503 singletonSmall4642
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4642) = raw1503Labels := by decide +kernel
  rw [hl, canonical1503 B hB] at h
  have hc0 : mixedMoment B raw1503 (Fin.cases (0 : Fin 2) singletonSmall4642) =
      mixedMoment B node1771 node1771Labels := by
    have ha : raw1503 = raw1504 := by apply Matrix.ext; unfold raw1503 raw1504; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4642 = raw1504Labels := by decide +kernel
    rw [ha, hj, canonical1504 B hB]
  have hc1 : mixedMoment B raw1503 (Fin.cases (1 : Fin 2) singletonSmall4642) =
      mixedMoment B node1838 node1838Labels := by
    have ha : raw1503 = raw1505 := by apply Matrix.ext; unfold raw1503 raw1505; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4642 = raw1505Labels := by decide +kernel
    rw [ha, hj, canonical1505 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4644 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4644 node4644Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1773 node1773Labels + mixedMoment B node1841 node1841Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1506 singletonSmall4644
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4644) = raw1506Labels := by decide +kernel
  rw [hl, canonical1506 B hB] at h
  have hc0 : mixedMoment B raw1506 (Fin.cases (0 : Fin 2) singletonSmall4644) =
      mixedMoment B node1773 node1773Labels := by
    have ha : raw1506 = raw1507 := by apply Matrix.ext; unfold raw1506 raw1507; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4644 = raw1507Labels := by decide +kernel
    rw [ha, hj, canonical1507 B hB]
  have hc1 : mixedMoment B raw1506 (Fin.cases (1 : Fin 2) singletonSmall4644) =
      mixedMoment B node1841 node1841Labels := by
    have ha : raw1506 = raw1508 := by apply Matrix.ext; unfold raw1506 raw1508; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4644 = raw1508Labels := by decide +kernel
    rw [ha, hj, canonical1508 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4645 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4645 node4645Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1774 node1774Labels + mixedMoment B node1840 node1840Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1509 singletonSmall4645
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4645) = raw1509Labels := by decide +kernel
  rw [hl, canonical1509 B hB] at h
  have hc0 : mixedMoment B raw1509 (Fin.cases (0 : Fin 2) singletonSmall4645) =
      mixedMoment B node1774 node1774Labels := by
    have ha : raw1509 = raw1510 := by apply Matrix.ext; unfold raw1509 raw1510; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4645 = raw1510Labels := by decide +kernel
    rw [ha, hj, canonical1510 B hB]
  have hc1 : mixedMoment B raw1509 (Fin.cases (1 : Fin 2) singletonSmall4645) =
      mixedMoment B node1840 node1840Labels := by
    have ha : raw1509 = raw1511 := by apply Matrix.ext; unfold raw1509 raw1511; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4645 = raw1511Labels := by decide +kernel
    rw [ha, hj, canonical1511 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4654 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4654 node4654Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1782 node1782Labels + mixedMoment B node1855 node1855Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1524 singletonSmall4654
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4654) = raw1524Labels := by decide +kernel
  rw [hl, canonical1524 B hB] at h
  have hc0 : mixedMoment B raw1524 (Fin.cases (0 : Fin 2) singletonSmall4654) =
      mixedMoment B node1782 node1782Labels := by
    have ha : raw1524 = raw1525 := by apply Matrix.ext; unfold raw1524 raw1525; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4654 = raw1525Labels := by decide +kernel
    rw [ha, hj, canonical1525 B hB]
  have hc1 : mixedMoment B raw1524 (Fin.cases (1 : Fin 2) singletonSmall4654) =
      mixedMoment B node1855 node1855Labels := by
    have ha : raw1524 = raw1526 := by apply Matrix.ext; unfold raw1524 raw1526; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4654 = raw1526Labels := by decide +kernel
    rw [ha, hj, canonical1526 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4709 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4709 node4709Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1863 node1863Labels + mixedMoment B node1883 node1883Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1596 singletonSmall4709
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4709) = raw1596Labels := by decide +kernel
  rw [hl, canonical1596 B hB] at h
  have hc0 : mixedMoment B raw1596 (Fin.cases (0 : Fin 2) singletonSmall4709) =
      mixedMoment B node1863 node1863Labels := by
    have ha : raw1596 = raw1597 := by apply Matrix.ext; unfold raw1596 raw1597; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4709 = raw1597Labels := by decide +kernel
    rw [ha, hj, canonical1597 B hB]
  have hc1 : mixedMoment B raw1596 (Fin.cases (1 : Fin 2) singletonSmall4709) =
      mixedMoment B node1883 node1883Labels := by
    have ha : raw1596 = raw1598 := by apply Matrix.ext; unfold raw1596 raw1598; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4709 = raw1598Labels := by decide +kernel
    rw [ha, hj, canonical1598 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4710 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4710 node4710Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1864 node1864Labels + mixedMoment B node1882 node1882Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1599 singletonSmall4710
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4710) = raw1599Labels := by decide +kernel
  rw [hl, canonical1599 B hB] at h
  have hc0 : mixedMoment B raw1599 (Fin.cases (0 : Fin 2) singletonSmall4710) =
      mixedMoment B node1864 node1864Labels := by
    have ha : raw1599 = raw1600 := by apply Matrix.ext; unfold raw1599 raw1600; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4710 = raw1600Labels := by decide +kernel
    rw [ha, hj, canonical1600 B hB]
  have hc1 : mixedMoment B raw1599 (Fin.cases (1 : Fin 2) singletonSmall4710) =
      mixedMoment B node1882 node1882Labels := by
    have ha : raw1599 = raw1601 := by apply Matrix.ext; unfold raw1599 raw1601; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4710 = raw1601Labels := by decide +kernel
    rw [ha, hj, canonical1601 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4717 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4717 node4717Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1871 node1871Labels + mixedMoment B node1892 node1892Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1611 singletonSmall4717
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4717) = raw1611Labels := by decide +kernel
  rw [hl, canonical1611 B hB] at h
  have hc0 : mixedMoment B raw1611 (Fin.cases (0 : Fin 2) singletonSmall4717) =
      mixedMoment B node1871 node1871Labels := by
    have ha : raw1611 = raw1612 := by apply Matrix.ext; unfold raw1611 raw1612; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4717 = raw1612Labels := by decide +kernel
    rw [ha, hj, canonical1612 B hB]
  have hc1 : mixedMoment B raw1611 (Fin.cases (1 : Fin 2) singletonSmall4717) =
      mixedMoment B node1892 node1892Labels := by
    have ha : raw1611 = raw1613 := by apply Matrix.ext; unfold raw1611 raw1613; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4717 = raw1613Labels := by decide +kernel
    rw [ha, hj, canonical1613 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4737 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4737 node4737Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1909 node1909Labels + mixedMoment B node1909 node1909Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1653 singletonSmall4737
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4737) = raw1653Labels := by decide +kernel
  rw [hl, canonical1653 B hB] at h
  have hc0 : mixedMoment B raw1653 (Fin.cases (0 : Fin 2) singletonSmall4737) =
      mixedMoment B node1909 node1909Labels := by
    have ha : raw1653 = raw1654 := by apply Matrix.ext; unfold raw1653 raw1654; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4737 = raw1654Labels := by decide +kernel
    rw [ha, hj, canonical1654 B hB]
  have hc1 : mixedMoment B raw1653 (Fin.cases (1 : Fin 2) singletonSmall4737) =
      mixedMoment B node1909 node1909Labels := by
    have ha : raw1653 = raw1655 := by apply Matrix.ext; unfold raw1653 raw1655; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4737 = raw1655Labels := by decide +kernel
    rw [ha, hj, canonical1655 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4802 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4802 node4802Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2020 node2020Labels + mixedMoment B node2202 node2202Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1734 singletonSmall4802
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4802) = raw1734Labels := by decide +kernel
  rw [hl, canonical1734 B hB] at h
  have hc0 : mixedMoment B raw1734 (Fin.cases (0 : Fin 2) singletonSmall4802) =
      mixedMoment B node2020 node2020Labels := by
    have ha : raw1734 = raw1735 := by apply Matrix.ext; unfold raw1734 raw1735; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4802 = raw1735Labels := by decide +kernel
    rw [ha, hj, canonical1735 B hB]
  have hc1 : mixedMoment B raw1734 (Fin.cases (1 : Fin 2) singletonSmall4802) =
      mixedMoment B node2202 node2202Labels := by
    have ha : raw1734 = raw1736 := by apply Matrix.ext; unfold raw1734 raw1736; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4802 = raw1736Labels := by decide +kernel
    rw [ha, hj, canonical1736 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4831 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4831 node4831Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2051 node2051Labels + mixedMoment B node2191 node2191Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1761 singletonSmall4831
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4831) = raw1761Labels := by decide +kernel
  rw [hl, canonical1761 B hB] at h
  have hc0 : mixedMoment B raw1761 (Fin.cases (0 : Fin 2) singletonSmall4831) =
      mixedMoment B node2051 node2051Labels := by
    have ha : raw1761 = raw1762 := by apply Matrix.ext; unfold raw1761 raw1762; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4831 = raw1762Labels := by decide +kernel
    rw [ha, hj, canonical1762 B hB]
  have hc1 : mixedMoment B raw1761 (Fin.cases (1 : Fin 2) singletonSmall4831) =
      mixedMoment B node2191 node2191Labels := by
    have ha : raw1761 = raw1763 := by apply Matrix.ext; unfold raw1761 raw1763; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4831 = raw1763Labels := by decide +kernel
    rw [ha, hj, canonical1763 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4832 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4832 node4832Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2052 node2052Labels + mixedMoment B node2193 node2193Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1764 singletonSmall4832
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4832) = raw1764Labels := by decide +kernel
  rw [hl, canonical1764 B hB] at h
  have hc0 : mixedMoment B raw1764 (Fin.cases (0 : Fin 2) singletonSmall4832) =
      mixedMoment B node2052 node2052Labels := by
    have ha : raw1764 = raw1765 := by apply Matrix.ext; unfold raw1764 raw1765; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4832 = raw1765Labels := by decide +kernel
    rw [ha, hj, canonical1765 B hB]
  have hc1 : mixedMoment B raw1764 (Fin.cases (1 : Fin 2) singletonSmall4832) =
      mixedMoment B node2193 node2193Labels := by
    have ha : raw1764 = raw1766 := by apply Matrix.ext; unfold raw1764 raw1766; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4832 = raw1766Labels := by decide +kernel
    rw [ha, hj, canonical1766 B hB]
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

theorem singleton5428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5428 node5428Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3845 node3845Labels + mixedMoment B node3845 node3845Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2517 singletonSmall5428
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5428) = raw2517Labels := by decide +kernel
  rw [hl, canonical2517 B hB] at h
  have hc0 : mixedMoment B raw2517 (Fin.cases (0 : Fin 2) singletonSmall5428) =
      mixedMoment B node3845 node3845Labels := by
    have ha : raw2517 = raw2518 := by apply Matrix.ext; unfold raw2517 raw2518; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5428 = raw2518Labels := by decide +kernel
    rw [ha, hj, canonical2518 B hB]
  have hc1 : mixedMoment B raw2517 (Fin.cases (1 : Fin 2) singletonSmall5428) =
      mixedMoment B node3845 node3845Labels := by
    have ha : raw2517 = raw2519 := by apply Matrix.ext; unfold raw2517 raw2519; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5428 = raw2519Labels := by decide +kernel
    rw [ha, hj, canonical2519 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node713 node713Labels = Sparse.eval nodeValue713 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 713) = mixedMoment B node713 node713Labels := rfl
  simpa [nodeValue713, Sparse.eval] using hc.symm

theorem sound715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node715 node715Labels = Sparse.eval nodeValue715 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 715) = mixedMoment B node715 node715Labels := rfl
  simpa [nodeValue715, Sparse.eval] using hc.symm

theorem sound716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node716 node716Labels = Sparse.eval nodeValue716 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 716) = mixedMoment B node716 node716Labels := rfl
  simpa [nodeValue716, Sparse.eval] using hc.symm

theorem sound725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node725 node725Labels = Sparse.eval nodeValue725 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 725) = mixedMoment B node725 node725Labels := rfl
  simpa [nodeValue725, Sparse.eval] using hc.symm

theorem sound751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node751 node751Labels = Sparse.eval nodeValue751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 751) = mixedMoment B node751 node751Labels := rfl
  simpa [nodeValue751, Sparse.eval] using hc.symm

theorem sound752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node752 node752Labels = Sparse.eval nodeValue752 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 752) = mixedMoment B node752 node752Labels := rfl
  simpa [nodeValue752, Sparse.eval] using hc.symm

theorem sound753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node753 node753Labels = Sparse.eval nodeValue753 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 753) = mixedMoment B node753 node753Labels := rfl
  simpa [nodeValue753, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node771 node771Labels = Sparse.eval nodeValue771 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 771) = mixedMoment B node771 node771Labels := rfl
  simpa [nodeValue771, Sparse.eval] using hc.symm

theorem sound807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node807 node807Labels = Sparse.eval nodeValue807 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 807) = mixedMoment B node807 node807Labels := rfl
  simpa [nodeValue807, Sparse.eval] using hc.symm

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

theorem sound1771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1771 node1771Labels = Sparse.eval nodeValue1771 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1771) = mixedMoment B node1771 node1771Labels := rfl
  simpa [nodeValue1771, Sparse.eval] using hc.symm

theorem sound1773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1773 node1773Labels = Sparse.eval nodeValue1773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1773) = mixedMoment B node1773 node1773Labels := rfl
  simpa [nodeValue1773, Sparse.eval] using hc.symm

theorem sound1774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1774 node1774Labels = Sparse.eval nodeValue1774 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1774) = mixedMoment B node1774 node1774Labels := rfl
  simpa [nodeValue1774, Sparse.eval] using hc.symm

theorem sound1782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1782 node1782Labels = Sparse.eval nodeValue1782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1782) = mixedMoment B node1782 node1782Labels := rfl
  simpa [nodeValue1782, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1838 node1838Labels = Sparse.eval nodeValue1838 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1838) = mixedMoment B node1838 node1838Labels := rfl
  simpa [nodeValue1838, Sparse.eval] using hc.symm

theorem sound1840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1840 node1840Labels = Sparse.eval nodeValue1840 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1840) = mixedMoment B node1840 node1840Labels := rfl
  simpa [nodeValue1840, Sparse.eval] using hc.symm

theorem sound1841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1841 node1841Labels = Sparse.eval nodeValue1841 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1841) = mixedMoment B node1841 node1841Labels := rfl
  simpa [nodeValue1841, Sparse.eval] using hc.symm

theorem sound1855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1855 node1855Labels = Sparse.eval nodeValue1855 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1855) = mixedMoment B node1855 node1855Labels := rfl
  simpa [nodeValue1855, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1863 node1863Labels = Sparse.eval nodeValue1863 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1863) = mixedMoment B node1863 node1863Labels := rfl
  simpa [nodeValue1863, Sparse.eval] using hc.symm

theorem sound1864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1864 node1864Labels = Sparse.eval nodeValue1864 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1864) = mixedMoment B node1864 node1864Labels := rfl
  simpa [nodeValue1864, Sparse.eval] using hc.symm

theorem sound1871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1871 node1871Labels = Sparse.eval nodeValue1871 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1871) = mixedMoment B node1871 node1871Labels := rfl
  simpa [nodeValue1871, Sparse.eval] using hc.symm

theorem sound1882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1882 node1882Labels = Sparse.eval nodeValue1882 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1882) = mixedMoment B node1882 node1882Labels := rfl
  simpa [nodeValue1882, Sparse.eval] using hc.symm

theorem sound1883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1883 node1883Labels = Sparse.eval nodeValue1883 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1883) = mixedMoment B node1883 node1883Labels := rfl
  simpa [nodeValue1883, Sparse.eval] using hc.symm

theorem sound1892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1892 node1892Labels = Sparse.eval nodeValue1892 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1892) = mixedMoment B node1892 node1892Labels := rfl
  simpa [nodeValue1892, Sparse.eval] using hc.symm

theorem sound1909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1909 node1909Labels = Sparse.eval nodeValue1909 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1909) = mixedMoment B node1909 node1909Labels := rfl
  simpa [nodeValue1909, Sparse.eval] using hc.symm

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

theorem sound2020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2020 node2020Labels = Sparse.eval nodeValue2020 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2020) = mixedMoment B node2020 node2020Labels := rfl
  simpa [nodeValue2020, Sparse.eval] using hc.symm

theorem sound2022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2022 node2022Labels = Sparse.eval nodeValue2022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2022) = mixedMoment B node2022 node2022Labels := rfl
  simpa [nodeValue2022, Sparse.eval] using hc.symm

theorem sound2029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2029 node2029Labels = Sparse.eval nodeValue2029 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2029) = mixedMoment B node2029 node2029Labels := rfl
  simpa [nodeValue2029, Sparse.eval] using hc.symm

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

theorem sound2051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2051 node2051Labels = Sparse.eval nodeValue2051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2051) = mixedMoment B node2051 node2051Labels := rfl
  simpa [nodeValue2051, Sparse.eval] using hc.symm

theorem sound2052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2052 node2052Labels = Sparse.eval nodeValue2052 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2052) = mixedMoment B node2052 node2052Labels := rfl
  simpa [nodeValue2052, Sparse.eval] using hc.symm

theorem sound2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2054 node2054Labels = Sparse.eval nodeValue2054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2054) = mixedMoment B node2054 node2054Labels := rfl
  simpa [nodeValue2054, Sparse.eval] using hc.symm

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

theorem sound2191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2191 node2191Labels = Sparse.eval nodeValue2191 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2191) = mixedMoment B node2191 node2191Labels := rfl
  simpa [nodeValue2191, Sparse.eval] using hc.symm

theorem sound2193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2193 node2193Labels = Sparse.eval nodeValue2193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2193) = mixedMoment B node2193 node2193Labels := rfl
  simpa [nodeValue2193, Sparse.eval] using hc.symm

theorem sound2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2202 node2202Labels = Sparse.eval nodeValue2202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2202) = mixedMoment B node2202 node2202Labels := rfl
  simpa [nodeValue2202, Sparse.eval] using hc.symm

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

theorem sound2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2206 node2206Labels = Sparse.eval nodeValue2206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2206) = mixedMoment B node2206 node2206Labels := rfl
  simpa [nodeValue2206, Sparse.eval] using hc.symm

theorem sound2225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2225 node2225Labels = Sparse.eval nodeValue2225 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2225) = mixedMoment B node2225 node2225Labels := rfl
  simpa [nodeValue2225, Sparse.eval] using hc.symm

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

theorem sound2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2262 node2262Labels = Sparse.eval nodeValue2262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2262) = mixedMoment B node2262 node2262Labels := rfl
  simpa [nodeValue2262, Sparse.eval] using hc.symm

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

theorem sound3767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3767 node3767Labels = Sparse.eval nodeValue3767 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3767) = mixedMoment B node3767 node3767Labels := rfl
  simpa [nodeValue3767, Sparse.eval] using hc.symm

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

theorem sound3794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3794 node3794Labels = Sparse.eval nodeValue3794 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3794) = mixedMoment B node3794 node3794Labels := rfl
  simpa [nodeValue3794, Sparse.eval] using hc.symm

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

theorem sound3845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3845 node3845Labels = Sparse.eval nodeValue3845 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3845) = mixedMoment B node3845 node3845Labels := rfl
  simpa [nodeValue3845, Sparse.eval] using hc.symm

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

theorem sound4210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4210 node4210Labels = Sparse.eval nodeValue4210 (mixedVector B) := by
  have h := singleton4210 B _hB
  rw [sound713 B _hB _hF, sound751 B _hB _hF] at h
  norm_num [nodeValue4210, nodeValue713, nodeValue751, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4212 node4212Labels = Sparse.eval nodeValue4212 (mixedVector B) := by
  have h := singleton4212 B _hB
  rw [sound715 B _hB _hF, sound753 B _hB _hF] at h
  norm_num [nodeValue4212, nodeValue715, nodeValue753, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4213 node4213Labels = Sparse.eval nodeValue4213 (mixedVector B) := by
  have h := singleton4213 B _hB
  rw [sound716 B _hB _hF, sound752 B _hB _hF] at h
  norm_num [nodeValue4213, nodeValue716, nodeValue752, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4224 node4224Labels = Sparse.eval nodeValue4224 (mixedVector B) := by
  have h := singleton4224 B _hB
  rw [sound725 B _hB _hF, sound771 B _hB _hF] at h
  norm_num [nodeValue4224, nodeValue725, nodeValue771, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4265 node4265Labels = Sparse.eval nodeValue4265 (mixedVector B) := by
  have h := singleton4265 B _hB
  rw [sound807 B _hB _hF] at h
  norm_num [nodeValue4265, nodeValue807, Sparse.eval] at h ⊢
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

theorem sound4642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4642 node4642Labels = Sparse.eval nodeValue4642 (mixedVector B) := by
  have h := singleton4642 B _hB
  rw [sound1771 B _hB _hF, sound1838 B _hB _hF] at h
  norm_num [nodeValue4642, nodeValue1771, nodeValue1838, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4644 node4644Labels = Sparse.eval nodeValue4644 (mixedVector B) := by
  have h := singleton4644 B _hB
  rw [sound1773 B _hB _hF, sound1841 B _hB _hF] at h
  norm_num [nodeValue4644, nodeValue1773, nodeValue1841, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4645 node4645Labels = Sparse.eval nodeValue4645 (mixedVector B) := by
  have h := singleton4645 B _hB
  rw [sound1774 B _hB _hF, sound1840 B _hB _hF] at h
  norm_num [nodeValue4645, nodeValue1774, nodeValue1840, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4654 node4654Labels = Sparse.eval nodeValue4654 (mixedVector B) := by
  have h := singleton4654 B _hB
  rw [sound1782 B _hB _hF, sound1855 B _hB _hF] at h
  norm_num [nodeValue4654, nodeValue1782, nodeValue1855, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4709 node4709Labels = Sparse.eval nodeValue4709 (mixedVector B) := by
  have h := singleton4709 B _hB
  rw [sound1863 B _hB _hF, sound1883 B _hB _hF] at h
  norm_num [nodeValue4709, nodeValue1863, nodeValue1883, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4710 node4710Labels = Sparse.eval nodeValue4710 (mixedVector B) := by
  have h := singleton4710 B _hB
  rw [sound1864 B _hB _hF, sound1882 B _hB _hF] at h
  norm_num [nodeValue4710, nodeValue1864, nodeValue1882, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4717 node4717Labels = Sparse.eval nodeValue4717 (mixedVector B) := by
  have h := singleton4717 B _hB
  rw [sound1871 B _hB _hF, sound1892 B _hB _hF] at h
  norm_num [nodeValue4717, nodeValue1871, nodeValue1892, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4737 node4737Labels = Sparse.eval nodeValue4737 (mixedVector B) := by
  have h := singleton4737 B _hB
  rw [sound1909 B _hB _hF] at h
  norm_num [nodeValue4737, nodeValue1909, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4802 node4802Labels = Sparse.eval nodeValue4802 (mixedVector B) := by
  have h := singleton4802 B _hB
  rw [sound2020 B _hB _hF, sound2202 B _hB _hF] at h
  norm_num [nodeValue4802, nodeValue2020, nodeValue2202, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4804 node4804Labels = Sparse.eval nodeValue4804 (mixedVector B) := by
  have h := singleton4804 B _hB
  rw [sound2022 B _hB _hF, sound2203 B _hB _hF] at h
  norm_num [nodeValue4804, nodeValue2022, nodeValue2203, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4811 node4811Labels = Sparse.eval nodeValue4811 (mixedVector B) := by
  have h := singleton4811 B _hB
  rw [sound2029 B _hB _hF, sound2225 B _hB _hF] at h
  norm_num [nodeValue4811, nodeValue2029, nodeValue2225, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4831 node4831Labels = Sparse.eval nodeValue4831 (mixedVector B) := by
  have h := singleton4831 B _hB
  rw [sound2051 B _hB _hF, sound2191 B _hB _hF] at h
  norm_num [nodeValue4831, nodeValue2051, nodeValue2191, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4832 node4832Labels = Sparse.eval nodeValue4832 (mixedVector B) := by
  have h := singleton4832 B _hB
  rw [sound2052 B _hB _hF, sound2193 B _hB _hF] at h
  norm_num [nodeValue4832, nodeValue2052, nodeValue2193, Sparse.eval] at h ⊢
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

theorem sound4888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4888 node4888Labels = Sparse.eval nodeValue4888 (mixedVector B) := by
  have h := singleton4888 B _hB
  rw [sound2244 B _hB _hF, sound2262 B _hB _hF] at h
  norm_num [nodeValue4888, nodeValue2244, nodeValue2262, Sparse.eval] at h ⊢
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

theorem sound5395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5395 node5395Labels = Sparse.eval nodeValue5395 (mixedVector B) := by
  have h := singleton5395 B _hB
  rw [sound3781 B _hB _hF, sound3794 B _hB _hF] at h
  norm_num [nodeValue5395, nodeValue3781, nodeValue3794, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5428 node5428Labels = Sparse.eval nodeValue5428 (mixedVector B) := by
  have h := singleton5428 B _hB
  rw [sound3845 B _hB _hF] at h
  norm_num [nodeValue5428, nodeValue3845, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources77
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2485 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2485 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2485 + difference 0 1) (sourceB2485 + difference 1 0) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2485 + difference 0 1) (sourceB2485 + difference 1 0) sourceC2485) = raw15071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw15071; decide +kernel
    rw [ha]
    exact (canonical15071 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2485 + difference 0 2) (sourceB2485 + difference 2 0) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA2485 + difference 0 2) (sourceB2485 + difference 2 0) sourceC2485) = raw15072 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw15072; decide +kernel
    rw [ha]
    exact (canonical15072 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2485 + difference 0 3) (sourceB2485 + difference 3 0) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2485 + difference 0 3) (sourceB2485 + difference 3 0) sourceC2485) = raw3426 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw3426; decide +kernel
    rw [ha]
    exact (canonical3426 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2485 + difference 0 4) (sourceB2485 + difference 4 0) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA2485 + difference 0 4) (sourceB2485 + difference 4 0) sourceC2485) = raw15073 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw15073; decide +kernel
    rw [ha]
    exact (canonical15073 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2485 + difference 0 5) (sourceB2485 + difference 5 0) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA2485 + difference 0 5) (sourceB2485 + difference 5 0) sourceC2485) = raw3416 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw3416; decide +kernel
    rw [ha]
    exact (canonical3416 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2485 + difference 1 0) (sourceB2485 + difference 0 1) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4265) := by
    have ha : (tripleCharges (sourceA2485 + difference 1 0) (sourceB2485 + difference 0 1) sourceC2485) = raw34243 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34243; decide +kernel
    rw [ha]
    exact (canonical34243 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2485 + difference 1 2) (sourceB2485 + difference 2 1) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4737) := by
    have ha : (tripleCharges (sourceA2485 + difference 1 2) (sourceB2485 + difference 2 1) sourceC2485) = raw34244 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34244; decide +kernel
    rw [ha]
    exact (canonical34244 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2485 + difference 1 3) (sourceB2485 + difference 3 1) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA2485 + difference 1 3) (sourceB2485 + difference 3 1) sourceC2485) = raw15062 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw15062; decide +kernel
    rw [ha]
    exact (canonical15062 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2485 + difference 1 4) (sourceB2485 + difference 4 1) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2485 + difference 1 4) (sourceB2485 + difference 4 1) sourceC2485) = raw34245 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34245; decide +kernel
    rw [ha]
    exact (canonical34245 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2485 + difference 1 5) (sourceB2485 + difference 5 1) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA2485 + difference 1 5) (sourceB2485 + difference 5 1) sourceC2485) = raw34246 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34246; decide +kernel
    rw [ha]
    exact (canonical34246 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2485 + difference 2 0) (sourceB2485 + difference 0 2) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4210) := by
    have ha : (tripleCharges (sourceA2485 + difference 2 0) (sourceB2485 + difference 0 2) sourceC2485) = raw34247 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34247; decide +kernel
    rw [ha]
    exact (canonical34247 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2485 + difference 2 1) (sourceB2485 + difference 1 2) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4642) := by
    have ha : (tripleCharges (sourceA2485 + difference 2 1) (sourceB2485 + difference 1 2) sourceC2485) = raw34248 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34248; decide +kernel
    rw [ha]
    exact (canonical34248 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2485 + difference 2 3) (sourceB2485 + difference 3 2) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2485 + difference 2 3) (sourceB2485 + difference 3 2) sourceC2485) = raw15066 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw15066; decide +kernel
    rw [ha]
    exact (canonical15066 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2485 + difference 2 4) (sourceB2485 + difference 4 2) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4787) := by
    have ha : (tripleCharges (sourceA2485 + difference 2 4) (sourceB2485 + difference 4 2) sourceC2485) = raw34249 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34249; decide +kernel
    rw [ha]
    exact (canonical34249 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2485 + difference 2 5) (sourceB2485 + difference 5 2) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA2485 + difference 2 5) (sourceB2485 + difference 5 2) sourceC2485) = raw34250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34250; decide +kernel
    rw [ha]
    exact (canonical34250 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2485 + difference 3 0) (sourceB2485 + difference 0 3) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4213) := by
    have ha : (tripleCharges (sourceA2485 + difference 3 0) (sourceB2485 + difference 0 3) sourceC2485) = raw34251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34251; decide +kernel
    rw [ha]
    exact (canonical34251 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2485 + difference 3 1) (sourceB2485 + difference 1 3) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4645) := by
    have ha : (tripleCharges (sourceA2485 + difference 3 1) (sourceB2485 + difference 1 3) sourceC2485) = raw34252 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34252; decide +kernel
    rw [ha]
    exact (canonical34252 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2485 + difference 3 2) (sourceB2485 + difference 2 3) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4710) := by
    have ha : (tripleCharges (sourceA2485 + difference 3 2) (sourceB2485 + difference 2 3) sourceC2485) = raw34253 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34253; decide +kernel
    rw [ha]
    exact (canonical34253 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2485 + difference 3 4) (sourceB2485 + difference 4 3) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA2485 + difference 3 4) (sourceB2485 + difference 4 3) sourceC2485) = raw34254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34254; decide +kernel
    rw [ha]
    exact (canonical34254 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2485 + difference 3 5) (sourceB2485 + difference 5 3) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2485 + difference 3 5) (sourceB2485 + difference 5 3) sourceC2485) = raw34255 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34255; decide +kernel
    rw [ha]
    exact (canonical34255 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2485 + difference 4 0) (sourceB2485 + difference 0 4) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4224) := by
    have ha : (tripleCharges (sourceA2485 + difference 4 0) (sourceB2485 + difference 0 4) sourceC2485) = raw34256 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34256; decide +kernel
    rw [ha]
    exact (canonical34256 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2485 + difference 4 1) (sourceB2485 + difference 1 4) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4654) := by
    have ha : (tripleCharges (sourceA2485 + difference 4 1) (sourceB2485 + difference 1 4) sourceC2485) = raw34257 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34257; decide +kernel
    rw [ha]
    exact (canonical34257 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2485 + difference 4 2) (sourceB2485 + difference 2 4) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4717) := by
    have ha : (tripleCharges (sourceA2485 + difference 4 2) (sourceB2485 + difference 2 4) sourceC2485) = raw34258 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34258; decide +kernel
    rw [ha]
    exact (canonical34258 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2485 + difference 4 3) (sourceB2485 + difference 3 4) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2485 + difference 4 3) (sourceB2485 + difference 3 4) sourceC2485) = raw15074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw15074; decide +kernel
    rw [ha]
    exact (canonical15074 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2485 + difference 4 5) (sourceB2485 + difference 5 4) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2485 + difference 4 5) (sourceB2485 + difference 5 4) sourceC2485) = raw34259 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34259; decide +kernel
    rw [ha]
    exact (canonical34259 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2485 + difference 5 0) (sourceB2485 + difference 0 5) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4212) := by
    have ha : (tripleCharges (sourceA2485 + difference 5 0) (sourceB2485 + difference 0 5) sourceC2485) = raw34260 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34260; decide +kernel
    rw [ha]
    exact (canonical34260 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2485 + difference 5 1) (sourceB2485 + difference 1 5) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4644) := by
    have ha : (tripleCharges (sourceA2485 + difference 5 1) (sourceB2485 + difference 1 5) sourceC2485) = raw34261 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34261; decide +kernel
    rw [ha]
    exact (canonical34261 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2485 + difference 5 2) (sourceB2485 + difference 2 5) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4709) := by
    have ha : (tripleCharges (sourceA2485 + difference 5 2) (sourceB2485 + difference 2 5) sourceC2485) = raw34262 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34262; decide +kernel
    rw [ha]
    exact (canonical34262 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2485 + difference 5 3) (sourceB2485 + difference 3 5) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2485 + difference 5 3) (sourceB2485 + difference 3 5) sourceC2485) = raw15078 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw15078; decide +kernel
    rw [ha]
    exact (canonical15078 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2485 + difference 5 4) (sourceB2485 + difference 4 5) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA2485 + difference 5 4) (sourceB2485 + difference 4 5) sourceC2485) = raw34263 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34263; decide +kernel
    rw [ha]
    exact (canonical34263 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2485 sourceB2485 sourceC2485
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2485, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic125
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2002 : Integer.Sparse.reindex keyMap MixedData.row2002 = numericRow2002 := by decide +kernel

theorem numericCheck2002 (x : Master → ℝ) : Integer.Sparse.eval numericRow2002 x =
    (17280 : ℝ) * reducedSource2002 x := by
  norm_num [numericRow2002, reducedSource2002, Integer.Sparse.eval, Sparse.eval, nodeValue4210, nodeValue4212, nodeValue4213, nodeValue4224, nodeValue4265, nodeValue4642, nodeValue4644, nodeValue4645, nodeValue4654, nodeValue4709, nodeValue4710, nodeValue4717, nodeValue4737, nodeValue4787, nodeValue4788, nodeValue4802, nodeValue4804, nodeValue4811, nodeValue4831, nodeValue4832, nodeValue4835, nodeValue4888, nodeValue5368, nodeValue5395, nodeValue5428, nodeValue5434, nodeValue5439]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows125
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2002 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2002 (mixedVector B) = 0 := by
  have h4210 : mixedVector B (Sum.inr 4210) = Sparse.eval nodeValue4210 (mixedVector B) := by
    change mixedMoment B node4210 node4210Labels = _
    exact sound4210 B hB hF
  have h4212 : mixedVector B (Sum.inr 4212) = Sparse.eval nodeValue4212 (mixedVector B) := by
    change mixedMoment B node4212 node4212Labels = _
    exact sound4212 B hB hF
  have h4213 : mixedVector B (Sum.inr 4213) = Sparse.eval nodeValue4213 (mixedVector B) := by
    change mixedMoment B node4213 node4213Labels = _
    exact sound4213 B hB hF
  have h4224 : mixedVector B (Sum.inr 4224) = Sparse.eval nodeValue4224 (mixedVector B) := by
    change mixedMoment B node4224 node4224Labels = _
    exact sound4224 B hB hF
  have h4265 : mixedVector B (Sum.inr 4265) = Sparse.eval nodeValue4265 (mixedVector B) := by
    change mixedMoment B node4265 node4265Labels = _
    exact sound4265 B hB hF
  have h4642 : mixedVector B (Sum.inr 4642) = Sparse.eval nodeValue4642 (mixedVector B) := by
    change mixedMoment B node4642 node4642Labels = _
    exact sound4642 B hB hF
  have h4644 : mixedVector B (Sum.inr 4644) = Sparse.eval nodeValue4644 (mixedVector B) := by
    change mixedMoment B node4644 node4644Labels = _
    exact sound4644 B hB hF
  have h4645 : mixedVector B (Sum.inr 4645) = Sparse.eval nodeValue4645 (mixedVector B) := by
    change mixedMoment B node4645 node4645Labels = _
    exact sound4645 B hB hF
  have h4654 : mixedVector B (Sum.inr 4654) = Sparse.eval nodeValue4654 (mixedVector B) := by
    change mixedMoment B node4654 node4654Labels = _
    exact sound4654 B hB hF
  have h4709 : mixedVector B (Sum.inr 4709) = Sparse.eval nodeValue4709 (mixedVector B) := by
    change mixedMoment B node4709 node4709Labels = _
    exact sound4709 B hB hF
  have h4710 : mixedVector B (Sum.inr 4710) = Sparse.eval nodeValue4710 (mixedVector B) := by
    change mixedMoment B node4710 node4710Labels = _
    exact sound4710 B hB hF
  have h4717 : mixedVector B (Sum.inr 4717) = Sparse.eval nodeValue4717 (mixedVector B) := by
    change mixedMoment B node4717 node4717Labels = _
    exact sound4717 B hB hF
  have h4737 : mixedVector B (Sum.inr 4737) = Sparse.eval nodeValue4737 (mixedVector B) := by
    change mixedMoment B node4737 node4737Labels = _
    exact sound4737 B hB hF
  have h4787 : mixedVector B (Sum.inr 4787) = Sparse.eval nodeValue4787 (mixedVector B) := by
    change mixedMoment B node4787 node4787Labels = _
    exact sound4787 B hB hF
  have h4788 : mixedVector B (Sum.inr 4788) = Sparse.eval nodeValue4788 (mixedVector B) := by
    change mixedMoment B node4788 node4788Labels = _
    exact sound4788 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4831 : mixedVector B (Sum.inr 4831) = Sparse.eval nodeValue4831 (mixedVector B) := by
    change mixedMoment B node4831 node4831Labels = _
    exact sound4831 B hB hF
  have h4832 : mixedVector B (Sum.inr 4832) = Sparse.eval nodeValue4832 (mixedVector B) := by
    change mixedMoment B node4832 node4832Labels = _
    exact sound4832 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4888 : mixedVector B (Sum.inr 4888) = Sparse.eval nodeValue4888 (mixedVector B) := by
    change mixedMoment B node4888 node4888Labels = _
    exact sound4888 B hB hF
  have h5368 : mixedVector B (Sum.inr 5368) = Sparse.eval nodeValue5368 (mixedVector B) := by
    change mixedMoment B node5368 node5368Labels = _
    exact sound5368 B hB hF
  have h5395 : mixedVector B (Sum.inr 5395) = Sparse.eval nodeValue5395 (mixedVector B) := by
    change mixedMoment B node5395 node5395Labels = _
    exact sound5395 B hB hF
  have h5428 : mixedVector B (Sum.inr 5428) = Sparse.eval nodeValue5428 (mixedVector B) := by
    change mixedMoment B node5428 node5428Labels = _
    exact sound5428 B hB hF
  have h5434 : mixedVector B (Sum.inr 5434) = Sparse.eval nodeValue5434 (mixedVector B) := by
    change mixedMoment B node5434 node5434Labels = _
    exact sound5434_e B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439_e B hB hF
  simpa only [sourceForm2485, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4210, h4212, h4213, h4224, h4265, h4642, h4644, h4645, h4654, h4709, h4710, h4717, h4737, h4787, h4788, h4802, h4804, h4811, h4831, h4832, h4835, h4888, h5368, h5395, h5428, h5434, h5439, reducedSource2002] using sourceEq2485 B hB

theorem rowSound2002_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2002 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2002, numericCheck2002, reducedZero2002 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002_e_oai
