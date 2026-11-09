-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1575_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:33:57.555467+00:00
-- url     : https://prove2.me/submissions/65117410-8cb2-46ac-8e2b-7d442d1f1f6b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound1299_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5292_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1311 raw1311Labels = mixedMoment B node4513 node4513Labels := by
  calc
    mixedMoment B raw1311 raw1311Labels = mixedMoment B raw1311step0 raw1311step0Labels := by
      have ha : raw1311step0 = (fun i j => raw1311 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1311step0 raw1311; decide +kernel
      have hl : raw1311step0Labels = raw1311Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1311 raw1311Labels permutation152 permutation4
    mixedMoment B raw1311step0 raw1311step0Labels = mixedMoment B raw1311step1 raw1311step1Labels := by
      have ha : raw1311step1 = raw1311step0 := by apply Matrix.ext; unfold raw1311step1 raw1311step0; decide +kernel
      have hl : raw1311step0Labels = labelEmbedding7 ∘ raw1311step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1311step0 raw1311step0Labels raw1311step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4513 node4513Labels := by rfl

theorem canonical1312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1312 raw1312Labels = mixedMoment B node1097 node1097Labels := by
  calc
    mixedMoment B raw1312 raw1312Labels = mixedMoment B raw1312step0 raw1312step0Labels := by
      have ha : raw1312step0 = (fun i j => raw1312 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1312step0 raw1312; decide +kernel
      have hl : raw1312step0Labels = raw1312Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1312 raw1312Labels permutation152 permutation4
    _ = mixedMoment B node1097 node1097Labels := by rfl

theorem canonical1313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1313 raw1313Labels = mixedMoment B node3232 node3232Labels := by
  calc
    mixedMoment B raw1313 raw1313Labels = mixedMoment B raw1313step0 raw1313step0Labels := by
      have ha : raw1313step0 = (fun i j => raw1313 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1313step0 raw1313; decide +kernel
      have hl : raw1313step0Labels = raw1313Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1313 raw1313Labels permutation152 permutation6
    mixedMoment B raw1313step0 raw1313step0Labels = mixedMoment B raw1313step1 raw1313step1Labels := by
      have ha : raw1313step1 = -raw1313step0 := by apply Matrix.ext; change ∀ i j, raw1313step1 i j = -(raw1313step0 i j); unfold raw1313step1 raw1313step0; decide +kernel
      have hl : raw1313step1Labels = raw1313step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1313step1 raw1313step1Labels = mixedMoment B raw1313step2 raw1313step2Labels := by
      have ha : raw1313step2 = raw1313step1 := by apply Matrix.ext; unfold raw1313step2 raw1313step1; decide +kernel
      have hl : raw1313step1Labels = labelEmbedding1 ∘ raw1313step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1313step1 raw1313step1Labels raw1313step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3232 node3232Labels := by rfl

theorem canonical1320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1320 raw1320Labels = mixedMoment B node4516 node4516Labels := by
  calc
    mixedMoment B raw1320 raw1320Labels = mixedMoment B raw1320step0 raw1320step0Labels := by
      have ha : raw1320step0 = (fun i j => raw1320 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1320step0 raw1320; decide +kernel
      have hl : raw1320step0Labels = raw1320Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1320 raw1320Labels permutation152 permutation4
    mixedMoment B raw1320step0 raw1320step0Labels = mixedMoment B raw1320step1 raw1320step1Labels := by
      have ha : raw1320step1 = raw1320step0 := by apply Matrix.ext; unfold raw1320step1 raw1320step0; decide +kernel
      have hl : raw1320step0Labels = labelEmbedding7 ∘ raw1320step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1320step0 raw1320step0Labels raw1320step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4516 node4516Labels := by rfl

theorem canonical1321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1321 raw1321Labels = mixedMoment B node1100 node1100Labels := by
  calc
    mixedMoment B raw1321 raw1321Labels = mixedMoment B raw1321step0 raw1321step0Labels := by
      have ha : raw1321step0 = (fun i j => raw1321 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1321step0 raw1321; decide +kernel
      have hl : raw1321step0Labels = raw1321Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1321 raw1321Labels permutation152 permutation4
    _ = mixedMoment B node1100 node1100Labels := by rfl

theorem canonical1322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1322 raw1322Labels = mixedMoment B node3234 node3234Labels := by
  calc
    mixedMoment B raw1322 raw1322Labels = mixedMoment B raw1322step0 raw1322step0Labels := by
      have ha : raw1322step0 = (fun i j => raw1322 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1322step0 raw1322; decide +kernel
      have hl : raw1322step0Labels = raw1322Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1322 raw1322Labels permutation152 permutation6
    mixedMoment B raw1322step0 raw1322step0Labels = mixedMoment B raw1322step1 raw1322step1Labels := by
      have ha : raw1322step1 = -raw1322step0 := by apply Matrix.ext; change ∀ i j, raw1322step1 i j = -(raw1322step0 i j); unfold raw1322step1 raw1322step0; decide +kernel
      have hl : raw1322step1Labels = raw1322step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1322step1 raw1322step1Labels = mixedMoment B raw1322step2 raw1322step2Labels := by
      have ha : raw1322step2 = raw1322step1 := by apply Matrix.ext; unfold raw1322step2 raw1322step1; decide +kernel
      have hl : raw1322step1Labels = labelEmbedding1 ∘ raw1322step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1322step1 raw1322step1Labels raw1322step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3234 node3234Labels := by rfl

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

theorem canonical1413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1413 raw1413Labels = mixedMoment B node4581 node4581Labels := by
  calc
    mixedMoment B raw1413 raw1413Labels = mixedMoment B raw1413step0 raw1413step0Labels := by
      have ha : raw1413step0 = (fun i j => raw1413 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1413step0 raw1413; decide +kernel
      have hl : raw1413step0Labels = raw1413Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1413 raw1413Labels permutation152 permutation4
    mixedMoment B raw1413step0 raw1413step0Labels = mixedMoment B raw1413step1 raw1413step1Labels := by
      have ha : raw1413step1 = raw1413step0 := by apply Matrix.ext; unfold raw1413step1 raw1413step0; decide +kernel
      have hl : raw1413step0Labels = labelEmbedding7 ∘ raw1413step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1413step0 raw1413step0Labels raw1413step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4581 node4581Labels := by rfl

theorem canonical1414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1414 raw1414Labels = mixedMoment B node1200 node1200Labels := by
  calc
    mixedMoment B raw1414 raw1414Labels = mixedMoment B raw1414step0 raw1414step0Labels := by
      have ha : raw1414step0 = (fun i j => raw1414 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1414step0 raw1414; decide +kernel
      have hl : raw1414step0Labels = raw1414Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1414 raw1414Labels permutation152 permutation4
    _ = mixedMoment B node1200 node1200Labels := by rfl

theorem canonical1415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1415 raw1415Labels = mixedMoment B node3281 node3281Labels := by
  calc
    mixedMoment B raw1415 raw1415Labels = mixedMoment B raw1415step0 raw1415step0Labels := by
      have ha : raw1415step0 = (fun i j => raw1415 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1415step0 raw1415; decide +kernel
      have hl : raw1415step0Labels = raw1415Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1415 raw1415Labels permutation152 permutation6
    mixedMoment B raw1415step0 raw1415step0Labels = mixedMoment B raw1415step1 raw1415step1Labels := by
      have ha : raw1415step1 = -raw1415step0 := by apply Matrix.ext; change ∀ i j, raw1415step1 i j = -(raw1415step0 i j); unfold raw1415step1 raw1415step0; decide +kernel
      have hl : raw1415step1Labels = raw1415step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1415step1 raw1415step1Labels = mixedMoment B raw1415step2 raw1415step2Labels := by
      have ha : raw1415step2 = raw1415step1 := by apply Matrix.ext; unfold raw1415step2 raw1415step1; decide +kernel
      have hl : raw1415step1Labels = labelEmbedding1 ∘ raw1415step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1415step1 raw1415step1Labels raw1415step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3281 node3281Labels := by rfl

theorem canonical1422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1422 raw1422Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw1422 raw1422Labels = mixedMoment B raw1422step0 raw1422step0Labels := by
      have ha : raw1422step0 = (fun i j => raw1422 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1422step0 raw1422; decide +kernel
      have hl : raw1422step0Labels = raw1422Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1422 raw1422Labels permutation152 permutation4
    mixedMoment B raw1422step0 raw1422step0Labels = mixedMoment B raw1422step1 raw1422step1Labels := by
      have ha : raw1422step1 = raw1422step0 := by apply Matrix.ext; unfold raw1422step1 raw1422step0; decide +kernel
      have hl : raw1422step0Labels = labelEmbedding7 ∘ raw1422step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1422step0 raw1422step0Labels raw1422step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

theorem canonical1423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1423 raw1423Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw1423 raw1423Labels = mixedMoment B raw1423step0 raw1423step0Labels := by
      have ha : raw1423step0 = (fun i j => raw1423 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1423step0 raw1423; decide +kernel
      have hl : raw1423step0Labels = raw1423Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1423 raw1423Labels permutation152 permutation4
    _ = mixedMoment B node1235 node1235Labels := by rfl

theorem canonical1424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1424 raw1424Labels = mixedMoment B node3292 node3292Labels := by
  calc
    mixedMoment B raw1424 raw1424Labels = mixedMoment B raw1424step0 raw1424step0Labels := by
      have ha : raw1424step0 = (fun i j => raw1424 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1424step0 raw1424; decide +kernel
      have hl : raw1424step0Labels = raw1424Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1424 raw1424Labels permutation152 permutation6
    mixedMoment B raw1424step0 raw1424step0Labels = mixedMoment B raw1424step1 raw1424step1Labels := by
      have ha : raw1424step1 = -raw1424step0 := by apply Matrix.ext; change ∀ i j, raw1424step1 i j = -(raw1424step0 i j); unfold raw1424step1 raw1424step0; decide +kernel
      have hl : raw1424step1Labels = raw1424step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1424step1 raw1424step1Labels = mixedMoment B raw1424step2 raw1424step2Labels := by
      have ha : raw1424step2 = raw1424step1 := by apply Matrix.ext; unfold raw1424step2 raw1424step1; decide +kernel
      have hl : raw1424step1Labels = labelEmbedding1 ∘ raw1424step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1424step1 raw1424step1Labels raw1424step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3292 node3292Labels := by rfl

theorem canonical1425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1425 raw1425Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw1425 raw1425Labels = mixedMoment B raw1425step0 raw1425step0Labels := by
      have ha : raw1425step0 = (fun i j => raw1425 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1425step0 raw1425; decide +kernel
      have hl : raw1425step0Labels = raw1425Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1425 raw1425Labels permutation32 permutation4
    mixedMoment B raw1425step0 raw1425step0Labels = mixedMoment B raw1425step1 raw1425step1Labels := by
      have ha : raw1425step1 = raw1425step0 := by apply Matrix.ext; unfold raw1425step1 raw1425step0; decide +kernel
      have hl : raw1425step0Labels = labelEmbedding7 ∘ raw1425step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1425step0 raw1425step0Labels raw1425step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical1426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1426 raw1426Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw1426 raw1426Labels = mixedMoment B raw1426step0 raw1426step0Labels := by
      have ha : raw1426step0 = (fun i j => raw1426 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1426step0 raw1426; decide +kernel
      have hl : raw1426step0Labels = raw1426Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1426 raw1426Labels permutation32 permutation4
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical1427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1427 raw1427Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw1427 raw1427Labels = mixedMoment B raw1427step0 raw1427step0Labels := by
      have ha : raw1427step0 = (fun i j => raw1427 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1427step0 raw1427; decide +kernel
      have hl : raw1427step0Labels = raw1427Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1427 raw1427Labels permutation32 permutation6
    mixedMoment B raw1427step0 raw1427step0Labels = mixedMoment B raw1427step1 raw1427step1Labels := by
      have ha : raw1427step1 = -raw1427step0 := by apply Matrix.ext; change ∀ i j, raw1427step1 i j = -(raw1427step0 i j); unfold raw1427step1 raw1427step0; decide +kernel
      have hl : raw1427step1Labels = raw1427step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1427step1 raw1427step1Labels = mixedMoment B raw1427step2 raw1427step2Labels := by
      have ha : raw1427step2 = raw1427step1 := by apply Matrix.ext; unfold raw1427step2 raw1427step1; decide +kernel
      have hl : raw1427step1Labels = labelEmbedding1 ∘ raw1427step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1427step1 raw1427step1Labels raw1427step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

theorem canonical1431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1431 raw1431Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw1431 raw1431Labels = mixedMoment B raw1431step0 raw1431step0Labels := by
      have ha : raw1431step0 = (fun i j => raw1431 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1431step0 raw1431; decide +kernel
      have hl : raw1431step0Labels = raw1431Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1431 raw1431Labels permutation32 permutation4
    mixedMoment B raw1431step0 raw1431step0Labels = mixedMoment B raw1431step1 raw1431step1Labels := by
      have ha : raw1431step1 = raw1431step0 := by apply Matrix.ext; unfold raw1431step1 raw1431step0; decide +kernel
      have hl : raw1431step0Labels = labelEmbedding7 ∘ raw1431step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1431step0 raw1431step0Labels raw1431step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

theorem canonical1432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1432 raw1432Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw1432 raw1432Labels = mixedMoment B raw1432step0 raw1432step0Labels := by
      have ha : raw1432step0 = (fun i j => raw1432 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1432step0 raw1432; decide +kernel
      have hl : raw1432step0Labels = raw1432Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1432 raw1432Labels permutation32 permutation4
    _ = mixedMoment B node1240 node1240Labels := by rfl

theorem canonical1433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1433 raw1433Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw1433 raw1433Labels = mixedMoment B raw1433step0 raw1433step0Labels := by
      have ha : raw1433step0 = (fun i j => raw1433 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1433step0 raw1433; decide +kernel
      have hl : raw1433step0Labels = raw1433Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1433 raw1433Labels permutation32 permutation6
    mixedMoment B raw1433step0 raw1433step0Labels = mixedMoment B raw1433step1 raw1433step1Labels := by
      have ha : raw1433step1 = -raw1433step0 := by apply Matrix.ext; change ∀ i j, raw1433step1 i j = -(raw1433step0 i j); unfold raw1433step1 raw1433step0; decide +kernel
      have hl : raw1433step1Labels = raw1433step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1433step1 raw1433step1Labels = mixedMoment B raw1433step2 raw1433step2Labels := by
      have ha : raw1433step2 = raw1433step1 := by apply Matrix.ext; unfold raw1433step2 raw1433step1; decide +kernel
      have hl : raw1433step1Labels = labelEmbedding1 ∘ raw1433step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1433step1 raw1433step1Labels raw1433step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

theorem canonical1449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1449 raw1449Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw1449 raw1449Labels = mixedMoment B raw1449step0 raw1449step0Labels := by
      have ha : raw1449step0 = (fun i j => raw1449 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1449step0 raw1449; decide +kernel
      have hl : raw1449step0Labels = raw1449Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1449 raw1449Labels permutation32 permutation4
    mixedMoment B raw1449step0 raw1449step0Labels = mixedMoment B raw1449step1 raw1449step1Labels := by
      have ha : raw1449step1 = raw1449step0 := by apply Matrix.ext; unfold raw1449step1 raw1449step0; decide +kernel
      have hl : raw1449step0Labels = labelEmbedding7 ∘ raw1449step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1449step0 raw1449step0Labels raw1449step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4622 node4622Labels := by rfl

theorem canonical1450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1450 raw1450Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw1450 raw1450Labels = mixedMoment B raw1450step0 raw1450step0Labels := by
      have ha : raw1450step0 = (fun i j => raw1450 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1450step0 raw1450; decide +kernel
      have hl : raw1450step0Labels = raw1450Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1450 raw1450Labels permutation32 permutation4
    _ = mixedMoment B node1299 node1299Labels := by rfl

theorem canonical1451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1451 raw1451Labels = mixedMoment B node3307 node3307Labels := by
  calc
    mixedMoment B raw1451 raw1451Labels = mixedMoment B raw1451step0 raw1451step0Labels := by
      have ha : raw1451step0 = (fun i j => raw1451 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1451step0 raw1451; decide +kernel
      have hl : raw1451step0Labels = raw1451Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1451 raw1451Labels permutation48 permutation3
    mixedMoment B raw1451step0 raw1451step0Labels = mixedMoment B raw1451step1 raw1451step1Labels := by
      have ha : raw1451step1 = -raw1451step0 := by apply Matrix.ext; change ∀ i j, raw1451step1 i j = -(raw1451step0 i j); unfold raw1451step1 raw1451step0; decide +kernel
      have hl : raw1451step1Labels = raw1451step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1451step1 raw1451step1Labels = mixedMoment B raw1451step2 raw1451step2Labels := by
      have ha : raw1451step2 = raw1451step1 := by apply Matrix.ext; unfold raw1451step2 raw1451step1; decide +kernel
      have hl : raw1451step1Labels = labelEmbedding1 ∘ raw1451step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1451step1 raw1451step1Labels raw1451step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3307 node3307Labels := by rfl

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

theorem canonical2226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2226 raw2226Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw2226 raw2226Labels = mixedMoment B raw2226step0 raw2226step0Labels := by
      have ha : raw2226step0 = (fun i j => raw2226 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2226step0 raw2226; decide +kernel
      have hl : raw2226step0Labels = raw2226Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2226 raw2226Labels permutation152 permutation5
    mixedMoment B raw2226step0 raw2226step0Labels = mixedMoment B raw2226step1 raw2226step1Labels := by
      have ha : raw2226step1 = raw2226step0 := by apply Matrix.ext; unfold raw2226step1 raw2226step0; decide +kernel
      have hl : raw2226step0Labels = labelEmbedding8 ∘ raw2226step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2226step0 raw2226step0Labels raw2226step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5202 node5202Labels := by rfl

theorem canonical2227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2227 raw2227Labels = mixedMoment B node2880 node2880Labels := by
  calc
    mixedMoment B raw2227 raw2227Labels = mixedMoment B raw2227step0 raw2227step0Labels := by
      have ha : raw2227step0 = (fun i j => raw2227 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2227step0 raw2227; decide +kernel
      have hl : raw2227step0Labels = raw2227Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2227 raw2227Labels permutation170 permutation4
    _ = mixedMoment B node2880 node2880Labels := by rfl

theorem canonical2228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2228 raw2228Labels = mixedMoment B node3617 node3617Labels := by
  calc
    mixedMoment B raw2228 raw2228Labels = mixedMoment B raw2228step0 raw2228step0Labels := by
      have ha : raw2228step0 = (fun i j => raw2228 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2228step0 raw2228; decide +kernel
      have hl : raw2228step0Labels = raw2228Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2228 raw2228Labels permutation184 permutation3
    mixedMoment B raw2228step0 raw2228step0Labels = mixedMoment B raw2228step1 raw2228step1Labels := by
      have ha : raw2228step1 = -raw2228step0 := by apply Matrix.ext; change ∀ i j, raw2228step1 i j = -(raw2228step0 i j); unfold raw2228step1 raw2228step0; decide +kernel
      have hl : raw2228step1Labels = raw2228step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2228step1 raw2228step1Labels = mixedMoment B raw2228step2 raw2228step2Labels := by
      have ha : raw2228step2 = raw2228step1 := by apply Matrix.ext; unfold raw2228step2 raw2228step1; decide +kernel
      have hl : raw2228step1Labels = labelEmbedding1 ∘ raw2228step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2228step1 raw2228step1Labels raw2228step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3617 node3617Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical209
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26792 raw26792Labels = mixedMoment B node5202 node5202Labels := by
  calc
    _ = mixedMoment B node5202 node5202Labels := by rfl

theorem canonical26793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26793 raw26793Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw26793 raw26793Labels = mixedMoment B raw26793step0 raw26793step0Labels := by
      have hz : ∀ j, raw26793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26793step0 = (fun i j => raw26793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26793step0 raw26793; decide +kernel
      have hl : raw26793step0Labels = raw26793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26793 raw26793Labels permutation346 hz
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical26794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26794 raw26794Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw26794 raw26794Labels = mixedMoment B raw26794step0 raw26794step0Labels := by
      have hz : ∀ j, raw26794 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26794step0 = (fun i j => raw26794 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26794step0 raw26794; decide +kernel
      have hl : raw26794step0Labels = raw26794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26794 raw26794Labels permutation434 hz
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical26795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26795 raw26795Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw26795 raw26795Labels = mixedMoment B raw26795step0 raw26795step0Labels := by
      have hz : ∀ j, raw26795 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26795step0 = (fun i j => raw26795 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26795step0 raw26795; decide +kernel
      have hl : raw26795step0Labels = raw26795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26795 raw26795Labels permutation520 hz
    _ = mixedMoment B node5292 node5292Labels := by rfl

theorem canonical26796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26796 raw26796Labels = mixedMoment B node5283 node5283Labels := by
  calc
    mixedMoment B raw26796 raw26796Labels = mixedMoment B raw26796step0 raw26796step0Labels := by
      have ha : raw26796step0 = (fun i j => raw26796 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26796step0 raw26796; decide +kernel
      have hl : raw26796step0Labels = raw26796Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26796 raw26796Labels permutation170 permutation2
    _ = mixedMoment B node5283 node5283Labels := by rfl

theorem canonical26797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26797 raw26797Labels = mixedMoment B node4171 node4171Labels := by
  calc
    mixedMoment B raw26797 raw26797Labels = mixedMoment B raw26797step0 raw26797step0Labels := by
      have ha : raw26797step0 = (fun i j => raw26797 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26797step0 raw26797; decide +kernel
      have hl : raw26797step0Labels = raw26797Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26797 raw26797Labels permutation170 permutation3
    mixedMoment B raw26797step0 raw26797step0Labels = mixedMoment B raw26797step1 raw26797step1Labels := by
      have ha : raw26797step1 = raw26797step0 := by apply Matrix.ext; unfold raw26797step1 raw26797step0; decide +kernel
      have hl : raw26797step0Labels = labelEmbedding6 ∘ raw26797step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26797step0 raw26797step0Labels raw26797step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4171 node4171Labels := by rfl

theorem canonical26798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26798 raw26798Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw26798 raw26798Labels = mixedMoment B raw26798step0 raw26798step0Labels := by
      have hz : ∀ j, raw26798 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26798step0 = (fun i j => raw26798 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26798step0 raw26798; decide +kernel
      have hl : raw26798step0Labels = raw26798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26798 raw26798Labels permutation346 hz
    mixedMoment B raw26798step0 raw26798step0Labels = mixedMoment B raw26798step1 raw26798step1Labels := by
      have ha : raw26798step1 = (fun i j => raw26798step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26798step1 raw26798step0; decide +kernel
      have hl : raw26798step1Labels = raw26798step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26798step0 raw26798step0Labels permutation40 permutation2
    _ = mixedMoment B node4622 node4622Labels := by rfl

theorem canonical26799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26799 raw26799Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw26799 raw26799Labels = mixedMoment B raw26799step0 raw26799step0Labels := by
      have hz : ∀ j, raw26799 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26799step0 = (fun i j => raw26799 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26799step0 raw26799; decide +kernel
      have hl : raw26799step0Labels = raw26799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26799 raw26799Labels permutation434 hz
    mixedMoment B raw26799step0 raw26799step0Labels = mixedMoment B raw26799step1 raw26799step1Labels := by
      have ha : raw26799step1 = (fun i j => raw26799step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26799step1 raw26799step0; decide +kernel
      have hl : raw26799step1Labels = raw26799step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26799step0 raw26799step0Labels permutation40 permutation2
    _ = mixedMoment B node4622 node4622Labels := by rfl

theorem canonical26800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26800 raw26800Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw26800 raw26800Labels = mixedMoment B raw26800step0 raw26800step0Labels := by
      have hz : ∀ j, raw26800 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26800step0 = (fun i j => raw26800 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26800step0 raw26800; decide +kernel
      have hl : raw26800step0Labels = raw26800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26800 raw26800Labels permutation520 hz
    mixedMoment B raw26800step0 raw26800step0Labels = mixedMoment B raw26800step1 raw26800step1Labels := by
      have ha : raw26800step1 = (fun i j => raw26800step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26800step1 raw26800step0; decide +kernel
      have hl : raw26800step1Labels = raw26800step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26800step0 raw26800step0Labels permutation40 permutation2
    _ = mixedMoment B node4622 node4622Labels := by rfl

theorem canonical26801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26801 raw26801Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw26801 raw26801Labels = mixedMoment B raw26801step0 raw26801step0Labels := by
      have ha : raw26801step0 = (fun i j => raw26801 (permutation246 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26801step0 raw26801; decide +kernel
      have hl : raw26801step0Labels = raw26801Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26801 raw26801Labels permutation246 permutation3
    mixedMoment B raw26801step0 raw26801step0Labels = mixedMoment B raw26801step1 raw26801step1Labels := by
      have ha : raw26801step1 = raw26801step0 := by apply Matrix.ext; unfold raw26801step1 raw26801step0; decide +kernel
      have hl : raw26801step0Labels = labelEmbedding6 ∘ raw26801step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26801step0 raw26801step0Labels raw26801step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

theorem canonical26802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26802 raw26802Labels = mixedMoment B node4139 node4139Labels := by
  calc
    mixedMoment B raw26802 raw26802Labels = mixedMoment B raw26802step0 raw26802step0Labels := by
      have ha : raw26802step0 = (fun i j => raw26802 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26802step0 raw26802; decide +kernel
      have hl : raw26802step0Labels = raw26802Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26802 raw26802Labels permutation173 permutation3
    mixedMoment B raw26802step0 raw26802step0Labels = mixedMoment B raw26802step1 raw26802step1Labels := by
      have ha : raw26802step1 = raw26802step0 := by apply Matrix.ext; unfold raw26802step1 raw26802step0; decide +kernel
      have hl : raw26802step0Labels = labelEmbedding6 ∘ raw26802step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26802step0 raw26802step0Labels raw26802step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4139 node4139Labels := by rfl

theorem canonical26803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26803 raw26803Labels = mixedMoment B node4513 node4513Labels := by
  calc
    mixedMoment B raw26803 raw26803Labels = mixedMoment B raw26803step0 raw26803step0Labels := by
      have ha : raw26803step0 = (fun i j => raw26803 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26803step0 raw26803; decide +kernel
      have hl : raw26803step0Labels = raw26803Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26803 raw26803Labels permutation173 permutation3
    mixedMoment B raw26803step0 raw26803step0Labels = mixedMoment B raw26803step1 raw26803step1Labels := by
      have ha : raw26803step1 = raw26803step0 := by apply Matrix.ext; unfold raw26803step1 raw26803step0; decide +kernel
      have hl : raw26803step0Labels = labelEmbedding6 ∘ raw26803step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26803step0 raw26803step0Labels raw26803step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4513 node4513Labels := by rfl

theorem canonical26804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26804 raw26804Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw26804 raw26804Labels = mixedMoment B raw26804step0 raw26804step0Labels := by
      have hz : ∀ j, raw26804 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26804step0 = (fun i j => raw26804 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26804step0 raw26804; decide +kernel
      have hl : raw26804step0Labels = raw26804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26804 raw26804Labels permutation434 hz
    mixedMoment B raw26804step0 raw26804step0Labels = mixedMoment B raw26804step1 raw26804step1Labels := by
      have ha : raw26804step1 = (fun i j => raw26804step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26804step1 raw26804step0; decide +kernel
      have hl : raw26804step1Labels = raw26804step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26804step0 raw26804step0Labels permutation37 permutation3
    mixedMoment B raw26804step1 raw26804step1Labels = mixedMoment B raw26804step2 raw26804step2Labels := by
      have ha : raw26804step2 = raw26804step1 := by apply Matrix.ext; unfold raw26804step2 raw26804step1; decide +kernel
      have hl : raw26804step1Labels = labelEmbedding6 ∘ raw26804step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26804step1 raw26804step1Labels raw26804step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical26805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26805 raw26805Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw26805 raw26805Labels = mixedMoment B raw26805step0 raw26805step0Labels := by
      have hz : ∀ j, raw26805 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26805step0 = (fun i j => raw26805 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26805step0 raw26805; decide +kernel
      have hl : raw26805step0Labels = raw26805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26805 raw26805Labels permutation520 hz
    mixedMoment B raw26805step0 raw26805step0Labels = mixedMoment B raw26805step1 raw26805step1Labels := by
      have ha : raw26805step1 = (fun i j => raw26805step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26805step1 raw26805step0; decide +kernel
      have hl : raw26805step1Labels = raw26805step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26805step0 raw26805step0Labels permutation37 permutation3
    mixedMoment B raw26805step1 raw26805step1Labels = mixedMoment B raw26805step2 raw26805step2Labels := by
      have ha : raw26805step2 = raw26805step1 := by apply Matrix.ext; unfold raw26805step2 raw26805step1; decide +kernel
      have hl : raw26805step1Labels = labelEmbedding6 ∘ raw26805step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26805step1 raw26805step1Labels raw26805step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical26806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26806 raw26806Labels = mixedMoment B node4581 node4581Labels := by
  calc
    mixedMoment B raw26806 raw26806Labels = mixedMoment B raw26806step0 raw26806step0Labels := by
      have ha : raw26806step0 = (fun i j => raw26806 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26806step0 raw26806; decide +kernel
      have hl : raw26806step0Labels = raw26806Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26806 raw26806Labels permutation173 permutation3
    mixedMoment B raw26806step0 raw26806step0Labels = mixedMoment B raw26806step1 raw26806step1Labels := by
      have ha : raw26806step1 = raw26806step0 := by apply Matrix.ext; unfold raw26806step1 raw26806step0; decide +kernel
      have hl : raw26806step0Labels = labelEmbedding6 ∘ raw26806step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26806step0 raw26806step0Labels raw26806step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4581 node4581Labels := by rfl

theorem canonical26807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26807 raw26807Labels = mixedMoment B node4139 node4139Labels := by
  calc
    mixedMoment B raw26807 raw26807Labels = mixedMoment B raw26807step0 raw26807step0Labels := by
      have ha : raw26807step0 = (fun i j => raw26807 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26807step0 raw26807; decide +kernel
      have hl : raw26807step0Labels = raw26807Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26807 raw26807Labels permutation171 permutation3
    mixedMoment B raw26807step0 raw26807step0Labels = mixedMoment B raw26807step1 raw26807step1Labels := by
      have ha : raw26807step1 = raw26807step0 := by apply Matrix.ext; unfold raw26807step1 raw26807step0; decide +kernel
      have hl : raw26807step0Labels = labelEmbedding6 ∘ raw26807step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26807step0 raw26807step0Labels raw26807step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4139 node4139Labels := by rfl

theorem canonical26808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26808 raw26808Labels = mixedMoment B node4513 node4513Labels := by
  calc
    mixedMoment B raw26808 raw26808Labels = mixedMoment B raw26808step0 raw26808step0Labels := by
      have ha : raw26808step0 = (fun i j => raw26808 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26808step0 raw26808; decide +kernel
      have hl : raw26808step0Labels = raw26808Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26808 raw26808Labels permutation171 permutation3
    mixedMoment B raw26808step0 raw26808step0Labels = mixedMoment B raw26808step1 raw26808step1Labels := by
      have ha : raw26808step1 = raw26808step0 := by apply Matrix.ext; unfold raw26808step1 raw26808step0; decide +kernel
      have hl : raw26808step0Labels = labelEmbedding6 ∘ raw26808step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26808step0 raw26808step0Labels raw26808step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4513 node4513Labels := by rfl

theorem canonical26809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26809 raw26809Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw26809 raw26809Labels = mixedMoment B raw26809step0 raw26809step0Labels := by
      have hz : ∀ j, raw26809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26809step0 = (fun i j => raw26809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26809step0 raw26809; decide +kernel
      have hl : raw26809step0Labels = raw26809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26809 raw26809Labels permutation346 hz
    mixedMoment B raw26809step0 raw26809step0Labels = mixedMoment B raw26809step1 raw26809step1Labels := by
      have ha : raw26809step1 = (fun i j => raw26809step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26809step1 raw26809step0; decide +kernel
      have hl : raw26809step1Labels = raw26809step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26809step0 raw26809step0Labels permutation37 permutation3
    mixedMoment B raw26809step1 raw26809step1Labels = mixedMoment B raw26809step2 raw26809step2Labels := by
      have ha : raw26809step2 = raw26809step1 := by apply Matrix.ext; unfold raw26809step2 raw26809step1; decide +kernel
      have hl : raw26809step1Labels = labelEmbedding6 ∘ raw26809step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26809step1 raw26809step1Labels raw26809step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical26810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26810 raw26810Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw26810 raw26810Labels = mixedMoment B raw26810step0 raw26810step0Labels := by
      have hz : ∀ j, raw26810 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26810step0 = (fun i j => raw26810 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26810step0 raw26810; decide +kernel
      have hl : raw26810step0Labels = raw26810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26810 raw26810Labels permutation520 hz
    mixedMoment B raw26810step0 raw26810step0Labels = mixedMoment B raw26810step1 raw26810step1Labels := by
      have ha : raw26810step1 = (fun i j => raw26810step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26810step1 raw26810step0; decide +kernel
      have hl : raw26810step1Labels = raw26810step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26810step0 raw26810step0Labels permutation36 permutation3
    mixedMoment B raw26810step1 raw26810step1Labels = mixedMoment B raw26810step2 raw26810step2Labels := by
      have ha : raw26810step2 = raw26810step1 := by apply Matrix.ext; unfold raw26810step2 raw26810step1; decide +kernel
      have hl : raw26810step1Labels = labelEmbedding6 ∘ raw26810step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26810step1 raw26810step1Labels raw26810step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical26811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26811 raw26811Labels = mixedMoment B node4581 node4581Labels := by
  calc
    mixedMoment B raw26811 raw26811Labels = mixedMoment B raw26811step0 raw26811step0Labels := by
      have ha : raw26811step0 = (fun i j => raw26811 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26811step0 raw26811; decide +kernel
      have hl : raw26811step0Labels = raw26811Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26811 raw26811Labels permutation171 permutation3
    mixedMoment B raw26811step0 raw26811step0Labels = mixedMoment B raw26811step1 raw26811step1Labels := by
      have ha : raw26811step1 = raw26811step0 := by apply Matrix.ext; unfold raw26811step1 raw26811step0; decide +kernel
      have hl : raw26811step0Labels = labelEmbedding6 ∘ raw26811step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26811step0 raw26811step0Labels raw26811step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4581 node4581Labels := by rfl

theorem canonical26812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26812 raw26812Labels = mixedMoment B node4139 node4139Labels := by
  calc
    mixedMoment B raw26812 raw26812Labels = mixedMoment B raw26812step0 raw26812step0Labels := by
      have ha : raw26812step0 = (fun i j => raw26812 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26812step0 raw26812; decide +kernel
      have hl : raw26812step0Labels = raw26812Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26812 raw26812Labels permutation170 permutation3
    mixedMoment B raw26812step0 raw26812step0Labels = mixedMoment B raw26812step1 raw26812step1Labels := by
      have ha : raw26812step1 = raw26812step0 := by apply Matrix.ext; unfold raw26812step1 raw26812step0; decide +kernel
      have hl : raw26812step0Labels = labelEmbedding6 ∘ raw26812step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26812step0 raw26812step0Labels raw26812step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4139 node4139Labels := by rfl

theorem canonical26813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26813 raw26813Labels = mixedMoment B node4513 node4513Labels := by
  calc
    mixedMoment B raw26813 raw26813Labels = mixedMoment B raw26813step0 raw26813step0Labels := by
      have ha : raw26813step0 = (fun i j => raw26813 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26813step0 raw26813; decide +kernel
      have hl : raw26813step0Labels = raw26813Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26813 raw26813Labels permutation170 permutation3
    mixedMoment B raw26813step0 raw26813step0Labels = mixedMoment B raw26813step1 raw26813step1Labels := by
      have ha : raw26813step1 = raw26813step0 := by apply Matrix.ext; unfold raw26813step1 raw26813step0; decide +kernel
      have hl : raw26813step0Labels = labelEmbedding6 ∘ raw26813step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26813step0 raw26813step0Labels raw26813step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4513 node4513Labels := by rfl

theorem canonical26814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26814 raw26814Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw26814 raw26814Labels = mixedMoment B raw26814step0 raw26814step0Labels := by
      have hz : ∀ j, raw26814 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26814step0 = (fun i j => raw26814 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26814step0 raw26814; decide +kernel
      have hl : raw26814step0Labels = raw26814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26814 raw26814Labels permutation346 hz
    mixedMoment B raw26814step0 raw26814step0Labels = mixedMoment B raw26814step1 raw26814step1Labels := by
      have ha : raw26814step1 = (fun i j => raw26814step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26814step1 raw26814step0; decide +kernel
      have hl : raw26814step1Labels = raw26814step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26814step0 raw26814step0Labels permutation36 permutation3
    mixedMoment B raw26814step1 raw26814step1Labels = mixedMoment B raw26814step2 raw26814step2Labels := by
      have ha : raw26814step2 = raw26814step1 := by apply Matrix.ext; unfold raw26814step2 raw26814step1; decide +kernel
      have hl : raw26814step1Labels = labelEmbedding6 ∘ raw26814step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26814step1 raw26814step1Labels raw26814step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical26815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26815 raw26815Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw26815 raw26815Labels = mixedMoment B raw26815step0 raw26815step0Labels := by
      have hz : ∀ j, raw26815 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26815step0 = (fun i j => raw26815 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26815step0 raw26815; decide +kernel
      have hl : raw26815step0Labels = raw26815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26815 raw26815Labels permutation434 hz
    mixedMoment B raw26815step0 raw26815step0Labels = mixedMoment B raw26815step1 raw26815step1Labels := by
      have ha : raw26815step1 = (fun i j => raw26815step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26815step1 raw26815step0; decide +kernel
      have hl : raw26815step1Labels = raw26815step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26815step0 raw26815step0Labels permutation36 permutation3
    mixedMoment B raw26815step1 raw26815step1Labels = mixedMoment B raw26815step2 raw26815step2Labels := by
      have ha : raw26815step2 = raw26815step1 := by apply Matrix.ext; unfold raw26815step2 raw26815step1; decide +kernel
      have hl : raw26815step1Labels = labelEmbedding6 ∘ raw26815step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26815step1 raw26815step1Labels raw26815step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

theorem canonical26816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26816 raw26816Labels = mixedMoment B node4581 node4581Labels := by
  calc
    mixedMoment B raw26816 raw26816Labels = mixedMoment B raw26816step0 raw26816step0Labels := by
      have ha : raw26816step0 = (fun i j => raw26816 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26816step0 raw26816; decide +kernel
      have hl : raw26816step0Labels = raw26816Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26816 raw26816Labels permutation170 permutation3
    mixedMoment B raw26816step0 raw26816step0Labels = mixedMoment B raw26816step1 raw26816step1Labels := by
      have ha : raw26816step1 = raw26816step0 := by apply Matrix.ext; unfold raw26816step1 raw26816step0; decide +kernel
      have hl : raw26816step0Labels = labelEmbedding6 ∘ raw26816step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26816step0 raw26816step0Labels raw26816step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4581 node4581Labels := by rfl

theorem canonical26817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26817 raw26817Labels = mixedMoment B node4143 node4143Labels := by
  calc
    mixedMoment B raw26817 raw26817Labels = mixedMoment B raw26817step0 raw26817step0Labels := by
      have ha : raw26817step0 = (fun i j => raw26817 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26817step0 raw26817; decide +kernel
      have hl : raw26817step0Labels = raw26817Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26817 raw26817Labels permutation152 permutation3
    mixedMoment B raw26817step0 raw26817step0Labels = mixedMoment B raw26817step1 raw26817step1Labels := by
      have ha : raw26817step1 = raw26817step0 := by apply Matrix.ext; unfold raw26817step1 raw26817step0; decide +kernel
      have hl : raw26817step0Labels = labelEmbedding6 ∘ raw26817step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26817step0 raw26817step0Labels raw26817step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4143 node4143Labels := by rfl

theorem canonical26818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26818 raw26818Labels = mixedMoment B node4516 node4516Labels := by
  calc
    mixedMoment B raw26818 raw26818Labels = mixedMoment B raw26818step0 raw26818step0Labels := by
      have ha : raw26818step0 = (fun i j => raw26818 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26818step0 raw26818; decide +kernel
      have hl : raw26818step0Labels = raw26818Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26818 raw26818Labels permutation152 permutation3
    mixedMoment B raw26818step0 raw26818step0Labels = mixedMoment B raw26818step1 raw26818step1Labels := by
      have ha : raw26818step1 = raw26818step0 := by apply Matrix.ext; unfold raw26818step1 raw26818step0; decide +kernel
      have hl : raw26818step0Labels = labelEmbedding6 ∘ raw26818step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26818step0 raw26818step0Labels raw26818step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4516 node4516Labels := by rfl

theorem canonical26819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26819 raw26819Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw26819 raw26819Labels = mixedMoment B raw26819step0 raw26819step0Labels := by
      have hz : ∀ j, raw26819 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26819step0 = (fun i j => raw26819 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26819step0 raw26819; decide +kernel
      have hl : raw26819step0Labels = raw26819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26819 raw26819Labels permutation346 hz
    mixedMoment B raw26819step0 raw26819step0Labels = mixedMoment B raw26819step1 raw26819step1Labels := by
      have ha : raw26819step1 = (fun i j => raw26819step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26819step1 raw26819step0; decide +kernel
      have hl : raw26819step1Labels = raw26819step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26819step0 raw26819step0Labels permutation32 permutation3
    mixedMoment B raw26819step1 raw26819step1Labels = mixedMoment B raw26819step2 raw26819step2Labels := by
      have ha : raw26819step2 = raw26819step1 := by apply Matrix.ext; unfold raw26819step2 raw26819step1; decide +kernel
      have hl : raw26819step1Labels = labelEmbedding6 ∘ raw26819step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26819step1 raw26819step1Labels raw26819step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

theorem canonical26820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26820 raw26820Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw26820 raw26820Labels = mixedMoment B raw26820step0 raw26820step0Labels := by
      have hz : ∀ j, raw26820 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw26820step0 = (fun i j => raw26820 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw26820step0 raw26820; decide +kernel
      have hl : raw26820step0Labels = raw26820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26820 raw26820Labels permutation434 hz
    mixedMoment B raw26820step0 raw26820step0Labels = mixedMoment B raw26820step1 raw26820step1Labels := by
      have ha : raw26820step1 = (fun i j => raw26820step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26820step1 raw26820step0; decide +kernel
      have hl : raw26820step1Labels = raw26820step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26820step0 raw26820step0Labels permutation32 permutation3
    mixedMoment B raw26820step1 raw26820step1Labels = mixedMoment B raw26820step2 raw26820step2Labels := by
      have ha : raw26820step2 = raw26820step1 := by apply Matrix.ext; unfold raw26820step2 raw26820step1; decide +kernel
      have hl : raw26820step1Labels = labelEmbedding6 ∘ raw26820step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26820step1 raw26820step1Labels raw26820step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

theorem canonical26821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26821 raw26821Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw26821 raw26821Labels = mixedMoment B raw26821step0 raw26821step0Labels := by
      have hz : ∀ j, raw26821 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26821step0 = (fun i j => raw26821 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26821step0 raw26821; decide +kernel
      have hl : raw26821step0Labels = raw26821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26821 raw26821Labels permutation520 hz
    mixedMoment B raw26821step0 raw26821step0Labels = mixedMoment B raw26821step1 raw26821step1Labels := by
      have ha : raw26821step1 = (fun i j => raw26821step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26821step1 raw26821step0; decide +kernel
      have hl : raw26821step1Labels = raw26821step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26821step0 raw26821step0Labels permutation32 permutation3
    mixedMoment B raw26821step1 raw26821step1Labels = mixedMoment B raw26821step2 raw26821step2Labels := by
      have ha : raw26821step2 = raw26821step1 := by apply Matrix.ext; unfold raw26821step2 raw26821step1; decide +kernel
      have hl : raw26821step1Labels = labelEmbedding6 ∘ raw26821step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26821step1 raw26821step1Labels raw26821step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw756 raw756Labels = mixedMoment B node4139 node4139Labels := by
  calc
    mixedMoment B raw756 raw756Labels = mixedMoment B raw756step0 raw756step0Labels := by
      have ha : raw756step0 = (fun i j => raw756 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw756step0 raw756; decide +kernel
      have hl : raw756step0Labels = raw756Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw756 raw756Labels permutation152 permutation4
    mixedMoment B raw756step0 raw756step0Labels = mixedMoment B raw756step1 raw756step1Labels := by
      have ha : raw756step1 = raw756step0 := by apply Matrix.ext; unfold raw756step1 raw756step0; decide +kernel
      have hl : raw756step0Labels = labelEmbedding7 ∘ raw756step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw756step0 raw756step0Labels raw756step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4139 node4139Labels := by rfl

theorem canonical757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw757 raw757Labels = mixedMoment B node567 node567Labels := by
  calc
    mixedMoment B raw757 raw757Labels = mixedMoment B raw757step0 raw757step0Labels := by
      have ha : raw757step0 = (fun i j => raw757 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw757step0 raw757; decide +kernel
      have hl : raw757step0Labels = raw757Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw757 raw757Labels permutation152 permutation4
    _ = mixedMoment B node567 node567Labels := by rfl

theorem canonical758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw758 raw758Labels = mixedMoment B node1488 node1488Labels := by
  calc
    mixedMoment B raw758 raw758Labels = mixedMoment B raw758step0 raw758step0Labels := by
      have ha : raw758step0 = (fun i j => raw758 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw758step0 raw758; decide +kernel
      have hl : raw758step0Labels = raw758Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw758 raw758Labels permutation152 permutation6
    mixedMoment B raw758step0 raw758step0Labels = mixedMoment B raw758step1 raw758step1Labels := by
      have ha : raw758step1 = -raw758step0 := by apply Matrix.ext; change ∀ i j, raw758step1 i j = -(raw758step0 i j); unfold raw758step1 raw758step0; decide +kernel
      have hl : raw758step1Labels = raw758step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw758step1 raw758step1Labels = mixedMoment B raw758step2 raw758step2Labels := by
      have ha : raw758step2 = raw758step1 := by apply Matrix.ext; unfold raw758step2 raw758step1; decide +kernel
      have hl : raw758step1Labels = labelEmbedding1 ∘ raw758step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw758step1 raw758step1Labels raw758step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1488 node1488Labels := by rfl

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

theorem canonical768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw768 raw768Labels = mixedMoment B node4143 node4143Labels := by
  calc
    mixedMoment B raw768 raw768Labels = mixedMoment B raw768step0 raw768step0Labels := by
      have ha : raw768step0 = (fun i j => raw768 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw768step0 raw768; decide +kernel
      have hl : raw768step0Labels = raw768Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw768 raw768Labels permutation152 permutation4
    mixedMoment B raw768step0 raw768step0Labels = mixedMoment B raw768step1 raw768step1Labels := by
      have ha : raw768step1 = raw768step0 := by apply Matrix.ext; unfold raw768step1 raw768step0; decide +kernel
      have hl : raw768step0Labels = labelEmbedding7 ∘ raw768step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw768step0 raw768step0Labels raw768step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4143 node4143Labels := by rfl

theorem canonical769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw769 raw769Labels = mixedMoment B node571 node571Labels := by
  calc
    mixedMoment B raw769 raw769Labels = mixedMoment B raw769step0 raw769step0Labels := by
      have ha : raw769step0 = (fun i j => raw769 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw769step0 raw769; decide +kernel
      have hl : raw769step0Labels = raw769Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw769 raw769Labels permutation152 permutation4
    _ = mixedMoment B node571 node571Labels := by rfl

theorem canonical770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw770 raw770Labels = mixedMoment B node1491 node1491Labels := by
  calc
    mixedMoment B raw770 raw770Labels = mixedMoment B raw770step0 raw770step0Labels := by
      have ha : raw770step0 = (fun i j => raw770 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw770step0 raw770; decide +kernel
      have hl : raw770step0Labels = raw770Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw770 raw770Labels permutation152 permutation6
    mixedMoment B raw770step0 raw770step0Labels = mixedMoment B raw770step1 raw770step1Labels := by
      have ha : raw770step1 = -raw770step0 := by apply Matrix.ext; change ∀ i j, raw770step1 i j = -(raw770step0 i j); unfold raw770step1 raw770step0; decide +kernel
      have hl : raw770step1Labels = raw770step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw770step1 raw770step1Labels = mixedMoment B raw770step2 raw770step2Labels := by
      have ha : raw770step2 = raw770step1 := by apply Matrix.ext; unfold raw770step2 raw770step1; decide +kernel
      have hl : raw770step1Labels = labelEmbedding1 ∘ raw770step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw770step1 raw770step1Labels raw770step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1491 node1491Labels := by rfl

theorem canonical801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw801 raw801Labels = mixedMoment B node4171 node4171Labels := by
  calc
    mixedMoment B raw801 raw801Labels = mixedMoment B raw801step0 raw801step0Labels := by
      have ha : raw801step0 = (fun i j => raw801 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw801step0 raw801; decide +kernel
      have hl : raw801step0Labels = raw801Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw801 raw801Labels permutation152 permutation4
    mixedMoment B raw801step0 raw801step0Labels = mixedMoment B raw801step1 raw801step1Labels := by
      have ha : raw801step1 = raw801step0 := by apply Matrix.ext; unfold raw801step1 raw801step0; decide +kernel
      have hl : raw801step0Labels = labelEmbedding7 ∘ raw801step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw801step0 raw801step0Labels raw801step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4171 node4171Labels := by rfl

theorem canonical802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw802 raw802Labels = mixedMoment B node599 node599Labels := by
  calc
    mixedMoment B raw802 raw802Labels = mixedMoment B raw802step0 raw802step0Labels := by
      have ha : raw802step0 = (fun i j => raw802 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw802step0 raw802; decide +kernel
      have hl : raw802step0Labels = raw802Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw802 raw802Labels permutation152 permutation4
    _ = mixedMoment B node599 node599Labels := by rfl

theorem canonical803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw803 raw803Labels = mixedMoment B node1506 node1506Labels := by
  calc
    mixedMoment B raw803 raw803Labels = mixedMoment B raw803step0 raw803step0Labels := by
      have ha : raw803step0 = (fun i j => raw803 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw803step0 raw803; decide +kernel
      have hl : raw803step0Labels = raw803Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw803 raw803Labels permutation152 permutation6
    mixedMoment B raw803step0 raw803step0Labels = mixedMoment B raw803step1 raw803step1Labels := by
      have ha : raw803step1 = -raw803step0 := by apply Matrix.ext; change ∀ i j, raw803step1 i j = -(raw803step0 i j); unfold raw803step1 raw803step0; decide +kernel
      have hl : raw803step1Labels = raw803step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw803step1 raw803step1Labels = mixedMoment B raw803step2 raw803step2Labels := by
      have ha : raw803step2 = raw803step1 := by apply Matrix.ext; unfold raw803step2 raw803step1; decide +kernel
      have hl : raw803step1Labels = labelEmbedding1 ∘ raw803step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw803step1 raw803step1Labels raw803step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1506 node1506Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4139 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4139 node4139Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node567 node567Labels + mixedMoment B node1488 node1488Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw756 singletonSmall4139
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4139) = raw756Labels := by decide +kernel
  rw [hl, canonical756 B hB] at h
  have hc0 : mixedMoment B raw756 (Fin.cases (0 : Fin 2) singletonSmall4139) =
      mixedMoment B node567 node567Labels := by
    have ha : raw756 = raw757 := by apply Matrix.ext; unfold raw756 raw757; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4139 = raw757Labels := by decide +kernel
    rw [ha, hj, canonical757 B hB]
  have hc1 : mixedMoment B raw756 (Fin.cases (1 : Fin 2) singletonSmall4139) =
      mixedMoment B node1488 node1488Labels := by
    have ha : raw756 = raw758 := by apply Matrix.ext; unfold raw756 raw758; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4139 = raw758Labels := by decide +kernel
    rw [ha, hj, canonical758 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4143 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4143 node4143Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node571 node571Labels + mixedMoment B node1491 node1491Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw768 singletonSmall4143
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4143) = raw768Labels := by decide +kernel
  rw [hl, canonical768 B hB] at h
  have hc0 : mixedMoment B raw768 (Fin.cases (0 : Fin 2) singletonSmall4143) =
      mixedMoment B node571 node571Labels := by
    have ha : raw768 = raw769 := by apply Matrix.ext; unfold raw768 raw769; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4143 = raw769Labels := by decide +kernel
    rw [ha, hj, canonical769 B hB]
  have hc1 : mixedMoment B raw768 (Fin.cases (1 : Fin 2) singletonSmall4143) =
      mixedMoment B node1491 node1491Labels := by
    have ha : raw768 = raw770 := by apply Matrix.ext; unfold raw768 raw770; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4143 = raw770Labels := by decide +kernel
    rw [ha, hj, canonical770 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4171 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4171 node4171Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node599 node599Labels + mixedMoment B node1506 node1506Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw801 singletonSmall4171
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4171) = raw801Labels := by decide +kernel
  rw [hl, canonical801 B hB] at h
  have hc0 : mixedMoment B raw801 (Fin.cases (0 : Fin 2) singletonSmall4171) =
      mixedMoment B node599 node599Labels := by
    have ha : raw801 = raw802 := by apply Matrix.ext; unfold raw801 raw802; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4171 = raw802Labels := by decide +kernel
    rw [ha, hj, canonical802 B hB]
  have hc1 : mixedMoment B raw801 (Fin.cases (1 : Fin 2) singletonSmall4171) =
      mixedMoment B node1506 node1506Labels := by
    have ha : raw801 = raw803 := by apply Matrix.ext; unfold raw801 raw803; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4171 = raw803Labels := by decide +kernel
    rw [ha, hj, canonical803 B hB]
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

theorem singleton4513 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4513 node4513Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1097 node1097Labels + mixedMoment B node3232 node3232Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1311 singletonSmall4513
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4513) = raw1311Labels := by decide +kernel
  rw [hl, canonical1311 B hB] at h
  have hc0 : mixedMoment B raw1311 (Fin.cases (0 : Fin 2) singletonSmall4513) =
      mixedMoment B node1097 node1097Labels := by
    have ha : raw1311 = raw1312 := by apply Matrix.ext; unfold raw1311 raw1312; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4513 = raw1312Labels := by decide +kernel
    rw [ha, hj, canonical1312 B hB]
  have hc1 : mixedMoment B raw1311 (Fin.cases (1 : Fin 2) singletonSmall4513) =
      mixedMoment B node3232 node3232Labels := by
    have ha : raw1311 = raw1313 := by apply Matrix.ext; unfold raw1311 raw1313; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4513 = raw1313Labels := by decide +kernel
    rw [ha, hj, canonical1313 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4516 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4516 node4516Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1100 node1100Labels + mixedMoment B node3234 node3234Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1320 singletonSmall4516
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4516) = raw1320Labels := by decide +kernel
  rw [hl, canonical1320 B hB] at h
  have hc0 : mixedMoment B raw1320 (Fin.cases (0 : Fin 2) singletonSmall4516) =
      mixedMoment B node1100 node1100Labels := by
    have ha : raw1320 = raw1321 := by apply Matrix.ext; unfold raw1320 raw1321; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4516 = raw1321Labels := by decide +kernel
    rw [ha, hj, canonical1321 B hB]
  have hc1 : mixedMoment B raw1320 (Fin.cases (1 : Fin 2) singletonSmall4516) =
      mixedMoment B node3234 node3234Labels := by
    have ha : raw1320 = raw1322 := by apply Matrix.ext; unfold raw1320 raw1322; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4516 = raw1322Labels := by decide +kernel
    rw [ha, hj, canonical1322 B hB]
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

theorem singleton4581 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4581 node4581Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1200 node1200Labels + mixedMoment B node3281 node3281Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1413 singletonSmall4581
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4581) = raw1413Labels := by decide +kernel
  rw [hl, canonical1413 B hB] at h
  have hc0 : mixedMoment B raw1413 (Fin.cases (0 : Fin 2) singletonSmall4581) =
      mixedMoment B node1200 node1200Labels := by
    have ha : raw1413 = raw1414 := by apply Matrix.ext; unfold raw1413 raw1414; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4581 = raw1414Labels := by decide +kernel
    rw [ha, hj, canonical1414 B hB]
  have hc1 : mixedMoment B raw1413 (Fin.cases (1 : Fin 2) singletonSmall4581) =
      mixedMoment B node3281 node3281Labels := by
    have ha : raw1413 = raw1415 := by apply Matrix.ext; unfold raw1413 raw1415; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4581 = raw1415Labels := by decide +kernel
    rw [ha, hj, canonical1415 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4601 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4601 node4601Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1235 node1235Labels + mixedMoment B node3292 node3292Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1422 singletonSmall4601
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4601) = raw1422Labels := by decide +kernel
  rw [hl, canonical1422 B hB] at h
  have hc0 : mixedMoment B raw1422 (Fin.cases (0 : Fin 2) singletonSmall4601) =
      mixedMoment B node1235 node1235Labels := by
    have ha : raw1422 = raw1423 := by apply Matrix.ext; unfold raw1422 raw1423; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4601 = raw1423Labels := by decide +kernel
    rw [ha, hj, canonical1423 B hB]
  have hc1 : mixedMoment B raw1422 (Fin.cases (1 : Fin 2) singletonSmall4601) =
      mixedMoment B node3292 node3292Labels := by
    have ha : raw1422 = raw1424 := by apply Matrix.ext; unfold raw1422 raw1424; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4601 = raw1424Labels := by decide +kernel
    rw [ha, hj, canonical1424 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4602 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4602 node4602Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1236 node1236Labels + mixedMoment B node3293 node3293Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1425 singletonSmall4602
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4602) = raw1425Labels := by decide +kernel
  rw [hl, canonical1425 B hB] at h
  have hc0 : mixedMoment B raw1425 (Fin.cases (0 : Fin 2) singletonSmall4602) =
      mixedMoment B node1236 node1236Labels := by
    have ha : raw1425 = raw1426 := by apply Matrix.ext; unfold raw1425 raw1426; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4602 = raw1426Labels := by decide +kernel
    rw [ha, hj, canonical1426 B hB]
  have hc1 : mixedMoment B raw1425 (Fin.cases (1 : Fin 2) singletonSmall4602) =
      mixedMoment B node3293 node3293Labels := by
    have ha : raw1425 = raw1427 := by apply Matrix.ext; unfold raw1425 raw1427; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4602 = raw1427Labels := by decide +kernel
    rw [ha, hj, canonical1427 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4606 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4606 node4606Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1240 node1240Labels + mixedMoment B node3299 node3299Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1431 singletonSmall4606
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4606) = raw1431Labels := by decide +kernel
  rw [hl, canonical1431 B hB] at h
  have hc0 : mixedMoment B raw1431 (Fin.cases (0 : Fin 2) singletonSmall4606) =
      mixedMoment B node1240 node1240Labels := by
    have ha : raw1431 = raw1432 := by apply Matrix.ext; unfold raw1431 raw1432; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4606 = raw1432Labels := by decide +kernel
    rw [ha, hj, canonical1432 B hB]
  have hc1 : mixedMoment B raw1431 (Fin.cases (1 : Fin 2) singletonSmall4606) =
      mixedMoment B node3299 node3299Labels := by
    have ha : raw1431 = raw1433 := by apply Matrix.ext; unfold raw1431 raw1433; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4606 = raw1433Labels := by decide +kernel
    rw [ha, hj, canonical1433 B hB]
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

theorem singleton4622 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4622 node4622Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1299 node1299Labels + mixedMoment B node3307 node3307Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1449 singletonSmall4622
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4622) = raw1449Labels := by decide +kernel
  rw [hl, canonical1449 B hB] at h
  have hc0 : mixedMoment B raw1449 (Fin.cases (0 : Fin 2) singletonSmall4622) =
      mixedMoment B node1299 node1299Labels := by
    have ha : raw1449 = raw1450 := by apply Matrix.ext; unfold raw1449 raw1450; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4622 = raw1450Labels := by decide +kernel
    rw [ha, hj, canonical1450 B hB]
  have hc1 : mixedMoment B raw1449 (Fin.cases (1 : Fin 2) singletonSmall4622) =
      mixedMoment B node3307 node3307Labels := by
    have ha : raw1449 = raw1451 := by apply Matrix.ext; unfold raw1449 raw1451; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4622 = raw1451Labels := by decide +kernel
    rw [ha, hj, canonical1451 B hB]
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

theorem singleton5202 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5202 node5202Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2880 node2880Labels + mixedMoment B node3617 node3617Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2226 singletonSmall5202
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5202) = raw2226Labels := by decide +kernel
  rw [hl, canonical2226 B hB] at h
  have hc0 : mixedMoment B raw2226 (Fin.cases (0 : Fin 2) singletonSmall5202) =
      mixedMoment B node2880 node2880Labels := by
    have ha : raw2226 = raw2227 := by apply Matrix.ext; unfold raw2226 raw2227; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5202 = raw2227Labels := by decide +kernel
    rw [ha, hj, canonical2227 B hB]
  have hc1 : mixedMoment B raw2226 (Fin.cases (1 : Fin 2) singletonSmall5202) =
      mixedMoment B node3617 node3617Labels := by
    have ha : raw2226 = raw2228 := by apply Matrix.ext; unfold raw2226 raw2228; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5202 = raw2228Labels := by decide +kernel
    rw [ha, hj, canonical2228 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound1097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1097 node1097Labels = Sparse.eval nodeValue1097 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1097) = mixedMoment B node1097 node1097Labels := rfl
  simpa [nodeValue1097, Sparse.eval] using hc.symm

theorem sound1100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1100 node1100Labels = Sparse.eval nodeValue1100 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1100) = mixedMoment B node1100 node1100Labels := rfl
  simpa [nodeValue1100, Sparse.eval] using hc.symm

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

theorem sound1200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1200 node1200Labels = Sparse.eval nodeValue1200 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1200) = mixedMoment B node1200 node1200Labels := rfl
  simpa [nodeValue1200, Sparse.eval] using hc.symm

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

theorem sound1235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1235 node1235Labels = Sparse.eval nodeValue1235 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1235) = mixedMoment B node1235 node1235Labels := rfl
  simpa [nodeValue1235, Sparse.eval] using hc.symm

theorem sound1236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1236 node1236Labels = Sparse.eval nodeValue1236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1236) = mixedMoment B node1236 node1236Labels := rfl
  simpa [nodeValue1236, Sparse.eval] using hc.symm

theorem sound1240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1240 node1240Labels = Sparse.eval nodeValue1240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1240) = mixedMoment B node1240 node1240Labels := rfl
  simpa [nodeValue1240, Sparse.eval] using hc.symm

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

theorem sound1488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1488 node1488Labels = Sparse.eval nodeValue1488 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1488) = mixedMoment B node1488 node1488Labels := rfl
  simpa [nodeValue1488, Sparse.eval] using hc.symm

theorem sound1491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1491 node1491Labels = Sparse.eval nodeValue1491 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1491) = mixedMoment B node1491 node1491Labels := rfl
  simpa [nodeValue1491, Sparse.eval] using hc.symm

theorem sound1506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1506 node1506Labels = Sparse.eval nodeValue1506 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1506) = mixedMoment B node1506 node1506Labels := rfl
  simpa [nodeValue1506, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3232 node3232Labels = Sparse.eval nodeValue3232 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3232) = mixedMoment B node3232 node3232Labels := rfl
  simpa [nodeValue3232, Sparse.eval] using hc.symm

theorem sound3234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3234 node3234Labels = Sparse.eval nodeValue3234 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3234) = mixedMoment B node3234 node3234Labels := rfl
  simpa [nodeValue3234, Sparse.eval] using hc.symm

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

theorem sound3281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3281 node3281Labels = Sparse.eval nodeValue3281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3281) = mixedMoment B node3281 node3281Labels := rfl
  simpa [nodeValue3281, Sparse.eval] using hc.symm

theorem sound3292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3292 node3292Labels = Sparse.eval nodeValue3292 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3292) = mixedMoment B node3292 node3292Labels := rfl
  simpa [nodeValue3292, Sparse.eval] using hc.symm

theorem sound3293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3293 node3293Labels = Sparse.eval nodeValue3293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3293) = mixedMoment B node3293 node3293Labels := rfl
  simpa [nodeValue3293, Sparse.eval] using hc.symm

theorem sound3299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3299 node3299Labels = Sparse.eval nodeValue3299 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3299) = mixedMoment B node3299 node3299Labels := rfl
  simpa [nodeValue3299, Sparse.eval] using hc.symm

theorem sound3307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3307 node3307Labels = Sparse.eval nodeValue3307 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3307) = mixedMoment B node3307 node3307Labels := rfl
  simpa [nodeValue3307, Sparse.eval] using hc.symm

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

theorem sound3617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3617 node3617Labels = Sparse.eval nodeValue3617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3617) = mixedMoment B node3617 node3617Labels := rfl
  simpa [nodeValue3617, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node567 node567Labels = Sparse.eval nodeValue567 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 567) = mixedMoment B node567 node567Labels := rfl
  simpa [nodeValue567, Sparse.eval] using hc.symm

theorem sound571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node571 node571Labels = Sparse.eval nodeValue571 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 571) = mixedMoment B node571 node571Labels := rfl
  simpa [nodeValue571, Sparse.eval] using hc.symm

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

theorem sound599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node599 node599Labels = Sparse.eval nodeValue599 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 599) = mixedMoment B node599 node599Labels := rfl
  simpa [nodeValue599, Sparse.eval] using hc.symm

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

theorem sound4139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4139 node4139Labels = Sparse.eval nodeValue4139 (mixedVector B) := by
  have h := singleton4139 B _hB
  rw [sound567 B _hB _hF, sound1488 B _hB _hF] at h
  norm_num [nodeValue4139, nodeValue567, nodeValue1488, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4143 node4143Labels = Sparse.eval nodeValue4143 (mixedVector B) := by
  have h := singleton4143 B _hB
  rw [sound571 B _hB _hF, sound1491 B _hB _hF] at h
  norm_num [nodeValue4143, nodeValue571, nodeValue1491, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4171 node4171Labels = Sparse.eval nodeValue4171 (mixedVector B) := by
  have h := singleton4171 B _hB
  rw [sound599 B _hB _hF, sound1506 B _hB _hF] at h
  norm_num [nodeValue4171, nodeValue599, nodeValue1506, Sparse.eval] at h ⊢
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

theorem sound4513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4513 node4513Labels = Sparse.eval nodeValue4513 (mixedVector B) := by
  have h := singleton4513 B _hB
  rw [sound1097 B _hB _hF, sound3232 B _hB _hF] at h
  norm_num [nodeValue4513, nodeValue1097, nodeValue3232, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4516 node4516Labels = Sparse.eval nodeValue4516 (mixedVector B) := by
  have h := singleton4516 B _hB
  rw [sound1100 B _hB _hF, sound3234 B _hB _hF] at h
  norm_num [nodeValue4516, nodeValue1100, nodeValue3234, Sparse.eval] at h ⊢
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

theorem sound4581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4581 node4581Labels = Sparse.eval nodeValue4581 (mixedVector B) := by
  have h := singleton4581 B _hB
  rw [sound1200 B _hB _hF, sound3281 B _hB _hF] at h
  norm_num [nodeValue4581, nodeValue1200, nodeValue3281, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4601 node4601Labels = Sparse.eval nodeValue4601 (mixedVector B) := by
  have h := singleton4601 B _hB
  rw [sound1235 B _hB _hF, sound3292 B _hB _hF] at h
  norm_num [nodeValue4601, nodeValue1235, nodeValue3292, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4602 node4602Labels = Sparse.eval nodeValue4602 (mixedVector B) := by
  have h := singleton4602 B _hB
  rw [sound1236 B _hB _hF, sound3293 B _hB _hF] at h
  norm_num [nodeValue4602, nodeValue1236, nodeValue3293, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4606 node4606Labels = Sparse.eval nodeValue4606 (mixedVector B) := by
  have h := singleton4606 B _hB
  rw [sound1240 B _hB _hF, sound3299 B _hB _hF] at h
  norm_num [nodeValue4606, nodeValue1240, nodeValue3299, Sparse.eval] at h ⊢
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

theorem sound4622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4622 node4622Labels = Sparse.eval nodeValue4622 (mixedVector B) := by
  have h := singleton4622 B _hB
  rw [sound1299_e B _hB _hF, sound3307 B _hB _hF] at h
  norm_num [nodeValue4622, nodeValue1299, nodeValue3307, Sparse.eval] at h ⊢
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

theorem sound5202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5202 node5202Labels = Sparse.eval nodeValue5202 (mixedVector B) := by
  have h := singleton5202 B _hB
  rw [sound2880 B _hB _hF, sound3617 B _hB _hF] at h
  norm_num [nodeValue5202, nodeValue2880, nodeValue3617, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem zero5283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5283 node5283Labels = 0 := by
  exact mixedMoment_alpha B hF node5283 node5283Labels 1 permutation152
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

theorem sound5283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5283 node5283Labels = Sparse.eval nodeValue5283 (mixedVector B) := by
  simpa only [nodeValue5283, Sparse.eval_nil] using zero5283 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources58
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1860 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1860 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1860 + difference 0 1) (sourceB1860 + difference 1 0) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5202) := by
    have ha : (tripleCharges (sourceA1860 + difference 0 1) (sourceB1860 + difference 1 0) sourceC1860) = raw26792 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26792; decide +kernel
    rw [ha]
    exact (canonical26792 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1860 + difference 0 2) (sourceB1860 + difference 2 0) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1860 + difference 0 2) (sourceB1860 + difference 2 0) sourceC1860) = raw26793 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26793; decide +kernel
    rw [ha]
    exact (canonical26793 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1860 + difference 0 3) (sourceB1860 + difference 3 0) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1860 + difference 0 3) (sourceB1860 + difference 3 0) sourceC1860) = raw26794 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26794; decide +kernel
    rw [ha]
    exact (canonical26794 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1860 + difference 0 4) (sourceB1860 + difference 4 0) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1860 + difference 0 4) (sourceB1860 + difference 4 0) sourceC1860) = raw26795 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26795; decide +kernel
    rw [ha]
    exact (canonical26795 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1860 + difference 0 5) (sourceB1860 + difference 5 0) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5283) := by
    have ha : (tripleCharges (sourceA1860 + difference 0 5) (sourceB1860 + difference 5 0) sourceC1860) = raw26796 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26796; decide +kernel
    rw [ha]
    exact (canonical26796 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1860 + difference 1 0) (sourceB1860 + difference 0 1) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4171) := by
    have ha : (tripleCharges (sourceA1860 + difference 1 0) (sourceB1860 + difference 0 1) sourceC1860) = raw26797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26797; decide +kernel
    rw [ha]
    exact (canonical26797 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1860 + difference 1 2) (sourceB1860 + difference 2 1) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1860 + difference 1 2) (sourceB1860 + difference 2 1) sourceC1860) = raw26798 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26798; decide +kernel
    rw [ha]
    exact (canonical26798 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1860 + difference 1 3) (sourceB1860 + difference 3 1) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1860 + difference 1 3) (sourceB1860 + difference 3 1) sourceC1860) = raw26799 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26799; decide +kernel
    rw [ha]
    exact (canonical26799 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1860 + difference 1 4) (sourceB1860 + difference 4 1) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1860 + difference 1 4) (sourceB1860 + difference 4 1) sourceC1860) = raw26800 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26800; decide +kernel
    rw [ha]
    exact (canonical26800 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1860 + difference 1 5) (sourceB1860 + difference 5 1) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1860 + difference 1 5) (sourceB1860 + difference 5 1) sourceC1860) = raw26801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26801; decide +kernel
    rw [ha]
    exact (canonical26801 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1860 + difference 2 0) (sourceB1860 + difference 0 2) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4139) := by
    have ha : (tripleCharges (sourceA1860 + difference 2 0) (sourceB1860 + difference 0 2) sourceC1860) = raw26802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26802; decide +kernel
    rw [ha]
    exact (canonical26802 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1860 + difference 2 1) (sourceB1860 + difference 1 2) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4513) := by
    have ha : (tripleCharges (sourceA1860 + difference 2 1) (sourceB1860 + difference 1 2) sourceC1860) = raw26803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26803; decide +kernel
    rw [ha]
    exact (canonical26803 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1860 + difference 2 3) (sourceB1860 + difference 3 2) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1860 + difference 2 3) (sourceB1860 + difference 3 2) sourceC1860) = raw26804 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26804; decide +kernel
    rw [ha]
    exact (canonical26804 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1860 + difference 2 4) (sourceB1860 + difference 4 2) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1860 + difference 2 4) (sourceB1860 + difference 4 2) sourceC1860) = raw26805 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26805; decide +kernel
    rw [ha]
    exact (canonical26805 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1860 + difference 2 5) (sourceB1860 + difference 5 2) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4581) := by
    have ha : (tripleCharges (sourceA1860 + difference 2 5) (sourceB1860 + difference 5 2) sourceC1860) = raw26806 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26806; decide +kernel
    rw [ha]
    exact (canonical26806 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1860 + difference 3 0) (sourceB1860 + difference 0 3) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4139) := by
    have ha : (tripleCharges (sourceA1860 + difference 3 0) (sourceB1860 + difference 0 3) sourceC1860) = raw26807 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26807; decide +kernel
    rw [ha]
    exact (canonical26807 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1860 + difference 3 1) (sourceB1860 + difference 1 3) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4513) := by
    have ha : (tripleCharges (sourceA1860 + difference 3 1) (sourceB1860 + difference 1 3) sourceC1860) = raw26808 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26808; decide +kernel
    rw [ha]
    exact (canonical26808 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1860 + difference 3 2) (sourceB1860 + difference 2 3) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1860 + difference 3 2) (sourceB1860 + difference 2 3) sourceC1860) = raw26809 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26809; decide +kernel
    rw [ha]
    exact (canonical26809 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1860 + difference 3 4) (sourceB1860 + difference 4 3) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1860 + difference 3 4) (sourceB1860 + difference 4 3) sourceC1860) = raw26810 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26810; decide +kernel
    rw [ha]
    exact (canonical26810 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1860 + difference 3 5) (sourceB1860 + difference 5 3) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4581) := by
    have ha : (tripleCharges (sourceA1860 + difference 3 5) (sourceB1860 + difference 5 3) sourceC1860) = raw26811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26811; decide +kernel
    rw [ha]
    exact (canonical26811 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1860 + difference 4 0) (sourceB1860 + difference 0 4) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4139) := by
    have ha : (tripleCharges (sourceA1860 + difference 4 0) (sourceB1860 + difference 0 4) sourceC1860) = raw26812 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26812; decide +kernel
    rw [ha]
    exact (canonical26812 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1860 + difference 4 1) (sourceB1860 + difference 1 4) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4513) := by
    have ha : (tripleCharges (sourceA1860 + difference 4 1) (sourceB1860 + difference 1 4) sourceC1860) = raw26813 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26813; decide +kernel
    rw [ha]
    exact (canonical26813 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1860 + difference 4 2) (sourceB1860 + difference 2 4) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1860 + difference 4 2) (sourceB1860 + difference 2 4) sourceC1860) = raw26814 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26814; decide +kernel
    rw [ha]
    exact (canonical26814 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1860 + difference 4 3) (sourceB1860 + difference 3 4) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1860 + difference 4 3) (sourceB1860 + difference 3 4) sourceC1860) = raw26815 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26815; decide +kernel
    rw [ha]
    exact (canonical26815 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1860 + difference 4 5) (sourceB1860 + difference 5 4) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4581) := by
    have ha : (tripleCharges (sourceA1860 + difference 4 5) (sourceB1860 + difference 5 4) sourceC1860) = raw26816 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26816; decide +kernel
    rw [ha]
    exact (canonical26816 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1860 + difference 5 0) (sourceB1860 + difference 0 5) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4143) := by
    have ha : (tripleCharges (sourceA1860 + difference 5 0) (sourceB1860 + difference 0 5) sourceC1860) = raw26817 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26817; decide +kernel
    rw [ha]
    exact (canonical26817 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1860 + difference 5 1) (sourceB1860 + difference 1 5) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4516) := by
    have ha : (tripleCharges (sourceA1860 + difference 5 1) (sourceB1860 + difference 1 5) sourceC1860) = raw26818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26818; decide +kernel
    rw [ha]
    exact (canonical26818 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1860 + difference 5 2) (sourceB1860 + difference 2 5) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1860 + difference 5 2) (sourceB1860 + difference 2 5) sourceC1860) = raw26819 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26819; decide +kernel
    rw [ha]
    exact (canonical26819 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1860 + difference 5 3) (sourceB1860 + difference 3 5) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1860 + difference 5 3) (sourceB1860 + difference 3 5) sourceC1860) = raw26820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26820; decide +kernel
    rw [ha]
    exact (canonical26820 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1860 + difference 5 4) (sourceB1860 + difference 4 5) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1860 + difference 5 4) (sourceB1860 + difference 4 5) sourceC1860) = raw26821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26821; decide +kernel
    rw [ha]
    exact (canonical26821 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1860 sourceB1860 sourceC1860
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1860, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1575 : Integer.Sparse.reindex keyMap MixedData.row1575 = numericRow1575 := by decide +kernel

theorem numericCheck1575 (x : Master → ℝ) : Integer.Sparse.eval numericRow1575 x =
    (5760 : ℝ) * reducedSource1575 x := by
  norm_num [numericRow1575, reducedSource1575, Integer.Sparse.eval, Sparse.eval, nodeValue4139, nodeValue4143, nodeValue4171, nodeValue4513, nodeValue4516, nodeValue4581, nodeValue4601, nodeValue4602, nodeValue4606, nodeValue4622, nodeValue5202, nodeValue5283, nodeValue5292]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows98
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1575 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1575 (mixedVector B) = 0 := by
  have h4139 : mixedVector B (Sum.inr 4139) = Sparse.eval nodeValue4139 (mixedVector B) := by
    change mixedMoment B node4139 node4139Labels = _
    exact sound4139 B hB hF
  have h4143 : mixedVector B (Sum.inr 4143) = Sparse.eval nodeValue4143 (mixedVector B) := by
    change mixedMoment B node4143 node4143Labels = _
    exact sound4143 B hB hF
  have h4171 : mixedVector B (Sum.inr 4171) = Sparse.eval nodeValue4171 (mixedVector B) := by
    change mixedMoment B node4171 node4171Labels = _
    exact sound4171 B hB hF
  have h4513 : mixedVector B (Sum.inr 4513) = Sparse.eval nodeValue4513 (mixedVector B) := by
    change mixedMoment B node4513 node4513Labels = _
    exact sound4513 B hB hF
  have h4516 : mixedVector B (Sum.inr 4516) = Sparse.eval nodeValue4516 (mixedVector B) := by
    change mixedMoment B node4516 node4516Labels = _
    exact sound4516 B hB hF
  have h4581 : mixedVector B (Sum.inr 4581) = Sparse.eval nodeValue4581 (mixedVector B) := by
    change mixedMoment B node4581 node4581Labels = _
    exact sound4581 B hB hF
  have h4601 : mixedVector B (Sum.inr 4601) = Sparse.eval nodeValue4601 (mixedVector B) := by
    change mixedMoment B node4601 node4601Labels = _
    exact sound4601 B hB hF
  have h4602 : mixedVector B (Sum.inr 4602) = Sparse.eval nodeValue4602 (mixedVector B) := by
    change mixedMoment B node4602 node4602Labels = _
    exact sound4602 B hB hF
  have h4606 : mixedVector B (Sum.inr 4606) = Sparse.eval nodeValue4606 (mixedVector B) := by
    change mixedMoment B node4606 node4606Labels = _
    exact sound4606 B hB hF
  have h4622 : mixedVector B (Sum.inr 4622) = Sparse.eval nodeValue4622 (mixedVector B) := by
    change mixedMoment B node4622 node4622Labels = _
    exact sound4622 B hB hF
  have h5202 : mixedVector B (Sum.inr 5202) = Sparse.eval nodeValue5202 (mixedVector B) := by
    change mixedMoment B node5202 node5202Labels = _
    exact sound5202 B hB hF
  have h5283 : mixedVector B (Sum.inr 5283) = Sparse.eval nodeValue5283 (mixedVector B) := by
    change mixedMoment B node5283 node5283Labels = _
    exact sound5283 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292_e B hB hF
  simpa only [sourceForm1860, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4139, h4143, h4171, h4513, h4516, h4581, h4601, h4602, h4606, h4622, h5202, h5283, h5292, reducedSource1575] using sourceEq1860 B hB

theorem rowSound1575_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1575 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1575, numericCheck1575, reducedZero1575 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1575_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1575_e_oai
