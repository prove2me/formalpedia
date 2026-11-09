-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:45:10.267193+00:00
-- url     : https://prove2.me/submissions/e2b544ac-fb8d-4b70-8ce3-36694cf0ae18

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E107
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170

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

theorem mixedMoment_zero_first_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (hA : ∀ i, A i 0 = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A i j.succ) (fun j => label j.succ) := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  unfold mixedIntegrand
  rw [Fin.prod_univ_succ]
  have hz : (fun i => A i 0) = 0 := funext hA
  rw [hz, rowFourier_zero, one_mul]

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

theorem delete_zero_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (σ : Equiv.Perm (Fin (n + 1))) (hz : ∀ i, A i (σ 0) = 0) :
    mixedMoment B A label =
      mixedMoment B (fun i j => A i (σ j.succ)) (fun j => label (σ j.succ)) := by
  rw [← mixedMoment_factor_permutation B A label σ]
  exact mixedMoment_zero_first_factor B _ _ hz

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

theorem canonical1512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1512 raw1512Labels = mixedMoment B node4648 node4648Labels := by
  calc
    mixedMoment B raw1512 raw1512Labels = mixedMoment B raw1512step0 raw1512step0Labels := by
      have ha : raw1512step0 = (fun i j => raw1512 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1512step0 raw1512; decide +kernel
      have hl : raw1512step0Labels = raw1512Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1512 raw1512Labels permutation152 permutation4
    mixedMoment B raw1512step0 raw1512step0Labels = mixedMoment B raw1512step1 raw1512step1Labels := by
      have ha : raw1512step1 = raw1512step0 := by apply Matrix.ext; unfold raw1512step1 raw1512step0; decide +kernel
      have hl : raw1512step0Labels = labelEmbedding7 ∘ raw1512step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1512step0 raw1512step0Labels raw1512step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4648 node4648Labels := by rfl

theorem canonical1513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1513 raw1513Labels = mixedMoment B node1776 node1776Labels := by
  calc
    mixedMoment B raw1513 raw1513Labels = mixedMoment B raw1513step0 raw1513step0Labels := by
      have ha : raw1513step0 = (fun i j => raw1513 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1513step0 raw1513; decide +kernel
      have hl : raw1513step0Labels = raw1513Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1513 raw1513Labels permutation152 permutation4
    _ = mixedMoment B node1776 node1776Labels := by rfl

theorem canonical1514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1514 raw1514Labels = mixedMoment B node1844 node1844Labels := by
  calc
    mixedMoment B raw1514 raw1514Labels = mixedMoment B raw1514step0 raw1514step0Labels := by
      have ha : raw1514step0 = (fun i j => raw1514 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1514step0 raw1514; decide +kernel
      have hl : raw1514step0Labels = raw1514Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1514 raw1514Labels permutation170 permutation6
    mixedMoment B raw1514step0 raw1514step0Labels = mixedMoment B raw1514step1 raw1514step1Labels := by
      have ha : raw1514step1 = -raw1514step0 := by apply Matrix.ext; change ∀ i j, raw1514step1 i j = -(raw1514step0 i j); unfold raw1514step1 raw1514step0; decide +kernel
      have hl : raw1514step1Labels = raw1514step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1514step1 raw1514step1Labels = mixedMoment B raw1514step2 raw1514step2Labels := by
      have ha : raw1514step2 = raw1514step1 := by apply Matrix.ext; unfold raw1514step2 raw1514step1; decide +kernel
      have hl : raw1514step1Labels = labelEmbedding1 ∘ raw1514step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1514step1 raw1514step1Labels raw1514step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1844 node1844Labels := by rfl

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

theorem canonical1656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1656 raw1656Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw1656 raw1656Labels = mixedMoment B raw1656step0 raw1656step0Labels := by
      have ha : raw1656step0 = (fun i j => raw1656 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1656step0 raw1656; decide +kernel
      have hl : raw1656step0Labels = raw1656Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1656 raw1656Labels permutation152 permutation4
    mixedMoment B raw1656step0 raw1656step0Labels = mixedMoment B raw1656step1 raw1656step1Labels := by
      have ha : raw1656step1 = raw1656step0 := by apply Matrix.ext; unfold raw1656step1 raw1656step0; decide +kernel
      have hl : raw1656step0Labels = labelEmbedding7 ∘ raw1656step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1656step0 raw1656step0Labels raw1656step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

theorem canonical1657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1657 raw1657Labels = mixedMoment B node1913 node1913Labels := by
  calc
    mixedMoment B raw1657 raw1657Labels = mixedMoment B raw1657step0 raw1657step0Labels := by
      have ha : raw1657step0 = (fun i j => raw1657 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1657step0 raw1657; decide +kernel
      have hl : raw1657step0Labels = raw1657Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1657 raw1657Labels permutation152 permutation4
    _ = mixedMoment B node1913 node1913Labels := by rfl

theorem canonical1658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1658 raw1658Labels = mixedMoment B node1922 node1922Labels := by
  calc
    mixedMoment B raw1658 raw1658Labels = mixedMoment B raw1658step0 raw1658step0Labels := by
      have ha : raw1658step0 = (fun i j => raw1658 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1658step0 raw1658; decide +kernel
      have hl : raw1658step0Labels = raw1658Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1658 raw1658Labels permutation170 permutation6
    mixedMoment B raw1658step0 raw1658step0Labels = mixedMoment B raw1658step1 raw1658step1Labels := by
      have ha : raw1658step1 = -raw1658step0 := by apply Matrix.ext; change ∀ i j, raw1658step1 i j = -(raw1658step0 i j); unfold raw1658step1 raw1658step0; decide +kernel
      have hl : raw1658step1Labels = raw1658step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1658step1 raw1658step1Labels = mixedMoment B raw1658step2 raw1658step2Labels := by
      have ha : raw1658step2 = raw1658step1 := by apply Matrix.ext; unfold raw1658step2 raw1658step1; decide +kernel
      have hl : raw1658step1Labels = labelEmbedding1 ∘ raw1658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1658step1 raw1658step1Labels raw1658step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1922 node1922Labels := by rfl

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

theorem canonical1665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1665 raw1665Labels = mixedMoment B node4746 node4746Labels := by
  calc
    mixedMoment B raw1665 raw1665Labels = mixedMoment B raw1665step0 raw1665step0Labels := by
      have ha : raw1665step0 = (fun i j => raw1665 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1665step0 raw1665; decide +kernel
      have hl : raw1665step0Labels = raw1665Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1665 raw1665Labels permutation152 permutation4
    mixedMoment B raw1665step0 raw1665step0Labels = mixedMoment B raw1665step1 raw1665step1Labels := by
      have ha : raw1665step1 = raw1665step0 := by apply Matrix.ext; unfold raw1665step1 raw1665step0; decide +kernel
      have hl : raw1665step0Labels = labelEmbedding7 ∘ raw1665step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1665step0 raw1665step0Labels raw1665step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4746 node4746Labels := by rfl

theorem canonical1666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1666 raw1666Labels = mixedMoment B node1925 node1925Labels := by
  calc
    mixedMoment B raw1666 raw1666Labels = mixedMoment B raw1666step0 raw1666step0Labels := by
      have ha : raw1666step0 = (fun i j => raw1666 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1666step0 raw1666; decide +kernel
      have hl : raw1666step0Labels = raw1666Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1666 raw1666Labels permutation152 permutation4
    _ = mixedMoment B node1925 node1925Labels := by rfl

theorem canonical1667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1667 raw1667Labels = mixedMoment B node1925 node1925Labels := by
  calc
    mixedMoment B raw1667 raw1667Labels = mixedMoment B raw1667step0 raw1667step0Labels := by
      have ha : raw1667step0 = (fun i j => raw1667 (permutation173 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1667step0 raw1667; decide +kernel
      have hl : raw1667step0Labels = raw1667Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1667 raw1667Labels permutation173 permutation6
    mixedMoment B raw1667step0 raw1667step0Labels = mixedMoment B raw1667step1 raw1667step1Labels := by
      have ha : raw1667step1 = -raw1667step0 := by apply Matrix.ext; change ∀ i j, raw1667step1 i j = -(raw1667step0 i j); unfold raw1667step1 raw1667step0; decide +kernel
      have hl : raw1667step1Labels = raw1667step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1667step1 raw1667step1Labels = mixedMoment B raw1667step2 raw1667step2Labels := by
      have ha : raw1667step2 = raw1667step1 := by apply Matrix.ext; unfold raw1667step2 raw1667step1; decide +kernel
      have hl : raw1667step1Labels = labelEmbedding1 ∘ raw1667step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1667step1 raw1667step1Labels raw1667step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1925 node1925Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2010 raw2010Labels = mixedMoment B node4998 node4998Labels := by
  calc
    mixedMoment B raw2010 raw2010Labels = mixedMoment B raw2010step0 raw2010step0Labels := by
      have ha : raw2010step0 = (fun i j => raw2010 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2010step0 raw2010; decide +kernel
      have hl : raw2010step0Labels = raw2010Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2010 raw2010Labels permutation152 permutation4
    mixedMoment B raw2010step0 raw2010step0Labels = mixedMoment B raw2010step1 raw2010step1Labels := by
      have ha : raw2010step1 = raw2010step0 := by apply Matrix.ext; unfold raw2010step1 raw2010step0; decide +kernel
      have hl : raw2010step0Labels = labelEmbedding7 ∘ raw2010step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2010step0 raw2010step0Labels raw2010step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4998 node4998Labels := by rfl

theorem canonical2011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2011 raw2011Labels = mixedMoment B node2383 node2383Labels := by
  calc
    mixedMoment B raw2011 raw2011Labels = mixedMoment B raw2011step0 raw2011step0Labels := by
      have ha : raw2011step0 = (fun i j => raw2011 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2011step0 raw2011; decide +kernel
      have hl : raw2011step0Labels = raw2011Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2011 raw2011Labels permutation152 permutation4
    _ = mixedMoment B node2383 node2383Labels := by rfl

theorem canonical2012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2012 raw2012Labels = mixedMoment B node3352 node3352Labels := by
  calc
    mixedMoment B raw2012 raw2012Labels = mixedMoment B raw2012step0 raw2012step0Labels := by
      have ha : raw2012step0 = (fun i j => raw2012 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2012step0 raw2012; decide +kernel
      have hl : raw2012step0Labels = raw2012Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2012 raw2012Labels permutation152 permutation6
    mixedMoment B raw2012step0 raw2012step0Labels = mixedMoment B raw2012step1 raw2012step1Labels := by
      have ha : raw2012step1 = -raw2012step0 := by apply Matrix.ext; change ∀ i j, raw2012step1 i j = -(raw2012step0 i j); unfold raw2012step1 raw2012step0; decide +kernel
      have hl : raw2012step1Labels = raw2012step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2012step1 raw2012step1Labels = mixedMoment B raw2012step2 raw2012step2Labels := by
      have ha : raw2012step2 = raw2012step1 := by apply Matrix.ext; unfold raw2012step2 raw2012step1; decide +kernel
      have hl : raw2012step1Labels = labelEmbedding1 ∘ raw2012step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2012step1 raw2012step1Labels raw2012step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3352 node3352Labels := by rfl

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

theorem canonical2094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2094 raw2094Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw2094 raw2094Labels = mixedMoment B raw2094step0 raw2094step0Labels := by
      have ha : raw2094step0 = (fun i j => raw2094 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2094step0 raw2094; decide +kernel
      have hl : raw2094step0Labels = raw2094Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2094 raw2094Labels permutation152 permutation4
    mixedMoment B raw2094step0 raw2094step0Labels = mixedMoment B raw2094step1 raw2094step1Labels := by
      have ha : raw2094step1 = raw2094step0 := by apply Matrix.ext; unfold raw2094step1 raw2094step0; decide +kernel
      have hl : raw2094step0Labels = labelEmbedding7 ∘ raw2094step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2094step0 raw2094step0Labels raw2094step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

theorem canonical2095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2095 raw2095Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw2095 raw2095Labels = mixedMoment B raw2095step0 raw2095step0Labels := by
      have ha : raw2095step0 = (fun i j => raw2095 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2095step0 raw2095; decide +kernel
      have hl : raw2095step0Labels = raw2095Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2095 raw2095Labels permutation152 permutation4
    _ = mixedMoment B node2480 node2480Labels := by rfl

theorem canonical2096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2096 raw2096Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw2096 raw2096Labels = mixedMoment B raw2096step0 raw2096step0Labels := by
      have ha : raw2096step0 = (fun i j => raw2096 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2096step0 raw2096; decide +kernel
      have hl : raw2096step0Labels = raw2096Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2096 raw2096Labels permutation158 permutation6
    mixedMoment B raw2096step0 raw2096step0Labels = mixedMoment B raw2096step1 raw2096step1Labels := by
      have ha : raw2096step1 = -raw2096step0 := by apply Matrix.ext; change ∀ i j, raw2096step1 i j = -(raw2096step0 i j); unfold raw2096step1 raw2096step0; decide +kernel
      have hl : raw2096step1Labels = raw2096step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2096step1 raw2096step1Labels = mixedMoment B raw2096step2 raw2096step2Labels := by
      have ha : raw2096step2 = raw2096step1 := by apply Matrix.ext; unfold raw2096step2 raw2096step1; decide +kernel
      have hl : raw2096step1Labels = labelEmbedding1 ∘ raw2096step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2096step1 raw2096step1Labels raw2096step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical251
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32235 raw32235Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw32235 raw32235Labels = mixedMoment B raw32235step0 raw32235step0Labels := by
      have ha : raw32235step0 = (fun i j => raw32235 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32235step0 raw32235; decide +kernel
      have hl : raw32235step0Labels = raw32235Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32235 raw32235Labels permutation152 permutation6
    mixedMoment B raw32235step0 raw32235step0Labels = mixedMoment B raw32235step1 raw32235step1Labels := by
      have ha : raw32235step1 = raw32235step0 := by apply Matrix.ext; unfold raw32235step1 raw32235step0; decide +kernel
      have hl : raw32235step0Labels = labelEmbedding9 ∘ raw32235step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32235step0 raw32235step0Labels raw32235step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

theorem canonical32236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32236 raw32236Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw32236 raw32236Labels = mixedMoment B raw32236step0 raw32236step0Labels := by
      have ha : raw32236step0 = (fun i j => raw32236 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32236step0 raw32236; decide +kernel
      have hl : raw32236step0Labels = raw32236Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32236 raw32236Labels permutation152 permutation6
    mixedMoment B raw32236step0 raw32236step0Labels = mixedMoment B raw32236step1 raw32236step1Labels := by
      have ha : raw32236step1 = raw32236step0 := by apply Matrix.ext; unfold raw32236step1 raw32236step0; decide +kernel
      have hl : raw32236step0Labels = labelEmbedding9 ∘ raw32236step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32236step0 raw32236step0Labels raw32236step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5076 node5076Labels := by rfl

theorem canonical32250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32250 raw32250Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw32250 raw32250Labels = mixedMoment B raw32250step0 raw32250step0Labels := by
      have hz : ∀ j, raw32250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32250step0 = (fun i j => raw32250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32250step0 raw32250; decide +kernel
      have hl : raw32250step0Labels = raw32250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32250 raw32250Labels permutation346 hz
    mixedMoment B raw32250step0 raw32250step0Labels = mixedMoment B raw32250step1 raw32250step1Labels := by
      have ha : raw32250step1 = (fun i j => raw32250step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32250step1 raw32250step0; decide +kernel
      have hl : raw32250step1Labels = raw32250step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32250step0 raw32250step0Labels permutation32 permutation6
    mixedMoment B raw32250step1 raw32250step1Labels = mixedMoment B raw32250step2 raw32250step2Labels := by
      have ha : raw32250step2 = raw32250step1 := by apply Matrix.ext; unfold raw32250step2 raw32250step1; decide +kernel
      have hl : raw32250step1Labels = labelEmbedding9 ∘ raw32250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32250step1 raw32250step1Labels raw32250step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4838 node4838Labels := by rfl

theorem canonical32251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32251 raw32251Labels = mixedMoment B node5104 node5104Labels := by
  calc
    mixedMoment B raw32251 raw32251Labels = mixedMoment B raw32251step0 raw32251step0Labels := by
      have hz : ∀ j, raw32251 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32251step0 = (fun i j => raw32251 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32251step0 raw32251; decide +kernel
      have hl : raw32251step0Labels = raw32251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32251 raw32251Labels permutation346 hz
    mixedMoment B raw32251step0 raw32251step0Labels = mixedMoment B raw32251step1 raw32251step1Labels := by
      have ha : raw32251step1 = (fun i j => raw32251step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32251step1 raw32251step0; decide +kernel
      have hl : raw32251step1Labels = raw32251step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32251step0 raw32251step0Labels permutation32 permutation6
    mixedMoment B raw32251step1 raw32251step1Labels = mixedMoment B raw32251step2 raw32251step2Labels := by
      have ha : raw32251step2 = raw32251step1 := by apply Matrix.ext; unfold raw32251step2 raw32251step1; decide +kernel
      have hl : raw32251step1Labels = labelEmbedding9 ∘ raw32251step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32251step1 raw32251step1Labels raw32251step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5104 node5104Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical252
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32327 raw32327Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw32327 raw32327Labels = mixedMoment B raw32327step0 raw32327step0Labels := by
      have ha : raw32327step0 = (fun i j => raw32327 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32327step0 raw32327; decide +kernel
      have hl : raw32327step0Labels = raw32327Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32327 raw32327Labels permutation154 permutation6
    mixedMoment B raw32327step0 raw32327step0Labels = mixedMoment B raw32327step1 raw32327step1Labels := by
      have ha : raw32327step1 = raw32327step0 := by apply Matrix.ext; unfold raw32327step1 raw32327step0; decide +kernel
      have hl : raw32327step0Labels = labelEmbedding9 ∘ raw32327step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32327step0 raw32327step0Labels raw32327step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical32328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32328 raw32328Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw32328 raw32328Labels = mixedMoment B raw32328step0 raw32328step0Labels := by
      have ha : raw32328step0 = (fun i j => raw32328 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32328step0 raw32328; decide +kernel
      have hl : raw32328step0Labels = raw32328Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32328 raw32328Labels permutation154 permutation6
    mixedMoment B raw32328step0 raw32328step0Labels = mixedMoment B raw32328step1 raw32328step1Labels := by
      have ha : raw32328step1 = raw32328step0 := by apply Matrix.ext; unfold raw32328step1 raw32328step0; decide +kernel
      have hl : raw32328step0Labels = labelEmbedding9 ∘ raw32328step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32328step0 raw32328step0Labels raw32328step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

theorem canonical32330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32330 raw32330Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw32330 raw32330Labels = mixedMoment B raw32330step0 raw32330step0Labels := by
      have ha : raw32330step0 = (fun i j => raw32330 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32330step0 raw32330; decide +kernel
      have hl : raw32330step0Labels = raw32330Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32330 raw32330Labels permutation152 permutation6
    mixedMoment B raw32330step0 raw32330step0Labels = mixedMoment B raw32330step1 raw32330step1Labels := by
      have ha : raw32330step1 = raw32330step0 := by apply Matrix.ext; unfold raw32330step1 raw32330step0; decide +kernel
      have hl : raw32330step0Labels = labelEmbedding9 ∘ raw32330step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32330step0 raw32330step0Labels raw32330step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical32331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32331 raw32331Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw32331 raw32331Labels = mixedMoment B raw32331step0 raw32331step0Labels := by
      have ha : raw32331step0 = (fun i j => raw32331 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32331step0 raw32331; decide +kernel
      have hl : raw32331step0Labels = raw32331Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32331 raw32331Labels permutation152 permutation6
    mixedMoment B raw32331step0 raw32331step0Labels = mixedMoment B raw32331step1 raw32331step1Labels := by
      have ha : raw32331step1 = raw32331step0 := by apply Matrix.ext; unfold raw32331step1 raw32331step0; decide +kernel
      have hl : raw32331step0Labels = labelEmbedding9 ∘ raw32331step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32331step0 raw32331step0Labels raw32331step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical258
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33136 raw33136Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw33136 raw33136Labels = mixedMoment B raw33136step0 raw33136step0Labels := by
      have ha : raw33136step0 = (fun i j => raw33136 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33136step0 raw33136; decide +kernel
      have hl : raw33136step0Labels = raw33136Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33136 raw33136Labels permutation167 permutation4
    mixedMoment B raw33136step0 raw33136step0Labels = mixedMoment B raw33136step1 raw33136step1Labels := by
      have ha : raw33136step1 = -raw33136step0 := by apply Matrix.ext; change ∀ i j, raw33136step1 i j = -(raw33136step0 i j); unfold raw33136step1 raw33136step0; decide +kernel
      have hl : raw33136step1Labels = raw33136step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33136step1 raw33136step1Labels = mixedMoment B raw33136step2 raw33136step2Labels := by
      have ha : raw33136step2 = raw33136step1 := by apply Matrix.ext; unfold raw33136step2 raw33136step1; decide +kernel
      have hl : raw33136step1Labels = labelEmbedding7 ∘ raw33136step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33136step1 raw33136step1Labels raw33136step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

theorem canonical33140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33140 raw33140Labels = mixedMoment B node4737 node4737Labels := by
  calc
    mixedMoment B raw33140 raw33140Labels = mixedMoment B raw33140step0 raw33140step0Labels := by
      have ha : raw33140step0 = (fun i j => raw33140 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33140step0 raw33140; decide +kernel
      have hl : raw33140step0Labels = raw33140Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33140 raw33140Labels permutation165 permutation4
    mixedMoment B raw33140step0 raw33140step0Labels = mixedMoment B raw33140step1 raw33140step1Labels := by
      have ha : raw33140step1 = -raw33140step0 := by apply Matrix.ext; change ∀ i j, raw33140step1 i j = -(raw33140step0 i j); unfold raw33140step1 raw33140step0; decide +kernel
      have hl : raw33140step1Labels = raw33140step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33140step1 raw33140step1Labels = mixedMoment B raw33140step2 raw33140step2Labels := by
      have ha : raw33140step2 = raw33140step1 := by apply Matrix.ext; unfold raw33140step2 raw33140step1; decide +kernel
      have hl : raw33140step1Labels = labelEmbedding7 ∘ raw33140step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33140step1 raw33140step1Labels raw33140step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4737 node4737Labels := by rfl

theorem canonical33146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33146 raw33146Labels = mixedMoment B node4998 node4998Labels := by
  calc
    mixedMoment B raw33146 raw33146Labels = mixedMoment B raw33146step0 raw33146step0Labels := by
      have ha : raw33146step0 = (fun i j => raw33146 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33146step0 raw33146; decide +kernel
      have hl : raw33146step0Labels = raw33146Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33146 raw33146Labels permutation152 permutation6
    mixedMoment B raw33146step0 raw33146step0Labels = mixedMoment B raw33146step1 raw33146step1Labels := by
      have ha : raw33146step1 = raw33146step0 := by apply Matrix.ext; unfold raw33146step1 raw33146step0; decide +kernel
      have hl : raw33146step0Labels = labelEmbedding9 ∘ raw33146step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33146step0 raw33146step0Labels raw33146step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4998 node4998Labels := by rfl

theorem canonical33147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33147 raw33147Labels = mixedMoment B node4736 node4736Labels := by
  calc
    mixedMoment B raw33147 raw33147Labels = mixedMoment B raw33147step0 raw33147step0Labels := by
      have ha : raw33147step0 = (fun i j => raw33147 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33147step0 raw33147; decide +kernel
      have hl : raw33147step0Labels = raw33147Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33147 raw33147Labels permutation164 permutation4
    mixedMoment B raw33147step0 raw33147step0Labels = mixedMoment B raw33147step1 raw33147step1Labels := by
      have ha : raw33147step1 = -raw33147step0 := by apply Matrix.ext; change ∀ i j, raw33147step1 i j = -(raw33147step0 i j); unfold raw33147step1 raw33147step0; decide +kernel
      have hl : raw33147step1Labels = raw33147step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33147step1 raw33147step1Labels = mixedMoment B raw33147step2 raw33147step2Labels := by
      have ha : raw33147step2 = raw33147step1 := by apply Matrix.ext; unfold raw33147step2 raw33147step1; decide +kernel
      have hl : raw33147step1Labels = labelEmbedding7 ∘ raw33147step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33147step1 raw33147step1Labels raw33147step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4736 node4736Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical259
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33237 raw33237Labels = mixedMoment B node4736 node4736Labels := by
  calc
    mixedMoment B raw33237 raw33237Labels = mixedMoment B raw33237step0 raw33237step0Labels := by
      have ha : raw33237step0 = (fun i j => raw33237 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33237step0 raw33237; decide +kernel
      have hl : raw33237step0Labels = raw33237Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33237 raw33237Labels permutation158 permutation4
    mixedMoment B raw33237step0 raw33237step0Labels = mixedMoment B raw33237step1 raw33237step1Labels := by
      have ha : raw33237step1 = -raw33237step0 := by apply Matrix.ext; change ∀ i j, raw33237step1 i j = -(raw33237step0 i j); unfold raw33237step1 raw33237step0; decide +kernel
      have hl : raw33237step1Labels = raw33237step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33237step1 raw33237step1Labels = mixedMoment B raw33237step2 raw33237step2Labels := by
      have ha : raw33237step2 = raw33237step1 := by apply Matrix.ext; unfold raw33237step2 raw33237step1; decide +kernel
      have hl : raw33237step1Labels = labelEmbedding7 ∘ raw33237step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33237step1 raw33237step1Labels raw33237step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4736 node4736Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical261
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33420 raw33420Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw33420 raw33420Labels = mixedMoment B raw33420step0 raw33420step0Labels := by
      have hz : ∀ j, raw33420 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33420step0 = (fun i j => raw33420 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33420step0 raw33420; decide +kernel
      have hl : raw33420step0Labels = raw33420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33420 raw33420Labels permutation346 hz
    mixedMoment B raw33420step0 raw33420step0Labels = mixedMoment B raw33420step1 raw33420step1Labels := by
      have hz : ∀ i, raw33420step0 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw33420step1 = (fun i j => raw33420step0 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw33420step1 raw33420step0; decide +kernel
      have hl : raw33420step1Labels = (fun j => raw33420step0Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw33420step0 raw33420step0Labels permutation2 hz
    mixedMoment B raw33420step1 raw33420step1Labels = mixedMoment B raw33420step2 raw33420step2Labels := by
      have ha : raw33420step2 = -raw33420step1 := by apply Matrix.ext; change ∀ i j, raw33420step2 i j = -(raw33420step1 i j); unfold raw33420step2 raw33420step1; decide +kernel
      have hl : raw33420step2Labels = raw33420step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33420step2 raw33420step2Labels = mixedMoment B raw33420step3 raw33420step3Labels := by
      have ha : raw33420step3 = raw33420step2 := by apply Matrix.ext; unfold raw33420step3 raw33420step2; decide +kernel
      have hl : raw33420step2Labels = labelEmbedding3 ∘ raw33420step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33420step2 raw33420step2Labels raw33420step3Labels labelEmbedding3 hl
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical33458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33458 raw33458Labels = mixedMoment B node4641 node4641Labels := by
  calc
    mixedMoment B raw33458 raw33458Labels = mixedMoment B raw33458step0 raw33458step0Labels := by
      have ha : raw33458step0 = (fun i j => raw33458 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33458step0 raw33458; decide +kernel
      have hl : raw33458step0Labels = raw33458Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33458 raw33458Labels permutation152 permutation4
    mixedMoment B raw33458step0 raw33458step0Labels = mixedMoment B raw33458step1 raw33458step1Labels := by
      have ha : raw33458step1 = -raw33458step0 := by apply Matrix.ext; change ∀ i j, raw33458step1 i j = -(raw33458step0 i j); unfold raw33458step1 raw33458step0; decide +kernel
      have hl : raw33458step1Labels = raw33458step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33458step1 raw33458step1Labels = mixedMoment B raw33458step2 raw33458step2Labels := by
      have ha : raw33458step2 = raw33458step1 := by apply Matrix.ext; unfold raw33458step2 raw33458step1; decide +kernel
      have hl : raw33458step1Labels = labelEmbedding7 ∘ raw33458step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33458step1 raw33458step1Labels raw33458step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4641 node4641Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical264
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33863 raw33863Labels = mixedMoment B node4746 node4746Labels := by
  calc
    mixedMoment B raw33863 raw33863Labels = mixedMoment B raw33863step0 raw33863step0Labels := by
      have ha : raw33863step0 = (fun i j => raw33863 (permutation173 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33863step0 raw33863; decide +kernel
      have hl : raw33863step0Labels = raw33863Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33863 raw33863Labels permutation173 permutation4
    mixedMoment B raw33863step0 raw33863step0Labels = mixedMoment B raw33863step1 raw33863step1Labels := by
      have ha : raw33863step1 = -raw33863step0 := by apply Matrix.ext; change ∀ i j, raw33863step1 i j = -(raw33863step0 i j); unfold raw33863step1 raw33863step0; decide +kernel
      have hl : raw33863step1Labels = raw33863step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33863step1 raw33863step1Labels = mixedMoment B raw33863step2 raw33863step2Labels := by
      have ha : raw33863step2 = raw33863step1 := by apply Matrix.ext; unfold raw33863step2 raw33863step1; decide +kernel
      have hl : raw33863step1Labels = labelEmbedding7 ∘ raw33863step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33863step1 raw33863step1Labels raw33863step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4746 node4746Labels := by rfl

theorem canonical33867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33867 raw33867Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw33867 raw33867Labels = mixedMoment B raw33867step0 raw33867step0Labels := by
      have ha : raw33867step0 = (fun i j => raw33867 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33867step0 raw33867; decide +kernel
      have hl : raw33867step0Labels = raw33867Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33867 raw33867Labels permutation154 permutation6
    mixedMoment B raw33867step0 raw33867step0Labels = mixedMoment B raw33867step1 raw33867step1Labels := by
      have ha : raw33867step1 = raw33867step0 := by apply Matrix.ext; unfold raw33867step1 raw33867step0; decide +kernel
      have hl : raw33867step0Labels = labelEmbedding9 ∘ raw33867step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33867step0 raw33867step0Labels raw33867step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

theorem canonical33871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33871 raw33871Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw33871 raw33871Labels = mixedMoment B raw33871step0 raw33871step0Labels := by
      have ha : raw33871step0 = (fun i j => raw33871 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33871step0 raw33871; decide +kernel
      have hl : raw33871step0Labels = raw33871Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33871 raw33871Labels permutation152 permutation6
    mixedMoment B raw33871step0 raw33871step0Labels = mixedMoment B raw33871step1 raw33871step1Labels := by
      have ha : raw33871step1 = raw33871step0 := by apply Matrix.ext; unfold raw33871step1 raw33871step0; decide +kernel
      have hl : raw33871step0Labels = labelEmbedding9 ∘ raw33871step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33871step0 raw33871step0Labels raw33871step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

theorem canonical33873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33873 raw33873Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw33873 raw33873Labels = mixedMoment B raw33873step0 raw33873step0Labels := by
      have ha : raw33873step0 = (fun i j => raw33873 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33873step0 raw33873; decide +kernel
      have hl : raw33873step0Labels = raw33873Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33873 raw33873Labels permutation152 permutation4
    mixedMoment B raw33873step0 raw33873step0Labels = mixedMoment B raw33873step1 raw33873step1Labels := by
      have ha : raw33873step1 = -raw33873step0 := by apply Matrix.ext; change ∀ i j, raw33873step1 i j = -(raw33873step0 i j); unfold raw33873step1 raw33873step0; decide +kernel
      have hl : raw33873step1Labels = raw33873step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33873step1 raw33873step1Labels = mixedMoment B raw33873step2 raw33873step2Labels := by
      have ha : raw33873step2 = raw33873step1 := by apply Matrix.ext; unfold raw33873step2 raw33873step1; decide +kernel
      have hl : raw33873step1Labels = labelEmbedding7 ∘ raw33873step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33873step1 raw33873step1Labels raw33873step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

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

theorem canonical34195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34195 raw34195Labels = mixedMoment B node4752 node4752Labels := by
  calc
    mixedMoment B raw34195 raw34195Labels = mixedMoment B raw34195step0 raw34195step0Labels := by
      have hz : ∀ j, raw34195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34195step0 = (fun i j => raw34195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34195step0 raw34195; decide +kernel
      have hl : raw34195step0Labels = raw34195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34195 raw34195Labels permutation346 hz
    mixedMoment B raw34195step0 raw34195step0Labels = mixedMoment B raw34195step1 raw34195step1Labels := by
      have ha : raw34195step1 = (fun i j => raw34195step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34195step1 raw34195step0; decide +kernel
      have hl : raw34195step1Labels = raw34195step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34195step0 raw34195step0Labels permutation35 permutation4
    mixedMoment B raw34195step1 raw34195step1Labels = mixedMoment B raw34195step2 raw34195step2Labels := by
      have ha : raw34195step2 = -raw34195step1 := by apply Matrix.ext; change ∀ i j, raw34195step2 i j = -(raw34195step1 i j); unfold raw34195step2 raw34195step1; decide +kernel
      have hl : raw34195step2Labels = raw34195step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34195step2 raw34195step2Labels = mixedMoment B raw34195step3 raw34195step3Labels := by
      have ha : raw34195step3 = raw34195step2 := by apply Matrix.ext; unfold raw34195step3 raw34195step2; decide +kernel
      have hl : raw34195step2Labels = labelEmbedding7 ∘ raw34195step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34195step2 raw34195step2Labels raw34195step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4752 node4752Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical268
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34395 raw34395Labels = mixedMoment B node4307 node4307Labels := by
  calc
    mixedMoment B raw34395 raw34395Labels = mixedMoment B raw34395step0 raw34395step0Labels := by
      have ha : raw34395step0 = (fun i j => raw34395 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34395step0 raw34395; decide +kernel
      have hl : raw34395step0Labels = raw34395Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34395 raw34395Labels permutation161 permutation4
    mixedMoment B raw34395step0 raw34395step0Labels = mixedMoment B raw34395step1 raw34395step1Labels := by
      have ha : raw34395step1 = -raw34395step0 := by apply Matrix.ext; change ∀ i j, raw34395step1 i j = -(raw34395step0 i j); unfold raw34395step1 raw34395step0; decide +kernel
      have hl : raw34395step1Labels = raw34395step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34395step1 raw34395step1Labels = mixedMoment B raw34395step2 raw34395step2Labels := by
      have ha : raw34395step2 = raw34395step1 := by apply Matrix.ext; unfold raw34395step2 raw34395step1; decide +kernel
      have hl : raw34395step1Labels = labelEmbedding7 ∘ raw34395step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34395step1 raw34395step1Labels raw34395step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4307 node4307Labels := by rfl

theorem canonical34396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34396 raw34396Labels = mixedMoment B node4648 node4648Labels := by
  calc
    mixedMoment B raw34396 raw34396Labels = mixedMoment B raw34396step0 raw34396step0Labels := by
      have ha : raw34396step0 = (fun i j => raw34396 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34396step0 raw34396; decide +kernel
      have hl : raw34396step0Labels = raw34396Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34396 raw34396Labels permutation161 permutation4
    mixedMoment B raw34396step0 raw34396step0Labels = mixedMoment B raw34396step1 raw34396step1Labels := by
      have ha : raw34396step1 = -raw34396step0 := by apply Matrix.ext; change ∀ i j, raw34396step1 i j = -(raw34396step0 i j); unfold raw34396step1 raw34396step0; decide +kernel
      have hl : raw34396step1Labels = raw34396step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34396step1 raw34396step1Labels = mixedMoment B raw34396step2 raw34396step2Labels := by
      have ha : raw34396step2 = raw34396step1 := by apply Matrix.ext; unfold raw34396step2 raw34396step1; decide +kernel
      have hl : raw34396step1Labels = labelEmbedding7 ∘ raw34396step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34396step1 raw34396step1Labels raw34396step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4648 node4648Labels := by rfl

theorem canonical34397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34397 raw34397Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw34397 raw34397Labels = mixedMoment B raw34397step0 raw34397step0Labels := by
      have ha : raw34397step0 = (fun i j => raw34397 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34397step0 raw34397; decide +kernel
      have hl : raw34397step0Labels = raw34397Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34397 raw34397Labels permutation161 permutation4
    mixedMoment B raw34397step0 raw34397step0Labels = mixedMoment B raw34397step1 raw34397step1Labels := by
      have ha : raw34397step1 = -raw34397step0 := by apply Matrix.ext; change ∀ i j, raw34397step1 i j = -(raw34397step0 i j); unfold raw34397step1 raw34397step0; decide +kernel
      have hl : raw34397step1Labels = raw34397step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34397step1 raw34397step1Labels = mixedMoment B raw34397step2 raw34397step2Labels := by
      have ha : raw34397step2 = raw34397step1 := by apply Matrix.ext; unfold raw34397step2 raw34397step1; decide +kernel
      have hl : raw34397step1Labels = labelEmbedding7 ∘ raw34397step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34397step1 raw34397step1Labels raw34397step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

theorem canonical34398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34398 raw34398Labels = mixedMoment B node4301 node4301Labels := by
  calc
    mixedMoment B raw34398 raw34398Labels = mixedMoment B raw34398step0 raw34398step0Labels := by
      have ha : raw34398step0 = (fun i j => raw34398 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34398step0 raw34398; decide +kernel
      have hl : raw34398step0Labels = raw34398Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34398 raw34398Labels permutation155 permutation4
    mixedMoment B raw34398step0 raw34398step0Labels = mixedMoment B raw34398step1 raw34398step1Labels := by
      have ha : raw34398step1 = -raw34398step0 := by apply Matrix.ext; change ∀ i j, raw34398step1 i j = -(raw34398step0 i j); unfold raw34398step1 raw34398step0; decide +kernel
      have hl : raw34398step1Labels = raw34398step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34398step1 raw34398step1Labels = mixedMoment B raw34398step2 raw34398step2Labels := by
      have ha : raw34398step2 = raw34398step1 := by apply Matrix.ext; unfold raw34398step2 raw34398step1; decide +kernel
      have hl : raw34398step1Labels = labelEmbedding7 ∘ raw34398step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34398step1 raw34398step1Labels raw34398step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4301 node4301Labels := by rfl

theorem canonical34399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34399 raw34399Labels = mixedMoment B node4642 node4642Labels := by
  calc
    mixedMoment B raw34399 raw34399Labels = mixedMoment B raw34399step0 raw34399step0Labels := by
      have ha : raw34399step0 = (fun i j => raw34399 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34399step0 raw34399; decide +kernel
      have hl : raw34399step0Labels = raw34399Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34399 raw34399Labels permutation155 permutation4
    mixedMoment B raw34399step0 raw34399step0Labels = mixedMoment B raw34399step1 raw34399step1Labels := by
      have ha : raw34399step1 = -raw34399step0 := by apply Matrix.ext; change ∀ i j, raw34399step1 i j = -(raw34399step0 i j); unfold raw34399step1 raw34399step0; decide +kernel
      have hl : raw34399step1Labels = raw34399step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34399step1 raw34399step1Labels = mixedMoment B raw34399step2 raw34399step2Labels := by
      have ha : raw34399step2 = raw34399step1 := by apply Matrix.ext; unfold raw34399step2 raw34399step1; decide +kernel
      have hl : raw34399step1Labels = labelEmbedding7 ∘ raw34399step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34399step1 raw34399step1Labels raw34399step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4642 node4642Labels := by rfl

theorem canonical34400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34400 raw34400Labels = mixedMoment B node4301 node4301Labels := by
  calc
    mixedMoment B raw34400 raw34400Labels = mixedMoment B raw34400step0 raw34400step0Labels := by
      have ha : raw34400step0 = (fun i j => raw34400 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34400step0 raw34400; decide +kernel
      have hl : raw34400step0Labels = raw34400Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34400 raw34400Labels permutation153 permutation4
    mixedMoment B raw34400step0 raw34400step0Labels = mixedMoment B raw34400step1 raw34400step1Labels := by
      have ha : raw34400step1 = -raw34400step0 := by apply Matrix.ext; change ∀ i j, raw34400step1 i j = -(raw34400step0 i j); unfold raw34400step1 raw34400step0; decide +kernel
      have hl : raw34400step1Labels = raw34400step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34400step1 raw34400step1Labels = mixedMoment B raw34400step2 raw34400step2Labels := by
      have ha : raw34400step2 = raw34400step1 := by apply Matrix.ext; unfold raw34400step2 raw34400step1; decide +kernel
      have hl : raw34400step1Labels = labelEmbedding7 ∘ raw34400step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34400step1 raw34400step1Labels raw34400step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4301 node4301Labels := by rfl

theorem canonical34401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34401 raw34401Labels = mixedMoment B node4642 node4642Labels := by
  calc
    mixedMoment B raw34401 raw34401Labels = mixedMoment B raw34401step0 raw34401step0Labels := by
      have ha : raw34401step0 = (fun i j => raw34401 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34401step0 raw34401; decide +kernel
      have hl : raw34401step0Labels = raw34401Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34401 raw34401Labels permutation153 permutation4
    mixedMoment B raw34401step0 raw34401step0Labels = mixedMoment B raw34401step1 raw34401step1Labels := by
      have ha : raw34401step1 = -raw34401step0 := by apply Matrix.ext; change ∀ i j, raw34401step1 i j = -(raw34401step0 i j); unfold raw34401step1 raw34401step0; decide +kernel
      have hl : raw34401step1Labels = raw34401step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34401step1 raw34401step1Labels = mixedMoment B raw34401step2 raw34401step2Labels := by
      have ha : raw34401step2 = raw34401step1 := by apply Matrix.ext; unfold raw34401step2 raw34401step1; decide +kernel
      have hl : raw34401step1Labels = labelEmbedding7 ∘ raw34401step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34401step1 raw34401step1Labels raw34401step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4642 node4642Labels := by rfl

theorem canonical34402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34402 raw34402Labels = mixedMoment B node4752 node4752Labels := by
  calc
    mixedMoment B raw34402 raw34402Labels = mixedMoment B raw34402step0 raw34402step0Labels := by
      have hz : ∀ j, raw34402 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34402step0 = (fun i j => raw34402 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34402step0 raw34402; decide +kernel
      have hl : raw34402step0Labels = raw34402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34402 raw34402Labels permutation346 hz
    mixedMoment B raw34402step0 raw34402step0Labels = mixedMoment B raw34402step1 raw34402step1Labels := by
      have ha : raw34402step1 = (fun i j => raw34402step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34402step1 raw34402step0; decide +kernel
      have hl : raw34402step1Labels = raw34402step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34402step0 raw34402step0Labels permutation33 permutation4
    mixedMoment B raw34402step1 raw34402step1Labels = mixedMoment B raw34402step2 raw34402step2Labels := by
      have ha : raw34402step2 = -raw34402step1 := by apply Matrix.ext; change ∀ i j, raw34402step2 i j = -(raw34402step1 i j); unfold raw34402step2 raw34402step1; decide +kernel
      have hl : raw34402step2Labels = raw34402step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34402step2 raw34402step2Labels = mixedMoment B raw34402step3 raw34402step3Labels := by
      have ha : raw34402step3 = raw34402step2 := by apply Matrix.ext; unfold raw34402step3 raw34402step2; decide +kernel
      have hl : raw34402step2Labels = labelEmbedding7 ∘ raw34402step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34402step2 raw34402step2Labels raw34402step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4752 node4752Labels := by rfl

theorem canonical34403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34403 raw34403Labels = mixedMoment B node4737 node4737Labels := by
  calc
    mixedMoment B raw34403 raw34403Labels = mixedMoment B raw34403step0 raw34403step0Labels := by
      have ha : raw34403step0 = (fun i j => raw34403 (permutation159 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34403step0 raw34403; decide +kernel
      have hl : raw34403step0Labels = raw34403Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34403 raw34403Labels permutation159 permutation4
    mixedMoment B raw34403step0 raw34403step0Labels = mixedMoment B raw34403step1 raw34403step1Labels := by
      have ha : raw34403step1 = -raw34403step0 := by apply Matrix.ext; change ∀ i j, raw34403step1 i j = -(raw34403step0 i j); unfold raw34403step1 raw34403step0; decide +kernel
      have hl : raw34403step1Labels = raw34403step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34403step1 raw34403step1Labels = mixedMoment B raw34403step2 raw34403step2Labels := by
      have ha : raw34403step2 = raw34403step1 := by apply Matrix.ext; unfold raw34403step2 raw34403step1; decide +kernel
      have hl : raw34403step1Labels = labelEmbedding7 ∘ raw34403step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34403step1 raw34403step1Labels raw34403step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4737 node4737Labels := by rfl

theorem canonical34404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34404 raw34404Labels = mixedMoment B node4300 node4300Labels := by
  calc
    mixedMoment B raw34404 raw34404Labels = mixedMoment B raw34404step0 raw34404step0Labels := by
      have ha : raw34404step0 = (fun i j => raw34404 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34404step0 raw34404; decide +kernel
      have hl : raw34404step0Labels = raw34404Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34404 raw34404Labels permutation152 permutation4
    mixedMoment B raw34404step0 raw34404step0Labels = mixedMoment B raw34404step1 raw34404step1Labels := by
      have ha : raw34404step1 = -raw34404step0 := by apply Matrix.ext; change ∀ i j, raw34404step1 i j = -(raw34404step0 i j); unfold raw34404step1 raw34404step0; decide +kernel
      have hl : raw34404step1Labels = raw34404step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34404step1 raw34404step1Labels = mixedMoment B raw34404step2 raw34404step2Labels := by
      have ha : raw34404step2 = raw34404step1 := by apply Matrix.ext; unfold raw34404step2 raw34404step1; decide +kernel
      have hl : raw34404step1Labels = labelEmbedding7 ∘ raw34404step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34404step1 raw34404step1Labels raw34404step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4300 node4300Labels := by rfl

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

theorem canonical1062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1062 raw1062Labels = mixedMoment B node4301 node4301Labels := by
  calc
    mixedMoment B raw1062 raw1062Labels = mixedMoment B raw1062step0 raw1062step0Labels := by
      have ha : raw1062step0 = (fun i j => raw1062 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1062step0 raw1062; decide +kernel
      have hl : raw1062step0Labels = raw1062Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1062 raw1062Labels permutation152 permutation4
    mixedMoment B raw1062step0 raw1062step0Labels = mixedMoment B raw1062step1 raw1062step1Labels := by
      have ha : raw1062step1 = raw1062step0 := by apply Matrix.ext; unfold raw1062step1 raw1062step0; decide +kernel
      have hl : raw1062step0Labels = labelEmbedding7 ∘ raw1062step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1062step0 raw1062step0Labels raw1062step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4301 node4301Labels := by rfl

theorem canonical1063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1063 raw1063Labels = mixedMoment B node879 node879Labels := by
  calc
    mixedMoment B raw1063 raw1063Labels = mixedMoment B raw1063step0 raw1063step0Labels := by
      have ha : raw1063step0 = (fun i j => raw1063 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1063step0 raw1063; decide +kernel
      have hl : raw1063step0Labels = raw1063Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1063 raw1063Labels permutation152 permutation4
    _ = mixedMoment B node879 node879Labels := by rfl

theorem canonical1064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1064 raw1064Labels = mixedMoment B node1556 node1556Labels := by
  calc
    mixedMoment B raw1064 raw1064Labels = mixedMoment B raw1064step0 raw1064step0Labels := by
      have ha : raw1064step0 = (fun i j => raw1064 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1064step0 raw1064; decide +kernel
      have hl : raw1064step0Labels = raw1064Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1064 raw1064Labels permutation153 permutation6
    mixedMoment B raw1064step0 raw1064step0Labels = mixedMoment B raw1064step1 raw1064step1Labels := by
      have ha : raw1064step1 = -raw1064step0 := by apply Matrix.ext; change ∀ i j, raw1064step1 i j = -(raw1064step0 i j); unfold raw1064step1 raw1064step0; decide +kernel
      have hl : raw1064step1Labels = raw1064step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1064step1 raw1064step1Labels = mixedMoment B raw1064step2 raw1064step2Labels := by
      have ha : raw1064step2 = raw1064step1 := by apply Matrix.ext; unfold raw1064step2 raw1064step1; decide +kernel
      have hl : raw1064step1Labels = labelEmbedding1 ∘ raw1064step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1064step1 raw1064step1Labels raw1064step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1556 node1556Labels := by rfl

theorem canonical1071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1071 raw1071Labels = mixedMoment B node4307 node4307Labels := by
  calc
    mixedMoment B raw1071 raw1071Labels = mixedMoment B raw1071step0 raw1071step0Labels := by
      have ha : raw1071step0 = (fun i j => raw1071 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1071step0 raw1071; decide +kernel
      have hl : raw1071step0Labels = raw1071Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1071 raw1071Labels permutation152 permutation4
    mixedMoment B raw1071step0 raw1071step0Labels = mixedMoment B raw1071step1 raw1071step1Labels := by
      have ha : raw1071step1 = raw1071step0 := by apply Matrix.ext; unfold raw1071step1 raw1071step0; decide +kernel
      have hl : raw1071step0Labels = labelEmbedding7 ∘ raw1071step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1071step0 raw1071step0Labels raw1071step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4307 node4307Labels := by rfl

theorem canonical1072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1072 raw1072Labels = mixedMoment B node885 node885Labels := by
  calc
    mixedMoment B raw1072 raw1072Labels = mixedMoment B raw1072step0 raw1072step0Labels := by
      have ha : raw1072step0 = (fun i j => raw1072 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1072step0 raw1072; decide +kernel
      have hl : raw1072step0Labels = raw1072Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1072 raw1072Labels permutation152 permutation4
    _ = mixedMoment B node885 node885Labels := by rfl

theorem canonical1073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1073 raw1073Labels = mixedMoment B node1563 node1563Labels := by
  calc
    mixedMoment B raw1073 raw1073Labels = mixedMoment B raw1073step0 raw1073step0Labels := by
      have ha : raw1073step0 = (fun i j => raw1073 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1073step0 raw1073; decide +kernel
      have hl : raw1073step0Labels = raw1073Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1073 raw1073Labels permutation170 permutation6
    mixedMoment B raw1073step0 raw1073step0Labels = mixedMoment B raw1073step1 raw1073step1Labels := by
      have ha : raw1073step1 = -raw1073step0 := by apply Matrix.ext; change ∀ i j, raw1073step1 i j = -(raw1073step0 i j); unfold raw1073step1 raw1073step0; decide +kernel
      have hl : raw1073step1Labels = raw1073step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1073step1 raw1073step1Labels = mixedMoment B raw1073step2 raw1073step2Labels := by
      have ha : raw1073step2 = raw1073step1 := by apply Matrix.ext; unfold raw1073step2 raw1073step1; decide +kernel
      have hl : raw1073step1Labels = labelEmbedding1 ∘ raw1073step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1073step1 raw1073step1Labels raw1073step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1563 node1563Labels := by rfl

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

theorem canonical1224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1224 raw1224Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw1224 raw1224Labels = mixedMoment B raw1224step0 raw1224step0Labels := by
      have ha : raw1224step0 = (fun i j => raw1224 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1224step0 raw1224; decide +kernel
      have hl : raw1224step0Labels = raw1224Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1224 raw1224Labels permutation152 permutation4
    mixedMoment B raw1224step0 raw1224step0Labels = mixedMoment B raw1224step1 raw1224step1Labels := by
      have ha : raw1224step1 = raw1224step0 := by apply Matrix.ext; unfold raw1224step1 raw1224step0; decide +kernel
      have hl : raw1224step0Labels = labelEmbedding7 ∘ raw1224step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1224step0 raw1224step0Labels raw1224step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

theorem canonical1225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1225 raw1225Labels = mixedMoment B node998 node998Labels := by
  calc
    mixedMoment B raw1225 raw1225Labels = mixedMoment B raw1225step0 raw1225step0Labels := by
      have ha : raw1225step0 = (fun i j => raw1225 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1225step0 raw1225; decide +kernel
      have hl : raw1225step0Labels = raw1225Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1225 raw1225Labels permutation152 permutation4
    _ = mixedMoment B node998 node998Labels := by rfl

theorem canonical1226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1226 raw1226Labels = mixedMoment B node1600 node1600Labels := by
  calc
    mixedMoment B raw1226 raw1226Labels = mixedMoment B raw1226step0 raw1226step0Labels := by
      have ha : raw1226step0 = (fun i j => raw1226 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1226step0 raw1226; decide +kernel
      have hl : raw1226step0Labels = raw1226Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1226 raw1226Labels permutation152 permutation6
    mixedMoment B raw1226step0 raw1226step0Labels = mixedMoment B raw1226step1 raw1226step1Labels := by
      have ha : raw1226step1 = -raw1226step0 := by apply Matrix.ext; change ∀ i j, raw1226step1 i j = -(raw1226step0 i j); unfold raw1226step1 raw1226step0; decide +kernel
      have hl : raw1226step1Labels = raw1226step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1226step1 raw1226step1Labels = mixedMoment B raw1226step2 raw1226step2Labels := by
      have ha : raw1226step2 = raw1226step1 := by apply Matrix.ext; unfold raw1226step2 raw1226step1; decide +kernel
      have hl : raw1226step1Labels = labelEmbedding1 ∘ raw1226step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1226step1 raw1226step1Labels raw1226step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1600 node1600Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4301 node4301Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node879 node879Labels + mixedMoment B node1556 node1556Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1062 singletonSmall4301
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4301) = raw1062Labels := by decide +kernel
  rw [hl, canonical1062 B hB] at h
  have hc0 : mixedMoment B raw1062 (Fin.cases (0 : Fin 2) singletonSmall4301) =
      mixedMoment B node879 node879Labels := by
    have ha : raw1062 = raw1063 := by apply Matrix.ext; unfold raw1062 raw1063; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4301 = raw1063Labels := by decide +kernel
    rw [ha, hj, canonical1063 B hB]
  have hc1 : mixedMoment B raw1062 (Fin.cases (1 : Fin 2) singletonSmall4301) =
      mixedMoment B node1556 node1556Labels := by
    have ha : raw1062 = raw1064 := by apply Matrix.ext; unfold raw1062 raw1064; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4301 = raw1064Labels := by decide +kernel
    rw [ha, hj, canonical1064 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4307 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4307 node4307Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node885 node885Labels + mixedMoment B node1563 node1563Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1071 singletonSmall4307
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4307) = raw1071Labels := by decide +kernel
  rw [hl, canonical1071 B hB] at h
  have hc0 : mixedMoment B raw1071 (Fin.cases (0 : Fin 2) singletonSmall4307) =
      mixedMoment B node885 node885Labels := by
    have ha : raw1071 = raw1072 := by apply Matrix.ext; unfold raw1071 raw1072; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4307 = raw1072Labels := by decide +kernel
    rw [ha, hj, canonical1072 B hB]
  have hc1 : mixedMoment B raw1071 (Fin.cases (1 : Fin 2) singletonSmall4307) =
      mixedMoment B node1563 node1563Labels := by
    have ha : raw1071 = raw1073 := by apply Matrix.ext; unfold raw1071 raw1073; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4307 = raw1073Labels := by decide +kernel
    rw [ha, hj, canonical1073 B hB]
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

theorem singleton4417 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4417 node4417Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node998 node998Labels + mixedMoment B node1600 node1600Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1224 singletonSmall4417
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4417) = raw1224Labels := by decide +kernel
  rw [hl, canonical1224 B hB] at h
  have hc0 : mixedMoment B raw1224 (Fin.cases (0 : Fin 2) singletonSmall4417) =
      mixedMoment B node998 node998Labels := by
    have ha : raw1224 = raw1225 := by apply Matrix.ext; unfold raw1224 raw1225; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4417 = raw1225Labels := by decide +kernel
    rw [ha, hj, canonical1225 B hB]
  have hc1 : mixedMoment B raw1224 (Fin.cases (1 : Fin 2) singletonSmall4417) =
      mixedMoment B node1600 node1600Labels := by
    have ha : raw1224 = raw1226 := by apply Matrix.ext; unfold raw1224 raw1226; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4417 = raw1226Labels := by decide +kernel
    rw [ha, hj, canonical1226 B hB]
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

theorem singleton4648 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4648 node4648Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1776 node1776Labels + mixedMoment B node1844 node1844Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1512 singletonSmall4648
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4648) = raw1512Labels := by decide +kernel
  rw [hl, canonical1512 B hB] at h
  have hc0 : mixedMoment B raw1512 (Fin.cases (0 : Fin 2) singletonSmall4648) =
      mixedMoment B node1776 node1776Labels := by
    have ha : raw1512 = raw1513 := by apply Matrix.ext; unfold raw1512 raw1513; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4648 = raw1513Labels := by decide +kernel
    rw [ha, hj, canonical1513 B hB]
  have hc1 : mixedMoment B raw1512 (Fin.cases (1 : Fin 2) singletonSmall4648) =
      mixedMoment B node1844 node1844Labels := by
    have ha : raw1512 = raw1514 := by apply Matrix.ext; unfold raw1512 raw1514; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4648 = raw1514Labels := by decide +kernel
    rw [ha, hj, canonical1514 B hB]
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

theorem singleton4740 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4740 node4740Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1913 node1913Labels + mixedMoment B node1922 node1922Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1656 singletonSmall4740
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4740) = raw1656Labels := by decide +kernel
  rw [hl, canonical1656 B hB] at h
  have hc0 : mixedMoment B raw1656 (Fin.cases (0 : Fin 2) singletonSmall4740) =
      mixedMoment B node1913 node1913Labels := by
    have ha : raw1656 = raw1657 := by apply Matrix.ext; unfold raw1656 raw1657; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4740 = raw1657Labels := by decide +kernel
    rw [ha, hj, canonical1657 B hB]
  have hc1 : mixedMoment B raw1656 (Fin.cases (1 : Fin 2) singletonSmall4740) =
      mixedMoment B node1922 node1922Labels := by
    have ha : raw1656 = raw1658 := by apply Matrix.ext; unfold raw1656 raw1658; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4740 = raw1658Labels := by decide +kernel
    rw [ha, hj, canonical1658 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4746 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4746 node4746Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1925 node1925Labels + mixedMoment B node1925 node1925Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1665 singletonSmall4746
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4746) = raw1665Labels := by decide +kernel
  rw [hl, canonical1665 B hB] at h
  have hc0 : mixedMoment B raw1665 (Fin.cases (0 : Fin 2) singletonSmall4746) =
      mixedMoment B node1925 node1925Labels := by
    have ha : raw1665 = raw1666 := by apply Matrix.ext; unfold raw1665 raw1666; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4746 = raw1666Labels := by decide +kernel
    rw [ha, hj, canonical1666 B hB]
  have hc1 : mixedMoment B raw1665 (Fin.cases (1 : Fin 2) singletonSmall4746) =
      mixedMoment B node1925 node1925Labels := by
    have ha : raw1665 = raw1667 := by apply Matrix.ext; unfold raw1665 raw1667; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4746 = raw1667Labels := by decide +kernel
    rw [ha, hj, canonical1667 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4998 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4998 node4998Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2383 node2383Labels + mixedMoment B node3352 node3352Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2010 singletonSmall4998
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4998) = raw2010Labels := by decide +kernel
  rw [hl, canonical2010 B hB] at h
  have hc0 : mixedMoment B raw2010 (Fin.cases (0 : Fin 2) singletonSmall4998) =
      mixedMoment B node2383 node2383Labels := by
    have ha : raw2010 = raw2011 := by apply Matrix.ext; unfold raw2010 raw2011; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4998 = raw2011Labels := by decide +kernel
    rw [ha, hj, canonical2011 B hB]
  have hc1 : mixedMoment B raw2010 (Fin.cases (1 : Fin 2) singletonSmall4998) =
      mixedMoment B node3352 node3352Labels := by
    have ha : raw2010 = raw2012 := by apply Matrix.ext; unfold raw2010 raw2012; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4998 = raw2012Labels := by decide +kernel
    rw [ha, hj, canonical2012 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton5073 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5073 node5073Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2480 node2480Labels + mixedMoment B node3467 node3467Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2094 singletonSmall5073
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5073) = raw2094Labels := by decide +kernel
  rw [hl, canonical2094 B hB] at h
  have hc0 : mixedMoment B raw2094 (Fin.cases (0 : Fin 2) singletonSmall5073) =
      mixedMoment B node2480 node2480Labels := by
    have ha : raw2094 = raw2095 := by apply Matrix.ext; unfold raw2094 raw2095; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5073 = raw2095Labels := by decide +kernel
    rw [ha, hj, canonical2095 B hB]
  have hc1 : mixedMoment B raw2094 (Fin.cases (1 : Fin 2) singletonSmall5073) =
      mixedMoment B node3467 node3467Labels := by
    have ha : raw2094 = raw2096 := by apply Matrix.ext; unfold raw2094 raw2096; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5073 = raw2096Labels := by decide +kernel
    rw [ha, hj, canonical2096 B hB]
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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node879 node879Labels = Sparse.eval nodeValue879 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 879) = mixedMoment B node879 node879Labels := rfl
  simpa [nodeValue879, Sparse.eval] using hc.symm

theorem sound885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node885 node885Labels = Sparse.eval nodeValue885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 885) = mixedMoment B node885 node885Labels := rfl
  simpa [nodeValue885, Sparse.eval] using hc.symm

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

theorem sound998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node998 node998Labels = Sparse.eval nodeValue998 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 998) = mixedMoment B node998 node998Labels := rfl
  simpa [nodeValue998, Sparse.eval] using hc.symm

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

theorem sound1556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1556 node1556Labels = Sparse.eval nodeValue1556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1556) = mixedMoment B node1556 node1556Labels := rfl
  simpa [nodeValue1556, Sparse.eval] using hc.symm

theorem sound1563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1563 node1563Labels = Sparse.eval nodeValue1563 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1563) = mixedMoment B node1563 node1563Labels := rfl
  simpa [nodeValue1563, Sparse.eval] using hc.symm

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

theorem sound1600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1600 node1600Labels = Sparse.eval nodeValue1600 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1600) = mixedMoment B node1600 node1600Labels := rfl
  simpa [nodeValue1600, Sparse.eval] using hc.symm

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

theorem sound1776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1776 node1776Labels = Sparse.eval nodeValue1776 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1776) = mixedMoment B node1776 node1776Labels := rfl
  simpa [nodeValue1776, Sparse.eval] using hc.symm

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

theorem sound1844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1844 node1844Labels = Sparse.eval nodeValue1844 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1844) = mixedMoment B node1844 node1844Labels := rfl
  simpa [nodeValue1844, Sparse.eval] using hc.symm

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

theorem sound1909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1909 node1909Labels = Sparse.eval nodeValue1909 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1909) = mixedMoment B node1909 node1909Labels := rfl
  simpa [nodeValue1909, Sparse.eval] using hc.symm

theorem sound1913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1913 node1913Labels = Sparse.eval nodeValue1913 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1913) = mixedMoment B node1913 node1913Labels := rfl
  simpa [nodeValue1913, Sparse.eval] using hc.symm

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

theorem sound1922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1922 node1922Labels = Sparse.eval nodeValue1922 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1922) = mixedMoment B node1922 node1922Labels := rfl
  simpa [nodeValue1922, Sparse.eval] using hc.symm

theorem sound1925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1925 node1925Labels = Sparse.eval nodeValue1925 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1925) = mixedMoment B node1925 node1925Labels := rfl
  simpa [nodeValue1925, Sparse.eval] using hc.symm

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

theorem sound2020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2020 node2020Labels = Sparse.eval nodeValue2020 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2020) = mixedMoment B node2020 node2020Labels := rfl
  simpa [nodeValue2020, Sparse.eval] using hc.symm

theorem sound2023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2023 node2023Labels = Sparse.eval nodeValue2023 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2023) = mixedMoment B node2023 node2023Labels := rfl
  simpa [nodeValue2023, Sparse.eval] using hc.symm

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

theorem sound2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2202 node2202Labels = Sparse.eval nodeValue2202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2202) = mixedMoment B node2202 node2202Labels := rfl
  simpa [nodeValue2202, Sparse.eval] using hc.symm

theorem sound2214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2214 node2214Labels = Sparse.eval nodeValue2214 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2214) = mixedMoment B node2214 node2214Labels := rfl
  simpa [nodeValue2214, Sparse.eval] using hc.symm

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

theorem sound2383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2383 node2383Labels = Sparse.eval nodeValue2383 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2383) = mixedMoment B node2383 node2383Labels := rfl
  simpa [nodeValue2383, Sparse.eval] using hc.symm

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

theorem sound2480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2480 node2480Labels = Sparse.eval nodeValue2480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2480) = mixedMoment B node2480 node2480Labels := rfl
  simpa [nodeValue2480, Sparse.eval] using hc.symm

theorem sound2483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2483 node2483Labels = Sparse.eval nodeValue2483 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2483) = mixedMoment B node2483 node2483Labels := rfl
  simpa [nodeValue2483, Sparse.eval] using hc.symm

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

theorem sound3352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3352 node3352Labels = Sparse.eval nodeValue3352 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3352) = mixedMoment B node3352 node3352Labels := rfl
  simpa [nodeValue3352, Sparse.eval] using hc.symm

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

theorem sound3467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3467 node3467Labels = Sparse.eval nodeValue3467 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3467) = mixedMoment B node3467 node3467Labels := rfl
  simpa [nodeValue3467, Sparse.eval] using hc.symm

theorem sound3477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3477 node3477Labels = Sparse.eval nodeValue3477 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3477) = mixedMoment B node3477 node3477Labels := rfl
  simpa [nodeValue3477, Sparse.eval] using hc.symm

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

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

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

theorem zero4300 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4300 node4300Labels = 0 := by
  exact mixedMoment_order_one B hB node4300 node4300Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4300 node4300Labels = Sparse.eval nodeValue4300 (mixedVector B) := by
  simpa only [nodeValue4300, Sparse.eval_nil] using zero4300 B _hB _hF

theorem sound4301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4301 node4301Labels = Sparse.eval nodeValue4301 (mixedVector B) := by
  have h := singleton4301 B _hB
  rw [sound879 B _hB _hF, sound1556 B _hB _hF] at h
  norm_num [nodeValue4301, nodeValue879, nodeValue1556, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4307 node4307Labels = Sparse.eval nodeValue4307 (mixedVector B) := by
  have h := singleton4307 B _hB
  rw [sound885 B _hB _hF, sound1563 B _hB _hF] at h
  norm_num [nodeValue4307, nodeValue885, nodeValue1563, Sparse.eval] at h ⊢
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

theorem sound4417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4417 node4417Labels = Sparse.eval nodeValue4417 (mixedVector B) := by
  have h := singleton4417 B _hB
  rw [sound998 B _hB _hF, sound1600 B _hB _hF] at h
  norm_num [nodeValue4417, nodeValue998, nodeValue1600, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4641 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4641 node4641Labels = 0 := by
  exact mixedMoment_order_one B hB node4641 node4641Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4641 node4641Labels = Sparse.eval nodeValue4641 (mixedVector B) := by
  simpa only [nodeValue4641, Sparse.eval_nil] using zero4641 B _hB _hF

theorem sound4642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4642 node4642Labels = Sparse.eval nodeValue4642 (mixedVector B) := by
  have h := singleton4642 B _hB
  rw [sound1771 B _hB _hF, sound1838 B _hB _hF] at h
  norm_num [nodeValue4642, nodeValue1771, nodeValue1838, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4648 node4648Labels = Sparse.eval nodeValue4648 (mixedVector B) := by
  have h := singleton4648 B _hB
  rw [sound1776 B _hB _hF, sound1844 B _hB _hF] at h
  norm_num [nodeValue4648, nodeValue1776, nodeValue1844, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4736 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4736 node4736Labels = 0 := by
  exact mixedMoment_order_one B hB node4736 node4736Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4752 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4752 node4752Labels = 0 := by
  exact mixedMoment_order_one B hB node4752 node4752Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4736 node4736Labels = Sparse.eval nodeValue4736 (mixedVector B) := by
  simpa only [nodeValue4736, Sparse.eval_nil] using zero4736 B _hB _hF

theorem sound4737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4737 node4737Labels = Sparse.eval nodeValue4737 (mixedVector B) := by
  have h := singleton4737 B _hB
  rw [sound1909 B _hB _hF] at h
  norm_num [nodeValue4737, nodeValue1909, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4740 node4740Labels = Sparse.eval nodeValue4740 (mixedVector B) := by
  have h := singleton4740 B _hB
  rw [sound1913 B _hB _hF, sound1922 B _hB _hF] at h
  norm_num [nodeValue4740, nodeValue1913, nodeValue1922, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4746 node4746Labels = Sparse.eval nodeValue4746 (mixedVector B) := by
  have h := singleton4746 B _hB
  rw [sound1925 B _hB _hF] at h
  norm_num [nodeValue4746, nodeValue1925, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4752 node4752Labels = Sparse.eval nodeValue4752 (mixedVector B) := by
  simpa only [nodeValue4752, Sparse.eval_nil] using zero4752 B _hB _hF

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

theorem zero4838 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4838 node4838Labels = 0 := by
  exact mixedMoment_order_one B hB node4838 node4838Labels 1
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

theorem sound4802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4802 node4802Labels = Sparse.eval nodeValue4802 (mixedVector B) := by
  have h := singleton4802 B _hB
  rw [sound2020 B _hB _hF, sound2202 B _hB _hF] at h
  norm_num [nodeValue4802, nodeValue2020, nodeValue2202, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4805 node4805Labels = Sparse.eval nodeValue4805 (mixedVector B) := by
  have h := singleton4805 B _hB
  rw [sound2023 B _hB _hF, sound2214 B _hB _hF] at h
  norm_num [nodeValue4805, nodeValue2023, nodeValue2214, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4838 node4838Labels = Sparse.eval nodeValue4838 (mixedVector B) := by
  simpa only [nodeValue4838, Sparse.eval_nil] using zero4838 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4998 node4998Labels = Sparse.eval nodeValue4998 (mixedVector B) := by
  have h := singleton4998 B _hB
  rw [sound2383 B _hB _hF, sound3352 B _hB _hF] at h
  norm_num [nodeValue4998, nodeValue2383, nodeValue3352, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5104 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5104 node5104Labels = 0 := by
  exact mixedMoment_order_one B hB node5104 node5104Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5073 node5073Labels = Sparse.eval nodeValue5073 (mixedVector B) := by
  have h := singleton5073 B _hB
  rw [sound2480 B _hB _hF, sound3467 B _hB _hF] at h
  norm_num [nodeValue5073, nodeValue2480, nodeValue3467, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5076 node5076Labels = Sparse.eval nodeValue5076 (mixedVector B) := by
  have h := singleton5076 B _hB
  rw [sound2483 B _hB _hF, sound3477 B _hB _hF] at h
  norm_num [nodeValue5076, nodeValue2483, nodeValue3477, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5104 node5104Labels = Sparse.eval nodeValue5104 (mixedVector B) := by
  simpa only [nodeValue5104, Sparse.eval_nil] using zero5104 B _hB _hF

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

theorem sourceEq2495 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2495 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2495 + difference 0 1) (sourceB2495 + difference 1 0) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4998) := by
    have ha : (tripleCharges (sourceA2495 + difference 0 1) (sourceB2495 + difference 1 0) sourceC2495) = raw33146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33146; decide +kernel
    rw [ha]
    exact (canonical33146 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2495 + difference 0 2) (sourceB2495 + difference 2 0) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA2495 + difference 0 2) (sourceB2495 + difference 2 0) sourceC2495) = raw32251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw32251; decide +kernel
    rw [ha]
    exact (canonical32251 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2495 + difference 0 3) (sourceB2495 + difference 3 0) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2495 + difference 0 3) (sourceB2495 + difference 3 0) sourceC2495) = raw32331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw32331; decide +kernel
    rw [ha]
    exact (canonical32331 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2495 + difference 0 4) (sourceB2495 + difference 4 0) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2495 + difference 0 4) (sourceB2495 + difference 4 0) sourceC2495) = raw32328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw32328; decide +kernel
    rw [ha]
    exact (canonical32328 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2495 + difference 0 5) (sourceB2495 + difference 5 0) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA2495 + difference 0 5) (sourceB2495 + difference 5 0) sourceC2495) = raw32236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw32236; decide +kernel
    rw [ha]
    exact (canonical32236 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2495 + difference 1 0) (sourceB2495 + difference 0 1) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA2495 + difference 1 0) (sourceB2495 + difference 0 1) sourceC2495) = raw33873 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33873; decide +kernel
    rw [ha]
    exact (canonical33873 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2495 + difference 1 2) (sourceB2495 + difference 2 1) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2495 + difference 1 2) (sourceB2495 + difference 2 1) sourceC2495) = raw32250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw32250; decide +kernel
    rw [ha]
    exact (canonical32250 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2495 + difference 1 3) (sourceB2495 + difference 3 1) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2495 + difference 1 3) (sourceB2495 + difference 3 1) sourceC2495) = raw32330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw32330; decide +kernel
    rw [ha]
    exact (canonical32330 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2495 + difference 1 4) (sourceB2495 + difference 4 1) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2495 + difference 1 4) (sourceB2495 + difference 4 1) sourceC2495) = raw32327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw32327; decide +kernel
    rw [ha]
    exact (canonical32327 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2495 + difference 1 5) (sourceB2495 + difference 5 1) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2495 + difference 1 5) (sourceB2495 + difference 5 1) sourceC2495) = raw32235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw32235; decide +kernel
    rw [ha]
    exact (canonical32235 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2495 + difference 2 0) (sourceB2495 + difference 0 2) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4307) := by
    have ha : (tripleCharges (sourceA2495 + difference 2 0) (sourceB2495 + difference 0 2) sourceC2495) = raw34395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34395; decide +kernel
    rw [ha]
    exact (canonical34395 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2495 + difference 2 1) (sourceB2495 + difference 1 2) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4648) := by
    have ha : (tripleCharges (sourceA2495 + difference 2 1) (sourceB2495 + difference 1 2) sourceC2495) = raw34396 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34396; decide +kernel
    rw [ha]
    exact (canonical34396 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2495 + difference 2 3) (sourceB2495 + difference 3 2) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA2495 + difference 2 3) (sourceB2495 + difference 3 2) sourceC2495) = raw34397 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34397; decide +kernel
    rw [ha]
    exact (canonical34397 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2495 + difference 2 4) (sourceB2495 + difference 4 2) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA2495 + difference 2 4) (sourceB2495 + difference 4 2) sourceC2495) = raw33136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33136; decide +kernel
    rw [ha]
    exact (canonical33136 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2495 + difference 2 5) (sourceB2495 + difference 5 2) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4746) := by
    have ha : (tripleCharges (sourceA2495 + difference 2 5) (sourceB2495 + difference 5 2) sourceC2495) = raw33863 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33863; decide +kernel
    rw [ha]
    exact (canonical33863 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2495 + difference 3 0) (sourceB2495 + difference 0 3) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4301) := by
    have ha : (tripleCharges (sourceA2495 + difference 3 0) (sourceB2495 + difference 0 3) sourceC2495) = raw34398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34398; decide +kernel
    rw [ha]
    exact (canonical34398 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2495 + difference 3 1) (sourceB2495 + difference 1 3) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4642) := by
    have ha : (tripleCharges (sourceA2495 + difference 3 1) (sourceB2495 + difference 1 3) sourceC2495) = raw34399 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34399; decide +kernel
    rw [ha]
    exact (canonical34399 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2495 + difference 3 2) (sourceB2495 + difference 2 3) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4752) := by
    have ha : (tripleCharges (sourceA2495 + difference 3 2) (sourceB2495 + difference 2 3) sourceC2495) = raw34195 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34195; decide +kernel
    rw [ha]
    exact (canonical34195 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2495 + difference 3 4) (sourceB2495 + difference 4 3) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4737) := by
    have ha : (tripleCharges (sourceA2495 + difference 3 4) (sourceB2495 + difference 4 3) sourceC2495) = raw33140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33140; decide +kernel
    rw [ha]
    exact (canonical33140 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2495 + difference 3 5) (sourceB2495 + difference 5 3) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA2495 + difference 3 5) (sourceB2495 + difference 5 3) sourceC2495) = raw33867 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33867; decide +kernel
    rw [ha]
    exact (canonical33867 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2495 + difference 4 0) (sourceB2495 + difference 0 4) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4301) := by
    have ha : (tripleCharges (sourceA2495 + difference 4 0) (sourceB2495 + difference 0 4) sourceC2495) = raw34400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34400; decide +kernel
    rw [ha]
    exact (canonical34400 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2495 + difference 4 1) (sourceB2495 + difference 1 4) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4642) := by
    have ha : (tripleCharges (sourceA2495 + difference 4 1) (sourceB2495 + difference 1 4) sourceC2495) = raw34401 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34401; decide +kernel
    rw [ha]
    exact (canonical34401 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2495 + difference 4 2) (sourceB2495 + difference 2 4) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4752) := by
    have ha : (tripleCharges (sourceA2495 + difference 4 2) (sourceB2495 + difference 2 4) sourceC2495) = raw34402 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34402; decide +kernel
    rw [ha]
    exact (canonical34402 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2495 + difference 4 3) (sourceB2495 + difference 3 4) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4737) := by
    have ha : (tripleCharges (sourceA2495 + difference 4 3) (sourceB2495 + difference 3 4) sourceC2495) = raw34403 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34403; decide +kernel
    rw [ha]
    exact (canonical34403 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2495 + difference 4 5) (sourceB2495 + difference 5 4) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA2495 + difference 4 5) (sourceB2495 + difference 5 4) sourceC2495) = raw33871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33871; decide +kernel
    rw [ha]
    exact (canonical33871 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2495 + difference 5 0) (sourceB2495 + difference 0 5) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4300) := by
    have ha : (tripleCharges (sourceA2495 + difference 5 0) (sourceB2495 + difference 0 5) sourceC2495) = raw34404 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34404; decide +kernel
    rw [ha]
    exact (canonical34404 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2495 + difference 5 1) (sourceB2495 + difference 1 5) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4641) := by
    have ha : (tripleCharges (sourceA2495 + difference 5 1) (sourceB2495 + difference 1 5) sourceC2495) = raw33458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33458; decide +kernel
    rw [ha]
    exact (canonical33458 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2495 + difference 5 2) (sourceB2495 + difference 2 5) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2495 + difference 5 2) (sourceB2495 + difference 2 5) sourceC2495) = raw33420 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33420; decide +kernel
    rw [ha]
    exact (canonical33420 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2495 + difference 5 3) (sourceB2495 + difference 3 5) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4736) := by
    have ha : (tripleCharges (sourceA2495 + difference 5 3) (sourceB2495 + difference 3 5) sourceC2495) = raw33237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33237; decide +kernel
    rw [ha]
    exact (canonical33237 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2495 + difference 5 4) (sourceB2495 + difference 4 5) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4736) := by
    have ha : (tripleCharges (sourceA2495 + difference 5 4) (sourceB2495 + difference 4 5) sourceC2495) = raw33147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33147; decide +kernel
    rw [ha]
    exact (canonical33147 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2495 sourceB2495 sourceC2495
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2495, Integer.Sparse.eval]
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

theorem reindexCheck2011 : Integer.Sparse.reindex keyMap MixedData.row2011 = numericRow2011 := by decide +kernel

theorem numericCheck2011 (x : Master → ℝ) : Integer.Sparse.eval numericRow2011 x =
    (4 : ℝ) * reducedSource2011 x := by
  norm_num [numericRow2011, reducedSource2011, Integer.Sparse.eval, Sparse.eval, nodeValue4080, nodeValue4300, nodeValue4301, nodeValue4307, nodeValue4417, nodeValue4641, nodeValue4642, nodeValue4648, nodeValue4736, nodeValue4737, nodeValue4740, nodeValue4746, nodeValue4752, nodeValue4802, nodeValue4805, nodeValue4838, nodeValue4998, nodeValue5073, nodeValue5076, nodeValue5104]
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

theorem reducedZero2011 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2011 (mixedVector B) = 0 := by
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4300 : mixedVector B (Sum.inr 4300) = Sparse.eval nodeValue4300 (mixedVector B) := by
    change mixedMoment B node4300 node4300Labels = _
    exact sound4300 B hB hF
  have h4301 : mixedVector B (Sum.inr 4301) = Sparse.eval nodeValue4301 (mixedVector B) := by
    change mixedMoment B node4301 node4301Labels = _
    exact sound4301 B hB hF
  have h4307 : mixedVector B (Sum.inr 4307) = Sparse.eval nodeValue4307 (mixedVector B) := by
    change mixedMoment B node4307 node4307Labels = _
    exact sound4307 B hB hF
  have h4417 : mixedVector B (Sum.inr 4417) = Sparse.eval nodeValue4417 (mixedVector B) := by
    change mixedMoment B node4417 node4417Labels = _
    exact sound4417 B hB hF
  have h4641 : mixedVector B (Sum.inr 4641) = Sparse.eval nodeValue4641 (mixedVector B) := by
    change mixedMoment B node4641 node4641Labels = _
    exact sound4641 B hB hF
  have h4642 : mixedVector B (Sum.inr 4642) = Sparse.eval nodeValue4642 (mixedVector B) := by
    change mixedMoment B node4642 node4642Labels = _
    exact sound4642 B hB hF
  have h4648 : mixedVector B (Sum.inr 4648) = Sparse.eval nodeValue4648 (mixedVector B) := by
    change mixedMoment B node4648 node4648Labels = _
    exact sound4648 B hB hF
  have h4736 : mixedVector B (Sum.inr 4736) = Sparse.eval nodeValue4736 (mixedVector B) := by
    change mixedMoment B node4736 node4736Labels = _
    exact sound4736 B hB hF
  have h4737 : mixedVector B (Sum.inr 4737) = Sparse.eval nodeValue4737 (mixedVector B) := by
    change mixedMoment B node4737 node4737Labels = _
    exact sound4737 B hB hF
  have h4740 : mixedVector B (Sum.inr 4740) = Sparse.eval nodeValue4740 (mixedVector B) := by
    change mixedMoment B node4740 node4740Labels = _
    exact sound4740 B hB hF
  have h4746 : mixedVector B (Sum.inr 4746) = Sparse.eval nodeValue4746 (mixedVector B) := by
    change mixedMoment B node4746 node4746Labels = _
    exact sound4746 B hB hF
  have h4752 : mixedVector B (Sum.inr 4752) = Sparse.eval nodeValue4752 (mixedVector B) := by
    change mixedMoment B node4752 node4752Labels = _
    exact sound4752 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4805 : mixedVector B (Sum.inr 4805) = Sparse.eval nodeValue4805 (mixedVector B) := by
    change mixedMoment B node4805 node4805Labels = _
    exact sound4805 B hB hF
  have h4838 : mixedVector B (Sum.inr 4838) = Sparse.eval nodeValue4838 (mixedVector B) := by
    change mixedMoment B node4838 node4838Labels = _
    exact sound4838 B hB hF
  have h4998 : mixedVector B (Sum.inr 4998) = Sparse.eval nodeValue4998 (mixedVector B) := by
    change mixedMoment B node4998 node4998Labels = _
    exact sound4998 B hB hF
  have h5073 : mixedVector B (Sum.inr 5073) = Sparse.eval nodeValue5073 (mixedVector B) := by
    change mixedMoment B node5073 node5073Labels = _
    exact sound5073 B hB hF
  have h5076 : mixedVector B (Sum.inr 5076) = Sparse.eval nodeValue5076 (mixedVector B) := by
    change mixedMoment B node5076 node5076Labels = _
    exact sound5076 B hB hF
  have h5104 : mixedVector B (Sum.inr 5104) = Sparse.eval nodeValue5104 (mixedVector B) := by
    change mixedMoment B node5104 node5104Labels = _
    exact sound5104 B hB hF
  simpa only [sourceForm2495, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4080, h4300, h4301, h4307, h4417, h4641, h4642, h4648, h4736, h4737, h4740, h4746, h4752, h4802, h4805, h4838, h4998, h5073, h5076, h5104, reducedSource2011] using sourceEq2495 B hB

theorem rowSound2011_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2011 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2011, numericCheck2011, reducedZero2011 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011_e_oai
