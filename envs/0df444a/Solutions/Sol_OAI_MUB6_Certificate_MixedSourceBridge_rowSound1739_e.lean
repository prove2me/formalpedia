-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:55:39.860016+00:00
-- url     : https://prove2.me/submissions/680d5b53-9c2d-4522-a64e-a78293117969

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
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

theorem canonical1527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1527 raw1527Labels = mixedMoment B node4657 node4657Labels := by
  calc
    mixedMoment B raw1527 raw1527Labels = mixedMoment B raw1527step0 raw1527step0Labels := by
      have ha : raw1527step0 = (fun i j => raw1527 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1527step0 raw1527; decide +kernel
      have hl : raw1527step0Labels = raw1527Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1527 raw1527Labels permutation8 permutation4
    mixedMoment B raw1527step0 raw1527step0Labels = mixedMoment B raw1527step1 raw1527step1Labels := by
      have ha : raw1527step1 = raw1527step0 := by apply Matrix.ext; unfold raw1527step1 raw1527step0; decide +kernel
      have hl : raw1527step0Labels = labelEmbedding7 ∘ raw1527step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1527step0 raw1527step0Labels raw1527step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4657 node4657Labels := by rfl

theorem canonical1528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1528 raw1528Labels = mixedMoment B node1783 node1783Labels := by
  calc
    mixedMoment B raw1528 raw1528Labels = mixedMoment B raw1528step0 raw1528step0Labels := by
      have ha : raw1528step0 = (fun i j => raw1528 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1528step0 raw1528; decide +kernel
      have hl : raw1528step0Labels = raw1528Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1528 raw1528Labels permutation8 permutation4
    _ = mixedMoment B node1783 node1783Labels := by rfl

theorem canonical1529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1529 raw1529Labels = mixedMoment B node1857 node1857Labels := by
  calc
    mixedMoment B raw1529 raw1529Labels = mixedMoment B raw1529step0 raw1529step0Labels := by
      have ha : raw1529step0 = (fun i j => raw1529 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1529step0 raw1529; decide +kernel
      have hl : raw1529step0Labels = raw1529Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1529 raw1529Labels permutation9 permutation6
    mixedMoment B raw1529step0 raw1529step0Labels = mixedMoment B raw1529step1 raw1529step1Labels := by
      have ha : raw1529step1 = -raw1529step0 := by apply Matrix.ext; change ∀ i j, raw1529step1 i j = -(raw1529step0 i j); unfold raw1529step1 raw1529step0; decide +kernel
      have hl : raw1529step1Labels = raw1529step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1529step1 raw1529step1Labels = mixedMoment B raw1529step2 raw1529step2Labels := by
      have ha : raw1529step2 = raw1529step1 := by apply Matrix.ext; unfold raw1529step2 raw1529step1; decide +kernel
      have hl : raw1529step1Labels = labelEmbedding1 ∘ raw1529step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1529step1 raw1529step1Labels raw1529step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1857 node1857Labels := by rfl

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

theorem canonical1614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1614 raw1614Labels = mixedMoment B node4719 node4719Labels := by
  calc
    mixedMoment B raw1614 raw1614Labels = mixedMoment B raw1614step0 raw1614step0Labels := by
      have ha : raw1614step0 = (fun i j => raw1614 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1614step0 raw1614; decide +kernel
      have hl : raw1614step0Labels = raw1614Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1614 raw1614Labels permutation32 permutation4
    mixedMoment B raw1614step0 raw1614step0Labels = mixedMoment B raw1614step1 raw1614step1Labels := by
      have ha : raw1614step1 = raw1614step0 := by apply Matrix.ext; unfold raw1614step1 raw1614step0; decide +kernel
      have hl : raw1614step0Labels = labelEmbedding7 ∘ raw1614step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1614step0 raw1614step0Labels raw1614step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4719 node4719Labels := by rfl

theorem canonical1615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1615 raw1615Labels = mixedMoment B node1873 node1873Labels := by
  calc
    mixedMoment B raw1615 raw1615Labels = mixedMoment B raw1615step0 raw1615step0Labels := by
      have ha : raw1615step0 = (fun i j => raw1615 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1615step0 raw1615; decide +kernel
      have hl : raw1615step0Labels = raw1615Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1615 raw1615Labels permutation32 permutation4
    _ = mixedMoment B node1873 node1873Labels := by rfl

theorem canonical1616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1616 raw1616Labels = mixedMoment B node1893 node1893Labels := by
  calc
    mixedMoment B raw1616 raw1616Labels = mixedMoment B raw1616step0 raw1616step0Labels := by
      have ha : raw1616step0 = (fun i j => raw1616 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1616step0 raw1616; decide +kernel
      have hl : raw1616step0Labels = raw1616Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1616 raw1616Labels permutation33 permutation6
    mixedMoment B raw1616step0 raw1616step0Labels = mixedMoment B raw1616step1 raw1616step1Labels := by
      have ha : raw1616step1 = -raw1616step0 := by apply Matrix.ext; change ∀ i j, raw1616step1 i j = -(raw1616step0 i j); unfold raw1616step1 raw1616step0; decide +kernel
      have hl : raw1616step1Labels = raw1616step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1616step1 raw1616step1Labels = mixedMoment B raw1616step2 raw1616step2Labels := by
      have ha : raw1616step2 = raw1616step1 := by apply Matrix.ext; unfold raw1616step2 raw1616step1; decide +kernel
      have hl : raw1616step1Labels = labelEmbedding1 ∘ raw1616step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1616step1 raw1616step1Labels raw1616step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1893 node1893Labels := by rfl

theorem canonical1659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1659 raw1659Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw1659 raw1659Labels = mixedMoment B raw1659step0 raw1659step0Labels := by
      have ha : raw1659step0 = (fun i j => raw1659 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1659step0 raw1659; decide +kernel
      have hl : raw1659step0Labels = raw1659Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1659 raw1659Labels permutation32 permutation4
    mixedMoment B raw1659step0 raw1659step0Labels = mixedMoment B raw1659step1 raw1659step1Labels := by
      have ha : raw1659step1 = raw1659step0 := by apply Matrix.ext; unfold raw1659step1 raw1659step0; decide +kernel
      have hl : raw1659step0Labels = labelEmbedding7 ∘ raw1659step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1659step0 raw1659step0Labels raw1659step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

theorem canonical1660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1660 raw1660Labels = mixedMoment B node1915 node1915Labels := by
  calc
    mixedMoment B raw1660 raw1660Labels = mixedMoment B raw1660step0 raw1660step0Labels := by
      have ha : raw1660step0 = (fun i j => raw1660 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1660step0 raw1660; decide +kernel
      have hl : raw1660step0Labels = raw1660Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1660 raw1660Labels permutation32 permutation4
    _ = mixedMoment B node1915 node1915Labels := by rfl

theorem canonical1661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1661 raw1661Labels = mixedMoment B node1946 node1946Labels := by
  calc
    mixedMoment B raw1661 raw1661Labels = mixedMoment B raw1661step0 raw1661step0Labels := by
      have ha : raw1661step0 = (fun i j => raw1661 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1661step0 raw1661; decide +kernel
      have hl : raw1661step0Labels = raw1661Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1661 raw1661Labels permutation33 permutation6
    mixedMoment B raw1661step0 raw1661step0Labels = mixedMoment B raw1661step1 raw1661step1Labels := by
      have ha : raw1661step1 = -raw1661step0 := by apply Matrix.ext; change ∀ i j, raw1661step1 i j = -(raw1661step0 i j); unfold raw1661step1 raw1661step0; decide +kernel
      have hl : raw1661step1Labels = raw1661step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1661step1 raw1661step1Labels = mixedMoment B raw1661step2 raw1661step2Labels := by
      have ha : raw1661step2 = raw1661step1 := by apply Matrix.ext; unfold raw1661step2 raw1661step1; decide +kernel
      have hl : raw1661step1Labels = labelEmbedding1 ∘ raw1661step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1661step1 raw1661step1Labels raw1661step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1946 node1946Labels := by rfl

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

theorem canonical1677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1677 raw1677Labels = mixedMoment B node4754 node4754Labels := by
  calc
    mixedMoment B raw1677 raw1677Labels = mixedMoment B raw1677step0 raw1677step0Labels := by
      have ha : raw1677step0 = (fun i j => raw1677 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1677step0 raw1677; decide +kernel
      have hl : raw1677step0Labels = raw1677Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1677 raw1677Labels permutation8 permutation4
    mixedMoment B raw1677step0 raw1677step0Labels = mixedMoment B raw1677step1 raw1677step1Labels := by
      have ha : raw1677step1 = raw1677step0 := by apply Matrix.ext; unfold raw1677step1 raw1677step0; decide +kernel
      have hl : raw1677step0Labels = labelEmbedding7 ∘ raw1677step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1677step0 raw1677step0Labels raw1677step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4754 node4754Labels := by rfl

theorem canonical1678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1678 raw1678Labels = mixedMoment B node1951 node1951Labels := by
  calc
    mixedMoment B raw1678 raw1678Labels = mixedMoment B raw1678step0 raw1678step0Labels := by
      have ha : raw1678step0 = (fun i j => raw1678 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1678step0 raw1678; decide +kernel
      have hl : raw1678step0Labels = raw1678Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1678 raw1678Labels permutation8 permutation4
    _ = mixedMoment B node1951 node1951Labels := by rfl

theorem canonical1679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1679 raw1679Labels = mixedMoment B node1951 node1951Labels := by
  calc
    mixedMoment B raw1679 raw1679Labels = mixedMoment B raw1679step0 raw1679step0Labels := by
      have ha : raw1679step0 = (fun i j => raw1679 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1679step0 raw1679; decide +kernel
      have hl : raw1679step0Labels = raw1679Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1679 raw1679Labels permutation9 permutation6
    mixedMoment B raw1679step0 raw1679step0Labels = mixedMoment B raw1679step1 raw1679step1Labels := by
      have ha : raw1679step1 = -raw1679step0 := by apply Matrix.ext; change ∀ i j, raw1679step1 i j = -(raw1679step0 i j); unfold raw1679step1 raw1679step0; decide +kernel
      have hl : raw1679step1Labels = raw1679step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1679step1 raw1679step1Labels = mixedMoment B raw1679step2 raw1679step2Labels := by
      have ha : raw1679step2 = raw1679step1 := by apply Matrix.ext; unfold raw1679step2 raw1679step1; decide +kernel
      have hl : raw1679step1Labels = labelEmbedding1 ∘ raw1679step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1679step1 raw1679step1Labels raw1679step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1951 node1951Labels := by rfl

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

theorem canonical1773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1773 raw1773Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw1773 raw1773Labels = mixedMoment B raw1773step0 raw1773step0Labels := by
      have ha : raw1773step0 = (fun i j => raw1773 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1773step0 raw1773; decide +kernel
      have hl : raw1773step0Labels = raw1773Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1773 raw1773Labels permutation8 permutation4
    mixedMoment B raw1773step0 raw1773step0Labels = mixedMoment B raw1773step1 raw1773step1Labels := by
      have ha : raw1773step1 = raw1773step0 := by apply Matrix.ext; unfold raw1773step1 raw1773step0; decide +kernel
      have hl : raw1773step0Labels = labelEmbedding7 ∘ raw1773step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1773step0 raw1773step0Labels raw1773step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

theorem canonical1774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1774 raw1774Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw1774 raw1774Labels = mixedMoment B raw1774step0 raw1774step0Labels := by
      have ha : raw1774step0 = (fun i j => raw1774 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1774step0 raw1774; decide +kernel
      have hl : raw1774step0Labels = raw1774Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1774 raw1774Labels permutation8 permutation4
    _ = mixedMoment B node2062 node2062Labels := by rfl

theorem canonical1775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1775 raw1775Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw1775 raw1775Labels = mixedMoment B raw1775step0 raw1775step0Labels := by
      have ha : raw1775step0 = (fun i j => raw1775 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1775step0 raw1775; decide +kernel
      have hl : raw1775step0Labels = raw1775Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1775 raw1775Labels permutation9 permutation6
    mixedMoment B raw1775step0 raw1775step0Labels = mixedMoment B raw1775step1 raw1775step1Labels := by
      have ha : raw1775step1 = -raw1775step0 := by apply Matrix.ext; change ∀ i j, raw1775step1 i j = -(raw1775step0 i j); unfold raw1775step1 raw1775step0; decide +kernel
      have hl : raw1775step1Labels = raw1775step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1775step1 raw1775step1Labels = mixedMoment B raw1775step2 raw1775step2Labels := by
      have ha : raw1775step2 = raw1775step1 := by apply Matrix.ext; unfold raw1775step2 raw1775step1; decide +kernel
      have hl : raw1775step1Labels = labelEmbedding1 ∘ raw1775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1775step1 raw1775step1Labels raw1775step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

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

theorem canonical2013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2013 raw2013Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw2013 raw2013Labels = mixedMoment B raw2013step0 raw2013step0Labels := by
      have ha : raw2013step0 = (fun i j => raw2013 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2013step0 raw2013; decide +kernel
      have hl : raw2013step0Labels = raw2013Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2013 raw2013Labels permutation32 permutation4
    mixedMoment B raw2013step0 raw2013step0Labels = mixedMoment B raw2013step1 raw2013step1Labels := by
      have ha : raw2013step1 = raw2013step0 := by apply Matrix.ext; unfold raw2013step1 raw2013step0; decide +kernel
      have hl : raw2013step0Labels = labelEmbedding7 ∘ raw2013step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2013step0 raw2013step0Labels raw2013step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

theorem canonical2014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2014 raw2014Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw2014 raw2014Labels = mixedMoment B raw2014step0 raw2014step0Labels := by
      have ha : raw2014step0 = (fun i j => raw2014 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2014step0 raw2014; decide +kernel
      have hl : raw2014step0Labels = raw2014Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2014 raw2014Labels permutation32 permutation4
    _ = mixedMoment B node2385 node2385Labels := by rfl

theorem canonical2015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2015 raw2015Labels = mixedMoment B node3353 node3353Labels := by
  calc
    mixedMoment B raw2015 raw2015Labels = mixedMoment B raw2015step0 raw2015step0Labels := by
      have ha : raw2015step0 = (fun i j => raw2015 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2015step0 raw2015; decide +kernel
      have hl : raw2015step0Labels = raw2015Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2015 raw2015Labels permutation32 permutation6
    mixedMoment B raw2015step0 raw2015step0Labels = mixedMoment B raw2015step1 raw2015step1Labels := by
      have ha : raw2015step1 = -raw2015step0 := by apply Matrix.ext; change ∀ i j, raw2015step1 i j = -(raw2015step0 i j); unfold raw2015step1 raw2015step0; decide +kernel
      have hl : raw2015step1Labels = raw2015step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2015step1 raw2015step1Labels = mixedMoment B raw2015step2 raw2015step2Labels := by
      have ha : raw2015step2 = raw2015step1 := by apply Matrix.ext; unfold raw2015step2 raw2015step1; decide +kernel
      have hl : raw2015step1Labels = labelEmbedding1 ∘ raw2015step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2015step1 raw2015step1Labels raw2015step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3353 node3353Labels := by rfl

theorem canonical2031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2031 raw2031Labels = mixedMoment B node5021 node5021Labels := by
  calc
    mixedMoment B raw2031 raw2031Labels = mixedMoment B raw2031step0 raw2031step0Labels := by
      have ha : raw2031step0 = (fun i j => raw2031 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2031step0 raw2031; decide +kernel
      have hl : raw2031step0Labels = raw2031Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2031 raw2031Labels permutation8 permutation4
    mixedMoment B raw2031step0 raw2031step0Labels = mixedMoment B raw2031step1 raw2031step1Labels := by
      have ha : raw2031step1 = raw2031step0 := by apply Matrix.ext; unfold raw2031step1 raw2031step0; decide +kernel
      have hl : raw2031step0Labels = labelEmbedding7 ∘ raw2031step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2031step0 raw2031step0Labels raw2031step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5021 node5021Labels := by rfl

theorem canonical2032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2032 raw2032Labels = mixedMoment B node2407 node2407Labels := by
  calc
    mixedMoment B raw2032 raw2032Labels = mixedMoment B raw2032step0 raw2032step0Labels := by
      have ha : raw2032step0 = (fun i j => raw2032 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2032step0 raw2032; decide +kernel
      have hl : raw2032step0Labels = raw2032Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2032 raw2032Labels permutation8 permutation4
    _ = mixedMoment B node2407 node2407Labels := by rfl

theorem canonical2033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2033 raw2033Labels = mixedMoment B node3360 node3360Labels := by
  calc
    mixedMoment B raw2033 raw2033Labels = mixedMoment B raw2033step0 raw2033step0Labels := by
      have ha : raw2033step0 = (fun i j => raw2033 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2033step0 raw2033; decide +kernel
      have hl : raw2033step0Labels = raw2033Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2033 raw2033Labels permutation31 permutation6
    mixedMoment B raw2033step0 raw2033step0Labels = mixedMoment B raw2033step1 raw2033step1Labels := by
      have ha : raw2033step1 = raw2033step0 := by apply Matrix.ext; unfold raw2033step1 raw2033step0; decide +kernel
      have hl : raw2033step0Labels = labelEmbedding1 ∘ raw2033step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2033step0 raw2033step0Labels raw2033step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3360 node3360Labels := by rfl

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

theorem canonical2133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2133 raw2133Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw2133 raw2133Labels = mixedMoment B raw2133step0 raw2133step0Labels := by
      have ha : raw2133step0 = (fun i j => raw2133 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2133step0 raw2133; decide +kernel
      have hl : raw2133step0Labels = raw2133Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2133 raw2133Labels permutation8 permutation4
    mixedMoment B raw2133step0 raw2133step0Labels = mixedMoment B raw2133step1 raw2133step1Labels := by
      have ha : raw2133step1 = raw2133step0 := by apply Matrix.ext; unfold raw2133step1 raw2133step0; decide +kernel
      have hl : raw2133step0Labels = labelEmbedding7 ∘ raw2133step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2133step0 raw2133step0Labels raw2133step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

theorem canonical2134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2134 raw2134Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw2134 raw2134Labels = mixedMoment B raw2134step0 raw2134step0Labels := by
      have ha : raw2134step0 = (fun i j => raw2134 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2134step0 raw2134; decide +kernel
      have hl : raw2134step0Labels = raw2134Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2134 raw2134Labels permutation8 permutation4
    _ = mixedMoment B node2519 node2519Labels := by rfl

theorem canonical2135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2135 raw2135Labels = mixedMoment B node3486 node3486Labels := by
  calc
    mixedMoment B raw2135 raw2135Labels = mixedMoment B raw2135step0 raw2135step0Labels := by
      have ha : raw2135step0 = (fun i j => raw2135 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2135step0 raw2135; decide +kernel
      have hl : raw2135step0Labels = raw2135Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2135 raw2135Labels permutation9 permutation6
    mixedMoment B raw2135step0 raw2135step0Labels = mixedMoment B raw2135step1 raw2135step1Labels := by
      have ha : raw2135step1 = -raw2135step0 := by apply Matrix.ext; change ∀ i j, raw2135step1 i j = -(raw2135step0 i j); unfold raw2135step1 raw2135step0; decide +kernel
      have hl : raw2135step1Labels = raw2135step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2135step1 raw2135step1Labels = mixedMoment B raw2135step2 raw2135step2Labels := by
      have ha : raw2135step2 = raw2135step1 := by apply Matrix.ext; unfold raw2135step2 raw2135step1; decide +kernel
      have hl : raw2135step1Labels = labelEmbedding1 ∘ raw2135step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2135step1 raw2135step1Labels raw2135step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3486 node3486Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical216
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27664 raw27664Labels = mixedMoment B node5107 node5107Labels := by
  calc
    mixedMoment B raw27664 raw27664Labels = mixedMoment B raw27664step0 raw27664step0Labels := by
      have hz : ∀ j, raw27664 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27664step0 = (fun i j => raw27664 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27664step0 raw27664; decide +kernel
      have hl : raw27664step0Labels = raw27664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27664 raw27664Labels permutation434 hz
    mixedMoment B raw27664step0 raw27664step0Labels = mixedMoment B raw27664step1 raw27664step1Labels := by
      have hz : ∀ j, raw27664step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27664step1 = (fun i j => raw27664step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27664step1 raw27664step0; decide +kernel
      have hl : raw27664step1Labels = raw27664step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27664step0 raw27664step0Labels permutation80 hz
    mixedMoment B raw27664step1 raw27664step1Labels = mixedMoment B raw27664step2 raw27664step2Labels := by
      have ha : raw27664step2 = (fun i j => raw27664step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27664step2 raw27664step1; decide +kernel
      have hl : raw27664step2Labels = raw27664step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27664step1 raw27664step1Labels permutation8 permutation6
    mixedMoment B raw27664step2 raw27664step2Labels = mixedMoment B raw27664step3 raw27664step3Labels := by
      have ha : raw27664step3 = raw27664step2 := by apply Matrix.ext; unfold raw27664step3 raw27664step2; decide +kernel
      have hl : raw27664step2Labels = labelEmbedding9 ∘ raw27664step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27664step2 raw27664step2Labels raw27664step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5107 node5107Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical224
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28679 raw28679Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw28679 raw28679Labels = mixedMoment B raw28679step0 raw28679step0Labels := by
      have hz : ∀ j, raw28679 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28679step0 = (fun i j => raw28679 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28679step0 raw28679; decide +kernel
      have hl : raw28679step0Labels = raw28679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28679 raw28679Labels permutation434 hz
    mixedMoment B raw28679step0 raw28679step0Labels = mixedMoment B raw28679step1 raw28679step1Labels := by
      have hz : ∀ j, raw28679step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28679step1 = (fun i j => raw28679step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28679step1 raw28679step0; decide +kernel
      have hl : raw28679step1Labels = raw28679step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28679step0 raw28679step0Labels permutation80 hz
    mixedMoment B raw28679step1 raw28679step1Labels = mixedMoment B raw28679step2 raw28679step2Labels := by
      have ha : raw28679step2 = (fun i j => raw28679step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28679step2 raw28679step1; decide +kernel
      have hl : raw28679step2Labels = raw28679step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28679step1 raw28679step1Labels permutation31 permutation6
    mixedMoment B raw28679step2 raw28679step2Labels = mixedMoment B raw28679step3 raw28679step3Labels := by
      have ha : raw28679step3 = -raw28679step2 := by apply Matrix.ext; change ∀ i j, raw28679step3 i j = -(raw28679step2 i j); unfold raw28679step3 raw28679step2; decide +kernel
      have hl : raw28679step3Labels = raw28679step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28679step3 raw28679step3Labels = mixedMoment B raw28679step4 raw28679step4Labels := by
      have ha : raw28679step4 = raw28679step3 := by apply Matrix.ext; unfold raw28679step4 raw28679step3; decide +kernel
      have hl : raw28679step3Labels = labelEmbedding9 ∘ raw28679step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28679step3 raw28679step3Labels raw28679step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4841 node4841Labels := by rfl

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

theorem canonical28815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28815 raw28815Labels = mixedMoment B node4741 node4741Labels := by
  calc
    mixedMoment B raw28815 raw28815Labels = mixedMoment B raw28815step0 raw28815step0Labels := by
      have hz : ∀ j, raw28815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28815step0 = (fun i j => raw28815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28815step0 raw28815; decide +kernel
      have hl : raw28815step0Labels = raw28815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28815 raw28815Labels permutation346 hz
    mixedMoment B raw28815step0 raw28815step0Labels = mixedMoment B raw28815step1 raw28815step1Labels := by
      have ha : raw28815step1 = (fun i j => raw28815step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28815step1 raw28815step0; decide +kernel
      have hl : raw28815step1Labels = raw28815step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28815step0 raw28815step0Labels permutation151 permutation6
    mixedMoment B raw28815step1 raw28815step1Labels = mixedMoment B raw28815step2 raw28815step2Labels := by
      have ha : raw28815step2 = -raw28815step1 := by apply Matrix.ext; change ∀ i j, raw28815step2 i j = -(raw28815step1 i j); unfold raw28815step2 raw28815step1; decide +kernel
      have hl : raw28815step2Labels = raw28815step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28815step2 raw28815step2Labels = mixedMoment B raw28815step3 raw28815step3Labels := by
      have ha : raw28815step3 = raw28815step2 := by apply Matrix.ext; unfold raw28815step3 raw28815step2; decide +kernel
      have hl : raw28815step2Labels = labelEmbedding9 ∘ raw28815step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28815step2 raw28815step2Labels raw28815step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4741 node4741Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical227
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29176 raw29176Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw29176 raw29176Labels = mixedMoment B raw29176step0 raw29176step0Labels := by
      have hz : ∀ j, raw29176 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29176step0 = (fun i j => raw29176 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29176step0 raw29176; decide +kernel
      have hl : raw29176step0Labels = raw29176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29176 raw29176Labels permutation346 hz
    mixedMoment B raw29176step0 raw29176step0Labels = mixedMoment B raw29176step1 raw29176step1Labels := by
      have ha : raw29176step1 = (fun i j => raw29176step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29176step1 raw29176step0; decide +kernel
      have hl : raw29176step1Labels = raw29176step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29176step0 raw29176step0Labels permutation151 permutation6
    mixedMoment B raw29176step1 raw29176step1Labels = mixedMoment B raw29176step2 raw29176step2Labels := by
      have ha : raw29176step2 = -raw29176step1 := by apply Matrix.ext; change ∀ i j, raw29176step2 i j = -(raw29176step1 i j); unfold raw29176step2 raw29176step1; decide +kernel
      have hl : raw29176step2Labels = raw29176step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29176step2 raw29176step2Labels = mixedMoment B raw29176step3 raw29176step3Labels := by
      have ha : raw29176step3 = raw29176step2 := by apply Matrix.ext; unfold raw29176step3 raw29176step2; decide +kernel
      have hl : raw29176step2Labels = labelEmbedding9 ∘ raw29176step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29176step2 raw29176step2Labels raw29176step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

theorem canonical29180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29180 raw29180Labels = mixedMoment B node4710 node4710Labels := by
  calc
    mixedMoment B raw29180 raw29180Labels = mixedMoment B raw29180step0 raw29180step0Labels := by
      have ha : raw29180step0 = (fun i j => raw29180 (permutation682 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29180step0 raw29180; decide +kernel
      have hl : raw29180step0Labels = raw29180Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29180 raw29180Labels permutation682 permutation4
    mixedMoment B raw29180step0 raw29180step0Labels = mixedMoment B raw29180step1 raw29180step1Labels := by
      have ha : raw29180step1 = raw29180step0 := by apply Matrix.ext; unfold raw29180step1 raw29180step0; decide +kernel
      have hl : raw29180step0Labels = labelEmbedding7 ∘ raw29180step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29180step0 raw29180step0Labels raw29180step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4710 node4710Labels := by rfl

theorem canonical29182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29182 raw29182Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw29182 raw29182Labels = mixedMoment B raw29182step0 raw29182step0Labels := by
      have hz : ∀ j, raw29182 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29182step0 = (fun i j => raw29182 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29182step0 raw29182; decide +kernel
      have hl : raw29182step0Labels = raw29182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29182 raw29182Labels permutation434 hz
    mixedMoment B raw29182step0 raw29182step0Labels = mixedMoment B raw29182step1 raw29182step1Labels := by
      have hz : ∀ j, raw29182step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29182step1 = (fun i j => raw29182step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29182step1 raw29182step0; decide +kernel
      have hl : raw29182step1Labels = raw29182step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29182step0 raw29182step0Labels permutation80 hz
    mixedMoment B raw29182step1 raw29182step1Labels = mixedMoment B raw29182step2 raw29182step2Labels := by
      have hz : ∀ i, raw29182step1 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw29182step2 = (fun i j => raw29182step1 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw29182step2 raw29182step1; decide +kernel
      have hl : raw29182step2Labels = (fun j => raw29182step1Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29182step1 raw29182step1Labels permutation2 hz
    mixedMoment B raw29182step2 raw29182step2Labels = mixedMoment B raw29182step3 raw29182step3Labels := by
      have ha : raw29182step3 = (fun i j => raw29182step2 (permutation31 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29182step3 raw29182step2; decide +kernel
      have hl : raw29182step3Labels = raw29182step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29182step2 raw29182step2Labels permutation31 permutation0
    mixedMoment B raw29182step3 raw29182step3Labels = mixedMoment B raw29182step4 raw29182step4Labels := by
      have ha : raw29182step4 = raw29182step3 := by apply Matrix.ext; unfold raw29182step4 raw29182step3; decide +kernel
      have hl : raw29182step3Labels = labelEmbedding3 ∘ raw29182step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29182step3 raw29182step3Labels raw29182step4Labels labelEmbedding3 hl
    _ = mixedMoment B node4081 node4081Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical228
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29184 raw29184Labels = mixedMoment B node4741 node4741Labels := by
  calc
    mixedMoment B raw29184 raw29184Labels = mixedMoment B raw29184step0 raw29184step0Labels := by
      have hz : ∀ j, raw29184 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29184step0 = (fun i j => raw29184 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29184step0 raw29184; decide +kernel
      have hl : raw29184step0Labels = raw29184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29184 raw29184Labels permutation434 hz
    mixedMoment B raw29184step0 raw29184step0Labels = mixedMoment B raw29184step1 raw29184step1Labels := by
      have ha : raw29184step1 = (fun i j => raw29184step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29184step1 raw29184step0; decide +kernel
      have hl : raw29184step1Labels = raw29184step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29184step0 raw29184step0Labels permutation151 permutation6
    mixedMoment B raw29184step1 raw29184step1Labels = mixedMoment B raw29184step2 raw29184step2Labels := by
      have ha : raw29184step2 = -raw29184step1 := by apply Matrix.ext; change ∀ i j, raw29184step2 i j = -(raw29184step1 i j); unfold raw29184step2 raw29184step1; decide +kernel
      have hl : raw29184step2Labels = raw29184step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29184step2 raw29184step2Labels = mixedMoment B raw29184step3 raw29184step3Labels := by
      have ha : raw29184step3 = raw29184step2 := by apply Matrix.ext; unfold raw29184step3 raw29184step2; decide +kernel
      have hl : raw29184step2Labels = labelEmbedding9 ∘ raw29184step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29184step2 raw29184step2Labels raw29184step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4741 node4741Labels := by rfl

theorem canonical29186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29186 raw29186Labels = mixedMoment B node4645 node4645Labels := by
  calc
    mixedMoment B raw29186 raw29186Labels = mixedMoment B raw29186step0 raw29186step0Labels := by
      have hz : ∀ j, raw29186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29186step0 = (fun i j => raw29186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29186step0 raw29186; decide +kernel
      have hl : raw29186step0Labels = raw29186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29186 raw29186Labels permutation346 hz
    mixedMoment B raw29186step0 raw29186step0Labels = mixedMoment B raw29186step1 raw29186step1Labels := by
      have ha : raw29186step1 = (fun i j => raw29186step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29186step1 raw29186step0; decide +kernel
      have hl : raw29186step1Labels = raw29186step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29186step0 raw29186step0Labels permutation151 permutation4
    mixedMoment B raw29186step1 raw29186step1Labels = mixedMoment B raw29186step2 raw29186step2Labels := by
      have ha : raw29186step2 = raw29186step1 := by apply Matrix.ext; unfold raw29186step2 raw29186step1; decide +kernel
      have hl : raw29186step1Labels = labelEmbedding7 ∘ raw29186step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29186step1 raw29186step1Labels raw29186step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4645 node4645Labels := by rfl

theorem canonical29190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29190 raw29190Labels = mixedMoment B node4304 node4304Labels := by
  calc
    mixedMoment B raw29190 raw29190Labels = mixedMoment B raw29190step0 raw29190step0Labels := by
      have hz : ∀ j, raw29190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29190step0 = (fun i j => raw29190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29190step0 raw29190; decide +kernel
      have hl : raw29190step0Labels = raw29190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29190 raw29190Labels permutation346 hz
    mixedMoment B raw29190step0 raw29190step0Labels = mixedMoment B raw29190step1 raw29190step1Labels := by
      have ha : raw29190step1 = (fun i j => raw29190step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29190step1 raw29190step0; decide +kernel
      have hl : raw29190step1Labels = raw29190step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29190step0 raw29190step0Labels permutation151 permutation4
    mixedMoment B raw29190step1 raw29190step1Labels = mixedMoment B raw29190step2 raw29190step2Labels := by
      have ha : raw29190step2 = raw29190step1 := by apply Matrix.ext; unfold raw29190step2 raw29190step1; decide +kernel
      have hl : raw29190step1Labels = labelEmbedding7 ∘ raw29190step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29190step1 raw29190step1Labels raw29190step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4304 node4304Labels := by rfl

theorem canonical29208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29208 raw29208Labels = mixedMoment B node4754 node4754Labels := by
  calc
    mixedMoment B raw29208 raw29208Labels = mixedMoment B raw29208step0 raw29208step0Labels := by
      have hz : ∀ j, raw29208 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29208step0 = (fun i j => raw29208 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29208step0 raw29208; decide +kernel
      have hl : raw29208step0Labels = raw29208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29208 raw29208Labels permutation434 hz
    mixedMoment B raw29208step0 raw29208step0Labels = mixedMoment B raw29208step1 raw29208step1Labels := by
      have hz : ∀ j, raw29208step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29208step1 = (fun i j => raw29208step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29208step1 raw29208step0; decide +kernel
      have hl : raw29208step1Labels = raw29208step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29208step0 raw29208step0Labels permutation80 hz
    mixedMoment B raw29208step1 raw29208step1Labels = mixedMoment B raw29208step2 raw29208step2Labels := by
      have ha : raw29208step2 = (fun i j => raw29208step1 (permutation30 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29208step2 raw29208step1; decide +kernel
      have hl : raw29208step2Labels = raw29208step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29208step1 raw29208step1Labels permutation30 permutation4
    mixedMoment B raw29208step2 raw29208step2Labels = mixedMoment B raw29208step3 raw29208step3Labels := by
      have ha : raw29208step3 = raw29208step2 := by apply Matrix.ext; unfold raw29208step3 raw29208step2; decide +kernel
      have hl : raw29208step2Labels = labelEmbedding7 ∘ raw29208step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29208step2 raw29208step2Labels raw29208step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4754 node4754Labels := by rfl

theorem canonical29209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29209 raw29209Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw29209 raw29209Labels = mixedMoment B raw29209step0 raw29209step0Labels := by
      have hz : ∀ j, raw29209 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29209step0 = (fun i j => raw29209 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29209step0 raw29209; decide +kernel
      have hl : raw29209step0Labels = raw29209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29209 raw29209Labels permutation434 hz
    mixedMoment B raw29209step0 raw29209step0Labels = mixedMoment B raw29209step1 raw29209step1Labels := by
      have ha : raw29209step1 = (fun i j => raw29209step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29209step1 raw29209step0; decide +kernel
      have hl : raw29209step1Labels = raw29209step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29209step0 raw29209step0Labels permutation151 permutation6
    mixedMoment B raw29209step1 raw29209step1Labels = mixedMoment B raw29209step2 raw29209step2Labels := by
      have ha : raw29209step2 = -raw29209step1 := by apply Matrix.ext; change ∀ i j, raw29209step2 i j = -(raw29209step1 i j); unfold raw29209step2 raw29209step1; decide +kernel
      have hl : raw29209step2Labels = raw29209step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29209step2 raw29209step2Labels = mixedMoment B raw29209step3 raw29209step3Labels := by
      have ha : raw29209step3 = raw29209step2 := by apply Matrix.ext; unfold raw29209step3 raw29209step2; decide +kernel
      have hl : raw29209step2Labels = labelEmbedding9 ∘ raw29209step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29209step2 raw29209step2Labels raw29209step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

theorem canonical29210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29210 raw29210Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw29210 raw29210Labels = mixedMoment B raw29210step0 raw29210step0Labels := by
      have hz : ∀ j, raw29210 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29210step0 = (fun i j => raw29210 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29210step0 raw29210; decide +kernel
      have hl : raw29210step0Labels = raw29210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29210 raw29210Labels permutation434 hz
    mixedMoment B raw29210step0 raw29210step0Labels = mixedMoment B raw29210step1 raw29210step1Labels := by
      have hz : ∀ j, raw29210step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29210step1 = (fun i j => raw29210step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29210step1 raw29210step0; decide +kernel
      have hl : raw29210step1Labels = raw29210step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29210step0 raw29210step0Labels permutation80 hz
    mixedMoment B raw29210step1 raw29210step1Labels = mixedMoment B raw29210step2 raw29210step2Labels := by
      have ha : raw29210step2 = (fun i j => raw29210step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29210step2 raw29210step1; decide +kernel
      have hl : raw29210step2Labels = raw29210step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29210step1 raw29210step1Labels permutation31 permutation6
    mixedMoment B raw29210step2 raw29210step2Labels = mixedMoment B raw29210step3 raw29210step3Labels := by
      have ha : raw29210step3 = -raw29210step2 := by apply Matrix.ext; change ∀ i j, raw29210step3 i j = -(raw29210step2 i j); unfold raw29210step3 raw29210step2; decide +kernel
      have hl : raw29210step3Labels = raw29210step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29210step3 raw29210step3Labels = mixedMoment B raw29210step4 raw29210step4Labels := by
      have ha : raw29210step4 = raw29210step3 := by apply Matrix.ext; unfold raw29210step4 raw29210step3; decide +kernel
      have hl : raw29210step3Labels = labelEmbedding9 ∘ raw29210step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29210step3 raw29210step3Labels raw29210step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

theorem canonical29211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29211 raw29211Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw29211 raw29211Labels = mixedMoment B raw29211step0 raw29211step0Labels := by
      have hz : ∀ j, raw29211 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29211step0 = (fun i j => raw29211 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29211step0 raw29211; decide +kernel
      have hl : raw29211step0Labels = raw29211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29211 raw29211Labels permutation434 hz
    mixedMoment B raw29211step0 raw29211step0Labels = mixedMoment B raw29211step1 raw29211step1Labels := by
      have hz : ∀ j, raw29211step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29211step1 = (fun i j => raw29211step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29211step1 raw29211step0; decide +kernel
      have hl : raw29211step1Labels = raw29211step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29211step0 raw29211step0Labels permutation80 hz
    mixedMoment B raw29211step1 raw29211step1Labels = mixedMoment B raw29211step2 raw29211step2Labels := by
      have ha : raw29211step2 = (fun i j => raw29211step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29211step2 raw29211step1; decide +kernel
      have hl : raw29211step2Labels = raw29211step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29211step1 raw29211step1Labels permutation31 permutation6
    mixedMoment B raw29211step2 raw29211step2Labels = mixedMoment B raw29211step3 raw29211step3Labels := by
      have ha : raw29211step3 = -raw29211step2 := by apply Matrix.ext; change ∀ i j, raw29211step3 i j = -(raw29211step2 i j); unfold raw29211step3 raw29211step2; decide +kernel
      have hl : raw29211step3Labels = raw29211step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29211step3 raw29211step3Labels = mixedMoment B raw29211step4 raw29211step4Labels := by
      have ha : raw29211step4 = raw29211step3 := by apply Matrix.ext; unfold raw29211step4 raw29211step3; decide +kernel
      have hl : raw29211step3Labels = labelEmbedding9 ∘ raw29211step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29211step3 raw29211step3Labels raw29211step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

theorem canonical29212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29212 raw29212Labels = mixedMoment B node4643 node4643Labels := by
  calc
    mixedMoment B raw29212 raw29212Labels = mixedMoment B raw29212step0 raw29212step0Labels := by
      have hz : ∀ j, raw29212 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29212step0 = (fun i j => raw29212 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29212step0 raw29212; decide +kernel
      have hl : raw29212step0Labels = raw29212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29212 raw29212Labels permutation434 hz
    mixedMoment B raw29212step0 raw29212step0Labels = mixedMoment B raw29212step1 raw29212step1Labels := by
      have ha : raw29212step1 = (fun i j => raw29212step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29212step1 raw29212step0; decide +kernel
      have hl : raw29212step1Labels = raw29212step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29212step0 raw29212step0Labels permutation32 permutation4
    mixedMoment B raw29212step1 raw29212step1Labels = mixedMoment B raw29212step2 raw29212step2Labels := by
      have ha : raw29212step2 = -raw29212step1 := by apply Matrix.ext; change ∀ i j, raw29212step2 i j = -(raw29212step1 i j); unfold raw29212step2 raw29212step1; decide +kernel
      have hl : raw29212step2Labels = raw29212step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29212step2 raw29212step2Labels = mixedMoment B raw29212step3 raw29212step3Labels := by
      have ha : raw29212step3 = raw29212step2 := by apply Matrix.ext; unfold raw29212step3 raw29212step2; decide +kernel
      have hl : raw29212step2Labels = labelEmbedding7 ∘ raw29212step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29212step2 raw29212step2Labels raw29212step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4643 node4643Labels := by rfl

theorem canonical29213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29213 raw29213Labels = mixedMoment B node4719 node4719Labels := by
  calc
    mixedMoment B raw29213 raw29213Labels = mixedMoment B raw29213step0 raw29213step0Labels := by
      have hz : ∀ j, raw29213 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29213step0 = (fun i j => raw29213 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29213step0 raw29213; decide +kernel
      have hl : raw29213step0Labels = raw29213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29213 raw29213Labels permutation434 hz
    mixedMoment B raw29213step0 raw29213step0Labels = mixedMoment B raw29213step1 raw29213step1Labels := by
      have ha : raw29213step1 = (fun i j => raw29213step0 (permutation150 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29213step1 raw29213step0; decide +kernel
      have hl : raw29213step1Labels = raw29213step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29213step0 raw29213step0Labels permutation150 permutation4
    mixedMoment B raw29213step1 raw29213step1Labels = mixedMoment B raw29213step2 raw29213step2Labels := by
      have ha : raw29213step2 = raw29213step1 := by apply Matrix.ext; unfold raw29213step2 raw29213step1; decide +kernel
      have hl : raw29213step1Labels = labelEmbedding7 ∘ raw29213step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29213step1 raw29213step1Labels raw29213step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4719 node4719Labels := by rfl

theorem canonical29214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29214 raw29214Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw29214 raw29214Labels = mixedMoment B raw29214step0 raw29214step0Labels := by
      have hz : ∀ j, raw29214 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29214step0 = (fun i j => raw29214 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29214step0 raw29214; decide +kernel
      have hl : raw29214step0Labels = raw29214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29214 raw29214Labels permutation434 hz
    mixedMoment B raw29214step0 raw29214step0Labels = mixedMoment B raw29214step1 raw29214step1Labels := by
      have ha : raw29214step1 = (fun i j => raw29214step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29214step1 raw29214step0; decide +kernel
      have hl : raw29214step1Labels = raw29214step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29214step0 raw29214step0Labels permutation151 permutation6
    mixedMoment B raw29214step1 raw29214step1Labels = mixedMoment B raw29214step2 raw29214step2Labels := by
      have ha : raw29214step2 = -raw29214step1 := by apply Matrix.ext; change ∀ i j, raw29214step2 i j = -(raw29214step1 i j); unfold raw29214step2 raw29214step1; decide +kernel
      have hl : raw29214step2Labels = raw29214step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29214step2 raw29214step2Labels = mixedMoment B raw29214step3 raw29214step3Labels := by
      have ha : raw29214step3 = raw29214step2 := by apply Matrix.ext; unfold raw29214step3 raw29214step2; decide +kernel
      have hl : raw29214step2Labels = labelEmbedding9 ∘ raw29214step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29214step2 raw29214step2Labels raw29214step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

theorem canonical29215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29215 raw29215Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw29215 raw29215Labels = mixedMoment B raw29215step0 raw29215step0Labels := by
      have hz : ∀ j, raw29215 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29215step0 = (fun i j => raw29215 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29215step0 raw29215; decide +kernel
      have hl : raw29215step0Labels = raw29215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29215 raw29215Labels permutation434 hz
    mixedMoment B raw29215step0 raw29215step0Labels = mixedMoment B raw29215step1 raw29215step1Labels := by
      have ha : raw29215step1 = (fun i j => raw29215step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29215step1 raw29215step0; decide +kernel
      have hl : raw29215step1Labels = raw29215step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29215step0 raw29215step0Labels permutation32 permutation6
    mixedMoment B raw29215step1 raw29215step1Labels = mixedMoment B raw29215step2 raw29215step2Labels := by
      have ha : raw29215step2 = raw29215step1 := by apply Matrix.ext; unfold raw29215step2 raw29215step1; decide +kernel
      have hl : raw29215step1Labels = labelEmbedding9 ∘ raw29215step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29215step1 raw29215step1Labels raw29215step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

theorem canonical29216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29216 raw29216Labels = mixedMoment B node4643 node4643Labels := by
  calc
    mixedMoment B raw29216 raw29216Labels = mixedMoment B raw29216step0 raw29216step0Labels := by
      have hz : ∀ j, raw29216 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29216step0 = (fun i j => raw29216 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29216step0 raw29216; decide +kernel
      have hl : raw29216step0Labels = raw29216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29216 raw29216Labels permutation346 hz
    mixedMoment B raw29216step0 raw29216step0Labels = mixedMoment B raw29216step1 raw29216step1Labels := by
      have ha : raw29216step1 = (fun i j => raw29216step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29216step1 raw29216step0; decide +kernel
      have hl : raw29216step1Labels = raw29216step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29216step0 raw29216step0Labels permutation32 permutation4
    mixedMoment B raw29216step1 raw29216step1Labels = mixedMoment B raw29216step2 raw29216step2Labels := by
      have ha : raw29216step2 = -raw29216step1 := by apply Matrix.ext; change ∀ i j, raw29216step2 i j = -(raw29216step1 i j); unfold raw29216step2 raw29216step1; decide +kernel
      have hl : raw29216step2Labels = raw29216step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29216step2 raw29216step2Labels = mixedMoment B raw29216step3 raw29216step3Labels := by
      have ha : raw29216step3 = raw29216step2 := by apply Matrix.ext; unfold raw29216step3 raw29216step2; decide +kernel
      have hl : raw29216step2Labels = labelEmbedding7 ∘ raw29216step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29216step2 raw29216step2Labels raw29216step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4643 node4643Labels := by rfl

theorem canonical29217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29217 raw29217Labels = mixedMoment B node4719 node4719Labels := by
  calc
    mixedMoment B raw29217 raw29217Labels = mixedMoment B raw29217step0 raw29217step0Labels := by
      have hz : ∀ j, raw29217 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29217step0 = (fun i j => raw29217 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29217step0 raw29217; decide +kernel
      have hl : raw29217step0Labels = raw29217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29217 raw29217Labels permutation346 hz
    mixedMoment B raw29217step0 raw29217step0Labels = mixedMoment B raw29217step1 raw29217step1Labels := by
      have ha : raw29217step1 = (fun i j => raw29217step0 (permutation150 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29217step1 raw29217step0; decide +kernel
      have hl : raw29217step1Labels = raw29217step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29217step0 raw29217step0Labels permutation150 permutation4
    mixedMoment B raw29217step1 raw29217step1Labels = mixedMoment B raw29217step2 raw29217step2Labels := by
      have ha : raw29217step2 = raw29217step1 := by apply Matrix.ext; unfold raw29217step2 raw29217step1; decide +kernel
      have hl : raw29217step1Labels = labelEmbedding7 ∘ raw29217step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29217step1 raw29217step1Labels raw29217step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4719 node4719Labels := by rfl

theorem canonical29218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29218 raw29218Labels = mixedMoment B node4710 node4710Labels := by
  calc
    mixedMoment B raw29218 raw29218Labels = mixedMoment B raw29218step0 raw29218step0Labels := by
      have ha : raw29218step0 = (fun i j => raw29218 (permutation688 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29218step0 raw29218; decide +kernel
      have hl : raw29218step0Labels = raw29218Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29218 raw29218Labels permutation688 permutation4
    mixedMoment B raw29218step0 raw29218step0Labels = mixedMoment B raw29218step1 raw29218step1Labels := by
      have ha : raw29218step1 = raw29218step0 := by apply Matrix.ext; unfold raw29218step1 raw29218step0; decide +kernel
      have hl : raw29218step0Labels = labelEmbedding7 ∘ raw29218step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29218step0 raw29218step0Labels raw29218step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4710 node4710Labels := by rfl

theorem canonical29219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29219 raw29219Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw29219 raw29219Labels = mixedMoment B raw29219step0 raw29219step0Labels := by
      have hz : ∀ j, raw29219 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29219step0 = (fun i j => raw29219 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29219step0 raw29219; decide +kernel
      have hl : raw29219step0Labels = raw29219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29219 raw29219Labels permutation346 hz
    mixedMoment B raw29219step0 raw29219step0Labels = mixedMoment B raw29219step1 raw29219step1Labels := by
      have ha : raw29219step1 = (fun i j => raw29219step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29219step1 raw29219step0; decide +kernel
      have hl : raw29219step1Labels = raw29219step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29219step0 raw29219step0Labels permutation151 permutation6
    mixedMoment B raw29219step1 raw29219step1Labels = mixedMoment B raw29219step2 raw29219step2Labels := by
      have ha : raw29219step2 = -raw29219step1 := by apply Matrix.ext; change ∀ i j, raw29219step2 i j = -(raw29219step1 i j); unfold raw29219step2 raw29219step1; decide +kernel
      have hl : raw29219step2Labels = raw29219step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29219step2 raw29219step2Labels = mixedMoment B raw29219step3 raw29219step3Labels := by
      have ha : raw29219step3 = raw29219step2 := by apply Matrix.ext; unfold raw29219step3 raw29219step2; decide +kernel
      have hl : raw29219step2Labels = labelEmbedding9 ∘ raw29219step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29219step2 raw29219step2Labels raw29219step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

theorem canonical29220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29220 raw29220Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw29220 raw29220Labels = mixedMoment B raw29220step0 raw29220step0Labels := by
      have hz : ∀ j, raw29220 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29220step0 = (fun i j => raw29220 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29220step0 raw29220; decide +kernel
      have hl : raw29220step0Labels = raw29220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29220 raw29220Labels permutation346 hz
    mixedMoment B raw29220step0 raw29220step0Labels = mixedMoment B raw29220step1 raw29220step1Labels := by
      have ha : raw29220step1 = (fun i j => raw29220step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29220step1 raw29220step0; decide +kernel
      have hl : raw29220step1Labels = raw29220step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29220step0 raw29220step0Labels permutation32 permutation6
    mixedMoment B raw29220step1 raw29220step1Labels = mixedMoment B raw29220step2 raw29220step2Labels := by
      have ha : raw29220step2 = raw29220step1 := by apply Matrix.ext; unfold raw29220step2 raw29220step1; decide +kernel
      have hl : raw29220step1Labels = labelEmbedding9 ∘ raw29220step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29220step1 raw29220step1Labels raw29220step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

theorem canonical29221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29221 raw29221Labels = mixedMoment B node4655 node4655Labels := by
  calc
    mixedMoment B raw29221 raw29221Labels = mixedMoment B raw29221step0 raw29221step0Labels := by
      have hz : ∀ j, raw29221 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29221step0 = (fun i j => raw29221 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29221step0 raw29221; decide +kernel
      have hl : raw29221step0Labels = raw29221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29221 raw29221Labels permutation434 hz
    mixedMoment B raw29221step0 raw29221step0Labels = mixedMoment B raw29221step1 raw29221step1Labels := by
      have hz : ∀ j, raw29221step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29221step1 = (fun i j => raw29221step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29221step1 raw29221step0; decide +kernel
      have hl : raw29221step1Labels = raw29221step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29221step0 raw29221step0Labels permutation80 hz
    mixedMoment B raw29221step1 raw29221step1Labels = mixedMoment B raw29221step2 raw29221step2Labels := by
      have ha : raw29221step2 = (fun i j => raw29221step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29221step2 raw29221step1; decide +kernel
      have hl : raw29221step2Labels = raw29221step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29221step1 raw29221step1Labels permutation31 permutation4
    mixedMoment B raw29221step2 raw29221step2Labels = mixedMoment B raw29221step3 raw29221step3Labels := by
      have ha : raw29221step3 = raw29221step2 := by apply Matrix.ext; unfold raw29221step3 raw29221step2; decide +kernel
      have hl : raw29221step2Labels = labelEmbedding7 ∘ raw29221step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29221step2 raw29221step2Labels raw29221step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4655 node4655Labels := by rfl

theorem canonical29222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29222 raw29222Labels = mixedMoment B node4657 node4657Labels := by
  calc
    mixedMoment B raw29222 raw29222Labels = mixedMoment B raw29222step0 raw29222step0Labels := by
      have hz : ∀ j, raw29222 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29222step0 = (fun i j => raw29222 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29222step0 raw29222; decide +kernel
      have hl : raw29222step0Labels = raw29222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29222 raw29222Labels permutation434 hz
    mixedMoment B raw29222step0 raw29222step0Labels = mixedMoment B raw29222step1 raw29222step1Labels := by
      have hz : ∀ j, raw29222step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29222step1 = (fun i j => raw29222step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29222step1 raw29222step0; decide +kernel
      have hl : raw29222step1Labels = raw29222step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29222step0 raw29222step0Labels permutation80 hz
    mixedMoment B raw29222step1 raw29222step1Labels = mixedMoment B raw29222step2 raw29222step2Labels := by
      have ha : raw29222step2 = (fun i j => raw29222step1 (permutation30 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29222step2 raw29222step1; decide +kernel
      have hl : raw29222step2Labels = raw29222step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29222step1 raw29222step1Labels permutation30 permutation4
    mixedMoment B raw29222step2 raw29222step2Labels = mixedMoment B raw29222step3 raw29222step3Labels := by
      have ha : raw29222step3 = raw29222step2 := by apply Matrix.ext; unfold raw29222step3 raw29222step2; decide +kernel
      have hl : raw29222step2Labels = labelEmbedding7 ∘ raw29222step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29222step2 raw29222step2Labels raw29222step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4657 node4657Labels := by rfl

theorem canonical29223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29223 raw29223Labels = mixedMoment B node4645 node4645Labels := by
  calc
    mixedMoment B raw29223 raw29223Labels = mixedMoment B raw29223step0 raw29223step0Labels := by
      have hz : ∀ j, raw29223 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29223step0 = (fun i j => raw29223 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29223step0 raw29223; decide +kernel
      have hl : raw29223step0Labels = raw29223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29223 raw29223Labels permutation434 hz
    mixedMoment B raw29223step0 raw29223step0Labels = mixedMoment B raw29223step1 raw29223step1Labels := by
      have ha : raw29223step1 = (fun i j => raw29223step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29223step1 raw29223step0; decide +kernel
      have hl : raw29223step1Labels = raw29223step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29223step0 raw29223step0Labels permutation151 permutation4
    mixedMoment B raw29223step1 raw29223step1Labels = mixedMoment B raw29223step2 raw29223step2Labels := by
      have ha : raw29223step2 = raw29223step1 := by apply Matrix.ext; unfold raw29223step2 raw29223step1; decide +kernel
      have hl : raw29223step1Labels = labelEmbedding7 ∘ raw29223step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29223step1 raw29223step1Labels raw29223step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4645 node4645Labels := by rfl

theorem canonical29224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29224 raw29224Labels = mixedMoment B node5021 node5021Labels := by
  calc
    mixedMoment B raw29224 raw29224Labels = mixedMoment B raw29224step0 raw29224step0Labels := by
      have hz : ∀ j, raw29224 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29224step0 = (fun i j => raw29224 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29224step0 raw29224; decide +kernel
      have hl : raw29224step0Labels = raw29224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29224 raw29224Labels permutation434 hz
    mixedMoment B raw29224step0 raw29224step0Labels = mixedMoment B raw29224step1 raw29224step1Labels := by
      have hz : ∀ j, raw29224step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29224step1 = (fun i j => raw29224step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29224step1 raw29224step0; decide +kernel
      have hl : raw29224step1Labels = raw29224step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29224step0 raw29224step0Labels permutation80 hz
    mixedMoment B raw29224step1 raw29224step1Labels = mixedMoment B raw29224step2 raw29224step2Labels := by
      have ha : raw29224step2 = (fun i j => raw29224step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29224step2 raw29224step1; decide +kernel
      have hl : raw29224step2Labels = raw29224step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29224step1 raw29224step1Labels permutation8 permutation6
    mixedMoment B raw29224step2 raw29224step2Labels = mixedMoment B raw29224step3 raw29224step3Labels := by
      have ha : raw29224step3 = raw29224step2 := by apply Matrix.ext; unfold raw29224step3 raw29224step2; decide +kernel
      have hl : raw29224step2Labels = labelEmbedding9 ∘ raw29224step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29224step2 raw29224step2Labels raw29224step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5021 node5021Labels := by rfl

theorem canonical29225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29225 raw29225Labels = mixedMoment B node4317 node4317Labels := by
  calc
    mixedMoment B raw29225 raw29225Labels = mixedMoment B raw29225step0 raw29225step0Labels := by
      have hz : ∀ j, raw29225 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29225step0 = (fun i j => raw29225 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29225step0 raw29225; decide +kernel
      have hl : raw29225step0Labels = raw29225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29225 raw29225Labels permutation434 hz
    mixedMoment B raw29225step0 raw29225step0Labels = mixedMoment B raw29225step1 raw29225step1Labels := by
      have hz : ∀ j, raw29225step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29225step1 = (fun i j => raw29225step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29225step1 raw29225step0; decide +kernel
      have hl : raw29225step1Labels = raw29225step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29225step0 raw29225step0Labels permutation80 hz
    mixedMoment B raw29225step1 raw29225step1Labels = mixedMoment B raw29225step2 raw29225step2Labels := by
      have ha : raw29225step2 = (fun i j => raw29225step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29225step2 raw29225step1; decide +kernel
      have hl : raw29225step2Labels = raw29225step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29225step1 raw29225step1Labels permutation31 permutation4
    mixedMoment B raw29225step2 raw29225step2Labels = mixedMoment B raw29225step3 raw29225step3Labels := by
      have ha : raw29225step3 = raw29225step2 := by apply Matrix.ext; unfold raw29225step3 raw29225step2; decide +kernel
      have hl : raw29225step2Labels = labelEmbedding7 ∘ raw29225step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29225step2 raw29225step2Labels raw29225step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4317 node4317Labels := by rfl

theorem canonical29226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29226 raw29226Labels = mixedMoment B node4319 node4319Labels := by
  calc
    mixedMoment B raw29226 raw29226Labels = mixedMoment B raw29226step0 raw29226step0Labels := by
      have hz : ∀ j, raw29226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29226step0 = (fun i j => raw29226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29226step0 raw29226; decide +kernel
      have hl : raw29226step0Labels = raw29226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29226 raw29226Labels permutation434 hz
    mixedMoment B raw29226step0 raw29226step0Labels = mixedMoment B raw29226step1 raw29226step1Labels := by
      have hz : ∀ j, raw29226step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29226step1 = (fun i j => raw29226step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29226step1 raw29226step0; decide +kernel
      have hl : raw29226step1Labels = raw29226step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29226step0 raw29226step0Labels permutation80 hz
    mixedMoment B raw29226step1 raw29226step1Labels = mixedMoment B raw29226step2 raw29226step2Labels := by
      have ha : raw29226step2 = (fun i j => raw29226step1 (permutation30 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29226step2 raw29226step1; decide +kernel
      have hl : raw29226step2Labels = raw29226step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29226step1 raw29226step1Labels permutation30 permutation4
    mixedMoment B raw29226step2 raw29226step2Labels = mixedMoment B raw29226step3 raw29226step3Labels := by
      have ha : raw29226step3 = raw29226step2 := by apply Matrix.ext; unfold raw29226step3 raw29226step2; decide +kernel
      have hl : raw29226step2Labels = labelEmbedding7 ∘ raw29226step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29226step2 raw29226step2Labels raw29226step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4319 node4319Labels := by rfl

theorem canonical29227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29227 raw29227Labels = mixedMoment B node4304 node4304Labels := by
  calc
    mixedMoment B raw29227 raw29227Labels = mixedMoment B raw29227step0 raw29227step0Labels := by
      have hz : ∀ j, raw29227 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29227step0 = (fun i j => raw29227 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29227step0 raw29227; decide +kernel
      have hl : raw29227step0Labels = raw29227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29227 raw29227Labels permutation434 hz
    mixedMoment B raw29227step0 raw29227step0Labels = mixedMoment B raw29227step1 raw29227step1Labels := by
      have ha : raw29227step1 = (fun i j => raw29227step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29227step1 raw29227step0; decide +kernel
      have hl : raw29227step1Labels = raw29227step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29227step0 raw29227step0Labels permutation151 permutation4
    mixedMoment B raw29227step1 raw29227step1Labels = mixedMoment B raw29227step2 raw29227step2Labels := by
      have ha : raw29227step2 = raw29227step1 := by apply Matrix.ext; unfold raw29227step2 raw29227step1; decide +kernel
      have hl : raw29227step1Labels = labelEmbedding7 ∘ raw29227step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29227step1 raw29227step1Labels raw29227step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4304 node4304Labels := by rfl

theorem canonical29228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29228 raw29228Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw29228 raw29228Labels = mixedMoment B raw29228step0 raw29228step0Labels := by
      have hz : ∀ j, raw29228 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29228step0 = (fun i j => raw29228 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29228step0 raw29228; decide +kernel
      have hl : raw29228step0Labels = raw29228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29228 raw29228Labels permutation434 hz
    mixedMoment B raw29228step0 raw29228step0Labels = mixedMoment B raw29228step1 raw29228step1Labels := by
      have hz : ∀ j, raw29228step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29228step1 = (fun i j => raw29228step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29228step1 raw29228step0; decide +kernel
      have hl : raw29228step1Labels = raw29228step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29228step0 raw29228step0Labels permutation80 hz
    mixedMoment B raw29228step1 raw29228step1Labels = mixedMoment B raw29228step2 raw29228step2Labels := by
      have ha : raw29228step2 = (fun i j => raw29228step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29228step2 raw29228step1; decide +kernel
      have hl : raw29228step2Labels = raw29228step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29228step1 raw29228step1Labels permutation31 permutation4
    mixedMoment B raw29228step2 raw29228step2Labels = mixedMoment B raw29228step3 raw29228step3Labels := by
      have ha : raw29228step3 = raw29228step2 := by apply Matrix.ext; unfold raw29228step3 raw29228step2; decide +kernel
      have hl : raw29228step2Labels = labelEmbedding7 ∘ raw29228step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29228step2 raw29228step2Labels raw29228step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4431 node4431Labels := by rfl

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

theorem canonical1068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1068 raw1068Labels = mixedMoment B node4304 node4304Labels := by
  calc
    mixedMoment B raw1068 raw1068Labels = mixedMoment B raw1068step0 raw1068step0Labels := by
      have ha : raw1068step0 = (fun i j => raw1068 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1068step0 raw1068; decide +kernel
      have hl : raw1068step0Labels = raw1068Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1068 raw1068Labels permutation32 permutation4
    mixedMoment B raw1068step0 raw1068step0Labels = mixedMoment B raw1068step1 raw1068step1Labels := by
      have ha : raw1068step1 = raw1068step0 := by apply Matrix.ext; unfold raw1068step1 raw1068step0; decide +kernel
      have hl : raw1068step0Labels = labelEmbedding7 ∘ raw1068step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1068step0 raw1068step0Labels raw1068step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4304 node4304Labels := by rfl

theorem canonical1069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1069 raw1069Labels = mixedMoment B node882 node882Labels := by
  calc
    mixedMoment B raw1069 raw1069Labels = mixedMoment B raw1069step0 raw1069step0Labels := by
      have ha : raw1069step0 = (fun i j => raw1069 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1069step0 raw1069; decide +kernel
      have hl : raw1069step0Labels = raw1069Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1069 raw1069Labels permutation32 permutation4
    _ = mixedMoment B node882 node882Labels := by rfl

theorem canonical1070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1070 raw1070Labels = mixedMoment B node1558 node1558Labels := by
  calc
    mixedMoment B raw1070 raw1070Labels = mixedMoment B raw1070step0 raw1070step0Labels := by
      have ha : raw1070step0 = (fun i j => raw1070 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1070step0 raw1070; decide +kernel
      have hl : raw1070step0Labels = raw1070Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1070 raw1070Labels permutation32 permutation6
    mixedMoment B raw1070step0 raw1070step0Labels = mixedMoment B raw1070step1 raw1070step1Labels := by
      have ha : raw1070step1 = -raw1070step0 := by apply Matrix.ext; change ∀ i j, raw1070step1 i j = -(raw1070step0 i j); unfold raw1070step1 raw1070step0; decide +kernel
      have hl : raw1070step1Labels = raw1070step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1070step1 raw1070step1Labels = mixedMoment B raw1070step2 raw1070step2Labels := by
      have ha : raw1070step2 = raw1070step1 := by apply Matrix.ext; unfold raw1070step2 raw1070step1; decide +kernel
      have hl : raw1070step1Labels = labelEmbedding1 ∘ raw1070step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1070step1 raw1070step1Labels raw1070step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1558 node1558Labels := by rfl

theorem canonical1092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1092 raw1092Labels = mixedMoment B node4319 node4319Labels := by
  calc
    mixedMoment B raw1092 raw1092Labels = mixedMoment B raw1092step0 raw1092step0Labels := by
      have ha : raw1092step0 = (fun i j => raw1092 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1092step0 raw1092; decide +kernel
      have hl : raw1092step0Labels = raw1092Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1092 raw1092Labels permutation8 permutation4
    mixedMoment B raw1092step0 raw1092step0Labels = mixedMoment B raw1092step1 raw1092step1Labels := by
      have ha : raw1092step1 = raw1092step0 := by apply Matrix.ext; unfold raw1092step1 raw1092step0; decide +kernel
      have hl : raw1092step0Labels = labelEmbedding7 ∘ raw1092step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1092step0 raw1092step0Labels raw1092step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4319 node4319Labels := by rfl

theorem canonical1093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1093 raw1093Labels = mixedMoment B node897 node897Labels := by
  calc
    mixedMoment B raw1093 raw1093Labels = mixedMoment B raw1093step0 raw1093step0Labels := by
      have ha : raw1093step0 = (fun i j => raw1093 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1093step0 raw1093; decide +kernel
      have hl : raw1093step0Labels = raw1093Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1093 raw1093Labels permutation8 permutation4
    _ = mixedMoment B node897 node897Labels := by rfl

theorem canonical1094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1094 raw1094Labels = mixedMoment B node1577 node1577Labels := by
  calc
    mixedMoment B raw1094 raw1094Labels = mixedMoment B raw1094step0 raw1094step0Labels := by
      have ha : raw1094step0 = (fun i j => raw1094 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1094step0 raw1094; decide +kernel
      have hl : raw1094step0Labels = raw1094Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1094 raw1094Labels permutation9 permutation6
    mixedMoment B raw1094step0 raw1094step0Labels = mixedMoment B raw1094step1 raw1094step1Labels := by
      have ha : raw1094step1 = -raw1094step0 := by apply Matrix.ext; change ∀ i j, raw1094step1 i j = -(raw1094step0 i j); unfold raw1094step1 raw1094step0; decide +kernel
      have hl : raw1094step1Labels = raw1094step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1094step1 raw1094step1Labels = mixedMoment B raw1094step2 raw1094step2Labels := by
      have ha : raw1094step2 = raw1094step1 := by apply Matrix.ext; unfold raw1094step2 raw1094step1; decide +kernel
      have hl : raw1094step1Labels = labelEmbedding1 ∘ raw1094step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1094step1 raw1094step1Labels raw1094step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1577 node1577Labels := by rfl

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

theorem canonical1242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1242 raw1242Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw1242 raw1242Labels = mixedMoment B raw1242step0 raw1242step0Labels := by
      have ha : raw1242step0 = (fun i j => raw1242 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1242step0 raw1242; decide +kernel
      have hl : raw1242step0Labels = raw1242Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1242 raw1242Labels permutation8 permutation4
    mixedMoment B raw1242step0 raw1242step0Labels = mixedMoment B raw1242step1 raw1242step1Labels := by
      have ha : raw1242step1 = raw1242step0 := by apply Matrix.ext; unfold raw1242step1 raw1242step0; decide +kernel
      have hl : raw1242step0Labels = labelEmbedding7 ∘ raw1242step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1242step0 raw1242step0Labels raw1242step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4431 node4431Labels := by rfl

theorem canonical1243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1243 raw1243Labels = mixedMoment B node1012 node1012Labels := by
  calc
    mixedMoment B raw1243 raw1243Labels = mixedMoment B raw1243step0 raw1243step0Labels := by
      have ha : raw1243step0 = (fun i j => raw1243 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1243step0 raw1243; decide +kernel
      have hl : raw1243step0Labels = raw1243Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1243 raw1243Labels permutation8 permutation4
    _ = mixedMoment B node1012 node1012Labels := by rfl

theorem canonical1244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1244 raw1244Labels = mixedMoment B node1627 node1627Labels := by
  calc
    mixedMoment B raw1244 raw1244Labels = mixedMoment B raw1244step0 raw1244step0Labels := by
      have ha : raw1244step0 = (fun i j => raw1244 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1244step0 raw1244; decide +kernel
      have hl : raw1244step0Labels = raw1244Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1244 raw1244Labels permutation8 permutation6
    mixedMoment B raw1244step0 raw1244step0Labels = mixedMoment B raw1244step1 raw1244step1Labels := by
      have ha : raw1244step1 = -raw1244step0 := by apply Matrix.ext; change ∀ i j, raw1244step1 i j = -(raw1244step0 i j); unfold raw1244step1 raw1244step0; decide +kernel
      have hl : raw1244step1Labels = raw1244step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1244step1 raw1244step1Labels = mixedMoment B raw1244step2 raw1244step2Labels := by
      have ha : raw1244step2 = raw1244step1 := by apply Matrix.ext; unfold raw1244step2 raw1244step1; decide +kernel
      have hl : raw1244step1Labels = labelEmbedding1 ∘ raw1244step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1244step1 raw1244step1Labels raw1244step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1627 node1627Labels := by rfl

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

theorem singleton4304 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4304 node4304Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node882 node882Labels + mixedMoment B node1558 node1558Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1068 singletonSmall4304
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4304) = raw1068Labels := by decide +kernel
  rw [hl, canonical1068 B hB] at h
  have hc0 : mixedMoment B raw1068 (Fin.cases (0 : Fin 2) singletonSmall4304) =
      mixedMoment B node882 node882Labels := by
    have ha : raw1068 = raw1069 := by apply Matrix.ext; unfold raw1068 raw1069; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4304 = raw1069Labels := by decide +kernel
    rw [ha, hj, canonical1069 B hB]
  have hc1 : mixedMoment B raw1068 (Fin.cases (1 : Fin 2) singletonSmall4304) =
      mixedMoment B node1558 node1558Labels := by
    have ha : raw1068 = raw1070 := by apply Matrix.ext; unfold raw1068 raw1070; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4304 = raw1070Labels := by decide +kernel
    rw [ha, hj, canonical1070 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4319 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4319 node4319Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node897 node897Labels + mixedMoment B node1577 node1577Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1092 singletonSmall4319
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4319) = raw1092Labels := by decide +kernel
  rw [hl, canonical1092 B hB] at h
  have hc0 : mixedMoment B raw1092 (Fin.cases (0 : Fin 2) singletonSmall4319) =
      mixedMoment B node897 node897Labels := by
    have ha : raw1092 = raw1093 := by apply Matrix.ext; unfold raw1092 raw1093; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4319 = raw1093Labels := by decide +kernel
    rw [ha, hj, canonical1093 B hB]
  have hc1 : mixedMoment B raw1092 (Fin.cases (1 : Fin 2) singletonSmall4319) =
      mixedMoment B node1577 node1577Labels := by
    have ha : raw1092 = raw1094 := by apply Matrix.ext; unfold raw1092 raw1094; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4319 = raw1094Labels := by decide +kernel
    rw [ha, hj, canonical1094 B hB]
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

theorem singleton4431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4431 node4431Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1012 node1012Labels + mixedMoment B node1627 node1627Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1242 singletonSmall4431
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4431) = raw1242Labels := by decide +kernel
  rw [hl, canonical1242 B hB] at h
  have hc0 : mixedMoment B raw1242 (Fin.cases (0 : Fin 2) singletonSmall4431) =
      mixedMoment B node1012 node1012Labels := by
    have ha : raw1242 = raw1243 := by apply Matrix.ext; unfold raw1242 raw1243; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4431 = raw1243Labels := by decide +kernel
    rw [ha, hj, canonical1243 B hB]
  have hc1 : mixedMoment B raw1242 (Fin.cases (1 : Fin 2) singletonSmall4431) =
      mixedMoment B node1627 node1627Labels := by
    have ha : raw1242 = raw1244 := by apply Matrix.ext; unfold raw1242 raw1244; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4431 = raw1244Labels := by decide +kernel
    rw [ha, hj, canonical1244 B hB]
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

theorem singleton4657 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4657 node4657Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1783 node1783Labels + mixedMoment B node1857 node1857Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1527 singletonSmall4657
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4657) = raw1527Labels := by decide +kernel
  rw [hl, canonical1527 B hB] at h
  have hc0 : mixedMoment B raw1527 (Fin.cases (0 : Fin 2) singletonSmall4657) =
      mixedMoment B node1783 node1783Labels := by
    have ha : raw1527 = raw1528 := by apply Matrix.ext; unfold raw1527 raw1528; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4657 = raw1528Labels := by decide +kernel
    rw [ha, hj, canonical1528 B hB]
  have hc1 : mixedMoment B raw1527 (Fin.cases (1 : Fin 2) singletonSmall4657) =
      mixedMoment B node1857 node1857Labels := by
    have ha : raw1527 = raw1529 := by apply Matrix.ext; unfold raw1527 raw1529; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4657 = raw1529Labels := by decide +kernel
    rw [ha, hj, canonical1529 B hB]
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

theorem singleton4719 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4719 node4719Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1873 node1873Labels + mixedMoment B node1893 node1893Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1614 singletonSmall4719
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4719) = raw1614Labels := by decide +kernel
  rw [hl, canonical1614 B hB] at h
  have hc0 : mixedMoment B raw1614 (Fin.cases (0 : Fin 2) singletonSmall4719) =
      mixedMoment B node1873 node1873Labels := by
    have ha : raw1614 = raw1615 := by apply Matrix.ext; unfold raw1614 raw1615; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4719 = raw1615Labels := by decide +kernel
    rw [ha, hj, canonical1615 B hB]
  have hc1 : mixedMoment B raw1614 (Fin.cases (1 : Fin 2) singletonSmall4719) =
      mixedMoment B node1893 node1893Labels := by
    have ha : raw1614 = raw1616 := by apply Matrix.ext; unfold raw1614 raw1616; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4719 = raw1616Labels := by decide +kernel
    rw [ha, hj, canonical1616 B hB]
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

theorem singleton4742 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4742 node4742Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1915 node1915Labels + mixedMoment B node1946 node1946Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1659 singletonSmall4742
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4742) = raw1659Labels := by decide +kernel
  rw [hl, canonical1659 B hB] at h
  have hc0 : mixedMoment B raw1659 (Fin.cases (0 : Fin 2) singletonSmall4742) =
      mixedMoment B node1915 node1915Labels := by
    have ha : raw1659 = raw1660 := by apply Matrix.ext; unfold raw1659 raw1660; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4742 = raw1660Labels := by decide +kernel
    rw [ha, hj, canonical1660 B hB]
  have hc1 : mixedMoment B raw1659 (Fin.cases (1 : Fin 2) singletonSmall4742) =
      mixedMoment B node1946 node1946Labels := by
    have ha : raw1659 = raw1661 := by apply Matrix.ext; unfold raw1659 raw1661; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4742 = raw1661Labels := by decide +kernel
    rw [ha, hj, canonical1661 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4754 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4754 node4754Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1951 node1951Labels + mixedMoment B node1951 node1951Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1677 singletonSmall4754
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4754) = raw1677Labels := by decide +kernel
  rw [hl, canonical1677 B hB] at h
  have hc0 : mixedMoment B raw1677 (Fin.cases (0 : Fin 2) singletonSmall4754) =
      mixedMoment B node1951 node1951Labels := by
    have ha : raw1677 = raw1678 := by apply Matrix.ext; unfold raw1677 raw1678; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4754 = raw1678Labels := by decide +kernel
    rw [ha, hj, canonical1678 B hB]
  have hc1 : mixedMoment B raw1677 (Fin.cases (1 : Fin 2) singletonSmall4754) =
      mixedMoment B node1951 node1951Labels := by
    have ha : raw1677 = raw1679 := by apply Matrix.ext; unfold raw1677 raw1679; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4754 = raw1679Labels := by decide +kernel
    rw [ha, hj, canonical1679 B hB]
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

theorem singleton4843 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4843 node4843Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2062 node2062Labels + mixedMoment B node2230 node2230Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1773 singletonSmall4843
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4843) = raw1773Labels := by decide +kernel
  rw [hl, canonical1773 B hB] at h
  have hc0 : mixedMoment B raw1773 (Fin.cases (0 : Fin 2) singletonSmall4843) =
      mixedMoment B node2062 node2062Labels := by
    have ha : raw1773 = raw1774 := by apply Matrix.ext; unfold raw1773 raw1774; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4843 = raw1774Labels := by decide +kernel
    rw [ha, hj, canonical1774 B hB]
  have hc1 : mixedMoment B raw1773 (Fin.cases (1 : Fin 2) singletonSmall4843) =
      mixedMoment B node2230 node2230Labels := by
    have ha : raw1773 = raw1775 := by apply Matrix.ext; unfold raw1773 raw1775; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4843 = raw1775Labels := by decide +kernel
    rw [ha, hj, canonical1775 B hB]
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

theorem singleton5000 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5000 node5000Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2385 node2385Labels + mixedMoment B node3353 node3353Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2013 singletonSmall5000
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5000) = raw2013Labels := by decide +kernel
  rw [hl, canonical2013 B hB] at h
  have hc0 : mixedMoment B raw2013 (Fin.cases (0 : Fin 2) singletonSmall5000) =
      mixedMoment B node2385 node2385Labels := by
    have ha : raw2013 = raw2014 := by apply Matrix.ext; unfold raw2013 raw2014; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5000 = raw2014Labels := by decide +kernel
    rw [ha, hj, canonical2014 B hB]
  have hc1 : mixedMoment B raw2013 (Fin.cases (1 : Fin 2) singletonSmall5000) =
      mixedMoment B node3353 node3353Labels := by
    have ha : raw2013 = raw2015 := by apply Matrix.ext; unfold raw2013 raw2015; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5000 = raw2015Labels := by decide +kernel
    rw [ha, hj, canonical2015 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5021 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5021 node5021Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2407 node2407Labels + mixedMoment B node3360 node3360Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2031 singletonSmall5021
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5021) = raw2031Labels := by decide +kernel
  rw [hl, canonical2031 B hB] at h
  have hc0 : mixedMoment B raw2031 (Fin.cases (0 : Fin 2) singletonSmall5021) =
      mixedMoment B node2407 node2407Labels := by
    have ha : raw2031 = raw2032 := by apply Matrix.ext; unfold raw2031 raw2032; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5021 = raw2032Labels := by decide +kernel
    rw [ha, hj, canonical2032 B hB]
  have hc1 : mixedMoment B raw2031 (Fin.cases (1 : Fin 2) singletonSmall5021) =
      mixedMoment B node3360 node3360Labels := by
    have ha : raw2031 = raw2033 := by apply Matrix.ext; unfold raw2031 raw2033; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5021 = raw2033Labels := by decide +kernel
    rw [ha, hj, canonical2033 B hB]
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

theorem singleton5109 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5109 node5109Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2519 node2519Labels + mixedMoment B node3486 node3486Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2133 singletonSmall5109
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5109) = raw2133Labels := by decide +kernel
  rw [hl, canonical2133 B hB] at h
  have hc0 : mixedMoment B raw2133 (Fin.cases (0 : Fin 2) singletonSmall5109) =
      mixedMoment B node2519 node2519Labels := by
    have ha : raw2133 = raw2134 := by apply Matrix.ext; unfold raw2133 raw2134; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5109 = raw2134Labels := by decide +kernel
    rw [ha, hj, canonical2134 B hB]
  have hc1 : mixedMoment B raw2133 (Fin.cases (1 : Fin 2) singletonSmall5109) =
      mixedMoment B node3486 node3486Labels := by
    have ha : raw2133 = raw2135 := by apply Matrix.ext; unfold raw2133 raw2135; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5109 = raw2135Labels := by decide +kernel
    rw [ha, hj, canonical2135 B hB]
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

theorem sound882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node882 node882Labels = Sparse.eval nodeValue882 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 882) = mixedMoment B node882 node882Labels := rfl
  simpa [nodeValue882, Sparse.eval] using hc.symm

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

theorem sound897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node897 node897Labels = Sparse.eval nodeValue897 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 897) = mixedMoment B node897 node897Labels := rfl
  simpa [nodeValue897, Sparse.eval] using hc.symm

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

theorem sound1012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1012 node1012Labels = Sparse.eval nodeValue1012 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1012) = mixedMoment B node1012 node1012Labels := rfl
  simpa [nodeValue1012, Sparse.eval] using hc.symm

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

theorem sound1558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1558 node1558Labels = Sparse.eval nodeValue1558 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1558) = mixedMoment B node1558 node1558Labels := rfl
  simpa [nodeValue1558, Sparse.eval] using hc.symm

theorem sound1577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1577 node1577Labels = Sparse.eval nodeValue1577 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1577) = mixedMoment B node1577 node1577Labels := rfl
  simpa [nodeValue1577, Sparse.eval] using hc.symm

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

theorem sound1627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1627 node1627Labels = Sparse.eval nodeValue1627 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1627) = mixedMoment B node1627 node1627Labels := rfl
  simpa [nodeValue1627, Sparse.eval] using hc.symm

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

theorem sound1774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1774 node1774Labels = Sparse.eval nodeValue1774 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1774) = mixedMoment B node1774 node1774Labels := rfl
  simpa [nodeValue1774, Sparse.eval] using hc.symm

theorem sound1783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1783 node1783Labels = Sparse.eval nodeValue1783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1783) = mixedMoment B node1783 node1783Labels := rfl
  simpa [nodeValue1783, Sparse.eval] using hc.symm

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

theorem sound1840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1840 node1840Labels = Sparse.eval nodeValue1840 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1840) = mixedMoment B node1840 node1840Labels := rfl
  simpa [nodeValue1840, Sparse.eval] using hc.symm

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

theorem sound1857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1857 node1857Labels = Sparse.eval nodeValue1857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1857) = mixedMoment B node1857 node1857Labels := rfl
  simpa [nodeValue1857, Sparse.eval] using hc.symm

theorem sound1864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1864 node1864Labels = Sparse.eval nodeValue1864 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1864) = mixedMoment B node1864 node1864Labels := rfl
  simpa [nodeValue1864, Sparse.eval] using hc.symm

theorem sound1873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1873 node1873Labels = Sparse.eval nodeValue1873 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1873) = mixedMoment B node1873 node1873Labels := rfl
  simpa [nodeValue1873, Sparse.eval] using hc.symm

theorem sound1882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1882 node1882Labels = Sparse.eval nodeValue1882 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1882) = mixedMoment B node1882 node1882Labels := rfl
  simpa [nodeValue1882, Sparse.eval] using hc.symm

theorem sound1893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1893 node1893Labels = Sparse.eval nodeValue1893 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1893) = mixedMoment B node1893 node1893Labels := rfl
  simpa [nodeValue1893, Sparse.eval] using hc.symm

theorem sound1915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1915 node1915Labels = Sparse.eval nodeValue1915 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1915) = mixedMoment B node1915 node1915Labels := rfl
  simpa [nodeValue1915, Sparse.eval] using hc.symm

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

theorem sound1946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1946 node1946Labels = Sparse.eval nodeValue1946 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1946) = mixedMoment B node1946 node1946Labels := rfl
  simpa [nodeValue1946, Sparse.eval] using hc.symm

theorem sound1951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1951 node1951Labels = Sparse.eval nodeValue1951 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1951) = mixedMoment B node1951 node1951Labels := rfl
  simpa [nodeValue1951, Sparse.eval] using hc.symm

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

theorem sound2062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2062 node2062Labels = Sparse.eval nodeValue2062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2062) = mixedMoment B node2062 node2062Labels := rfl
  simpa [nodeValue2062, Sparse.eval] using hc.symm

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

theorem sound2230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2230 node2230Labels = Sparse.eval nodeValue2230 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2230) = mixedMoment B node2230 node2230Labels := rfl
  simpa [nodeValue2230, Sparse.eval] using hc.symm

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

theorem sound2385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2385 node2385Labels = Sparse.eval nodeValue2385 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2385) = mixedMoment B node2385 node2385Labels := rfl
  simpa [nodeValue2385, Sparse.eval] using hc.symm

theorem sound2407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2407 node2407Labels = Sparse.eval nodeValue2407 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2407) = mixedMoment B node2407 node2407Labels := rfl
  simpa [nodeValue2407, Sparse.eval] using hc.symm

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

theorem sound2519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2519 node2519Labels = Sparse.eval nodeValue2519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2519) = mixedMoment B node2519 node2519Labels := rfl
  simpa [nodeValue2519, Sparse.eval] using hc.symm

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

theorem sound3353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3353 node3353Labels = Sparse.eval nodeValue3353 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3353) = mixedMoment B node3353 node3353Labels := rfl
  simpa [nodeValue3353, Sparse.eval] using hc.symm

theorem sound3360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3360 node3360Labels = Sparse.eval nodeValue3360 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3360) = mixedMoment B node3360 node3360Labels := rfl
  simpa [nodeValue3360, Sparse.eval] using hc.symm

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

theorem sound3486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3486 node3486Labels = Sparse.eval nodeValue3486 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3486) = mixedMoment B node3486 node3486Labels := rfl
  simpa [nodeValue3486, Sparse.eval] using hc.symm

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

theorem sound4081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4081 node4081Labels = Sparse.eval nodeValue4081 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4081) = mixedMoment B node4081 node4081Labels := rfl
  simpa [nodeValue4081, Sparse.eval] using hc.symm

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

theorem zero4317 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4317 node4317Labels = 0 := by
  exact mixedMoment_order_one B hB node4317 node4317Labels 1
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

theorem sound4304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4304 node4304Labels = Sparse.eval nodeValue4304 (mixedVector B) := by
  have h := singleton4304 B _hB
  rw [sound882 B _hB _hF, sound1558 B _hB _hF] at h
  norm_num [nodeValue4304, nodeValue882, nodeValue1558, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4317 node4317Labels = Sparse.eval nodeValue4317 (mixedVector B) := by
  simpa only [nodeValue4317, Sparse.eval_nil] using zero4317 B _hB _hF

theorem sound4319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4319 node4319Labels = Sparse.eval nodeValue4319 (mixedVector B) := by
  have h := singleton4319 B _hB
  rw [sound897 B _hB _hF, sound1577 B _hB _hF] at h
  norm_num [nodeValue4319, nodeValue897, nodeValue1577, Sparse.eval] at h ⊢
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

theorem sound4431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4431 node4431Labels = Sparse.eval nodeValue4431 (mixedVector B) := by
  have h := singleton4431 B _hB
  rw [sound1012 B _hB _hF, sound1627 B _hB _hF] at h
  norm_num [nodeValue4431, nodeValue1012, nodeValue1627, Sparse.eval] at h ⊢
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

theorem zero4643 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4643 node4643Labels = 0 := by
  exact mixedMoment_order_one B hB node4643 node4643Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4655 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4655 node4655Labels = 0 := by
  exact mixedMoment_order_one B hB node4655 node4655Labels 1
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

theorem sound4643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4643 node4643Labels = Sparse.eval nodeValue4643 (mixedVector B) := by
  simpa only [nodeValue4643, Sparse.eval_nil] using zero4643 B _hB _hF

theorem sound4645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4645 node4645Labels = Sparse.eval nodeValue4645 (mixedVector B) := by
  have h := singleton4645 B _hB
  rw [sound1774 B _hB _hF, sound1840 B _hB _hF] at h
  norm_num [nodeValue4645, nodeValue1774, nodeValue1840, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4655 node4655Labels = Sparse.eval nodeValue4655 (mixedVector B) := by
  simpa only [nodeValue4655, Sparse.eval_nil] using zero4655 B _hB _hF

theorem sound4657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4657 node4657Labels = Sparse.eval nodeValue4657 (mixedVector B) := by
  have h := singleton4657 B _hB
  rw [sound1783 B _hB _hF, sound1857 B _hB _hF] at h
  norm_num [nodeValue4657, nodeValue1783, nodeValue1857, Sparse.eval] at h ⊢
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

theorem sound4710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4710 node4710Labels = Sparse.eval nodeValue4710 (mixedVector B) := by
  have h := singleton4710 B _hB
  rw [sound1864 B _hB _hF, sound1882 B _hB _hF] at h
  norm_num [nodeValue4710, nodeValue1864, nodeValue1882, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4719 node4719Labels = Sparse.eval nodeValue4719 (mixedVector B) := by
  have h := singleton4719 B _hB
  rw [sound1873 B _hB _hF, sound1893 B _hB _hF] at h
  norm_num [nodeValue4719, nodeValue1873, nodeValue1893, Sparse.eval] at h ⊢
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

theorem zero4741 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4741 node4741Labels = 0 := by
  exact mixedMoment_order_one B hB node4741 node4741Labels 1
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

theorem sound4741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4741 node4741Labels = Sparse.eval nodeValue4741 (mixedVector B) := by
  simpa only [nodeValue4741, Sparse.eval_nil] using zero4741 B _hB _hF

theorem sound4742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4742 node4742Labels = Sparse.eval nodeValue4742 (mixedVector B) := by
  have h := singleton4742 B _hB
  rw [sound1915 B _hB _hF, sound1946 B _hB _hF] at h
  norm_num [nodeValue4742, nodeValue1915, nodeValue1946, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4754 node4754Labels = Sparse.eval nodeValue4754 (mixedVector B) := by
  have h := singleton4754 B _hB
  rw [sound1951 B _hB _hF] at h
  norm_num [nodeValue4754, nodeValue1951, Sparse.eval] at h ⊢
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

theorem sound4841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4841 node4841Labels = Sparse.eval nodeValue4841 (mixedVector B) := by
  simpa only [nodeValue4841, Sparse.eval_nil] using zero4841 B _hB _hF

theorem sound4843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4843 node4843Labels = Sparse.eval nodeValue4843 (mixedVector B) := by
  have h := singleton4843 B _hB
  rw [sound2062 B _hB _hF, sound2230 B _hB _hF] at h
  norm_num [nodeValue4843, nodeValue2062, nodeValue2230, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5000 node5000Labels = Sparse.eval nodeValue5000 (mixedVector B) := by
  have h := singleton5000 B _hB
  rw [sound2385 B _hB _hF, sound3353 B _hB _hF] at h
  norm_num [nodeValue5000, nodeValue2385, nodeValue3353, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5021 node5021Labels = Sparse.eval nodeValue5021 (mixedVector B) := by
  have h := singleton5021 B _hB
  rw [sound2407 B _hB _hF, sound3360 B _hB _hF] at h
  norm_num [nodeValue5021, nodeValue2407, nodeValue3360, Sparse.eval] at h ⊢
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

theorem zero5107 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5107 node5107Labels = 0 := by
  exact mixedMoment_order_one B hB node5107 node5107Labels 1
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

theorem sound5107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5107 node5107Labels = Sparse.eval nodeValue5107 (mixedVector B) := by
  simpa only [nodeValue5107, Sparse.eval_nil] using zero5107 B _hB _hF

theorem sound5109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5109 node5109Labels = Sparse.eval nodeValue5109 (mixedVector B) := by
  have h := singleton5109 B _hB
  rw [sound2519 B _hB _hF, sound3486 B _hB _hF] at h
  norm_num [nodeValue5109, nodeValue2519, nodeValue3486, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources65
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2084 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2084 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2084 + difference 0 1) (sourceB2084 + difference 1 0) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4754) := by
    have ha : (tripleCharges (sourceA2084 + difference 0 1) (sourceB2084 + difference 1 0) sourceC2084) = raw29208 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29208; decide +kernel
    rw [ha]
    exact (canonical29208 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2084 + difference 0 2) (sourceB2084 + difference 2 0) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA2084 + difference 0 2) (sourceB2084 + difference 2 0) sourceC2084) = raw29209 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29209; decide +kernel
    rw [ha]
    exact (canonical29209 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2084 + difference 0 3) (sourceB2084 + difference 3 0) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA2084 + difference 0 3) (sourceB2084 + difference 3 0) sourceC2084) = raw29176 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29176; decide +kernel
    rw [ha]
    exact (canonical29176 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2084 + difference 0 4) (sourceB2084 + difference 4 0) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA2084 + difference 0 4) (sourceB2084 + difference 4 0) sourceC2084) = raw29210 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29210; decide +kernel
    rw [ha]
    exact (canonical29210 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2084 + difference 0 5) (sourceB2084 + difference 5 0) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA2084 + difference 0 5) (sourceB2084 + difference 5 0) sourceC2084) = raw29211 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29211; decide +kernel
    rw [ha]
    exact (canonical29211 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2084 + difference 1 0) (sourceB2084 + difference 0 1) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA2084 + difference 1 0) (sourceB2084 + difference 0 1) sourceC2084) = raw29182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29182; decide +kernel
    rw [ha]
    exact (canonical29182 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2084 + difference 1 2) (sourceB2084 + difference 2 1) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4741) := by
    have ha : (tripleCharges (sourceA2084 + difference 1 2) (sourceB2084 + difference 2 1) sourceC2084) = raw29184 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29184; decide +kernel
    rw [ha]
    exact (canonical29184 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2084 + difference 1 3) (sourceB2084 + difference 3 1) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4741) := by
    have ha : (tripleCharges (sourceA2084 + difference 1 3) (sourceB2084 + difference 3 1) sourceC2084) = raw28815 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw28815; decide +kernel
    rw [ha]
    exact (canonical28815 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2084 + difference 1 4) (sourceB2084 + difference 4 1) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA2084 + difference 1 4) (sourceB2084 + difference 4 1) sourceC2084) = raw28679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw28679; decide +kernel
    rw [ha]
    exact (canonical28679 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2084 + difference 1 5) (sourceB2084 + difference 5 1) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5107) := by
    have ha : (tripleCharges (sourceA2084 + difference 1 5) (sourceB2084 + difference 5 1) sourceC2084) = raw27664 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw27664; decide +kernel
    rw [ha]
    exact (canonical27664 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2084 + difference 2 0) (sourceB2084 + difference 0 2) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4643) := by
    have ha : (tripleCharges (sourceA2084 + difference 2 0) (sourceB2084 + difference 0 2) sourceC2084) = raw29212 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29212; decide +kernel
    rw [ha]
    exact (canonical29212 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2084 + difference 2 1) (sourceB2084 + difference 1 2) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4719) := by
    have ha : (tripleCharges (sourceA2084 + difference 2 1) (sourceB2084 + difference 1 2) sourceC2084) = raw29213 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29213; decide +kernel
    rw [ha]
    exact (canonical29213 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2084 + difference 2 3) (sourceB2084 + difference 3 2) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4710) := by
    have ha : (tripleCharges (sourceA2084 + difference 2 3) (sourceB2084 + difference 3 2) sourceC2084) = raw29180 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29180; decide +kernel
    rw [ha]
    exact (canonical29180 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2084 + difference 2 4) (sourceB2084 + difference 4 2) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA2084 + difference 2 4) (sourceB2084 + difference 4 2) sourceC2084) = raw29214 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29214; decide +kernel
    rw [ha]
    exact (canonical29214 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2084 + difference 2 5) (sourceB2084 + difference 5 2) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA2084 + difference 2 5) (sourceB2084 + difference 5 2) sourceC2084) = raw29215 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29215; decide +kernel
    rw [ha]
    exact (canonical29215 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2084 + difference 3 0) (sourceB2084 + difference 0 3) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4643) := by
    have ha : (tripleCharges (sourceA2084 + difference 3 0) (sourceB2084 + difference 0 3) sourceC2084) = raw29216 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29216; decide +kernel
    rw [ha]
    exact (canonical29216 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2084 + difference 3 1) (sourceB2084 + difference 1 3) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4719) := by
    have ha : (tripleCharges (sourceA2084 + difference 3 1) (sourceB2084 + difference 1 3) sourceC2084) = raw29217 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29217; decide +kernel
    rw [ha]
    exact (canonical29217 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2084 + difference 3 2) (sourceB2084 + difference 2 3) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4710) := by
    have ha : (tripleCharges (sourceA2084 + difference 3 2) (sourceB2084 + difference 2 3) sourceC2084) = raw29218 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29218; decide +kernel
    rw [ha]
    exact (canonical29218 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2084 + difference 3 4) (sourceB2084 + difference 4 3) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA2084 + difference 3 4) (sourceB2084 + difference 4 3) sourceC2084) = raw29219 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29219; decide +kernel
    rw [ha]
    exact (canonical29219 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2084 + difference 3 5) (sourceB2084 + difference 5 3) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA2084 + difference 3 5) (sourceB2084 + difference 5 3) sourceC2084) = raw29220 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29220; decide +kernel
    rw [ha]
    exact (canonical29220 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2084 + difference 4 0) (sourceB2084 + difference 0 4) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4655) := by
    have ha : (tripleCharges (sourceA2084 + difference 4 0) (sourceB2084 + difference 0 4) sourceC2084) = raw29221 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29221; decide +kernel
    rw [ha]
    exact (canonical29221 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2084 + difference 4 1) (sourceB2084 + difference 1 4) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4657) := by
    have ha : (tripleCharges (sourceA2084 + difference 4 1) (sourceB2084 + difference 1 4) sourceC2084) = raw29222 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29222; decide +kernel
    rw [ha]
    exact (canonical29222 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2084 + difference 4 2) (sourceB2084 + difference 2 4) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4645) := by
    have ha : (tripleCharges (sourceA2084 + difference 4 2) (sourceB2084 + difference 2 4) sourceC2084) = raw29223 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29223; decide +kernel
    rw [ha]
    exact (canonical29223 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2084 + difference 4 3) (sourceB2084 + difference 3 4) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4645) := by
    have ha : (tripleCharges (sourceA2084 + difference 4 3) (sourceB2084 + difference 3 4) sourceC2084) = raw29186 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29186; decide +kernel
    rw [ha]
    exact (canonical29186 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2084 + difference 4 5) (sourceB2084 + difference 5 4) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5021) := by
    have ha : (tripleCharges (sourceA2084 + difference 4 5) (sourceB2084 + difference 5 4) sourceC2084) = raw29224 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29224; decide +kernel
    rw [ha]
    exact (canonical29224 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2084 + difference 5 0) (sourceB2084 + difference 0 5) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4317) := by
    have ha : (tripleCharges (sourceA2084 + difference 5 0) (sourceB2084 + difference 0 5) sourceC2084) = raw29225 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29225; decide +kernel
    rw [ha]
    exact (canonical29225 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2084 + difference 5 1) (sourceB2084 + difference 1 5) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4319) := by
    have ha : (tripleCharges (sourceA2084 + difference 5 1) (sourceB2084 + difference 1 5) sourceC2084) = raw29226 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29226; decide +kernel
    rw [ha]
    exact (canonical29226 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2084 + difference 5 2) (sourceB2084 + difference 2 5) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4304) := by
    have ha : (tripleCharges (sourceA2084 + difference 5 2) (sourceB2084 + difference 2 5) sourceC2084) = raw29227 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29227; decide +kernel
    rw [ha]
    exact (canonical29227 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2084 + difference 5 3) (sourceB2084 + difference 3 5) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4304) := by
    have ha : (tripleCharges (sourceA2084 + difference 5 3) (sourceB2084 + difference 3 5) sourceC2084) = raw29190 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29190; decide +kernel
    rw [ha]
    exact (canonical29190 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2084 + difference 5 4) (sourceB2084 + difference 4 5) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA2084 + difference 5 4) (sourceB2084 + difference 4 5) sourceC2084) = raw29228 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29228; decide +kernel
    rw [ha]
    exact (canonical29228 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2084 sourceB2084 sourceC2084
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2084, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1739 : Integer.Sparse.reindex keyMap MixedData.row1739 = numericRow1739 := by decide +kernel

theorem numericCheck1739 (x : Master → ℝ) : Integer.Sparse.eval numericRow1739 x =
    (4 : ℝ) * reducedSource1739 x := by
  norm_num [numericRow1739, reducedSource1739, Integer.Sparse.eval, Sparse.eval, nodeValue4081, nodeValue4304, nodeValue4317, nodeValue4319, nodeValue4431, nodeValue4643, nodeValue4645, nodeValue4655, nodeValue4657, nodeValue4710, nodeValue4719, nodeValue4741, nodeValue4742, nodeValue4754, nodeValue4788, nodeValue4841, nodeValue4843, nodeValue5000, nodeValue5021, nodeValue5107, nodeValue5109] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1739 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1739 (mixedVector B) = 0 := by
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  have h4304 : mixedVector B (Sum.inr 4304) = Sparse.eval nodeValue4304 (mixedVector B) := by
    change mixedMoment B node4304 node4304Labels = _
    exact sound4304 B hB hF
  have h4317 : mixedVector B (Sum.inr 4317) = Sparse.eval nodeValue4317 (mixedVector B) := by
    change mixedMoment B node4317 node4317Labels = _
    exact sound4317 B hB hF
  have h4319 : mixedVector B (Sum.inr 4319) = Sparse.eval nodeValue4319 (mixedVector B) := by
    change mixedMoment B node4319 node4319Labels = _
    exact sound4319 B hB hF
  have h4431 : mixedVector B (Sum.inr 4431) = Sparse.eval nodeValue4431 (mixedVector B) := by
    change mixedMoment B node4431 node4431Labels = _
    exact sound4431 B hB hF
  have h4643 : mixedVector B (Sum.inr 4643) = Sparse.eval nodeValue4643 (mixedVector B) := by
    change mixedMoment B node4643 node4643Labels = _
    exact sound4643 B hB hF
  have h4645 : mixedVector B (Sum.inr 4645) = Sparse.eval nodeValue4645 (mixedVector B) := by
    change mixedMoment B node4645 node4645Labels = _
    exact sound4645 B hB hF
  have h4655 : mixedVector B (Sum.inr 4655) = Sparse.eval nodeValue4655 (mixedVector B) := by
    change mixedMoment B node4655 node4655Labels = _
    exact sound4655 B hB hF
  have h4657 : mixedVector B (Sum.inr 4657) = Sparse.eval nodeValue4657 (mixedVector B) := by
    change mixedMoment B node4657 node4657Labels = _
    exact sound4657 B hB hF
  have h4710 : mixedVector B (Sum.inr 4710) = Sparse.eval nodeValue4710 (mixedVector B) := by
    change mixedMoment B node4710 node4710Labels = _
    exact sound4710 B hB hF
  have h4719 : mixedVector B (Sum.inr 4719) = Sparse.eval nodeValue4719 (mixedVector B) := by
    change mixedMoment B node4719 node4719Labels = _
    exact sound4719 B hB hF
  have h4741 : mixedVector B (Sum.inr 4741) = Sparse.eval nodeValue4741 (mixedVector B) := by
    change mixedMoment B node4741 node4741Labels = _
    exact sound4741 B hB hF
  have h4742 : mixedVector B (Sum.inr 4742) = Sparse.eval nodeValue4742 (mixedVector B) := by
    change mixedMoment B node4742 node4742Labels = _
    exact sound4742 B hB hF
  have h4754 : mixedVector B (Sum.inr 4754) = Sparse.eval nodeValue4754 (mixedVector B) := by
    change mixedMoment B node4754 node4754Labels = _
    exact sound4754 B hB hF
  have h4788 : mixedVector B (Sum.inr 4788) = Sparse.eval nodeValue4788 (mixedVector B) := by
    change mixedMoment B node4788 node4788Labels = _
    exact sound4788 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h4843 : mixedVector B (Sum.inr 4843) = Sparse.eval nodeValue4843 (mixedVector B) := by
    change mixedMoment B node4843 node4843Labels = _
    exact sound4843 B hB hF
  have h5000 : mixedVector B (Sum.inr 5000) = Sparse.eval nodeValue5000 (mixedVector B) := by
    change mixedMoment B node5000 node5000Labels = _
    exact sound5000 B hB hF
  have h5021 : mixedVector B (Sum.inr 5021) = Sparse.eval nodeValue5021 (mixedVector B) := by
    change mixedMoment B node5021 node5021Labels = _
    exact sound5021 B hB hF
  have h5107 : mixedVector B (Sum.inr 5107) = Sparse.eval nodeValue5107 (mixedVector B) := by
    change mixedMoment B node5107 node5107Labels = _
    exact sound5107 B hB hF
  have h5109 : mixedVector B (Sum.inr 5109) = Sparse.eval nodeValue5109 (mixedVector B) := by
    change mixedMoment B node5109 node5109Labels = _
    exact sound5109 B hB hF
  simpa only [sourceForm2084, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4081, h4304, h4317, h4319, h4431, h4643, h4645, h4655, h4657, h4710, h4719, h4741, h4742, h4754, h4788, h4841, h4843, h5000, h5021, h5107, h5109, reducedSource1739] using sourceEq2084 B hB

theorem rowSound1739_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1739 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1739, numericCheck1739, reducedZero1739 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739_e_oai
