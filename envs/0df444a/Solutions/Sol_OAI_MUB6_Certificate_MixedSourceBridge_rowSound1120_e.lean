-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T20:37:23.262808+00:00
-- url     : https://prove2.me/submissions/accee878-9771-46a3-aaf4-25f60c2443b3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E143
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E171

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

theorem IsHadamard.transpose {H : CMatrix} (hH : IsHadamard H) :
    IsHadamard H.transpose := by
  refine ⟨fun i j => hH.1 j i, ?_⟩
  ext i j
  simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm, eq_comm] using
    hH.row_orthogonal j i

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

theorem transition_reverse (b c : Basis) :
    transition c b = (transition b c).conjTranspose := by
  ext i j
  simp [transition, Matrix.conjTranspose_apply]

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

theorem average_prod (f : ι × κ → ℝ) :
    average f = average (fun i => average (fun k => f (i, k))) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

theorem average_comm (f : ι → κ → ℝ) :
    average (fun i => average (fun k => f i k)) =
      average (fun k => average (fun i => f i k)) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

theorem sum_eq_card_mul_average (f : ι → ℝ) :
    (∑ i, f i) = (Fintype.card ι : ℝ) * average f := by
  classical
  by_cases hc : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    simp [average]
  · have hcr : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hc
    simp only [average, ← mul_assoc, mul_inv_cancel₀ hcr, one_mul]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentSymmetry
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem injectiveMoment_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A = average (fun ρ : Fin p ↪ Coord =>
      average (fun κ : Fin q ↪ Coord =>
        ((exponentMonomial H A ρ κ).re +
          (exponentMonomial H.transpose A ρ κ).re) / 2)) :=
  average_prod _

theorem injectiveMoment_reverse_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    (average (fun κ : Fin q ↪ Coord => average (fun ρ : Fin p ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))) = injectiveMoment H A := by
  rw [average_comm]
  exact (injectiveMoment_iterated H A).symm

theorem exponentMonomial_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A.transpose κ ρ = exponentMonomial H.transpose A ρ κ := by
  exact Finset.prod_comm

theorem injectiveMoment_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A.transpose = injectiveMoment H A := by
  rw [injectiveMoment_iterated, injectiveMoment_iterated, average_comm]
  apply average_congr
  intro ρ
  apply average_congr
  intro κ
  rw [exponentMonomial_transpose, exponentMonomial_transpose]
  simp only [Matrix.transpose_transpose, add_comm]

theorem exponentMonomial_neg {p q : ℕ} (H : CMatrix)
    (hH : ∀ i j, Complex.normSq (H i j) = 1)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (-A) ρ κ = conj (exponentMonomial H A ρ κ) := by
  simp only [exponentMonomial, Matrix.neg_apply, zpow_neg, map_prod, map_zpow₀]
  apply Finset.prod_congr rfl
  intro u _
  apply Finset.prod_congr rfl
  intro v _
  rw [← unit_inv_eq_conj (hH (ρ u) (κ v)), inv_zpow]

theorem injectiveMoment_neg {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin q) ℤ) : injectiveMoment H (-A) = injectiveMoment H A := by
  apply average_congr
  intro s
  rw [exponentMonomial_neg H hH.1, exponentMonomial_neg H.transpose hH.transpose.1]
  simp

theorem exponentMonomial_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p))
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (fun i j => A (σ i) j) ρ κ =
      exponentMonomial H A (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) κ := by
  unfold exponentMonomial
  simpa only [Equiv.embeddingCongr_apply, Function.Embedding.congr_apply,
    Function.comp_apply, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.refl_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp σ (fun i => ∏ j, H (ρ (σ.symm i)) (κ j) ^ A i j)

theorem injectiveMoment_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p)) :
    injectiveMoment H (fun i j => A (σ i) j) = injectiveMoment H A := by
  rw [injectiveMoment_iterated H (fun i j => A (σ i) j), injectiveMoment_iterated H A]
  simp_rw [exponentMonomial_row_permutation H A σ,
    exponentMonomial_row_permutation H.transpose A σ]
  exact average_equiv (Equiv.embeddingCongr σ (Equiv.refl Coord))
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))

theorem injectiveMoment_column_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin q)) :
    injectiveMoment H (fun i j => A i (σ j)) = injectiveMoment H A := by
  rw [← injectiveMoment_transpose H (fun i j => A i (σ j))]
  change injectiveMoment H (fun i j => A.transpose (σ i) j) = _
  rw [injectiveMoment_row_permutation, injectiveMoment_transpose]

theorem exponentMonomial_zero_first_row {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0)
    (ρ : Fin (p + 1) ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A ρ κ =
      exponentMonomial H (fun i j => A i.succ j) (Sampling.dropFirst ρ) κ := by
  simp only [exponentMonomial, Fin.prod_univ_succ, hA, zpow_zero,
    Finset.prod_const_one, one_mul]
  rfl

theorem injectiveMoment_zero_first_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A i.succ j) := by
  rw [injectiveMoment_iterated H A,
    injectiveMoment_iterated H (fun i j => A i.succ j)]
  simp_rw [exponentMonomial_zero_first_row H A hA,
    exponentMonomial_zero_first_row H.transpose A hA]
  exact Sampling.average_dropFirst hp
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H (fun i j => A i.succ j) ρ κ).re +
        (exponentMonomial H.transpose (fun i j => A i.succ j) ρ κ).re) / 2))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Canonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small semantic steps used by the generated canonicalization traces. Each
step preserves the actual averaged injective moment. The finite side conditions
(state dimensions, permutation inverses, and zero entries) are checked separately.
-/
noncomputable section
namespace MUB6.Certificate

/-- Move a zero row to the front and delete it. -/
theorem moment_delete_zero_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (σ : Equiv.Perm (Fin (p + 1)))
    (hzero : ∀ j, A (σ 0) j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i.succ) j) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i.succ) j) :=
      injectiveMoment_zero_first_row hp H _ hzero

/-- The column version uses the transpose symmetry already present in the
manuscript's normalization. -/
theorem moment_delete_zero_column {p q : ℕ} (hq : q < 6) (H : CMatrix)
    (A : Matrix (Fin p) (Fin (q + 1)) ℤ) (σ : Equiv.Perm (Fin (q + 1)))
    (hzero : ∀ i, A i (σ 0) = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A i (σ j.succ)) := by
  calc
    injectiveMoment H A = injectiveMoment H A.transpose :=
      (injectiveMoment_transpose H A).symm
    _ = injectiveMoment H (fun i j => A.transpose (σ i.succ) j) :=
      moment_delete_zero_row hq H A.transpose σ hzero
    _ = injectiveMoment H (fun i j => A i (σ j.succ)) :=
      injectiveMoment_transpose H (fun i j => A i (σ j.succ))

/-- Simultaneous row and column relabeling. -/
theorem moment_permute {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ)
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) (τ j)) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i) (τ j)) :=
      (injectiveMoment_column_permutation H (fun i j => A (σ i) j) τ).symm

end MUB6.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Interpretation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindexing and averaging preserve the interpretation of sparse forms.
These algebraic facts connect finite checked coefficients to actual moments. -/
namespace MUB6.Certificate

namespace Sparse

variable {ι κ Ω : Type*}

theorem eval_average [Fintype Ω] (v : Sparse ι) (x : Ω → ι → ℝ) :
    eval v (fun i => average (fun ω => x ω i)) =
      average (fun ω => eval v (x ω)) := by
  induction v with
  | nil => simp
  | cons p v ih =>
    simp only [eval_cons, average_add, average_mul, ih]

end Sparse

end MUB6.Certificate

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_PartitionExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    {z : ℂ} (hz : z ≠ 0) : (∏ i ∈ s, z ^ a i) = z ^ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hz]

theorem product_grouped {n k : ℕ} (label : Fin n → Fin k)
    (x : Fin k → ℂ) (hx : ∀ b, x b ≠ 0) (a : Fin n → ℤ) :
    (∏ j, x (label j) ^ a j) = ∏ b, x b ^ (∑ j with label j = b, a j) := by
  rw [← Finset.prod_fiberwise Finset.univ label]
  apply Finset.prod_congr rfl
  intro b _
  rw [← prod_zpow_eq_zpow_sum _ a (hx b)]
  apply Finset.prod_congr rfl
  intro j hj
  rw [(Finset.mem_filter.mp hj).2]

theorem rawMonomial_grouped {p n k : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin k)
    (ρ : Fin p ↪ Coord) (κ : Fin k ↪ Coord) :
    rawMonomial H A ρ (fun j => κ (label j)) =
      exponentMonomial H (groupedColumns A label) ρ κ := by
  unfold rawMonomial exponentMonomial groupedColumns
  apply Finset.prod_congr rfl
  intro i _
  exact product_grouped label (fun b => H (ρ i) (κ b))
    (fun b => unit_ne_zero (hH.1 _ _)) (fun j => A i j)

theorem rowFourier_product_expand {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) (ρ : Fin p ↪ Coord) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ κ : Fin n → Coord, rawMonomial H A ρ κ := by
  simp only [rowFourier, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [Fintype.prod_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro κ _
  exact Finset.prod_comm

/-- The unnormalized equality-partition identity. The factor `(6)_k` in
the manuscript is exactly the cardinality of the inner injection type. -/
theorem rowFourier_partition_expand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        exponentMonomial H (groupedColumns A (F.label s)) ρ κ := by
  rw [rowFourier_product_expand]
  have hs := (F.assignmentsEquiv cover).sum_comp
    (fun κ : Fin n → Coord => rawMonomial H A ρ κ)
  change (∑ s : Σ s, Fin (F.blocks s) ↪ Coord,
    rawMonomial H A ρ (fun i => s.2 (F.label s.1 i))) = _ at hs
  rw [Fintype.sum_sigma] at hs
  rw [← hs]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro κ _
  exact rawMonomial_grouped hH A (F.label s) ρ κ

end MUB6

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SmallPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.EqualityPatterns

theorem pattern3_0 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (_h20 : f 2 = f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 0 i = family3.label 0 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_1 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (h20 : f 2 ≠ f 0)
    (_h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 1 i = family3.label 1 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_2 {B : Type*} (f : Fin 3 → B)
    (_h10 : f 1 ≠ f 0)
    (h20 : f 2 = f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 2 i = family3.label 2 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_3 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (_h20 : f 2 ≠ f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 3 i = family3.label 3 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_4 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (h20 : f 2 ≠ f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 4 i = family3.label 4 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm] <;> grind

theorem covers3 {B : Type*} (f : Fin 3 → B) :
    ∃ p, ∀ i j, (family3.label p i = family3.label p j ↔ f i = f j) := by
  classical
  by_cases h10 : f 1 = f 0
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨0, ?_⟩
      apply pattern3_0 f <;> simp_all [eq_comm]
    ·
      refine ⟨1, ?_⟩
      apply pattern3_1 f <;> simp_all [eq_comm]
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨2, ?_⟩
      apply pattern3_2 f <;> simp_all [eq_comm]
    ·
      by_cases h21 : f 2 = f 1
      ·
        refine ⟨3, ?_⟩
        apply pattern3_3 f <;> simp_all [eq_comm]
      ·
        refine ⟨4, ?_⟩
        apply pattern3_4 f <;> simp_all [eq_comm]

end MUB6.EqualityPatterns

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_NormalizedPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem inverse_six_pow_real (n : ℕ) :
    (6 : ℂ)⁻¹ ^ n = (((6 : ℝ)⁻¹ ^ n : ℝ) : ℂ) := by
  simp

theorem partition_integrand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    ((∏ j, rowFourier H ρ (fun i => A i j)).re +
      (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re) / 2 =
      (6 : ℝ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        ((exponentMonomial H (groupedColumns A (F.label s)) ρ κ).re +
          (exponentMonomial H.transpose (groupedColumns A (F.label s)) ρ κ).re) / 2 := by
  rw [rowFourier_partition_expand hH A ρ F cover,
    rowFourier_partition_expand hH.transpose A ρ F cover, inverse_six_pow_real]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.re_sum, div_eq_mul_inv, ← Finset.sum_mul,
    Finset.sum_add_distrib]
  ring

theorem average_injection_sum {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    average (fun ρ : Fin p ↪ Coord => ∑ κ : Fin q ↪ Coord,
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2) =
      (Fintype.card (Fin q ↪ Coord) : ℝ) * injectiveMoment H A := by
  have he (ρ : Fin p ↪ Coord) := sum_eq_card_mul_average
    (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2)
  simp_rw [he]
  rw [average_mul, ← injectiveMoment_iterated H A]

/-- The normalized equality-pattern expansion. For k blocks the coefficient
is `card (Fin k ↪ Fin 6) / 6^n`, exactly `(6)_k / 6^n` in the source. -/
theorem averagedRowProducts_partition {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    averagedRowProducts H A =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        injectiveMoment H (groupedColumns A (F.label s)) := by
  unfold averagedRowProducts
  simp_rw [partition_integrand hH A _ F cover]
  rw [average_mul, average_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [average_injection_sum H (groupedColumns A (F.label s))]
  simp only [div_eq_mul_inv, inv_pow]
  ring

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_OrderedPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem familyAverage_add (B : Fin 7 → Basis) (F G : CMatrix → ℝ) :
    familyAverage B (fun H => F H + G H) = familyAverage B F + familyAverage B G := by
  simp only [familyAverage, average_add]

theorem familyAverage_mul (B : Fin 7 → Basis) (c : ℝ) (F : CMatrix → ℝ) :
    familyAverage B (fun H => c * F H) = c * familyAverage B F := by
  simp only [familyAverage, average_mul]

theorem relativeMatrix_reverse (B : Fin 7 → Basis) (p : Fin 7 × Coord) :
    relativeMatrix B (reversePair p).1 (reversePair p).2 =
      (relativeMatrix B p.1 p.2).conjTranspose := by
  simp only [relativeMatrix, reversePair, Fin.succAbove_succAbove_predAbove]
  exact transition_reverse _ _

theorem familyAverage_transpose (B : Fin 7 → Basis) (F : CMatrix → ℝ)
    (hF : ∀ H, F (fun i j => conj (H i j)) = F H) :
    familyAverage B (fun H => F H.transpose) = familyAverage B F := by
  change (average (fun r : Fin 7 => average (fun s : Coord => F ((relativeMatrix B r s).transpose)))) =
    average (fun r : Fin 7 => average (fun s : Coord => F (relativeMatrix B r s)))
  rw [← average_prod (fun p : Fin 7 × Coord => F ((relativeMatrix B p.1 p.2).transpose)),
    ← average_prod (fun p : Fin 7 × Coord => F (relativeMatrix B p.1 p.2))]
  have h (p : Fin 7 × Coord) :
      F ((relativeMatrix B p.1 p.2).transpose) =
        F (relativeMatrix B (reversePair p).1 (reversePair p).2) := by
    rw [relativeMatrix_reverse]
    exact (hF ((relativeMatrix B p.1 p.2).transpose)).symm
  simp_rw [h]
  exact average_equiv reversePairEquiv (fun p => F (relativeMatrix B p.1 p.2))

theorem rowFourier_conjugate {p : ℕ} (H : CMatrix) (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier (fun i j => conj (H i j)) ρ a = conj (rowFourier H ρ a) := by
  simp only [rowFourier, map_mul, map_sum, map_prod, map_zpow₀, map_inv₀, map_ofNat]

theorem unorientedRowProducts_conjugate {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    unorientedRowProducts (fun i j => conj (H i j)) A = unorientedRowProducts H A := by
  apply average_congr
  intro ρ
  simp only [rowFourier_conjugate, ← map_prod, Complex.conj_re]

theorem averagedRowProducts_split {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    averagedRowProducts H A =
      (1 / 2 : ℝ) * unorientedRowProducts H A +
        (1 / 2 : ℝ) * unorientedRowProducts H.transpose A := by
  have h (ρ : Fin p ↪ Coord) :
      ((∏ j, rowFourier H ρ (fun i => A i j)).re +
        (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re) / 2 =
      (1 / 2 : ℝ) * (∏ j, rowFourier H ρ (fun i => A i j)).re +
        (1 / 2 : ℝ) * (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re := by ring
  simp only [averagedRowProducts, h, average_add, average_mul, unorientedRowProducts]

theorem familyAverage_averagedRowProducts {p n : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    familyAverage B (fun H => averagedRowProducts H A) =
      familyAverage B (fun H => unorientedRowProducts H A) := by
  simp only [averagedRowProducts_split, familyAverage_add, familyAverage_mul]
  rw [familyAverage_transpose B (fun H => unorientedRowProducts H A)
    (fun H => unorientedRowProducts_conjugate H A)]
  ring

theorem mixedMoment_single_label {p n : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      familyAverage B (fun H => unorientedRowProducts H A) := by
  apply average_congr
  intro r
  have h (ρ : Fin p ↪ Coord) :
      average (fun τ : Fin 1 ↪ Coord =>
        (mixedIntegrand B A (fun _ => (0 : Fin 1)) r ρ τ).re) =
      average (fun s : Coord => (∏ j, rowFourier (relativeMatrix B r s) ρ (fun i => A i j)).re) := by
    exact average_equiv singletonEmbeddingEquiv
      (fun s => (∏ j, rowFourier (relativeMatrix B r s) ρ (fun i => A i j)).re)
  simp_rw [h]
  exact average_comm _

/-- Single-label mixed moments expand into the manuscript's transpose-averaged
pair moments with the exact falling-factorial weights. -/
theorem mixedMoment_single_label_partition {p n : ℕ} {P : Type*} [Fintype P]
    (B : Fin 7 → Basis) (hB : IsMUBFamily B) (A : Matrix (Fin p) (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        familyPairMoment B (groupedColumns A (F.label s)) := by
  rw [mixedMoment_single_label, ← familyAverage_averagedRowProducts]
  unfold familyAverage
  simp_rw [averagedRowProducts_partition (relativeMatrix_isHadamard B hB _ _) A F cover,
    average_sum, average_mul]
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical78 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw78 raw78Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw78 raw78Labels = mixedMoment B raw78step0 raw78step0Labels := by
      have ha : raw78step0 = (fun i j => raw78 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw78step0 raw78; decide +kernel
      have hl : raw78step0Labels = raw78Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw78 raw78Labels permutation8 permutation5
    mixedMoment B raw78step0 raw78step0Labels = mixedMoment B raw78step1 raw78step1Labels := by
      have ha : raw78step1 = raw78step0 := by apply Matrix.ext; unfold raw78step1 raw78step0; decide +kernel
      have hl : raw78step0Labels = labelEmbedding1 ∘ raw78step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw78step0 raw78step0Labels raw78step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1301 node1301Labels := by rfl

theorem canonical79 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw79 raw79Labels = mixedMoment B node157 node157Labels := by
  calc
    mixedMoment B raw79 raw79Labels = mixedMoment B raw79step0 raw79step0Labels := by
      have ha : raw79step0 = (fun i j => raw79 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw79step0 raw79; decide +kernel
      have hl : raw79step0Labels = raw79Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw79 raw79Labels permutation10 permutation4
    _ = mixedMoment B node157 node157Labels := by rfl

theorem canonical82 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw82 raw82Labels = mixedMoment B node1304 node1304Labels := by
  calc
    mixedMoment B raw82 raw82Labels = mixedMoment B raw82step0 raw82step0Labels := by
      have ha : raw82step0 = (fun i j => raw82 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw82step0 raw82; decide +kernel
      have hl : raw82step0Labels = raw82Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw82 raw82Labels permutation2 permutation5
    mixedMoment B raw82step0 raw82step0Labels = mixedMoment B raw82step1 raw82step1Labels := by
      have ha : raw82step1 = raw82step0 := by apply Matrix.ext; unfold raw82step1 raw82step0; decide +kernel
      have hl : raw82step0Labels = labelEmbedding1 ∘ raw82step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw82step0 raw82step0Labels raw82step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1304 node1304Labels := by rfl

theorem canonical83 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw83 raw83Labels = mixedMoment B node158 node158Labels := by
  calc
    mixedMoment B raw83 raw83Labels = mixedMoment B raw83step0 raw83step0Labels := by
      have ha : raw83step0 = (fun i j => raw83 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw83step0 raw83; decide +kernel
      have hl : raw83step0Labels = raw83Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw83 raw83Labels permutation2 permutation5
    _ = mixedMoment B node158 node158Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical1323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1323 raw1323Labels = mixedMoment B node4517 node4517Labels := by
  calc
    mixedMoment B raw1323 raw1323Labels = mixedMoment B raw1323step0 raw1323step0Labels := by
      have ha : raw1323step0 = (fun i j => raw1323 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1323step0 raw1323; decide +kernel
      have hl : raw1323step0Labels = raw1323Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1323 raw1323Labels permutation32 permutation4
    mixedMoment B raw1323step0 raw1323step0Labels = mixedMoment B raw1323step1 raw1323step1Labels := by
      have ha : raw1323step1 = raw1323step0 := by apply Matrix.ext; unfold raw1323step1 raw1323step0; decide +kernel
      have hl : raw1323step0Labels = labelEmbedding7 ∘ raw1323step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1323step0 raw1323step0Labels raw1323step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4517 node4517Labels := by rfl

theorem canonical1324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1324 raw1324Labels = mixedMoment B node1101 node1101Labels := by
  calc
    mixedMoment B raw1324 raw1324Labels = mixedMoment B raw1324step0 raw1324step0Labels := by
      have ha : raw1324step0 = (fun i j => raw1324 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1324step0 raw1324; decide +kernel
      have hl : raw1324step0Labels = raw1324Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1324 raw1324Labels permutation32 permutation4
    _ = mixedMoment B node1101 node1101Labels := by rfl

theorem canonical1325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1325 raw1325Labels = mixedMoment B node3235 node3235Labels := by
  calc
    mixedMoment B raw1325 raw1325Labels = mixedMoment B raw1325step0 raw1325step0Labels := by
      have ha : raw1325step0 = (fun i j => raw1325 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1325step0 raw1325; decide +kernel
      have hl : raw1325step0Labels = raw1325Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1325 raw1325Labels permutation32 permutation6
    mixedMoment B raw1325step0 raw1325step0Labels = mixedMoment B raw1325step1 raw1325step1Labels := by
      have ha : raw1325step1 = -raw1325step0 := by apply Matrix.ext; change ∀ i j, raw1325step1 i j = -(raw1325step0 i j); unfold raw1325step1 raw1325step0; decide +kernel
      have hl : raw1325step1Labels = raw1325step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1325step1 raw1325step1Labels = mixedMoment B raw1325step2 raw1325step2Labels := by
      have ha : raw1325step2 = raw1325step1 := by apply Matrix.ext; unfold raw1325step2 raw1325step1; decide +kernel
      have hl : raw1325step1Labels = labelEmbedding1 ∘ raw1325step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1325step1 raw1325step1Labels raw1325step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3235 node3235Labels := by rfl

theorem canonical1332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1332 raw1332Labels = mixedMoment B node4520 node4520Labels := by
  calc
    mixedMoment B raw1332 raw1332Labels = mixedMoment B raw1332step0 raw1332step0Labels := by
      have ha : raw1332step0 = (fun i j => raw1332 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1332step0 raw1332; decide +kernel
      have hl : raw1332step0Labels = raw1332Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1332 raw1332Labels permutation8 permutation4
    mixedMoment B raw1332step0 raw1332step0Labels = mixedMoment B raw1332step1 raw1332step1Labels := by
      have ha : raw1332step1 = raw1332step0 := by apply Matrix.ext; unfold raw1332step1 raw1332step0; decide +kernel
      have hl : raw1332step0Labels = labelEmbedding7 ∘ raw1332step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1332step0 raw1332step0Labels raw1332step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4520 node4520Labels := by rfl

theorem canonical1333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1333 raw1333Labels = mixedMoment B node1104 node1104Labels := by
  calc
    mixedMoment B raw1333 raw1333Labels = mixedMoment B raw1333step0 raw1333step0Labels := by
      have ha : raw1333step0 = (fun i j => raw1333 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1333step0 raw1333; decide +kernel
      have hl : raw1333step0Labels = raw1333Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1333 raw1333Labels permutation8 permutation4
    _ = mixedMoment B node1104 node1104Labels := by rfl

theorem canonical1334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1334 raw1334Labels = mixedMoment B node3237 node3237Labels := by
  calc
    mixedMoment B raw1334 raw1334Labels = mixedMoment B raw1334step0 raw1334step0Labels := by
      have ha : raw1334step0 = (fun i j => raw1334 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1334step0 raw1334; decide +kernel
      have hl : raw1334step0Labels = raw1334Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1334 raw1334Labels permutation8 permutation6
    mixedMoment B raw1334step0 raw1334step0Labels = mixedMoment B raw1334step1 raw1334step1Labels := by
      have ha : raw1334step1 = -raw1334step0 := by apply Matrix.ext; change ∀ i j, raw1334step1 i j = -(raw1334step0 i j); unfold raw1334step1 raw1334step0; decide +kernel
      have hl : raw1334step1Labels = raw1334step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1334step1 raw1334step1Labels = mixedMoment B raw1334step2 raw1334step2Labels := by
      have ha : raw1334step2 = raw1334step1 := by apply Matrix.ext; unfold raw1334step2 raw1334step1; decide +kernel
      have hl : raw1334step1Labels = labelEmbedding1 ∘ raw1334step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1334step1 raw1334step1Labels raw1334step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3237 node3237Labels := by rfl

theorem canonical1341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1341 raw1341Labels = mixedMoment B node4523 node4523Labels := by
  calc
    mixedMoment B raw1341 raw1341Labels = mixedMoment B raw1341step0 raw1341step0Labels := by
      have ha : raw1341step0 = (fun i j => raw1341 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1341step0 raw1341; decide +kernel
      have hl : raw1341step0Labels = raw1341Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1341 raw1341Labels permutation152 permutation4
    mixedMoment B raw1341step0 raw1341step0Labels = mixedMoment B raw1341step1 raw1341step1Labels := by
      have ha : raw1341step1 = raw1341step0 := by apply Matrix.ext; unfold raw1341step1 raw1341step0; decide +kernel
      have hl : raw1341step0Labels = labelEmbedding7 ∘ raw1341step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1341step0 raw1341step0Labels raw1341step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4523 node4523Labels := by rfl

theorem canonical1342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1342 raw1342Labels = mixedMoment B node1107 node1107Labels := by
  calc
    mixedMoment B raw1342 raw1342Labels = mixedMoment B raw1342step0 raw1342step0Labels := by
      have ha : raw1342step0 = (fun i j => raw1342 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1342step0 raw1342; decide +kernel
      have hl : raw1342step0Labels = raw1342Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1342 raw1342Labels permutation152 permutation4
    _ = mixedMoment B node1107 node1107Labels := by rfl

theorem canonical1343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1343 raw1343Labels = mixedMoment B node3250 node3250Labels := by
  calc
    mixedMoment B raw1343 raw1343Labels = mixedMoment B raw1343step0 raw1343step0Labels := by
      have ha : raw1343step0 = (fun i j => raw1343 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1343step0 raw1343; decide +kernel
      have hl : raw1343step0Labels = raw1343Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1343 raw1343Labels permutation152 permutation6
    mixedMoment B raw1343step0 raw1343step0Labels = mixedMoment B raw1343step1 raw1343step1Labels := by
      have ha : raw1343step1 = -raw1343step0 := by apply Matrix.ext; change ∀ i j, raw1343step1 i j = -(raw1343step0 i j); unfold raw1343step1 raw1343step0; decide +kernel
      have hl : raw1343step1Labels = raw1343step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1343step1 raw1343step1Labels = mixedMoment B raw1343step2 raw1343step2Labels := by
      have ha : raw1343step2 = raw1343step1 := by apply Matrix.ext; unfold raw1343step2 raw1343step1; decide +kernel
      have hl : raw1343step1Labels = labelEmbedding1 ∘ raw1343step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1343step1 raw1343step1Labels raw1343step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3250 node3250Labels := by rfl

theorem canonical1350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1350 raw1350Labels = mixedMoment B node4526 node4526Labels := by
  calc
    mixedMoment B raw1350 raw1350Labels = mixedMoment B raw1350step0 raw1350step0Labels := by
      have ha : raw1350step0 = (fun i j => raw1350 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1350step0 raw1350; decide +kernel
      have hl : raw1350step0Labels = raw1350Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1350 raw1350Labels permutation32 permutation4
    mixedMoment B raw1350step0 raw1350step0Labels = mixedMoment B raw1350step1 raw1350step1Labels := by
      have ha : raw1350step1 = raw1350step0 := by apply Matrix.ext; unfold raw1350step1 raw1350step0; decide +kernel
      have hl : raw1350step0Labels = labelEmbedding7 ∘ raw1350step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1350step0 raw1350step0Labels raw1350step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4526 node4526Labels := by rfl

theorem canonical1351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1351 raw1351Labels = mixedMoment B node1110 node1110Labels := by
  calc
    mixedMoment B raw1351 raw1351Labels = mixedMoment B raw1351step0 raw1351step0Labels := by
      have ha : raw1351step0 = (fun i j => raw1351 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1351step0 raw1351; decide +kernel
      have hl : raw1351step0Labels = raw1351Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1351 raw1351Labels permutation32 permutation4
    _ = mixedMoment B node1110 node1110Labels := by rfl

theorem canonical1352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1352 raw1352Labels = mixedMoment B node3252 node3252Labels := by
  calc
    mixedMoment B raw1352 raw1352Labels = mixedMoment B raw1352step0 raw1352step0Labels := by
      have ha : raw1352step0 = (fun i j => raw1352 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1352step0 raw1352; decide +kernel
      have hl : raw1352step0Labels = raw1352Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1352 raw1352Labels permutation32 permutation6
    mixedMoment B raw1352step0 raw1352step0Labels = mixedMoment B raw1352step1 raw1352step1Labels := by
      have ha : raw1352step1 = -raw1352step0 := by apply Matrix.ext; change ∀ i j, raw1352step1 i j = -(raw1352step0 i j); unfold raw1352step1 raw1352step0; decide +kernel
      have hl : raw1352step1Labels = raw1352step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1352step1 raw1352step1Labels = mixedMoment B raw1352step2 raw1352step2Labels := by
      have ha : raw1352step2 = raw1352step1 := by apply Matrix.ext; unfold raw1352step2 raw1352step1; decide +kernel
      have hl : raw1352step1Labels = labelEmbedding1 ∘ raw1352step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1352step1 raw1352step1Labels raw1352step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3252 node3252Labels := by rfl

theorem canonical1371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1371 raw1371Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw1371 raw1371Labels = mixedMoment B raw1371step0 raw1371step0Labels := by
      have ha : raw1371step0 = (fun i j => raw1371 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1371step0 raw1371; decide +kernel
      have hl : raw1371step0Labels = raw1371Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1371 raw1371Labels permutation32 permutation4
    mixedMoment B raw1371step0 raw1371step0Labels = mixedMoment B raw1371step1 raw1371step1Labels := by
      have ha : raw1371step1 = raw1371step0 := by apply Matrix.ext; unfold raw1371step1 raw1371step0; decide +kernel
      have hl : raw1371step0Labels = labelEmbedding7 ∘ raw1371step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1371step0 raw1371step0Labels raw1371step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4546 node4546Labels := by rfl

theorem canonical1372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1372 raw1372Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw1372 raw1372Labels = mixedMoment B raw1372step0 raw1372step0Labels := by
      have ha : raw1372step0 = (fun i j => raw1372 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1372step0 raw1372; decide +kernel
      have hl : raw1372step0Labels = raw1372Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1372 raw1372Labels permutation32 permutation4
    _ = mixedMoment B node1131 node1131Labels := by rfl

theorem canonical1373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1373 raw1373Labels = mixedMoment B node3264 node3264Labels := by
  calc
    mixedMoment B raw1373 raw1373Labels = mixedMoment B raw1373step0 raw1373step0Labels := by
      have ha : raw1373step0 = (fun i j => raw1373 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1373step0 raw1373; decide +kernel
      have hl : raw1373step0Labels = raw1373Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1373 raw1373Labels permutation32 permutation6
    mixedMoment B raw1373step0 raw1373step0Labels = mixedMoment B raw1373step1 raw1373step1Labels := by
      have ha : raw1373step1 = -raw1373step0 := by apply Matrix.ext; change ∀ i j, raw1373step1 i j = -(raw1373step0 i j); unfold raw1373step1 raw1373step0; decide +kernel
      have hl : raw1373step1Labels = raw1373step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1373step1 raw1373step1Labels = mixedMoment B raw1373step2 raw1373step2Labels := by
      have ha : raw1373step2 = raw1373step1 := by apply Matrix.ext; unfold raw1373step2 raw1373step1; decide +kernel
      have hl : raw1373step1Labels = labelEmbedding1 ∘ raw1373step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1373step1 raw1373step1Labels raw1373step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3264 node3264Labels := by rfl

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

theorem canonical1434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1434 raw1434Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw1434 raw1434Labels = mixedMoment B raw1434step0 raw1434step0Labels := by
      have ha : raw1434step0 = (fun i j => raw1434 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1434step0 raw1434; decide +kernel
      have hl : raw1434step0Labels = raw1434Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1434 raw1434Labels permutation8 permutation4
    mixedMoment B raw1434step0 raw1434step0Labels = mixedMoment B raw1434step1 raw1434step1Labels := by
      have ha : raw1434step1 = raw1434step0 := by apply Matrix.ext; unfold raw1434step1 raw1434step0; decide +kernel
      have hl : raw1434step0Labels = labelEmbedding7 ∘ raw1434step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1434step0 raw1434step0Labels raw1434step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

theorem canonical1435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1435 raw1435Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw1435 raw1435Labels = mixedMoment B raw1435step0 raw1435step0Labels := by
      have ha : raw1435step0 = (fun i j => raw1435 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1435step0 raw1435; decide +kernel
      have hl : raw1435step0Labels = raw1435Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1435 raw1435Labels permutation8 permutation4
    _ = mixedMoment B node1242 node1242Labels := by rfl

theorem canonical1436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1436 raw1436Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw1436 raw1436Labels = mixedMoment B raw1436step0 raw1436step0Labels := by
      have ha : raw1436step0 = (fun i j => raw1436 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1436step0 raw1436; decide +kernel
      have hl : raw1436step0Labels = raw1436Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1436 raw1436Labels permutation8 permutation6
    mixedMoment B raw1436step0 raw1436step0Labels = mixedMoment B raw1436step1 raw1436step1Labels := by
      have ha : raw1436step1 = -raw1436step0 := by apply Matrix.ext; change ∀ i j, raw1436step1 i j = -(raw1436step0 i j); unfold raw1436step1 raw1436step0; decide +kernel
      have hl : raw1436step1Labels = raw1436step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1436step1 raw1436step1Labels = mixedMoment B raw1436step2 raw1436step2Labels := by
      have ha : raw1436step2 = raw1436step1 := by apply Matrix.ext; unfold raw1436step2 raw1436step1; decide +kernel
      have hl : raw1436step1Labels = labelEmbedding1 ∘ raw1436step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1436step1 raw1436step1Labels raw1436step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3300 node3300Labels := by rfl

theorem canonical1437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1437 raw1437Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw1437 raw1437Labels = mixedMoment B raw1437step0 raw1437step0Labels := by
      have ha : raw1437step0 = (fun i j => raw1437 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1437step0 raw1437; decide +kernel
      have hl : raw1437step0Labels = raw1437Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1437 raw1437Labels permutation8 permutation4
    mixedMoment B raw1437step0 raw1437step0Labels = mixedMoment B raw1437step1 raw1437step1Labels := by
      have ha : raw1437step1 = raw1437step0 := by apply Matrix.ext; unfold raw1437step1 raw1437step0; decide +kernel
      have hl : raw1437step0Labels = labelEmbedding7 ∘ raw1437step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1437step0 raw1437step0Labels raw1437step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical1438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1438 raw1438Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw1438 raw1438Labels = mixedMoment B raw1438step0 raw1438step0Labels := by
      have ha : raw1438step0 = (fun i j => raw1438 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1438step0 raw1438; decide +kernel
      have hl : raw1438step0Labels = raw1438Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1438 raw1438Labels permutation8 permutation4
    _ = mixedMoment B node1246 node1246Labels := by rfl

theorem canonical1439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1439 raw1439Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw1439 raw1439Labels = mixedMoment B raw1439step0 raw1439step0Labels := by
      have ha : raw1439step0 = (fun i j => raw1439 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1439step0 raw1439; decide +kernel
      have hl : raw1439step0Labels = raw1439Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1439 raw1439Labels permutation8 permutation6
    mixedMoment B raw1439step0 raw1439step0Labels = mixedMoment B raw1439step1 raw1439step1Labels := by
      have ha : raw1439step1 = -raw1439step0 := by apply Matrix.ext; change ∀ i j, raw1439step1 i j = -(raw1439step0 i j); unfold raw1439step1 raw1439step0; decide +kernel
      have hl : raw1439step1Labels = raw1439step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1439step1 raw1439step1Labels = mixedMoment B raw1439step2 raw1439step2Labels := by
      have ha : raw1439step2 = raw1439step1 := by apply Matrix.ext; unfold raw1439step2 raw1439step1; decide +kernel
      have hl : raw1439step1Labels = labelEmbedding1 ∘ raw1439step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1439step1 raw1439step1Labels raw1439step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3301 node3301Labels := by rfl

theorem canonical1455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1455 raw1455Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw1455 raw1455Labels = mixedMoment B raw1455step0 raw1455step0Labels := by
      have ha : raw1455step0 = (fun i j => raw1455 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1455step0 raw1455; decide +kernel
      have hl : raw1455step0Labels = raw1455Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1455 raw1455Labels permutation8 permutation4
    mixedMoment B raw1455step0 raw1455step0Labels = mixedMoment B raw1455step1 raw1455step1Labels := by
      have ha : raw1455step1 = raw1455step0 := by apply Matrix.ext; unfold raw1455step1 raw1455step0; decide +kernel
      have hl : raw1455step0Labels = labelEmbedding7 ∘ raw1455step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1455step0 raw1455step0Labels raw1455step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4624 node4624Labels := by rfl

theorem canonical1456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1456 raw1456Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw1456 raw1456Labels = mixedMoment B raw1456step0 raw1456step0Labels := by
      have ha : raw1456step0 = (fun i j => raw1456 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1456step0 raw1456; decide +kernel
      have hl : raw1456step0Labels = raw1456Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1456 raw1456Labels permutation8 permutation4
    _ = mixedMoment B node1301 node1301Labels := by rfl

theorem canonical1457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1457 raw1457Labels = mixedMoment B node3309 node3309Labels := by
  calc
    mixedMoment B raw1457 raw1457Labels = mixedMoment B raw1457step0 raw1457step0Labels := by
      have ha : raw1457step0 = (fun i j => raw1457 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1457step0 raw1457; decide +kernel
      have hl : raw1457step0Labels = raw1457Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1457 raw1457Labels permutation10 permutation3
    mixedMoment B raw1457step0 raw1457step0Labels = mixedMoment B raw1457step1 raw1457step1Labels := by
      have ha : raw1457step1 = -raw1457step0 := by apply Matrix.ext; change ∀ i j, raw1457step1 i j = -(raw1457step0 i j); unfold raw1457step1 raw1457step0; decide +kernel
      have hl : raw1457step1Labels = raw1457step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1457step1 raw1457step1Labels = mixedMoment B raw1457step2 raw1457step2Labels := by
      have ha : raw1457step2 = raw1457step1 := by apply Matrix.ext; unfold raw1457step2 raw1457step1; decide +kernel
      have hl : raw1457step1Labels = labelEmbedding1 ∘ raw1457step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1457step1 raw1457step1Labels raw1457step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3309 node3309Labels := by rfl

theorem canonical1458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1458 raw1458Labels = mixedMoment B node4625 node4625Labels := by
  calc
    mixedMoment B raw1458 raw1458Labels = mixedMoment B raw1458step0 raw1458step0Labels := by
      have ha : raw1458step0 = (fun i j => raw1458 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1458step0 raw1458; decide +kernel
      have hl : raw1458step0Labels = raw1458Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1458 raw1458Labels permutation2 permutation4
    mixedMoment B raw1458step0 raw1458step0Labels = mixedMoment B raw1458step1 raw1458step1Labels := by
      have ha : raw1458step1 = raw1458step0 := by apply Matrix.ext; unfold raw1458step1 raw1458step0; decide +kernel
      have hl : raw1458step0Labels = labelEmbedding7 ∘ raw1458step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1458step0 raw1458step0Labels raw1458step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4625 node4625Labels := by rfl

theorem canonical1459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1459 raw1459Labels = mixedMoment B node1304 node1304Labels := by
  calc
    mixedMoment B raw1459 raw1459Labels = mixedMoment B raw1459step0 raw1459step0Labels := by
      have ha : raw1459step0 = (fun i j => raw1459 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1459step0 raw1459; decide +kernel
      have hl : raw1459step0Labels = raw1459Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1459 raw1459Labels permutation2 permutation4
    _ = mixedMoment B node1304 node1304Labels := by rfl

theorem canonical1460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1460 raw1460Labels = mixedMoment B node3310 node3310Labels := by
  calc
    mixedMoment B raw1460 raw1460Labels = mixedMoment B raw1460step0 raw1460step0Labels := by
      have ha : raw1460step0 = (fun i j => raw1460 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1460step0 raw1460; decide +kernel
      have hl : raw1460step0Labels = raw1460Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1460 raw1460Labels permutation2 permutation6
    mixedMoment B raw1460step0 raw1460step0Labels = mixedMoment B raw1460step1 raw1460step1Labels := by
      have ha : raw1460step1 = -raw1460step0 := by apply Matrix.ext; change ∀ i j, raw1460step1 i j = -(raw1460step0 i j); unfold raw1460step1 raw1460step0; decide +kernel
      have hl : raw1460step1Labels = raw1460step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1460step1 raw1460step1Labels = mixedMoment B raw1460step2 raw1460step2Labels := by
      have ha : raw1460step2 = raw1460step1 := by apply Matrix.ext; unfold raw1460step2 raw1460step1; decide +kernel
      have hl : raw1460step1Labels = labelEmbedding1 ∘ raw1460step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1460step1 raw1460step1Labels raw1460step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3310 node3310Labels := by rfl

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

theorem canonical15022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15022 raw15022Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw15022 raw15022Labels = mixedMoment B raw15022step0 raw15022step0Labels := by
      have hz : ∀ j, raw15022 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15022step0 = (fun i j => raw15022 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15022step0 raw15022; decide +kernel
      have hl : raw15022step0Labels = raw15022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15022 raw15022Labels permutation346 hz
    mixedMoment B raw15022step0 raw15022step0Labels = mixedMoment B raw15022step1 raw15022step1Labels := by
      have hz : ∀ j, raw15022step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw15022step1 = (fun i j => raw15022step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw15022step1 raw15022step0; decide +kernel
      have hl : raw15022step1Labels = raw15022step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15022step0 raw15022step0Labels permutation56 hz
    _ = mixedMoment B node5293 node5293Labels := by rfl

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

theorem canonical2103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2103 raw2103Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw2103 raw2103Labels = mixedMoment B raw2103step0 raw2103step0Labels := by
      have ha : raw2103step0 = (fun i j => raw2103 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2103step0 raw2103; decide +kernel
      have hl : raw2103step0Labels = raw2103Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2103 raw2103Labels permutation32 permutation4
    mixedMoment B raw2103step0 raw2103step0Labels = mixedMoment B raw2103step1 raw2103step1Labels := by
      have ha : raw2103step1 = raw2103step0 := by apply Matrix.ext; unfold raw2103step1 raw2103step0; decide +kernel
      have hl : raw2103step0Labels = labelEmbedding7 ∘ raw2103step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2103step0 raw2103step0Labels raw2103step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

theorem canonical2104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2104 raw2104Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw2104 raw2104Labels = mixedMoment B raw2104step0 raw2104step0Labels := by
      have ha : raw2104step0 = (fun i j => raw2104 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2104step0 raw2104; decide +kernel
      have hl : raw2104step0Labels = raw2104Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2104 raw2104Labels permutation32 permutation4
    _ = mixedMoment B node2485 node2485Labels := by rfl

theorem canonical2105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2105 raw2105Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw2105 raw2105Labels = mixedMoment B raw2105step0 raw2105step0Labels := by
      have ha : raw2105step0 = (fun i j => raw2105 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2105step0 raw2105; decide +kernel
      have hl : raw2105step0Labels = raw2105Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2105 raw2105Labels permutation32 permutation6
    mixedMoment B raw2105step0 raw2105step0Labels = mixedMoment B raw2105step1 raw2105step1Labels := by
      have ha : raw2105step1 = -raw2105step0 := by apply Matrix.ext; change ∀ i j, raw2105step1 i j = -(raw2105step0 i j); unfold raw2105step1 raw2105step0; decide +kernel
      have hl : raw2105step1Labels = raw2105step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2105step1 raw2105step1Labels = mixedMoment B raw2105step2 raw2105step2Labels := by
      have ha : raw2105step2 = raw2105step1 := by apply Matrix.ext; unfold raw2105step2 raw2105step1; decide +kernel
      have hl : raw2105step1Labels = labelEmbedding1 ∘ raw2105step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2105step1 raw2105step1Labels raw2105step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20749 raw20749Labels = mixedMoment B node4144 node4144Labels := by
  calc
    mixedMoment B raw20749 raw20749Labels = mixedMoment B raw20749step0 raw20749step0Labels := by
      have hz : ∀ j, raw20749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20749step0 = (fun i j => raw20749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20749step0 raw20749; decide +kernel
      have hl : raw20749step0Labels = raw20749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20749 raw20749Labels permutation346 hz
    mixedMoment B raw20749step0 raw20749step0Labels = mixedMoment B raw20749step1 raw20749step1Labels := by
      have ha : raw20749step1 = (fun i j => raw20749step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20749step1 raw20749step0; decide +kernel
      have hl : raw20749step1Labels = raw20749step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20749step0 raw20749step0Labels permutation38 permutation3
    mixedMoment B raw20749step1 raw20749step1Labels = mixedMoment B raw20749step2 raw20749step2Labels := by
      have ha : raw20749step2 = raw20749step1 := by apply Matrix.ext; unfold raw20749step2 raw20749step1; decide +kernel
      have hl : raw20749step1Labels = labelEmbedding6 ∘ raw20749step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20749step1 raw20749step1Labels raw20749step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4144 node4144Labels := by rfl

theorem canonical20750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20750 raw20750Labels = mixedMoment B node4523 node4523Labels := by
  calc
    mixedMoment B raw20750 raw20750Labels = mixedMoment B raw20750step0 raw20750step0Labels := by
      have ha : raw20750step0 = (fun i j => raw20750 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20750step0 raw20750; decide +kernel
      have hl : raw20750step0Labels = raw20750Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20750 raw20750Labels permutation182 permutation3
    mixedMoment B raw20750step0 raw20750step0Labels = mixedMoment B raw20750step1 raw20750step1Labels := by
      have ha : raw20750step1 = raw20750step0 := by apply Matrix.ext; unfold raw20750step1 raw20750step0; decide +kernel
      have hl : raw20750step0Labels = labelEmbedding6 ∘ raw20750step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20750step0 raw20750step0Labels raw20750step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4523 node4523Labels := by rfl

theorem canonical20751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20751 raw20751Labels = mixedMoment B node4517 node4517Labels := by
  calc
    mixedMoment B raw20751 raw20751Labels = mixedMoment B raw20751step0 raw20751step0Labels := by
      have hz : ∀ j, raw20751 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20751step0 = (fun i j => raw20751 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20751step0 raw20751; decide +kernel
      have hl : raw20751step0Labels = raw20751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20751 raw20751Labels permutation346 hz
    mixedMoment B raw20751step0 raw20751step0Labels = mixedMoment B raw20751step1 raw20751step1Labels := by
      have ha : raw20751step1 = (fun i j => raw20751step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20751step1 raw20751step0; decide +kernel
      have hl : raw20751step1Labels = raw20751step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20751step0 raw20751step0Labels permutation38 permutation3
    mixedMoment B raw20751step1 raw20751step1Labels = mixedMoment B raw20751step2 raw20751step2Labels := by
      have ha : raw20751step2 = raw20751step1 := by apply Matrix.ext; unfold raw20751step2 raw20751step1; decide +kernel
      have hl : raw20751step1Labels = labelEmbedding6 ∘ raw20751step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20751step1 raw20751step1Labels raw20751step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4517 node4517Labels := by rfl

theorem canonical20752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20752 raw20752Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw20752 raw20752Labels = mixedMoment B raw20752step0 raw20752step0Labels := by
      have hz : ∀ j, raw20752 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20752step0 = (fun i j => raw20752 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20752step0 raw20752; decide +kernel
      have hl : raw20752step0Labels = raw20752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20752 raw20752Labels permutation520 hz
    mixedMoment B raw20752step0 raw20752step0Labels = mixedMoment B raw20752step1 raw20752step1Labels := by
      have hz : ∀ j, raw20752step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20752step1 = (fun i j => raw20752step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20752step1 raw20752step0; decide +kernel
      have hl : raw20752step1Labels = raw20752step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20752step0 raw20752step0Labels permutation80 hz
    mixedMoment B raw20752step1 raw20752step1Labels = mixedMoment B raw20752step2 raw20752step2Labels := by
      have ha : raw20752step2 = (fun i j => raw20752step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20752step2 raw20752step1; decide +kernel
      have hl : raw20752step2Labels = raw20752step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20752step1 raw20752step1Labels permutation10 permutation3
    mixedMoment B raw20752step2 raw20752step2Labels = mixedMoment B raw20752step3 raw20752step3Labels := by
      have ha : raw20752step3 = raw20752step2 := by apply Matrix.ext; unfold raw20752step3 raw20752step2; decide +kernel
      have hl : raw20752step2Labels = labelEmbedding6 ∘ raw20752step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20752step2 raw20752step2Labels raw20752step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

theorem canonical20753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20753 raw20753Labels = mixedMoment B node4144 node4144Labels := by
  calc
    mixedMoment B raw20753 raw20753Labels = mixedMoment B raw20753step0 raw20753step0Labels := by
      have hz : ∀ j, raw20753 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20753step0 = (fun i j => raw20753 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20753step0 raw20753; decide +kernel
      have hl : raw20753step0Labels = raw20753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20753 raw20753Labels permutation265 hz
    mixedMoment B raw20753step0 raw20753step0Labels = mixedMoment B raw20753step1 raw20753step1Labels := by
      have ha : raw20753step1 = (fun i j => raw20753step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20753step1 raw20753step0; decide +kernel
      have hl : raw20753step1Labels = raw20753step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20753step0 raw20753step0Labels permutation38 permutation3
    mixedMoment B raw20753step1 raw20753step1Labels = mixedMoment B raw20753step2 raw20753step2Labels := by
      have ha : raw20753step2 = raw20753step1 := by apply Matrix.ext; unfold raw20753step2 raw20753step1; decide +kernel
      have hl : raw20753step1Labels = labelEmbedding6 ∘ raw20753step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20753step1 raw20753step1Labels raw20753step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4144 node4144Labels := by rfl

theorem canonical20754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20754 raw20754Labels = mixedMoment B node4523 node4523Labels := by
  calc
    mixedMoment B raw20754 raw20754Labels = mixedMoment B raw20754step0 raw20754step0Labels := by
      have ha : raw20754step0 = (fun i j => raw20754 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20754step0 raw20754; decide +kernel
      have hl : raw20754step0Labels = raw20754Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20754 raw20754Labels permutation158 permutation3
    mixedMoment B raw20754step0 raw20754step0Labels = mixedMoment B raw20754step1 raw20754step1Labels := by
      have ha : raw20754step1 = raw20754step0 := by apply Matrix.ext; unfold raw20754step1 raw20754step0; decide +kernel
      have hl : raw20754step0Labels = labelEmbedding6 ∘ raw20754step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20754step0 raw20754step0Labels raw20754step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4523 node4523Labels := by rfl

theorem canonical20755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20755 raw20755Labels = mixedMoment B node4517 node4517Labels := by
  calc
    mixedMoment B raw20755 raw20755Labels = mixedMoment B raw20755step0 raw20755step0Labels := by
      have hz : ∀ j, raw20755 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20755step0 = (fun i j => raw20755 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20755step0 raw20755; decide +kernel
      have hl : raw20755step0Labels = raw20755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20755 raw20755Labels permutation265 hz
    mixedMoment B raw20755step0 raw20755step0Labels = mixedMoment B raw20755step1 raw20755step1Labels := by
      have ha : raw20755step1 = (fun i j => raw20755step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20755step1 raw20755step0; decide +kernel
      have hl : raw20755step1Labels = raw20755step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20755step0 raw20755step0Labels permutation38 permutation3
    mixedMoment B raw20755step1 raw20755step1Labels = mixedMoment B raw20755step2 raw20755step2Labels := by
      have ha : raw20755step2 = raw20755step1 := by apply Matrix.ext; unfold raw20755step2 raw20755step1; decide +kernel
      have hl : raw20755step1Labels = labelEmbedding6 ∘ raw20755step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20755step1 raw20755step1Labels raw20755step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4517 node4517Labels := by rfl

theorem canonical20756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20756 raw20756Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw20756 raw20756Labels = mixedMoment B raw20756step0 raw20756step0Labels := by
      have hz : ∀ j, raw20756 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20756step0 = (fun i j => raw20756 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20756step0 raw20756; decide +kernel
      have hl : raw20756step0Labels = raw20756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20756 raw20756Labels permutation520 hz
    mixedMoment B raw20756step0 raw20756step0Labels = mixedMoment B raw20756step1 raw20756step1Labels := by
      have hz : ∀ j, raw20756step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20756step1 = (fun i j => raw20756step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20756step1 raw20756step0; decide +kernel
      have hl : raw20756step1Labels = raw20756step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20756step0 raw20756step0Labels permutation56 hz
    mixedMoment B raw20756step1 raw20756step1Labels = mixedMoment B raw20756step2 raw20756step2Labels := by
      have ha : raw20756step2 = (fun i j => raw20756step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20756step2 raw20756step1; decide +kernel
      have hl : raw20756step2Labels = raw20756step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20756step1 raw20756step1Labels permutation10 permutation3
    mixedMoment B raw20756step2 raw20756step2Labels = mixedMoment B raw20756step3 raw20756step3Labels := by
      have ha : raw20756step3 = raw20756step2 := by apply Matrix.ext; unfold raw20756step3 raw20756step2; decide +kernel
      have hl : raw20756step2Labels = labelEmbedding6 ∘ raw20756step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20756step2 raw20756step2Labels raw20756step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

theorem canonical20757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20757 raw20757Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw20757 raw20757Labels = mixedMoment B raw20757step0 raw20757step0Labels := by
      have hz : ∀ j, raw20757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20757step0 = (fun i j => raw20757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20757step0 raw20757; decide +kernel
      have hl : raw20757step0Labels = raw20757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20757 raw20757Labels permutation346 hz
    mixedMoment B raw20757step0 raw20757step0Labels = mixedMoment B raw20757step1 raw20757step1Labels := by
      have hz : ∀ j, raw20757step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20757step1 = (fun i j => raw20757step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20757step1 raw20757step0; decide +kernel
      have hl : raw20757step1Labels = raw20757step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20757step0 raw20757step0Labels permutation56 hz
    mixedMoment B raw20757step1 raw20757step1Labels = mixedMoment B raw20757step2 raw20757step2Labels := by
      have ha : raw20757step2 = (fun i j => raw20757step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20757step2 raw20757step1; decide +kernel
      have hl : raw20757step2Labels = raw20757step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20757step1 raw20757step1Labels permutation8 permutation3
    mixedMoment B raw20757step2 raw20757step2Labels = mixedMoment B raw20757step3 raw20757step3Labels := by
      have ha : raw20757step3 = raw20757step2 := by apply Matrix.ext; unfold raw20757step3 raw20757step2; decide +kernel
      have hl : raw20757step2Labels = labelEmbedding6 ∘ raw20757step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20757step2 raw20757step2Labels raw20757step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4177 node4177Labels := by rfl

theorem canonical20758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20758 raw20758Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw20758 raw20758Labels = mixedMoment B raw20758step0 raw20758step0Labels := by
      have hz : ∀ j, raw20758 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20758step0 = (fun i j => raw20758 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20758step0 raw20758; decide +kernel
      have hl : raw20758step0Labels = raw20758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20758 raw20758Labels permutation346 hz
    mixedMoment B raw20758step0 raw20758step0Labels = mixedMoment B raw20758step1 raw20758step1Labels := by
      have ha : raw20758step1 = (fun i j => raw20758step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20758step1 raw20758step0; decide +kernel
      have hl : raw20758step1Labels = raw20758step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20758step0 raw20758step0Labels permutation32 permutation3
    mixedMoment B raw20758step1 raw20758step1Labels = mixedMoment B raw20758step2 raw20758step2Labels := by
      have ha : raw20758step2 = raw20758step1 := by apply Matrix.ext; unfold raw20758step2 raw20758step1; decide +kernel
      have hl : raw20758step1Labels = labelEmbedding6 ∘ raw20758step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20758step1 raw20758step1Labels raw20758step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4546 node4546Labels := by rfl

theorem canonical20759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20759 raw20759Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw20759 raw20759Labels = mixedMoment B raw20759step0 raw20759step0Labels := by
      have hz : ∀ j, raw20759 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20759step0 = (fun i j => raw20759 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20759step0 raw20759; decide +kernel
      have hl : raw20759step0Labels = raw20759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20759 raw20759Labels permutation265 hz
    mixedMoment B raw20759step0 raw20759step0Labels = mixedMoment B raw20759step1 raw20759step1Labels := by
      have ha : raw20759step1 = (fun i j => raw20759step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20759step1 raw20759step0; decide +kernel
      have hl : raw20759step1Labels = raw20759step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20759step0 raw20759step0Labels permutation32 permutation3
    mixedMoment B raw20759step1 raw20759step1Labels = mixedMoment B raw20759step2 raw20759step2Labels := by
      have ha : raw20759step2 = raw20759step1 := by apply Matrix.ext; unfold raw20759step2 raw20759step1; decide +kernel
      have hl : raw20759step1Labels = labelEmbedding6 ∘ raw20759step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20759step1 raw20759step1Labels raw20759step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4546 node4546Labels := by rfl

theorem canonical20760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20760 raw20760Labels = mixedMoment B node4625 node4625Labels := by
  calc
    mixedMoment B raw20760 raw20760Labels = mixedMoment B raw20760step0 raw20760step0Labels := by
      have hz : ∀ j, raw20760 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20760step0 = (fun i j => raw20760 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20760step0 raw20760; decide +kernel
      have hl : raw20760step0Labels = raw20760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20760 raw20760Labels permutation520 hz
    mixedMoment B raw20760step0 raw20760step0Labels = mixedMoment B raw20760step1 raw20760step1Labels := by
      have hz : ∀ j, raw20760step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20760step1 = (fun i j => raw20760step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20760step1 raw20760step0; decide +kernel
      have hl : raw20760step1Labels = raw20760step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20760step0 raw20760step0Labels permutation80 hz
    mixedMoment B raw20760step1 raw20760step1Labels = mixedMoment B raw20760step2 raw20760step2Labels := by
      have hz : ∀ j, raw20760step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20760step2 = (fun i j => raw20760step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20760step2 raw20760step1; decide +kernel
      have hl : raw20760step2Labels = raw20760step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20760step1 raw20760step1Labels permutation14 hz
    mixedMoment B raw20760step2 raw20760step2Labels = mixedMoment B raw20760step3 raw20760step3Labels := by
      have ha : raw20760step3 = (fun i j => raw20760step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20760step3 raw20760step2; decide +kernel
      have hl : raw20760step3Labels = raw20760step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20760step2 raw20760step2Labels permutation2 permutation3
    mixedMoment B raw20760step3 raw20760step3Labels = mixedMoment B raw20760step4 raw20760step4Labels := by
      have ha : raw20760step4 = raw20760step3 := by apply Matrix.ext; unfold raw20760step4 raw20760step3; decide +kernel
      have hl : raw20760step3Labels = labelEmbedding6 ∘ raw20760step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20760step3 raw20760step3Labels raw20760step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4625 node4625Labels := by rfl

theorem canonical20761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20761 raw20761Labels = mixedMoment B node4148 node4148Labels := by
  calc
    mixedMoment B raw20761 raw20761Labels = mixedMoment B raw20761step0 raw20761step0Labels := by
      have hz : ∀ j, raw20761 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20761step0 = (fun i j => raw20761 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20761step0 raw20761; decide +kernel
      have hl : raw20761step0Labels = raw20761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20761 raw20761Labels permutation346 hz
    mixedMoment B raw20761step0 raw20761step0Labels = mixedMoment B raw20761step1 raw20761step1Labels := by
      have hz : ∀ j, raw20761step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20761step1 = (fun i j => raw20761step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20761step1 raw20761step0; decide +kernel
      have hl : raw20761step1Labels = raw20761step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20761step0 raw20761step0Labels permutation56 hz
    mixedMoment B raw20761step1 raw20761step1Labels = mixedMoment B raw20761step2 raw20761step2Labels := by
      have ha : raw20761step2 = (fun i j => raw20761step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20761step2 raw20761step1; decide +kernel
      have hl : raw20761step2Labels = raw20761step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20761step1 raw20761step1Labels permutation8 permutation3
    mixedMoment B raw20761step2 raw20761step2Labels = mixedMoment B raw20761step3 raw20761step3Labels := by
      have ha : raw20761step3 = raw20761step2 := by apply Matrix.ext; unfold raw20761step3 raw20761step2; decide +kernel
      have hl : raw20761step2Labels = labelEmbedding6 ∘ raw20761step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20761step2 raw20761step2Labels raw20761step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4148 node4148Labels := by rfl

theorem canonical20762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20762 raw20762Labels = mixedMoment B node4526 node4526Labels := by
  calc
    mixedMoment B raw20762 raw20762Labels = mixedMoment B raw20762step0 raw20762step0Labels := by
      have hz : ∀ j, raw20762 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20762step0 = (fun i j => raw20762 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20762step0 raw20762; decide +kernel
      have hl : raw20762step0Labels = raw20762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20762 raw20762Labels permutation346 hz
    mixedMoment B raw20762step0 raw20762step0Labels = mixedMoment B raw20762step1 raw20762step1Labels := by
      have ha : raw20762step1 = (fun i j => raw20762step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20762step1 raw20762step0; decide +kernel
      have hl : raw20762step1Labels = raw20762step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20762step0 raw20762step0Labels permutation32 permutation3
    mixedMoment B raw20762step1 raw20762step1Labels = mixedMoment B raw20762step2 raw20762step2Labels := by
      have ha : raw20762step2 = raw20762step1 := by apply Matrix.ext; unfold raw20762step2 raw20762step1; decide +kernel
      have hl : raw20762step1Labels = labelEmbedding6 ∘ raw20762step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20762step1 raw20762step1Labels raw20762step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4526 node4526Labels := by rfl

theorem canonical20763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20763 raw20763Labels = mixedMoment B node4526 node4526Labels := by
  calc
    mixedMoment B raw20763 raw20763Labels = mixedMoment B raw20763step0 raw20763step0Labels := by
      have hz : ∀ j, raw20763 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20763step0 = (fun i j => raw20763 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20763step0 raw20763; decide +kernel
      have hl : raw20763step0Labels = raw20763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20763 raw20763Labels permutation265 hz
    mixedMoment B raw20763step0 raw20763step0Labels = mixedMoment B raw20763step1 raw20763step1Labels := by
      have ha : raw20763step1 = (fun i j => raw20763step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20763step1 raw20763step0; decide +kernel
      have hl : raw20763step1Labels = raw20763step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20763step0 raw20763step0Labels permutation32 permutation3
    mixedMoment B raw20763step1 raw20763step1Labels = mixedMoment B raw20763step2 raw20763step2Labels := by
      have ha : raw20763step2 = raw20763step1 := by apply Matrix.ext; unfold raw20763step2 raw20763step1; decide +kernel
      have hl : raw20763step1Labels = labelEmbedding6 ∘ raw20763step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20763step1 raw20763step1Labels raw20763step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4526 node4526Labels := by rfl

theorem canonical20764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20764 raw20764Labels = mixedMoment B node4520 node4520Labels := by
  calc
    mixedMoment B raw20764 raw20764Labels = mixedMoment B raw20764step0 raw20764step0Labels := by
      have hz : ∀ j, raw20764 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20764step0 = (fun i j => raw20764 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20764step0 raw20764; decide +kernel
      have hl : raw20764step0Labels = raw20764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20764 raw20764Labels permutation346 hz
    mixedMoment B raw20764step0 raw20764step0Labels = mixedMoment B raw20764step1 raw20764step1Labels := by
      have hz : ∀ j, raw20764step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20764step1 = (fun i j => raw20764step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20764step1 raw20764step0; decide +kernel
      have hl : raw20764step1Labels = raw20764step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20764step0 raw20764step0Labels permutation56 hz
    mixedMoment B raw20764step1 raw20764step1Labels = mixedMoment B raw20764step2 raw20764step2Labels := by
      have ha : raw20764step2 = (fun i j => raw20764step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20764step2 raw20764step1; decide +kernel
      have hl : raw20764step2Labels = raw20764step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20764step1 raw20764step1Labels permutation8 permutation3
    mixedMoment B raw20764step2 raw20764step2Labels = mixedMoment B raw20764step3 raw20764step3Labels := by
      have ha : raw20764step3 = raw20764step2 := by apply Matrix.ext; unfold raw20764step3 raw20764step2; decide +kernel
      have hl : raw20764step2Labels = labelEmbedding6 ∘ raw20764step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20764step2 raw20764step2Labels raw20764step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4520 node4520Labels := by rfl

theorem canonical20765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20765 raw20765Labels = mixedMoment B node4146 node4146Labels := by
  calc
    mixedMoment B raw20765 raw20765Labels = mixedMoment B raw20765step0 raw20765step0Labels := by
      have hz : ∀ j, raw20765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20765step0 = (fun i j => raw20765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20765step0 raw20765; decide +kernel
      have hl : raw20765step0Labels = raw20765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20765 raw20765Labels permutation346 hz
    mixedMoment B raw20765step0 raw20765step0Labels = mixedMoment B raw20765step1 raw20765step1Labels := by
      have hz : ∀ j, raw20765step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20765step1 = (fun i j => raw20765step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20765step1 raw20765step0; decide +kernel
      have hl : raw20765step1Labels = raw20765step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20765step0 raw20765step0Labels permutation56 hz
    mixedMoment B raw20765step1 raw20765step1Labels = mixedMoment B raw20765step2 raw20765step2Labels := by
      have ha : raw20765step2 = (fun i j => raw20765step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20765step2 raw20765step1; decide +kernel
      have hl : raw20765step2Labels = raw20765step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20765step1 raw20765step1Labels permutation8 permutation3
    mixedMoment B raw20765step2 raw20765step2Labels = mixedMoment B raw20765step3 raw20765step3Labels := by
      have ha : raw20765step3 = raw20765step2 := by apply Matrix.ext; unfold raw20765step3 raw20765step2; decide +kernel
      have hl : raw20765step2Labels = labelEmbedding6 ∘ raw20765step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20765step2 raw20765step2Labels raw20765step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4146 node4146Labels := by rfl

theorem canonical20766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20766 raw20766Labels = mixedMoment B node4293 node4293Labels := by
  calc
    mixedMoment B raw20766 raw20766Labels = mixedMoment B raw20766step0 raw20766step0Labels := by
      have hz : ∀ j, raw20766 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20766step0 = (fun i j => raw20766 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20766step0 raw20766; decide +kernel
      have hl : raw20766step0Labels = raw20766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20766 raw20766Labels permutation346 hz
    mixedMoment B raw20766step0 raw20766step0Labels = mixedMoment B raw20766step1 raw20766step1Labels := by
      have ha : raw20766step1 = (fun i j => raw20766step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20766step1 raw20766step0; decide +kernel
      have hl : raw20766step1Labels = raw20766step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20766step0 raw20766step0Labels permutation151 permutation3
    mixedMoment B raw20766step1 raw20766step1Labels = mixedMoment B raw20766step2 raw20766step2Labels := by
      have ha : raw20766step2 = -raw20766step1 := by apply Matrix.ext; change ∀ i j, raw20766step2 i j = -(raw20766step1 i j); unfold raw20766step2 raw20766step1; decide +kernel
      have hl : raw20766step2Labels = raw20766step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20766step2 raw20766step2Labels = mixedMoment B raw20766step3 raw20766step3Labels := by
      have ha : raw20766step3 = raw20766step2 := by apply Matrix.ext; unfold raw20766step3 raw20766step2; decide +kernel
      have hl : raw20766step2Labels = labelEmbedding6 ∘ raw20766step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20766step2 raw20766step2Labels raw20766step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4293 node4293Labels := by rfl

theorem canonical20767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20767 raw20767Labels = mixedMoment B node4293 node4293Labels := by
  calc
    mixedMoment B raw20767 raw20767Labels = mixedMoment B raw20767step0 raw20767step0Labels := by
      have hz : ∀ j, raw20767 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20767step0 = (fun i j => raw20767 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20767step0 raw20767; decide +kernel
      have hl : raw20767step0Labels = raw20767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20767 raw20767Labels permutation265 hz
    mixedMoment B raw20767step0 raw20767step0Labels = mixedMoment B raw20767step1 raw20767step1Labels := by
      have ha : raw20767step1 = (fun i j => raw20767step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20767step1 raw20767step0; decide +kernel
      have hl : raw20767step1Labels = raw20767step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20767step0 raw20767step0Labels permutation151 permutation3
    mixedMoment B raw20767step1 raw20767step1Labels = mixedMoment B raw20767step2 raw20767step2Labels := by
      have ha : raw20767step2 = -raw20767step1 := by apply Matrix.ext; change ∀ i j, raw20767step2 i j = -(raw20767step1 i j); unfold raw20767step2 raw20767step1; decide +kernel
      have hl : raw20767step2Labels = raw20767step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20767step2 raw20767step2Labels = mixedMoment B raw20767step3 raw20767step3Labels := by
      have ha : raw20767step3 = raw20767step2 := by apply Matrix.ext; unfold raw20767step3 raw20767step2; decide +kernel
      have hl : raw20767step2Labels = labelEmbedding6 ∘ raw20767step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20767step2 raw20767step2Labels raw20767step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4293 node4293Labels := by rfl

theorem canonical20768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20768 raw20768Labels = mixedMoment B node4315 node4315Labels := by
  calc
    mixedMoment B raw20768 raw20768Labels = mixedMoment B raw20768step0 raw20768step0Labels := by
      have hz : ∀ j, raw20768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20768step0 = (fun i j => raw20768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20768step0 raw20768; decide +kernel
      have hl : raw20768step0Labels = raw20768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20768 raw20768Labels permutation346 hz
    mixedMoment B raw20768step0 raw20768step0Labels = mixedMoment B raw20768step1 raw20768step1Labels := by
      have hz : ∀ j, raw20768step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20768step1 = (fun i j => raw20768step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20768step1 raw20768step0; decide +kernel
      have hl : raw20768step1Labels = raw20768step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20768step0 raw20768step0Labels permutation56 hz
    mixedMoment B raw20768step1 raw20768step1Labels = mixedMoment B raw20768step2 raw20768step2Labels := by
      have ha : raw20768step2 = (fun i j => raw20768step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20768step2 raw20768step1; decide +kernel
      have hl : raw20768step2Labels = raw20768step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20768step1 raw20768step1Labels permutation31 permutation3
    mixedMoment B raw20768step2 raw20768step2Labels = mixedMoment B raw20768step3 raw20768step3Labels := by
      have ha : raw20768step3 = -raw20768step2 := by apply Matrix.ext; change ∀ i j, raw20768step3 i j = -(raw20768step2 i j); unfold raw20768step3 raw20768step2; decide +kernel
      have hl : raw20768step3Labels = raw20768step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20768step3 raw20768step3Labels = mixedMoment B raw20768step4 raw20768step4Labels := by
      have ha : raw20768step4 = raw20768step3 := by apply Matrix.ext; unfold raw20768step4 raw20768step3; decide +kernel
      have hl : raw20768step3Labels = labelEmbedding6 ∘ raw20768step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20768step3 raw20768step3Labels raw20768step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4315 node4315Labels := by rfl

theorem canonical20769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20769 raw20769Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw20769 raw20769Labels = mixedMoment B raw20769step0 raw20769step0Labels := by
      have hz : ∀ j, raw20769 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20769step0 = (fun i j => raw20769 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20769step0 raw20769; decide +kernel
      have hl : raw20769step0Labels = raw20769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20769 raw20769Labels permutation520 hz
    mixedMoment B raw20769step0 raw20769step0Labels = mixedMoment B raw20769step1 raw20769step1Labels := by
      have hz : ∀ j, raw20769step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20769step1 = (fun i j => raw20769step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20769step1 raw20769step0; decide +kernel
      have hl : raw20769step1Labels = raw20769step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20769step0 raw20769step0Labels permutation80 hz
    mixedMoment B raw20769step1 raw20769step1Labels = mixedMoment B raw20769step2 raw20769step2Labels := by
      have hz : ∀ j, raw20769step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20769step2 = (fun i j => raw20769step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20769step2 raw20769step1; decide +kernel
      have hl : raw20769step2Labels = raw20769step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20769step1 raw20769step1Labels permutation14 hz
    mixedMoment B raw20769step2 raw20769step2Labels = mixedMoment B raw20769step3 raw20769step3Labels := by
      have ha : raw20769step3 = (fun i j => raw20769step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20769step3 raw20769step2; decide +kernel
      have hl : raw20769step3Labels = raw20769step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20769step2 raw20769step2Labels permutation7 permutation3
    mixedMoment B raw20769step3 raw20769step3Labels = mixedMoment B raw20769step4 raw20769step4Labels := by
      have ha : raw20769step4 = -raw20769step3 := by apply Matrix.ext; change ∀ i j, raw20769step4 i j = -(raw20769step3 i j); unfold raw20769step4 raw20769step3; decide +kernel
      have hl : raw20769step4Labels = raw20769step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20769step4 raw20769step4Labels = mixedMoment B raw20769step5 raw20769step5Labels := by
      have ha : raw20769step5 = raw20769step4 := by apply Matrix.ext; unfold raw20769step5 raw20769step4; decide +kernel
      have hl : raw20769step4Labels = labelEmbedding6 ∘ raw20769step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20769step4 raw20769step4Labels raw20769step5Labels labelEmbedding6 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

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

theorem canonical2301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2301 raw2301Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw2301 raw2301Labels = mixedMoment B raw2301step0 raw2301step0Labels := by
      have ha : raw2301step0 = (fun i j => raw2301 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2301step0 raw2301; decide +kernel
      have hl : raw2301step0Labels = raw2301Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2301 raw2301Labels permutation8 permutation4
    mixedMoment B raw2301step0 raw2301step0Labels = mixedMoment B raw2301step1 raw2301step1Labels := by
      have ha : raw2301step1 = raw2301step0 := by apply Matrix.ext; unfold raw2301step1 raw2301step0; decide +kernel
      have hl : raw2301step0Labels = labelEmbedding7 ∘ raw2301step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2301step0 raw2301step0Labels raw2301step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

theorem canonical2302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2302 raw2302Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw2302 raw2302Labels = mixedMoment B raw2302step0 raw2302step0Labels := by
      have ha : raw2302step0 = (fun i j => raw2302 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2302step0 raw2302; decide +kernel
      have hl : raw2302step0Labels = raw2302Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2302 raw2302Labels permutation8 permutation4
    _ = mixedMoment B node2767 node2767Labels := by rfl

theorem canonical2303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2303 raw2303Labels = mixedMoment B node3627 node3627Labels := by
  calc
    mixedMoment B raw2303 raw2303Labels = mixedMoment B raw2303step0 raw2303step0Labels := by
      have ha : raw2303step0 = (fun i j => raw2303 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2303step0 raw2303; decide +kernel
      have hl : raw2303step0Labels = raw2303Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2303 raw2303Labels permutation10 permutation6
    mixedMoment B raw2303step0 raw2303step0Labels = mixedMoment B raw2303step1 raw2303step1Labels := by
      have ha : raw2303step1 = -raw2303step0 := by apply Matrix.ext; change ∀ i j, raw2303step1 i j = -(raw2303step0 i j); unfold raw2303step1 raw2303step0; decide +kernel
      have hl : raw2303step1Labels = raw2303step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2303step1 raw2303step1Labels = mixedMoment B raw2303step2 raw2303step2Labels := by
      have ha : raw2303step2 = raw2303step1 := by apply Matrix.ext; unfold raw2303step2 raw2303step1; decide +kernel
      have hl : raw2303step1Labels = labelEmbedding1 ∘ raw2303step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2303step1 raw2303step1Labels raw2303step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3627 node3627Labels := by rfl

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

theorem canonical2307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2307 raw2307Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw2307 raw2307Labels = mixedMoment B raw2307step0 raw2307step0Labels := by
      have ha : raw2307step0 = (fun i j => raw2307 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2307step0 raw2307; decide +kernel
      have hl : raw2307step0Labels = raw2307Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2307 raw2307Labels permutation2 permutation4
    mixedMoment B raw2307step0 raw2307step0Labels = mixedMoment B raw2307step1 raw2307step1Labels := by
      have ha : raw2307step1 = raw2307step0 := by apply Matrix.ext; unfold raw2307step1 raw2307step0; decide +kernel
      have hl : raw2307step0Labels = labelEmbedding7 ∘ raw2307step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2307step0 raw2307step0Labels raw2307step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5296 node5296Labels := by rfl

theorem canonical2308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2308 raw2308Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw2308 raw2308Labels = mixedMoment B raw2308step0 raw2308step0Labels := by
      have ha : raw2308step0 = (fun i j => raw2308 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2308step0 raw2308; decide +kernel
      have hl : raw2308step0Labels = raw2308Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2308 raw2308Labels permutation2 permutation4
    _ = mixedMoment B node2770 node2770Labels := by rfl

theorem canonical2309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2309 raw2309Labels = mixedMoment B node3634 node3634Labels := by
  calc
    mixedMoment B raw2309 raw2309Labels = mixedMoment B raw2309step0 raw2309step0Labels := by
      have ha : raw2309step0 = (fun i j => raw2309 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2309step0 raw2309; decide +kernel
      have hl : raw2309step0Labels = raw2309Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2309 raw2309Labels permutation7 permutation3
    mixedMoment B raw2309step0 raw2309step0Labels = mixedMoment B raw2309step1 raw2309step1Labels := by
      have ha : raw2309step1 = raw2309step0 := by apply Matrix.ext; unfold raw2309step1 raw2309step0; decide +kernel
      have hl : raw2309step0Labels = labelEmbedding1 ∘ raw2309step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2309step0 raw2309step0Labels raw2309step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3634 node3634Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw270 raw270Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw270 raw270Labels = mixedMoment B raw270step0 raw270step0Labels := by
      have ha : raw270step0 = (fun i j => raw270 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw270step0 raw270; decide +kernel
      have hl : raw270step0Labels = raw270Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw270 raw270Labels permutation8 permutation5
    mixedMoment B raw270step0 raw270step0Labels = mixedMoment B raw270step1 raw270step1Labels := by
      have ha : raw270step1 = raw270step0 := by apply Matrix.ext; unfold raw270step1 raw270step0; decide +kernel
      have hl : raw270step0Labels = labelEmbedding1 ∘ raw270step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw270step0 raw270step0Labels raw270step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2767 node2767Labels := by rfl

theorem canonical271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw271 raw271Labels = mixedMoment B node404 node404Labels := by
  calc
    mixedMoment B raw271 raw271Labels = mixedMoment B raw271step0 raw271step0Labels := by
      have ha : raw271step0 = (fun i j => raw271 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw271step0 raw271; decide +kernel
      have hl : raw271step0Labels = raw271Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw271 raw271Labels permutation8 permutation5
    _ = mixedMoment B node404 node404Labels := by rfl

theorem canonical274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw274 raw274Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw274 raw274Labels = mixedMoment B raw274step0 raw274step0Labels := by
      have ha : raw274step0 = (fun i j => raw274 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw274step0 raw274; decide +kernel
      have hl : raw274step0Labels = raw274Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw274 raw274Labels permutation2 permutation5
    mixedMoment B raw274step0 raw274step0Labels = mixedMoment B raw274step1 raw274step1Labels := by
      have ha : raw274step1 = raw274step0 := by apply Matrix.ext; unfold raw274step1 raw274step0; decide +kernel
      have hl : raw274step0Labels = labelEmbedding1 ∘ raw274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw274step0 raw274step0Labels raw274step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2770 node2770Labels := by rfl

theorem canonical275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw275 raw275Labels = mixedMoment B node407 node407Labels := by
  calc
    mixedMoment B raw275 raw275Labels = mixedMoment B raw275step0 raw275step0Labels := by
      have ha : raw275step0 = (fun i j => raw275 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw275step0 raw275; decide +kernel
      have hl : raw275step0Labels = raw275Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw275 raw275Labels permutation7 permutation4
    mixedMoment B raw275step0 raw275step0Labels = mixedMoment B raw275step1 raw275step1Labels := by
      have ha : raw275step1 = -raw275step0 := by apply Matrix.ext; change ∀ i j, raw275step1 i j = -(raw275step0 i j); unfold raw275step1 raw275step0; decide +kernel
      have hl : raw275step1Labels = raw275step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node407 node407Labels := by rfl

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

theorem canonical771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw771 raw771Labels = mixedMoment B node4144 node4144Labels := by
  calc
    mixedMoment B raw771 raw771Labels = mixedMoment B raw771step0 raw771step0Labels := by
      have ha : raw771step0 = (fun i j => raw771 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw771step0 raw771; decide +kernel
      have hl : raw771step0Labels = raw771Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw771 raw771Labels permutation32 permutation4
    mixedMoment B raw771step0 raw771step0Labels = mixedMoment B raw771step1 raw771step1Labels := by
      have ha : raw771step1 = raw771step0 := by apply Matrix.ext; unfold raw771step1 raw771step0; decide +kernel
      have hl : raw771step0Labels = labelEmbedding7 ∘ raw771step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw771step0 raw771step0Labels raw771step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4144 node4144Labels := by rfl

theorem canonical772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw772 raw772Labels = mixedMoment B node572 node572Labels := by
  calc
    mixedMoment B raw772 raw772Labels = mixedMoment B raw772step0 raw772step0Labels := by
      have ha : raw772step0 = (fun i j => raw772 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw772step0 raw772; decide +kernel
      have hl : raw772step0Labels = raw772Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw772 raw772Labels permutation32 permutation4
    _ = mixedMoment B node572 node572Labels := by rfl

theorem canonical773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw773 raw773Labels = mixedMoment B node1492 node1492Labels := by
  calc
    mixedMoment B raw773 raw773Labels = mixedMoment B raw773step0 raw773step0Labels := by
      have ha : raw773step0 = (fun i j => raw773 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw773step0 raw773; decide +kernel
      have hl : raw773step0Labels = raw773Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw773 raw773Labels permutation32 permutation6
    mixedMoment B raw773step0 raw773step0Labels = mixedMoment B raw773step1 raw773step1Labels := by
      have ha : raw773step1 = -raw773step0 := by apply Matrix.ext; change ∀ i j, raw773step1 i j = -(raw773step0 i j); unfold raw773step1 raw773step0; decide +kernel
      have hl : raw773step1Labels = raw773step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw773step1 raw773step1Labels = mixedMoment B raw773step2 raw773step2Labels := by
      have ha : raw773step2 = raw773step1 := by apply Matrix.ext; unfold raw773step2 raw773step1; decide +kernel
      have hl : raw773step1Labels = labelEmbedding1 ∘ raw773step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw773step1 raw773step1Labels raw773step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1492 node1492Labels := by rfl

theorem canonical777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw777 raw777Labels = mixedMoment B node4146 node4146Labels := by
  calc
    mixedMoment B raw777 raw777Labels = mixedMoment B raw777step0 raw777step0Labels := by
      have ha : raw777step0 = (fun i j => raw777 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw777step0 raw777; decide +kernel
      have hl : raw777step0Labels = raw777Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw777 raw777Labels permutation8 permutation4
    mixedMoment B raw777step0 raw777step0Labels = mixedMoment B raw777step1 raw777step1Labels := by
      have ha : raw777step1 = raw777step0 := by apply Matrix.ext; unfold raw777step1 raw777step0; decide +kernel
      have hl : raw777step0Labels = labelEmbedding7 ∘ raw777step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw777step0 raw777step0Labels raw777step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4146 node4146Labels := by rfl

theorem canonical778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw778 raw778Labels = mixedMoment B node574 node574Labels := by
  calc
    mixedMoment B raw778 raw778Labels = mixedMoment B raw778step0 raw778step0Labels := by
      have ha : raw778step0 = (fun i j => raw778 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw778step0 raw778; decide +kernel
      have hl : raw778step0Labels = raw778Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw778 raw778Labels permutation8 permutation4
    _ = mixedMoment B node574 node574Labels := by rfl

theorem canonical779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw779 raw779Labels = mixedMoment B node1494 node1494Labels := by
  calc
    mixedMoment B raw779 raw779Labels = mixedMoment B raw779step0 raw779step0Labels := by
      have ha : raw779step0 = (fun i j => raw779 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw779step0 raw779; decide +kernel
      have hl : raw779step0Labels = raw779Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw779 raw779Labels permutation8 permutation6
    mixedMoment B raw779step0 raw779step0Labels = mixedMoment B raw779step1 raw779step1Labels := by
      have ha : raw779step1 = -raw779step0 := by apply Matrix.ext; change ∀ i j, raw779step1 i j = -(raw779step0 i j); unfold raw779step1 raw779step0; decide +kernel
      have hl : raw779step1Labels = raw779step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw779step1 raw779step1Labels = mixedMoment B raw779step2 raw779step2Labels := by
      have ha : raw779step2 = raw779step1 := by apply Matrix.ext; unfold raw779step2 raw779step1; decide +kernel
      have hl : raw779step1Labels = labelEmbedding1 ∘ raw779step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw779step1 raw779step1Labels raw779step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1494 node1494Labels := by rfl

theorem canonical783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw783 raw783Labels = mixedMoment B node4148 node4148Labels := by
  calc
    mixedMoment B raw783 raw783Labels = mixedMoment B raw783step0 raw783step0Labels := by
      have ha : raw783step0 = (fun i j => raw783 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw783step0 raw783; decide +kernel
      have hl : raw783step0Labels = raw783Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw783 raw783Labels permutation8 permutation4
    mixedMoment B raw783step0 raw783step0Labels = mixedMoment B raw783step1 raw783step1Labels := by
      have ha : raw783step1 = raw783step0 := by apply Matrix.ext; unfold raw783step1 raw783step0; decide +kernel
      have hl : raw783step0Labels = labelEmbedding7 ∘ raw783step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw783step0 raw783step0Labels raw783step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4148 node4148Labels := by rfl

theorem canonical784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw784 raw784Labels = mixedMoment B node576 node576Labels := by
  calc
    mixedMoment B raw784 raw784Labels = mixedMoment B raw784step0 raw784step0Labels := by
      have ha : raw784step0 = (fun i j => raw784 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw784step0 raw784; decide +kernel
      have hl : raw784step0Labels = raw784Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw784 raw784Labels permutation8 permutation4
    _ = mixedMoment B node576 node576Labels := by rfl

theorem canonical785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw785 raw785Labels = mixedMoment B node1496 node1496Labels := by
  calc
    mixedMoment B raw785 raw785Labels = mixedMoment B raw785step0 raw785step0Labels := by
      have ha : raw785step0 = (fun i j => raw785 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw785step0 raw785; decide +kernel
      have hl : raw785step0Labels = raw785Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw785 raw785Labels permutation8 permutation6
    mixedMoment B raw785step0 raw785step0Labels = mixedMoment B raw785step1 raw785step1Labels := by
      have ha : raw785step1 = -raw785step0 := by apply Matrix.ext; change ∀ i j, raw785step1 i j = -(raw785step0 i j); unfold raw785step1 raw785step0; decide +kernel
      have hl : raw785step1Labels = raw785step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw785step1 raw785step1Labels = mixedMoment B raw785step2 raw785step2Labels := by
      have ha : raw785step2 = raw785step1 := by apply Matrix.ext; unfold raw785step2 raw785step1; decide +kernel
      have hl : raw785step1Labels = labelEmbedding1 ∘ raw785step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw785step1 raw785step1Labels raw785step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1496 node1496Labels := by rfl

theorem canonical813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw813 raw813Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw813 raw813Labels = mixedMoment B raw813step0 raw813step0Labels := by
      have ha : raw813step0 = (fun i j => raw813 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw813step0 raw813; decide +kernel
      have hl : raw813step0Labels = raw813Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw813 raw813Labels permutation8 permutation4
    mixedMoment B raw813step0 raw813step0Labels = mixedMoment B raw813step1 raw813step1Labels := by
      have ha : raw813step1 = raw813step0 := by apply Matrix.ext; unfold raw813step1 raw813step0; decide +kernel
      have hl : raw813step0Labels = labelEmbedding7 ∘ raw813step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw813step0 raw813step0Labels raw813step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4177 node4177Labels := by rfl

theorem canonical814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw814 raw814Labels = mixedMoment B node605 node605Labels := by
  calc
    mixedMoment B raw814 raw814Labels = mixedMoment B raw814step0 raw814step0Labels := by
      have ha : raw814step0 = (fun i j => raw814 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw814step0 raw814; decide +kernel
      have hl : raw814step0Labels = raw814Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw814 raw814Labels permutation8 permutation4
    _ = mixedMoment B node605 node605Labels := by rfl

theorem canonical815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw815 raw815Labels = mixedMoment B node1518 node1518Labels := by
  calc
    mixedMoment B raw815 raw815Labels = mixedMoment B raw815step0 raw815step0Labels := by
      have ha : raw815step0 = (fun i j => raw815 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw815step0 raw815; decide +kernel
      have hl : raw815step0Labels = raw815Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw815 raw815Labels permutation8 permutation6
    mixedMoment B raw815step0 raw815step0Labels = mixedMoment B raw815step1 raw815step1Labels := by
      have ha : raw815step1 = -raw815step0 := by apply Matrix.ext; change ∀ i j, raw815step1 i j = -(raw815step0 i j); unfold raw815step1 raw815step0; decide +kernel
      have hl : raw815step1Labels = raw815step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw815step1 raw815step1Labels = mixedMoment B raw815step2 raw815step2Labels := by
      have ha : raw815step2 = raw815step1 := by apply Matrix.ext; unfold raw815step2 raw815step1; decide +kernel
      have hl : raw815step1Labels = labelEmbedding1 ∘ raw815step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw815step1 raw815step1Labels raw815step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1518 node1518Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7811 raw7811Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw7811 raw7811Labels = mixedMoment B raw7811step0 raw7811step0Labels := by
      have hz : ∀ j, raw7811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7811step0 = (fun i j => raw7811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7811step0 raw7811; decide +kernel
      have hl : raw7811step0Labels = raw7811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7811 raw7811Labels permutation346 hz
    mixedMoment B raw7811step0 raw7811step0Labels = mixedMoment B raw7811step1 raw7811step1Labels := by
      have ha : raw7811step1 = (fun i j => raw7811step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7811step1 raw7811step0; decide +kernel
      have hl : raw7811step1Labels = raw7811step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7811step0 raw7811step0Labels permutation38 permutation3
    mixedMoment B raw7811step1 raw7811step1Labels = mixedMoment B raw7811step2 raw7811step2Labels := by
      have ha : raw7811step2 = raw7811step1 := by apply Matrix.ext; unfold raw7811step2 raw7811step1; decide +kernel
      have hl : raw7811step1Labels = labelEmbedding6 ∘ raw7811step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7811step1 raw7811step1Labels raw7811step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

theorem canonical7816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7816 raw7816Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw7816 raw7816Labels = mixedMoment B raw7816step0 raw7816step0Labels := by
      have hz : ∀ j, raw7816 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7816step0 = (fun i j => raw7816 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7816step0 raw7816; decide +kernel
      have hl : raw7816step0Labels = raw7816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7816 raw7816Labels permutation265 hz
    mixedMoment B raw7816step0 raw7816step0Labels = mixedMoment B raw7816step1 raw7816step1Labels := by
      have ha : raw7816step1 = (fun i j => raw7816step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7816step1 raw7816step0; decide +kernel
      have hl : raw7816step1Labels = raw7816step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7816step0 raw7816step0Labels permutation38 permutation3
    mixedMoment B raw7816step1 raw7816step1Labels = mixedMoment B raw7816step2 raw7816step2Labels := by
      have ha : raw7816step2 = raw7816step1 := by apply Matrix.ext; unfold raw7816step2 raw7816step1; decide +kernel
      have hl : raw7816step1Labels = labelEmbedding6 ∘ raw7816step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7816step1 raw7816step1Labels raw7816step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

theorem canonical7821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7821 raw7821Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw7821 raw7821Labels = mixedMoment B raw7821step0 raw7821step0Labels := by
      have hz : ∀ j, raw7821 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7821step0 = (fun i j => raw7821 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7821step0 raw7821; decide +kernel
      have hl : raw7821step0Labels = raw7821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7821 raw7821Labels permutation346 hz
    mixedMoment B raw7821step0 raw7821step0Labels = mixedMoment B raw7821step1 raw7821step1Labels := by
      have hz : ∀ j, raw7821step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7821step1 = (fun i j => raw7821step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7821step1 raw7821step0; decide +kernel
      have hl : raw7821step1Labels = raw7821step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7821step0 raw7821step0Labels permutation56 hz
    mixedMoment B raw7821step1 raw7821step1Labels = mixedMoment B raw7821step2 raw7821step2Labels := by
      have ha : raw7821step2 = (fun i j => raw7821step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7821step2 raw7821step1; decide +kernel
      have hl : raw7821step2Labels = raw7821step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7821step1 raw7821step1Labels permutation10 permutation2
    _ = mixedMoment B node4624 node4624Labels := by rfl

theorem canonical7826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7826 raw7826Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw7826 raw7826Labels = mixedMoment B raw7826step0 raw7826step0Labels := by
      have hz : ∀ j, raw7826 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7826step0 = (fun i j => raw7826 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7826step0 raw7826; decide +kernel
      have hl : raw7826step0Labels = raw7826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7826 raw7826Labels permutation346 hz
    mixedMoment B raw7826step0 raw7826step0Labels = mixedMoment B raw7826step1 raw7826step1Labels := by
      have hz : ∀ j, raw7826step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7826step1 = (fun i j => raw7826step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7826step1 raw7826step0; decide +kernel
      have hl : raw7826step1Labels = raw7826step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7826step0 raw7826step0Labels permutation56 hz
    mixedMoment B raw7826step1 raw7826step1Labels = mixedMoment B raw7826step2 raw7826step2Labels := by
      have ha : raw7826step2 = (fun i j => raw7826step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7826step2 raw7826step1; decide +kernel
      have hl : raw7826step2Labels = raw7826step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7826step1 raw7826step1Labels permutation9 permutation3
    mixedMoment B raw7826step2 raw7826step2Labels = mixedMoment B raw7826step3 raw7826step3Labels := by
      have ha : raw7826step3 = raw7826step2 := by apply Matrix.ext; unfold raw7826step3 raw7826step2; decide +kernel
      have hl : raw7826step2Labels = labelEmbedding6 ∘ raw7826step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7826step2 raw7826step2Labels raw7826step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical7832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7832 raw7832Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw7832 raw7832Labels = mixedMoment B raw7832step0 raw7832step0Labels := by
      have hz : ∀ j, raw7832 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7832step0 = (fun i j => raw7832 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7832step0 raw7832; decide +kernel
      have hl : raw7832step0Labels = raw7832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7832 raw7832Labels permutation346 hz
    mixedMoment B raw7832step0 raw7832step0Labels = mixedMoment B raw7832step1 raw7832step1Labels := by
      have ha : raw7832step1 = (fun i j => raw7832step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7832step1 raw7832step0; decide +kernel
      have hl : raw7832step1Labels = raw7832step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7832step0 raw7832step0Labels permutation151 permutation3
    mixedMoment B raw7832step1 raw7832step1Labels = mixedMoment B raw7832step2 raw7832step2Labels := by
      have ha : raw7832step2 = -raw7832step1 := by apply Matrix.ext; change ∀ i j, raw7832step2 i j = -(raw7832step1 i j); unfold raw7832step2 raw7832step1; decide +kernel
      have hl : raw7832step2Labels = raw7832step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7832step2 raw7832step2Labels = mixedMoment B raw7832step3 raw7832step3Labels := by
      have ha : raw7832step3 = raw7832step2 := by apply Matrix.ext; unfold raw7832step3 raw7832step2; decide +kernel
      have hl : raw7832step2Labels = labelEmbedding6 ∘ raw7832step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7832step2 raw7832step2Labels raw7832step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

theorem canonical7833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7833 raw7833Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw7833 raw7833Labels = mixedMoment B raw7833step0 raw7833step0Labels := by
      have hz : ∀ j, raw7833 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7833step0 = (fun i j => raw7833 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7833step0 raw7833; decide +kernel
      have hl : raw7833step0Labels = raw7833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7833 raw7833Labels permutation265 hz
    mixedMoment B raw7833step0 raw7833step0Labels = mixedMoment B raw7833step1 raw7833step1Labels := by
      have ha : raw7833step1 = (fun i j => raw7833step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7833step1 raw7833step0; decide +kernel
      have hl : raw7833step1Labels = raw7833step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7833step0 raw7833step0Labels permutation151 permutation3
    mixedMoment B raw7833step1 raw7833step1Labels = mixedMoment B raw7833step2 raw7833step2Labels := by
      have ha : raw7833step2 = -raw7833step1 := by apply Matrix.ext; change ∀ i j, raw7833step2 i j = -(raw7833step1 i j); unfold raw7833step2 raw7833step1; decide +kernel
      have hl : raw7833step2Labels = raw7833step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7833step2 raw7833step2Labels = mixedMoment B raw7833step3 raw7833step3Labels := by
      have ha : raw7833step3 = raw7833step2 := by apply Matrix.ext; unfold raw7833step3 raw7833step2; decide +kernel
      have hl : raw7833step2Labels = labelEmbedding6 ∘ raw7833step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7833step2 raw7833step2Labels raw7833step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

theorem canonical7834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7834 raw7834Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw7834 raw7834Labels = mixedMoment B raw7834step0 raw7834step0Labels := by
      have hz : ∀ j, raw7834 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7834step0 = (fun i j => raw7834 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7834step0 raw7834; decide +kernel
      have hl : raw7834step0Labels = raw7834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7834 raw7834Labels permutation346 hz
    mixedMoment B raw7834step0 raw7834step0Labels = mixedMoment B raw7834step1 raw7834step1Labels := by
      have hz : ∀ j, raw7834step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7834step1 = (fun i j => raw7834step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7834step1 raw7834step0; decide +kernel
      have hl : raw7834step1Labels = raw7834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7834step0 raw7834step0Labels permutation56 hz
    mixedMoment B raw7834step1 raw7834step1Labels = mixedMoment B raw7834step2 raw7834step2Labels := by
      have ha : raw7834step2 = (fun i j => raw7834step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7834step2 raw7834step1; decide +kernel
      have hl : raw7834step2Labels = raw7834step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7834step1 raw7834step1Labels permutation31 permutation3
    mixedMoment B raw7834step2 raw7834step2Labels = mixedMoment B raw7834step3 raw7834step3Labels := by
      have ha : raw7834step3 = -raw7834step2 := by apply Matrix.ext; change ∀ i j, raw7834step3 i j = -(raw7834step2 i j); unfold raw7834step3 raw7834step2; decide +kernel
      have hl : raw7834step3Labels = raw7834step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7834step3 raw7834step3Labels = mixedMoment B raw7834step4 raw7834step4Labels := by
      have ha : raw7834step4 = raw7834step3 := by apply Matrix.ext; unfold raw7834step4 raw7834step3; decide +kernel
      have hl : raw7834step3Labels = labelEmbedding6 ∘ raw7834step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7834step3 raw7834step3Labels raw7834step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

theorem canonical7835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7835 raw7835Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw7835 raw7835Labels = mixedMoment B raw7835step0 raw7835step0Labels := by
      have hz : ∀ j, raw7835 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7835step0 = (fun i j => raw7835 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7835step0 raw7835; decide +kernel
      have hl : raw7835step0Labels = raw7835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7835 raw7835Labels permutation520 hz
    mixedMoment B raw7835step0 raw7835step0Labels = mixedMoment B raw7835step1 raw7835step1Labels := by
      have hz : ∀ j, raw7835step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7835step1 = (fun i j => raw7835step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7835step1 raw7835step0; decide +kernel
      have hl : raw7835step1Labels = raw7835step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7835step0 raw7835step0Labels permutation80 hz
    mixedMoment B raw7835step1 raw7835step1Labels = mixedMoment B raw7835step2 raw7835step2Labels := by
      have hz : ∀ j, raw7835step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7835step2 = (fun i j => raw7835step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7835step2 raw7835step1; decide +kernel
      have hl : raw7835step2Labels = raw7835step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7835step1 raw7835step1Labels permutation14 hz
    _ = mixedMoment B node5296 node5296Labels := by rfl

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

theorem canonical1041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1041 raw1041Labels = mixedMoment B node4293 node4293Labels := by
  calc
    mixedMoment B raw1041 raw1041Labels = mixedMoment B raw1041step0 raw1041step0Labels := by
      have ha : raw1041step0 = (fun i j => raw1041 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1041step0 raw1041; decide +kernel
      have hl : raw1041step0Labels = raw1041Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1041 raw1041Labels permutation32 permutation4
    mixedMoment B raw1041step0 raw1041step0Labels = mixedMoment B raw1041step1 raw1041step1Labels := by
      have ha : raw1041step1 = raw1041step0 := by apply Matrix.ext; unfold raw1041step1 raw1041step0; decide +kernel
      have hl : raw1041step0Labels = labelEmbedding7 ∘ raw1041step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1041step0 raw1041step0Labels raw1041step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4293 node4293Labels := by rfl

theorem canonical1042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1042 raw1042Labels = mixedMoment B node871 node871Labels := by
  calc
    mixedMoment B raw1042 raw1042Labels = mixedMoment B raw1042step0 raw1042step0Labels := by
      have ha : raw1042step0 = (fun i j => raw1042 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1042step0 raw1042; decide +kernel
      have hl : raw1042step0Labels = raw1042Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1042 raw1042Labels permutation32 permutation4
    _ = mixedMoment B node871 node871Labels := by rfl

theorem canonical1043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1043 raw1043Labels = mixedMoment B node1568 node1568Labels := by
  calc
    mixedMoment B raw1043 raw1043Labels = mixedMoment B raw1043step0 raw1043step0Labels := by
      have ha : raw1043step0 = (fun i j => raw1043 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1043step0 raw1043; decide +kernel
      have hl : raw1043step0Labels = raw1043Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1043 raw1043Labels permutation32 permutation6
    mixedMoment B raw1043step0 raw1043step0Labels = mixedMoment B raw1043step1 raw1043step1Labels := by
      have ha : raw1043step1 = -raw1043step0 := by apply Matrix.ext; change ∀ i j, raw1043step1 i j = -(raw1043step0 i j); unfold raw1043step1 raw1043step0; decide +kernel
      have hl : raw1043step1Labels = raw1043step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1043step1 raw1043step1Labels = mixedMoment B raw1043step2 raw1043step2Labels := by
      have ha : raw1043step2 = raw1043step1 := by apply Matrix.ext; unfold raw1043step2 raw1043step1; decide +kernel
      have hl : raw1043step1Labels = labelEmbedding1 ∘ raw1043step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1043step1 raw1043step1Labels raw1043step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1568 node1568Labels := by rfl

theorem canonical1086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1086 raw1086Labels = mixedMoment B node4315 node4315Labels := by
  calc
    mixedMoment B raw1086 raw1086Labels = mixedMoment B raw1086step0 raw1086step0Labels := by
      have ha : raw1086step0 = (fun i j => raw1086 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1086step0 raw1086; decide +kernel
      have hl : raw1086step0Labels = raw1086Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1086 raw1086Labels permutation8 permutation4
    mixedMoment B raw1086step0 raw1086step0Labels = mixedMoment B raw1086step1 raw1086step1Labels := by
      have ha : raw1086step1 = raw1086step0 := by apply Matrix.ext; unfold raw1086step1 raw1086step0; decide +kernel
      have hl : raw1086step0Labels = labelEmbedding7 ∘ raw1086step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1086step0 raw1086step0Labels raw1086step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4315 node4315Labels := by rfl

theorem canonical1087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1087 raw1087Labels = mixedMoment B node893 node893Labels := by
  calc
    mixedMoment B raw1087 raw1087Labels = mixedMoment B raw1087step0 raw1087step0Labels := by
      have ha : raw1087step0 = (fun i j => raw1087 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1087step0 raw1087; decide +kernel
      have hl : raw1087step0Labels = raw1087Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1087 raw1087Labels permutation8 permutation4
    _ = mixedMoment B node893 node893Labels := by rfl

theorem canonical1088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1088 raw1088Labels = mixedMoment B node1578 node1578Labels := by
  calc
    mixedMoment B raw1088 raw1088Labels = mixedMoment B raw1088step0 raw1088step0Labels := by
      have ha : raw1088step0 = (fun i j => raw1088 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1088step0 raw1088; decide +kernel
      have hl : raw1088step0Labels = raw1088Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1088 raw1088Labels permutation8 permutation6
    mixedMoment B raw1088step0 raw1088step0Labels = mixedMoment B raw1088step1 raw1088step1Labels := by
      have ha : raw1088step1 = -raw1088step0 := by apply Matrix.ext; change ∀ i j, raw1088step1 i j = -(raw1088step0 i j); unfold raw1088step1 raw1088step0; decide +kernel
      have hl : raw1088step1Labels = raw1088step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1088step1 raw1088step1Labels = mixedMoment B raw1088step2 raw1088step2Labels := by
      have ha : raw1088step2 = raw1088step1 := by apply Matrix.ext; unfold raw1088step2 raw1088step1; decide +kernel
      have hl : raw1088step1Labels = labelEmbedding1 ∘ raw1088step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1088step1 raw1088step1Labels raw1088step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1578 node1578Labels := by rfl

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

theorem sum_fin_five {R : Type*} [AddCommMonoid R] (f : Fin 5 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + f 4))) = _
  ac_rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_GroupedColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit grouping formulas for the two- and three-column equality
patterns. These discharge the dependent finite-label calculations once,
so concrete certificate rows need only ordinary integer arithmetic. -/

open scoped BigOperators
namespace MUB6

theorem groupedColumns_family3_0 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 0) =
      (fun i (_ : Fin 1) => A i 0 + A i 1 + A i 2) := by
  change groupedColumns A (fun _ : Fin 3 => (0 : Fin 1)) = _
  ext i b
  have hb : b = 0 := Subsingleton.elim _ _
  subst b
  simp [groupedColumns, Fin.sum_univ_succ, add_assoc]

theorem groupedColumns_family3_1 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 1) =
      (fun i => ![A i 0 + A i 1, A i 2]) := by
  change groupedColumns A (![0, 0, 1] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_2 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 2) =
      (fun i => ![A i 0 + A i 2, A i 1]) := by
  change groupedColumns A (![0, 1, 0] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_3 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 3) =
      (fun i => ![A i 0, A i 1 + A i 2]) := by
  change groupedColumns A (![0, 1, 1] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_4 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 4) = A := by
  change groupedColumns A (fun j : Fin 3 => j) = _
  ext i b
  simp [groupedColumns, Finset.sum_filter]

end MUB6

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_PairAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedSemantics

theorem eval_familyPairVector (B : Fin 7 → Basis) (v : Sparse (Fin 909)) :
    Sparse.eval v (familyPairVector B) =
      familyAverage B (fun H => Sparse.eval v (PairSemantics.momentVector H)) := by
  unfold familyPairVector familyAverage
  rw [Sparse.eval_average]
  apply average_congr
  intro r
  exact Sparse.eval_average v _

theorem familyPairMoment_of_pointwise {p n : ℕ} (B : Fin 7 → Basis)
    (hB : IsMUBFamily B) (A : Matrix (Fin p) (Fin n) ℤ) (v : Sparse (Fin 909))
    (h : ∀ H, IsHadamard H →
      injectiveMoment H A = Sparse.eval v (PairSemantics.momentVector H)) :
    familyPairMoment B A = Sparse.eval v (familyPairVector B) := by
  rw [eval_familyPairVector]
  unfold familyPairMoment familyAverage
  apply average_congr
  intro r
  apply average_congr
  intro s
  exact h _ (relativeMatrix_isHadamard B hB r s)

end MUB6.Certificate.MixedSemantics

end

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleRules
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

/-- The five equality patterns for three sampled column indices. -/
theorem single_label_three {p : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin 3) ℤ) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      (1 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 0)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 1)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 2)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 3)) +
      (5 / 9 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 4)) := by
  have h := mixedMoment_single_label_partition B hB A
    EqualityPatterns.family3 EqualityPatterns.covers3
  rw [sum_fin_five] at h
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3,
    EqualityPatterns.blocks3, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Nat.descFactorial] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5197 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5197 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5197 = injectiveMoment H raw5197step0 := by
      have hz : ∀ j, raw5197 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5197step0 = (fun i j => raw5197 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5197 permutation21 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical5199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5199 = injectiveMoment H node11 := by
  rfl

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical239
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7678 = injectiveMoment H node65 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical781 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw781 = injectiveMoment H node181 := by
  calc
    injectiveMoment H raw781 = injectiveMoment H raw781step0 := by
      have heq : raw781step0 = -raw781 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw781).symm
    injectiveMoment H raw781step0 = injectiveMoment H raw781step1 := by
      have heq : raw781step1 = (fun i j => raw781step0 (permutation11 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw781step0 permutation11 permutation8
    _ = injectiveMoment H node181 := by rfl

theorem canonical784 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw784 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw784 = injectiveMoment H raw784step0 := by
      have heq : raw784step0 = raw784.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw784).symm
    injectiveMoment H raw784step0 = injectiveMoment H raw784step1 := by
      have heq : raw784step1 = (fun i j => raw784step0 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw784step0 permutation7 permutation6
    _ = injectiveMoment H node63 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7683 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7683 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7683 = injectiveMoment H raw7683step0 := by
      have heq : raw7683step0 = (fun i j => raw7683 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7683 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

theorem canonical7709 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7709 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7709 = injectiveMoment H raw7709step0 := by
      have hz : ∀ j, raw7709 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw7709step0 = (fun i j => raw7709 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7709 permutation5 hz
    _ = injectiveMoment H node5 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7977 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7977 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw7977 = injectiveMoment H raw7977step0 := by
      have heq : raw7977step0 = raw7977.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7977).symm
    injectiveMoment H raw7977step0 = injectiveMoment H raw7977step1 := by
      have heq : raw7977step1 = (fun i j => raw7977step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7977step0 permutation5 permutation2
    _ = injectiveMoment H node10 := by rfl

theorem canonical7979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7979 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7979 = injectiveMoment H raw7979step0 := by
      have hz : ∀ j, raw7979 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7979step0 = (fun i j => raw7979 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979 permutation7 hz
    injectiveMoment H raw7979step0 = injectiveMoment H raw7979step1 := by
      have hz : ∀ j, raw7979step0 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7979step1 = (fun i j => raw7979step0 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step0 permutation2 hz
    injectiveMoment H raw7979step1 = injectiveMoment H raw7979step2 := by
      have hz : ∀ j, raw7979step1 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7979step2 = (fun i j => raw7979step1 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step1 permutation0 hz
    injectiveMoment H raw7979step2 = injectiveMoment H raw7979step3 := by
      have hz : ∀ i, raw7979step2 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7979step3 = (fun i j => raw7979step2 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7979step2 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

theorem canonical7980 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7980 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7980 = injectiveMoment H raw7980step0 := by
      have hz : ∀ j, raw7980 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7980step0 = (fun i j => raw7980 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980 permutation27 hz
    injectiveMoment H raw7980step0 = injectiveMoment H raw7980step1 := by
      have hz : ∀ j, raw7980step0 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7980step1 = (fun i j => raw7980step0 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step0 permutation7 hz
    injectiveMoment H raw7980step1 = injectiveMoment H raw7980step2 := by
      have hz : ∀ j, raw7980step1 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7980step2 = (fun i j => raw7980step1 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step1 permutation2 hz
    injectiveMoment H raw7980step2 = injectiveMoment H raw7980step3 := by
      have hz : ∀ j, raw7980step2 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7980step3 = (fun i j => raw7980step2 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step2 permutation0 hz
    injectiveMoment H raw7980step3 = injectiveMoment H raw7980step4 := by
      have hz : ∀ i, raw7980step3 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7980step4 = (fun i j => raw7980step3 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7980step3 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical895 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw895 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw895 = injectiveMoment H raw895step0 := by
      have hz : ∀ j, raw895 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw895step0 = (fun i j => raw895 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw895 permutation15 hz
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical900 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw900 = injectiveMoment H node3 := by
  calc
    injectiveMoment H raw900 = injectiveMoment H raw900step0 := by
      have hz : ∀ j, raw900 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw900step0 = (fun i j => raw900 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw900 permutation5 hz
    _ = injectiveMoment H node3 := by rfl

theorem canonical917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw917 = injectiveMoment H node10 := by
  rfl

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentContraction
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonality relations for injective moments. The saturated relation uses
only six-row moments, even though its generating exponent array has seven rows. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem rowMonomial_difference {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (t : Coord) (κ : Fin q ↪ Coord) :
    rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ =
      H t (κ v) * conj (H t (κ w)) := by
  classical
  simp only [rowMonomial, Pi.sub_apply, zpow_sub₀ (unit_ne_zero (hH.1 _ _)),
    Finset.prod_div_distrib]
  have hv : (∏ j, H t (κ j) ^ ((Pi.single v 1 : Fin q → ℤ) j)) = H t (κ v) := by
    simp [Pi.single_apply]
  have hw : (∏ j, H t (κ j) ^ ((Pi.single w 1 : Fin q → ℤ) j)) = H t (κ w) := by
    simp [Pi.single_apply]
  rw [hv, hw, div_eq_mul_inv, unit_inv_eq_conj (hH.1 _ _)]

theorem rowMonomial_sum_zero {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (hvw : v ≠ w) (κ : Fin q ↪ Coord) :
    (∑ t, rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ) = 0 := by
  simp_rw [rowMonomial_difference hH]
  have hkwv : κ w ≠ κ v := fun h => hvw (κ.injective h.symm)
  simpa only [hkwv, ite_false, if_false, mul_comm] using hH.column_orthogonal (κ w) (κ v)

theorem contractionMonomial_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionMonomial H A ρ κ t) = 0 := by
  simp only [contractionMonomial, hA, ← Finset.mul_sum, rowMonomial_sum_zero hH v w hvw,
    mul_zero]

theorem contractionMonomial_new {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ)
    (ρ : Fin (p + 1) ↪ Coord) (κ : Fin q ↪ Coord) :
    contractionMonomial H A (Sampling.dropFirst ρ) κ (ρ 0) =
      exponentMonomial H A ρ κ := by
  simp only [contractionMonomial, exponentMonomial, rowMonomial, Fin.prod_univ_succ,
    Sampling.dropFirst_apply]
  exact mul_comm _ _

theorem contractionMonomial_occupied {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) (j : Fin p) :
    contractionMonomial H A ρ κ (ρ j) = exponentMonomial H (mergeFirst A j) ρ κ := by
  classical
  simp only [contractionMonomial, exponentMonomial, mergeFirst,
    zpow_add₀ (unit_ne_zero (hH.1 _ _)), Finset.prod_mul_distrib]
  congr 1
  simp [rowMonomial]

theorem contractionIntegrand_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionIntegrand H A ρ κ t) = 0 := by
  simp only [contractionIntegrand, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
    ← Complex.re_sum, contractionMonomial_sum_zero hH A v w hvw hA,
    contractionMonomial_sum_zero hH.transpose A v w hvw hA, Complex.zero_re,
    zero_add, zero_mul]

/-- The coefficient is 6-p, where p is the number of rows other than the
contracted row. Equivalently it is 7 minus the original row count. -/
theorem injectiveMoment_first_row_contraction {p q : ℕ} (hp : p < 6)
    {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1) :
    ((6 - p : ℕ) : ℝ) * injectiveMoment H A +
      (∑ j, injectiveMoment H (mergeFirst A j)) = 0 := by
  have ht (κ : Fin q ↪ Coord) := Sampling.average_contraction hp
    (fun ρ t => contractionIntegrand H A ρ κ t)
    (fun ρ => contractionIntegrand_sum_zero hH A v w hvw hA ρ κ)
  have hav : average (fun κ : Fin q ↪ Coord =>
      ((6 - p : ℕ) : ℝ) *
        average (fun ρ : Fin (p + 1) ↪ Coord =>
          contractionIntegrand H A (Sampling.dropFirst ρ) κ (ρ 0)) +
        ∑ j : Fin p, average (fun ρ : Fin p ↪ Coord =>
          contractionIntegrand H A ρ κ (ρ j))) = 0 := by
    simp only [ht, average_zero]
  rw [average_add, average_mul, average_sum] at hav
  simp only [contractionIntegrand, contractionMonomial_new,
    contractionMonomial_occupied hH, contractionMonomial_occupied hH.transpose] at hav
  simp only [injectiveMoment_reverse_iterated] at hav
  exact hav

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5177 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5177 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5177 = injectiveMoment H raw5177step0 := by
      have hz : ∀ j, raw5177 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5177step0 = (fun i j => raw5177 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5177 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical5183 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5183 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5183 = injectiveMoment H raw5183step0 := by
      have hz : ∀ j, raw5183 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5183step0 = (fun i j => raw5183 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5183 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5458 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5458 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5458 = injectiveMoment H raw5458step0 := by
      have heq : raw5458step0 = raw5458.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5458).symm
    injectiveMoment H raw5458step0 = injectiveMoment H raw5458step1 := by
      have heq : raw5458step1 = (fun i j => raw5458step0 (permutation6 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5458step0 permutation6 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical187
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5990 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw5990 = injectiveMoment H raw5990step0 := by
      have heq : raw5990step0 = raw5990.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5990).symm
    injectiveMoment H raw5990step0 = injectiveMoment H raw5990step1 := by
      have heq : raw5990step1 = (fun i j => raw5990step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5990step0 permutation7 permutation2
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical215
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6885 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6885 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw6885 = injectiveMoment H raw6885step0 := by
      have heq : raw6885step0 = raw6885.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6885).symm
    injectiveMoment H raw6885step0 = injectiveMoment H raw6885step1 := by
      have heq : raw6885step1 = (fun i j => raw6885step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6885step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical241
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7718 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7718 = injectiveMoment H node5 := by
  rfl

theorem canonical7735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7735 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7735 = injectiveMoment H raw7735step0 := by
      have hz : ∀ j, raw7735 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7735step0 = (fun i j => raw7735 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7735 permutation7 hz
    _ = injectiveMoment H node5 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8215 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8215 = injectiveMoment H raw8215step0 := by
      have hz : ∀ i, raw8215 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8215step0 = (fun i j => raw8215 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8215 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical841 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw841 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw841 = injectiveMoment H raw841step0 := by
      have heq : raw841step0 = raw841.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw841).symm
    injectiveMoment H raw841step0 = injectiveMoment H raw841step1 := by
      have heq : raw841step1 = (fun i j => raw841step0 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw841step0 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical279
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8946 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw8946 = injectiveMoment H raw8946step0 := by
      have hz : ∀ j, raw8946 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw8946step0 = (fun i j => raw8946 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8946 permutation0 hz
    injectiveMoment H raw8946step0 = injectiveMoment H raw8946step1 := by
      have hz : ∀ i, raw8946step0 i (permutation2 0) = 0 := by decide +kernel
      have heq : raw8946step1 = (fun i j => raw8946step0 i (permutation2 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step0 permutation2 hz
    injectiveMoment H raw8946step1 = injectiveMoment H raw8946step2 := by
      have hz : ∀ i, raw8946step1 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw8946step2 = (fun i j => raw8946step1 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step1 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical175 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw175 = injectiveMoment H node150 := by
  calc
    injectiveMoment H raw175 = injectiveMoment H raw175step0 := by
      have heq : raw175step0 = -raw175 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw175).symm
    injectiveMoment H raw175step0 = injectiveMoment H raw175step1 := by
      have heq : raw175step1 = (fun i j => raw175step0 (permutation11 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw175step0 permutation11 permutation6
    _ = injectiveMoment H node150 := by rfl

theorem canonical176 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw176 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw176 = injectiveMoment H raw176step0 := by
      have heq : raw176step0 = raw176.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw176).symm
    injectiveMoment H raw176step0 = injectiveMoment H raw176step1 := by
      have heq : raw176step1 = -raw176step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw176step0).symm
    injectiveMoment H raw176step1 = injectiveMoment H raw176step2 := by
      have heq : raw176step2 = (fun i j => raw176step1 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw176step1 permutation4 permutation6
    _ = injectiveMoment H node52 := by rfl

theorem canonical180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw180 = injectiveMoment H node9 := by
  calc
    injectiveMoment H raw180 = injectiveMoment H raw180step0 := by
      have heq : raw180step0 = raw180.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw180).symm
    _ = injectiveMoment H node9 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical208 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw208 = injectiveMoment H node16 := by
  rfl

theorem canonical211 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw211 = injectiveMoment H node8 := by
  rfl

theorem canonical214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw214 = injectiveMoment H node9 := by
  rfl

theorem canonical215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw215 = injectiveMoment H node2 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound0
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound0 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node0 = Sparse.eval value0 (momentVector H) := by
  have hc : momentVector H 0 = injectiveMoment H node0 := rfl
  simp [value0, Sparse.eval, hc]

theorem sound2 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node2 = Sparse.eval value2 (momentVector H) := by
  have hc : momentVector H 6 = injectiveMoment H node2 := rfl
  simp [value2, Sparse.eval, hc]

theorem sound3 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node3 = Sparse.eval value3 (momentVector H) := by
  have hc : momentVector H 2 = injectiveMoment H node3 := rfl
  simp [value3, Sparse.eval, hc]

theorem sound4 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node4 = Sparse.eval value4 (momentVector H) := by
  have hc : momentVector H 1 = injectiveMoment H node4 := rfl
  simp [value4, Sparse.eval, hc]

theorem sound5 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node5 = Sparse.eval value5 (momentVector H) := by
  have heq : pivotMatrix5 = (fun u v => node5 (pivotPermutation5 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node5 = injectiveMoment H pivotMatrix5 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix5 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 1 < 6) hH pivotMatrix5 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix5 (0 : Fin 1)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : mergeFirst pivotMatrix5 (0 : Fin 1) = raw8946 := by ext i j; fin_cases i; fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8946 hH).trans (sound0 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (5 : ℝ) * injectiveMoment H node5 + (injectiveMoment H (mergeFirst pivotMatrix5 (0 : Fin 1))) = 0 at hc
  rw [hm0] at hc
  norm_num [value5, value0, Sparse.eval] at hc ⊢
  linarith

theorem sound8 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node8 = Sparse.eval value8 (momentVector H) := by
  have heq : pivotMatrix8 = (fun u v => node8 (pivotPermutation8 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node8 = injectiveMoment H pivotMatrix8 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix8 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix8 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (0 : Fin 2) = raw926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical926 hH).trans (sound3 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)) =
      Sparse.eval value2 (momentVector H) := by
    have heq : mergeFirst pivotMatrix8 (1 : Fin 2) = raw215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical215 hH).trans (sound2 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node8 + (injectiveMoment H (mergeFirst pivotMatrix8 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix8 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value8, value2, value3, Sparse.eval] at hc ⊢
  linarith

theorem sound9 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node9 = Sparse.eval value9 (momentVector H) := by
  have hc : momentVector H 5 = injectiveMoment H node9 := rfl
  simp [value9, Sparse.eval, hc]

theorem sound10 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node10 = Sparse.eval value10 (momentVector H) := by
  have heq : pivotMatrix10 = (fun u v => node10 (pivotPermutation10 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node10 = injectiveMoment H pivotMatrix10 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix10 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix10 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix10 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix10 (0 : Fin 2) = raw5210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5210 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix10 (1 : Fin 2)) =
      Sparse.eval value3 (momentVector H) := by
    have heq : mergeFirst pivotMatrix10 (1 : Fin 2) = raw926 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical926 hH).trans (sound3 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node10 + (injectiveMoment H (mergeFirst pivotMatrix10 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix10 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value10, value3, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound11 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node11 = Sparse.eval value11 (momentVector H) := by
  have heq : pivotMatrix11 = (fun u v => node11 (pivotPermutation11 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node11 = injectiveMoment H pivotMatrix11 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix11 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix11 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix11 (0 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix11 (0 : Fin 2) = raw7718 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7718 hH).trans (sound5 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix11 (1 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix11 (1 : Fin 2) = raw5210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5210 hH).trans (sound4 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node11 + (injectiveMoment H (mergeFirst pivotMatrix11 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix11 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value11, value4, value5, Sparse.eval] at hc ⊢
  linarith

theorem sound16 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node16 = Sparse.eval value16 (momentVector H) := by
  have heq : pivotMatrix16 = (fun u v => node16 (pivotPermutation16 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node16 = injectiveMoment H pivotMatrix16 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix16 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix16 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix16 (0 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (0 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix16 (1 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (1 : Fin 3) = raw214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical214 hH).trans (sound9 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix16 (2 : Fin 3)) =
      Sparse.eval value8 (momentVector H) := by
    have heq : mergeFirst pivotMatrix16 (2 : Fin 3) = raw211 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical211 hH).trans (sound8 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node16 + (injectiveMoment H (mergeFirst pivotMatrix16 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix16 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix16 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value16, value10, value8, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound35 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node35 = Sparse.eval value35 (momentVector H) := by
  have hc : momentVector H 8 = injectiveMoment H node35 := rfl
  simp [value35, Sparse.eval, hc]

theorem sound52 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node52 = Sparse.eval value52 (momentVector H) := by
  have heq : pivotMatrix52 = (fun u v => node52.transpose (pivotPermutation52 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node52 = injectiveMoment H pivotMatrix52 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix52 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix52 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (0 : Fin 2) = raw180 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical180 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix52 (1 : Fin 2) = raw841 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical841 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node52 + (injectiveMoment H (mergeFirst pivotMatrix52 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix52 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value52, value10, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound56 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node56 = Sparse.eval value56 (momentVector H) := by
  have heq : pivotMatrix56 = (fun u v => node56 (pivotPermutation56 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node56 = injectiveMoment H pivotMatrix56 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix56 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix56 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (0 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix56 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node56 + (injectiveMoment H (mergeFirst pivotMatrix56 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix56 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value56, value10, value11, Sparse.eval] at hc ⊢
  linarith

theorem sound62 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node62 = Sparse.eval value62 (momentVector H) := by
  have heq : pivotMatrix62 = (fun u v => node62 (pivotPermutation62 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node62 = injectiveMoment H pivotMatrix62 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix62 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix62 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (1 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node62 + (injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value62, value11, value4, Sparse.eval] at hc ⊢
  linarith

theorem sound63 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node63 = Sparse.eval value63 (momentVector H) := by
  have heq : pivotMatrix63 = (fun u v => node63.transpose (pivotPermutation63 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node63 = injectiveMoment H pivotMatrix63 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
    rw [injectiveMoment_transpose]
  have hshape : pivotMatrix63 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix63 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (0 : Fin 2) = raw5458 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5458 hH).trans (sound10 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix63 (1 : Fin 2) = raw7977 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7977 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node63 + (injectiveMoment H (mergeFirst pivotMatrix63 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix63 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value63, value10, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1447 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1447 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw1447 = injectiveMoment H raw1447step0 := by
      have heq : raw1447step0 = raw1447.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1447).symm
    injectiveMoment H raw1447step0 = injectiveMoment H raw1447step1 := by
      have heq : raw1447step1 = (fun i j => raw1447step0 (permutation8 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1447step0 permutation8 permutation6
    _ = injectiveMoment H node52 := by rfl

theorem canonical1449 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1449 = injectiveMoment H node35 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2861 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2861 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw2861 = injectiveMoment H raw2861step0 := by
      have heq : raw2861step0 = raw2861.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2861).symm
    injectiveMoment H raw2861step0 = injectiveMoment H raw2861step1 := by
      have heq : raw2861step1 = (fun i j => raw2861step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2861step0 permutation6 permutation5
    _ = injectiveMoment H node63 := by rfl

theorem canonical2862 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2862 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2862 = injectiveMoment H raw2862step0 := by
      have heq : raw2862step0 = (fun i j => raw2862 (permutation3 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2862 permutation3 permutation5
    _ = injectiveMoment H node56 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound65 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node65 = Sparse.eval value65 (momentVector H) := by
  have heq : pivotMatrix65 = (fun u v => node65 (pivotPermutation65 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node65 = injectiveMoment H pivotMatrix65 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix65 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix65 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (0 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (1 : Fin 3) = raw7709 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7709 hH).trans (sound5 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (2 : Fin 3) = raw7735 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7735 hH).trans (sound5 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node65 + (injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value65, value11, value5, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4160 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4160 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4160 = injectiveMoment H raw4160step0 := by
      have heq : raw4160step0 = -raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4160).symm
    injectiveMoment H raw4160step0 = injectiveMoment H raw4160step1 := by
      have heq : raw4160step1 = (fun i j => raw4160step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4160step0 permutation7 permutation5
    _ = injectiveMoment H node62 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound150 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node150 = Sparse.eval value150 (momentVector H) := by
  have heq : pivotMatrix150 = (fun u v => node150 (pivotPermutation150 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node150 = injectiveMoment H pivotMatrix150 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix150 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix150 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix150 (0 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix150 (0 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix150 (1 : Fin 3)) =
      Sparse.eval value35 (momentVector H) := by
    have heq : mergeFirst pivotMatrix150 (1 : Fin 3) = raw1449 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1449 hH).trans (sound35 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix150 (2 : Fin 3)) =
      Sparse.eval value52 (momentVector H) := by
    have heq : mergeFirst pivotMatrix150 (2 : Fin 3) = raw1447 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1447 hH).trans (sound52 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node150 + (injectiveMoment H (mergeFirst pivotMatrix150 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix150 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix150 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value150, value35, value52, value56, Sparse.eval] at hc ⊢
  linarith

theorem sound181 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node181 = Sparse.eval value181 (momentVector H) := by
  have heq : pivotMatrix181 = (fun u v => node181 (pivotPermutation181 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node181 = injectiveMoment H pivotMatrix181 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix181 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix181 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix181 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (0 : Fin 3) = raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4160 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix181 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (1 : Fin 3) = raw2862 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2862 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix181 (2 : Fin 3)) =
      Sparse.eval value63 (momentVector H) := by
    have heq : mergeFirst pivotMatrix181 (2 : Fin 3) = raw2861 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2861 hH).trans (sound63 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node181 + (injectiveMoment H (mergeFirst pivotMatrix181 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix181 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix181 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value181, value56, value62, value63, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node404 node404Labels = Sparse.eval singlePairValue404 (familyPairVector B) := by
  have hp := single_label_three B hB node404
  have hl : node404Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node404 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 1) = PairSemantics.raw5197 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node404 PairSemantics.raw5197; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5197 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 2) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node404 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node404 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node404 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value181 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node404 (EqualityPatterns.family3.label 4) = PairSemantics.raw781 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node404 PairSemantics.raw781; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical781 hH).trans (PairSemantics.sound181 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue404, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value65, PairSemantics.value181, Sparse.eval] at hp ⊢
  linarith only [hp]

theorem singlePair407 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node407 node407Labels = Sparse.eval singlePairValue407 (familyPairVector B) := by
  have hp := single_label_three B hB node407
  have hl : node407Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node407 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node407 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node407 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node407 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node407 (EqualityPatterns.family3.label 1) = PairSemantics.raw5199 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node407 PairSemantics.raw5199; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node407 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node407 (EqualityPatterns.family3.label 2) = PairSemantics.raw7683 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node407 PairSemantics.raw7683; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7683 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node407 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value3 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node407 (EqualityPatterns.family3.label 3) = PairSemantics.raw900 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node407 PairSemantics.raw900; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical900 hH).trans (PairSemantics.sound3 hH)
  have hm4 : familyPairMoment B (groupedColumns node407 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value63 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node407 (EqualityPatterns.family3.label 4) = PairSemantics.raw784 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node407 PairSemantics.raw784; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical784 hH).trans (PairSemantics.sound63 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue407, PairSemantics.value0, PairSemantics.value3, PairSemantics.value11, PairSemantics.value63, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair157 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node157 node157Labels = Sparse.eval singlePairValue157 (familyPairVector B) := by
  have hp := single_label_three B hB node157
  have hl : node157Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node157 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node157 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node157 PairSemantics.raw7980
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node157 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node157 (EqualityPatterns.family3.label 1) = PairSemantics.raw5177 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node157 PairSemantics.raw5177
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5177 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node157 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node157 (EqualityPatterns.family3.label 2) = PairSemantics.raw5197 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node157 PairSemantics.raw5197
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5197 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node157 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value16 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node157 (EqualityPatterns.family3.label 3) = PairSemantics.raw208 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node157 PairSemantics.raw208
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical208 hH).trans (PairSemantics.sound16 hH)
  have hm4 : familyPairMoment B (groupedColumns node157 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value150 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node157 (EqualityPatterns.family3.label 4) = PairSemantics.raw175 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node157 PairSemantics.raw175
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical175 hH).trans (PairSemantics.sound150 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue157, PairSemantics.value0, PairSemantics.value11, PairSemantics.value16, PairSemantics.value150, Sparse.eval] at hp ⊢
  linarith only [hp]

theorem singlePair158 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node158 node158Labels = Sparse.eval singlePairValue158 (familyPairVector B) := by
  have hp := single_label_three B hB node158
  have hl : node158Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node158 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node158 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext
      unfold node158 PairSemantics.raw7979
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node158 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node158 (EqualityPatterns.family3.label 1) = PairSemantics.raw5183 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext
      unfold node158 PairSemantics.raw5183
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5183 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node158 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node158 (EqualityPatterns.family3.label 2) = PairSemantics.raw5199 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext
      unfold node158 PairSemantics.raw5199
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node158 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value8 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node158 (EqualityPatterns.family3.label 3) = PairSemantics.raw211 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext
      unfold node158 PairSemantics.raw211
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical211 hH).trans (PairSemantics.sound8 hH)
  have hm4 : familyPairMoment B (groupedColumns node158 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value52 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node158 (EqualityPatterns.family3.label 4) = PairSemantics.raw176 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext
      unfold node158 PairSemantics.raw176
      decide +kernel
    rw [heq]
    exact (PairSemantics.canonical176 hH).trans (PairSemantics.sound52 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue158, PairSemantics.value0, PairSemantics.value4, PairSemantics.value8, PairSemantics.value11, PairSemantics.value52, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton1301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1301 node1301Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node157 node157Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw78 singletonSmall1301
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1301) = raw78Labels := by decide +kernel
  rw [hl, canonical78 B hB] at h
  have hc0 : mixedMoment B raw78 (Fin.cases (0 : Fin 1) singletonSmall1301) =
      mixedMoment B node157 node157Labels := by
    have ha : raw78 = raw79 := by apply Matrix.ext; unfold raw78 raw79; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1301 = raw79Labels := by decide +kernel
    rw [ha, hj, canonical79 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton1304 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node1304 node1304Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node158 node158Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw82 singletonSmall1304
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall1304) = raw82Labels := by decide +kernel
  rw [hl, canonical82 B hB] at h
  have hc0 : mixedMoment B raw82 (Fin.cases (0 : Fin 1) singletonSmall1304) =
      mixedMoment B node158 node158Labels := by
    have ha : raw82 = raw83 := by apply Matrix.ext; unfold raw82 raw83; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall1304 = raw83Labels := by decide +kernel
    rw [ha, hj, canonical83 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton2767 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2767 node2767Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node404 node404Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw270 singletonSmall2767
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2767) = raw270Labels := by decide +kernel
  rw [hl, canonical270 B hB] at h
  have hc0 : mixedMoment B raw270 (Fin.cases (0 : Fin 1) singletonSmall2767) =
      mixedMoment B node404 node404Labels := by
    have ha : raw270 = raw271 := by apply Matrix.ext; unfold raw270 raw271; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2767 = raw271Labels := by decide +kernel
    rw [ha, hj, canonical271 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

theorem singleton2770 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2770 node2770Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node407 node407Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw274 singletonSmall2770
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2770) = raw274Labels := by decide +kernel
  rw [hl, canonical274 B hB] at h
  have hc0 : mixedMoment B raw274 (Fin.cases (0 : Fin 1) singletonSmall2770) =
      mixedMoment B node407 node407Labels := by
    have ha : raw274 = raw275 := by apply Matrix.ext; unfold raw274 raw275; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2770 = raw275Labels := by decide +kernel
    rw [ha, hj, canonical275 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4144 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4144 node4144Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node572 node572Labels + mixedMoment B node1492 node1492Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw771 singletonSmall4144
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4144) = raw771Labels := by decide +kernel
  rw [hl, canonical771 B hB] at h
  have hc0 : mixedMoment B raw771 (Fin.cases (0 : Fin 2) singletonSmall4144) =
      mixedMoment B node572 node572Labels := by
    have ha : raw771 = raw772 := by apply Matrix.ext; unfold raw771 raw772; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4144 = raw772Labels := by decide +kernel
    rw [ha, hj, canonical772 B hB]
  have hc1 : mixedMoment B raw771 (Fin.cases (1 : Fin 2) singletonSmall4144) =
      mixedMoment B node1492 node1492Labels := by
    have ha : raw771 = raw773 := by apply Matrix.ext; unfold raw771 raw773; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4144 = raw773Labels := by decide +kernel
    rw [ha, hj, canonical773 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4146 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4146 node4146Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node574 node574Labels + mixedMoment B node1494 node1494Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw777 singletonSmall4146
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4146) = raw777Labels := by decide +kernel
  rw [hl, canonical777 B hB] at h
  have hc0 : mixedMoment B raw777 (Fin.cases (0 : Fin 2) singletonSmall4146) =
      mixedMoment B node574 node574Labels := by
    have ha : raw777 = raw778 := by apply Matrix.ext; unfold raw777 raw778; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4146 = raw778Labels := by decide +kernel
    rw [ha, hj, canonical778 B hB]
  have hc1 : mixedMoment B raw777 (Fin.cases (1 : Fin 2) singletonSmall4146) =
      mixedMoment B node1494 node1494Labels := by
    have ha : raw777 = raw779 := by apply Matrix.ext; unfold raw777 raw779; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4146 = raw779Labels := by decide +kernel
    rw [ha, hj, canonical779 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4148 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4148 node4148Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node576 node576Labels + mixedMoment B node1496 node1496Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw783 singletonSmall4148
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4148) = raw783Labels := by decide +kernel
  rw [hl, canonical783 B hB] at h
  have hc0 : mixedMoment B raw783 (Fin.cases (0 : Fin 2) singletonSmall4148) =
      mixedMoment B node576 node576Labels := by
    have ha : raw783 = raw784 := by apply Matrix.ext; unfold raw783 raw784; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4148 = raw784Labels := by decide +kernel
    rw [ha, hj, canonical784 B hB]
  have hc1 : mixedMoment B raw783 (Fin.cases (1 : Fin 2) singletonSmall4148) =
      mixedMoment B node1496 node1496Labels := by
    have ha : raw783 = raw785 := by apply Matrix.ext; unfold raw783 raw785; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4148 = raw785Labels := by decide +kernel
    rw [ha, hj, canonical785 B hB]
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

theorem singleton4177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4177 node4177Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node605 node605Labels + mixedMoment B node1518 node1518Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw813 singletonSmall4177
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4177) = raw813Labels := by decide +kernel
  rw [hl, canonical813 B hB] at h
  have hc0 : mixedMoment B raw813 (Fin.cases (0 : Fin 2) singletonSmall4177) =
      mixedMoment B node605 node605Labels := by
    have ha : raw813 = raw814 := by apply Matrix.ext; unfold raw813 raw814; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4177 = raw814Labels := by decide +kernel
    rw [ha, hj, canonical814 B hB]
  have hc1 : mixedMoment B raw813 (Fin.cases (1 : Fin 2) singletonSmall4177) =
      mixedMoment B node1518 node1518Labels := by
    have ha : raw813 = raw815 := by apply Matrix.ext; unfold raw813 raw815; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4177 = raw815Labels := by decide +kernel
    rw [ha, hj, canonical815 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4293 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4293 node4293Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node871 node871Labels + mixedMoment B node1568 node1568Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1041 singletonSmall4293
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4293) = raw1041Labels := by decide +kernel
  rw [hl, canonical1041 B hB] at h
  have hc0 : mixedMoment B raw1041 (Fin.cases (0 : Fin 2) singletonSmall4293) =
      mixedMoment B node871 node871Labels := by
    have ha : raw1041 = raw1042 := by apply Matrix.ext; unfold raw1041 raw1042; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4293 = raw1042Labels := by decide +kernel
    rw [ha, hj, canonical1042 B hB]
  have hc1 : mixedMoment B raw1041 (Fin.cases (1 : Fin 2) singletonSmall4293) =
      mixedMoment B node1568 node1568Labels := by
    have ha : raw1041 = raw1043 := by apply Matrix.ext; unfold raw1041 raw1043; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4293 = raw1043Labels := by decide +kernel
    rw [ha, hj, canonical1043 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4315 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4315 node4315Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node893 node893Labels + mixedMoment B node1578 node1578Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1086 singletonSmall4315
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4315) = raw1086Labels := by decide +kernel
  rw [hl, canonical1086 B hB] at h
  have hc0 : mixedMoment B raw1086 (Fin.cases (0 : Fin 2) singletonSmall4315) =
      mixedMoment B node893 node893Labels := by
    have ha : raw1086 = raw1087 := by apply Matrix.ext; unfold raw1086 raw1087; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4315 = raw1087Labels := by decide +kernel
    rw [ha, hj, canonical1087 B hB]
  have hc1 : mixedMoment B raw1086 (Fin.cases (1 : Fin 2) singletonSmall4315) =
      mixedMoment B node1578 node1578Labels := by
    have ha : raw1086 = raw1088 := by apply Matrix.ext; unfold raw1086 raw1088; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4315 = raw1088Labels := by decide +kernel
    rw [ha, hj, canonical1088 B hB]
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

theorem singleton4517 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4517 node4517Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1101 node1101Labels + mixedMoment B node3235 node3235Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1323 singletonSmall4517
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4517) = raw1323Labels := by decide +kernel
  rw [hl, canonical1323 B hB] at h
  have hc0 : mixedMoment B raw1323 (Fin.cases (0 : Fin 2) singletonSmall4517) =
      mixedMoment B node1101 node1101Labels := by
    have ha : raw1323 = raw1324 := by apply Matrix.ext; unfold raw1323 raw1324; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4517 = raw1324Labels := by decide +kernel
    rw [ha, hj, canonical1324 B hB]
  have hc1 : mixedMoment B raw1323 (Fin.cases (1 : Fin 2) singletonSmall4517) =
      mixedMoment B node3235 node3235Labels := by
    have ha : raw1323 = raw1325 := by apply Matrix.ext; unfold raw1323 raw1325; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4517 = raw1325Labels := by decide +kernel
    rw [ha, hj, canonical1325 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4520 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4520 node4520Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1104 node1104Labels + mixedMoment B node3237 node3237Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1332 singletonSmall4520
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4520) = raw1332Labels := by decide +kernel
  rw [hl, canonical1332 B hB] at h
  have hc0 : mixedMoment B raw1332 (Fin.cases (0 : Fin 2) singletonSmall4520) =
      mixedMoment B node1104 node1104Labels := by
    have ha : raw1332 = raw1333 := by apply Matrix.ext; unfold raw1332 raw1333; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4520 = raw1333Labels := by decide +kernel
    rw [ha, hj, canonical1333 B hB]
  have hc1 : mixedMoment B raw1332 (Fin.cases (1 : Fin 2) singletonSmall4520) =
      mixedMoment B node3237 node3237Labels := by
    have ha : raw1332 = raw1334 := by apply Matrix.ext; unfold raw1332 raw1334; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4520 = raw1334Labels := by decide +kernel
    rw [ha, hj, canonical1334 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4523 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4523 node4523Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1107 node1107Labels + mixedMoment B node3250 node3250Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1341 singletonSmall4523
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4523) = raw1341Labels := by decide +kernel
  rw [hl, canonical1341 B hB] at h
  have hc0 : mixedMoment B raw1341 (Fin.cases (0 : Fin 2) singletonSmall4523) =
      mixedMoment B node1107 node1107Labels := by
    have ha : raw1341 = raw1342 := by apply Matrix.ext; unfold raw1341 raw1342; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4523 = raw1342Labels := by decide +kernel
    rw [ha, hj, canonical1342 B hB]
  have hc1 : mixedMoment B raw1341 (Fin.cases (1 : Fin 2) singletonSmall4523) =
      mixedMoment B node3250 node3250Labels := by
    have ha : raw1341 = raw1343 := by apply Matrix.ext; unfold raw1341 raw1343; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4523 = raw1343Labels := by decide +kernel
    rw [ha, hj, canonical1343 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4526 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4526 node4526Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1110 node1110Labels + mixedMoment B node3252 node3252Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1350 singletonSmall4526
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4526) = raw1350Labels := by decide +kernel
  rw [hl, canonical1350 B hB] at h
  have hc0 : mixedMoment B raw1350 (Fin.cases (0 : Fin 2) singletonSmall4526) =
      mixedMoment B node1110 node1110Labels := by
    have ha : raw1350 = raw1351 := by apply Matrix.ext; unfold raw1350 raw1351; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4526 = raw1351Labels := by decide +kernel
    rw [ha, hj, canonical1351 B hB]
  have hc1 : mixedMoment B raw1350 (Fin.cases (1 : Fin 2) singletonSmall4526) =
      mixedMoment B node3252 node3252Labels := by
    have ha : raw1350 = raw1352 := by apply Matrix.ext; unfold raw1350 raw1352; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4526 = raw1352Labels := by decide +kernel
    rw [ha, hj, canonical1352 B hB]
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

theorem singleton4546 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4546 node4546Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1131 node1131Labels + mixedMoment B node3264 node3264Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1371 singletonSmall4546
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4546) = raw1371Labels := by decide +kernel
  rw [hl, canonical1371 B hB] at h
  have hc0 : mixedMoment B raw1371 (Fin.cases (0 : Fin 2) singletonSmall4546) =
      mixedMoment B node1131 node1131Labels := by
    have ha : raw1371 = raw1372 := by apply Matrix.ext; unfold raw1371 raw1372; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4546 = raw1372Labels := by decide +kernel
    rw [ha, hj, canonical1372 B hB]
  have hc1 : mixedMoment B raw1371 (Fin.cases (1 : Fin 2) singletonSmall4546) =
      mixedMoment B node3264 node3264Labels := by
    have ha : raw1371 = raw1373 := by apply Matrix.ext; unfold raw1371 raw1373; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4546 = raw1373Labels := by decide +kernel
    rw [ha, hj, canonical1373 B hB]
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

theorem singleton4608 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4608 node4608Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1242 node1242Labels + mixedMoment B node3300 node3300Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1434 singletonSmall4608
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4608) = raw1434Labels := by decide +kernel
  rw [hl, canonical1434 B hB] at h
  have hc0 : mixedMoment B raw1434 (Fin.cases (0 : Fin 2) singletonSmall4608) =
      mixedMoment B node1242 node1242Labels := by
    have ha : raw1434 = raw1435 := by apply Matrix.ext; unfold raw1434 raw1435; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4608 = raw1435Labels := by decide +kernel
    rw [ha, hj, canonical1435 B hB]
  have hc1 : mixedMoment B raw1434 (Fin.cases (1 : Fin 2) singletonSmall4608) =
      mixedMoment B node3300 node3300Labels := by
    have ha : raw1434 = raw1436 := by apply Matrix.ext; unfold raw1434 raw1436; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4608 = raw1436Labels := by decide +kernel
    rw [ha, hj, canonical1436 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4612 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4612 node4612Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1246 node1246Labels + mixedMoment B node3301 node3301Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1437 singletonSmall4612
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4612) = raw1437Labels := by decide +kernel
  rw [hl, canonical1437 B hB] at h
  have hc0 : mixedMoment B raw1437 (Fin.cases (0 : Fin 2) singletonSmall4612) =
      mixedMoment B node1246 node1246Labels := by
    have ha : raw1437 = raw1438 := by apply Matrix.ext; unfold raw1437 raw1438; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4612 = raw1438Labels := by decide +kernel
    rw [ha, hj, canonical1438 B hB]
  have hc1 : mixedMoment B raw1437 (Fin.cases (1 : Fin 2) singletonSmall4612) =
      mixedMoment B node3301 node3301Labels := by
    have ha : raw1437 = raw1439 := by apply Matrix.ext; unfold raw1437 raw1439; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4612 = raw1439Labels := by decide +kernel
    rw [ha, hj, canonical1439 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4624 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4624 node4624Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1301 node1301Labels + mixedMoment B node3309 node3309Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1455 singletonSmall4624
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4624) = raw1455Labels := by decide +kernel
  rw [hl, canonical1455 B hB] at h
  have hc0 : mixedMoment B raw1455 (Fin.cases (0 : Fin 2) singletonSmall4624) =
      mixedMoment B node1301 node1301Labels := by
    have ha : raw1455 = raw1456 := by apply Matrix.ext; unfold raw1455 raw1456; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4624 = raw1456Labels := by decide +kernel
    rw [ha, hj, canonical1456 B hB]
  have hc1 : mixedMoment B raw1455 (Fin.cases (1 : Fin 2) singletonSmall4624) =
      mixedMoment B node3309 node3309Labels := by
    have ha : raw1455 = raw1457 := by apply Matrix.ext; unfold raw1455 raw1457; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4624 = raw1457Labels := by decide +kernel
    rw [ha, hj, canonical1457 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4625 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4625 node4625Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1304 node1304Labels + mixedMoment B node3310 node3310Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1458 singletonSmall4625
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4625) = raw1458Labels := by decide +kernel
  rw [hl, canonical1458 B hB] at h
  have hc0 : mixedMoment B raw1458 (Fin.cases (0 : Fin 2) singletonSmall4625) =
      mixedMoment B node1304 node1304Labels := by
    have ha : raw1458 = raw1459 := by apply Matrix.ext; unfold raw1458 raw1459; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4625 = raw1459Labels := by decide +kernel
    rw [ha, hj, canonical1459 B hB]
  have hc1 : mixedMoment B raw1458 (Fin.cases (1 : Fin 2) singletonSmall4625) =
      mixedMoment B node3310 node3310Labels := by
    have ha : raw1458 = raw1460 := by apply Matrix.ext; unfold raw1458 raw1460; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4625 = raw1460Labels := by decide +kernel
    rw [ha, hj, canonical1460 B hB]
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

theorem singleton5078 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5078 node5078Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2485 node2485Labels + mixedMoment B node3481 node3481Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2103 singletonSmall5078
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5078) = raw2103Labels := by decide +kernel
  rw [hl, canonical2103 B hB] at h
  have hc0 : mixedMoment B raw2103 (Fin.cases (0 : Fin 2) singletonSmall5078) =
      mixedMoment B node2485 node2485Labels := by
    have ha : raw2103 = raw2104 := by apply Matrix.ext; unfold raw2103 raw2104; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5078 = raw2104Labels := by decide +kernel
    rw [ha, hj, canonical2104 B hB]
  have hc1 : mixedMoment B raw2103 (Fin.cases (1 : Fin 2) singletonSmall5078) =
      mixedMoment B node3481 node3481Labels := by
    have ha : raw2103 = raw2105 := by apply Matrix.ext; unfold raw2103 raw2105; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5078 = raw2105Labels := by decide +kernel
    rw [ha, hj, canonical2105 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5293 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5293 node5293Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2767 node2767Labels + mixedMoment B node3627 node3627Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2301 singletonSmall5293
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5293) = raw2301Labels := by decide +kernel
  rw [hl, canonical2301 B hB] at h
  have hc0 : mixedMoment B raw2301 (Fin.cases (0 : Fin 2) singletonSmall5293) =
      mixedMoment B node2767 node2767Labels := by
    have ha : raw2301 = raw2302 := by apply Matrix.ext; unfold raw2301 raw2302; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5293 = raw2302Labels := by decide +kernel
    rw [ha, hj, canonical2302 B hB]
  have hc1 : mixedMoment B raw2301 (Fin.cases (1 : Fin 2) singletonSmall5293) =
      mixedMoment B node3627 node3627Labels := by
    have ha : raw2301 = raw2303 := by apply Matrix.ext; unfold raw2301 raw2303; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5293 = raw2303Labels := by decide +kernel
    rw [ha, hj, canonical2303 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5296 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5296 node5296Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2770 node2770Labels + mixedMoment B node3634 node3634Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2307 singletonSmall5296
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5296) = raw2307Labels := by decide +kernel
  rw [hl, canonical2307 B hB] at h
  have hc0 : mixedMoment B raw2307 (Fin.cases (0 : Fin 2) singletonSmall5296) =
      mixedMoment B node2770 node2770Labels := by
    have ha : raw2307 = raw2308 := by apply Matrix.ext; unfold raw2307 raw2308; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5296 = raw2308Labels := by decide +kernel
    rw [ha, hj, canonical2308 B hB]
  have hc1 : mixedMoment B raw2307 (Fin.cases (1 : Fin 2) singletonSmall5296) =
      mixedMoment B node3634 node3634Labels := by
    have ha : raw2307 = raw2309 := by apply Matrix.ext; unfold raw2307 raw2309; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5296 = raw2309Labels := by decide +kernel
    rw [ha, hj, canonical2309 B hB]
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

theorem sound871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node871 node871Labels = Sparse.eval nodeValue871 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 871) = mixedMoment B node871 node871Labels := rfl
  simpa [nodeValue871, Sparse.eval] using hc.symm

theorem sound893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node893 node893Labels = Sparse.eval nodeValue893 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 893) = mixedMoment B node893 node893Labels := rfl
  simpa [nodeValue893, Sparse.eval] using hc.symm

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

theorem sound1101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1101 node1101Labels = Sparse.eval nodeValue1101 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1101) = mixedMoment B node1101 node1101Labels := rfl
  simpa [nodeValue1101, Sparse.eval] using hc.symm

theorem sound1104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1104 node1104Labels = Sparse.eval nodeValue1104 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1104) = mixedMoment B node1104 node1104Labels := rfl
  simpa [nodeValue1104, Sparse.eval] using hc.symm

theorem sound1107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1107 node1107Labels = Sparse.eval nodeValue1107 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1107) = mixedMoment B node1107 node1107Labels := rfl
  simpa [nodeValue1107, Sparse.eval] using hc.symm

theorem sound1110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1110 node1110Labels = Sparse.eval nodeValue1110 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1110) = mixedMoment B node1110 node1110Labels := rfl
  simpa [nodeValue1110, Sparse.eval] using hc.symm

theorem sound1131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1131 node1131Labels = Sparse.eval nodeValue1131 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1131) = mixedMoment B node1131 node1131Labels := rfl
  simpa [nodeValue1131, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node157 node157Labels = Sparse.eval nodeValue157 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue157 (familyPairVector B) := singlePair157 B _hB
    _ = _ := by
      norm_num [singlePairValue157, nodeValue157, Sparse.eval, mixedVector]
      ring

theorem sound158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node158 node158Labels = Sparse.eval nodeValue158 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue158 (familyPairVector B) := singlePair158 B _hB
    _ = _ := by
      norm_num [singlePairValue158, nodeValue158, Sparse.eval, mixedVector]
      ring

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

theorem sound1240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1240 node1240Labels = Sparse.eval nodeValue1240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1240) = mixedMoment B node1240 node1240Labels := rfl
  simpa [nodeValue1240, Sparse.eval] using hc.symm

theorem sound1242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1242 node1242Labels = Sparse.eval nodeValue1242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1242) = mixedMoment B node1242 node1242Labels := rfl
  simpa [nodeValue1242, Sparse.eval] using hc.symm

theorem sound1246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1246 node1246Labels = Sparse.eval nodeValue1246 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1246) = mixedMoment B node1246 node1246Labels := rfl
  simpa [nodeValue1246, Sparse.eval] using hc.symm

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

theorem sound1301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1301 node1301Labels = Sparse.eval nodeValue1301 (mixedVector B) := by
  have h := singleton1301 B _hB
  rw [sound157 B _hB _hF] at h
  norm_num [nodeValue1301, nodeValue157, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1304 node1304Labels = Sparse.eval nodeValue1304 (mixedVector B) := by
  have h := singleton1304 B _hB
  rw [sound158 B _hB _hF] at h
  norm_num [nodeValue1304, nodeValue158, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound1492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1492 node1492Labels = Sparse.eval nodeValue1492 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1492) = mixedMoment B node1492 node1492Labels := rfl
  simpa [nodeValue1492, Sparse.eval] using hc.symm

theorem sound1494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1494 node1494Labels = Sparse.eval nodeValue1494 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1494) = mixedMoment B node1494 node1494Labels := rfl
  simpa [nodeValue1494, Sparse.eval] using hc.symm

theorem sound1496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1496 node1496Labels = Sparse.eval nodeValue1496 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1496) = mixedMoment B node1496 node1496Labels := rfl
  simpa [nodeValue1496, Sparse.eval] using hc.symm

theorem sound1518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1518 node1518Labels = Sparse.eval nodeValue1518 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1518) = mixedMoment B node1518 node1518Labels := rfl
  simpa [nodeValue1518, Sparse.eval] using hc.symm

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

theorem sound1568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1568 node1568Labels = Sparse.eval nodeValue1568 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1568) = mixedMoment B node1568 node1568Labels := rfl
  simpa [nodeValue1568, Sparse.eval] using hc.symm

theorem sound1578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1578 node1578Labels = Sparse.eval nodeValue1578 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1578) = mixedMoment B node1578 node1578Labels := rfl
  simpa [nodeValue1578, Sparse.eval] using hc.symm

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

theorem sound1752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1752 node1752Labels = Sparse.eval nodeValue1752 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1752) = mixedMoment B node1752 node1752Labels := rfl
  simpa [nodeValue1752, Sparse.eval] using hc.symm

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

theorem sound2485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2485 node2485Labels = Sparse.eval nodeValue2485 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2485) = mixedMoment B node2485 node2485Labels := rfl
  simpa [nodeValue2485, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node404 node404Labels = Sparse.eval nodeValue404 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue404 (familyPairVector B) := singlePair404 B _hB
    _ = _ := by
      norm_num [singlePairValue404, nodeValue404, Sparse.eval, mixedVector]
      ring

theorem sound407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node407 node407Labels = Sparse.eval nodeValue407 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue407 (familyPairVector B) := singlePair407 B _hB
    _ = _ := by norm_num [singlePairValue407, nodeValue407, Sparse.eval, mixedVector]

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

theorem sound2767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2767 node2767Labels = Sparse.eval nodeValue2767 (mixedVector B) := by
  have h := singleton2767 B _hB
  rw [sound404 B _hB _hF] at h
  norm_num [nodeValue2767, nodeValue404, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2770 node2770Labels = Sparse.eval nodeValue2770 (mixedVector B) := by
  have h := singleton2770 B _hB
  rw [sound407 B _hB _hF] at h
  norm_num [nodeValue2770, nodeValue407, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound3235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3235 node3235Labels = Sparse.eval nodeValue3235 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3235) = mixedMoment B node3235 node3235Labels := rfl
  simpa [nodeValue3235, Sparse.eval] using hc.symm

theorem sound3237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3237 node3237Labels = Sparse.eval nodeValue3237 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3237) = mixedMoment B node3237 node3237Labels := rfl
  simpa [nodeValue3237, Sparse.eval] using hc.symm

theorem sound3250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3250 node3250Labels = Sparse.eval nodeValue3250 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3250) = mixedMoment B node3250 node3250Labels := rfl
  simpa [nodeValue3250, Sparse.eval] using hc.symm

theorem sound3252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3252 node3252Labels = Sparse.eval nodeValue3252 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3252) = mixedMoment B node3252 node3252Labels := rfl
  simpa [nodeValue3252, Sparse.eval] using hc.symm

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

theorem sound3264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3264 node3264Labels = Sparse.eval nodeValue3264 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3264) = mixedMoment B node3264 node3264Labels := rfl
  simpa [nodeValue3264, Sparse.eval] using hc.symm

theorem sound3299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3299 node3299Labels = Sparse.eval nodeValue3299 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3299) = mixedMoment B node3299 node3299Labels := rfl
  simpa [nodeValue3299, Sparse.eval] using hc.symm

theorem sound3300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3300 node3300Labels = Sparse.eval nodeValue3300 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3300) = mixedMoment B node3300 node3300Labels := rfl
  simpa [nodeValue3300, Sparse.eval] using hc.symm

theorem sound3301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3301 node3301Labels = Sparse.eval nodeValue3301 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3301) = mixedMoment B node3301 node3301Labels := rfl
  simpa [nodeValue3301, Sparse.eval] using hc.symm

theorem sound3309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3309 node3309Labels = Sparse.eval nodeValue3309 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3309) = mixedMoment B node3309 node3309Labels := rfl
  simpa [nodeValue3309, Sparse.eval] using hc.symm

theorem sound3310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3310 node3310Labels = Sparse.eval nodeValue3310 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3310) = mixedMoment B node3310 node3310Labels := rfl
  simpa [nodeValue3310, Sparse.eval] using hc.symm

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

theorem sound3481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3481 node3481Labels = Sparse.eval nodeValue3481 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3481) = mixedMoment B node3481 node3481Labels := rfl
  simpa [nodeValue3481, Sparse.eval] using hc.symm

theorem sound3486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3486 node3486Labels = Sparse.eval nodeValue3486 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3486) = mixedMoment B node3486 node3486Labels := rfl
  simpa [nodeValue3486, Sparse.eval] using hc.symm

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

theorem sound3627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3627 node3627Labels = Sparse.eval nodeValue3627 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3627) = mixedMoment B node3627 node3627Labels := rfl
  simpa [nodeValue3627, Sparse.eval] using hc.symm

theorem sound3634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3634 node3634Labels = Sparse.eval nodeValue3634 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3634) = mixedMoment B node3634 node3634Labels := rfl
  simpa [nodeValue3634, Sparse.eval] using hc.symm

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

theorem sound572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node572 node572Labels = Sparse.eval nodeValue572 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 572) = mixedMoment B node572 node572Labels := rfl
  simpa [nodeValue572, Sparse.eval] using hc.symm

theorem sound574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node574 node574Labels = Sparse.eval nodeValue574 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 574) = mixedMoment B node574 node574Labels := rfl
  simpa [nodeValue574, Sparse.eval] using hc.symm

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

theorem sound576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node576 node576Labels = Sparse.eval nodeValue576 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 576) = mixedMoment B node576 node576Labels := rfl
  simpa [nodeValue576, Sparse.eval] using hc.symm

theorem sound605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node605 node605Labels = Sparse.eval nodeValue605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 605) = mixedMoment B node605 node605Labels := rfl
  simpa [nodeValue605, Sparse.eval] using hc.symm

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

theorem sound4144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4144 node4144Labels = Sparse.eval nodeValue4144 (mixedVector B) := by
  have h := singleton4144 B _hB
  rw [sound572 B _hB _hF, sound1492 B _hB _hF] at h
  norm_num [nodeValue4144, nodeValue572, nodeValue1492, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4146 node4146Labels = Sparse.eval nodeValue4146 (mixedVector B) := by
  have h := singleton4146 B _hB
  rw [sound574 B _hB _hF, sound1494 B _hB _hF] at h
  norm_num [nodeValue4146, nodeValue574, nodeValue1494, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4148 node4148Labels = Sparse.eval nodeValue4148 (mixedVector B) := by
  have h := singleton4148 B _hB
  rw [sound576 B _hB _hF, sound1496 B _hB _hF] at h
  norm_num [nodeValue4148, nodeValue576, nodeValue1496, Sparse.eval] at h ⊢
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

theorem sound4177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4177 node4177Labels = Sparse.eval nodeValue4177 (mixedVector B) := by
  have h := singleton4177 B _hB
  rw [sound605 B _hB _hF, sound1518 B _hB _hF] at h
  norm_num [nodeValue4177, nodeValue605, nodeValue1518, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4293 node4293Labels = Sparse.eval nodeValue4293 (mixedVector B) := by
  have h := singleton4293 B _hB
  rw [sound871 B _hB _hF, sound1568 B _hB _hF] at h
  norm_num [nodeValue4293, nodeValue871, nodeValue1568, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4315 node4315Labels = Sparse.eval nodeValue4315 (mixedVector B) := by
  have h := singleton4315 B _hB
  rw [sound893 B _hB _hF, sound1578 B _hB _hF] at h
  norm_num [nodeValue4315, nodeValue893, nodeValue1578, Sparse.eval] at h ⊢
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

theorem sound4517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4517 node4517Labels = Sparse.eval nodeValue4517 (mixedVector B) := by
  have h := singleton4517 B _hB
  rw [sound1101 B _hB _hF, sound3235 B _hB _hF] at h
  norm_num [nodeValue4517, nodeValue1101, nodeValue3235, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4520 node4520Labels = Sparse.eval nodeValue4520 (mixedVector B) := by
  have h := singleton4520 B _hB
  rw [sound1104 B _hB _hF, sound3237 B _hB _hF] at h
  norm_num [nodeValue4520, nodeValue1104, nodeValue3237, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4523 node4523Labels = Sparse.eval nodeValue4523 (mixedVector B) := by
  have h := singleton4523 B _hB
  rw [sound1107 B _hB _hF, sound3250 B _hB _hF] at h
  norm_num [nodeValue4523, nodeValue1107, nodeValue3250, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4526 node4526Labels = Sparse.eval nodeValue4526 (mixedVector B) := by
  have h := singleton4526 B _hB
  rw [sound1110 B _hB _hF, sound3252 B _hB _hF] at h
  norm_num [nodeValue4526, nodeValue1110, nodeValue3252, Sparse.eval] at h ⊢
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

theorem sound4546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4546 node4546Labels = Sparse.eval nodeValue4546 (mixedVector B) := by
  have h := singleton4546 B _hB
  rw [sound1131 B _hB _hF, sound3264 B _hB _hF] at h
  norm_num [nodeValue4546, nodeValue1131, nodeValue3264, Sparse.eval] at h ⊢
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

theorem sound4608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4608 node4608Labels = Sparse.eval nodeValue4608 (mixedVector B) := by
  have h := singleton4608 B _hB
  rw [sound1242 B _hB _hF, sound3300 B _hB _hF] at h
  norm_num [nodeValue4608, nodeValue1242, nodeValue3300, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4612 node4612Labels = Sparse.eval nodeValue4612 (mixedVector B) := by
  have h := singleton4612 B _hB
  rw [sound1246 B _hB _hF, sound3301 B _hB _hF] at h
  norm_num [nodeValue4612, nodeValue1246, nodeValue3301, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4624 node4624Labels = Sparse.eval nodeValue4624 (mixedVector B) := by
  have h := singleton4624 B _hB
  rw [sound1301 B _hB _hF, sound3309 B _hB _hF] at h
  norm_num [nodeValue4624, nodeValue1301, nodeValue3309, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4625 node4625Labels = Sparse.eval nodeValue4625 (mixedVector B) := by
  have h := singleton4625 B _hB
  rw [sound1304 B _hB _hF, sound3310 B _hB _hF] at h
  norm_num [nodeValue4625, nodeValue1304, nodeValue3310, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5078 node5078Labels = Sparse.eval nodeValue5078 (mixedVector B) := by
  have h := singleton5078 B _hB
  rw [sound2485 B _hB _hF, sound3481 B _hB _hF] at h
  norm_num [nodeValue5078, nodeValue2485, nodeValue3481, Sparse.eval] at h ⊢
  linarith only [h]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5293 node5293Labels = Sparse.eval nodeValue5293 (mixedVector B) := by
  have h := singleton5293 B _hB
  rw [sound2767 B _hB _hF, sound3627 B _hB _hF] at h
  norm_num [nodeValue5293, nodeValue2767, nodeValue3627, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5296 node5296Labels = Sparse.eval nodeValue5296 (mixedVector B) := by
  have h := singleton5296 B _hB
  rw [sound2770 B _hB _hF, sound3634 B _hB _hF] at h
  norm_num [nodeValue5296, nodeValue2770, nodeValue3634, Sparse.eval] at h ⊢
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

theorem sourceEq1291 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1291 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1291 + difference 0 1) (sourceB1291 + difference 1 0) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1291 + difference 0 1) (sourceB1291 + difference 1 0) sourceC1291) = raw7832 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw7832; decide +kernel
    rw [ha]
    exact (canonical7832 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1291 + difference 0 2) (sourceB1291 + difference 2 0) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1291 + difference 0 2) (sourceB1291 + difference 2 0) sourceC1291) = raw7833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw7833; decide +kernel
    rw [ha]
    exact (canonical7833 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1291 + difference 0 3) (sourceB1291 + difference 3 0) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA1291 + difference 0 3) (sourceB1291 + difference 3 0) sourceC1291) = raw7834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw7834; decide +kernel
    rw [ha]
    exact (canonical7834 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1291 + difference 0 4) (sourceB1291 + difference 4 0) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA1291 + difference 0 4) (sourceB1291 + difference 4 0) sourceC1291) = raw7835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw7835; decide +kernel
    rw [ha]
    exact (canonical7835 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1291 + difference 0 5) (sourceB1291 + difference 5 0) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1291 + difference 0 5) (sourceB1291 + difference 5 0) sourceC1291) = raw15022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw15022; decide +kernel
    rw [ha]
    exact (canonical15022 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1291 + difference 1 0) (sourceB1291 + difference 0 1) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4144) := by
    have ha : (tripleCharges (sourceA1291 + difference 1 0) (sourceB1291 + difference 0 1) sourceC1291) = raw20749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20749; decide +kernel
    rw [ha]
    exact (canonical20749 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1291 + difference 1 2) (sourceB1291 + difference 2 1) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4523) := by
    have ha : (tripleCharges (sourceA1291 + difference 1 2) (sourceB1291 + difference 2 1) sourceC1291) = raw20750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20750; decide +kernel
    rw [ha]
    exact (canonical20750 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1291 + difference 1 3) (sourceB1291 + difference 3 1) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4517) := by
    have ha : (tripleCharges (sourceA1291 + difference 1 3) (sourceB1291 + difference 3 1) sourceC1291) = raw20751 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20751; decide +kernel
    rw [ha]
    exact (canonical20751 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1291 + difference 1 4) (sourceB1291 + difference 4 1) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1291 + difference 1 4) (sourceB1291 + difference 4 1) sourceC1291) = raw20752 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20752; decide +kernel
    rw [ha]
    exact (canonical20752 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1291 + difference 1 5) (sourceB1291 + difference 5 1) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1291 + difference 1 5) (sourceB1291 + difference 5 1) sourceC1291) = raw7811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw7811; decide +kernel
    rw [ha]
    exact (canonical7811 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1291 + difference 2 0) (sourceB1291 + difference 0 2) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4144) := by
    have ha : (tripleCharges (sourceA1291 + difference 2 0) (sourceB1291 + difference 0 2) sourceC1291) = raw20753 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20753; decide +kernel
    rw [ha]
    exact (canonical20753 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1291 + difference 2 1) (sourceB1291 + difference 1 2) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4523) := by
    have ha : (tripleCharges (sourceA1291 + difference 2 1) (sourceB1291 + difference 1 2) sourceC1291) = raw20754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20754; decide +kernel
    rw [ha]
    exact (canonical20754 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1291 + difference 2 3) (sourceB1291 + difference 3 2) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4517) := by
    have ha : (tripleCharges (sourceA1291 + difference 2 3) (sourceB1291 + difference 3 2) sourceC1291) = raw20755 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20755; decide +kernel
    rw [ha]
    exact (canonical20755 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1291 + difference 2 4) (sourceB1291 + difference 4 2) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1291 + difference 2 4) (sourceB1291 + difference 4 2) sourceC1291) = raw20756 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20756; decide +kernel
    rw [ha]
    exact (canonical20756 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1291 + difference 2 5) (sourceB1291 + difference 5 2) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1291 + difference 2 5) (sourceB1291 + difference 5 2) sourceC1291) = raw7816 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw7816; decide +kernel
    rw [ha]
    exact (canonical7816 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1291 + difference 3 0) (sourceB1291 + difference 0 3) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4177) := by
    have ha : (tripleCharges (sourceA1291 + difference 3 0) (sourceB1291 + difference 0 3) sourceC1291) = raw20757 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20757; decide +kernel
    rw [ha]
    exact (canonical20757 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1291 + difference 3 1) (sourceB1291 + difference 1 3) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1291 + difference 3 1) (sourceB1291 + difference 1 3) sourceC1291) = raw20758 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20758; decide +kernel
    rw [ha]
    exact (canonical20758 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1291 + difference 3 2) (sourceB1291 + difference 2 3) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1291 + difference 3 2) (sourceB1291 + difference 2 3) sourceC1291) = raw20759 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20759; decide +kernel
    rw [ha]
    exact (canonical20759 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1291 + difference 3 4) (sourceB1291 + difference 4 3) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1291 + difference 3 4) (sourceB1291 + difference 4 3) sourceC1291) = raw20760 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20760; decide +kernel
    rw [ha]
    exact (canonical20760 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1291 + difference 3 5) (sourceB1291 + difference 5 3) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1291 + difference 3 5) (sourceB1291 + difference 5 3) sourceC1291) = raw7821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw7821; decide +kernel
    rw [ha]
    exact (canonical7821 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1291 + difference 4 0) (sourceB1291 + difference 0 4) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4148) := by
    have ha : (tripleCharges (sourceA1291 + difference 4 0) (sourceB1291 + difference 0 4) sourceC1291) = raw20761 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20761; decide +kernel
    rw [ha]
    exact (canonical20761 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1291 + difference 4 1) (sourceB1291 + difference 1 4) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4526) := by
    have ha : (tripleCharges (sourceA1291 + difference 4 1) (sourceB1291 + difference 1 4) sourceC1291) = raw20762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20762; decide +kernel
    rw [ha]
    exact (canonical20762 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1291 + difference 4 2) (sourceB1291 + difference 2 4) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4526) := by
    have ha : (tripleCharges (sourceA1291 + difference 4 2) (sourceB1291 + difference 2 4) sourceC1291) = raw20763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20763; decide +kernel
    rw [ha]
    exact (canonical20763 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1291 + difference 4 3) (sourceB1291 + difference 3 4) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4520) := by
    have ha : (tripleCharges (sourceA1291 + difference 4 3) (sourceB1291 + difference 3 4) sourceC1291) = raw20764 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20764; decide +kernel
    rw [ha]
    exact (canonical20764 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1291 + difference 4 5) (sourceB1291 + difference 5 4) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1291 + difference 4 5) (sourceB1291 + difference 5 4) sourceC1291) = raw7826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw7826; decide +kernel
    rw [ha]
    exact (canonical7826 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1291 + difference 5 0) (sourceB1291 + difference 0 5) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4146) := by
    have ha : (tripleCharges (sourceA1291 + difference 5 0) (sourceB1291 + difference 0 5) sourceC1291) = raw20765 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20765; decide +kernel
    rw [ha]
    exact (canonical20765 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1291 + difference 5 1) (sourceB1291 + difference 1 5) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4293) := by
    have ha : (tripleCharges (sourceA1291 + difference 5 1) (sourceB1291 + difference 1 5) sourceC1291) = raw20766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20766; decide +kernel
    rw [ha]
    exact (canonical20766 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1291 + difference 5 2) (sourceB1291 + difference 2 5) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4293) := by
    have ha : (tripleCharges (sourceA1291 + difference 5 2) (sourceB1291 + difference 2 5) sourceC1291) = raw20767 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20767; decide +kernel
    rw [ha]
    exact (canonical20767 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1291 + difference 5 3) (sourceB1291 + difference 3 5) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4315) := by
    have ha : (tripleCharges (sourceA1291 + difference 5 3) (sourceB1291 + difference 3 5) sourceC1291) = raw20768 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20768; decide +kernel
    rw [ha]
    exact (canonical20768 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1291 + difference 5 4) (sourceB1291 + difference 4 5) sourceC1291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1291 + difference 5 4) (sourceB1291 + difference 4 5) sourceC1291) = raw20769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1291 sourceB1291 sourceC1291 difference raw20769; decide +kernel
    rw [ha]
    exact (canonical20769 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1291 sourceB1291 sourceC1291
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1291, Integer.Sparse.eval]
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

theorem reindexCheck1120 : Integer.Sparse.reindex keyMap MixedData.row1120 = numericRow1120 := by decide +kernel

theorem numericCheck1120 (x : Master → ℝ) : Integer.Sparse.eval numericRow1120 x =
    (4320 : ℝ) * reducedSource1120 x := by
  norm_num [numericRow1120, reducedSource1120, Integer.Sparse.eval, Sparse.eval, nodeValue4144, nodeValue4146, nodeValue4148, nodeValue4177, nodeValue4293, nodeValue4315, nodeValue4468, nodeValue4517, nodeValue4520, nodeValue4523, nodeValue4526, nodeValue4546, nodeValue4606, nodeValue4608, nodeValue4612, nodeValue4624, nodeValue4625, nodeValue5078, nodeValue5109, nodeValue5293, nodeValue5296]
  ring

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

theorem reducedZero1120 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1120 (mixedVector B) = 0 := by
  have h4144 : mixedVector B (Sum.inr 4144) = Sparse.eval nodeValue4144 (mixedVector B) := by
    change mixedMoment B node4144 node4144Labels = _
    exact sound4144 B hB hF
  have h4146 : mixedVector B (Sum.inr 4146) = Sparse.eval nodeValue4146 (mixedVector B) := by
    change mixedMoment B node4146 node4146Labels = _
    exact sound4146 B hB hF
  have h4148 : mixedVector B (Sum.inr 4148) = Sparse.eval nodeValue4148 (mixedVector B) := by
    change mixedMoment B node4148 node4148Labels = _
    exact sound4148 B hB hF
  have h4177 : mixedVector B (Sum.inr 4177) = Sparse.eval nodeValue4177 (mixedVector B) := by
    change mixedMoment B node4177 node4177Labels = _
    exact sound4177 B hB hF
  have h4293 : mixedVector B (Sum.inr 4293) = Sparse.eval nodeValue4293 (mixedVector B) := by
    change mixedMoment B node4293 node4293Labels = _
    exact sound4293 B hB hF
  have h4315 : mixedVector B (Sum.inr 4315) = Sparse.eval nodeValue4315 (mixedVector B) := by
    change mixedMoment B node4315 node4315Labels = _
    exact sound4315 B hB hF
  have h4468 : mixedVector B (Sum.inr 4468) = Sparse.eval nodeValue4468 (mixedVector B) := by
    change mixedMoment B node4468 node4468Labels = _
    exact sound4468 B hB hF
  have h4517 : mixedVector B (Sum.inr 4517) = Sparse.eval nodeValue4517 (mixedVector B) := by
    change mixedMoment B node4517 node4517Labels = _
    exact sound4517 B hB hF
  have h4520 : mixedVector B (Sum.inr 4520) = Sparse.eval nodeValue4520 (mixedVector B) := by
    change mixedMoment B node4520 node4520Labels = _
    exact sound4520 B hB hF
  have h4523 : mixedVector B (Sum.inr 4523) = Sparse.eval nodeValue4523 (mixedVector B) := by
    change mixedMoment B node4523 node4523Labels = _
    exact sound4523 B hB hF
  have h4526 : mixedVector B (Sum.inr 4526) = Sparse.eval nodeValue4526 (mixedVector B) := by
    change mixedMoment B node4526 node4526Labels = _
    exact sound4526 B hB hF
  have h4546 : mixedVector B (Sum.inr 4546) = Sparse.eval nodeValue4546 (mixedVector B) := by
    change mixedMoment B node4546 node4546Labels = _
    exact sound4546 B hB hF
  have h4606 : mixedVector B (Sum.inr 4606) = Sparse.eval nodeValue4606 (mixedVector B) := by
    change mixedMoment B node4606 node4606Labels = _
    exact sound4606 B hB hF
  have h4608 : mixedVector B (Sum.inr 4608) = Sparse.eval nodeValue4608 (mixedVector B) := by
    change mixedMoment B node4608 node4608Labels = _
    exact sound4608 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4624 : mixedVector B (Sum.inr 4624) = Sparse.eval nodeValue4624 (mixedVector B) := by
    change mixedMoment B node4624 node4624Labels = _
    exact sound4624 B hB hF
  have h4625 : mixedVector B (Sum.inr 4625) = Sparse.eval nodeValue4625 (mixedVector B) := by
    change mixedMoment B node4625 node4625Labels = _
    exact sound4625 B hB hF
  have h5078 : mixedVector B (Sum.inr 5078) = Sparse.eval nodeValue5078 (mixedVector B) := by
    change mixedMoment B node5078 node5078Labels = _
    exact sound5078 B hB hF
  have h5109 : mixedVector B (Sum.inr 5109) = Sparse.eval nodeValue5109 (mixedVector B) := by
    change mixedMoment B node5109 node5109Labels = _
    exact sound5109 B hB hF
  have h5293 : mixedVector B (Sum.inr 5293) = Sparse.eval nodeValue5293 (mixedVector B) := by
    change mixedMoment B node5293 node5293Labels = _
    exact sound5293 B hB hF
  have h5296 : mixedVector B (Sum.inr 5296) = Sparse.eval nodeValue5296 (mixedVector B) := by
    change mixedMoment B node5296 node5296Labels = _
    exact sound5296 B hB hF
  simpa only [sourceForm1291, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4144, h4146, h4148, h4177, h4293, h4315, h4468, h4517, h4520, h4523, h4526, h4546, h4606, h4608, h4612, h4624, h4625, h5078, h5109, h5293, h5296, reducedSource1120] using sourceEq1291 B hB

theorem rowSound1120_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1120 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1120, numericCheck1120, reducedZero1120 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e_oai
