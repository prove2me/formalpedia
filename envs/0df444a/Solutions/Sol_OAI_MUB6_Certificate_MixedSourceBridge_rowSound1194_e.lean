-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T20:11:31.411588+00:00
-- url     : https://prove2.me/submissions/9cabb78f-aaaa-41df-9782-91d6bac2adb1

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E103
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
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

theorem canonical1302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1302 raw1302Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw1302 raw1302Labels = mixedMoment B raw1302step0 raw1302step0Labels := by
      have ha : raw1302step0 = (fun i j => raw1302 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1302step0 raw1302; decide +kernel
      have hl : raw1302step0Labels = raw1302Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1302 raw1302Labels permutation8 permutation4
    mixedMoment B raw1302step0 raw1302step0Labels = mixedMoment B raw1302step1 raw1302step1Labels := by
      have ha : raw1302step1 = raw1302step0 := by apply Matrix.ext; unfold raw1302step1 raw1302step0; decide +kernel
      have hl : raw1302step0Labels = labelEmbedding7 ∘ raw1302step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1302step0 raw1302step0Labels raw1302step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

theorem canonical1303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1303 raw1303Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw1303 raw1303Labels = mixedMoment B raw1303step0 raw1303step0Labels := by
      have ha : raw1303step0 = (fun i j => raw1303 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1303step0 raw1303; decide +kernel
      have hl : raw1303step0Labels = raw1303Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1303 raw1303Labels permutation8 permutation4
    _ = mixedMoment B node1087 node1087Labels := by rfl

theorem canonical1304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1304 raw1304Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw1304 raw1304Labels = mixedMoment B raw1304step0 raw1304step0Labels := by
      have ha : raw1304step0 = (fun i j => raw1304 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1304step0 raw1304; decide +kernel
      have hl : raw1304step0Labels = raw1304Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1304 raw1304Labels permutation12 permutation6
    mixedMoment B raw1304step0 raw1304step0Labels = mixedMoment B raw1304step1 raw1304step1Labels := by
      have ha : raw1304step1 = -raw1304step0 := by apply Matrix.ext; change ∀ i j, raw1304step1 i j = -(raw1304step0 i j); unfold raw1304step1 raw1304step0; decide +kernel
      have hl : raw1304step1Labels = raw1304step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1304step1 raw1304step1Labels = mixedMoment B raw1304step2 raw1304step2Labels := by
      have ha : raw1304step2 = raw1304step1 := by apply Matrix.ext; unfold raw1304step2 raw1304step1; decide +kernel
      have hl : raw1304step1Labels = labelEmbedding1 ∘ raw1304step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1304step1 raw1304step1Labels raw1304step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1739 node1739Labels := by rfl

theorem canonical1308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1308 raw1308Labels = mixedMoment B node4510 node4510Labels := by
  calc
    mixedMoment B raw1308 raw1308Labels = mixedMoment B raw1308step0 raw1308step0Labels := by
      have ha : raw1308step0 = (fun i j => raw1308 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1308step0 raw1308; decide +kernel
      have hl : raw1308step0Labels = raw1308Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1308 raw1308Labels permutation2 permutation4
    mixedMoment B raw1308step0 raw1308step0Labels = mixedMoment B raw1308step1 raw1308step1Labels := by
      have ha : raw1308step1 = raw1308step0 := by apply Matrix.ext; unfold raw1308step1 raw1308step0; decide +kernel
      have hl : raw1308step0Labels = labelEmbedding7 ∘ raw1308step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1308step0 raw1308step0Labels raw1308step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4510 node4510Labels := by rfl

theorem canonical1309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1309 raw1309Labels = mixedMoment B node1094 node1094Labels := by
  calc
    mixedMoment B raw1309 raw1309Labels = mixedMoment B raw1309step0 raw1309step0Labels := by
      have ha : raw1309step0 = (fun i j => raw1309 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1309step0 raw1309; decide +kernel
      have hl : raw1309step0Labels = raw1309Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1309 raw1309Labels permutation2 permutation4
    _ = mixedMoment B node1094 node1094Labels := by rfl

theorem canonical1310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1310 raw1310Labels = mixedMoment B node1741 node1741Labels := by
  calc
    mixedMoment B raw1310 raw1310Labels = mixedMoment B raw1310step0 raw1310step0Labels := by
      have ha : raw1310step0 = (fun i j => raw1310 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1310step0 raw1310; decide +kernel
      have hl : raw1310step0Labels = raw1310Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1310 raw1310Labels permutation2 permutation6
    mixedMoment B raw1310step0 raw1310step0Labels = mixedMoment B raw1310step1 raw1310step1Labels := by
      have ha : raw1310step1 = -raw1310step0 := by apply Matrix.ext; change ∀ i j, raw1310step1 i j = -(raw1310step0 i j); unfold raw1310step1 raw1310step0; decide +kernel
      have hl : raw1310step1Labels = raw1310step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1310step1 raw1310step1Labels = mixedMoment B raw1310step2 raw1310step2Labels := by
      have ha : raw1310step2 = raw1310step1 := by apply Matrix.ext; unfold raw1310step2 raw1310step1; decide +kernel
      have hl : raw1310step1Labels = labelEmbedding1 ∘ raw1310step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1310step1 raw1310step1Labels raw1310step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1741 node1741Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical169
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21690 raw21690Labels = mixedMoment B node4128 node4128Labels := by
  calc
    mixedMoment B raw21690 raw21690Labels = mixedMoment B raw21690step0 raw21690step0Labels := by
      have hz : ∀ j, raw21690 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21690step0 = (fun i j => raw21690 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21690step0 raw21690; decide +kernel
      have hl : raw21690step0Labels = raw21690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21690 raw21690Labels permutation434 hz
    mixedMoment B raw21690step0 raw21690step0Labels = mixedMoment B raw21690step1 raw21690step1Labels := by
      have hz : ∀ j, raw21690step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21690step1 = (fun i j => raw21690step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21690step1 raw21690step0; decide +kernel
      have hl : raw21690step1Labels = raw21690step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21690step0 raw21690step0Labels permutation80 hz
    mixedMoment B raw21690step1 raw21690step1Labels = mixedMoment B raw21690step2 raw21690step2Labels := by
      have ha : raw21690step2 = (fun i j => raw21690step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21690step2 raw21690step1; decide +kernel
      have hl : raw21690step2Labels = raw21690step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21690step1 raw21690step1Labels permutation8 permutation3
    mixedMoment B raw21690step2 raw21690step2Labels = mixedMoment B raw21690step3 raw21690step3Labels := by
      have ha : raw21690step3 = raw21690step2 := by apply Matrix.ext; unfold raw21690step3 raw21690step2; decide +kernel
      have hl : raw21690step2Labels = labelEmbedding6 ∘ raw21690step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21690step2 raw21690step2Labels raw21690step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4128 node4128Labels := by rfl

theorem canonical21691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21691 raw21691Labels = mixedMoment B node4309 node4309Labels := by
  calc
    mixedMoment B raw21691 raw21691Labels = mixedMoment B raw21691step0 raw21691step0Labels := by
      have hz : ∀ j, raw21691 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21691step0 = (fun i j => raw21691 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21691step0 raw21691; decide +kernel
      have hl : raw21691step0Labels = raw21691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21691 raw21691Labels permutation434 hz
    mixedMoment B raw21691step0 raw21691step0Labels = mixedMoment B raw21691step1 raw21691step1Labels := by
      have ha : raw21691step1 = (fun i j => raw21691step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21691step1 raw21691step0; decide +kernel
      have hl : raw21691step1Labels = raw21691step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21691step0 raw21691step0Labels permutation38 permutation3
    mixedMoment B raw21691step1 raw21691step1Labels = mixedMoment B raw21691step2 raw21691step2Labels := by
      have ha : raw21691step2 = raw21691step1 := by apply Matrix.ext; unfold raw21691step2 raw21691step1; decide +kernel
      have hl : raw21691step1Labels = labelEmbedding6 ∘ raw21691step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21691step1 raw21691step1Labels raw21691step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4309 node4309Labels := by rfl

theorem canonical21692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21692 raw21692Labels = mixedMoment B node4309 node4309Labels := by
  calc
    mixedMoment B raw21692 raw21692Labels = mixedMoment B raw21692step0 raw21692step0Labels := by
      have hz : ∀ j, raw21692 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21692step0 = (fun i j => raw21692 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21692step0 raw21692; decide +kernel
      have hl : raw21692step0Labels = raw21692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21692 raw21692Labels permutation346 hz
    mixedMoment B raw21692step0 raw21692step0Labels = mixedMoment B raw21692step1 raw21692step1Labels := by
      have ha : raw21692step1 = (fun i j => raw21692step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21692step1 raw21692step0; decide +kernel
      have hl : raw21692step1Labels = raw21692step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21692step0 raw21692step0Labels permutation38 permutation3
    mixedMoment B raw21692step1 raw21692step1Labels = mixedMoment B raw21692step2 raw21692step2Labels := by
      have ha : raw21692step2 = raw21692step1 := by apply Matrix.ext; unfold raw21692step2 raw21692step1; decide +kernel
      have hl : raw21692step1Labels = labelEmbedding6 ∘ raw21692step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21692step1 raw21692step1Labels raw21692step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4309 node4309Labels := by rfl

theorem canonical21693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21693 raw21693Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw21693 raw21693Labels = mixedMoment B raw21693step0 raw21693step0Labels := by
      have hz : ∀ j, raw21693 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21693step0 = (fun i j => raw21693 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21693step0 raw21693; decide +kernel
      have hl : raw21693step0Labels = raw21693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21693 raw21693Labels permutation434 hz
    mixedMoment B raw21693step0 raw21693step0Labels = mixedMoment B raw21693step1 raw21693step1Labels := by
      have hz : ∀ j, raw21693step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21693step1 = (fun i j => raw21693step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21693step1 raw21693step0; decide +kernel
      have hl : raw21693step1Labels = raw21693step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21693step0 raw21693step0Labels permutation80 hz
    mixedMoment B raw21693step1 raw21693step1Labels = mixedMoment B raw21693step2 raw21693step2Labels := by
      have ha : raw21693step2 = (fun i j => raw21693step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21693step2 raw21693step1; decide +kernel
      have hl : raw21693step2Labels = raw21693step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21693step1 raw21693step1Labels permutation10 permutation3
    mixedMoment B raw21693step2 raw21693step2Labels = mixedMoment B raw21693step3 raw21693step3Labels := by
      have ha : raw21693step3 = raw21693step2 := by apply Matrix.ext; unfold raw21693step3 raw21693step2; decide +kernel
      have hl : raw21693step2Labels = labelEmbedding6 ∘ raw21693step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21693step2 raw21693step2Labels raw21693step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

theorem canonical21694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21694 raw21694Labels = mixedMoment B node4128 node4128Labels := by
  calc
    mixedMoment B raw21694 raw21694Labels = mixedMoment B raw21694step0 raw21694step0Labels := by
      have hz : ∀ j, raw21694 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21694step0 = (fun i j => raw21694 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21694step0 raw21694; decide +kernel
      have hl : raw21694step0Labels = raw21694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21694 raw21694Labels permutation434 hz
    mixedMoment B raw21694step0 raw21694step0Labels = mixedMoment B raw21694step1 raw21694step1Labels := by
      have hz : ∀ j, raw21694step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21694step1 = (fun i j => raw21694step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21694step1 raw21694step0; decide +kernel
      have hl : raw21694step1Labels = raw21694step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21694step0 raw21694step0Labels permutation56 hz
    mixedMoment B raw21694step1 raw21694step1Labels = mixedMoment B raw21694step2 raw21694step2Labels := by
      have ha : raw21694step2 = (fun i j => raw21694step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21694step2 raw21694step1; decide +kernel
      have hl : raw21694step2Labels = raw21694step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21694step1 raw21694step1Labels permutation8 permutation3
    mixedMoment B raw21694step2 raw21694step2Labels = mixedMoment B raw21694step3 raw21694step3Labels := by
      have ha : raw21694step3 = raw21694step2 := by apply Matrix.ext; unfold raw21694step3 raw21694step2; decide +kernel
      have hl : raw21694step2Labels = labelEmbedding6 ∘ raw21694step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21694step2 raw21694step2Labels raw21694step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4128 node4128Labels := by rfl

theorem canonical21695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21695 raw21695Labels = mixedMoment B node4309 node4309Labels := by
  calc
    mixedMoment B raw21695 raw21695Labels = mixedMoment B raw21695step0 raw21695step0Labels := by
      have hz : ∀ j, raw21695 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21695step0 = (fun i j => raw21695 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21695step0 raw21695; decide +kernel
      have hl : raw21695step0Labels = raw21695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21695 raw21695Labels permutation434 hz
    mixedMoment B raw21695step0 raw21695step0Labels = mixedMoment B raw21695step1 raw21695step1Labels := by
      have ha : raw21695step1 = (fun i j => raw21695step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21695step1 raw21695step0; decide +kernel
      have hl : raw21695step1Labels = raw21695step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21695step0 raw21695step0Labels permutation32 permutation3
    mixedMoment B raw21695step1 raw21695step1Labels = mixedMoment B raw21695step2 raw21695step2Labels := by
      have ha : raw21695step2 = raw21695step1 := by apply Matrix.ext; unfold raw21695step2 raw21695step1; decide +kernel
      have hl : raw21695step1Labels = labelEmbedding6 ∘ raw21695step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21695step1 raw21695step1Labels raw21695step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4309 node4309Labels := by rfl

theorem canonical21696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21696 raw21696Labels = mixedMoment B node4309 node4309Labels := by
  calc
    mixedMoment B raw21696 raw21696Labels = mixedMoment B raw21696step0 raw21696step0Labels := by
      have hz : ∀ j, raw21696 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21696step0 = (fun i j => raw21696 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21696step0 raw21696; decide +kernel
      have hl : raw21696step0Labels = raw21696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21696 raw21696Labels permutation265 hz
    mixedMoment B raw21696step0 raw21696step0Labels = mixedMoment B raw21696step1 raw21696step1Labels := by
      have ha : raw21696step1 = (fun i j => raw21696step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21696step1 raw21696step0; decide +kernel
      have hl : raw21696step1Labels = raw21696step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21696step0 raw21696step0Labels permutation38 permutation3
    mixedMoment B raw21696step1 raw21696step1Labels = mixedMoment B raw21696step2 raw21696step2Labels := by
      have ha : raw21696step2 = raw21696step1 := by apply Matrix.ext; unfold raw21696step2 raw21696step1; decide +kernel
      have hl : raw21696step1Labels = labelEmbedding6 ∘ raw21696step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21696step1 raw21696step1Labels raw21696step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4309 node4309Labels := by rfl

theorem canonical21697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21697 raw21697Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw21697 raw21697Labels = mixedMoment B raw21697step0 raw21697step0Labels := by
      have hz : ∀ j, raw21697 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21697step0 = (fun i j => raw21697 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21697step0 raw21697; decide +kernel
      have hl : raw21697step0Labels = raw21697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21697 raw21697Labels permutation434 hz
    mixedMoment B raw21697step0 raw21697step0Labels = mixedMoment B raw21697step1 raw21697step1Labels := by
      have hz : ∀ j, raw21697step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21697step1 = (fun i j => raw21697step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21697step1 raw21697step0; decide +kernel
      have hl : raw21697step1Labels = raw21697step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21697step0 raw21697step0Labels permutation56 hz
    mixedMoment B raw21697step1 raw21697step1Labels = mixedMoment B raw21697step2 raw21697step2Labels := by
      have ha : raw21697step2 = (fun i j => raw21697step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21697step2 raw21697step1; decide +kernel
      have hl : raw21697step2Labels = raw21697step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21697step1 raw21697step1Labels permutation10 permutation3
    mixedMoment B raw21697step2 raw21697step2Labels = mixedMoment B raw21697step3 raw21697step3Labels := by
      have ha : raw21697step3 = raw21697step2 := by apply Matrix.ext; unfold raw21697step3 raw21697step2; decide +kernel
      have hl : raw21697step2Labels = labelEmbedding6 ∘ raw21697step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21697step2 raw21697step2Labels raw21697step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

theorem canonical21698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21698 raw21698Labels = mixedMoment B node4128 node4128Labels := by
  calc
    mixedMoment B raw21698 raw21698Labels = mixedMoment B raw21698step0 raw21698step0Labels := by
      have hz : ∀ j, raw21698 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21698step0 = (fun i j => raw21698 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21698step0 raw21698; decide +kernel
      have hl : raw21698step0Labels = raw21698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21698 raw21698Labels permutation346 hz
    mixedMoment B raw21698step0 raw21698step0Labels = mixedMoment B raw21698step1 raw21698step1Labels := by
      have hz : ∀ j, raw21698step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21698step1 = (fun i j => raw21698step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21698step1 raw21698step0; decide +kernel
      have hl : raw21698step1Labels = raw21698step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21698step0 raw21698step0Labels permutation56 hz
    mixedMoment B raw21698step1 raw21698step1Labels = mixedMoment B raw21698step2 raw21698step2Labels := by
      have ha : raw21698step2 = (fun i j => raw21698step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21698step2 raw21698step1; decide +kernel
      have hl : raw21698step2Labels = raw21698step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21698step1 raw21698step1Labels permutation8 permutation3
    mixedMoment B raw21698step2 raw21698step2Labels = mixedMoment B raw21698step3 raw21698step3Labels := by
      have ha : raw21698step3 = raw21698step2 := by apply Matrix.ext; unfold raw21698step3 raw21698step2; decide +kernel
      have hl : raw21698step2Labels = labelEmbedding6 ∘ raw21698step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21698step2 raw21698step2Labels raw21698step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4128 node4128Labels := by rfl

theorem canonical21699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21699 raw21699Labels = mixedMoment B node4309 node4309Labels := by
  calc
    mixedMoment B raw21699 raw21699Labels = mixedMoment B raw21699step0 raw21699step0Labels := by
      have hz : ∀ j, raw21699 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21699step0 = (fun i j => raw21699 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21699step0 raw21699; decide +kernel
      have hl : raw21699step0Labels = raw21699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21699 raw21699Labels permutation346 hz
    mixedMoment B raw21699step0 raw21699step0Labels = mixedMoment B raw21699step1 raw21699step1Labels := by
      have ha : raw21699step1 = (fun i j => raw21699step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21699step1 raw21699step0; decide +kernel
      have hl : raw21699step1Labels = raw21699step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21699step0 raw21699step0Labels permutation32 permutation3
    mixedMoment B raw21699step1 raw21699step1Labels = mixedMoment B raw21699step2 raw21699step2Labels := by
      have ha : raw21699step2 = raw21699step1 := by apply Matrix.ext; unfold raw21699step2 raw21699step1; decide +kernel
      have hl : raw21699step1Labels = labelEmbedding6 ∘ raw21699step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21699step1 raw21699step1Labels raw21699step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4309 node4309Labels := by rfl

theorem canonical21700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21700 raw21700Labels = mixedMoment B node4309 node4309Labels := by
  calc
    mixedMoment B raw21700 raw21700Labels = mixedMoment B raw21700step0 raw21700step0Labels := by
      have hz : ∀ j, raw21700 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21700step0 = (fun i j => raw21700 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21700step0 raw21700; decide +kernel
      have hl : raw21700step0Labels = raw21700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21700 raw21700Labels permutation265 hz
    mixedMoment B raw21700step0 raw21700step0Labels = mixedMoment B raw21700step1 raw21700step1Labels := by
      have ha : raw21700step1 = (fun i j => raw21700step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21700step1 raw21700step0; decide +kernel
      have hl : raw21700step1Labels = raw21700step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21700step0 raw21700step0Labels permutation32 permutation3
    mixedMoment B raw21700step1 raw21700step1Labels = mixedMoment B raw21700step2 raw21700step2Labels := by
      have ha : raw21700step2 = raw21700step1 := by apply Matrix.ext; unfold raw21700step2 raw21700step1; decide +kernel
      have hl : raw21700step1Labels = labelEmbedding6 ∘ raw21700step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21700step1 raw21700step1Labels raw21700step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4309 node4309Labels := by rfl

theorem canonical21701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21701 raw21701Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw21701 raw21701Labels = mixedMoment B raw21701step0 raw21701step0Labels := by
      have hz : ∀ j, raw21701 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21701step0 = (fun i j => raw21701 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21701step0 raw21701; decide +kernel
      have hl : raw21701step0Labels = raw21701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21701 raw21701Labels permutation346 hz
    mixedMoment B raw21701step0 raw21701step0Labels = mixedMoment B raw21701step1 raw21701step1Labels := by
      have hz : ∀ j, raw21701step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21701step1 = (fun i j => raw21701step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21701step1 raw21701step0; decide +kernel
      have hl : raw21701step1Labels = raw21701step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21701step0 raw21701step0Labels permutation56 hz
    mixedMoment B raw21701step1 raw21701step1Labels = mixedMoment B raw21701step2 raw21701step2Labels := by
      have ha : raw21701step2 = (fun i j => raw21701step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21701step2 raw21701step1; decide +kernel
      have hl : raw21701step2Labels = raw21701step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21701step1 raw21701step1Labels permutation10 permutation3
    mixedMoment B raw21701step2 raw21701step2Labels = mixedMoment B raw21701step3 raw21701step3Labels := by
      have ha : raw21701step3 = raw21701step2 := by apply Matrix.ext; unfold raw21701step3 raw21701step2; decide +kernel
      have hl : raw21701step2Labels = labelEmbedding6 ∘ raw21701step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21701step2 raw21701step2Labels raw21701step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

theorem canonical21702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21702 raw21702Labels = mixedMoment B node4138 node4138Labels := by
  calc
    mixedMoment B raw21702 raw21702Labels = mixedMoment B raw21702step0 raw21702step0Labels := by
      have hz : ∀ j, raw21702 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21702step0 = (fun i j => raw21702 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21702step0 raw21702; decide +kernel
      have hl : raw21702step0Labels = raw21702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21702 raw21702Labels permutation434 hz
    mixedMoment B raw21702step0 raw21702step0Labels = mixedMoment B raw21702step1 raw21702step1Labels := by
      have hz : ∀ j, raw21702step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21702step1 = (fun i j => raw21702step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21702step1 raw21702step0; decide +kernel
      have hl : raw21702step1Labels = raw21702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21702step0 raw21702step0Labels permutation80 hz
    mixedMoment B raw21702step1 raw21702step1Labels = mixedMoment B raw21702step2 raw21702step2Labels := by
      have hz : ∀ j, raw21702step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21702step2 = (fun i j => raw21702step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21702step2 raw21702step1; decide +kernel
      have hl : raw21702step2Labels = raw21702step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21702step1 raw21702step1Labels permutation14 hz
    mixedMoment B raw21702step2 raw21702step2Labels = mixedMoment B raw21702step3 raw21702step3Labels := by
      have ha : raw21702step3 = (fun i j => raw21702step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21702step3 raw21702step2; decide +kernel
      have hl : raw21702step3Labels = raw21702step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21702step2 raw21702step2Labels permutation2 permutation3
    mixedMoment B raw21702step3 raw21702step3Labels = mixedMoment B raw21702step4 raw21702step4Labels := by
      have ha : raw21702step4 = raw21702step3 := by apply Matrix.ext; unfold raw21702step4 raw21702step3; decide +kernel
      have hl : raw21702step3Labels = labelEmbedding6 ∘ raw21702step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21702step3 raw21702step3Labels raw21702step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4138 node4138Labels := by rfl

theorem canonical21703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21703 raw21703Labels = mixedMoment B node4319 node4319Labels := by
  calc
    mixedMoment B raw21703 raw21703Labels = mixedMoment B raw21703step0 raw21703step0Labels := by
      have hz : ∀ j, raw21703 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21703step0 = (fun i j => raw21703 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21703step0 raw21703; decide +kernel
      have hl : raw21703step0Labels = raw21703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21703 raw21703Labels permutation434 hz
    mixedMoment B raw21703step0 raw21703step0Labels = mixedMoment B raw21703step1 raw21703step1Labels := by
      have hz : ∀ j, raw21703step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21703step1 = (fun i j => raw21703step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21703step1 raw21703step0; decide +kernel
      have hl : raw21703step1Labels = raw21703step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21703step0 raw21703step0Labels permutation80 hz
    mixedMoment B raw21703step1 raw21703step1Labels = mixedMoment B raw21703step2 raw21703step2Labels := by
      have ha : raw21703step2 = (fun i j => raw21703step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21703step2 raw21703step1; decide +kernel
      have hl : raw21703step2Labels = raw21703step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21703step1 raw21703step1Labels permutation8 permutation3
    mixedMoment B raw21703step2 raw21703step2Labels = mixedMoment B raw21703step3 raw21703step3Labels := by
      have ha : raw21703step3 = raw21703step2 := by apply Matrix.ext; unfold raw21703step3 raw21703step2; decide +kernel
      have hl : raw21703step2Labels = labelEmbedding6 ∘ raw21703step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21703step2 raw21703step2Labels raw21703step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4319 node4319Labels := by rfl

theorem canonical21704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21704 raw21704Labels = mixedMoment B node4319 node4319Labels := by
  calc
    mixedMoment B raw21704 raw21704Labels = mixedMoment B raw21704step0 raw21704step0Labels := by
      have hz : ∀ j, raw21704 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21704step0 = (fun i j => raw21704 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21704step0 raw21704; decide +kernel
      have hl : raw21704step0Labels = raw21704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21704 raw21704Labels permutation434 hz
    mixedMoment B raw21704step0 raw21704step0Labels = mixedMoment B raw21704step1 raw21704step1Labels := by
      have hz : ∀ j, raw21704step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21704step1 = (fun i j => raw21704step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21704step1 raw21704step0; decide +kernel
      have hl : raw21704step1Labels = raw21704step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21704step0 raw21704step0Labels permutation56 hz
    mixedMoment B raw21704step1 raw21704step1Labels = mixedMoment B raw21704step2 raw21704step2Labels := by
      have ha : raw21704step2 = (fun i j => raw21704step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21704step2 raw21704step1; decide +kernel
      have hl : raw21704step2Labels = raw21704step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21704step1 raw21704step1Labels permutation8 permutation3
    mixedMoment B raw21704step2 raw21704step2Labels = mixedMoment B raw21704step3 raw21704step3Labels := by
      have ha : raw21704step3 = raw21704step2 := by apply Matrix.ext; unfold raw21704step3 raw21704step2; decide +kernel
      have hl : raw21704step2Labels = labelEmbedding6 ∘ raw21704step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21704step2 raw21704step2Labels raw21704step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4319 node4319Labels := by rfl

theorem canonical21705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21705 raw21705Labels = mixedMoment B node4319 node4319Labels := by
  calc
    mixedMoment B raw21705 raw21705Labels = mixedMoment B raw21705step0 raw21705step0Labels := by
      have hz : ∀ j, raw21705 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21705step0 = (fun i j => raw21705 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21705step0 raw21705; decide +kernel
      have hl : raw21705step0Labels = raw21705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21705 raw21705Labels permutation346 hz
    mixedMoment B raw21705step0 raw21705step0Labels = mixedMoment B raw21705step1 raw21705step1Labels := by
      have hz : ∀ j, raw21705step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21705step1 = (fun i j => raw21705step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21705step1 raw21705step0; decide +kernel
      have hl : raw21705step1Labels = raw21705step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21705step0 raw21705step0Labels permutation56 hz
    mixedMoment B raw21705step1 raw21705step1Labels = mixedMoment B raw21705step2 raw21705step2Labels := by
      have ha : raw21705step2 = (fun i j => raw21705step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21705step2 raw21705step1; decide +kernel
      have hl : raw21705step2Labels = raw21705step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21705step1 raw21705step1Labels permutation8 permutation3
    mixedMoment B raw21705step2 raw21705step2Labels = mixedMoment B raw21705step3 raw21705step3Labels := by
      have ha : raw21705step3 = raw21705step2 := by apply Matrix.ext; unfold raw21705step3 raw21705step2; decide +kernel
      have hl : raw21705step2Labels = labelEmbedding6 ∘ raw21705step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21705step2 raw21705step2Labels raw21705step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4319 node4319Labels := by rfl

theorem canonical21706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21706 raw21706Labels = mixedMoment B node4134 node4134Labels := by
  calc
    mixedMoment B raw21706 raw21706Labels = mixedMoment B raw21706step0 raw21706step0Labels := by
      have hz : ∀ j, raw21706 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21706step0 = (fun i j => raw21706 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21706step0 raw21706; decide +kernel
      have hl : raw21706step0Labels = raw21706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21706 raw21706Labels permutation434 hz
    mixedMoment B raw21706step0 raw21706step0Labels = mixedMoment B raw21706step1 raw21706step1Labels := by
      have hz : ∀ j, raw21706step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21706step1 = (fun i j => raw21706step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21706step1 raw21706step0; decide +kernel
      have hl : raw21706step1Labels = raw21706step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21706step0 raw21706step0Labels permutation80 hz
    mixedMoment B raw21706step1 raw21706step1Labels = mixedMoment B raw21706step2 raw21706step2Labels := by
      have hz : ∀ j, raw21706step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21706step2 = (fun i j => raw21706step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21706step2 raw21706step1; decide +kernel
      have hl : raw21706step2Labels = raw21706step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21706step1 raw21706step1Labels permutation14 hz
    mixedMoment B raw21706step2 raw21706step2Labels = mixedMoment B raw21706step3 raw21706step3Labels := by
      have ha : raw21706step3 = (fun i j => raw21706step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21706step3 raw21706step2; decide +kernel
      have hl : raw21706step3Labels = raw21706step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21706step2 raw21706step2Labels permutation2 permutation3
    mixedMoment B raw21706step3 raw21706step3Labels = mixedMoment B raw21706step4 raw21706step4Labels := by
      have ha : raw21706step4 = raw21706step3 := by apply Matrix.ext; unfold raw21706step4 raw21706step3; decide +kernel
      have hl : raw21706step3Labels = labelEmbedding6 ∘ raw21706step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21706step3 raw21706step3Labels raw21706step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4134 node4134Labels := by rfl

theorem canonical21707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21707 raw21707Labels = mixedMoment B node4315 node4315Labels := by
  calc
    mixedMoment B raw21707 raw21707Labels = mixedMoment B raw21707step0 raw21707step0Labels := by
      have hz : ∀ j, raw21707 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21707step0 = (fun i j => raw21707 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21707step0 raw21707; decide +kernel
      have hl : raw21707step0Labels = raw21707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21707 raw21707Labels permutation434 hz
    mixedMoment B raw21707step0 raw21707step0Labels = mixedMoment B raw21707step1 raw21707step1Labels := by
      have hz : ∀ j, raw21707step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21707step1 = (fun i j => raw21707step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21707step1 raw21707step0; decide +kernel
      have hl : raw21707step1Labels = raw21707step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21707step0 raw21707step0Labels permutation80 hz
    mixedMoment B raw21707step1 raw21707step1Labels = mixedMoment B raw21707step2 raw21707step2Labels := by
      have ha : raw21707step2 = (fun i j => raw21707step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21707step2 raw21707step1; decide +kernel
      have hl : raw21707step2Labels = raw21707step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21707step1 raw21707step1Labels permutation8 permutation3
    mixedMoment B raw21707step2 raw21707step2Labels = mixedMoment B raw21707step3 raw21707step3Labels := by
      have ha : raw21707step3 = raw21707step2 := by apply Matrix.ext; unfold raw21707step3 raw21707step2; decide +kernel
      have hl : raw21707step2Labels = labelEmbedding6 ∘ raw21707step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21707step2 raw21707step2Labels raw21707step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4315 node4315Labels := by rfl

theorem canonical21708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21708 raw21708Labels = mixedMoment B node4315 node4315Labels := by
  calc
    mixedMoment B raw21708 raw21708Labels = mixedMoment B raw21708step0 raw21708step0Labels := by
      have hz : ∀ j, raw21708 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21708step0 = (fun i j => raw21708 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21708step0 raw21708; decide +kernel
      have hl : raw21708step0Labels = raw21708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21708 raw21708Labels permutation434 hz
    mixedMoment B raw21708step0 raw21708step0Labels = mixedMoment B raw21708step1 raw21708step1Labels := by
      have hz : ∀ j, raw21708step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21708step1 = (fun i j => raw21708step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21708step1 raw21708step0; decide +kernel
      have hl : raw21708step1Labels = raw21708step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21708step0 raw21708step0Labels permutation56 hz
    mixedMoment B raw21708step1 raw21708step1Labels = mixedMoment B raw21708step2 raw21708step2Labels := by
      have ha : raw21708step2 = (fun i j => raw21708step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21708step2 raw21708step1; decide +kernel
      have hl : raw21708step2Labels = raw21708step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21708step1 raw21708step1Labels permutation8 permutation3
    mixedMoment B raw21708step2 raw21708step2Labels = mixedMoment B raw21708step3 raw21708step3Labels := by
      have ha : raw21708step3 = raw21708step2 := by apply Matrix.ext; unfold raw21708step3 raw21708step2; decide +kernel
      have hl : raw21708step2Labels = labelEmbedding6 ∘ raw21708step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21708step2 raw21708step2Labels raw21708step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4315 node4315Labels := by rfl

theorem canonical21709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21709 raw21709Labels = mixedMoment B node4315 node4315Labels := by
  calc
    mixedMoment B raw21709 raw21709Labels = mixedMoment B raw21709step0 raw21709step0Labels := by
      have hz : ∀ j, raw21709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21709step0 = (fun i j => raw21709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21709step0 raw21709; decide +kernel
      have hl : raw21709step0Labels = raw21709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21709 raw21709Labels permutation346 hz
    mixedMoment B raw21709step0 raw21709step0Labels = mixedMoment B raw21709step1 raw21709step1Labels := by
      have hz : ∀ j, raw21709step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21709step1 = (fun i j => raw21709step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21709step1 raw21709step0; decide +kernel
      have hl : raw21709step1Labels = raw21709step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21709step0 raw21709step0Labels permutation56 hz
    mixedMoment B raw21709step1 raw21709step1Labels = mixedMoment B raw21709step2 raw21709step2Labels := by
      have ha : raw21709step2 = (fun i j => raw21709step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21709step2 raw21709step1; decide +kernel
      have hl : raw21709step2Labels = raw21709step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21709step1 raw21709step1Labels permutation8 permutation3
    mixedMoment B raw21709step2 raw21709step2Labels = mixedMoment B raw21709step3 raw21709step3Labels := by
      have ha : raw21709step3 = raw21709step2 := by apply Matrix.ext; unfold raw21709step3 raw21709step2; decide +kernel
      have hl : raw21709step2Labels = labelEmbedding6 ∘ raw21709step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21709step2 raw21709step2Labels raw21709step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4315 node4315Labels := by rfl

theorem canonical21710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21710 raw21710Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw21710 raw21710Labels = mixedMoment B raw21710step0 raw21710step0Labels := by
      have hz : ∀ j, raw21710 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21710step0 = (fun i j => raw21710 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21710step0 raw21710; decide +kernel
      have hl : raw21710step0Labels = raw21710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21710 raw21710Labels permutation434 hz
    mixedMoment B raw21710step0 raw21710step0Labels = mixedMoment B raw21710step1 raw21710step1Labels := by
      have hz : ∀ j, raw21710step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21710step1 = (fun i j => raw21710step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21710step1 raw21710step0; decide +kernel
      have hl : raw21710step1Labels = raw21710step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21710step0 raw21710step0Labels permutation80 hz
    mixedMoment B raw21710step1 raw21710step1Labels = mixedMoment B raw21710step2 raw21710step2Labels := by
      have hz : ∀ j, raw21710step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21710step2 = (fun i j => raw21710step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21710step2 raw21710step1; decide +kernel
      have hl : raw21710step2Labels = raw21710step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21710step1 raw21710step1Labels permutation14 hz
    mixedMoment B raw21710step2 raw21710step2Labels = mixedMoment B raw21710step3 raw21710step3Labels := by
      have ha : raw21710step3 = (fun i j => raw21710step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21710step3 raw21710step2; decide +kernel
      have hl : raw21710step3Labels = raw21710step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21710step2 raw21710step2Labels permutation2 permutation3
    mixedMoment B raw21710step3 raw21710step3Labels = mixedMoment B raw21710step4 raw21710step4Labels := by
      have ha : raw21710step4 = raw21710step3 := by apply Matrix.ext; unfold raw21710step4 raw21710step3; decide +kernel
      have hl : raw21710step3Labels = labelEmbedding6 ∘ raw21710step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21710step3 raw21710step3Labels raw21710step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

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

theorem canonical2325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2325 raw2325Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw2325 raw2325Labels = mixedMoment B raw2325step0 raw2325step0Labels := by
      have ha : raw2325step0 = (fun i j => raw2325 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2325step0 raw2325; decide +kernel
      have hl : raw2325step0Labels = raw2325Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2325 raw2325Labels permutation2 permutation4
    mixedMoment B raw2325step0 raw2325step0Labels = mixedMoment B raw2325step1 raw2325step1Labels := by
      have ha : raw2325step1 = raw2325step0 := by apply Matrix.ext; unfold raw2325step1 raw2325step0; decide +kernel
      have hl : raw2325step0Labels = labelEmbedding7 ∘ raw2325step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2325step0 raw2325step0Labels raw2325step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

theorem canonical2326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2326 raw2326Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw2326 raw2326Labels = mixedMoment B raw2326step0 raw2326step0Labels := by
      have ha : raw2326step0 = (fun i j => raw2326 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2326step0 raw2326; decide +kernel
      have hl : raw2326step0Labels = raw2326Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2326 raw2326Labels permutation2 permutation4
    _ = mixedMoment B node2788 node2788Labels := by rfl

theorem canonical2327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2327 raw2327Labels = mixedMoment B node3633 node3633Labels := by
  calc
    mixedMoment B raw2327 raw2327Labels = mixedMoment B raw2327step0 raw2327step0Labels := by
      have ha : raw2327step0 = (fun i j => raw2327 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2327step0 raw2327; decide +kernel
      have hl : raw2327step0Labels = raw2327Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2327 raw2327Labels permutation3 permutation6
    mixedMoment B raw2327step0 raw2327step0Labels = mixedMoment B raw2327step1 raw2327step1Labels := by
      have ha : raw2327step1 = -raw2327step0 := by apply Matrix.ext; change ∀ i j, raw2327step1 i j = -(raw2327step0 i j); unfold raw2327step1 raw2327step0; decide +kernel
      have hl : raw2327step1Labels = raw2327step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2327step1 raw2327step1Labels = mixedMoment B raw2327step2 raw2327step2Labels := by
      have ha : raw2327step2 = raw2327step1 := by apply Matrix.ext; unfold raw2327step2 raw2327step1; decide +kernel
      have hl : raw2327step1Labels = labelEmbedding1 ∘ raw2327step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2327step1 raw2327step1Labels raw2327step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3633 node3633Labels := by rfl

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

theorem canonical284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw284 raw284Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw284 raw284Labels = mixedMoment B raw284step0 raw284step0Labels := by
      have ha : raw284step0 = (fun i j => raw284 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw284step0 raw284; decide +kernel
      have hl : raw284step0Labels = raw284Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw284 raw284Labels permutation2 permutation5
    mixedMoment B raw284step0 raw284step0Labels = mixedMoment B raw284step1 raw284step1Labels := by
      have ha : raw284step1 = raw284step0 := by apply Matrix.ext; unfold raw284step1 raw284step0; decide +kernel
      have hl : raw284step0Labels = labelEmbedding1 ∘ raw284step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw284step0 raw284step0Labels raw284step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2788 node2788Labels := by rfl

theorem canonical285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw285 raw285Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw285 raw285Labels = mixedMoment B raw285step0 raw285step0Labels := by
      have ha : raw285step0 = (fun i j => raw285 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw285step0 raw285; decide +kernel
      have hl : raw285step0Labels = raw285Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw285 raw285Labels permutation2 permutation5
    _ = mixedMoment B node420 node420Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2871 raw2871Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw2871 raw2871Labels = mixedMoment B raw2871step0 raw2871step0Labels := by
      have hz : ∀ j, raw2871 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2871step0 = (fun i j => raw2871 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2871step0 raw2871; decide +kernel
      have hl : raw2871step0Labels = raw2871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2871 raw2871Labels permutation434 hz
    mixedMoment B raw2871step0 raw2871step0Labels = mixedMoment B raw2871step1 raw2871step1Labels := by
      have hz : ∀ j, raw2871step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2871step1 = (fun i j => raw2871step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2871step1 raw2871step0; decide +kernel
      have hl : raw2871step1Labels = raw2871step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2871step0 raw2871step0Labels permutation80 hz
    mixedMoment B raw2871step1 raw2871step1Labels = mixedMoment B raw2871step2 raw2871step2Labels := by
      have hz : ∀ j, raw2871step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2871step2 = (fun i j => raw2871step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2871step2 raw2871step1; decide +kernel
      have hl : raw2871step2Labels = raw2871step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2871step1 raw2871step1Labels permutation14 hz
    mixedMoment B raw2871step2 raw2871step2Labels = mixedMoment B raw2871step3 raw2871step3Labels := by
      have ha : raw2871step3 = (fun i j => raw2871step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2871step3 raw2871step2; decide +kernel
      have hl : raw2871step3Labels = raw2871step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2871step2 raw2871step2Labels permutation2 permutation3
    mixedMoment B raw2871step3 raw2871step3Labels = mixedMoment B raw2871step4 raw2871step4Labels := by
      have ha : raw2871step4 = raw2871step3 := by apply Matrix.ext; unfold raw2871step4 raw2871step3; decide +kernel
      have hl : raw2871step3Labels = labelEmbedding6 ∘ raw2871step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2871step3 raw2871step3Labels raw2871step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

theorem canonical2876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2876 raw2876Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw2876 raw2876Labels = mixedMoment B raw2876step0 raw2876step0Labels := by
      have hz : ∀ j, raw2876 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2876step0 = (fun i j => raw2876 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2876step0 raw2876; decide +kernel
      have hl : raw2876step0Labels = raw2876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2876 raw2876Labels permutation434 hz
    mixedMoment B raw2876step0 raw2876step0Labels = mixedMoment B raw2876step1 raw2876step1Labels := by
      have hz : ∀ j, raw2876step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2876step1 = (fun i j => raw2876step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2876step1 raw2876step0; decide +kernel
      have hl : raw2876step1Labels = raw2876step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2876step0 raw2876step0Labels permutation80 hz
    mixedMoment B raw2876step1 raw2876step1Labels = mixedMoment B raw2876step2 raw2876step2Labels := by
      have hz : ∀ j, raw2876step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2876step2 = (fun i j => raw2876step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2876step2 raw2876step1; decide +kernel
      have hl : raw2876step2Labels = raw2876step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2876step1 raw2876step1Labels permutation14 hz
    mixedMoment B raw2876step2 raw2876step2Labels = mixedMoment B raw2876step3 raw2876step3Labels := by
      have ha : raw2876step3 = (fun i j => raw2876step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2876step3 raw2876step2; decide +kernel
      have hl : raw2876step3Labels = raw2876step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2876step2 raw2876step2Labels permutation7 permutation2
    mixedMoment B raw2876step3 raw2876step3Labels = mixedMoment B raw2876step4 raw2876step4Labels := by
      have ha : raw2876step4 = -raw2876step3 := by apply Matrix.ext; change ∀ i j, raw2876step4 i j = -(raw2876step3 i j); unfold raw2876step4 raw2876step3; decide +kernel
      have hl : raw2876step4Labels = raw2876step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5296 node5296Labels := by rfl

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

theorem canonical735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw735 raw735Labels = mixedMoment B node4128 node4128Labels := by
  calc
    mixedMoment B raw735 raw735Labels = mixedMoment B raw735step0 raw735step0Labels := by
      have ha : raw735step0 = (fun i j => raw735 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw735step0 raw735; decide +kernel
      have hl : raw735step0Labels = raw735Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw735 raw735Labels permutation8 permutation4
    mixedMoment B raw735step0 raw735step0Labels = mixedMoment B raw735step1 raw735step1Labels := by
      have ha : raw735step1 = raw735step0 := by apply Matrix.ext; unfold raw735step1 raw735step0; decide +kernel
      have hl : raw735step0Labels = labelEmbedding7 ∘ raw735step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw735step0 raw735step0Labels raw735step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4128 node4128Labels := by rfl

theorem canonical736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw736 raw736Labels = mixedMoment B node559 node559Labels := by
  calc
    mixedMoment B raw736 raw736Labels = mixedMoment B raw736step0 raw736step0Labels := by
      have ha : raw736step0 = (fun i j => raw736 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw736step0 raw736; decide +kernel
      have hl : raw736step0Labels = raw736Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw736 raw736Labels permutation8 permutation4
    _ = mixedMoment B node559 node559Labels := by rfl

theorem canonical737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw737 raw737Labels = mixedMoment B node690 node690Labels := by
  calc
    mixedMoment B raw737 raw737Labels = mixedMoment B raw737step0 raw737step0Labels := by
      have ha : raw737step0 = (fun i j => raw737 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw737step0 raw737; decide +kernel
      have hl : raw737step0Labels = raw737Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw737 raw737Labels permutation9 permutation6
    mixedMoment B raw737step0 raw737step0Labels = mixedMoment B raw737step1 raw737step1Labels := by
      have ha : raw737step1 = -raw737step0 := by apply Matrix.ext; change ∀ i j, raw737step1 i j = -(raw737step0 i j); unfold raw737step1 raw737step0; decide +kernel
      have hl : raw737step1Labels = raw737step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw737step1 raw737step1Labels = mixedMoment B raw737step2 raw737step2Labels := by
      have ha : raw737step2 = raw737step1 := by apply Matrix.ext; unfold raw737step2 raw737step1; decide +kernel
      have hl : raw737step1Labels = labelEmbedding1 ∘ raw737step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw737step1 raw737step1Labels raw737step2Labels labelEmbedding1 hl
    _ = mixedMoment B node690 node690Labels := by rfl

theorem canonical747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw747 raw747Labels = mixedMoment B node4134 node4134Labels := by
  calc
    mixedMoment B raw747 raw747Labels = mixedMoment B raw747step0 raw747step0Labels := by
      have ha : raw747step0 = (fun i j => raw747 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw747step0 raw747; decide +kernel
      have hl : raw747step0Labels = raw747Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw747 raw747Labels permutation2 permutation4
    mixedMoment B raw747step0 raw747step0Labels = mixedMoment B raw747step1 raw747step1Labels := by
      have ha : raw747step1 = raw747step0 := by apply Matrix.ext; unfold raw747step1 raw747step0; decide +kernel
      have hl : raw747step0Labels = labelEmbedding7 ∘ raw747step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw747step0 raw747step0Labels raw747step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4134 node4134Labels := by rfl

theorem canonical748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw748 raw748Labels = mixedMoment B node564 node564Labels := by
  calc
    mixedMoment B raw748 raw748Labels = mixedMoment B raw748step0 raw748step0Labels := by
      have ha : raw748step0 = (fun i j => raw748 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw748step0 raw748; decide +kernel
      have hl : raw748step0Labels = raw748Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw748 raw748Labels permutation2 permutation4
    _ = mixedMoment B node564 node564Labels := by rfl

theorem canonical749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw749 raw749Labels = mixedMoment B node695 node695Labels := by
  calc
    mixedMoment B raw749 raw749Labels = mixedMoment B raw749step0 raw749step0Labels := by
      have ha : raw749step0 = (fun i j => raw749 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw749step0 raw749; decide +kernel
      have hl : raw749step0Labels = raw749Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw749 raw749Labels permutation2 permutation6
    mixedMoment B raw749step0 raw749step0Labels = mixedMoment B raw749step1 raw749step1Labels := by
      have ha : raw749step1 = -raw749step0 := by apply Matrix.ext; change ∀ i j, raw749step1 i j = -(raw749step0 i j); unfold raw749step1 raw749step0; decide +kernel
      have hl : raw749step1Labels = raw749step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw749step1 raw749step1Labels = mixedMoment B raw749step2 raw749step2Labels := by
      have ha : raw749step2 = raw749step1 := by apply Matrix.ext; unfold raw749step2 raw749step1; decide +kernel
      have hl : raw749step1Labels = labelEmbedding1 ∘ raw749step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw749step1 raw749step1Labels raw749step2Labels labelEmbedding1 hl
    _ = mixedMoment B node695 node695Labels := by rfl

theorem canonical753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw753 raw753Labels = mixedMoment B node4138 node4138Labels := by
  calc
    mixedMoment B raw753 raw753Labels = mixedMoment B raw753step0 raw753step0Labels := by
      have ha : raw753step0 = (fun i j => raw753 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw753step0 raw753; decide +kernel
      have hl : raw753step0Labels = raw753Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw753 raw753Labels permutation2 permutation4
    mixedMoment B raw753step0 raw753step0Labels = mixedMoment B raw753step1 raw753step1Labels := by
      have ha : raw753step1 = raw753step0 := by apply Matrix.ext; unfold raw753step1 raw753step0; decide +kernel
      have hl : raw753step0Labels = labelEmbedding7 ∘ raw753step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw753step0 raw753step0Labels raw753step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4138 node4138Labels := by rfl

theorem canonical754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw754 raw754Labels = mixedMoment B node566 node566Labels := by
  calc
    mixedMoment B raw754 raw754Labels = mixedMoment B raw754step0 raw754step0Labels := by
      have ha : raw754step0 = (fun i j => raw754 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw754step0 raw754; decide +kernel
      have hl : raw754step0Labels = raw754Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw754 raw754Labels permutation2 permutation4
    _ = mixedMoment B node566 node566Labels := by rfl

theorem canonical755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw755 raw755Labels = mixedMoment B node694 node694Labels := by
  calc
    mixedMoment B raw755 raw755Labels = mixedMoment B raw755step0 raw755step0Labels := by
      have ha : raw755step0 = (fun i j => raw755 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw755step0 raw755; decide +kernel
      have hl : raw755step0Labels = raw755Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw755 raw755Labels permutation3 permutation6
    mixedMoment B raw755step0 raw755step0Labels = mixedMoment B raw755step1 raw755step1Labels := by
      have ha : raw755step1 = -raw755step0 := by apply Matrix.ext; change ∀ i j, raw755step1 i j = -(raw755step0 i j); unfold raw755step1 raw755step0; decide +kernel
      have hl : raw755step1Labels = raw755step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw755step1 raw755step1Labels = mixedMoment B raw755step2 raw755step2Labels := by
      have ha : raw755step2 = raw755step1 := by apply Matrix.ext; unfold raw755step2 raw755step1; decide +kernel
      have hl : raw755step1Labels = labelEmbedding1 ∘ raw755step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw755step1 raw755step1Labels raw755step2Labels labelEmbedding1 hl
    _ = mixedMoment B node694 node694Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7597 raw7597Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw7597 raw7597Labels = mixedMoment B raw7597step0 raw7597step0Labels := by
      have hz : ∀ j, raw7597 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7597step0 = (fun i j => raw7597 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7597step0 raw7597; decide +kernel
      have hl : raw7597step0Labels = raw7597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7597 raw7597Labels permutation434 hz
    mixedMoment B raw7597step0 raw7597step0Labels = mixedMoment B raw7597step1 raw7597step1Labels := by
      have hz : ∀ j, raw7597step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7597step1 = (fun i j => raw7597step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7597step1 raw7597step0; decide +kernel
      have hl : raw7597step1Labels = raw7597step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7597step0 raw7597step0Labels permutation80 hz
    mixedMoment B raw7597step1 raw7597step1Labels = mixedMoment B raw7597step2 raw7597step2Labels := by
      have ha : raw7597step2 = (fun i j => raw7597step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7597step2 raw7597step1; decide +kernel
      have hl : raw7597step2Labels = raw7597step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7597step1 raw7597step1Labels permutation8 permutation3
    mixedMoment B raw7597step2 raw7597step2Labels = mixedMoment B raw7597step3 raw7597step3Labels := by
      have ha : raw7597step3 = raw7597step2 := by apply Matrix.ext; unfold raw7597step3 raw7597step2; decide +kernel
      have hl : raw7597step2Labels = labelEmbedding6 ∘ raw7597step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7597step2 raw7597step2Labels raw7597step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

theorem canonical7600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7600 raw7600Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw7600 raw7600Labels = mixedMoment B raw7600step0 raw7600step0Labels := by
      have hz : ∀ j, raw7600 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7600step0 = (fun i j => raw7600 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7600step0 raw7600; decide +kernel
      have hl : raw7600step0Labels = raw7600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7600 raw7600Labels permutation434 hz
    mixedMoment B raw7600step0 raw7600step0Labels = mixedMoment B raw7600step1 raw7600step1Labels := by
      have hz : ∀ j, raw7600step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7600step1 = (fun i j => raw7600step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7600step1 raw7600step0; decide +kernel
      have hl : raw7600step1Labels = raw7600step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7600step0 raw7600step0Labels permutation56 hz
    mixedMoment B raw7600step1 raw7600step1Labels = mixedMoment B raw7600step2 raw7600step2Labels := by
      have ha : raw7600step2 = (fun i j => raw7600step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7600step2 raw7600step1; decide +kernel
      have hl : raw7600step2Labels = raw7600step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7600step1 raw7600step1Labels permutation8 permutation3
    mixedMoment B raw7600step2 raw7600step2Labels = mixedMoment B raw7600step3 raw7600step3Labels := by
      have ha : raw7600step3 = raw7600step2 := by apply Matrix.ext; unfold raw7600step3 raw7600step2; decide +kernel
      have hl : raw7600step2Labels = labelEmbedding6 ∘ raw7600step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7600step2 raw7600step2Labels raw7600step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

theorem canonical7603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7603 raw7603Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw7603 raw7603Labels = mixedMoment B raw7603step0 raw7603step0Labels := by
      have hz : ∀ j, raw7603 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7603step0 = (fun i j => raw7603 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7603step0 raw7603; decide +kernel
      have hl : raw7603step0Labels = raw7603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7603 raw7603Labels permutation346 hz
    mixedMoment B raw7603step0 raw7603step0Labels = mixedMoment B raw7603step1 raw7603step1Labels := by
      have hz : ∀ j, raw7603step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7603step1 = (fun i j => raw7603step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7603step1 raw7603step0; decide +kernel
      have hl : raw7603step1Labels = raw7603step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7603step0 raw7603step0Labels permutation56 hz
    mixedMoment B raw7603step1 raw7603step1Labels = mixedMoment B raw7603step2 raw7603step2Labels := by
      have ha : raw7603step2 = (fun i j => raw7603step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7603step2 raw7603step1; decide +kernel
      have hl : raw7603step2Labels = raw7603step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7603step1 raw7603step1Labels permutation8 permutation3
    mixedMoment B raw7603step2 raw7603step2Labels = mixedMoment B raw7603step3 raw7603step3Labels := by
      have ha : raw7603step3 = raw7603step2 := by apply Matrix.ext; unfold raw7603step3 raw7603step2; decide +kernel
      have hl : raw7603step2Labels = labelEmbedding6 ∘ raw7603step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7603step2 raw7603step2Labels raw7603step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

theorem canonical7606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7606 raw7606Labels = mixedMoment B node4510 node4510Labels := by
  calc
    mixedMoment B raw7606 raw7606Labels = mixedMoment B raw7606step0 raw7606step0Labels := by
      have hz : ∀ j, raw7606 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7606step0 = (fun i j => raw7606 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7606step0 raw7606; decide +kernel
      have hl : raw7606step0Labels = raw7606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7606 raw7606Labels permutation434 hz
    mixedMoment B raw7606step0 raw7606step0Labels = mixedMoment B raw7606step1 raw7606step1Labels := by
      have hz : ∀ j, raw7606step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7606step1 = (fun i j => raw7606step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7606step1 raw7606step0; decide +kernel
      have hl : raw7606step1Labels = raw7606step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7606step0 raw7606step0Labels permutation80 hz
    mixedMoment B raw7606step1 raw7606step1Labels = mixedMoment B raw7606step2 raw7606step2Labels := by
      have hz : ∀ j, raw7606step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7606step2 = (fun i j => raw7606step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7606step2 raw7606step1; decide +kernel
      have hl : raw7606step2Labels = raw7606step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7606step1 raw7606step1Labels permutation14 hz
    mixedMoment B raw7606step2 raw7606step2Labels = mixedMoment B raw7606step3 raw7606step3Labels := by
      have ha : raw7606step3 = (fun i j => raw7606step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7606step3 raw7606step2; decide +kernel
      have hl : raw7606step3Labels = raw7606step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7606step2 raw7606step2Labels permutation3 permutation3
    mixedMoment B raw7606step3 raw7606step3Labels = mixedMoment B raw7606step4 raw7606step4Labels := by
      have ha : raw7606step4 = raw7606step3 := by apply Matrix.ext; unfold raw7606step4 raw7606step3; decide +kernel
      have hl : raw7606step3Labels = labelEmbedding6 ∘ raw7606step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7606step3 raw7606step3Labels raw7606step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4510 node4510Labels := by rfl

theorem canonical7611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7611 raw7611Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw7611 raw7611Labels = mixedMoment B raw7611step0 raw7611step0Labels := by
      have hz : ∀ j, raw7611 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7611step0 = (fun i j => raw7611 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7611step0 raw7611; decide +kernel
      have hl : raw7611step0Labels = raw7611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7611 raw7611Labels permutation434 hz
    mixedMoment B raw7611step0 raw7611step0Labels = mixedMoment B raw7611step1 raw7611step1Labels := by
      have hz : ∀ j, raw7611step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7611step1 = (fun i j => raw7611step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7611step1 raw7611step0; decide +kernel
      have hl : raw7611step1Labels = raw7611step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7611step0 raw7611step0Labels permutation80 hz
    mixedMoment B raw7611step1 raw7611step1Labels = mixedMoment B raw7611step2 raw7611step2Labels := by
      have ha : raw7611step2 = (fun i j => raw7611step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7611step2 raw7611step1; decide +kernel
      have hl : raw7611step2Labels = raw7611step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7611step1 raw7611step1Labels permutation8 permutation3
    mixedMoment B raw7611step2 raw7611step2Labels = mixedMoment B raw7611step3 raw7611step3Labels := by
      have ha : raw7611step3 = raw7611step2 := by apply Matrix.ext; unfold raw7611step3 raw7611step2; decide +kernel
      have hl : raw7611step2Labels = labelEmbedding6 ∘ raw7611step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7611step2 raw7611step2Labels raw7611step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

theorem canonical7612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7612 raw7612Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw7612 raw7612Labels = mixedMoment B raw7612step0 raw7612step0Labels := by
      have hz : ∀ j, raw7612 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7612step0 = (fun i j => raw7612 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7612step0 raw7612; decide +kernel
      have hl : raw7612step0Labels = raw7612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7612 raw7612Labels permutation434 hz
    mixedMoment B raw7612step0 raw7612step0Labels = mixedMoment B raw7612step1 raw7612step1Labels := by
      have hz : ∀ j, raw7612step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7612step1 = (fun i j => raw7612step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7612step1 raw7612step0; decide +kernel
      have hl : raw7612step1Labels = raw7612step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7612step0 raw7612step0Labels permutation56 hz
    mixedMoment B raw7612step1 raw7612step1Labels = mixedMoment B raw7612step2 raw7612step2Labels := by
      have ha : raw7612step2 = (fun i j => raw7612step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7612step2 raw7612step1; decide +kernel
      have hl : raw7612step2Labels = raw7612step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7612step1 raw7612step1Labels permutation8 permutation3
    mixedMoment B raw7612step2 raw7612step2Labels = mixedMoment B raw7612step3 raw7612step3Labels := by
      have ha : raw7612step3 = raw7612step2 := by apply Matrix.ext; unfold raw7612step3 raw7612step2; decide +kernel
      have hl : raw7612step2Labels = labelEmbedding6 ∘ raw7612step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7612step2 raw7612step2Labels raw7612step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

theorem canonical7613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7613 raw7613Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw7613 raw7613Labels = mixedMoment B raw7613step0 raw7613step0Labels := by
      have hz : ∀ j, raw7613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7613step0 = (fun i j => raw7613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7613step0 raw7613; decide +kernel
      have hl : raw7613step0Labels = raw7613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7613 raw7613Labels permutation346 hz
    mixedMoment B raw7613step0 raw7613step0Labels = mixedMoment B raw7613step1 raw7613step1Labels := by
      have hz : ∀ j, raw7613step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7613step1 = (fun i j => raw7613step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7613step1 raw7613step0; decide +kernel
      have hl : raw7613step1Labels = raw7613step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7613step0 raw7613step0Labels permutation56 hz
    mixedMoment B raw7613step1 raw7613step1Labels = mixedMoment B raw7613step2 raw7613step2Labels := by
      have ha : raw7613step2 = (fun i j => raw7613step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7613step2 raw7613step1; decide +kernel
      have hl : raw7613step2Labels = raw7613step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7613step1 raw7613step1Labels permutation8 permutation3
    mixedMoment B raw7613step2 raw7613step2Labels = mixedMoment B raw7613step3 raw7613step3Labels := by
      have ha : raw7613step3 = raw7613step2 := by apply Matrix.ext; unfold raw7613step3 raw7613step2; decide +kernel
      have hl : raw7613step2Labels = labelEmbedding6 ∘ raw7613step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7613step2 raw7613step2Labels raw7613step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

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

theorem canonical1074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1074 raw1074Labels = mixedMoment B node4309 node4309Labels := by
  calc
    mixedMoment B raw1074 raw1074Labels = mixedMoment B raw1074step0 raw1074step0Labels := by
      have ha : raw1074step0 = (fun i j => raw1074 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1074step0 raw1074; decide +kernel
      have hl : raw1074step0Labels = raw1074Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1074 raw1074Labels permutation32 permutation4
    mixedMoment B raw1074step0 raw1074step0Labels = mixedMoment B raw1074step1 raw1074step1Labels := by
      have ha : raw1074step1 = raw1074step0 := by apply Matrix.ext; unfold raw1074step1 raw1074step0; decide +kernel
      have hl : raw1074step0Labels = labelEmbedding7 ∘ raw1074step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1074step0 raw1074step0Labels raw1074step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4309 node4309Labels := by rfl

theorem canonical1075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1075 raw1075Labels = mixedMoment B node887 node887Labels := by
  calc
    mixedMoment B raw1075 raw1075Labels = mixedMoment B raw1075step0 raw1075step0Labels := by
      have ha : raw1075step0 = (fun i j => raw1075 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1075step0 raw1075; decide +kernel
      have hl : raw1075step0Labels = raw1075Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1075 raw1075Labels permutation32 permutation4
    _ = mixedMoment B node887 node887Labels := by rfl

theorem canonical1076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1076 raw1076Labels = mixedMoment B node1573 node1573Labels := by
  calc
    mixedMoment B raw1076 raw1076Labels = mixedMoment B raw1076step0 raw1076step0Labels := by
      have ha : raw1076step0 = (fun i j => raw1076 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1076step0 raw1076; decide +kernel
      have hl : raw1076step0Labels = raw1076Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1076 raw1076Labels permutation33 permutation6
    mixedMoment B raw1076step0 raw1076step0Labels = mixedMoment B raw1076step1 raw1076step1Labels := by
      have ha : raw1076step1 = -raw1076step0 := by apply Matrix.ext; change ∀ i j, raw1076step1 i j = -(raw1076step0 i j); unfold raw1076step1 raw1076step0; decide +kernel
      have hl : raw1076step1Labels = raw1076step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1076step1 raw1076step1Labels = mixedMoment B raw1076step2 raw1076step2Labels := by
      have ha : raw1076step2 = raw1076step1 := by apply Matrix.ext; unfold raw1076step2 raw1076step1; decide +kernel
      have hl : raw1076step1Labels = labelEmbedding1 ∘ raw1076step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1076step1 raw1076step1Labels raw1076step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1573 node1573Labels := by rfl

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

theorem canonical1269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1269 raw1269Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw1269 raw1269Labels = mixedMoment B raw1269step0 raw1269step0Labels := by
      have ha : raw1269step0 = (fun i j => raw1269 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1269step0 raw1269; decide +kernel
      have hl : raw1269step0Labels = raw1269Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1269 raw1269Labels permutation8 permutation4
    mixedMoment B raw1269step0 raw1269step0Labels = mixedMoment B raw1269step1 raw1269step1Labels := by
      have ha : raw1269step1 = raw1269step0 := by apply Matrix.ext; unfold raw1269step1 raw1269step0; decide +kernel
      have hl : raw1269step0Labels = labelEmbedding7 ∘ raw1269step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1269step0 raw1269step0Labels raw1269step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

theorem canonical1270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1270 raw1270Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw1270 raw1270Labels = mixedMoment B raw1270step0 raw1270step0Labels := by
      have ha : raw1270step0 = (fun i j => raw1270 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1270step0 raw1270; decide +kernel
      have hl : raw1270step0Labels = raw1270Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1270 raw1270Labels permutation8 permutation4
    _ = mixedMoment B node1046 node1046Labels := by rfl

theorem canonical1271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1271 raw1271Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw1271 raw1271Labels = mixedMoment B raw1271step0 raw1271step0Labels := by
      have ha : raw1271step0 = (fun i j => raw1271 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1271step0 raw1271; decide +kernel
      have hl : raw1271step0Labels = raw1271Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1271 raw1271Labels permutation8 permutation6
    mixedMoment B raw1271step0 raw1271step0Labels = mixedMoment B raw1271step1 raw1271step1Labels := by
      have ha : raw1271step1 = -raw1271step0 := by apply Matrix.ext; change ∀ i j, raw1271step1 i j = -(raw1271step0 i j); unfold raw1271step1 raw1271step0; decide +kernel
      have hl : raw1271step1Labels = raw1271step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1271step1 raw1271step1Labels = mixedMoment B raw1271step2 raw1271step2Labels := by
      have ha : raw1271step2 = raw1271step1 := by apply Matrix.ext; unfold raw1271step2 raw1271step1; decide +kernel
      have hl : raw1271step1Labels = labelEmbedding1 ∘ raw1271step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1271step1 raw1271step1Labels raw1271step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

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

theorem canonical5199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5199 = injectiveMoment H node11 := by
  rfl

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

theorem canonical5214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5214 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw5214 = injectiveMoment H raw5214step0 := by
      have hz : ∀ j, raw5214 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw5214step0 = (fun i j => raw5214 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5214 permutation7 hz
    _ = injectiveMoment H node4 := by rfl

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

theorem sound36 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node36 = Sparse.eval value36 (momentVector H) := by
  have hc : momentVector H 3 = injectiveMoment H node36 := rfl
  simp [value36, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical813 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw813 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw813 = injectiveMoment H raw813step0 := by
      have heq : raw813step0 = -raw813 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw813).symm
    injectiveMoment H raw813step0 = injectiveMoment H raw813step1 := by
      have heq : raw813step1 = (fun i j => raw813step0 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw813step0 permutation4 permutation8
    _ = injectiveMoment H node36 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SinglePriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair420 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node420 node420Labels = Sparse.eval singlePairValue420 (familyPairVector B) := by
  have hp := single_label_three B hB node420
  have hl : node420Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node420 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 1) = PairSemantics.raw5214 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node420 PairSemantics.raw5214; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5214 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 2) = PairSemantics.raw7683 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node420 PairSemantics.raw7683; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7683 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 3) = PairSemantics.raw917 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node420 PairSemantics.raw917; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical917 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node420 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value36 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node420 (EqualityPatterns.family3.label 4) = PairSemantics.raw813 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node420 PairSemantics.raw813; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical813 hH).trans (PairSemantics.sound36 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue420, PairSemantics.value0, PairSemantics.value4, PairSemantics.value10, PairSemantics.value11, PairSemantics.value36, Sparse.eval] at hp ⊢
  linarith only [hp]

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

theorem singleton2788 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2788 node2788Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node420 node420Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw284 singletonSmall2788
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2788) = raw284Labels := by decide +kernel
  rw [hl, canonical284 B hB] at h
  have hc0 : mixedMoment B raw284 (Fin.cases (0 : Fin 1) singletonSmall2788) =
      mixedMoment B node420 node420Labels := by
    have ha : raw284 = raw285 := by apply Matrix.ext; unfold raw284 raw285; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2788 = raw285Labels := by decide +kernel
    rw [ha, hj, canonical285 B hB]
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

theorem singleton4128 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4128 node4128Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node559 node559Labels + mixedMoment B node690 node690Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw735 singletonSmall4128
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4128) = raw735Labels := by decide +kernel
  rw [hl, canonical735 B hB] at h
  have hc0 : mixedMoment B raw735 (Fin.cases (0 : Fin 2) singletonSmall4128) =
      mixedMoment B node559 node559Labels := by
    have ha : raw735 = raw736 := by apply Matrix.ext; unfold raw735 raw736; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4128 = raw736Labels := by decide +kernel
    rw [ha, hj, canonical736 B hB]
  have hc1 : mixedMoment B raw735 (Fin.cases (1 : Fin 2) singletonSmall4128) =
      mixedMoment B node690 node690Labels := by
    have ha : raw735 = raw737 := by apply Matrix.ext; unfold raw735 raw737; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4128 = raw737Labels := by decide +kernel
    rw [ha, hj, canonical737 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4134 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4134 node4134Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node564 node564Labels + mixedMoment B node695 node695Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw747 singletonSmall4134
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4134) = raw747Labels := by decide +kernel
  rw [hl, canonical747 B hB] at h
  have hc0 : mixedMoment B raw747 (Fin.cases (0 : Fin 2) singletonSmall4134) =
      mixedMoment B node564 node564Labels := by
    have ha : raw747 = raw748 := by apply Matrix.ext; unfold raw747 raw748; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4134 = raw748Labels := by decide +kernel
    rw [ha, hj, canonical748 B hB]
  have hc1 : mixedMoment B raw747 (Fin.cases (1 : Fin 2) singletonSmall4134) =
      mixedMoment B node695 node695Labels := by
    have ha : raw747 = raw749 := by apply Matrix.ext; unfold raw747 raw749; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4134 = raw749Labels := by decide +kernel
    rw [ha, hj, canonical749 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4138 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4138 node4138Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node566 node566Labels + mixedMoment B node694 node694Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw753 singletonSmall4138
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4138) = raw753Labels := by decide +kernel
  rw [hl, canonical753 B hB] at h
  have hc0 : mixedMoment B raw753 (Fin.cases (0 : Fin 2) singletonSmall4138) =
      mixedMoment B node566 node566Labels := by
    have ha : raw753 = raw754 := by apply Matrix.ext; unfold raw753 raw754; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4138 = raw754Labels := by decide +kernel
    rw [ha, hj, canonical754 B hB]
  have hc1 : mixedMoment B raw753 (Fin.cases (1 : Fin 2) singletonSmall4138) =
      mixedMoment B node694 node694Labels := by
    have ha : raw753 = raw755 := by apply Matrix.ext; unfold raw753 raw755; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4138 = raw755Labels := by decide +kernel
    rw [ha, hj, canonical755 B hB]
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

theorem singleton4309 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4309 node4309Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node887 node887Labels + mixedMoment B node1573 node1573Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1074 singletonSmall4309
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4309) = raw1074Labels := by decide +kernel
  rw [hl, canonical1074 B hB] at h
  have hc0 : mixedMoment B raw1074 (Fin.cases (0 : Fin 2) singletonSmall4309) =
      mixedMoment B node887 node887Labels := by
    have ha : raw1074 = raw1075 := by apply Matrix.ext; unfold raw1074 raw1075; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4309 = raw1075Labels := by decide +kernel
    rw [ha, hj, canonical1075 B hB]
  have hc1 : mixedMoment B raw1074 (Fin.cases (1 : Fin 2) singletonSmall4309) =
      mixedMoment B node1573 node1573Labels := by
    have ha : raw1074 = raw1076 := by apply Matrix.ext; unfold raw1074 raw1076; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4309 = raw1076Labels := by decide +kernel
    rw [ha, hj, canonical1076 B hB]
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

theorem singleton4463 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4463 node4463Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1046 node1046Labels + mixedMoment B node1750 node1750Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1269 singletonSmall4463
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4463) = raw1269Labels := by decide +kernel
  rw [hl, canonical1269 B hB] at h
  have hc0 : mixedMoment B raw1269 (Fin.cases (0 : Fin 2) singletonSmall4463) =
      mixedMoment B node1046 node1046Labels := by
    have ha : raw1269 = raw1270 := by apply Matrix.ext; unfold raw1269 raw1270; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4463 = raw1270Labels := by decide +kernel
    rw [ha, hj, canonical1270 B hB]
  have hc1 : mixedMoment B raw1269 (Fin.cases (1 : Fin 2) singletonSmall4463) =
      mixedMoment B node1750 node1750Labels := by
    have ha : raw1269 = raw1271 := by apply Matrix.ext; unfold raw1269 raw1271; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4463 = raw1271Labels := by decide +kernel
    rw [ha, hj, canonical1271 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4503 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4503 node4503Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1087 node1087Labels + mixedMoment B node1739 node1739Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1302 singletonSmall4503
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4503) = raw1302Labels := by decide +kernel
  rw [hl, canonical1302 B hB] at h
  have hc0 : mixedMoment B raw1302 (Fin.cases (0 : Fin 2) singletonSmall4503) =
      mixedMoment B node1087 node1087Labels := by
    have ha : raw1302 = raw1303 := by apply Matrix.ext; unfold raw1302 raw1303; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4503 = raw1303Labels := by decide +kernel
    rw [ha, hj, canonical1303 B hB]
  have hc1 : mixedMoment B raw1302 (Fin.cases (1 : Fin 2) singletonSmall4503) =
      mixedMoment B node1739 node1739Labels := by
    have ha : raw1302 = raw1304 := by apply Matrix.ext; unfold raw1302 raw1304; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4503 = raw1304Labels := by decide +kernel
    rw [ha, hj, canonical1304 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4510 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4510 node4510Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1094 node1094Labels + mixedMoment B node1741 node1741Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1308 singletonSmall4510
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4510) = raw1308Labels := by decide +kernel
  rw [hl, canonical1308 B hB] at h
  have hc0 : mixedMoment B raw1308 (Fin.cases (0 : Fin 2) singletonSmall4510) =
      mixedMoment B node1094 node1094Labels := by
    have ha : raw1308 = raw1309 := by apply Matrix.ext; unfold raw1308 raw1309; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4510 = raw1309Labels := by decide +kernel
    rw [ha, hj, canonical1309 B hB]
  have hc1 : mixedMoment B raw1308 (Fin.cases (1 : Fin 2) singletonSmall4510) =
      mixedMoment B node1741 node1741Labels := by
    have ha : raw1308 = raw1310 := by apply Matrix.ext; unfold raw1308 raw1310; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4510 = raw1310Labels := by decide +kernel
    rw [ha, hj, canonical1310 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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

theorem singleton5310 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5310 node5310Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2788 node2788Labels + mixedMoment B node3633 node3633Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2325 singletonSmall5310
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5310) = raw2325Labels := by decide +kernel
  rw [hl, canonical2325 B hB] at h
  have hc0 : mixedMoment B raw2325 (Fin.cases (0 : Fin 2) singletonSmall5310) =
      mixedMoment B node2788 node2788Labels := by
    have ha : raw2325 = raw2326 := by apply Matrix.ext; unfold raw2325 raw2326; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5310 = raw2326Labels := by decide +kernel
    rw [ha, hj, canonical2326 B hB]
  have hc1 : mixedMoment B raw2325 (Fin.cases (1 : Fin 2) singletonSmall5310) =
      mixedMoment B node3633 node3633Labels := by
    have ha : raw2325 = raw2327 := by apply Matrix.ext; unfold raw2325 raw2327; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5310 = raw2327Labels := by decide +kernel
    rw [ha, hj, canonical2327 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SoundPriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node420 node420Labels = Sparse.eval nodeValue420 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue420 (familyPairVector B) := singlePair420 B _hB
    _ = _ := by norm_num [singlePairValue420, nodeValue420, Sparse.eval, mixedVector] <;> ring

theorem sound2788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2788 node2788Labels = Sparse.eval nodeValue2788 (mixedVector B) := by
  have h := singleton2788 B _hB
  rw [sound420 B _hB _hF] at h
  norm_num [nodeValue2788, nodeValue420, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound3633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3633 node3633Labels = Sparse.eval nodeValue3633 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3633) = mixedMoment B node3633 node3633Labels := rfl
  simpa [nodeValue3633, Sparse.eval] using hc.symm

theorem sound5310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5310 node5310Labels = Sparse.eval nodeValue5310 (mixedVector B) := by
  have h := singleton5310 B _hB
  rw [sound2788 B _hB _hF, sound3633 B _hB _hF] at h
  norm_num [nodeValue5310, nodeValue2788, nodeValue3633, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node690 node690Labels = Sparse.eval nodeValue690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 690) = mixedMoment B node690 node690Labels := rfl
  simpa [nodeValue690, Sparse.eval] using hc.symm

theorem sound694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node694 node694Labels = Sparse.eval nodeValue694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 694) = mixedMoment B node694 node694Labels := rfl
  simpa [nodeValue694, Sparse.eval] using hc.symm

theorem sound695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node695 node695Labels = Sparse.eval nodeValue695 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 695) = mixedMoment B node695 node695Labels := rfl
  simpa [nodeValue695, Sparse.eval] using hc.symm

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

theorem sound887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node887 node887Labels = Sparse.eval nodeValue887 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 887) = mixedMoment B node887 node887Labels := rfl
  simpa [nodeValue887, Sparse.eval] using hc.symm

theorem sound893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node893 node893Labels = Sparse.eval nodeValue893 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 893) = mixedMoment B node893 node893Labels := rfl
  simpa [nodeValue893, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1046 node1046Labels = Sparse.eval nodeValue1046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1046) = mixedMoment B node1046 node1046Labels := rfl
  simpa [nodeValue1046, Sparse.eval] using hc.symm

theorem sound1051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1051 node1051Labels = Sparse.eval nodeValue1051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1051) = mixedMoment B node1051 node1051Labels := rfl
  simpa [nodeValue1051, Sparse.eval] using hc.symm

theorem sound1087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1087 node1087Labels = Sparse.eval nodeValue1087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1087) = mixedMoment B node1087 node1087Labels := rfl
  simpa [nodeValue1087, Sparse.eval] using hc.symm

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

theorem sound1094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1094 node1094Labels = Sparse.eval nodeValue1094 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1094) = mixedMoment B node1094 node1094Labels := rfl
  simpa [nodeValue1094, Sparse.eval] using hc.symm

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

theorem sound1573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1573 node1573Labels = Sparse.eval nodeValue1573 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1573) = mixedMoment B node1573 node1573Labels := rfl
  simpa [nodeValue1573, Sparse.eval] using hc.symm

theorem sound1577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1577 node1577Labels = Sparse.eval nodeValue1577 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1577) = mixedMoment B node1577 node1577Labels := rfl
  simpa [nodeValue1577, Sparse.eval] using hc.symm

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

theorem sound1739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1739 node1739Labels = Sparse.eval nodeValue1739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1739) = mixedMoment B node1739 node1739Labels := rfl
  simpa [nodeValue1739, Sparse.eval] using hc.symm

theorem sound1741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1741 node1741Labels = Sparse.eval nodeValue1741 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1741) = mixedMoment B node1741 node1741Labels := rfl
  simpa [nodeValue1741, Sparse.eval] using hc.symm

theorem sound1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1750 node1750Labels = Sparse.eval nodeValue1750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1750) = mixedMoment B node1750 node1750Labels := rfl
  simpa [nodeValue1750, Sparse.eval] using hc.symm

theorem sound1752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1752 node1752Labels = Sparse.eval nodeValue1752 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1752) = mixedMoment B node1752 node1752Labels := rfl
  simpa [nodeValue1752, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem sound559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node559 node559Labels = Sparse.eval nodeValue559 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 559) = mixedMoment B node559 node559Labels := rfl
  simpa [nodeValue559, Sparse.eval] using hc.symm

theorem sound564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node564 node564Labels = Sparse.eval nodeValue564 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 564) = mixedMoment B node564 node564Labels := rfl
  simpa [nodeValue564, Sparse.eval] using hc.symm

theorem sound566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node566 node566Labels = Sparse.eval nodeValue566 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 566) = mixedMoment B node566 node566Labels := rfl
  simpa [nodeValue566, Sparse.eval] using hc.symm

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

theorem sound4128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4128 node4128Labels = Sparse.eval nodeValue4128 (mixedVector B) := by
  have h := singleton4128 B _hB
  rw [sound559 B _hB _hF, sound690 B _hB _hF] at h
  norm_num [nodeValue4128, nodeValue559, nodeValue690, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4134 node4134Labels = Sparse.eval nodeValue4134 (mixedVector B) := by
  have h := singleton4134 B _hB
  rw [sound564 B _hB _hF, sound695 B _hB _hF] at h
  norm_num [nodeValue4134, nodeValue564, nodeValue695, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4138 node4138Labels = Sparse.eval nodeValue4138 (mixedVector B) := by
  have h := singleton4138 B _hB
  rw [sound566 B _hB _hF, sound694 B _hB _hF] at h
  norm_num [nodeValue4138, nodeValue566, nodeValue694, Sparse.eval] at h ⊢
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

theorem sound4309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4309 node4309Labels = Sparse.eval nodeValue4309 (mixedVector B) := by
  have h := singleton4309 B _hB
  rw [sound887 B _hB _hF, sound1573 B _hB _hF] at h
  norm_num [nodeValue4309, nodeValue887, nodeValue1573, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4315 node4315Labels = Sparse.eval nodeValue4315 (mixedVector B) := by
  have h := singleton4315 B _hB
  rw [sound893 B _hB _hF, sound1578 B _hB _hF] at h
  norm_num [nodeValue4315, nodeValue893, nodeValue1578, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4463 node4463Labels = Sparse.eval nodeValue4463 (mixedVector B) := by
  have h := singleton4463 B _hB
  rw [sound1046 B _hB _hF, sound1750 B _hB _hF] at h
  norm_num [nodeValue4463, nodeValue1046, nodeValue1750, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4503 node4503Labels = Sparse.eval nodeValue4503 (mixedVector B) := by
  have h := singleton4503 B _hB
  rw [sound1087 B _hB _hF, sound1739 B _hB _hF] at h
  norm_num [nodeValue4503, nodeValue1087, nodeValue1739, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4510 node4510Labels = Sparse.eval nodeValue4510 (mixedVector B) := by
  have h := singleton4510 B _hB
  rw [sound1094 B _hB _hF, sound1741 B _hB _hF] at h
  norm_num [nodeValue4510, nodeValue1094, nodeValue1741, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources43
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1381 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1381 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1381 + difference 0 1) (sourceB1381 + difference 1 0) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA1381 + difference 0 1) (sourceB1381 + difference 1 0) sourceC1381) = raw7611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw7611; decide +kernel
    rw [ha]
    exact (canonical7611 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1381 + difference 0 2) (sourceB1381 + difference 2 0) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA1381 + difference 0 2) (sourceB1381 + difference 2 0) sourceC1381) = raw7612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw7612; decide +kernel
    rw [ha]
    exact (canonical7612 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1381 + difference 0 3) (sourceB1381 + difference 3 0) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA1381 + difference 0 3) (sourceB1381 + difference 3 0) sourceC1381) = raw7613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw7613; decide +kernel
    rw [ha]
    exact (canonical7613 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1381 + difference 0 4) (sourceB1381 + difference 4 0) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA1381 + difference 0 4) (sourceB1381 + difference 4 0) sourceC1381) = raw2876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw2876; decide +kernel
    rw [ha]
    exact (canonical2876 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1381 + difference 0 5) (sourceB1381 + difference 5 0) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA1381 + difference 0 5) (sourceB1381 + difference 5 0) sourceC1381) = raw2871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw2871; decide +kernel
    rw [ha]
    exact (canonical2871 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1381 + difference 1 0) (sourceB1381 + difference 0 1) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4128) := by
    have ha : (tripleCharges (sourceA1381 + difference 1 0) (sourceB1381 + difference 0 1) sourceC1381) = raw21690 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21690; decide +kernel
    rw [ha]
    exact (canonical21690 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1381 + difference 1 2) (sourceB1381 + difference 2 1) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4309) := by
    have ha : (tripleCharges (sourceA1381 + difference 1 2) (sourceB1381 + difference 2 1) sourceC1381) = raw21691 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21691; decide +kernel
    rw [ha]
    exact (canonical21691 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1381 + difference 1 3) (sourceB1381 + difference 3 1) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4309) := by
    have ha : (tripleCharges (sourceA1381 + difference 1 3) (sourceB1381 + difference 3 1) sourceC1381) = raw21692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21692; decide +kernel
    rw [ha]
    exact (canonical21692 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1381 + difference 1 4) (sourceB1381 + difference 4 1) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1381 + difference 1 4) (sourceB1381 + difference 4 1) sourceC1381) = raw21693 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21693; decide +kernel
    rw [ha]
    exact (canonical21693 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1381 + difference 1 5) (sourceB1381 + difference 5 1) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1381 + difference 1 5) (sourceB1381 + difference 5 1) sourceC1381) = raw7597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw7597; decide +kernel
    rw [ha]
    exact (canonical7597 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1381 + difference 2 0) (sourceB1381 + difference 0 2) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4128) := by
    have ha : (tripleCharges (sourceA1381 + difference 2 0) (sourceB1381 + difference 0 2) sourceC1381) = raw21694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21694; decide +kernel
    rw [ha]
    exact (canonical21694 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1381 + difference 2 1) (sourceB1381 + difference 1 2) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4309) := by
    have ha : (tripleCharges (sourceA1381 + difference 2 1) (sourceB1381 + difference 1 2) sourceC1381) = raw21695 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21695; decide +kernel
    rw [ha]
    exact (canonical21695 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1381 + difference 2 3) (sourceB1381 + difference 3 2) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4309) := by
    have ha : (tripleCharges (sourceA1381 + difference 2 3) (sourceB1381 + difference 3 2) sourceC1381) = raw21696 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21696; decide +kernel
    rw [ha]
    exact (canonical21696 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1381 + difference 2 4) (sourceB1381 + difference 4 2) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1381 + difference 2 4) (sourceB1381 + difference 4 2) sourceC1381) = raw21697 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21697; decide +kernel
    rw [ha]
    exact (canonical21697 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1381 + difference 2 5) (sourceB1381 + difference 5 2) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1381 + difference 2 5) (sourceB1381 + difference 5 2) sourceC1381) = raw7600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw7600; decide +kernel
    rw [ha]
    exact (canonical7600 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1381 + difference 3 0) (sourceB1381 + difference 0 3) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4128) := by
    have ha : (tripleCharges (sourceA1381 + difference 3 0) (sourceB1381 + difference 0 3) sourceC1381) = raw21698 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21698; decide +kernel
    rw [ha]
    exact (canonical21698 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1381 + difference 3 1) (sourceB1381 + difference 1 3) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4309) := by
    have ha : (tripleCharges (sourceA1381 + difference 3 1) (sourceB1381 + difference 1 3) sourceC1381) = raw21699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21699; decide +kernel
    rw [ha]
    exact (canonical21699 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1381 + difference 3 2) (sourceB1381 + difference 2 3) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4309) := by
    have ha : (tripleCharges (sourceA1381 + difference 3 2) (sourceB1381 + difference 2 3) sourceC1381) = raw21700 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21700; decide +kernel
    rw [ha]
    exact (canonical21700 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1381 + difference 3 4) (sourceB1381 + difference 4 3) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1381 + difference 3 4) (sourceB1381 + difference 4 3) sourceC1381) = raw21701 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21701; decide +kernel
    rw [ha]
    exact (canonical21701 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1381 + difference 3 5) (sourceB1381 + difference 5 3) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1381 + difference 3 5) (sourceB1381 + difference 5 3) sourceC1381) = raw7603 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw7603; decide +kernel
    rw [ha]
    exact (canonical7603 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1381 + difference 4 0) (sourceB1381 + difference 0 4) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4138) := by
    have ha : (tripleCharges (sourceA1381 + difference 4 0) (sourceB1381 + difference 0 4) sourceC1381) = raw21702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21702; decide +kernel
    rw [ha]
    exact (canonical21702 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1381 + difference 4 1) (sourceB1381 + difference 1 4) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4319) := by
    have ha : (tripleCharges (sourceA1381 + difference 4 1) (sourceB1381 + difference 1 4) sourceC1381) = raw21703 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21703; decide +kernel
    rw [ha]
    exact (canonical21703 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1381 + difference 4 2) (sourceB1381 + difference 2 4) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4319) := by
    have ha : (tripleCharges (sourceA1381 + difference 4 2) (sourceB1381 + difference 2 4) sourceC1381) = raw21704 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21704; decide +kernel
    rw [ha]
    exact (canonical21704 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1381 + difference 4 3) (sourceB1381 + difference 3 4) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4319) := by
    have ha : (tripleCharges (sourceA1381 + difference 4 3) (sourceB1381 + difference 3 4) sourceC1381) = raw21705 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21705; decide +kernel
    rw [ha]
    exact (canonical21705 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1381 + difference 4 5) (sourceB1381 + difference 5 4) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4510) := by
    have ha : (tripleCharges (sourceA1381 + difference 4 5) (sourceB1381 + difference 5 4) sourceC1381) = raw7606 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw7606; decide +kernel
    rw [ha]
    exact (canonical7606 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1381 + difference 5 0) (sourceB1381 + difference 0 5) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4134) := by
    have ha : (tripleCharges (sourceA1381 + difference 5 0) (sourceB1381 + difference 0 5) sourceC1381) = raw21706 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21706; decide +kernel
    rw [ha]
    exact (canonical21706 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1381 + difference 5 1) (sourceB1381 + difference 1 5) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4315) := by
    have ha : (tripleCharges (sourceA1381 + difference 5 1) (sourceB1381 + difference 1 5) sourceC1381) = raw21707 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21707; decide +kernel
    rw [ha]
    exact (canonical21707 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1381 + difference 5 2) (sourceB1381 + difference 2 5) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4315) := by
    have ha : (tripleCharges (sourceA1381 + difference 5 2) (sourceB1381 + difference 2 5) sourceC1381) = raw21708 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21708; decide +kernel
    rw [ha]
    exact (canonical21708 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1381 + difference 5 3) (sourceB1381 + difference 3 5) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4315) := by
    have ha : (tripleCharges (sourceA1381 + difference 5 3) (sourceB1381 + difference 3 5) sourceC1381) = raw21709 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21709; decide +kernel
    rw [ha]
    exact (canonical21709 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1381 + difference 5 4) (sourceB1381 + difference 4 5) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1381 + difference 5 4) (sourceB1381 + difference 4 5) sourceC1381) = raw21710 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21710; decide +kernel
    rw [ha]
    exact (canonical21710 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1381 sourceB1381 sourceC1381
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1381, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1194 : Integer.Sparse.reindex keyMap MixedData.row1194 = numericRow1194 := by decide +kernel

theorem numericCheck1194 (x : Master → ℝ) : Integer.Sparse.eval numericRow1194 x =
    (2880 : ℝ) * reducedSource1194 x := by
  norm_num [numericRow1194, reducedSource1194, Integer.Sparse.eval, Sparse.eval, nodeValue4128, nodeValue4134, nodeValue4138, nodeValue4309, nodeValue4315, nodeValue4319, nodeValue4463, nodeValue4468, nodeValue4503, nodeValue4510, nodeValue5109, nodeValue5296, nodeValue5310] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1194 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1194 (mixedVector B) = 0 := by
  have h4128 : mixedVector B (Sum.inr 4128) = Sparse.eval nodeValue4128 (mixedVector B) := by
    change mixedMoment B node4128 node4128Labels = _
    exact sound4128 B hB hF
  have h4134 : mixedVector B (Sum.inr 4134) = Sparse.eval nodeValue4134 (mixedVector B) := by
    change mixedMoment B node4134 node4134Labels = _
    exact sound4134 B hB hF
  have h4138 : mixedVector B (Sum.inr 4138) = Sparse.eval nodeValue4138 (mixedVector B) := by
    change mixedMoment B node4138 node4138Labels = _
    exact sound4138 B hB hF
  have h4309 : mixedVector B (Sum.inr 4309) = Sparse.eval nodeValue4309 (mixedVector B) := by
    change mixedMoment B node4309 node4309Labels = _
    exact sound4309 B hB hF
  have h4315 : mixedVector B (Sum.inr 4315) = Sparse.eval nodeValue4315 (mixedVector B) := by
    change mixedMoment B node4315 node4315Labels = _
    exact sound4315 B hB hF
  have h4319 : mixedVector B (Sum.inr 4319) = Sparse.eval nodeValue4319 (mixedVector B) := by
    change mixedMoment B node4319 node4319Labels = _
    exact sound4319 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4468 : mixedVector B (Sum.inr 4468) = Sparse.eval nodeValue4468 (mixedVector B) := by
    change mixedMoment B node4468 node4468Labels = _
    exact sound4468 B hB hF
  have h4503 : mixedVector B (Sum.inr 4503) = Sparse.eval nodeValue4503 (mixedVector B) := by
    change mixedMoment B node4503 node4503Labels = _
    exact sound4503 B hB hF
  have h4510 : mixedVector B (Sum.inr 4510) = Sparse.eval nodeValue4510 (mixedVector B) := by
    change mixedMoment B node4510 node4510Labels = _
    exact sound4510 B hB hF
  have h5109 : mixedVector B (Sum.inr 5109) = Sparse.eval nodeValue5109 (mixedVector B) := by
    change mixedMoment B node5109 node5109Labels = _
    exact sound5109 B hB hF
  have h5296 : mixedVector B (Sum.inr 5296) = Sparse.eval nodeValue5296 (mixedVector B) := by
    change mixedMoment B node5296 node5296Labels = _
    exact sound5296 B hB hF
  have h5310 : mixedVector B (Sum.inr 5310) = Sparse.eval nodeValue5310 (mixedVector B) := by
    change mixedMoment B node5310 node5310Labels = _
    exact sound5310 B hB hF
  simpa only [sourceForm1381, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4128, h4134, h4138, h4309, h4315, h4319, h4463, h4468, h4503, h4510, h5109, h5296, h5310, reducedSource1194] using sourceEq1381 B hB

theorem rowSound1194_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1194 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1194, numericCheck1194, reducedZero1194 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194_e_oai
