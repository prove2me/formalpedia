-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound542_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T01:50:48.407631+00:00
-- url     : https://prove2.me/submissions/86332f7c-f9cc-4602-9b07-2acdea6af528

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E127
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

theorem canonical1770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1770 raw1770Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw1770 raw1770Labels = mixedMoment B raw1770step0 raw1770step0Labels := by
      have ha : raw1770step0 = (fun i j => raw1770 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1770step0 raw1770; decide +kernel
      have hl : raw1770step0Labels = raw1770Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1770 raw1770Labels permutation32 permutation4
    mixedMoment B raw1770step0 raw1770step0Labels = mixedMoment B raw1770step1 raw1770step1Labels := by
      have ha : raw1770step1 = raw1770step0 := by apply Matrix.ext; unfold raw1770step1 raw1770step0; decide +kernel
      have hl : raw1770step0Labels = labelEmbedding7 ∘ raw1770step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1770step0 raw1770step0Labels raw1770step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

theorem canonical1771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1771 raw1771Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw1771 raw1771Labels = mixedMoment B raw1771step0 raw1771step0Labels := by
      have ha : raw1771step0 = (fun i j => raw1771 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1771step0 raw1771; decide +kernel
      have hl : raw1771step0Labels = raw1771Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1771 raw1771Labels permutation32 permutation4
    _ = mixedMoment B node2058 node2058Labels := by rfl

theorem canonical1772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1772 raw1772Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw1772 raw1772Labels = mixedMoment B raw1772step0 raw1772step0Labels := by
      have ha : raw1772step0 = (fun i j => raw1772 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1772step0 raw1772; decide +kernel
      have hl : raw1772step0Labels = raw1772Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1772 raw1772Labels permutation36 permutation6
    mixedMoment B raw1772step0 raw1772step0Labels = mixedMoment B raw1772step1 raw1772step1Labels := by
      have ha : raw1772step1 = -raw1772step0 := by apply Matrix.ext; change ∀ i j, raw1772step1 i j = -(raw1772step0 i j); unfold raw1772step1 raw1772step0; decide +kernel
      have hl : raw1772step1Labels = raw1772step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1772step1 raw1772step1Labels = mixedMoment B raw1772step2 raw1772step2Labels := by
      have ha : raw1772step2 = raw1772step1 := by apply Matrix.ext; unfold raw1772step2 raw1772step1; decide +kernel
      have hl : raw1772step1Labels = labelEmbedding1 ∘ raw1772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1772step1 raw1772step1Labels raw1772step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

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

theorem canonical1818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1818 raw1818Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw1818 raw1818Labels = mixedMoment B raw1818step0 raw1818step0Labels := by
      have ha : raw1818step0 = (fun i j => raw1818 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1818step0 raw1818; decide +kernel
      have hl : raw1818step0Labels = raw1818Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1818 raw1818Labels permutation32 permutation4
    mixedMoment B raw1818step0 raw1818step0Labels = mixedMoment B raw1818step1 raw1818step1Labels := by
      have ha : raw1818step1 = raw1818step0 := by apply Matrix.ext; unfold raw1818step1 raw1818step0; decide +kernel
      have hl : raw1818step0Labels = labelEmbedding7 ∘ raw1818step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1818step0 raw1818step0Labels raw1818step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical1819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1819 raw1819Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw1819 raw1819Labels = mixedMoment B raw1819step0 raw1819step0Labels := by
      have ha : raw1819step0 = (fun i j => raw1819 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1819step0 raw1819; decide +kernel
      have hl : raw1819step0Labels = raw1819Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1819 raw1819Labels permutation32 permutation4
    _ = mixedMoment B node2245 node2245Labels := by rfl

theorem canonical1820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1820 raw1820Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw1820 raw1820Labels = mixedMoment B raw1820step0 raw1820step0Labels := by
      have ha : raw1820step0 = (fun i j => raw1820 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1820step0 raw1820; decide +kernel
      have hl : raw1820step0Labels = raw1820Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1820 raw1820Labels permutation50 permutation6
    mixedMoment B raw1820step0 raw1820step0Labels = mixedMoment B raw1820step1 raw1820step1Labels := by
      have ha : raw1820step1 = -raw1820step0 := by apply Matrix.ext; change ∀ i j, raw1820step1 i j = -(raw1820step0 i j); unfold raw1820step1 raw1820step0; decide +kernel
      have hl : raw1820step1Labels = raw1820step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1820step1 raw1820step1Labels = mixedMoment B raw1820step2 raw1820step2Labels := by
      have ha : raw1820step2 = raw1820step1 := by apply Matrix.ext; unfold raw1820step2 raw1820step1; decide +kernel
      have hl : raw1820step1Labels = labelEmbedding1 ∘ raw1820step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1820step1 raw1820step1Labels raw1820step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

theorem canonical1824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1824 raw1824Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw1824 raw1824Labels = mixedMoment B raw1824step0 raw1824step0Labels := by
      have ha : raw1824step0 = (fun i j => raw1824 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1824step0 raw1824; decide +kernel
      have hl : raw1824step0Labels = raw1824Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1824 raw1824Labels permutation8 permutation4
    mixedMoment B raw1824step0 raw1824step0Labels = mixedMoment B raw1824step1 raw1824step1Labels := by
      have ha : raw1824step1 = raw1824step0 := by apply Matrix.ext; unfold raw1824step1 raw1824step0; decide +kernel
      have hl : raw1824step0Labels = labelEmbedding7 ∘ raw1824step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1824step0 raw1824step0Labels raw1824step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

theorem canonical1825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1825 raw1825Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw1825 raw1825Labels = mixedMoment B raw1825step0 raw1825step0Labels := by
      have ha : raw1825step0 = (fun i j => raw1825 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1825step0 raw1825; decide +kernel
      have hl : raw1825step0Labels = raw1825Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1825 raw1825Labels permutation8 permutation4
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical1826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1826 raw1826Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw1826 raw1826Labels = mixedMoment B raw1826step0 raw1826step0Labels := by
      have ha : raw1826step0 = (fun i j => raw1826 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1826step0 raw1826; decide +kernel
      have hl : raw1826step0Labels = raw1826Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1826 raw1826Labels permutation12 permutation6
    mixedMoment B raw1826step0 raw1826step0Labels = mixedMoment B raw1826step1 raw1826step1Labels := by
      have ha : raw1826step1 = -raw1826step0 := by apply Matrix.ext; change ∀ i j, raw1826step1 i j = -(raw1826step0 i j); unfold raw1826step1 raw1826step0; decide +kernel
      have hl : raw1826step1Labels = raw1826step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1826step1 raw1826step1Labels = mixedMoment B raw1826step2 raw1826step2Labels := by
      have ha : raw1826step2 = raw1826step1 := by apply Matrix.ext; unfold raw1826step2 raw1826step1; decide +kernel
      have hl : raw1826step1Labels = labelEmbedding1 ∘ raw1826step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1826step1 raw1826step1Labels raw1826step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2278 node2278Labels := by rfl

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

theorem canonical2304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2304 raw2304Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw2304 raw2304Labels = mixedMoment B raw2304step0 raw2304step0Labels := by
      have ha : raw2304step0 = (fun i j => raw2304 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2304step0 raw2304; decide +kernel
      have hl : raw2304step0Labels = raw2304Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2304 raw2304Labels permutation8 permutation4
    mixedMoment B raw2304step0 raw2304step0Labels = mixedMoment B raw2304step1 raw2304step1Labels := by
      have ha : raw2304step1 = raw2304step0 := by apply Matrix.ext; unfold raw2304step1 raw2304step0; decide +kernel
      have hl : raw2304step0Labels = labelEmbedding7 ∘ raw2304step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2304step0 raw2304step0Labels raw2304step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

theorem canonical2305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2305 raw2305Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw2305 raw2305Labels = mixedMoment B raw2305step0 raw2305step0Labels := by
      have ha : raw2305step0 = (fun i j => raw2305 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2305step0 raw2305; decide +kernel
      have hl : raw2305step0Labels = raw2305Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2305 raw2305Labels permutation8 permutation4
    _ = mixedMoment B node2768 node2768Labels := by rfl

theorem canonical2306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2306 raw2306Labels = mixedMoment B node3632 node3632Labels := by
  calc
    mixedMoment B raw2306 raw2306Labels = mixedMoment B raw2306step0 raw2306step0Labels := by
      have ha : raw2306step0 = (fun i j => raw2306 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2306step0 raw2306; decide +kernel
      have hl : raw2306step0Labels = raw2306Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2306 raw2306Labels permutation12 permutation6
    mixedMoment B raw2306step0 raw2306step0Labels = mixedMoment B raw2306step1 raw2306step1Labels := by
      have ha : raw2306step1 = -raw2306step0 := by apply Matrix.ext; change ∀ i j, raw2306step1 i j = -(raw2306step0 i j); unfold raw2306step1 raw2306step0; decide +kernel
      have hl : raw2306step1Labels = raw2306step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2306step1 raw2306step1Labels = mixedMoment B raw2306step2 raw2306step2Labels := by
      have ha : raw2306step2 = raw2306step1 := by apply Matrix.ext; unfold raw2306step2 raw2306step1; decide +kernel
      have hl : raw2306step1Labels = labelEmbedding1 ∘ raw2306step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2306step1 raw2306step1Labels raw2306step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3632 node3632Labels := by rfl

theorem canonical2313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2313 raw2313Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw2313 raw2313Labels = mixedMoment B raw2313step0 raw2313step0Labels := by
      have ha : raw2313step0 = (fun i j => raw2313 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2313step0 raw2313; decide +kernel
      have hl : raw2313step0Labels = raw2313Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2313 raw2313Labels permutation8 permutation5
    mixedMoment B raw2313step0 raw2313step0Labels = mixedMoment B raw2313step1 raw2313step1Labels := by
      have ha : raw2313step1 = raw2313step0 := by apply Matrix.ext; unfold raw2313step1 raw2313step0; decide +kernel
      have hl : raw2313step0Labels = labelEmbedding8 ∘ raw2313step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2313step0 raw2313step0Labels raw2313step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

theorem canonical2314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2314 raw2314Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw2314 raw2314Labels = mixedMoment B raw2314step0 raw2314step0Labels := by
      have ha : raw2314step0 = (fun i j => raw2314 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2314step0 raw2314; decide +kernel
      have hl : raw2314step0Labels = raw2314Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2314 raw2314Labels permutation8 permutation4
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical2315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2315 raw2315Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw2315 raw2315Labels = mixedMoment B raw2315step0 raw2315step0Labels := by
      have ha : raw2315step0 = (fun i j => raw2315 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2315step0 raw2315; decide +kernel
      have hl : raw2315step0Labels = raw2315Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2315 raw2315Labels permutation11 permutation3
    mixedMoment B raw2315step0 raw2315step0Labels = mixedMoment B raw2315step1 raw2315step1Labels := by
      have ha : raw2315step1 = -raw2315step0 := by apply Matrix.ext; change ∀ i j, raw2315step1 i j = -(raw2315step0 i j); unfold raw2315step1 raw2315step0; decide +kernel
      have hl : raw2315step1Labels = raw2315step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2315step1 raw2315step1Labels = mixedMoment B raw2315step2 raw2315step2Labels := by
      have ha : raw2315step2 = raw2315step1 := by apply Matrix.ext; unfold raw2315step2 raw2315step1; decide +kernel
      have hl : raw2315step1Labels = labelEmbedding1 ∘ raw2315step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2315step1 raw2315step1Labels raw2315step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3626 node3626Labels := by rfl

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

theorem canonical272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw272 raw272Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw272 raw272Labels = mixedMoment B raw272step0 raw272step0Labels := by
      have ha : raw272step0 = (fun i j => raw272 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw272step0 raw272; decide +kernel
      have hl : raw272step0Labels = raw272Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw272 raw272Labels permutation8 permutation5
    mixedMoment B raw272step0 raw272step0Labels = mixedMoment B raw272step1 raw272step1Labels := by
      have ha : raw272step1 = raw272step0 := by apply Matrix.ext; unfold raw272step1 raw272step0; decide +kernel
      have hl : raw272step0Labels = labelEmbedding1 ∘ raw272step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw272step0 raw272step0Labels raw272step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2768 node2768Labels := by rfl

theorem canonical273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw273 raw273Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw273 raw273Labels = mixedMoment B raw273step0 raw273step0Labels := by
      have ha : raw273step0 = (fun i j => raw273 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw273step0 raw273; decide +kernel
      have hl : raw273step0Labels = raw273Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw273 raw273Labels permutation8 permutation5
    _ = mixedMoment B node405 node405Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10702 raw10702Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw10702 raw10702Labels = mixedMoment B raw10702step0 raw10702step0Labels := by
      have hz : ∀ j, raw10702 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10702step0 = (fun i j => raw10702 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10702step0 raw10702; decide +kernel
      have hl : raw10702step0Labels = raw10702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10702 raw10702Labels permutation434 hz
    mixedMoment B raw10702step0 raw10702step0Labels = mixedMoment B raw10702step1 raw10702step1Labels := by
      have hz : ∀ j, raw10702step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10702step1 = (fun i j => raw10702step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10702step1 raw10702step0; decide +kernel
      have hl : raw10702step1Labels = raw10702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10702step0 raw10702step0Labels permutation80 hz
    mixedMoment B raw10702step1 raw10702step1Labels = mixedMoment B raw10702step2 raw10702step2Labels := by
      have ha : raw10702step2 = (fun i j => raw10702step1 (permutation16 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10702step2 raw10702step1; decide +kernel
      have hl : raw10702step2Labels = raw10702step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10702step1 raw10702step1Labels permutation16 permutation4
    mixedMoment B raw10702step2 raw10702step2Labels = mixedMoment B raw10702step3 raw10702step3Labels := by
      have ha : raw10702step3 = -raw10702step2 := by apply Matrix.ext; change ∀ i j, raw10702step3 i j = -(raw10702step2 i j); unfold raw10702step3 raw10702step2; decide +kernel
      have hl : raw10702step3Labels = raw10702step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10702step3 raw10702step3Labels = mixedMoment B raw10702step4 raw10702step4Labels := by
      have ha : raw10702step4 = raw10702step3 := by apply Matrix.ext; unfold raw10702step4 raw10702step3; decide +kernel
      have hl : raw10702step3Labels = labelEmbedding7 ∘ raw10702step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10702step3 raw10702step3Labels raw10702step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

theorem canonical10703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10703 raw10703Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw10703 raw10703Labels = mixedMoment B raw10703step0 raw10703step0Labels := by
      have hz : ∀ j, raw10703 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10703step0 = (fun i j => raw10703 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10703step0 raw10703; decide +kernel
      have hl : raw10703step0Labels = raw10703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10703 raw10703Labels permutation434 hz
    mixedMoment B raw10703step0 raw10703step0Labels = mixedMoment B raw10703step1 raw10703step1Labels := by
      have ha : raw10703step1 = (fun i j => raw10703step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10703step1 raw10703step0; decide +kernel
      have hl : raw10703step1Labels = raw10703step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10703step0 raw10703step0Labels permutation43 permutation7
    mixedMoment B raw10703step1 raw10703step1Labels = mixedMoment B raw10703step2 raw10703step2Labels := by
      have ha : raw10703step2 = -raw10703step1 := by apply Matrix.ext; change ∀ i j, raw10703step2 i j = -(raw10703step1 i j); unfold raw10703step2 raw10703step1; decide +kernel
      have hl : raw10703step2Labels = raw10703step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10703step2 raw10703step2Labels = mixedMoment B raw10703step3 raw10703step3Labels := by
      have ha : raw10703step3 = raw10703step2 := by apply Matrix.ext; unfold raw10703step3 raw10703step2; decide +kernel
      have hl : raw10703step2Labels = labelEmbedding10 ∘ raw10703step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10703step2 raw10703step2Labels raw10703step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

theorem canonical10704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10704 raw10704Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw10704 raw10704Labels = mixedMoment B raw10704step0 raw10704step0Labels := by
      have hz : ∀ j, raw10704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10704step0 = (fun i j => raw10704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10704step0 raw10704; decide +kernel
      have hl : raw10704step0Labels = raw10704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10704 raw10704Labels permutation346 hz
    mixedMoment B raw10704step0 raw10704step0Labels = mixedMoment B raw10704step1 raw10704step1Labels := by
      have ha : raw10704step1 = (fun i j => raw10704step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10704step1 raw10704step0; decide +kernel
      have hl : raw10704step1Labels = raw10704step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10704step0 raw10704step0Labels permutation43 permutation7
    mixedMoment B raw10704step1 raw10704step1Labels = mixedMoment B raw10704step2 raw10704step2Labels := by
      have ha : raw10704step2 = -raw10704step1 := by apply Matrix.ext; change ∀ i j, raw10704step2 i j = -(raw10704step1 i j); unfold raw10704step2 raw10704step1; decide +kernel
      have hl : raw10704step2Labels = raw10704step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10704step2 raw10704step2Labels = mixedMoment B raw10704step3 raw10704step3Labels := by
      have ha : raw10704step3 = raw10704step2 := by apply Matrix.ext; unfold raw10704step3 raw10704step2; decide +kernel
      have hl : raw10704step2Labels = labelEmbedding10 ∘ raw10704step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10704step2 raw10704step2Labels raw10704step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

theorem canonical10705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10705 raw10705Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw10705 raw10705Labels = mixedMoment B raw10705step0 raw10705step0Labels := by
      have hz : ∀ j, raw10705 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10705step0 = (fun i j => raw10705 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10705step0 raw10705; decide +kernel
      have hl : raw10705step0Labels = raw10705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10705 raw10705Labels permutation434 hz
    mixedMoment B raw10705step0 raw10705step0Labels = mixedMoment B raw10705step1 raw10705step1Labels := by
      have hz : ∀ j, raw10705step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10705step1 = (fun i j => raw10705step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10705step1 raw10705step0; decide +kernel
      have hl : raw10705step1Labels = raw10705step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10705step0 raw10705step0Labels permutation80 hz
    mixedMoment B raw10705step1 raw10705step1Labels = mixedMoment B raw10705step2 raw10705step2Labels := by
      have ha : raw10705step2 = (fun i j => raw10705step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10705step2 raw10705step1; decide +kernel
      have hl : raw10705step2Labels = raw10705step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10705step1 raw10705step1Labels permutation13 permutation7
    mixedMoment B raw10705step2 raw10705step2Labels = mixedMoment B raw10705step3 raw10705step3Labels := by
      have ha : raw10705step3 = -raw10705step2 := by apply Matrix.ext; change ∀ i j, raw10705step3 i j = -(raw10705step2 i j); unfold raw10705step3 raw10705step2; decide +kernel
      have hl : raw10705step3Labels = raw10705step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10705step3 raw10705step3Labels = mixedMoment B raw10705step4 raw10705step4Labels := by
      have ha : raw10705step4 = raw10705step3 := by apply Matrix.ext; unfold raw10705step4 raw10705step3; decide +kernel
      have hl : raw10705step3Labels = labelEmbedding10 ∘ raw10705step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10705step3 raw10705step3Labels raw10705step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

theorem canonical10706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10706 raw10706Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw10706 raw10706Labels = mixedMoment B raw10706step0 raw10706step0Labels := by
      have hz : ∀ j, raw10706 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10706step0 = (fun i j => raw10706 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10706step0 raw10706; decide +kernel
      have hl : raw10706step0Labels = raw10706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10706 raw10706Labels permutation434 hz
    mixedMoment B raw10706step0 raw10706step0Labels = mixedMoment B raw10706step1 raw10706step1Labels := by
      have hz : ∀ j, raw10706step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10706step1 = (fun i j => raw10706step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10706step1 raw10706step0; decide +kernel
      have hl : raw10706step1Labels = raw10706step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10706step0 raw10706step0Labels permutation80 hz
    mixedMoment B raw10706step1 raw10706step1Labels = mixedMoment B raw10706step2 raw10706step2Labels := by
      have ha : raw10706step2 = (fun i j => raw10706step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10706step2 raw10706step1; decide +kernel
      have hl : raw10706step2Labels = raw10706step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10706step1 raw10706step1Labels permutation13 permutation7
    mixedMoment B raw10706step2 raw10706step2Labels = mixedMoment B raw10706step3 raw10706step3Labels := by
      have ha : raw10706step3 = -raw10706step2 := by apply Matrix.ext; change ∀ i j, raw10706step3 i j = -(raw10706step2 i j); unfold raw10706step3 raw10706step2; decide +kernel
      have hl : raw10706step3Labels = raw10706step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10706step3 raw10706step3Labels = mixedMoment B raw10706step4 raw10706step4Labels := by
      have ha : raw10706step4 = raw10706step3 := by apply Matrix.ext; unfold raw10706step4 raw10706step3; decide +kernel
      have hl : raw10706step3Labels = labelEmbedding10 ∘ raw10706step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10706step3 raw10706step3Labels raw10706step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

theorem canonical10707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10707 raw10707Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw10707 raw10707Labels = mixedMoment B raw10707step0 raw10707step0Labels := by
      have hz : ∀ j, raw10707 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10707step0 = (fun i j => raw10707 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10707step0 raw10707; decide +kernel
      have hl : raw10707step0Labels = raw10707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10707 raw10707Labels permutation434 hz
    mixedMoment B raw10707step0 raw10707step0Labels = mixedMoment B raw10707step1 raw10707step1Labels := by
      have hz : ∀ j, raw10707step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10707step1 = (fun i j => raw10707step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10707step1 raw10707step0; decide +kernel
      have hl : raw10707step1Labels = raw10707step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10707step0 raw10707step0Labels permutation80 hz
    mixedMoment B raw10707step1 raw10707step1Labels = mixedMoment B raw10707step2 raw10707step2Labels := by
      have ha : raw10707step2 = (fun i j => raw10707step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10707step2 raw10707step1; decide +kernel
      have hl : raw10707step2Labels = raw10707step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10707step1 raw10707step1Labels permutation10 permutation2
    _ = mixedMoment B node4503 node4503Labels := by rfl

theorem canonical10708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10708 raw10708Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw10708 raw10708Labels = mixedMoment B raw10708step0 raw10708step0Labels := by
      have hz : ∀ j, raw10708 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10708step0 = (fun i j => raw10708 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10708step0 raw10708; decide +kernel
      have hl : raw10708step0Labels = raw10708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10708 raw10708Labels permutation434 hz
    mixedMoment B raw10708step0 raw10708step0Labels = mixedMoment B raw10708step1 raw10708step1Labels := by
      have ha : raw10708step1 = (fun i j => raw10708step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10708step1 raw10708step0; decide +kernel
      have hl : raw10708step1Labels = raw10708step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10708step0 raw10708step0Labels permutation40 permutation2
    _ = mixedMoment B node4839 node4839Labels := by rfl

theorem canonical10709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10709 raw10709Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw10709 raw10709Labels = mixedMoment B raw10709step0 raw10709step0Labels := by
      have hz : ∀ j, raw10709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10709step0 = (fun i j => raw10709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10709step0 raw10709; decide +kernel
      have hl : raw10709step0Labels = raw10709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10709 raw10709Labels permutation346 hz
    mixedMoment B raw10709step0 raw10709step0Labels = mixedMoment B raw10709step1 raw10709step1Labels := by
      have ha : raw10709step1 = (fun i j => raw10709step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10709step1 raw10709step0; decide +kernel
      have hl : raw10709step1Labels = raw10709step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10709step0 raw10709step0Labels permutation40 permutation2
    _ = mixedMoment B node4839 node4839Labels := by rfl

theorem canonical10710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10710 raw10710Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw10710 raw10710Labels = mixedMoment B raw10710step0 raw10710step0Labels := by
      have hz : ∀ j, raw10710 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10710step0 = (fun i j => raw10710 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10710step0 raw10710; decide +kernel
      have hl : raw10710step0Labels = raw10710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10710 raw10710Labels permutation434 hz
    mixedMoment B raw10710step0 raw10710step0Labels = mixedMoment B raw10710step1 raw10710step1Labels := by
      have hz : ∀ j, raw10710step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10710step1 = (fun i j => raw10710step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10710step1 raw10710step0; decide +kernel
      have hl : raw10710step1Labels = raw10710step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10710step0 raw10710step0Labels permutation80 hz
    mixedMoment B raw10710step1 raw10710step1Labels = mixedMoment B raw10710step2 raw10710step2Labels := by
      have ha : raw10710step2 = (fun i j => raw10710step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10710step2 raw10710step1; decide +kernel
      have hl : raw10710step2Labels = raw10710step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10710step1 raw10710step1Labels permutation10 permutation2
    _ = mixedMoment B node4896 node4896Labels := by rfl

theorem canonical10711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10711 raw10711Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw10711 raw10711Labels = mixedMoment B raw10711step0 raw10711step0Labels := by
      have hz : ∀ j, raw10711 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10711step0 = (fun i j => raw10711 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10711step0 raw10711; decide +kernel
      have hl : raw10711step0Labels = raw10711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10711 raw10711Labels permutation434 hz
    mixedMoment B raw10711step0 raw10711step0Labels = mixedMoment B raw10711step1 raw10711step1Labels := by
      have hz : ∀ j, raw10711step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10711step1 = (fun i j => raw10711step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10711step1 raw10711step0; decide +kernel
      have hl : raw10711step1Labels = raw10711step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10711step0 raw10711step0Labels permutation80 hz
    mixedMoment B raw10711step1 raw10711step1Labels = mixedMoment B raw10711step2 raw10711step2Labels := by
      have ha : raw10711step2 = (fun i j => raw10711step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10711step2 raw10711step1; decide +kernel
      have hl : raw10711step2Labels = raw10711step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10711step1 raw10711step1Labels permutation13 permutation7
    mixedMoment B raw10711step2 raw10711step2Labels = mixedMoment B raw10711step3 raw10711step3Labels := by
      have ha : raw10711step3 = -raw10711step2 := by apply Matrix.ext; change ∀ i j, raw10711step3 i j = -(raw10711step2 i j); unfold raw10711step3 raw10711step2; decide +kernel
      have hl : raw10711step3Labels = raw10711step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10711step3 raw10711step3Labels = mixedMoment B raw10711step4 raw10711step4Labels := by
      have ha : raw10711step4 = raw10711step3 := by apply Matrix.ext; unfold raw10711step4 raw10711step3; decide +kernel
      have hl : raw10711step3Labels = labelEmbedding10 ∘ raw10711step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10711step3 raw10711step3Labels raw10711step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

theorem canonical10712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10712 raw10712Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw10712 raw10712Labels = mixedMoment B raw10712step0 raw10712step0Labels := by
      have hz : ∀ j, raw10712 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10712step0 = (fun i j => raw10712 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10712step0 raw10712; decide +kernel
      have hl : raw10712step0Labels = raw10712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10712 raw10712Labels permutation434 hz
    _ = mixedMoment B node4475 node4475Labels := by rfl

theorem canonical10713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10713 raw10713Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw10713 raw10713Labels = mixedMoment B raw10713step0 raw10713step0Labels := by
      have hz : ∀ j, raw10713 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10713step0 = (fun i j => raw10713 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10713step0 raw10713; decide +kernel
      have hl : raw10713step0Labels = raw10713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10713 raw10713Labels permutation434 hz
    _ = mixedMoment B node4880 node4880Labels := by rfl

theorem canonical10714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10714 raw10714Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw10714 raw10714Labels = mixedMoment B raw10714step0 raw10714step0Labels := by
      have ha : raw10714step0 = (fun i j => raw10714 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10714step0 raw10714; decide +kernel
      have hl : raw10714step0Labels = raw10714Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10714 raw10714Labels permutation200 permutation2
    _ = mixedMoment B node4816 node4816Labels := by rfl

theorem canonical10715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10715 raw10715Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw10715 raw10715Labels = mixedMoment B raw10715step0 raw10715step0Labels := by
      have hz : ∀ j, raw10715 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10715step0 = (fun i j => raw10715 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10715step0 raw10715; decide +kernel
      have hl : raw10715step0Labels = raw10715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10715 raw10715Labels permutation434 hz
    mixedMoment B raw10715step0 raw10715step0Labels = mixedMoment B raw10715step1 raw10715step1Labels := by
      have ha : raw10715step1 = (fun i j => raw10715step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10715step1 raw10715step0; decide +kernel
      have hl : raw10715step1Labels = raw10715step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10715step0 raw10715step0Labels permutation44 permutation2
    _ = mixedMoment B node4891 node4891Labels := by rfl

theorem canonical10716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10716 raw10716Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw10716 raw10716Labels = mixedMoment B raw10716step0 raw10716step0Labels := by
      have hz : ∀ j, raw10716 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10716step0 = (fun i j => raw10716 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10716step0 raw10716; decide +kernel
      have hl : raw10716step0Labels = raw10716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10716 raw10716Labels permutation434 hz
    mixedMoment B raw10716step0 raw10716step0Labels = mixedMoment B raw10716step1 raw10716step1Labels := by
      have ha : raw10716step1 = (fun i j => raw10716step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10716step1 raw10716step0; decide +kernel
      have hl : raw10716step1Labels = raw10716step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10716step0 raw10716step0Labels permutation43 permutation7
    mixedMoment B raw10716step1 raw10716step1Labels = mixedMoment B raw10716step2 raw10716step2Labels := by
      have ha : raw10716step2 = -raw10716step1 := by apply Matrix.ext; change ∀ i j, raw10716step2 i j = -(raw10716step1 i j); unfold raw10716step2 raw10716step1; decide +kernel
      have hl : raw10716step2Labels = raw10716step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10716step2 raw10716step2Labels = mixedMoment B raw10716step3 raw10716step3Labels := by
      have ha : raw10716step3 = raw10716step2 := by apply Matrix.ext; unfold raw10716step3 raw10716step2; decide +kernel
      have hl : raw10716step2Labels = labelEmbedding10 ∘ raw10716step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10716step2 raw10716step2Labels raw10716step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical10717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10717 raw10717Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw10717 raw10717Labels = mixedMoment B raw10717step0 raw10717step0Labels := by
      have hz : ∀ j, raw10717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10717step0 = (fun i j => raw10717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10717step0 raw10717; decide +kernel
      have hl : raw10717step0Labels = raw10717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10717 raw10717Labels permutation346 hz
    _ = mixedMoment B node4475 node4475Labels := by rfl

theorem canonical10718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10718 raw10718Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw10718 raw10718Labels = mixedMoment B raw10718step0 raw10718step0Labels := by
      have hz : ∀ j, raw10718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10718step0 = (fun i j => raw10718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10718step0 raw10718; decide +kernel
      have hl : raw10718step0Labels = raw10718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10718 raw10718Labels permutation346 hz
    _ = mixedMoment B node4880 node4880Labels := by rfl

theorem canonical10719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10719 raw10719Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw10719 raw10719Labels = mixedMoment B raw10719step0 raw10719step0Labels := by
      have ha : raw10719step0 = (fun i j => raw10719 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10719step0 raw10719; decide +kernel
      have hl : raw10719step0Labels = raw10719Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10719 raw10719Labels permutation176 permutation2
    _ = mixedMoment B node4816 node4816Labels := by rfl

theorem canonical10720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10720 raw10720Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw10720 raw10720Labels = mixedMoment B raw10720step0 raw10720step0Labels := by
      have hz : ∀ j, raw10720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10720step0 = (fun i j => raw10720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10720step0 raw10720; decide +kernel
      have hl : raw10720step0Labels = raw10720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10720 raw10720Labels permutation346 hz
    mixedMoment B raw10720step0 raw10720step0Labels = mixedMoment B raw10720step1 raw10720step1Labels := by
      have ha : raw10720step1 = (fun i j => raw10720step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10720step1 raw10720step0; decide +kernel
      have hl : raw10720step1Labels = raw10720step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10720step0 raw10720step0Labels permutation44 permutation2
    _ = mixedMoment B node4891 node4891Labels := by rfl

theorem canonical10721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10721 raw10721Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw10721 raw10721Labels = mixedMoment B raw10721step0 raw10721step0Labels := by
      have hz : ∀ j, raw10721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10721step0 = (fun i j => raw10721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10721step0 raw10721; decide +kernel
      have hl : raw10721step0Labels = raw10721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10721 raw10721Labels permutation346 hz
    mixedMoment B raw10721step0 raw10721step0Labels = mixedMoment B raw10721step1 raw10721step1Labels := by
      have ha : raw10721step1 = (fun i j => raw10721step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10721step1 raw10721step0; decide +kernel
      have hl : raw10721step1Labels = raw10721step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10721step0 raw10721step0Labels permutation43 permutation7
    mixedMoment B raw10721step1 raw10721step1Labels = mixedMoment B raw10721step2 raw10721step2Labels := by
      have ha : raw10721step2 = -raw10721step1 := by apply Matrix.ext; change ∀ i j, raw10721step2 i j = -(raw10721step1 i j); unfold raw10721step2 raw10721step1; decide +kernel
      have hl : raw10721step2Labels = raw10721step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10721step2 raw10721step2Labels = mixedMoment B raw10721step3 raw10721step3Labels := by
      have ha : raw10721step3 = raw10721step2 := by apply Matrix.ext; unfold raw10721step3 raw10721step2; decide +kernel
      have hl : raw10721step2Labels = labelEmbedding10 ∘ raw10721step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10721step2 raw10721step2Labels raw10721step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

theorem canonical10722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10722 raw10722Labels = mixedMoment B node4480 node4480Labels := by
  calc
    mixedMoment B raw10722 raw10722Labels = mixedMoment B raw10722step0 raw10722step0Labels := by
      have hz : ∀ j, raw10722 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10722step0 = (fun i j => raw10722 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10722step0 raw10722; decide +kernel
      have hl : raw10722step0Labels = raw10722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10722 raw10722Labels permutation434 hz
    mixedMoment B raw10722step0 raw10722step0Labels = mixedMoment B raw10722step1 raw10722step1Labels := by
      have hz : ∀ j, raw10722step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10722step1 = (fun i j => raw10722step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10722step1 raw10722step0; decide +kernel
      have hl : raw10722step1Labels = raw10722step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10722step0 raw10722step0Labels permutation80 hz
    mixedMoment B raw10722step1 raw10722step1Labels = mixedMoment B raw10722step2 raw10722step2Labels := by
      have ha : raw10722step2 = (fun i j => raw10722step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10722step2 raw10722step1; decide +kernel
      have hl : raw10722step2Labels = raw10722step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10722step1 raw10722step1Labels permutation9 permutation2
    _ = mixedMoment B node4480 node4480Labels := by rfl

theorem canonical10723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10723 raw10723Labels = mixedMoment B node4884 node4884Labels := by
  calc
    mixedMoment B raw10723 raw10723Labels = mixedMoment B raw10723step0 raw10723step0Labels := by
      have hz : ∀ j, raw10723 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10723step0 = (fun i j => raw10723 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10723step0 raw10723; decide +kernel
      have hl : raw10723step0Labels = raw10723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10723 raw10723Labels permutation434 hz
    mixedMoment B raw10723step0 raw10723step0Labels = mixedMoment B raw10723step1 raw10723step1Labels := by
      have hz : ∀ j, raw10723step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10723step1 = (fun i j => raw10723step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10723step1 raw10723step0; decide +kernel
      have hl : raw10723step1Labels = raw10723step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10723step0 raw10723step0Labels permutation80 hz
    mixedMoment B raw10723step1 raw10723step1Labels = mixedMoment B raw10723step2 raw10723step2Labels := by
      have ha : raw10723step2 = (fun i j => raw10723step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10723step2 raw10723step1; decide +kernel
      have hl : raw10723step2Labels = raw10723step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10723step1 raw10723step1Labels permutation9 permutation2
    _ = mixedMoment B node4884 node4884Labels := by rfl

theorem canonical10724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10724 raw10724Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw10724 raw10724Labels = mixedMoment B raw10724step0 raw10724step0Labels := by
      have hz : ∀ j, raw10724 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10724step0 = (fun i j => raw10724 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10724step0 raw10724; decide +kernel
      have hl : raw10724step0Labels = raw10724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10724 raw10724Labels permutation434 hz
    mixedMoment B raw10724step0 raw10724step0Labels = mixedMoment B raw10724step1 raw10724step1Labels := by
      have ha : raw10724step1 = (fun i j => raw10724step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10724step1 raw10724step0; decide +kernel
      have hl : raw10724step1Labels = raw10724step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10724step0 raw10724step0Labels permutation39 permutation2
    _ = mixedMoment B node4821 node4821Labels := by rfl

theorem canonical10725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10725 raw10725Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw10725 raw10725Labels = mixedMoment B raw10725step0 raw10725step0Labels := by
      have hz : ∀ j, raw10725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10725step0 = (fun i j => raw10725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10725step0 raw10725; decide +kernel
      have hl : raw10725step0Labels = raw10725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10725 raw10725Labels permutation346 hz
    mixedMoment B raw10725step0 raw10725step0Labels = mixedMoment B raw10725step1 raw10725step1Labels := by
      have ha : raw10725step1 = (fun i j => raw10725step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10725step1 raw10725step0; decide +kernel
      have hl : raw10725step1Labels = raw10725step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10725step0 raw10725step0Labels permutation39 permutation2
    _ = mixedMoment B node4821 node4821Labels := by rfl

theorem canonical10726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10726 raw10726Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw10726 raw10726Labels = mixedMoment B raw10726step0 raw10726step0Labels := by
      have hz : ∀ j, raw10726 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10726step0 = (fun i j => raw10726 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10726step0 raw10726; decide +kernel
      have hl : raw10726step0Labels = raw10726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10726 raw10726Labels permutation434 hz
    mixedMoment B raw10726step0 raw10726step0Labels = mixedMoment B raw10726step1 raw10726step1Labels := by
      have hz : ∀ j, raw10726step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10726step1 = (fun i j => raw10726step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10726step1 raw10726step0; decide +kernel
      have hl : raw10726step1Labels = raw10726step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10726step0 raw10726step0Labels permutation80 hz
    mixedMoment B raw10726step1 raw10726step1Labels = mixedMoment B raw10726step2 raw10726step2Labels := by
      have ha : raw10726step2 = (fun i j => raw10726step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10726step2 raw10726step1; decide +kernel
      have hl : raw10726step2Labels = raw10726step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10726step1 raw10726step1Labels permutation13 permutation7
    mixedMoment B raw10726step2 raw10726step2Labels = mixedMoment B raw10726step3 raw10726step3Labels := by
      have ha : raw10726step3 = -raw10726step2 := by apply Matrix.ext; change ∀ i j, raw10726step3 i j = -(raw10726step2 i j); unfold raw10726step3 raw10726step2; decide +kernel
      have hl : raw10726step3Labels = raw10726step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10726step3 raw10726step3Labels = mixedMoment B raw10726step4 raw10726step4Labels := by
      have ha : raw10726step4 = raw10726step3 := by apply Matrix.ext; unfold raw10726step4 raw10726step3; decide +kernel
      have hl : raw10726step3Labels = labelEmbedding10 ∘ raw10726step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10726step3 raw10726step3Labels raw10726step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

theorem canonical10727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10727 raw10727Labels = mixedMoment B node4478 node4478Labels := by
  calc
    mixedMoment B raw10727 raw10727Labels = mixedMoment B raw10727step0 raw10727step0Labels := by
      have hz : ∀ j, raw10727 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10727step0 = (fun i j => raw10727 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10727step0 raw10727; decide +kernel
      have hl : raw10727step0Labels = raw10727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10727 raw10727Labels permutation434 hz
    mixedMoment B raw10727step0 raw10727step0Labels = mixedMoment B raw10727step1 raw10727step1Labels := by
      have hz : ∀ j, raw10727step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10727step1 = (fun i j => raw10727step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10727step1 raw10727step0; decide +kernel
      have hl : raw10727step1Labels = raw10727step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10727step0 raw10727step0Labels permutation80 hz
    _ = mixedMoment B node4478 node4478Labels := by rfl

theorem canonical10728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10728 raw10728Labels = mixedMoment B node4844 node4844Labels := by
  calc
    mixedMoment B raw10728 raw10728Labels = mixedMoment B raw10728step0 raw10728step0Labels := by
      have hz : ∀ j, raw10728 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10728step0 = (fun i j => raw10728 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10728step0 raw10728; decide +kernel
      have hl : raw10728step0Labels = raw10728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10728 raw10728Labels permutation434 hz
    mixedMoment B raw10728step0 raw10728step0Labels = mixedMoment B raw10728step1 raw10728step1Labels := by
      have hz : ∀ j, raw10728step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10728step1 = (fun i j => raw10728step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10728step1 raw10728step0; decide +kernel
      have hl : raw10728step1Labels = raw10728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10728step0 raw10728step0Labels permutation80 hz
    mixedMoment B raw10728step1 raw10728step1Labels = mixedMoment B raw10728step2 raw10728step2Labels := by
      have ha : raw10728step2 = (fun i j => raw10728step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10728step2 raw10728step1; decide +kernel
      have hl : raw10728step2Labels = raw10728step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10728step1 raw10728step1Labels permutation31 permutation3
    mixedMoment B raw10728step2 raw10728step2Labels = mixedMoment B raw10728step3 raw10728step3Labels := by
      have ha : raw10728step3 = -raw10728step2 := by apply Matrix.ext; change ∀ i j, raw10728step3 i j = -(raw10728step2 i j); unfold raw10728step3 raw10728step2; decide +kernel
      have hl : raw10728step3Labels = raw10728step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10728step3 raw10728step3Labels = mixedMoment B raw10728step4 raw10728step4Labels := by
      have ha : raw10728step4 = raw10728step3 := by apply Matrix.ext; unfold raw10728step4 raw10728step3; decide +kernel
      have hl : raw10728step3Labels = labelEmbedding6 ∘ raw10728step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10728step3 raw10728step3Labels raw10728step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4844 node4844Labels := by rfl

theorem canonical10729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10729 raw10729Labels = mixedMoment B node4819 node4819Labels := by
  calc
    mixedMoment B raw10729 raw10729Labels = mixedMoment B raw10729step0 raw10729step0Labels := by
      have hz : ∀ j, raw10729 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10729step0 = (fun i j => raw10729 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10729step0 raw10729; decide +kernel
      have hl : raw10729step0Labels = raw10729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10729 raw10729Labels permutation434 hz
    mixedMoment B raw10729step0 raw10729step0Labels = mixedMoment B raw10729step1 raw10729step1Labels := by
      have ha : raw10729step1 = (fun i j => raw10729step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10729step1 raw10729step0; decide +kernel
      have hl : raw10729step1Labels = raw10729step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10729step0 raw10729step0Labels permutation38 permutation2
    _ = mixedMoment B node4819 node4819Labels := by rfl

theorem canonical10730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10730 raw10730Labels = mixedMoment B node4819 node4819Labels := by
  calc
    mixedMoment B raw10730 raw10730Labels = mixedMoment B raw10730step0 raw10730step0Labels := by
      have hz : ∀ j, raw10730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10730step0 = (fun i j => raw10730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10730step0 raw10730; decide +kernel
      have hl : raw10730step0Labels = raw10730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10730 raw10730Labels permutation346 hz
    mixedMoment B raw10730step0 raw10730step0Labels = mixedMoment B raw10730step1 raw10730step1Labels := by
      have ha : raw10730step1 = (fun i j => raw10730step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10730step1 raw10730step0; decide +kernel
      have hl : raw10730step1Labels = raw10730step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10730step0 raw10730step0Labels permutation38 permutation2
    _ = mixedMoment B node4819 node4819Labels := by rfl

theorem canonical10731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10731 raw10731Labels = mixedMoment B node4892 node4892Labels := by
  calc
    mixedMoment B raw10731 raw10731Labels = mixedMoment B raw10731step0 raw10731step0Labels := by
      have hz : ∀ j, raw10731 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10731step0 = (fun i j => raw10731 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10731step0 raw10731; decide +kernel
      have hl : raw10731step0Labels = raw10731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10731 raw10731Labels permutation434 hz
    mixedMoment B raw10731step0 raw10731step0Labels = mixedMoment B raw10731step1 raw10731step1Labels := by
      have hz : ∀ j, raw10731step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10731step1 = (fun i j => raw10731step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10731step1 raw10731step0; decide +kernel
      have hl : raw10731step1Labels = raw10731step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10731step0 raw10731step0Labels permutation80 hz
    mixedMoment B raw10731step1 raw10731step1Labels = mixedMoment B raw10731step2 raw10731step2Labels := by
      have ha : raw10731step2 = (fun i j => raw10731step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10731step2 raw10731step1; decide +kernel
      have hl : raw10731step2Labels = raw10731step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10731step1 raw10731step1Labels permutation10 permutation2
    _ = mixedMoment B node4892 node4892Labels := by rfl

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

theorem canonical5204 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5204 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw5204 = injectiveMoment H raw5204step0 := by
      have hz : ∀ j, raw5204 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw5204step0 = (fun i j => raw5204 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5204 permutation27 hz
    _ = injectiveMoment H node11 := by rfl

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

theorem canonical7671 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7671 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7671 = injectiveMoment H raw7671step0 := by
      have hz : ∀ j, raw7671 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw7671step0 = (fun i j => raw7671 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7671 permutation21 hz
    injectiveMoment H raw7671step0 = injectiveMoment H raw7671step1 := by
      have heq : raw7671step1 = (fun i j => raw7671step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7671step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

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

theorem canonical782 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw782 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw782 = injectiveMoment H raw782step0 := by
      have heq : raw782step0 = -raw782 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw782).symm
    injectiveMoment H raw782step0 = injectiveMoment H raw782step1 := by
      have heq : raw782step1 = (fun i j => raw782step0 (permutation13 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw782step0 permutation13 permutation8
    _ = injectiveMoment H node185 := by rfl

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

theorem sound57 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node57 = Sparse.eval value57 (momentVector H) := by
  have heq : pivotMatrix57 = (fun u v => node57 (pivotPermutation57 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node57 = injectiveMoment H pivotMatrix57 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix57 0 = Pi.single (0 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix57 0 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix57 (1 : Fin 2) = raw5990 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5990 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node57 + (injectiveMoment H (mergeFirst pivotMatrix57 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix57 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value57, value10, value4, Sparse.eval] at hc ⊢
  linarith

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

theorem canonical2863 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2863 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw2863 = injectiveMoment H raw2863step0 := by
      have heq : raw2863step0 = (fun i j => raw2863 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2863 permutation4 permutation5
    _ = injectiveMoment H node56 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical186
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5979 = injectiveMoment H node57 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2845 = injectiveMoment H node36 := by
  rfl

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

theorem sound185 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node185 = Sparse.eval value185 (momentVector H) := by
  have heq : pivotMatrix185 = (fun u v => node185 (pivotPermutation185 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node185 = injectiveMoment H pivotMatrix185 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix185 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix185 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (0 : Fin 3) = raw5979 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5979 hH).trans (sound57 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) =
      Sparse.eval value56 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (1 : Fin 3) = raw2863 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2863 hH).trans (sound56 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix185 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node185 + (injectiveMoment H (mergeFirst pivotMatrix185 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix185 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value185, value36, value56, value57, Sparse.eval] at hc ⊢
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

theorem singlePair405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node405 node405Labels = Sparse.eval singlePairValue405 (familyPairVector B) := by
  have hp := single_label_three B hB node405
  have hl : node405Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node405 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 1) = PairSemantics.raw5204 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node405 PairSemantics.raw5204; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5204 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 2) = PairSemantics.raw7671 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node405 PairSemantics.raw7671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7671 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value10 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 3) = PairSemantics.raw895 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node405 PairSemantics.raw895; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical895 hH).trans (PairSemantics.sound10 hH)
  have hm4 : familyPairMoment B (groupedColumns node405 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value185 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node405 (EqualityPatterns.family3.label 4) = PairSemantics.raw782 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node405 PairSemantics.raw782; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical782 hH).trans (PairSemantics.sound185 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue405, PairSemantics.value0, PairSemantics.value10, PairSemantics.value11, PairSemantics.value185, Sparse.eval] at hp ⊢
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

theorem singleton2768 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2768 node2768Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node405 node405Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw272 singletonSmall2768
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2768) = raw272Labels := by decide +kernel
  rw [hl, canonical272 B hB] at h
  have hc0 : mixedMoment B raw272 (Fin.cases (0 : Fin 1) singletonSmall2768) =
      mixedMoment B node405 node405Labels := by
    have ha : raw272 = raw273 := by apply Matrix.ext; unfold raw272 raw273; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2768 = raw273Labels := by decide +kernel
    rw [ha, hj, canonical273 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  rw [hc0] at h
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

theorem singleton4839 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4839 node4839Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2058 node2058Labels + mixedMoment B node2216 node2216Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1770 singletonSmall4839
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4839) = raw1770Labels := by decide +kernel
  rw [hl, canonical1770 B hB] at h
  have hc0 : mixedMoment B raw1770 (Fin.cases (0 : Fin 2) singletonSmall4839) =
      mixedMoment B node2058 node2058Labels := by
    have ha : raw1770 = raw1771 := by apply Matrix.ext; unfold raw1770 raw1771; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4839 = raw1771Labels := by decide +kernel
    rw [ha, hj, canonical1771 B hB]
  have hc1 : mixedMoment B raw1770 (Fin.cases (1 : Fin 2) singletonSmall4839) =
      mixedMoment B node2216 node2216Labels := by
    have ha : raw1770 = raw1772 := by apply Matrix.ext; unfold raw1770 raw1772; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4839 = raw1772Labels := by decide +kernel
    rw [ha, hj, canonical1772 B hB]
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

theorem singleton4889 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4889 node4889Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2245 node2245Labels + mixedMoment B node2277 node2277Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1818 singletonSmall4889
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4889) = raw1818Labels := by decide +kernel
  rw [hl, canonical1818 B hB] at h
  have hc0 : mixedMoment B raw1818 (Fin.cases (0 : Fin 2) singletonSmall4889) =
      mixedMoment B node2245 node2245Labels := by
    have ha : raw1818 = raw1819 := by apply Matrix.ext; unfold raw1818 raw1819; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4889 = raw1819Labels := by decide +kernel
    rw [ha, hj, canonical1819 B hB]
  have hc1 : mixedMoment B raw1818 (Fin.cases (1 : Fin 2) singletonSmall4889) =
      mixedMoment B node2277 node2277Labels := by
    have ha : raw1818 = raw1820 := by apply Matrix.ext; unfold raw1818 raw1820; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4889 = raw1820Labels := by decide +kernel
    rw [ha, hj, canonical1820 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4896 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4896 node4896Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2266 node2266Labels + mixedMoment B node2278 node2278Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1824 singletonSmall4896
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4896) = raw1824Labels := by decide +kernel
  rw [hl, canonical1824 B hB] at h
  have hc0 : mixedMoment B raw1824 (Fin.cases (0 : Fin 2) singletonSmall4896) =
      mixedMoment B node2266 node2266Labels := by
    have ha : raw1824 = raw1825 := by apply Matrix.ext; unfold raw1824 raw1825; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4896 = raw1825Labels := by decide +kernel
    rw [ha, hj, canonical1825 B hB]
  have hc1 : mixedMoment B raw1824 (Fin.cases (1 : Fin 2) singletonSmall4896) =
      mixedMoment B node2278 node2278Labels := by
    have ha : raw1824 = raw1826 := by apply Matrix.ext; unfold raw1824 raw1826; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4896 = raw1826Labels := by decide +kernel
    rw [ha, hj, canonical1826 B hB]
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

theorem singleton5294 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5294 node5294Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2768 node2768Labels + mixedMoment B node3632 node3632Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2304 singletonSmall5294
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5294) = raw2304Labels := by decide +kernel
  rw [hl, canonical2304 B hB] at h
  have hc0 : mixedMoment B raw2304 (Fin.cases (0 : Fin 2) singletonSmall5294) =
      mixedMoment B node2768 node2768Labels := by
    have ha : raw2304 = raw2305 := by apply Matrix.ext; unfold raw2304 raw2305; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5294 = raw2305Labels := by decide +kernel
    rw [ha, hj, canonical2305 B hB]
  have hc1 : mixedMoment B raw2304 (Fin.cases (1 : Fin 2) singletonSmall5294) =
      mixedMoment B node3632 node3632Labels := by
    have ha : raw2304 = raw2306 := by apply Matrix.ext; unfold raw2304 raw2306; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5294 = raw2306Labels := by decide +kernel
    rw [ha, hj, canonical2306 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5302 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5302 node5302Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3054 node3054Labels + mixedMoment B node3626 node3626Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2313 singletonSmall5302
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5302) = raw2313Labels := by decide +kernel
  rw [hl, canonical2313 B hB] at h
  have hc0 : mixedMoment B raw2313 (Fin.cases (0 : Fin 2) singletonSmall5302) =
      mixedMoment B node3054 node3054Labels := by
    have ha : raw2313 = raw2314 := by apply Matrix.ext; unfold raw2313 raw2314; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5302 = raw2314Labels := by decide +kernel
    rw [ha, hj, canonical2314 B hB]
  have hc1 : mixedMoment B raw2313 (Fin.cases (1 : Fin 2) singletonSmall5302) =
      mixedMoment B node3626 node3626Labels := by
    have ha : raw2313 = raw2315 := by apply Matrix.ext; unfold raw2313 raw2315; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5302 = raw2315Labels := by decide +kernel
    rw [ha, hj, canonical2315 B hB]
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

theorem sound3054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3054 node3054Labels = Sparse.eval nodeValue3054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3054) = mixedMoment B node3054 node3054Labels := rfl
  simpa [nodeValue3054, Sparse.eval] using hc.symm

theorem sound3626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3626 node3626Labels = Sparse.eval nodeValue3626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3626) = mixedMoment B node3626 node3626Labels := rfl
  simpa [nodeValue3626, Sparse.eval] using hc.symm

theorem sound5302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5302 node5302Labels = Sparse.eval nodeValue5302 (mixedVector B) := by
  have h := singleton5302 B _hB
  rw [sound3054 B _hB _hF, sound3626 B _hB _hF] at h
  norm_num [nodeValue5302, nodeValue3054, nodeValue3626, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound1087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1087 node1087Labels = Sparse.eval nodeValue1087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1087) = mixedMoment B node1087 node1087Labels := rfl
  simpa [nodeValue1087, Sparse.eval] using hc.symm

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

theorem sound2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2058 node2058Labels = Sparse.eval nodeValue2058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2058) = mixedMoment B node2058 node2058Labels := rfl
  simpa [nodeValue2058, Sparse.eval] using hc.symm

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

theorem sound2216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2216 node2216Labels = Sparse.eval nodeValue2216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2216) = mixedMoment B node2216 node2216Labels := rfl
  simpa [nodeValue2216, Sparse.eval] using hc.symm

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

theorem sound2245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2245 node2245Labels = Sparse.eval nodeValue2245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2245) = mixedMoment B node2245 node2245Labels := rfl
  simpa [nodeValue2245, Sparse.eval] using hc.symm

theorem sound2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2266 node2266Labels = Sparse.eval nodeValue2266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2266) = mixedMoment B node2266 node2266Labels := rfl
  simpa [nodeValue2266, Sparse.eval] using hc.symm

theorem sound2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2277 node2277Labels = Sparse.eval nodeValue2277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2277) = mixedMoment B node2277 node2277Labels := rfl
  simpa [nodeValue2277, Sparse.eval] using hc.symm

theorem sound2278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2278 node2278Labels = Sparse.eval nodeValue2278 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2278) = mixedMoment B node2278 node2278Labels := rfl
  simpa [nodeValue2278, Sparse.eval] using hc.symm

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

theorem sound405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node405 node405Labels = Sparse.eval nodeValue405 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue405 (familyPairVector B) := singlePair405 B _hB
    _ = _ := by
      norm_num [singlePairValue405, nodeValue405, Sparse.eval, mixedVector]
      ring

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

theorem sound2768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2768 node2768Labels = Sparse.eval nodeValue2768 (mixedVector B) := by
  have h := singleton2768 B _hB
  rw [sound405 B _hB _hF] at h
  norm_num [nodeValue2768, nodeValue405, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound3632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3632 node3632Labels = Sparse.eval nodeValue3632 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3632) = mixedMoment B node3632 node3632Labels := rfl
  simpa [nodeValue3632, Sparse.eval] using hc.symm

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

theorem sound4475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4475 node4475Labels = Sparse.eval nodeValue4475 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4475) = mixedMoment B node4475 node4475Labels := rfl
  simpa [nodeValue4475, Sparse.eval] using hc.symm

theorem sound4478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4478 node4478Labels = Sparse.eval nodeValue4478 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4478) = mixedMoment B node4478 node4478Labels := rfl
  simpa [nodeValue4478, Sparse.eval] using hc.symm

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

theorem sound4480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4480 node4480Labels = Sparse.eval nodeValue4480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4480) = mixedMoment B node4480 node4480Labels := rfl
  simpa [nodeValue4480, Sparse.eval] using hc.symm

theorem sound4503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4503 node4503Labels = Sparse.eval nodeValue4503 (mixedVector B) := by
  have h := singleton4503 B _hB
  rw [sound1087 B _hB _hF, sound1739 B _hB _hF] at h
  norm_num [nodeValue4503, nodeValue1087, nodeValue1739, Sparse.eval] at h ⊢
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

theorem sound4816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4816 node4816Labels = Sparse.eval nodeValue4816 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4816) = mixedMoment B node4816 node4816Labels := rfl
  simpa [nodeValue4816, Sparse.eval] using hc.symm

theorem sound4819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4819 node4819Labels = Sparse.eval nodeValue4819 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4819) = mixedMoment B node4819 node4819Labels := rfl
  simpa [nodeValue4819, Sparse.eval] using hc.symm

theorem sound4821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4821 node4821Labels = Sparse.eval nodeValue4821 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4821) = mixedMoment B node4821 node4821Labels := rfl
  simpa [nodeValue4821, Sparse.eval] using hc.symm

theorem sound4839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4839 node4839Labels = Sparse.eval nodeValue4839 (mixedVector B) := by
  have h := singleton4839 B _hB
  rw [sound2058 B _hB _hF, sound2216 B _hB _hF] at h
  norm_num [nodeValue4839, nodeValue2058, nodeValue2216, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4844 node4844Labels = Sparse.eval nodeValue4844 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4844) = mixedMoment B node4844 node4844Labels := rfl
  simpa [nodeValue4844, Sparse.eval] using hc.symm

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

theorem sound4880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4880 node4880Labels = Sparse.eval nodeValue4880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4880) = mixedMoment B node4880 node4880Labels := rfl
  simpa [nodeValue4880, Sparse.eval] using hc.symm

theorem sound4884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4884 node4884Labels = Sparse.eval nodeValue4884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4884) = mixedMoment B node4884 node4884Labels := rfl
  simpa [nodeValue4884, Sparse.eval] using hc.symm

theorem sound4889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4889 node4889Labels = Sparse.eval nodeValue4889 (mixedVector B) := by
  have h := singleton4889 B _hB
  rw [sound2245 B _hB _hF, sound2277 B _hB _hF] at h
  norm_num [nodeValue4889, nodeValue2245, nodeValue2277, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4891 node4891Labels = Sparse.eval nodeValue4891 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4891) = mixedMoment B node4891 node4891Labels := rfl
  simpa [nodeValue4891, Sparse.eval] using hc.symm

theorem sound4892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4892 node4892Labels = Sparse.eval nodeValue4892 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4892) = mixedMoment B node4892 node4892Labels := rfl
  simpa [nodeValue4892, Sparse.eval] using hc.symm

theorem sound4895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4895 node4895Labels = Sparse.eval nodeValue4895 (mixedVector B) := by
  simpa only [nodeValue4895, Sparse.eval_nil] using zero4895 B _hB _hF

theorem sound4896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4896 node4896Labels = Sparse.eval nodeValue4896 (mixedVector B) := by
  have h := singleton4896 B _hB
  rw [sound2266 B _hB _hF, sound2278 B _hB _hF] at h
  norm_num [nodeValue4896, nodeValue2266, nodeValue2278, Sparse.eval] at h ⊢
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

theorem sound5267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5267 node5267Labels = Sparse.eval nodeValue5267 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5267) = mixedMoment B node5267 node5267Labels := rfl
  simpa [nodeValue5267, Sparse.eval] using hc.symm

theorem sound5276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5276 node5276Labels = Sparse.eval nodeValue5276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5276) = mixedMoment B node5276 node5276Labels := rfl
  simpa [nodeValue5276, Sparse.eval] using hc.symm

theorem sound5294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5294 node5294Labels = Sparse.eval nodeValue5294 (mixedVector B) := by
  have h := singleton5294 B _hB
  rw [sound2768 B _hB _hF, sound3632 B _hB _hF] at h
  norm_num [nodeValue5294, nodeValue2768, nodeValue3632, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources19
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq633 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm633 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA633 + difference 0 1) (sourceB633 + difference 1 0) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA633 + difference 0 1) (sourceB633 + difference 1 0) sourceC633) = raw10702 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10702; decide +kernel
    rw [ha]
    exact (canonical10702 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA633 + difference 0 2) (sourceB633 + difference 2 0) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA633 + difference 0 2) (sourceB633 + difference 2 0) sourceC633) = raw10703 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10703; decide +kernel
    rw [ha]
    exact (canonical10703 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA633 + difference 0 3) (sourceB633 + difference 3 0) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA633 + difference 0 3) (sourceB633 + difference 3 0) sourceC633) = raw10704 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10704; decide +kernel
    rw [ha]
    exact (canonical10704 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA633 + difference 0 4) (sourceB633 + difference 4 0) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA633 + difference 0 4) (sourceB633 + difference 4 0) sourceC633) = raw10705 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10705; decide +kernel
    rw [ha]
    exact (canonical10705 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA633 + difference 0 5) (sourceB633 + difference 5 0) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA633 + difference 0 5) (sourceB633 + difference 5 0) sourceC633) = raw10706 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10706; decide +kernel
    rw [ha]
    exact (canonical10706 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA633 + difference 1 0) (sourceB633 + difference 0 1) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA633 + difference 1 0) (sourceB633 + difference 0 1) sourceC633) = raw10707 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10707; decide +kernel
    rw [ha]
    exact (canonical10707 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA633 + difference 1 2) (sourceB633 + difference 2 1) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA633 + difference 1 2) (sourceB633 + difference 2 1) sourceC633) = raw10708 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10708; decide +kernel
    rw [ha]
    exact (canonical10708 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA633 + difference 1 3) (sourceB633 + difference 3 1) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA633 + difference 1 3) (sourceB633 + difference 3 1) sourceC633) = raw10709 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10709; decide +kernel
    rw [ha]
    exact (canonical10709 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA633 + difference 1 4) (sourceB633 + difference 4 1) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA633 + difference 1 4) (sourceB633 + difference 4 1) sourceC633) = raw10710 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10710; decide +kernel
    rw [ha]
    exact (canonical10710 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA633 + difference 1 5) (sourceB633 + difference 5 1) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA633 + difference 1 5) (sourceB633 + difference 5 1) sourceC633) = raw10711 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10711; decide +kernel
    rw [ha]
    exact (canonical10711 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA633 + difference 2 0) (sourceB633 + difference 0 2) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4475) := by
    have ha : (tripleCharges (sourceA633 + difference 2 0) (sourceB633 + difference 0 2) sourceC633) = raw10712 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10712; decide +kernel
    rw [ha]
    exact (canonical10712 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA633 + difference 2 1) (sourceB633 + difference 1 2) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA633 + difference 2 1) (sourceB633 + difference 1 2) sourceC633) = raw10713 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10713; decide +kernel
    rw [ha]
    exact (canonical10713 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA633 + difference 2 3) (sourceB633 + difference 3 2) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA633 + difference 2 3) (sourceB633 + difference 3 2) sourceC633) = raw10714 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10714; decide +kernel
    rw [ha]
    exact (canonical10714 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA633 + difference 2 4) (sourceB633 + difference 4 2) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA633 + difference 2 4) (sourceB633 + difference 4 2) sourceC633) = raw10715 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10715; decide +kernel
    rw [ha]
    exact (canonical10715 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA633 + difference 2 5) (sourceB633 + difference 5 2) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA633 + difference 2 5) (sourceB633 + difference 5 2) sourceC633) = raw10716 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10716; decide +kernel
    rw [ha]
    exact (canonical10716 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA633 + difference 3 0) (sourceB633 + difference 0 3) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4475) := by
    have ha : (tripleCharges (sourceA633 + difference 3 0) (sourceB633 + difference 0 3) sourceC633) = raw10717 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10717; decide +kernel
    rw [ha]
    exact (canonical10717 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA633 + difference 3 1) (sourceB633 + difference 1 3) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA633 + difference 3 1) (sourceB633 + difference 1 3) sourceC633) = raw10718 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10718; decide +kernel
    rw [ha]
    exact (canonical10718 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA633 + difference 3 2) (sourceB633 + difference 2 3) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA633 + difference 3 2) (sourceB633 + difference 2 3) sourceC633) = raw10719 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10719; decide +kernel
    rw [ha]
    exact (canonical10719 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA633 + difference 3 4) (sourceB633 + difference 4 3) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA633 + difference 3 4) (sourceB633 + difference 4 3) sourceC633) = raw10720 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10720; decide +kernel
    rw [ha]
    exact (canonical10720 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA633 + difference 3 5) (sourceB633 + difference 5 3) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA633 + difference 3 5) (sourceB633 + difference 5 3) sourceC633) = raw10721 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10721; decide +kernel
    rw [ha]
    exact (canonical10721 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA633 + difference 4 0) (sourceB633 + difference 0 4) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4480) := by
    have ha : (tripleCharges (sourceA633 + difference 4 0) (sourceB633 + difference 0 4) sourceC633) = raw10722 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10722; decide +kernel
    rw [ha]
    exact (canonical10722 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA633 + difference 4 1) (sourceB633 + difference 1 4) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4884) := by
    have ha : (tripleCharges (sourceA633 + difference 4 1) (sourceB633 + difference 1 4) sourceC633) = raw10723 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10723; decide +kernel
    rw [ha]
    exact (canonical10723 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA633 + difference 4 2) (sourceB633 + difference 2 4) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4821) := by
    have ha : (tripleCharges (sourceA633 + difference 4 2) (sourceB633 + difference 2 4) sourceC633) = raw10724 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10724; decide +kernel
    rw [ha]
    exact (canonical10724 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA633 + difference 4 3) (sourceB633 + difference 3 4) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4821) := by
    have ha : (tripleCharges (sourceA633 + difference 4 3) (sourceB633 + difference 3 4) sourceC633) = raw10725 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10725; decide +kernel
    rw [ha]
    exact (canonical10725 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA633 + difference 4 5) (sourceB633 + difference 5 4) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA633 + difference 4 5) (sourceB633 + difference 5 4) sourceC633) = raw10726 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10726; decide +kernel
    rw [ha]
    exact (canonical10726 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA633 + difference 5 0) (sourceB633 + difference 0 5) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4478) := by
    have ha : (tripleCharges (sourceA633 + difference 5 0) (sourceB633 + difference 0 5) sourceC633) = raw10727 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10727; decide +kernel
    rw [ha]
    exact (canonical10727 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA633 + difference 5 1) (sourceB633 + difference 1 5) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4844) := by
    have ha : (tripleCharges (sourceA633 + difference 5 1) (sourceB633 + difference 1 5) sourceC633) = raw10728 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10728; decide +kernel
    rw [ha]
    exact (canonical10728 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA633 + difference 5 2) (sourceB633 + difference 2 5) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4819) := by
    have ha : (tripleCharges (sourceA633 + difference 5 2) (sourceB633 + difference 2 5) sourceC633) = raw10729 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10729; decide +kernel
    rw [ha]
    exact (canonical10729 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA633 + difference 5 3) (sourceB633 + difference 3 5) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4819) := by
    have ha : (tripleCharges (sourceA633 + difference 5 3) (sourceB633 + difference 3 5) sourceC633) = raw10730 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10730; decide +kernel
    rw [ha]
    exact (canonical10730 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA633 + difference 5 4) (sourceB633 + difference 4 5) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA633 + difference 5 4) (sourceB633 + difference 4 5) sourceC633) = raw10731 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10731; decide +kernel
    rw [ha]
    exact (canonical10731 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA633 sourceB633 sourceC633
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm633, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck542 : Integer.Sparse.reindex keyMap MixedData.row542 = numericRow542 := by decide +kernel

theorem numericCheck542 (x : Master → ℝ) : Integer.Sparse.eval numericRow542 x =
    (8640 : ℝ) * reducedSource542 x := by
  norm_num [numericRow542, reducedSource542, Integer.Sparse.eval, Sparse.eval, nodeValue4475, nodeValue4478, nodeValue4480, nodeValue4503, nodeValue4816, nodeValue4819, nodeValue4821, nodeValue4839, nodeValue4844, nodeValue4880, nodeValue4884, nodeValue4889, nodeValue4891, nodeValue4892, nodeValue4895, nodeValue4896, nodeValue5267, nodeValue5276, nodeValue5294, nodeValue5302]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero542 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource542 (mixedVector B) = 0 := by
  have h4475 : mixedVector B (Sum.inr 4475) = Sparse.eval nodeValue4475 (mixedVector B) := by
    change mixedMoment B node4475 node4475Labels = _
    exact sound4475 B hB hF
  have h4478 : mixedVector B (Sum.inr 4478) = Sparse.eval nodeValue4478 (mixedVector B) := by
    change mixedMoment B node4478 node4478Labels = _
    exact sound4478 B hB hF
  have h4480 : mixedVector B (Sum.inr 4480) = Sparse.eval nodeValue4480 (mixedVector B) := by
    change mixedMoment B node4480 node4480Labels = _
    exact sound4480 B hB hF
  have h4503 : mixedVector B (Sum.inr 4503) = Sparse.eval nodeValue4503 (mixedVector B) := by
    change mixedMoment B node4503 node4503Labels = _
    exact sound4503 B hB hF
  have h4816 : mixedVector B (Sum.inr 4816) = Sparse.eval nodeValue4816 (mixedVector B) := by
    change mixedMoment B node4816 node4816Labels = _
    exact sound4816 B hB hF
  have h4819 : mixedVector B (Sum.inr 4819) = Sparse.eval nodeValue4819 (mixedVector B) := by
    change mixedMoment B node4819 node4819Labels = _
    exact sound4819 B hB hF
  have h4821 : mixedVector B (Sum.inr 4821) = Sparse.eval nodeValue4821 (mixedVector B) := by
    change mixedMoment B node4821 node4821Labels = _
    exact sound4821 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4844 : mixedVector B (Sum.inr 4844) = Sparse.eval nodeValue4844 (mixedVector B) := by
    change mixedMoment B node4844 node4844Labels = _
    exact sound4844 B hB hF
  have h4880 : mixedVector B (Sum.inr 4880) = Sparse.eval nodeValue4880 (mixedVector B) := by
    change mixedMoment B node4880 node4880Labels = _
    exact sound4880 B hB hF
  have h4884 : mixedVector B (Sum.inr 4884) = Sparse.eval nodeValue4884 (mixedVector B) := by
    change mixedMoment B node4884 node4884Labels = _
    exact sound4884 B hB hF
  have h4889 : mixedVector B (Sum.inr 4889) = Sparse.eval nodeValue4889 (mixedVector B) := by
    change mixedMoment B node4889 node4889Labels = _
    exact sound4889 B hB hF
  have h4891 : mixedVector B (Sum.inr 4891) = Sparse.eval nodeValue4891 (mixedVector B) := by
    change mixedMoment B node4891 node4891Labels = _
    exact sound4891 B hB hF
  have h4892 : mixedVector B (Sum.inr 4892) = Sparse.eval nodeValue4892 (mixedVector B) := by
    change mixedMoment B node4892 node4892Labels = _
    exact sound4892 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  have h4896 : mixedVector B (Sum.inr 4896) = Sparse.eval nodeValue4896 (mixedVector B) := by
    change mixedMoment B node4896 node4896Labels = _
    exact sound4896 B hB hF
  have h5267 : mixedVector B (Sum.inr 5267) = Sparse.eval nodeValue5267 (mixedVector B) := by
    change mixedMoment B node5267 node5267Labels = _
    exact sound5267 B hB hF
  have h5276 : mixedVector B (Sum.inr 5276) = Sparse.eval nodeValue5276 (mixedVector B) := by
    change mixedMoment B node5276 node5276Labels = _
    exact sound5276 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  have h5302 : mixedVector B (Sum.inr 5302) = Sparse.eval nodeValue5302 (mixedVector B) := by
    change mixedMoment B node5302 node5302Labels = _
    exact sound5302 B hB hF
  simpa only [sourceForm633, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4475, h4478, h4480, h4503, h4816, h4819, h4821, h4839, h4844, h4880, h4884, h4889, h4891, h4892, h4895, h4896, h5267, h5276, h5294, h5302, reducedSource542] using sourceEq633 B hB

theorem rowSound542_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row542 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck542, numericCheck542, reducedZero542 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound542_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound542_e_oai
