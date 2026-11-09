-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T20:52:24.279818+00:00
-- url     : https://prove2.me/submissions/dd5c7e36-cfbd-4238-bdae-5bc270f54d34

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw246 raw246Labels = mixedMoment B node2604 node2604Labels := by
  calc
    mixedMoment B raw246 raw246Labels = mixedMoment B raw246step0 raw246step0Labels := by
      have ha : raw246step0 = (fun i j => raw246 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw246step0 raw246; decide +kernel
      have hl : raw246step0Labels = raw246Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw246 raw246Labels permutation8 permutation5
    mixedMoment B raw246step0 raw246step0Labels = mixedMoment B raw246step1 raw246step1Labels := by
      have ha : raw246step1 = raw246step0 := by apply Matrix.ext; unfold raw246step1 raw246step0; decide +kernel
      have hl : raw246step0Labels = labelEmbedding1 ∘ raw246step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw246step0 raw246step0Labels raw246step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2604 node2604Labels := by rfl

theorem canonical247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw247 raw247Labels = mixedMoment B node343 node343Labels := by
  calc
    mixedMoment B raw247 raw247Labels = mixedMoment B raw247step0 raw247step0Labels := by
      have ha : raw247step0 = (fun i j => raw247 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw247step0 raw247; decide +kernel
      have hl : raw247step0Labels = raw247Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw247 raw247Labels permutation8 permutation5
    _ = mixedMoment B node343 node343Labels := by rfl

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

theorem canonical1287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1287 raw1287Labels = mixedMoment B node4491 node4491Labels := by
  calc
    mixedMoment B raw1287 raw1287Labels = mixedMoment B raw1287step0 raw1287step0Labels := by
      have ha : raw1287step0 = (fun i j => raw1287 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1287step0 raw1287; decide +kernel
      have hl : raw1287step0Labels = raw1287Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1287 raw1287Labels permutation8 permutation4
    mixedMoment B raw1287step0 raw1287step0Labels = mixedMoment B raw1287step1 raw1287step1Labels := by
      have ha : raw1287step1 = raw1287step0 := by apply Matrix.ext; unfold raw1287step1 raw1287step0; decide +kernel
      have hl : raw1287step0Labels = labelEmbedding7 ∘ raw1287step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1287step0 raw1287step0Labels raw1287step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4491 node4491Labels := by rfl

theorem canonical1288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1288 raw1288Labels = mixedMoment B node1075 node1075Labels := by
  calc
    mixedMoment B raw1288 raw1288Labels = mixedMoment B raw1288step0 raw1288step0Labels := by
      have ha : raw1288step0 = (fun i j => raw1288 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1288step0 raw1288; decide +kernel
      have hl : raw1288step0Labels = raw1288Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1288 raw1288Labels permutation8 permutation4
    _ = mixedMoment B node1075 node1075Labels := by rfl

theorem canonical1289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1289 raw1289Labels = mixedMoment B node1653 node1653Labels := by
  calc
    mixedMoment B raw1289 raw1289Labels = mixedMoment B raw1289step0 raw1289step0Labels := by
      have ha : raw1289step0 = (fun i j => raw1289 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1289step0 raw1289; decide +kernel
      have hl : raw1289step0Labels = raw1289Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1289 raw1289Labels permutation8 permutation6
    mixedMoment B raw1289step0 raw1289step0Labels = mixedMoment B raw1289step1 raw1289step1Labels := by
      have ha : raw1289step1 = -raw1289step0 := by apply Matrix.ext; change ∀ i j, raw1289step1 i j = -(raw1289step0 i j); unfold raw1289step1 raw1289step0; decide +kernel
      have hl : raw1289step1Labels = raw1289step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1289step1 raw1289step1Labels = mixedMoment B raw1289step2 raw1289step2Labels := by
      have ha : raw1289step2 = raw1289step1 := by apply Matrix.ext; unfold raw1289step2 raw1289step1; decide +kernel
      have hl : raw1289step1Labels = labelEmbedding1 ∘ raw1289step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1289step1 raw1289step1Labels raw1289step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1653 node1653Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13587 raw13587Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw13587 raw13587Labels = mixedMoment B raw13587step0 raw13587step0Labels := by
      have hz : ∀ j, raw13587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13587step0 = (fun i j => raw13587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13587step0 raw13587; decide +kernel
      have hl : raw13587step0Labels = raw13587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13587 raw13587Labels permutation346 hz
    mixedMoment B raw13587step0 raw13587step0Labels = mixedMoment B raw13587step1 raw13587step1Labels := by
      have ha : raw13587step1 = (fun i j => raw13587step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13587step1 raw13587step0; decide +kernel
      have hl : raw13587step1Labels = raw13587step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13587step0 raw13587step0Labels permutation36 permutation3
    mixedMoment B raw13587step1 raw13587step1Labels = mixedMoment B raw13587step2 raw13587step2Labels := by
      have ha : raw13587step2 = raw13587step1 := by apply Matrix.ext; unfold raw13587step2 raw13587step1; decide +kernel
      have hl : raw13587step1Labels = labelEmbedding6 ∘ raw13587step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13587step1 raw13587step1Labels raw13587step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

theorem canonical13591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13591 raw13591Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw13591 raw13591Labels = mixedMoment B raw13591step0 raw13591step0Labels := by
      have hz : ∀ j, raw13591 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13591step0 = (fun i j => raw13591 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13591step0 raw13591; decide +kernel
      have hl : raw13591step0Labels = raw13591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13591 raw13591Labels permutation346 hz
    mixedMoment B raw13591step0 raw13591step0Labels = mixedMoment B raw13591step1 raw13591step1Labels := by
      have ha : raw13591step1 = (fun i j => raw13591step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13591step1 raw13591step0; decide +kernel
      have hl : raw13591step1Labels = raw13591step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13591step0 raw13591step0Labels permutation32 permutation3
    mixedMoment B raw13591step1 raw13591step1Labels = mixedMoment B raw13591step2 raw13591step2Labels := by
      have ha : raw13591step2 = raw13591step1 := by apply Matrix.ext; unfold raw13591step2 raw13591step1; decide +kernel
      have hl : raw13591step1Labels = labelEmbedding6 ∘ raw13591step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13591step1 raw13591step1Labels raw13591step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical138
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17694 raw17694Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw17694 raw17694Labels = mixedMoment B raw17694step0 raw17694step0Labels := by
      have hz : ∀ j, raw17694 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17694step0 = (fun i j => raw17694 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17694step0 raw17694; decide +kernel
      have hl : raw17694step0Labels = raw17694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17694 raw17694Labels permutation434 hz
    mixedMoment B raw17694step0 raw17694step0Labels = mixedMoment B raw17694step1 raw17694step1Labels := by
      have hz : ∀ j, raw17694step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17694step1 = (fun i j => raw17694step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17694step1 raw17694step0; decide +kernel
      have hl : raw17694step1Labels = raw17694step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17694step0 raw17694step0Labels permutation80 hz
    mixedMoment B raw17694step1 raw17694step1Labels = mixedMoment B raw17694step2 raw17694step2Labels := by
      have ha : raw17694step2 = (fun i j => raw17694step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17694step2 raw17694step1; decide +kernel
      have hl : raw17694step2Labels = raw17694step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17694step1 raw17694step1Labels permutation9 permutation3
    mixedMoment B raw17694step2 raw17694step2Labels = mixedMoment B raw17694step3 raw17694step3Labels := by
      have ha : raw17694step3 = raw17694step2 := by apply Matrix.ext; unfold raw17694step3 raw17694step2; decide +kernel
      have hl : raw17694step2Labels = labelEmbedding6 ∘ raw17694step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17694step2 raw17694step2Labels raw17694step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

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

theorem canonical2106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2106 raw2106Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw2106 raw2106Labels = mixedMoment B raw2106step0 raw2106step0Labels := by
      have ha : raw2106step0 = (fun i j => raw2106 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2106step0 raw2106; decide +kernel
      have hl : raw2106step0Labels = raw2106Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2106 raw2106Labels permutation32 permutation4
    mixedMoment B raw2106step0 raw2106step0Labels = mixedMoment B raw2106step1 raw2106step1Labels := by
      have ha : raw2106step1 = raw2106step0 := by apply Matrix.ext; unfold raw2106step1 raw2106step0; decide +kernel
      have hl : raw2106step0Labels = labelEmbedding7 ∘ raw2106step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2106step0 raw2106step0Labels raw2106step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

theorem canonical2107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2107 raw2107Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw2107 raw2107Labels = mixedMoment B raw2107step0 raw2107step0Labels := by
      have ha : raw2107step0 = (fun i j => raw2107 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2107step0 raw2107; decide +kernel
      have hl : raw2107step0Labels = raw2107Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2107 raw2107Labels permutation32 permutation4
    _ = mixedMoment B node2488 node2488Labels := by rfl

theorem canonical2108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2108 raw2108Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw2108 raw2108Labels = mixedMoment B raw2108step0 raw2108step0Labels := by
      have ha : raw2108step0 = (fun i j => raw2108 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2108step0 raw2108; decide +kernel
      have hl : raw2108step0Labels = raw2108Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2108 raw2108Labels permutation34 permutation6
    mixedMoment B raw2108step0 raw2108step0Labels = mixedMoment B raw2108step1 raw2108step1Labels := by
      have ha : raw2108step1 = -raw2108step0 := by apply Matrix.ext; change ∀ i j, raw2108step1 i j = -(raw2108step0 i j); unfold raw2108step1 raw2108step0; decide +kernel
      have hl : raw2108step1Labels = raw2108step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2108step1 raw2108step1Labels = mixedMoment B raw2108step2 raw2108step2Labels := by
      have ha : raw2108step2 = raw2108step1 := by apply Matrix.ext; unfold raw2108step2 raw2108step1; decide +kernel
      have hl : raw2108step1Labels = labelEmbedding1 ∘ raw2108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2108step1 raw2108step1Labels raw2108step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical165
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21243 raw21243Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw21243 raw21243Labels = mixedMoment B raw21243step0 raw21243step0Labels := by
      have hz : ∀ j, raw21243 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21243step0 = (fun i j => raw21243 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21243step0 raw21243; decide +kernel
      have hl : raw21243step0Labels = raw21243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21243 raw21243Labels permutation434 hz
    mixedMoment B raw21243step0 raw21243step0Labels = mixedMoment B raw21243step1 raw21243step1Labels := by
      have hz : ∀ j, raw21243step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21243step1 = (fun i j => raw21243step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21243step1 raw21243step0; decide +kernel
      have hl : raw21243step1Labels = raw21243step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21243step0 raw21243step0Labels permutation80 hz
    mixedMoment B raw21243step1 raw21243step1Labels = mixedMoment B raw21243step2 raw21243step2Labels := by
      have ha : raw21243step2 = (fun i j => raw21243step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21243step2 raw21243step1; decide +kernel
      have hl : raw21243step2Labels = raw21243step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21243step1 raw21243step1Labels permutation10 permutation3
    mixedMoment B raw21243step2 raw21243step2Labels = mixedMoment B raw21243step3 raw21243step3Labels := by
      have ha : raw21243step3 = raw21243step2 := by apply Matrix.ext; unfold raw21243step3 raw21243step2; decide +kernel
      have hl : raw21243step2Labels = labelEmbedding6 ∘ raw21243step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21243step2 raw21243step2Labels raw21243step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical166
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21248 raw21248Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw21248 raw21248Labels = mixedMoment B raw21248step0 raw21248step0Labels := by
      have hz : ∀ j, raw21248 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21248step0 = (fun i j => raw21248 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21248step0 raw21248; decide +kernel
      have hl : raw21248step0Labels = raw21248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21248 raw21248Labels permutation434 hz
    mixedMoment B raw21248step0 raw21248step0Labels = mixedMoment B raw21248step1 raw21248step1Labels := by
      have ha : raw21248step1 = (fun i j => raw21248step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21248step1 raw21248step0; decide +kernel
      have hl : raw21248step1Labels = raw21248step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21248step0 raw21248step0Labels permutation32 permutation3
    mixedMoment B raw21248step1 raw21248step1Labels = mixedMoment B raw21248step2 raw21248step2Labels := by
      have ha : raw21248step2 = raw21248step1 := by apply Matrix.ext; unfold raw21248step2 raw21248step1; decide +kernel
      have hl : raw21248step1Labels = labelEmbedding6 ∘ raw21248step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21248step1 raw21248step1Labels raw21248step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

theorem canonical21253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21253 raw21253Labels = mixedMoment B node4111 node4111Labels := by
  calc
    mixedMoment B raw21253 raw21253Labels = mixedMoment B raw21253step0 raw21253step0Labels := by
      have hz : ∀ j, raw21253 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21253step0 = (fun i j => raw21253 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21253step0 raw21253; decide +kernel
      have hl : raw21253step0Labels = raw21253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21253 raw21253Labels permutation434 hz
    mixedMoment B raw21253step0 raw21253step0Labels = mixedMoment B raw21253step1 raw21253step1Labels := by
      have hz : ∀ j, raw21253step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21253step1 = (fun i j => raw21253step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21253step1 raw21253step0; decide +kernel
      have hl : raw21253step1Labels = raw21253step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21253step0 raw21253step0Labels permutation80 hz
    mixedMoment B raw21253step1 raw21253step1Labels = mixedMoment B raw21253step2 raw21253step2Labels := by
      have ha : raw21253step2 = (fun i j => raw21253step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21253step2 raw21253step1; decide +kernel
      have hl : raw21253step2Labels = raw21253step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21253step1 raw21253step1Labels permutation8 permutation3
    mixedMoment B raw21253step2 raw21253step2Labels = mixedMoment B raw21253step3 raw21253step3Labels := by
      have ha : raw21253step3 = raw21253step2 := by apply Matrix.ext; unfold raw21253step3 raw21253step2; decide +kernel
      have hl : raw21253step2Labels = labelEmbedding6 ∘ raw21253step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21253step2 raw21253step2Labels raw21253step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4111 node4111Labels := by rfl

theorem canonical21254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21254 raw21254Labels = mixedMoment B node4361 node4361Labels := by
  calc
    mixedMoment B raw21254 raw21254Labels = mixedMoment B raw21254step0 raw21254step0Labels := by
      have hz : ∀ j, raw21254 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21254step0 = (fun i j => raw21254 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21254step0 raw21254; decide +kernel
      have hl : raw21254step0Labels = raw21254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21254 raw21254Labels permutation434 hz
    mixedMoment B raw21254step0 raw21254step0Labels = mixedMoment B raw21254step1 raw21254step1Labels := by
      have hz : ∀ j, raw21254step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21254step1 = (fun i j => raw21254step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21254step1 raw21254step0; decide +kernel
      have hl : raw21254step1Labels = raw21254step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21254step0 raw21254step0Labels permutation80 hz
    mixedMoment B raw21254step1 raw21254step1Labels = mixedMoment B raw21254step2 raw21254step2Labels := by
      have ha : raw21254step2 = (fun i j => raw21254step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21254step2 raw21254step1; decide +kernel
      have hl : raw21254step2Labels = raw21254step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21254step1 raw21254step1Labels permutation8 permutation3
    mixedMoment B raw21254step2 raw21254step2Labels = mixedMoment B raw21254step3 raw21254step3Labels := by
      have ha : raw21254step3 = raw21254step2 := by apply Matrix.ext; unfold raw21254step3 raw21254step2; decide +kernel
      have hl : raw21254step2Labels = labelEmbedding6 ∘ raw21254step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21254step2 raw21254step2Labels raw21254step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4361 node4361Labels := by rfl

theorem canonical21255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21255 raw21255Labels = mixedMoment B node4296 node4296Labels := by
  calc
    mixedMoment B raw21255 raw21255Labels = mixedMoment B raw21255step0 raw21255step0Labels := by
      have hz : ∀ j, raw21255 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21255step0 = (fun i j => raw21255 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21255step0 raw21255; decide +kernel
      have hl : raw21255step0Labels = raw21255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21255 raw21255Labels permutation434 hz
    mixedMoment B raw21255step0 raw21255step0Labels = mixedMoment B raw21255step1 raw21255step1Labels := by
      have ha : raw21255step1 = (fun i j => raw21255step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21255step1 raw21255step0; decide +kernel
      have hl : raw21255step1Labels = raw21255step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21255step0 raw21255step0Labels permutation38 permutation3
    mixedMoment B raw21255step1 raw21255step1Labels = mixedMoment B raw21255step2 raw21255step2Labels := by
      have ha : raw21255step2 = raw21255step1 := by apply Matrix.ext; unfold raw21255step2 raw21255step1; decide +kernel
      have hl : raw21255step1Labels = labelEmbedding6 ∘ raw21255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21255step1 raw21255step1Labels raw21255step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4296 node4296Labels := by rfl

theorem canonical21256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21256 raw21256Labels = mixedMoment B node4296 node4296Labels := by
  calc
    mixedMoment B raw21256 raw21256Labels = mixedMoment B raw21256step0 raw21256step0Labels := by
      have hz : ∀ j, raw21256 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21256step0 = (fun i j => raw21256 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21256step0 raw21256; decide +kernel
      have hl : raw21256step0Labels = raw21256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21256 raw21256Labels permutation346 hz
    mixedMoment B raw21256step0 raw21256step0Labels = mixedMoment B raw21256step1 raw21256step1Labels := by
      have ha : raw21256step1 = (fun i j => raw21256step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21256step1 raw21256step0; decide +kernel
      have hl : raw21256step1Labels = raw21256step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21256step0 raw21256step0Labels permutation38 permutation3
    mixedMoment B raw21256step1 raw21256step1Labels = mixedMoment B raw21256step2 raw21256step2Labels := by
      have ha : raw21256step2 = raw21256step1 := by apply Matrix.ext; unfold raw21256step2 raw21256step1; decide +kernel
      have hl : raw21256step1Labels = labelEmbedding6 ∘ raw21256step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21256step1 raw21256step1Labels raw21256step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4296 node4296Labels := by rfl

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

theorem canonical2214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2214 raw2214Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw2214 raw2214Labels = mixedMoment B raw2214step0 raw2214step0Labels := by
      have ha : raw2214step0 = (fun i j => raw2214 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2214step0 raw2214; decide +kernel
      have hl : raw2214step0Labels = raw2214Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2214 raw2214Labels permutation8 permutation4
    mixedMoment B raw2214step0 raw2214step0Labels = mixedMoment B raw2214step1 raw2214step1Labels := by
      have ha : raw2214step1 = raw2214step0 := by apply Matrix.ext; unfold raw2214step1 raw2214step0; decide +kernel
      have hl : raw2214step0Labels = labelEmbedding7 ∘ raw2214step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2214step0 raw2214step0Labels raw2214step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

theorem canonical2215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2215 raw2215Labels = mixedMoment B node2604 node2604Labels := by
  calc
    mixedMoment B raw2215 raw2215Labels = mixedMoment B raw2215step0 raw2215step0Labels := by
      have ha : raw2215step0 = (fun i j => raw2215 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2215step0 raw2215; decide +kernel
      have hl : raw2215step0Labels = raw2215Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2215 raw2215Labels permutation8 permutation4
    _ = mixedMoment B node2604 node2604Labels := by rfl

theorem canonical2216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2216 raw2216Labels = mixedMoment B node3614 node3614Labels := by
  calc
    mixedMoment B raw2216 raw2216Labels = mixedMoment B raw2216step0 raw2216step0Labels := by
      have ha : raw2216step0 = (fun i j => raw2216 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2216step0 raw2216; decide +kernel
      have hl : raw2216step0Labels = raw2216Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2216 raw2216Labels permutation8 permutation6
    mixedMoment B raw2216step0 raw2216step0Labels = mixedMoment B raw2216step1 raw2216step1Labels := by
      have ha : raw2216step1 = -raw2216step0 := by apply Matrix.ext; change ∀ i j, raw2216step1 i j = -(raw2216step0 i j); unfold raw2216step1 raw2216step0; decide +kernel
      have hl : raw2216step1Labels = raw2216step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2216step1 raw2216step1Labels = mixedMoment B raw2216step2 raw2216step2Labels := by
      have ha : raw2216step2 = raw2216step1 := by apply Matrix.ext; unfold raw2216step2 raw2216step1; decide +kernel
      have hl : raw2216step1Labels = labelEmbedding1 ∘ raw2216step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2216step1 raw2216step1Labels raw2216step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3614 node3614Labels := by rfl

theorem canonical2295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2295 raw2295Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw2295 raw2295Labels = mixedMoment B raw2295step0 raw2295step0Labels := by
      have ha : raw2295step0 = (fun i j => raw2295 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2295step0 raw2295; decide +kernel
      have hl : raw2295step0Labels = raw2295Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2295 raw2295Labels permutation8 permutation4
    mixedMoment B raw2295step0 raw2295step0Labels = mixedMoment B raw2295step1 raw2295step1Labels := by
      have ha : raw2295step1 = raw2295step0 := by apply Matrix.ext; unfold raw2295step1 raw2295step0; decide +kernel
      have hl : raw2295step0Labels = labelEmbedding7 ∘ raw2295step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2295step0 raw2295step0Labels raw2295step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

theorem canonical2296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2296 raw2296Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw2296 raw2296Labels = mixedMoment B raw2296step0 raw2296step0Labels := by
      have ha : raw2296step0 = (fun i j => raw2296 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2296step0 raw2296; decide +kernel
      have hl : raw2296step0Labels = raw2296Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2296 raw2296Labels permutation8 permutation4
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical2297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2297 raw2297Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw2297 raw2297Labels = mixedMoment B raw2297step0 raw2297step0Labels := by
      have ha : raw2297step0 = (fun i j => raw2297 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2297step0 raw2297; decide +kernel
      have hl : raw2297step0Labels = raw2297Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2297 raw2297Labels permutation10 permutation6
    mixedMoment B raw2297step0 raw2297step0Labels = mixedMoment B raw2297step1 raw2297step1Labels := by
      have ha : raw2297step1 = -raw2297step0 := by apply Matrix.ext; change ∀ i j, raw2297step1 i j = -(raw2297step0 i j); unfold raw2297step1 raw2297step0; decide +kernel
      have hl : raw2297step1Labels = raw2297step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2297step1 raw2297step1Labels = mixedMoment B raw2297step2 raw2297step2Labels := by
      have ha : raw2297step2 = raw2297step1 := by apply Matrix.ext; unfold raw2297step2 raw2297step1; decide +kernel
      have hl : raw2297step1Labels = labelEmbedding1 ∘ raw2297step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2297step1 raw2297step1Labels raw2297step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical179
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23036 raw23036Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw23036 raw23036Labels = mixedMoment B raw23036step0 raw23036step0Labels := by
      have hz : ∀ j, raw23036 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23036step0 = (fun i j => raw23036 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23036step0 raw23036; decide +kernel
      have hl : raw23036step0Labels = raw23036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23036 raw23036Labels permutation434 hz
    mixedMoment B raw23036step0 raw23036step0Labels = mixedMoment B raw23036step1 raw23036step1Labels := by
      have ha : raw23036step1 = (fun i j => raw23036step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23036step1 raw23036step0; decide +kernel
      have hl : raw23036step1Labels = raw23036step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23036step0 raw23036step0Labels permutation39 permutation3
    mixedMoment B raw23036step1 raw23036step1Labels = mixedMoment B raw23036step2 raw23036step2Labels := by
      have ha : raw23036step2 = raw23036step1 := by apply Matrix.ext; unfold raw23036step2 raw23036step1; decide +kernel
      have hl : raw23036step1Labels = labelEmbedding6 ∘ raw23036step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23036step1 raw23036step1Labels raw23036step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

theorem canonical23037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23037 raw23037Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw23037 raw23037Labels = mixedMoment B raw23037step0 raw23037step0Labels := by
      have hz : ∀ j, raw23037 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23037step0 = (fun i j => raw23037 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23037step0 raw23037; decide +kernel
      have hl : raw23037step0Labels = raw23037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23037 raw23037Labels permutation346 hz
    mixedMoment B raw23037step0 raw23037step0Labels = mixedMoment B raw23037step1 raw23037step1Labels := by
      have ha : raw23037step1 = (fun i j => raw23037step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23037step1 raw23037step0; decide +kernel
      have hl : raw23037step1Labels = raw23037step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23037step0 raw23037step0Labels permutation39 permutation3
    mixedMoment B raw23037step1 raw23037step1Labels = mixedMoment B raw23037step2 raw23037step2Labels := by
      have ha : raw23037step2 = raw23037step1 := by apply Matrix.ext; unfold raw23037step2 raw23037step1; decide +kernel
      have hl : raw23037step1Labels = labelEmbedding6 ∘ raw23037step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23037step1 raw23037step1Labels raw23037step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

theorem canonical23038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23038 raw23038Labels = mixedMoment B node4132 node4132Labels := by
  calc
    mixedMoment B raw23038 raw23038Labels = mixedMoment B raw23038step0 raw23038step0Labels := by
      have hz : ∀ j, raw23038 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23038step0 = (fun i j => raw23038 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23038step0 raw23038; decide +kernel
      have hl : raw23038step0Labels = raw23038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23038 raw23038Labels permutation434 hz
    mixedMoment B raw23038step0 raw23038step0Labels = mixedMoment B raw23038step1 raw23038step1Labels := by
      have hz : ∀ j, raw23038step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23038step1 = (fun i j => raw23038step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23038step1 raw23038step0; decide +kernel
      have hl : raw23038step1Labels = raw23038step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23038step0 raw23038step0Labels permutation80 hz
    mixedMoment B raw23038step1 raw23038step1Labels = mixedMoment B raw23038step2 raw23038step2Labels := by
      have ha : raw23038step2 = (fun i j => raw23038step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23038step2 raw23038step1; decide +kernel
      have hl : raw23038step2Labels = raw23038step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23038step1 raw23038step1Labels permutation9 permutation3
    mixedMoment B raw23038step2 raw23038step2Labels = mixedMoment B raw23038step3 raw23038step3Labels := by
      have ha : raw23038step3 = raw23038step2 := by apply Matrix.ext; unfold raw23038step3 raw23038step2; decide +kernel
      have hl : raw23038step2Labels = labelEmbedding6 ∘ raw23038step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23038step2 raw23038step2Labels raw23038step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4132 node4132Labels := by rfl

theorem canonical23039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23039 raw23039Labels = mixedMoment B node4313 node4313Labels := by
  calc
    mixedMoment B raw23039 raw23039Labels = mixedMoment B raw23039step0 raw23039step0Labels := by
      have hz : ∀ j, raw23039 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23039step0 = (fun i j => raw23039 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23039step0 raw23039; decide +kernel
      have hl : raw23039step0Labels = raw23039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23039 raw23039Labels permutation434 hz
    mixedMoment B raw23039step0 raw23039step0Labels = mixedMoment B raw23039step1 raw23039step1Labels := by
      have ha : raw23039step1 = (fun i j => raw23039step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23039step1 raw23039step0; decide +kernel
      have hl : raw23039step1Labels = raw23039step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23039step0 raw23039step0Labels permutation39 permutation3
    mixedMoment B raw23039step1 raw23039step1Labels = mixedMoment B raw23039step2 raw23039step2Labels := by
      have ha : raw23039step2 = raw23039step1 := by apply Matrix.ext; unfold raw23039step2 raw23039step1; decide +kernel
      have hl : raw23039step1Labels = labelEmbedding6 ∘ raw23039step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23039step1 raw23039step1Labels raw23039step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4313 node4313Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical180
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23040 raw23040Labels = mixedMoment B node4313 node4313Labels := by
  calc
    mixedMoment B raw23040 raw23040Labels = mixedMoment B raw23040step0 raw23040step0Labels := by
      have hz : ∀ j, raw23040 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23040step0 = (fun i j => raw23040 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23040step0 raw23040; decide +kernel
      have hl : raw23040step0Labels = raw23040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23040 raw23040Labels permutation346 hz
    mixedMoment B raw23040step0 raw23040step0Labels = mixedMoment B raw23040step1 raw23040step1Labels := by
      have ha : raw23040step1 = (fun i j => raw23040step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23040step1 raw23040step0; decide +kernel
      have hl : raw23040step1Labels = raw23040step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23040step0 raw23040step0Labels permutation39 permutation3
    mixedMoment B raw23040step1 raw23040step1Labels = mixedMoment B raw23040step2 raw23040step2Labels := by
      have ha : raw23040step2 = raw23040step1 := by apply Matrix.ext; unfold raw23040step2 raw23040step1; decide +kernel
      have hl : raw23040step1Labels = labelEmbedding6 ∘ raw23040step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23040step1 raw23040step1Labels raw23040step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4313 node4313Labels := by rfl

theorem canonical23041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23041 raw23041Labels = mixedMoment B node4491 node4491Labels := by
  calc
    mixedMoment B raw23041 raw23041Labels = mixedMoment B raw23041step0 raw23041step0Labels := by
      have hz : ∀ j, raw23041 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23041step0 = (fun i j => raw23041 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23041step0 raw23041; decide +kernel
      have hl : raw23041step0Labels = raw23041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23041 raw23041Labels permutation434 hz
    mixedMoment B raw23041step0 raw23041step0Labels = mixedMoment B raw23041step1 raw23041step1Labels := by
      have hz : ∀ j, raw23041step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23041step1 = (fun i j => raw23041step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23041step1 raw23041step0; decide +kernel
      have hl : raw23041step1Labels = raw23041step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23041step0 raw23041step0Labels permutation80 hz
    mixedMoment B raw23041step1 raw23041step1Labels = mixedMoment B raw23041step2 raw23041step2Labels := by
      have ha : raw23041step2 = (fun i j => raw23041step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23041step2 raw23041step1; decide +kernel
      have hl : raw23041step2Labels = raw23041step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23041step1 raw23041step1Labels permutation12 permutation3
    mixedMoment B raw23041step2 raw23041step2Labels = mixedMoment B raw23041step3 raw23041step3Labels := by
      have ha : raw23041step3 = raw23041step2 := by apply Matrix.ext; unfold raw23041step3 raw23041step2; decide +kernel
      have hl : raw23041step2Labels = labelEmbedding6 ∘ raw23041step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23041step2 raw23041step2Labels raw23041step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4491 node4491Labels := by rfl

theorem canonical23042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23042 raw23042Labels = mixedMoment B node4106 node4106Labels := by
  calc
    mixedMoment B raw23042 raw23042Labels = mixedMoment B raw23042step0 raw23042step0Labels := by
      have hz : ∀ j, raw23042 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23042step0 = (fun i j => raw23042 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23042step0 raw23042; decide +kernel
      have hl : raw23042step0Labels = raw23042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23042 raw23042Labels permutation434 hz
    mixedMoment B raw23042step0 raw23042step0Labels = mixedMoment B raw23042step1 raw23042step1Labels := by
      have ha : raw23042step1 = (fun i j => raw23042step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23042step1 raw23042step0; decide +kernel
      have hl : raw23042step1Labels = raw23042step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23042step0 raw23042step0Labels permutation33 permutation3
    mixedMoment B raw23042step1 raw23042step1Labels = mixedMoment B raw23042step2 raw23042step2Labels := by
      have ha : raw23042step2 = raw23042step1 := by apply Matrix.ext; unfold raw23042step2 raw23042step1; decide +kernel
      have hl : raw23042step1Labels = labelEmbedding6 ∘ raw23042step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23042step1 raw23042step1Labels raw23042step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4106 node4106Labels := by rfl

theorem canonical23043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23043 raw23043Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw23043 raw23043Labels = mixedMoment B raw23043step0 raw23043step0Labels := by
      have hz : ∀ j, raw23043 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23043step0 = (fun i j => raw23043 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23043step0 raw23043; decide +kernel
      have hl : raw23043step0Labels = raw23043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23043 raw23043Labels permutation434 hz
    mixedMoment B raw23043step0 raw23043step0Labels = mixedMoment B raw23043step1 raw23043step1Labels := by
      have ha : raw23043step1 = (fun i j => raw23043step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23043step1 raw23043step0; decide +kernel
      have hl : raw23043step1Labels = raw23043step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23043step0 raw23043step0Labels permutation33 permutation3
    mixedMoment B raw23043step1 raw23043step1Labels = mixedMoment B raw23043step2 raw23043step2Labels := by
      have ha : raw23043step2 = raw23043step1 := by apply Matrix.ext; unfold raw23043step2 raw23043step1; decide +kernel
      have hl : raw23043step1Labels = labelEmbedding6 ∘ raw23043step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23043step1 raw23043step1Labels raw23043step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4354 node4354Labels := by rfl

theorem canonical23044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23044 raw23044Labels = mixedMoment B node4291 node4291Labels := by
  calc
    mixedMoment B raw23044 raw23044Labels = mixedMoment B raw23044step0 raw23044step0Labels := by
      have ha : raw23044step0 = (fun i j => raw23044 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23044step0 raw23044; decide +kernel
      have hl : raw23044step0Labels = raw23044Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23044 raw23044Labels permutation201 permutation3
    mixedMoment B raw23044step0 raw23044step0Labels = mixedMoment B raw23044step1 raw23044step1Labels := by
      have ha : raw23044step1 = raw23044step0 := by apply Matrix.ext; unfold raw23044step1 raw23044step0; decide +kernel
      have hl : raw23044step0Labels = labelEmbedding6 ∘ raw23044step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23044step0 raw23044step0Labels raw23044step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4291 node4291Labels := by rfl

theorem canonical23045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23045 raw23045Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw23045 raw23045Labels = mixedMoment B raw23045step0 raw23045step0Labels := by
      have hz : ∀ j, raw23045 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23045step0 = (fun i j => raw23045 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23045step0 raw23045; decide +kernel
      have hl : raw23045step0Labels = raw23045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23045 raw23045Labels permutation434 hz
    mixedMoment B raw23045step0 raw23045step0Labels = mixedMoment B raw23045step1 raw23045step1Labels := by
      have ha : raw23045step1 = (fun i j => raw23045step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23045step1 raw23045step0; decide +kernel
      have hl : raw23045step1Labels = raw23045step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23045step0 raw23045step0Labels permutation36 permutation3
    mixedMoment B raw23045step1 raw23045step1Labels = mixedMoment B raw23045step2 raw23045step2Labels := by
      have ha : raw23045step2 = raw23045step1 := by apply Matrix.ext; unfold raw23045step2 raw23045step1; decide +kernel
      have hl : raw23045step1Labels = labelEmbedding6 ∘ raw23045step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23045step1 raw23045step1Labels raw23045step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

theorem canonical23046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23046 raw23046Labels = mixedMoment B node4106 node4106Labels := by
  calc
    mixedMoment B raw23046 raw23046Labels = mixedMoment B raw23046step0 raw23046step0Labels := by
      have hz : ∀ j, raw23046 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23046step0 = (fun i j => raw23046 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23046step0 raw23046; decide +kernel
      have hl : raw23046step0Labels = raw23046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23046 raw23046Labels permutation346 hz
    mixedMoment B raw23046step0 raw23046step0Labels = mixedMoment B raw23046step1 raw23046step1Labels := by
      have ha : raw23046step1 = (fun i j => raw23046step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23046step1 raw23046step0; decide +kernel
      have hl : raw23046step1Labels = raw23046step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23046step0 raw23046step0Labels permutation33 permutation3
    mixedMoment B raw23046step1 raw23046step1Labels = mixedMoment B raw23046step2 raw23046step2Labels := by
      have ha : raw23046step2 = raw23046step1 := by apply Matrix.ext; unfold raw23046step2 raw23046step1; decide +kernel
      have hl : raw23046step1Labels = labelEmbedding6 ∘ raw23046step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23046step1 raw23046step1Labels raw23046step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4106 node4106Labels := by rfl

theorem canonical23047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23047 raw23047Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw23047 raw23047Labels = mixedMoment B raw23047step0 raw23047step0Labels := by
      have hz : ∀ j, raw23047 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23047step0 = (fun i j => raw23047 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23047step0 raw23047; decide +kernel
      have hl : raw23047step0Labels = raw23047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23047 raw23047Labels permutation346 hz
    mixedMoment B raw23047step0 raw23047step0Labels = mixedMoment B raw23047step1 raw23047step1Labels := by
      have ha : raw23047step1 = (fun i j => raw23047step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23047step1 raw23047step0; decide +kernel
      have hl : raw23047step1Labels = raw23047step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23047step0 raw23047step0Labels permutation33 permutation3
    mixedMoment B raw23047step1 raw23047step1Labels = mixedMoment B raw23047step2 raw23047step2Labels := by
      have ha : raw23047step2 = raw23047step1 := by apply Matrix.ext; unfold raw23047step2 raw23047step1; decide +kernel
      have hl : raw23047step1Labels = labelEmbedding6 ∘ raw23047step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23047step1 raw23047step1Labels raw23047step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4354 node4354Labels := by rfl

theorem canonical23048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23048 raw23048Labels = mixedMoment B node4291 node4291Labels := by
  calc
    mixedMoment B raw23048 raw23048Labels = mixedMoment B raw23048step0 raw23048step0Labels := by
      have ha : raw23048step0 = (fun i j => raw23048 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23048step0 raw23048; decide +kernel
      have hl : raw23048step0Labels = raw23048Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23048 raw23048Labels permutation177 permutation3
    mixedMoment B raw23048step0 raw23048step0Labels = mixedMoment B raw23048step1 raw23048step1Labels := by
      have ha : raw23048step1 = raw23048step0 := by apply Matrix.ext; unfold raw23048step1 raw23048step0; decide +kernel
      have hl : raw23048step0Labels = labelEmbedding6 ∘ raw23048step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23048step0 raw23048step0Labels raw23048step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4291 node4291Labels := by rfl

theorem canonical23049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23049 raw23049Labels = mixedMoment B node4109 node4109Labels := by
  calc
    mixedMoment B raw23049 raw23049Labels = mixedMoment B raw23049step0 raw23049step0Labels := by
      have hz : ∀ j, raw23049 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23049step0 = (fun i j => raw23049 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23049step0 raw23049; decide +kernel
      have hl : raw23049step0Labels = raw23049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23049 raw23049Labels permutation434 hz
    mixedMoment B raw23049step0 raw23049step0Labels = mixedMoment B raw23049step1 raw23049step1Labels := by
      have hz : ∀ j, raw23049step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23049step1 = (fun i j => raw23049step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23049step1 raw23049step0; decide +kernel
      have hl : raw23049step1Labels = raw23049step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23049step0 raw23049step0Labels permutation80 hz
    mixedMoment B raw23049step1 raw23049step1Labels = mixedMoment B raw23049step2 raw23049step2Labels := by
      have ha : raw23049step2 = (fun i j => raw23049step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23049step2 raw23049step1; decide +kernel
      have hl : raw23049step2Labels = raw23049step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23049step1 raw23049step1Labels permutation9 permutation3
    mixedMoment B raw23049step2 raw23049step2Labels = mixedMoment B raw23049step3 raw23049step3Labels := by
      have ha : raw23049step3 = raw23049step2 := by apply Matrix.ext; unfold raw23049step3 raw23049step2; decide +kernel
      have hl : raw23049step2Labels = labelEmbedding6 ∘ raw23049step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23049step2 raw23049step2Labels raw23049step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4109 node4109Labels := by rfl

theorem canonical23050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23050 raw23050Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw23050 raw23050Labels = mixedMoment B raw23050step0 raw23050step0Labels := by
      have hz : ∀ j, raw23050 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23050step0 = (fun i j => raw23050 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23050step0 raw23050; decide +kernel
      have hl : raw23050step0Labels = raw23050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23050 raw23050Labels permutation434 hz
    mixedMoment B raw23050step0 raw23050step0Labels = mixedMoment B raw23050step1 raw23050step1Labels := by
      have hz : ∀ j, raw23050step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23050step1 = (fun i j => raw23050step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23050step1 raw23050step0; decide +kernel
      have hl : raw23050step1Labels = raw23050step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23050step0 raw23050step0Labels permutation80 hz
    mixedMoment B raw23050step1 raw23050step1Labels = mixedMoment B raw23050step2 raw23050step2Labels := by
      have ha : raw23050step2 = (fun i j => raw23050step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23050step2 raw23050step1; decide +kernel
      have hl : raw23050step2Labels = raw23050step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23050step1 raw23050step1Labels permutation9 permutation3
    mixedMoment B raw23050step2 raw23050step2Labels = mixedMoment B raw23050step3 raw23050step3Labels := by
      have ha : raw23050step3 = raw23050step2 := by apply Matrix.ext; unfold raw23050step3 raw23050step2; decide +kernel
      have hl : raw23050step2Labels = labelEmbedding6 ∘ raw23050step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23050step2 raw23050step2Labels raw23050step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4359 node4359Labels := by rfl

theorem canonical23051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23051 raw23051Labels = mixedMoment B node4294 node4294Labels := by
  calc
    mixedMoment B raw23051 raw23051Labels = mixedMoment B raw23051step0 raw23051step0Labels := by
      have hz : ∀ j, raw23051 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23051step0 = (fun i j => raw23051 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23051step0 raw23051; decide +kernel
      have hl : raw23051step0Labels = raw23051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23051 raw23051Labels permutation434 hz
    mixedMoment B raw23051step0 raw23051step0Labels = mixedMoment B raw23051step1 raw23051step1Labels := by
      have ha : raw23051step1 = (fun i j => raw23051step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23051step1 raw23051step0; decide +kernel
      have hl : raw23051step1Labels = raw23051step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23051step0 raw23051step0Labels permutation39 permutation3
    mixedMoment B raw23051step1 raw23051step1Labels = mixedMoment B raw23051step2 raw23051step2Labels := by
      have ha : raw23051step2 = raw23051step1 := by apply Matrix.ext; unfold raw23051step2 raw23051step1; decide +kernel
      have hl : raw23051step1Labels = labelEmbedding6 ∘ raw23051step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23051step1 raw23051step1Labels raw23051step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4294 node4294Labels := by rfl

theorem canonical23052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23052 raw23052Labels = mixedMoment B node4294 node4294Labels := by
  calc
    mixedMoment B raw23052 raw23052Labels = mixedMoment B raw23052step0 raw23052step0Labels := by
      have hz : ∀ j, raw23052 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23052step0 = (fun i j => raw23052 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23052step0 raw23052; decide +kernel
      have hl : raw23052step0Labels = raw23052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23052 raw23052Labels permutation346 hz
    mixedMoment B raw23052step0 raw23052step0Labels = mixedMoment B raw23052step1 raw23052step1Labels := by
      have ha : raw23052step1 = (fun i j => raw23052step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23052step1 raw23052step0; decide +kernel
      have hl : raw23052step1Labels = raw23052step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23052step0 raw23052step0Labels permutation39 permutation3
    mixedMoment B raw23052step1 raw23052step1Labels = mixedMoment B raw23052step2 raw23052step2Labels := by
      have ha : raw23052step2 = raw23052step1 := by apply Matrix.ext; unfold raw23052step2 raw23052step1; decide +kernel
      have hl : raw23052step1Labels = labelEmbedding6 ∘ raw23052step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23052step1 raw23052step1Labels raw23052step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4294 node4294Labels := by rfl

theorem canonical23053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23053 raw23053Labels = mixedMoment B node4454 node4454Labels := by
  calc
    mixedMoment B raw23053 raw23053Labels = mixedMoment B raw23053step0 raw23053step0Labels := by
      have hz : ∀ j, raw23053 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23053step0 = (fun i j => raw23053 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23053step0 raw23053; decide +kernel
      have hl : raw23053step0Labels = raw23053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23053 raw23053Labels permutation434 hz
    mixedMoment B raw23053step0 raw23053step0Labels = mixedMoment B raw23053step1 raw23053step1Labels := by
      have hz : ∀ j, raw23053step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23053step1 = (fun i j => raw23053step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23053step1 raw23053step0; decide +kernel
      have hl : raw23053step1Labels = raw23053step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23053step0 raw23053step0Labels permutation80 hz
    mixedMoment B raw23053step1 raw23053step1Labels = mixedMoment B raw23053step2 raw23053step2Labels := by
      have ha : raw23053step2 = (fun i j => raw23053step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23053step2 raw23053step1; decide +kernel
      have hl : raw23053step2Labels = raw23053step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23053step1 raw23053step1Labels permutation9 permutation3
    mixedMoment B raw23053step2 raw23053step2Labels = mixedMoment B raw23053step3 raw23053step3Labels := by
      have ha : raw23053step3 = raw23053step2 := by apply Matrix.ext; unfold raw23053step3 raw23053step2; decide +kernel
      have hl : raw23053step2Labels = labelEmbedding6 ∘ raw23053step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23053step2 raw23053step2Labels raw23053step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4454 node4454Labels := by rfl

theorem canonical23054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23054 raw23054Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw23054 raw23054Labels = mixedMoment B raw23054step0 raw23054step0Labels := by
      have hz : ∀ j, raw23054 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23054step0 = (fun i j => raw23054 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23054step0 raw23054; decide +kernel
      have hl : raw23054step0Labels = raw23054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23054 raw23054Labels permutation434 hz
    mixedMoment B raw23054step0 raw23054step0Labels = mixedMoment B raw23054step1 raw23054step1Labels := by
      have hz : ∀ j, raw23054step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23054step1 = (fun i j => raw23054step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23054step1 raw23054step0; decide +kernel
      have hl : raw23054step1Labels = raw23054step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23054step0 raw23054step0Labels permutation80 hz
    mixedMoment B raw23054step1 raw23054step1Labels = mixedMoment B raw23054step2 raw23054step2Labels := by
      have ha : raw23054step2 = (fun i j => raw23054step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23054step2 raw23054step1; decide +kernel
      have hl : raw23054step2Labels = raw23054step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23054step1 raw23054step1Labels permutation8 permutation3
    mixedMoment B raw23054step2 raw23054step2Labels = mixedMoment B raw23054step3 raw23054step3Labels := by
      have ha : raw23054step3 = raw23054step2 := by apply Matrix.ext; unfold raw23054step3 raw23054step2; decide +kernel
      have hl : raw23054step2Labels = labelEmbedding6 ∘ raw23054step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23054step2 raw23054step2Labels raw23054step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3049 raw3049Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw3049 raw3049Labels = mixedMoment B raw3049step0 raw3049step0Labels := by
      have hz : ∀ j, raw3049 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3049step0 = (fun i j => raw3049 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3049step0 raw3049; decide +kernel
      have hl : raw3049step0Labels = raw3049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3049 raw3049Labels permutation434 hz
    mixedMoment B raw3049step0 raw3049step0Labels = mixedMoment B raw3049step1 raw3049step1Labels := by
      have hz : ∀ j, raw3049step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3049step1 = (fun i j => raw3049step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3049step1 raw3049step0; decide +kernel
      have hl : raw3049step1Labels = raw3049step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3049step0 raw3049step0Labels permutation80 hz
    mixedMoment B raw3049step1 raw3049step1Labels = mixedMoment B raw3049step2 raw3049step2Labels := by
      have ha : raw3049step2 = (fun i j => raw3049step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3049step2 raw3049step1; decide +kernel
      have hl : raw3049step2Labels = raw3049step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3049step1 raw3049step1Labels permutation9 permutation3
    mixedMoment B raw3049step2 raw3049step2Labels = mixedMoment B raw3049step3 raw3049step3Labels := by
      have ha : raw3049step3 = raw3049step2 := by apply Matrix.ext; unfold raw3049step3 raw3049step2; decide +kernel
      have hl : raw3049step2Labels = labelEmbedding6 ∘ raw3049step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3049step2 raw3049step2Labels raw3049step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

theorem canonical3054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3054 raw3054Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw3054 raw3054Labels = mixedMoment B raw3054step0 raw3054step0Labels := by
      have hz : ∀ j, raw3054 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3054step0 = (fun i j => raw3054 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3054step0 raw3054; decide +kernel
      have hl : raw3054step0Labels = raw3054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3054 raw3054Labels permutation434 hz
    mixedMoment B raw3054step0 raw3054step0Labels = mixedMoment B raw3054step1 raw3054step1Labels := by
      have hz : ∀ j, raw3054step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3054step1 = (fun i j => raw3054step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3054step1 raw3054step0; decide +kernel
      have hl : raw3054step1Labels = raw3054step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3054step0 raw3054step0Labels permutation80 hz
    mixedMoment B raw3054step1 raw3054step1Labels = mixedMoment B raw3054step2 raw3054step2Labels := by
      have ha : raw3054step2 = (fun i j => raw3054step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3054step2 raw3054step1; decide +kernel
      have hl : raw3054step2Labels = raw3054step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3054step1 raw3054step1Labels permutation8 permutation3
    mixedMoment B raw3054step2 raw3054step2Labels = mixedMoment B raw3054step3 raw3054step3Labels := by
      have ha : raw3054step3 = raw3054step2 := by apply Matrix.ext; unfold raw3054step3 raw3054step2; decide +kernel
      have hl : raw3054step2Labels = labelEmbedding6 ∘ raw3054step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3054step2 raw3054step2Labels raw3054step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

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

theorem canonical690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw690 raw690Labels = mixedMoment B node4106 node4106Labels := by
  calc
    mixedMoment B raw690 raw690Labels = mixedMoment B raw690step0 raw690step0Labels := by
      have ha : raw690step0 = (fun i j => raw690 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw690step0 raw690; decide +kernel
      have hl : raw690step0Labels = raw690Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw690 raw690Labels permutation32 permutation4
    mixedMoment B raw690step0 raw690step0Labels = mixedMoment B raw690step1 raw690step1Labels := by
      have ha : raw690step1 = raw690step0 := by apply Matrix.ext; unfold raw690step1 raw690step0; decide +kernel
      have hl : raw690step0Labels = labelEmbedding7 ∘ raw690step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw690step0 raw690step0Labels raw690step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4106 node4106Labels := by rfl

theorem canonical691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw691 raw691Labels = mixedMoment B node543 node543Labels := by
  calc
    mixedMoment B raw691 raw691Labels = mixedMoment B raw691step0 raw691step0Labels := by
      have ha : raw691step0 = (fun i j => raw691 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw691step0 raw691; decide +kernel
      have hl : raw691step0Labels = raw691Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw691 raw691Labels permutation32 permutation4
    _ = mixedMoment B node543 node543Labels := by rfl

theorem canonical692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw692 raw692Labels = mixedMoment B node675 node675Labels := by
  calc
    mixedMoment B raw692 raw692Labels = mixedMoment B raw692step0 raw692step0Labels := by
      have ha : raw692step0 = (fun i j => raw692 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw692step0 raw692; decide +kernel
      have hl : raw692step0Labels = raw692Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw692 raw692Labels permutation44 permutation6
    mixedMoment B raw692step0 raw692step0Labels = mixedMoment B raw692step1 raw692step1Labels := by
      have ha : raw692step1 = -raw692step0 := by apply Matrix.ext; change ∀ i j, raw692step1 i j = -(raw692step0 i j); unfold raw692step1 raw692step0; decide +kernel
      have hl : raw692step1Labels = raw692step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw692step1 raw692step1Labels = mixedMoment B raw692step2 raw692step2Labels := by
      have ha : raw692step2 = raw692step1 := by apply Matrix.ext; unfold raw692step2 raw692step1; decide +kernel
      have hl : raw692step1Labels = labelEmbedding1 ∘ raw692step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw692step1 raw692step1Labels raw692step2Labels labelEmbedding1 hl
    _ = mixedMoment B node675 node675Labels := by rfl

theorem canonical699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw699 raw699Labels = mixedMoment B node4109 node4109Labels := by
  calc
    mixedMoment B raw699 raw699Labels = mixedMoment B raw699step0 raw699step0Labels := by
      have ha : raw699step0 = (fun i j => raw699 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw699step0 raw699; decide +kernel
      have hl : raw699step0Labels = raw699Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw699 raw699Labels permutation8 permutation4
    mixedMoment B raw699step0 raw699step0Labels = mixedMoment B raw699step1 raw699step1Labels := by
      have ha : raw699step1 = raw699step0 := by apply Matrix.ext; unfold raw699step1 raw699step0; decide +kernel
      have hl : raw699step0Labels = labelEmbedding7 ∘ raw699step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw699step0 raw699step0Labels raw699step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4109 node4109Labels := by rfl

theorem canonical700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw700 raw700Labels = mixedMoment B node546 node546Labels := by
  calc
    mixedMoment B raw700 raw700Labels = mixedMoment B raw700step0 raw700step0Labels := by
      have ha : raw700step0 = (fun i j => raw700 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw700step0 raw700; decide +kernel
      have hl : raw700step0Labels = raw700Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw700 raw700Labels permutation8 permutation4
    _ = mixedMoment B node546 node546Labels := by rfl

theorem canonical701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw701 raw701Labels = mixedMoment B node676 node676Labels := by
  calc
    mixedMoment B raw701 raw701Labels = mixedMoment B raw701step0 raw701step0Labels := by
      have ha : raw701step0 = (fun i j => raw701 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw701step0 raw701; decide +kernel
      have hl : raw701step0Labels = raw701Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw701 raw701Labels permutation10 permutation6
    mixedMoment B raw701step0 raw701step0Labels = mixedMoment B raw701step1 raw701step1Labels := by
      have ha : raw701step1 = -raw701step0 := by apply Matrix.ext; change ∀ i j, raw701step1 i j = -(raw701step0 i j); unfold raw701step1 raw701step0; decide +kernel
      have hl : raw701step1Labels = raw701step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw701step1 raw701step1Labels = mixedMoment B raw701step2 raw701step2Labels := by
      have ha : raw701step2 = raw701step1 := by apply Matrix.ext; unfold raw701step2 raw701step1; decide +kernel
      have hl : raw701step1Labels = labelEmbedding1 ∘ raw701step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw701step1 raw701step1Labels raw701step2Labels labelEmbedding1 hl
    _ = mixedMoment B node676 node676Labels := by rfl

theorem canonical705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw705 raw705Labels = mixedMoment B node4111 node4111Labels := by
  calc
    mixedMoment B raw705 raw705Labels = mixedMoment B raw705step0 raw705step0Labels := by
      have ha : raw705step0 = (fun i j => raw705 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw705step0 raw705; decide +kernel
      have hl : raw705step0Labels = raw705Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw705 raw705Labels permutation8 permutation4
    mixedMoment B raw705step0 raw705step0Labels = mixedMoment B raw705step1 raw705step1Labels := by
      have ha : raw705step1 = raw705step0 := by apply Matrix.ext; unfold raw705step1 raw705step0; decide +kernel
      have hl : raw705step0Labels = labelEmbedding7 ∘ raw705step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw705step0 raw705step0Labels raw705step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4111 node4111Labels := by rfl

theorem canonical706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw706 raw706Labels = mixedMoment B node548 node548Labels := by
  calc
    mixedMoment B raw706 raw706Labels = mixedMoment B raw706step0 raw706step0Labels := by
      have ha : raw706step0 = (fun i j => raw706 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw706step0 raw706; decide +kernel
      have hl : raw706step0Labels = raw706Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw706 raw706Labels permutation8 permutation4
    _ = mixedMoment B node548 node548Labels := by rfl

theorem canonical707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw707 raw707Labels = mixedMoment B node685 node685Labels := by
  calc
    mixedMoment B raw707 raw707Labels = mixedMoment B raw707step0 raw707step0Labels := by
      have ha : raw707step0 = (fun i j => raw707 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw707step0 raw707; decide +kernel
      have hl : raw707step0Labels = raw707Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw707 raw707Labels permutation9 permutation6
    mixedMoment B raw707step0 raw707step0Labels = mixedMoment B raw707step1 raw707step1Labels := by
      have ha : raw707step1 = -raw707step0 := by apply Matrix.ext; change ∀ i j, raw707step1 i j = -(raw707step0 i j); unfold raw707step1 raw707step0; decide +kernel
      have hl : raw707step1Labels = raw707step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw707step1 raw707step1Labels = mixedMoment B raw707step2 raw707step2Labels := by
      have ha : raw707step2 = raw707step1 := by apply Matrix.ext; unfold raw707step2 raw707step1; decide +kernel
      have hl : raw707step1Labels = labelEmbedding1 ∘ raw707step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw707step1 raw707step1Labels raw707step2Labels labelEmbedding1 hl
    _ = mixedMoment B node685 node685Labels := by rfl

theorem canonical741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw741 raw741Labels = mixedMoment B node4132 node4132Labels := by
  calc
    mixedMoment B raw741 raw741Labels = mixedMoment B raw741step0 raw741step0Labels := by
      have ha : raw741step0 = (fun i j => raw741 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw741step0 raw741; decide +kernel
      have hl : raw741step0Labels = raw741Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw741 raw741Labels permutation8 permutation4
    mixedMoment B raw741step0 raw741step0Labels = mixedMoment B raw741step1 raw741step1Labels := by
      have ha : raw741step1 = raw741step0 := by apply Matrix.ext; unfold raw741step1 raw741step0; decide +kernel
      have hl : raw741step0Labels = labelEmbedding7 ∘ raw741step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw741step0 raw741step0Labels raw741step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4132 node4132Labels := by rfl

theorem canonical742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw742 raw742Labels = mixedMoment B node562 node562Labels := by
  calc
    mixedMoment B raw742 raw742Labels = mixedMoment B raw742step0 raw742step0Labels := by
      have ha : raw742step0 = (fun i j => raw742 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw742step0 raw742; decide +kernel
      have hl : raw742step0Labels = raw742Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw742 raw742Labels permutation8 permutation4
    _ = mixedMoment B node562 node562Labels := by rfl

theorem canonical743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw743 raw743Labels = mixedMoment B node679 node679Labels := by
  calc
    mixedMoment B raw743 raw743Labels = mixedMoment B raw743step0 raw743step0Labels := by
      have ha : raw743step0 = (fun i j => raw743 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw743step0 raw743; decide +kernel
      have hl : raw743step0Labels = raw743Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw743 raw743Labels permutation10 permutation6
    mixedMoment B raw743step0 raw743step0Labels = mixedMoment B raw743step1 raw743step1Labels := by
      have ha : raw743step1 = -raw743step0 := by apply Matrix.ext; change ∀ i j, raw743step1 i j = -(raw743step0 i j); unfold raw743step1 raw743step0; decide +kernel
      have hl : raw743step1Labels = raw743step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw743step1 raw743step1Labels = mixedMoment B raw743step2 raw743step2Labels := by
      have ha : raw743step2 = raw743step1 := by apply Matrix.ext; unfold raw743step2 raw743step1; decide +kernel
      have hl : raw743step1Labels = labelEmbedding1 ∘ raw743step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw743step1 raw743step1Labels raw743step2Labels labelEmbedding1 hl
    _ = mixedMoment B node679 node679Labels := by rfl

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

theorem canonical1035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1035 raw1035Labels = mixedMoment B node4291 node4291Labels := by
  calc
    mixedMoment B raw1035 raw1035Labels = mixedMoment B raw1035step0 raw1035step0Labels := by
      have ha : raw1035step0 = (fun i j => raw1035 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1035step0 raw1035; decide +kernel
      have hl : raw1035step0Labels = raw1035Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1035 raw1035Labels permutation152 permutation4
    mixedMoment B raw1035step0 raw1035step0Labels = mixedMoment B raw1035step1 raw1035step1Labels := by
      have ha : raw1035step1 = raw1035step0 := by apply Matrix.ext; unfold raw1035step1 raw1035step0; decide +kernel
      have hl : raw1035step0Labels = labelEmbedding7 ∘ raw1035step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1035step0 raw1035step0Labels raw1035step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4291 node4291Labels := by rfl

theorem canonical1036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1036 raw1036Labels = mixedMoment B node869 node869Labels := by
  calc
    mixedMoment B raw1036 raw1036Labels = mixedMoment B raw1036step0 raw1036step0Labels := by
      have ha : raw1036step0 = (fun i j => raw1036 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1036step0 raw1036; decide +kernel
      have hl : raw1036step0Labels = raw1036Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1036 raw1036Labels permutation152 permutation4
    _ = mixedMoment B node869 node869Labels := by rfl

theorem canonical1037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1037 raw1037Labels = mixedMoment B node1561 node1561Labels := by
  calc
    mixedMoment B raw1037 raw1037Labels = mixedMoment B raw1037step0 raw1037step0Labels := by
      have ha : raw1037step0 = (fun i j => raw1037 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1037step0 raw1037; decide +kernel
      have hl : raw1037step0Labels = raw1037Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1037 raw1037Labels permutation164 permutation6
    mixedMoment B raw1037step0 raw1037step0Labels = mixedMoment B raw1037step1 raw1037step1Labels := by
      have ha : raw1037step1 = -raw1037step0 := by apply Matrix.ext; change ∀ i j, raw1037step1 i j = -(raw1037step0 i j); unfold raw1037step1 raw1037step0; decide +kernel
      have hl : raw1037step1Labels = raw1037step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1037step1 raw1037step1Labels = mixedMoment B raw1037step2 raw1037step2Labels := by
      have ha : raw1037step2 = raw1037step1 := by apply Matrix.ext; unfold raw1037step2 raw1037step1; decide +kernel
      have hl : raw1037step1Labels = labelEmbedding1 ∘ raw1037step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1037step1 raw1037step1Labels raw1037step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1561 node1561Labels := by rfl

theorem canonical1044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1044 raw1044Labels = mixedMoment B node4294 node4294Labels := by
  calc
    mixedMoment B raw1044 raw1044Labels = mixedMoment B raw1044step0 raw1044step0Labels := by
      have ha : raw1044step0 = (fun i j => raw1044 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1044step0 raw1044; decide +kernel
      have hl : raw1044step0Labels = raw1044Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1044 raw1044Labels permutation32 permutation4
    mixedMoment B raw1044step0 raw1044step0Labels = mixedMoment B raw1044step1 raw1044step1Labels := by
      have ha : raw1044step1 = raw1044step0 := by apply Matrix.ext; unfold raw1044step1 raw1044step0; decide +kernel
      have hl : raw1044step0Labels = labelEmbedding7 ∘ raw1044step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1044step0 raw1044step0Labels raw1044step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4294 node4294Labels := by rfl

theorem canonical1045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1045 raw1045Labels = mixedMoment B node872 node872Labels := by
  calc
    mixedMoment B raw1045 raw1045Labels = mixedMoment B raw1045step0 raw1045step0Labels := by
      have ha : raw1045step0 = (fun i j => raw1045 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1045step0 raw1045; decide +kernel
      have hl : raw1045step0Labels = raw1045Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1045 raw1045Labels permutation32 permutation4
    _ = mixedMoment B node872 node872Labels := by rfl

theorem canonical1046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1046 raw1046Labels = mixedMoment B node1562 node1562Labels := by
  calc
    mixedMoment B raw1046 raw1046Labels = mixedMoment B raw1046step0 raw1046step0Labels := by
      have ha : raw1046step0 = (fun i j => raw1046 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1046step0 raw1046; decide +kernel
      have hl : raw1046step0Labels = raw1046Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1046 raw1046Labels permutation34 permutation6
    mixedMoment B raw1046step0 raw1046step0Labels = mixedMoment B raw1046step1 raw1046step1Labels := by
      have ha : raw1046step1 = -raw1046step0 := by apply Matrix.ext; change ∀ i j, raw1046step1 i j = -(raw1046step0 i j); unfold raw1046step1 raw1046step0; decide +kernel
      have hl : raw1046step1Labels = raw1046step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1046step1 raw1046step1Labels = mixedMoment B raw1046step2 raw1046step2Labels := by
      have ha : raw1046step2 = raw1046step1 := by apply Matrix.ext; unfold raw1046step2 raw1046step1; decide +kernel
      have hl : raw1046step1Labels = labelEmbedding1 ∘ raw1046step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1046step1 raw1046step1Labels raw1046step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1562 node1562Labels := by rfl

theorem canonical1050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1050 raw1050Labels = mixedMoment B node4296 node4296Labels := by
  calc
    mixedMoment B raw1050 raw1050Labels = mixedMoment B raw1050step0 raw1050step0Labels := by
      have ha : raw1050step0 = (fun i j => raw1050 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1050step0 raw1050; decide +kernel
      have hl : raw1050step0Labels = raw1050Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1050 raw1050Labels permutation32 permutation4
    mixedMoment B raw1050step0 raw1050step0Labels = mixedMoment B raw1050step1 raw1050step1Labels := by
      have ha : raw1050step1 = raw1050step0 := by apply Matrix.ext; unfold raw1050step1 raw1050step0; decide +kernel
      have hl : raw1050step0Labels = labelEmbedding7 ∘ raw1050step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1050step0 raw1050step0Labels raw1050step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4296 node4296Labels := by rfl

theorem canonical1051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1051 raw1051Labels = mixedMoment B node874 node874Labels := by
  calc
    mixedMoment B raw1051 raw1051Labels = mixedMoment B raw1051step0 raw1051step0Labels := by
      have ha : raw1051step0 = (fun i j => raw1051 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1051step0 raw1051; decide +kernel
      have hl : raw1051step0Labels = raw1051Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1051 raw1051Labels permutation32 permutation4
    _ = mixedMoment B node874 node874Labels := by rfl

theorem canonical1052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1052 raw1052Labels = mixedMoment B node1570 node1570Labels := by
  calc
    mixedMoment B raw1052 raw1052Labels = mixedMoment B raw1052step0 raw1052step0Labels := by
      have ha : raw1052step0 = (fun i j => raw1052 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1052step0 raw1052; decide +kernel
      have hl : raw1052step0Labels = raw1052Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1052 raw1052Labels permutation33 permutation6
    mixedMoment B raw1052step0 raw1052step0Labels = mixedMoment B raw1052step1 raw1052step1Labels := by
      have ha : raw1052step1 = -raw1052step0 := by apply Matrix.ext; change ∀ i j, raw1052step1 i j = -(raw1052step0 i j); unfold raw1052step1 raw1052step0; decide +kernel
      have hl : raw1052step1Labels = raw1052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1052step1 raw1052step1Labels = mixedMoment B raw1052step2 raw1052step2Labels := by
      have ha : raw1052step2 = raw1052step1 := by apply Matrix.ext; unfold raw1052step2 raw1052step1; decide +kernel
      have hl : raw1052step1Labels = labelEmbedding1 ∘ raw1052step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1052step1 raw1052step1Labels raw1052step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1570 node1570Labels := by rfl

theorem canonical1080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1080 raw1080Labels = mixedMoment B node4313 node4313Labels := by
  calc
    mixedMoment B raw1080 raw1080Labels = mixedMoment B raw1080step0 raw1080step0Labels := by
      have ha : raw1080step0 = (fun i j => raw1080 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1080step0 raw1080; decide +kernel
      have hl : raw1080step0Labels = raw1080Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1080 raw1080Labels permutation32 permutation4
    mixedMoment B raw1080step0 raw1080step0Labels = mixedMoment B raw1080step1 raw1080step1Labels := by
      have ha : raw1080step1 = raw1080step0 := by apply Matrix.ext; unfold raw1080step1 raw1080step0; decide +kernel
      have hl : raw1080step0Labels = labelEmbedding7 ∘ raw1080step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1080step0 raw1080step0Labels raw1080step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4313 node4313Labels := by rfl

theorem canonical1081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1081 raw1081Labels = mixedMoment B node891 node891Labels := by
  calc
    mixedMoment B raw1081 raw1081Labels = mixedMoment B raw1081step0 raw1081step0Labels := by
      have ha : raw1081step0 = (fun i j => raw1081 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1081step0 raw1081; decide +kernel
      have hl : raw1081step0Labels = raw1081Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1081 raw1081Labels permutation32 permutation4
    _ = mixedMoment B node891 node891Labels := by rfl

theorem canonical1082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1082 raw1082Labels = mixedMoment B node1565 node1565Labels := by
  calc
    mixedMoment B raw1082 raw1082Labels = mixedMoment B raw1082step0 raw1082step0Labels := by
      have ha : raw1082step0 = (fun i j => raw1082 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1082step0 raw1082; decide +kernel
      have hl : raw1082step0Labels = raw1082Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1082 raw1082Labels permutation34 permutation6
    mixedMoment B raw1082step0 raw1082step0Labels = mixedMoment B raw1082step1 raw1082step1Labels := by
      have ha : raw1082step1 = -raw1082step0 := by apply Matrix.ext; change ∀ i j, raw1082step1 i j = -(raw1082step0 i j); unfold raw1082step1 raw1082step0; decide +kernel
      have hl : raw1082step1Labels = raw1082step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1082step1 raw1082step1Labels = mixedMoment B raw1082step2 raw1082step2Labels := by
      have ha : raw1082step2 = raw1082step1 := by apply Matrix.ext; unfold raw1082step2 raw1082step1; decide +kernel
      have hl : raw1082step1Labels = labelEmbedding1 ∘ raw1082step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1082step1 raw1082step1Labels raw1082step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1565 node1565Labels := by rfl

theorem canonical1146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1146 raw1146Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw1146 raw1146Labels = mixedMoment B raw1146step0 raw1146step0Labels := by
      have ha : raw1146step0 = (fun i j => raw1146 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1146step0 raw1146; decide +kernel
      have hl : raw1146step0Labels = raw1146Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1146 raw1146Labels permutation32 permutation4
    mixedMoment B raw1146step0 raw1146step0Labels = mixedMoment B raw1146step1 raw1146step1Labels := by
      have ha : raw1146step1 = raw1146step0 := by apply Matrix.ext; unfold raw1146step1 raw1146step0; decide +kernel
      have hl : raw1146step0Labels = labelEmbedding7 ∘ raw1146step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1146step0 raw1146step0Labels raw1146step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4354 node4354Labels := by rfl

theorem canonical1147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1147 raw1147Labels = mixedMoment B node932 node932Labels := by
  calc
    mixedMoment B raw1147 raw1147Labels = mixedMoment B raw1147step0 raw1147step0Labels := by
      have ha : raw1147step0 = (fun i j => raw1147 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1147step0 raw1147; decide +kernel
      have hl : raw1147step0Labels = raw1147Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1147 raw1147Labels permutation32 permutation4
    _ = mixedMoment B node932 node932Labels := by rfl

theorem canonical1148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1148 raw1148Labels = mixedMoment B node1681 node1681Labels := by
  calc
    mixedMoment B raw1148 raw1148Labels = mixedMoment B raw1148step0 raw1148step0Labels := by
      have ha : raw1148step0 = (fun i j => raw1148 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1148step0 raw1148; decide +kernel
      have hl : raw1148step0Labels = raw1148Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1148 raw1148Labels permutation34 permutation6
    mixedMoment B raw1148step0 raw1148step0Labels = mixedMoment B raw1148step1 raw1148step1Labels := by
      have ha : raw1148step1 = -raw1148step0 := by apply Matrix.ext; change ∀ i j, raw1148step1 i j = -(raw1148step0 i j); unfold raw1148step1 raw1148step0; decide +kernel
      have hl : raw1148step1Labels = raw1148step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1148step1 raw1148step1Labels = mixedMoment B raw1148step2 raw1148step2Labels := by
      have ha : raw1148step2 = raw1148step1 := by apply Matrix.ext; unfold raw1148step2 raw1148step1; decide +kernel
      have hl : raw1148step1Labels = labelEmbedding1 ∘ raw1148step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1148step1 raw1148step1Labels raw1148step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1681 node1681Labels := by rfl

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

theorem canonical1155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1155 raw1155Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw1155 raw1155Labels = mixedMoment B raw1155step0 raw1155step0Labels := by
      have ha : raw1155step0 = (fun i j => raw1155 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1155step0 raw1155; decide +kernel
      have hl : raw1155step0Labels = raw1155Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1155 raw1155Labels permutation8 permutation4
    mixedMoment B raw1155step0 raw1155step0Labels = mixedMoment B raw1155step1 raw1155step1Labels := by
      have ha : raw1155step1 = raw1155step0 := by apply Matrix.ext; unfold raw1155step1 raw1155step0; decide +kernel
      have hl : raw1155step0Labels = labelEmbedding7 ∘ raw1155step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1155step0 raw1155step0Labels raw1155step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4359 node4359Labels := by rfl

theorem canonical1156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1156 raw1156Labels = mixedMoment B node937 node937Labels := by
  calc
    mixedMoment B raw1156 raw1156Labels = mixedMoment B raw1156step0 raw1156step0Labels := by
      have ha : raw1156step0 = (fun i j => raw1156 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1156step0 raw1156; decide +kernel
      have hl : raw1156step0Labels = raw1156Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1156 raw1156Labels permutation8 permutation4
    _ = mixedMoment B node937 node937Labels := by rfl

theorem canonical1157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1157 raw1157Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw1157 raw1157Labels = mixedMoment B raw1157step0 raw1157step0Labels := by
      have ha : raw1157step0 = (fun i j => raw1157 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1157step0 raw1157; decide +kernel
      have hl : raw1157step0Labels = raw1157Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1157 raw1157Labels permutation8 permutation6
    mixedMoment B raw1157step0 raw1157step0Labels = mixedMoment B raw1157step1 raw1157step1Labels := by
      have ha : raw1157step1 = -raw1157step0 := by apply Matrix.ext; change ∀ i j, raw1157step1 i j = -(raw1157step0 i j); unfold raw1157step1 raw1157step0; decide +kernel
      have hl : raw1157step1Labels = raw1157step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1157step1 raw1157step1Labels = mixedMoment B raw1157step2 raw1157step2Labels := by
      have ha : raw1157step2 = raw1157step1 := by apply Matrix.ext; unfold raw1157step2 raw1157step1; decide +kernel
      have hl : raw1157step1Labels = labelEmbedding1 ∘ raw1157step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1157step1 raw1157step1Labels raw1157step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1683 node1683Labels := by rfl

theorem canonical1161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1161 raw1161Labels = mixedMoment B node4361 node4361Labels := by
  calc
    mixedMoment B raw1161 raw1161Labels = mixedMoment B raw1161step0 raw1161step0Labels := by
      have ha : raw1161step0 = (fun i j => raw1161 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1161step0 raw1161; decide +kernel
      have hl : raw1161step0Labels = raw1161Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1161 raw1161Labels permutation8 permutation4
    mixedMoment B raw1161step0 raw1161step0Labels = mixedMoment B raw1161step1 raw1161step1Labels := by
      have ha : raw1161step1 = raw1161step0 := by apply Matrix.ext; unfold raw1161step1 raw1161step0; decide +kernel
      have hl : raw1161step0Labels = labelEmbedding7 ∘ raw1161step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1161step0 raw1161step0Labels raw1161step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4361 node4361Labels := by rfl

theorem canonical1162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1162 raw1162Labels = mixedMoment B node939 node939Labels := by
  calc
    mixedMoment B raw1162 raw1162Labels = mixedMoment B raw1162step0 raw1162step0Labels := by
      have ha : raw1162step0 = (fun i j => raw1162 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1162step0 raw1162; decide +kernel
      have hl : raw1162step0Labels = raw1162Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1162 raw1162Labels permutation8 permutation4
    _ = mixedMoment B node939 node939Labels := by rfl

theorem canonical1163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1163 raw1163Labels = mixedMoment B node1694 node1694Labels := by
  calc
    mixedMoment B raw1163 raw1163Labels = mixedMoment B raw1163step0 raw1163step0Labels := by
      have ha : raw1163step0 = (fun i j => raw1163 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1163step0 raw1163; decide +kernel
      have hl : raw1163step0Labels = raw1163Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1163 raw1163Labels permutation9 permutation6
    mixedMoment B raw1163step0 raw1163step0Labels = mixedMoment B raw1163step1 raw1163step1Labels := by
      have ha : raw1163step1 = -raw1163step0 := by apply Matrix.ext; change ∀ i j, raw1163step1 i j = -(raw1163step0 i j); unfold raw1163step1 raw1163step0; decide +kernel
      have hl : raw1163step1Labels = raw1163step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1163step1 raw1163step1Labels = mixedMoment B raw1163step2 raw1163step2Labels := by
      have ha : raw1163step2 = raw1163step1 := by apply Matrix.ext; unfold raw1163step2 raw1163step1; decide +kernel
      have hl : raw1163step1Labels = labelEmbedding1 ∘ raw1163step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1163step1 raw1163step1Labels raw1163step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1694 node1694Labels := by rfl

theorem canonical1248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1248 raw1248Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw1248 raw1248Labels = mixedMoment B raw1248step0 raw1248step0Labels := by
      have ha : raw1248step0 = (fun i j => raw1248 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1248step0 raw1248; decide +kernel
      have hl : raw1248step0Labels = raw1248Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1248 raw1248Labels permutation32 permutation4
    mixedMoment B raw1248step0 raw1248step0Labels = mixedMoment B raw1248step1 raw1248step1Labels := by
      have ha : raw1248step1 = raw1248step0 := by apply Matrix.ext; unfold raw1248step1 raw1248step0; decide +kernel
      have hl : raw1248step0Labels = labelEmbedding7 ∘ raw1248step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1248step0 raw1248step0Labels raw1248step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

theorem canonical1249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1249 raw1249Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw1249 raw1249Labels = mixedMoment B raw1249step0 raw1249step0Labels := by
      have ha : raw1249step0 = (fun i j => raw1249 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1249step0 raw1249; decide +kernel
      have hl : raw1249step0Labels = raw1249Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1249 raw1249Labels permutation32 permutation4
    _ = mixedMoment B node1035 node1035Labels := by rfl

theorem canonical1250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1250 raw1250Labels = mixedMoment B node1645 node1645Labels := by
  calc
    mixedMoment B raw1250 raw1250Labels = mixedMoment B raw1250step0 raw1250step0Labels := by
      have ha : raw1250step0 = (fun i j => raw1250 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1250step0 raw1250; decide +kernel
      have hl : raw1250step0Labels = raw1250Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1250 raw1250Labels permutation38 permutation6
    mixedMoment B raw1250step0 raw1250step0Labels = mixedMoment B raw1250step1 raw1250step1Labels := by
      have ha : raw1250step1 = -raw1250step0 := by apply Matrix.ext; change ∀ i j, raw1250step1 i j = -(raw1250step0 i j); unfold raw1250step1 raw1250step0; decide +kernel
      have hl : raw1250step1Labels = raw1250step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1250step1 raw1250step1Labels = mixedMoment B raw1250step2 raw1250step2Labels := by
      have ha : raw1250step2 = raw1250step1 := by apply Matrix.ext; unfold raw1250step2 raw1250step1; decide +kernel
      have hl : raw1250step1Labels = labelEmbedding1 ∘ raw1250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1250step1 raw1250step1Labels raw1250step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1645 node1645Labels := by rfl

theorem canonical1251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1251 raw1251Labels = mixedMoment B node4454 node4454Labels := by
  calc
    mixedMoment B raw1251 raw1251Labels = mixedMoment B raw1251step0 raw1251step0Labels := by
      have ha : raw1251step0 = (fun i j => raw1251 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1251step0 raw1251; decide +kernel
      have hl : raw1251step0Labels = raw1251Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1251 raw1251Labels permutation8 permutation4
    mixedMoment B raw1251step0 raw1251step0Labels = mixedMoment B raw1251step1 raw1251step1Labels := by
      have ha : raw1251step1 = raw1251step0 := by apply Matrix.ext; unfold raw1251step1 raw1251step0; decide +kernel
      have hl : raw1251step0Labels = labelEmbedding7 ∘ raw1251step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1251step0 raw1251step0Labels raw1251step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4454 node4454Labels := by rfl

theorem canonical1252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1252 raw1252Labels = mixedMoment B node1037 node1037Labels := by
  calc
    mixedMoment B raw1252 raw1252Labels = mixedMoment B raw1252step0 raw1252step0Labels := by
      have ha : raw1252step0 = (fun i j => raw1252 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1252step0 raw1252; decide +kernel
      have hl : raw1252step0Labels = raw1252Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1252 raw1252Labels permutation8 permutation4
    _ = mixedMoment B node1037 node1037Labels := by rfl

theorem canonical1253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1253 raw1253Labels = mixedMoment B node1647 node1647Labels := by
  calc
    mixedMoment B raw1253 raw1253Labels = mixedMoment B raw1253step0 raw1253step0Labels := by
      have ha : raw1253step0 = (fun i j => raw1253 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1253step0 raw1253; decide +kernel
      have hl : raw1253step0Labels = raw1253Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1253 raw1253Labels permutation10 permutation6
    mixedMoment B raw1253step0 raw1253step0Labels = mixedMoment B raw1253step1 raw1253step1Labels := by
      have ha : raw1253step1 = -raw1253step0 := by apply Matrix.ext; change ∀ i j, raw1253step1 i j = -(raw1253step0 i j); unfold raw1253step1 raw1253step0; decide +kernel
      have hl : raw1253step1Labels = raw1253step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1253step1 raw1253step1Labels = mixedMoment B raw1253step2 raw1253step2Labels := by
      have ha : raw1253step2 = raw1253step1 := by apply Matrix.ext; unfold raw1253step2 raw1253step1; decide +kernel
      have hl : raw1253step1Labels = labelEmbedding1 ∘ raw1253step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1253step1 raw1253step1Labels raw1253step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1647 node1647Labels := by rfl

theorem canonical1266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1266 raw1266Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw1266 raw1266Labels = mixedMoment B raw1266step0 raw1266step0Labels := by
      have ha : raw1266step0 = (fun i j => raw1266 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1266step0 raw1266; decide +kernel
      have hl : raw1266step0Labels = raw1266Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1266 raw1266Labels permutation32 permutation4
    mixedMoment B raw1266step0 raw1266step0Labels = mixedMoment B raw1266step1 raw1266step1Labels := by
      have ha : raw1266step1 = raw1266step0 := by apply Matrix.ext; unfold raw1266step1 raw1266step0; decide +kernel
      have hl : raw1266step0Labels = labelEmbedding7 ∘ raw1266step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1266step0 raw1266step0Labels raw1266step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

theorem canonical1267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1267 raw1267Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw1267 raw1267Labels = mixedMoment B raw1267step0 raw1267step0Labels := by
      have ha : raw1267step0 = (fun i j => raw1267 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1267step0 raw1267; decide +kernel
      have hl : raw1267step0Labels = raw1267Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1267 raw1267Labels permutation32 permutation4
    _ = mixedMoment B node1044 node1044Labels := by rfl

theorem canonical1268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1268 raw1268Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw1268 raw1268Labels = mixedMoment B raw1268step0 raw1268step0Labels := by
      have ha : raw1268step0 = (fun i j => raw1268 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1268step0 raw1268; decide +kernel
      have hl : raw1268step0Labels = raw1268Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1268 raw1268Labels permutation50 permutation6
    mixedMoment B raw1268step0 raw1268step0Labels = mixedMoment B raw1268step1 raw1268step1Labels := by
      have ha : raw1268step1 = -raw1268step0 := by apply Matrix.ext; change ∀ i j, raw1268step1 i j = -(raw1268step0 i j); unfold raw1268step1 raw1268step0; decide +kernel
      have hl : raw1268step1Labels = raw1268step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1268step1 raw1268step1Labels = mixedMoment B raw1268step2 raw1268step2Labels := by
      have ha : raw1268step2 = raw1268step1 := by apply Matrix.ext; unfold raw1268step2 raw1268step1; decide +kernel
      have hl : raw1268step1Labels = labelEmbedding1 ∘ raw1268step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1268step1 raw1268step1Labels raw1268step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5169 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5169 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5169 = injectiveMoment H raw5169step0 := by
      have hz : ∀ j, raw5169 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5169step0 = (fun i j => raw5169 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5169 permutation21 hz
    injectiveMoment H raw5169step0 = injectiveMoment H raw5169step1 := by
      have hz : ∀ j, raw5169step0 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5169step1 = (fun i j => raw5169step0 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5169step0 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical671 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw671 = injectiveMoment H node169 := by
  calc
    injectiveMoment H raw671 = injectiveMoment H raw671step0 := by
      have heq : raw671step0 = -raw671 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw671).symm
    injectiveMoment H raw671step0 = injectiveMoment H raw671step1 := by
      have heq : raw671step1 = (fun i j => raw671step0 (permutation9 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw671step0 permutation9 permutation8
    _ = injectiveMoment H node169 := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7685 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7685 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7685 = injectiveMoment H raw7685step0 := by
      have hz : ∀ j, raw7685 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7685step0 = (fun i j => raw7685 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7685 permutation27 hz
    injectiveMoment H raw7685step0 = injectiveMoment H raw7685step1 := by
      have heq : raw7685step1 = (fun i j => raw7685step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7685step0 permutation7 permutation2
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

theorem canonical872 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw872 = injectiveMoment H node25 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical917 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw917 = injectiveMoment H node10 := by
  rfl

theorem canonical924 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw924 = injectiveMoment H node10 := by
  calc
    injectiveMoment H raw924 = injectiveMoment H raw924step0 := by
      have heq : raw924step0 = (fun i j => raw924 (permutation4 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw924 permutation4 permutation1
    _ = injectiveMoment H node10 := by rfl

theorem canonical926 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw926 = injectiveMoment H node3 := by
  rfl

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

theorem canonical214 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw214 = injectiveMoment H node9 := by
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

theorem sound25 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node25 = Sparse.eval value25 (momentVector H) := by
  have heq : pivotMatrix25 = (fun u v => node25 (pivotPermutation25 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node25 = injectiveMoment H pivotMatrix25 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix25 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix25 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix25 (0 : Fin 3)) =
      Sparse.eval value9 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (0 : Fin 3) = raw214 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical214 hH).trans (sound9 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix25 (1 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (1 : Fin 3) = raw917 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical917 hH).trans (sound10 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix25 (2 : Fin 3)) =
      Sparse.eval value10 (momentVector H) := by
    have heq : mergeFirst pivotMatrix25 (2 : Fin 3) = raw924 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical924 hH).trans (sound10 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node25 + (injectiveMoment H (mergeFirst pivotMatrix25 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix25 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix25 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value25, value10, value9, Sparse.eval] at hc ⊢
  linarith

theorem sound31 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node31 = Sparse.eval value31 (momentVector H) := by
  have hc : momentVector H 7 = injectiveMoment H node31 := rfl
  simp [value31, Sparse.eval, hc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical1435 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1435 = injectiveMoment H node31 := by
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical2823 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2823 = injectiveMoment H node57 := by
  calc
    injectiveMoment H raw2823 = injectiveMoment H raw2823step0 := by
      have heq : raw2823step0 = (fun i j => raw2823 (permutation4 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2823 permutation4 permutation5
    _ = injectiveMoment H node57 := by rfl

theorem canonical2845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2845 = injectiveMoment H node36 := by
  rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound169 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node169 = Sparse.eval value169 (momentVector H) := by
  have heq : pivotMatrix169 = (fun u v => node169 (pivotPermutation169 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node169 = injectiveMoment H pivotMatrix169 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix169 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix169 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix169 (0 : Fin 3)) =
      Sparse.eval value31 (momentVector H) := by
    have heq : mergeFirst pivotMatrix169 (0 : Fin 3) = raw1435 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical1435 hH).trans (sound31 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix169 (1 : Fin 3)) =
      Sparse.eval value57 (momentVector H) := by
    have heq : mergeFirst pivotMatrix169 (1 : Fin 3) = raw2823 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2823 hH).trans (sound57 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix169 (2 : Fin 3)) =
      Sparse.eval value36 (momentVector H) := by
    have heq : mergeFirst pivotMatrix169 (2 : Fin 3) = raw2845 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical2845 hH).trans (sound36 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node169 + (injectiveMoment H (mergeFirst pivotMatrix169 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix169 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix169 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value169, value31, value36, value57, Sparse.eval] at hc ⊢
  linarith

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair343 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node343 node343Labels = Sparse.eval singlePairValue343 (familyPairVector B) := by
  have hp := single_label_three B hB node343
  have hl : node343Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node343 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 1) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node343 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm2 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 2) = PairSemantics.raw7685 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node343 PairSemantics.raw7685; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7685 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value25 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 3) = PairSemantics.raw872 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node343 PairSemantics.raw872; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical872 hH).trans (PairSemantics.sound25 hH)
  have hm4 : familyPairMoment B (groupedColumns node343 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value169 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node343 (EqualityPatterns.family3.label 4) = PairSemantics.raw671 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node343 PairSemantics.raw671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical671 hH).trans (PairSemantics.sound169 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue343, PairSemantics.value0, PairSemantics.value4, PairSemantics.value11, PairSemantics.value25, PairSemantics.value169, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton2604 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node2604 node2604Labels =
      -(5 : ℝ)⁻¹ * (mixedMoment B node343 node343Labels) := by
  have h := singleton_first (by decide : 1 < 6) B hB raw246 singletonSmall2604
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall2604) = raw246Labels := by decide +kernel
  rw [hl, canonical246 B hB] at h
  have hc0 : mixedMoment B raw246 (Fin.cases (0 : Fin 1) singletonSmall2604) =
      mixedMoment B node343 node343Labels := by
    have ha : raw246 = raw247 := by apply Matrix.ext; unfold raw246 raw247; decide +kernel
    have hj : Fin.cases (0 : Fin 1) singletonSmall2604 = raw247Labels := by decide +kernel
    rw [ha, hj, canonical247 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4106 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4106 node4106Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node543 node543Labels + mixedMoment B node675 node675Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw690 singletonSmall4106
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4106) = raw690Labels := by decide +kernel
  rw [hl, canonical690 B hB] at h
  have hc0 : mixedMoment B raw690 (Fin.cases (0 : Fin 2) singletonSmall4106) =
      mixedMoment B node543 node543Labels := by
    have ha : raw690 = raw691 := by apply Matrix.ext; unfold raw690 raw691; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4106 = raw691Labels := by decide +kernel
    rw [ha, hj, canonical691 B hB]
  have hc1 : mixedMoment B raw690 (Fin.cases (1 : Fin 2) singletonSmall4106) =
      mixedMoment B node675 node675Labels := by
    have ha : raw690 = raw692 := by apply Matrix.ext; unfold raw690 raw692; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4106 = raw692Labels := by decide +kernel
    rw [ha, hj, canonical692 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4109 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4109 node4109Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node546 node546Labels + mixedMoment B node676 node676Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw699 singletonSmall4109
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4109) = raw699Labels := by decide +kernel
  rw [hl, canonical699 B hB] at h
  have hc0 : mixedMoment B raw699 (Fin.cases (0 : Fin 2) singletonSmall4109) =
      mixedMoment B node546 node546Labels := by
    have ha : raw699 = raw700 := by apply Matrix.ext; unfold raw699 raw700; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4109 = raw700Labels := by decide +kernel
    rw [ha, hj, canonical700 B hB]
  have hc1 : mixedMoment B raw699 (Fin.cases (1 : Fin 2) singletonSmall4109) =
      mixedMoment B node676 node676Labels := by
    have ha : raw699 = raw701 := by apply Matrix.ext; unfold raw699 raw701; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4109 = raw701Labels := by decide +kernel
    rw [ha, hj, canonical701 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4111 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4111 node4111Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node548 node548Labels + mixedMoment B node685 node685Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw705 singletonSmall4111
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4111) = raw705Labels := by decide +kernel
  rw [hl, canonical705 B hB] at h
  have hc0 : mixedMoment B raw705 (Fin.cases (0 : Fin 2) singletonSmall4111) =
      mixedMoment B node548 node548Labels := by
    have ha : raw705 = raw706 := by apply Matrix.ext; unfold raw705 raw706; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4111 = raw706Labels := by decide +kernel
    rw [ha, hj, canonical706 B hB]
  have hc1 : mixedMoment B raw705 (Fin.cases (1 : Fin 2) singletonSmall4111) =
      mixedMoment B node685 node685Labels := by
    have ha : raw705 = raw707 := by apply Matrix.ext; unfold raw705 raw707; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4111 = raw707Labels := by decide +kernel
    rw [ha, hj, canonical707 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4132 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4132 node4132Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node562 node562Labels + mixedMoment B node679 node679Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw741 singletonSmall4132
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4132) = raw741Labels := by decide +kernel
  rw [hl, canonical741 B hB] at h
  have hc0 : mixedMoment B raw741 (Fin.cases (0 : Fin 2) singletonSmall4132) =
      mixedMoment B node562 node562Labels := by
    have ha : raw741 = raw742 := by apply Matrix.ext; unfold raw741 raw742; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4132 = raw742Labels := by decide +kernel
    rw [ha, hj, canonical742 B hB]
  have hc1 : mixedMoment B raw741 (Fin.cases (1 : Fin 2) singletonSmall4132) =
      mixedMoment B node679 node679Labels := by
    have ha : raw741 = raw743 := by apply Matrix.ext; unfold raw741 raw743; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4132 = raw743Labels := by decide +kernel
    rw [ha, hj, canonical743 B hB]
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

theorem singleton4291 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4291 node4291Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node869 node869Labels + mixedMoment B node1561 node1561Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1035 singletonSmall4291
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4291) = raw1035Labels := by decide +kernel
  rw [hl, canonical1035 B hB] at h
  have hc0 : mixedMoment B raw1035 (Fin.cases (0 : Fin 2) singletonSmall4291) =
      mixedMoment B node869 node869Labels := by
    have ha : raw1035 = raw1036 := by apply Matrix.ext; unfold raw1035 raw1036; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4291 = raw1036Labels := by decide +kernel
    rw [ha, hj, canonical1036 B hB]
  have hc1 : mixedMoment B raw1035 (Fin.cases (1 : Fin 2) singletonSmall4291) =
      mixedMoment B node1561 node1561Labels := by
    have ha : raw1035 = raw1037 := by apply Matrix.ext; unfold raw1035 raw1037; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4291 = raw1037Labels := by decide +kernel
    rw [ha, hj, canonical1037 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4294 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4294 node4294Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node872 node872Labels + mixedMoment B node1562 node1562Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1044 singletonSmall4294
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4294) = raw1044Labels := by decide +kernel
  rw [hl, canonical1044 B hB] at h
  have hc0 : mixedMoment B raw1044 (Fin.cases (0 : Fin 2) singletonSmall4294) =
      mixedMoment B node872 node872Labels := by
    have ha : raw1044 = raw1045 := by apply Matrix.ext; unfold raw1044 raw1045; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4294 = raw1045Labels := by decide +kernel
    rw [ha, hj, canonical1045 B hB]
  have hc1 : mixedMoment B raw1044 (Fin.cases (1 : Fin 2) singletonSmall4294) =
      mixedMoment B node1562 node1562Labels := by
    have ha : raw1044 = raw1046 := by apply Matrix.ext; unfold raw1044 raw1046; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4294 = raw1046Labels := by decide +kernel
    rw [ha, hj, canonical1046 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4296 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4296 node4296Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node874 node874Labels + mixedMoment B node1570 node1570Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1050 singletonSmall4296
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4296) = raw1050Labels := by decide +kernel
  rw [hl, canonical1050 B hB] at h
  have hc0 : mixedMoment B raw1050 (Fin.cases (0 : Fin 2) singletonSmall4296) =
      mixedMoment B node874 node874Labels := by
    have ha : raw1050 = raw1051 := by apply Matrix.ext; unfold raw1050 raw1051; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4296 = raw1051Labels := by decide +kernel
    rw [ha, hj, canonical1051 B hB]
  have hc1 : mixedMoment B raw1050 (Fin.cases (1 : Fin 2) singletonSmall4296) =
      mixedMoment B node1570 node1570Labels := by
    have ha : raw1050 = raw1052 := by apply Matrix.ext; unfold raw1050 raw1052; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4296 = raw1052Labels := by decide +kernel
    rw [ha, hj, canonical1052 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4313 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4313 node4313Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node891 node891Labels + mixedMoment B node1565 node1565Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1080 singletonSmall4313
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4313) = raw1080Labels := by decide +kernel
  rw [hl, canonical1080 B hB] at h
  have hc0 : mixedMoment B raw1080 (Fin.cases (0 : Fin 2) singletonSmall4313) =
      mixedMoment B node891 node891Labels := by
    have ha : raw1080 = raw1081 := by apply Matrix.ext; unfold raw1080 raw1081; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4313 = raw1081Labels := by decide +kernel
    rw [ha, hj, canonical1081 B hB]
  have hc1 : mixedMoment B raw1080 (Fin.cases (1 : Fin 2) singletonSmall4313) =
      mixedMoment B node1565 node1565Labels := by
    have ha : raw1080 = raw1082 := by apply Matrix.ext; unfold raw1080 raw1082; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4313 = raw1082Labels := by decide +kernel
    rw [ha, hj, canonical1082 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4354 node4354Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node932 node932Labels + mixedMoment B node1681 node1681Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1146 singletonSmall4354
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4354) = raw1146Labels := by decide +kernel
  rw [hl, canonical1146 B hB] at h
  have hc0 : mixedMoment B raw1146 (Fin.cases (0 : Fin 2) singletonSmall4354) =
      mixedMoment B node932 node932Labels := by
    have ha : raw1146 = raw1147 := by apply Matrix.ext; unfold raw1146 raw1147; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4354 = raw1147Labels := by decide +kernel
    rw [ha, hj, canonical1147 B hB]
  have hc1 : mixedMoment B raw1146 (Fin.cases (1 : Fin 2) singletonSmall4354) =
      mixedMoment B node1681 node1681Labels := by
    have ha : raw1146 = raw1148 := by apply Matrix.ext; unfold raw1146 raw1148; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4354 = raw1148Labels := by decide +kernel
    rw [ha, hj, canonical1148 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4359 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4359 node4359Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node937 node937Labels + mixedMoment B node1683 node1683Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1155 singletonSmall4359
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4359) = raw1155Labels := by decide +kernel
  rw [hl, canonical1155 B hB] at h
  have hc0 : mixedMoment B raw1155 (Fin.cases (0 : Fin 2) singletonSmall4359) =
      mixedMoment B node937 node937Labels := by
    have ha : raw1155 = raw1156 := by apply Matrix.ext; unfold raw1155 raw1156; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4359 = raw1156Labels := by decide +kernel
    rw [ha, hj, canonical1156 B hB]
  have hc1 : mixedMoment B raw1155 (Fin.cases (1 : Fin 2) singletonSmall4359) =
      mixedMoment B node1683 node1683Labels := by
    have ha : raw1155 = raw1157 := by apply Matrix.ext; unfold raw1155 raw1157; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4359 = raw1157Labels := by decide +kernel
    rw [ha, hj, canonical1157 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4361 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4361 node4361Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node939 node939Labels + mixedMoment B node1694 node1694Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1161 singletonSmall4361
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4361) = raw1161Labels := by decide +kernel
  rw [hl, canonical1161 B hB] at h
  have hc0 : mixedMoment B raw1161 (Fin.cases (0 : Fin 2) singletonSmall4361) =
      mixedMoment B node939 node939Labels := by
    have ha : raw1161 = raw1162 := by apply Matrix.ext; unfold raw1161 raw1162; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4361 = raw1162Labels := by decide +kernel
    rw [ha, hj, canonical1162 B hB]
  have hc1 : mixedMoment B raw1161 (Fin.cases (1 : Fin 2) singletonSmall4361) =
      mixedMoment B node1694 node1694Labels := by
    have ha : raw1161 = raw1163 := by apply Matrix.ext; unfold raw1161 raw1163; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4361 = raw1163Labels := by decide +kernel
    rw [ha, hj, canonical1163 B hB]
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

theorem singleton4452 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4452 node4452Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1035 node1035Labels + mixedMoment B node1645 node1645Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1248 singletonSmall4452
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4452) = raw1248Labels := by decide +kernel
  rw [hl, canonical1248 B hB] at h
  have hc0 : mixedMoment B raw1248 (Fin.cases (0 : Fin 2) singletonSmall4452) =
      mixedMoment B node1035 node1035Labels := by
    have ha : raw1248 = raw1249 := by apply Matrix.ext; unfold raw1248 raw1249; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4452 = raw1249Labels := by decide +kernel
    rw [ha, hj, canonical1249 B hB]
  have hc1 : mixedMoment B raw1248 (Fin.cases (1 : Fin 2) singletonSmall4452) =
      mixedMoment B node1645 node1645Labels := by
    have ha : raw1248 = raw1250 := by apply Matrix.ext; unfold raw1248 raw1250; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4452 = raw1250Labels := by decide +kernel
    rw [ha, hj, canonical1250 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4454 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4454 node4454Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1037 node1037Labels + mixedMoment B node1647 node1647Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1251 singletonSmall4454
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4454) = raw1251Labels := by decide +kernel
  rw [hl, canonical1251 B hB] at h
  have hc0 : mixedMoment B raw1251 (Fin.cases (0 : Fin 2) singletonSmall4454) =
      mixedMoment B node1037 node1037Labels := by
    have ha : raw1251 = raw1252 := by apply Matrix.ext; unfold raw1251 raw1252; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4454 = raw1252Labels := by decide +kernel
    rw [ha, hj, canonical1252 B hB]
  have hc1 : mixedMoment B raw1251 (Fin.cases (1 : Fin 2) singletonSmall4454) =
      mixedMoment B node1647 node1647Labels := by
    have ha : raw1251 = raw1253 := by apply Matrix.ext; unfold raw1251 raw1253; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4454 = raw1253Labels := by decide +kernel
    rw [ha, hj, canonical1253 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4461 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4461 node4461Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1044 node1044Labels + mixedMoment B node1737 node1737Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1266 singletonSmall4461
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4461) = raw1266Labels := by decide +kernel
  rw [hl, canonical1266 B hB] at h
  have hc0 : mixedMoment B raw1266 (Fin.cases (0 : Fin 2) singletonSmall4461) =
      mixedMoment B node1044 node1044Labels := by
    have ha : raw1266 = raw1267 := by apply Matrix.ext; unfold raw1266 raw1267; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4461 = raw1267Labels := by decide +kernel
    rw [ha, hj, canonical1267 B hB]
  have hc1 : mixedMoment B raw1266 (Fin.cases (1 : Fin 2) singletonSmall4461) =
      mixedMoment B node1737 node1737Labels := by
    have ha : raw1266 = raw1268 := by apply Matrix.ext; unfold raw1266 raw1268; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4461 = raw1268Labels := by decide +kernel
    rw [ha, hj, canonical1268 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4491 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4491 node4491Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1075 node1075Labels + mixedMoment B node1653 node1653Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1287 singletonSmall4491
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4491) = raw1287Labels := by decide +kernel
  rw [hl, canonical1287 B hB] at h
  have hc0 : mixedMoment B raw1287 (Fin.cases (0 : Fin 2) singletonSmall4491) =
      mixedMoment B node1075 node1075Labels := by
    have ha : raw1287 = raw1288 := by apply Matrix.ext; unfold raw1287 raw1288; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4491 = raw1288Labels := by decide +kernel
    rw [ha, hj, canonical1288 B hB]
  have hc1 : mixedMoment B raw1287 (Fin.cases (1 : Fin 2) singletonSmall4491) =
      mixedMoment B node1653 node1653Labels := by
    have ha : raw1287 = raw1289 := by apply Matrix.ext; unfold raw1287 raw1289; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4491 = raw1289Labels := by decide +kernel
    rw [ha, hj, canonical1289 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5080 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5080 node5080Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2488 node2488Labels + mixedMoment B node3478 node3478Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2106 singletonSmall5080
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5080) = raw2106Labels := by decide +kernel
  rw [hl, canonical2106 B hB] at h
  have hc0 : mixedMoment B raw2106 (Fin.cases (0 : Fin 2) singletonSmall5080) =
      mixedMoment B node2488 node2488Labels := by
    have ha : raw2106 = raw2107 := by apply Matrix.ext; unfold raw2106 raw2107; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5080 = raw2107Labels := by decide +kernel
    rw [ha, hj, canonical2107 B hB]
  have hc1 : mixedMoment B raw2106 (Fin.cases (1 : Fin 2) singletonSmall5080) =
      mixedMoment B node3478 node3478Labels := by
    have ha : raw2106 = raw2108 := by apply Matrix.ext; unfold raw2106 raw2108; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5080 = raw2108Labels := by decide +kernel
    rw [ha, hj, canonical2108 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton5176 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5176 node5176Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2604 node2604Labels + mixedMoment B node3614 node3614Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2214 singletonSmall5176
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5176) = raw2214Labels := by decide +kernel
  rw [hl, canonical2214 B hB] at h
  have hc0 : mixedMoment B raw2214 (Fin.cases (0 : Fin 2) singletonSmall5176) =
      mixedMoment B node2604 node2604Labels := by
    have ha : raw2214 = raw2215 := by apply Matrix.ext; unfold raw2214 raw2215; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5176 = raw2215Labels := by decide +kernel
    rw [ha, hj, canonical2215 B hB]
  have hc1 : mixedMoment B raw2214 (Fin.cases (1 : Fin 2) singletonSmall5176) =
      mixedMoment B node3614 node3614Labels := by
    have ha : raw2214 = raw2216 := by apply Matrix.ext; unfold raw2214 raw2216; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5176 = raw2216Labels := by decide +kernel
    rw [ha, hj, canonical2216 B hB]
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

theorem singleton5291 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5291 node5291Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2765 node2765Labels + mixedMoment B node3582 node3582Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2295 singletonSmall5291
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5291) = raw2295Labels := by decide +kernel
  rw [hl, canonical2295 B hB] at h
  have hc0 : mixedMoment B raw2295 (Fin.cases (0 : Fin 2) singletonSmall5291) =
      mixedMoment B node2765 node2765Labels := by
    have ha : raw2295 = raw2296 := by apply Matrix.ext; unfold raw2295 raw2296; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5291 = raw2296Labels := by decide +kernel
    rw [ha, hj, canonical2296 B hB]
  have hc1 : mixedMoment B raw2295 (Fin.cases (1 : Fin 2) singletonSmall5291) =
      mixedMoment B node3582 node3582Labels := by
    have ha : raw2295 = raw2297 := by apply Matrix.ext; unfold raw2295 raw2297; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5291 = raw2297Labels := by decide +kernel
    rw [ha, hj, canonical2297 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node675 node675Labels = Sparse.eval nodeValue675 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 675) = mixedMoment B node675 node675Labels := rfl
  simpa [nodeValue675, Sparse.eval] using hc.symm

theorem sound676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node676 node676Labels = Sparse.eval nodeValue676 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 676) = mixedMoment B node676 node676Labels := rfl
  simpa [nodeValue676, Sparse.eval] using hc.symm

theorem sound679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node679 node679Labels = Sparse.eval nodeValue679 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 679) = mixedMoment B node679 node679Labels := rfl
  simpa [nodeValue679, Sparse.eval] using hc.symm

theorem sound685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node685 node685Labels = Sparse.eval nodeValue685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 685) = mixedMoment B node685 node685Labels := rfl
  simpa [nodeValue685, Sparse.eval] using hc.symm

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

theorem sound869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node869 node869Labels = Sparse.eval nodeValue869 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 869) = mixedMoment B node869 node869Labels := rfl
  simpa [nodeValue869, Sparse.eval] using hc.symm

theorem sound872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node872 node872Labels = Sparse.eval nodeValue872 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 872) = mixedMoment B node872 node872Labels := rfl
  simpa [nodeValue872, Sparse.eval] using hc.symm

theorem sound874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node874 node874Labels = Sparse.eval nodeValue874 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 874) = mixedMoment B node874 node874Labels := rfl
  simpa [nodeValue874, Sparse.eval] using hc.symm

theorem sound891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node891 node891Labels = Sparse.eval nodeValue891 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 891) = mixedMoment B node891 node891Labels := rfl
  simpa [nodeValue891, Sparse.eval] using hc.symm

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

theorem sound932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node932 node932Labels = Sparse.eval nodeValue932 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 932) = mixedMoment B node932 node932Labels := rfl
  simpa [nodeValue932, Sparse.eval] using hc.symm

theorem sound937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node937 node937Labels = Sparse.eval nodeValue937 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 937) = mixedMoment B node937 node937Labels := rfl
  simpa [nodeValue937, Sparse.eval] using hc.symm

theorem sound939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node939 node939Labels = Sparse.eval nodeValue939 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 939) = mixedMoment B node939 node939Labels := rfl
  simpa [nodeValue939, Sparse.eval] using hc.symm

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

theorem sound1035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1035 node1035Labels = Sparse.eval nodeValue1035 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1035) = mixedMoment B node1035 node1035Labels := rfl
  simpa [nodeValue1035, Sparse.eval] using hc.symm

theorem sound1037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1037 node1037Labels = Sparse.eval nodeValue1037 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1037) = mixedMoment B node1037 node1037Labels := rfl
  simpa [nodeValue1037, Sparse.eval] using hc.symm

theorem sound1044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1044 node1044Labels = Sparse.eval nodeValue1044 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1044) = mixedMoment B node1044 node1044Labels := rfl
  simpa [nodeValue1044, Sparse.eval] using hc.symm

theorem sound1046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1046 node1046Labels = Sparse.eval nodeValue1046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1046) = mixedMoment B node1046 node1046Labels := rfl
  simpa [nodeValue1046, Sparse.eval] using hc.symm

theorem sound1075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1075 node1075Labels = Sparse.eval nodeValue1075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1075) = mixedMoment B node1075 node1075Labels := rfl
  simpa [nodeValue1075, Sparse.eval] using hc.symm

theorem sound1087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1087 node1087Labels = Sparse.eval nodeValue1087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1087) = mixedMoment B node1087 node1087Labels := rfl
  simpa [nodeValue1087, Sparse.eval] using hc.symm

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

theorem sound1561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1561 node1561Labels = Sparse.eval nodeValue1561 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1561) = mixedMoment B node1561 node1561Labels := rfl
  simpa [nodeValue1561, Sparse.eval] using hc.symm

theorem sound1562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1562 node1562Labels = Sparse.eval nodeValue1562 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1562) = mixedMoment B node1562 node1562Labels := rfl
  simpa [nodeValue1562, Sparse.eval] using hc.symm

theorem sound1565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1565 node1565Labels = Sparse.eval nodeValue1565 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1565) = mixedMoment B node1565 node1565Labels := rfl
  simpa [nodeValue1565, Sparse.eval] using hc.symm

theorem sound1570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1570 node1570Labels = Sparse.eval nodeValue1570 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1570) = mixedMoment B node1570 node1570Labels := rfl
  simpa [nodeValue1570, Sparse.eval] using hc.symm

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

theorem sound1645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1645 node1645Labels = Sparse.eval nodeValue1645 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1645) = mixedMoment B node1645 node1645Labels := rfl
  simpa [nodeValue1645, Sparse.eval] using hc.symm

theorem sound1647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1647 node1647Labels = Sparse.eval nodeValue1647 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1647) = mixedMoment B node1647 node1647Labels := rfl
  simpa [nodeValue1647, Sparse.eval] using hc.symm

theorem sound1653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1653 node1653Labels = Sparse.eval nodeValue1653 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1653) = mixedMoment B node1653 node1653Labels := rfl
  simpa [nodeValue1653, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1681 node1681Labels = Sparse.eval nodeValue1681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1681) = mixedMoment B node1681 node1681Labels := rfl
  simpa [nodeValue1681, Sparse.eval] using hc.symm

theorem sound1683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1683 node1683Labels = Sparse.eval nodeValue1683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1683) = mixedMoment B node1683 node1683Labels := rfl
  simpa [nodeValue1683, Sparse.eval] using hc.symm

theorem sound1694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1694 node1694Labels = Sparse.eval nodeValue1694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1694) = mixedMoment B node1694 node1694Labels := rfl
  simpa [nodeValue1694, Sparse.eval] using hc.symm

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

theorem sound1737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1737 node1737Labels = Sparse.eval nodeValue1737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1737) = mixedMoment B node1737 node1737Labels := rfl
  simpa [nodeValue1737, Sparse.eval] using hc.symm

theorem sound1739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1739 node1739Labels = Sparse.eval nodeValue1739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1739) = mixedMoment B node1739 node1739Labels := rfl
  simpa [nodeValue1739, Sparse.eval] using hc.symm

theorem sound1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1750 node1750Labels = Sparse.eval nodeValue1750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1750) = mixedMoment B node1750 node1750Labels := rfl
  simpa [nodeValue1750, Sparse.eval] using hc.symm

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

theorem sound2488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2488 node2488Labels = Sparse.eval nodeValue2488 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2488) = mixedMoment B node2488 node2488Labels := rfl
  simpa [nodeValue2488, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node343 node343Labels = Sparse.eval nodeValue343 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue343 (familyPairVector B) := singlePair343 B _hB
    _ = _ := by norm_num [singlePairValue343, nodeValue343, Sparse.eval, mixedVector] <;> ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2604 node2604Labels = Sparse.eval nodeValue2604 (mixedVector B) := by
  have h := singleton2604 B _hB
  rw [sound343 B _hB _hF] at h
  norm_num [nodeValue2604, nodeValue343, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound2765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2765 node2765Labels = Sparse.eval nodeValue2765 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2765) = mixedMoment B node2765 node2765Labels := rfl
  simpa [nodeValue2765, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3478 node3478Labels = Sparse.eval nodeValue3478 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3478) = mixedMoment B node3478 node3478Labels := rfl
  simpa [nodeValue3478, Sparse.eval] using hc.symm

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

theorem sound3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3582 node3582Labels = Sparse.eval nodeValue3582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3582) = mixedMoment B node3582 node3582Labels := rfl
  simpa [nodeValue3582, Sparse.eval] using hc.symm

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

theorem sound3614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3614 node3614Labels = Sparse.eval nodeValue3614 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3614) = mixedMoment B node3614 node3614Labels := rfl
  simpa [nodeValue3614, Sparse.eval] using hc.symm

theorem sound3632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3632 node3632Labels = Sparse.eval nodeValue3632 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3632) = mixedMoment B node3632 node3632Labels := rfl
  simpa [nodeValue3632, Sparse.eval] using hc.symm

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

theorem sound543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node543 node543Labels = Sparse.eval nodeValue543 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 543) = mixedMoment B node543 node543Labels := rfl
  simpa [nodeValue543, Sparse.eval] using hc.symm

theorem sound546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node546 node546Labels = Sparse.eval nodeValue546 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 546) = mixedMoment B node546 node546Labels := rfl
  simpa [nodeValue546, Sparse.eval] using hc.symm

theorem sound548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node548 node548Labels = Sparse.eval nodeValue548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 548) = mixedMoment B node548 node548Labels := rfl
  simpa [nodeValue548, Sparse.eval] using hc.symm

theorem sound562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node562 node562Labels = Sparse.eval nodeValue562 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 562) = mixedMoment B node562 node562Labels := rfl
  simpa [nodeValue562, Sparse.eval] using hc.symm

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

theorem sound4106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4106 node4106Labels = Sparse.eval nodeValue4106 (mixedVector B) := by
  have h := singleton4106 B _hB
  rw [sound543 B _hB _hF, sound675 B _hB _hF] at h
  norm_num [nodeValue4106, nodeValue543, nodeValue675, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4109 node4109Labels = Sparse.eval nodeValue4109 (mixedVector B) := by
  have h := singleton4109 B _hB
  rw [sound546 B _hB _hF, sound676 B _hB _hF] at h
  norm_num [nodeValue4109, nodeValue546, nodeValue676, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4111 node4111Labels = Sparse.eval nodeValue4111 (mixedVector B) := by
  have h := singleton4111 B _hB
  rw [sound548 B _hB _hF, sound685 B _hB _hF] at h
  norm_num [nodeValue4111, nodeValue548, nodeValue685, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4132 node4132Labels = Sparse.eval nodeValue4132 (mixedVector B) := by
  have h := singleton4132 B _hB
  rw [sound562 B _hB _hF, sound679 B _hB _hF] at h
  norm_num [nodeValue4132, nodeValue562, nodeValue679, Sparse.eval] at h ⊢
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

theorem sound4291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4291 node4291Labels = Sparse.eval nodeValue4291 (mixedVector B) := by
  have h := singleton4291 B _hB
  rw [sound869 B _hB _hF, sound1561 B _hB _hF] at h
  norm_num [nodeValue4291, nodeValue869, nodeValue1561, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4294 node4294Labels = Sparse.eval nodeValue4294 (mixedVector B) := by
  have h := singleton4294 B _hB
  rw [sound872 B _hB _hF, sound1562 B _hB _hF] at h
  norm_num [nodeValue4294, nodeValue872, nodeValue1562, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4296 node4296Labels = Sparse.eval nodeValue4296 (mixedVector B) := by
  have h := singleton4296 B _hB
  rw [sound874 B _hB _hF, sound1570 B _hB _hF] at h
  norm_num [nodeValue4296, nodeValue874, nodeValue1570, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4313 node4313Labels = Sparse.eval nodeValue4313 (mixedVector B) := by
  have h := singleton4313 B _hB
  rw [sound891 B _hB _hF, sound1565 B _hB _hF] at h
  norm_num [nodeValue4313, nodeValue891, nodeValue1565, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4354 node4354Labels = Sparse.eval nodeValue4354 (mixedVector B) := by
  have h := singleton4354 B _hB
  rw [sound932 B _hB _hF, sound1681 B _hB _hF] at h
  norm_num [nodeValue4354, nodeValue932, nodeValue1681, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4359 node4359Labels = Sparse.eval nodeValue4359 (mixedVector B) := by
  have h := singleton4359 B _hB
  rw [sound937 B _hB _hF, sound1683 B _hB _hF] at h
  norm_num [nodeValue4359, nodeValue937, nodeValue1683, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4361 node4361Labels = Sparse.eval nodeValue4361 (mixedVector B) := by
  have h := singleton4361 B _hB
  rw [sound939 B _hB _hF, sound1694 B _hB _hF] at h
  norm_num [nodeValue4361, nodeValue939, nodeValue1694, Sparse.eval] at h ⊢
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

theorem sound4452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4452 node4452Labels = Sparse.eval nodeValue4452 (mixedVector B) := by
  have h := singleton4452 B _hB
  rw [sound1035 B _hB _hF, sound1645 B _hB _hF] at h
  norm_num [nodeValue4452, nodeValue1035, nodeValue1645, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4454 node4454Labels = Sparse.eval nodeValue4454 (mixedVector B) := by
  have h := singleton4454 B _hB
  rw [sound1037 B _hB _hF, sound1647 B _hB _hF] at h
  norm_num [nodeValue4454, nodeValue1037, nodeValue1647, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4461 node4461Labels = Sparse.eval nodeValue4461 (mixedVector B) := by
  have h := singleton4461 B _hB
  rw [sound1044 B _hB _hF, sound1737 B _hB _hF] at h
  norm_num [nodeValue4461, nodeValue1044, nodeValue1737, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4463 node4463Labels = Sparse.eval nodeValue4463 (mixedVector B) := by
  have h := singleton4463 B _hB
  rw [sound1046 B _hB _hF, sound1750 B _hB _hF] at h
  norm_num [nodeValue4463, nodeValue1046, nodeValue1750, Sparse.eval] at h ⊢
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

theorem sound4491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4491 node4491Labels = Sparse.eval nodeValue4491 (mixedVector B) := by
  have h := singleton4491 B _hB
  rw [sound1075 B _hB _hF, sound1653 B _hB _hF] at h
  norm_num [nodeValue4491, nodeValue1075, nodeValue1653, Sparse.eval] at h ⊢
  linarith only [h]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5080 node5080Labels = Sparse.eval nodeValue5080 (mixedVector B) := by
  have h := singleton5080 B _hB
  rw [sound2488 B _hB _hF, sound3478 B _hB _hF] at h
  norm_num [nodeValue5080, nodeValue2488, nodeValue3478, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5176 node5176Labels = Sparse.eval nodeValue5176 (mixedVector B) := by
  have h := singleton5176 B _hB
  rw [sound2604 B _hB _hF, sound3614 B _hB _hF] at h
  norm_num [nodeValue5176, nodeValue2604, nodeValue3614, Sparse.eval] at h ⊢
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

theorem sound5291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5291 node5291Labels = Sparse.eval nodeValue5291 (mixedVector B) := by
  have h := singleton5291 B _hB
  rw [sound2765 B _hB _hF, sound3582 B _hB _hF] at h
  norm_num [nodeValue5291, nodeValue2765, nodeValue3582, Sparse.eval] at h ⊢
  linarith only [h]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources47
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1517 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1517 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1517 + difference 0 1) (sourceB1517 + difference 1 0) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA1517 + difference 0 1) (sourceB1517 + difference 1 0) sourceC1517) = raw17694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw17694; decide +kernel
    rw [ha]
    exact (canonical17694 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1517 + difference 0 2) (sourceB1517 + difference 2 0) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA1517 + difference 0 2) (sourceB1517 + difference 2 0) sourceC1517) = raw23036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23036; decide +kernel
    rw [ha]
    exact (canonical23036 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1517 + difference 0 3) (sourceB1517 + difference 3 0) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA1517 + difference 0 3) (sourceB1517 + difference 3 0) sourceC1517) = raw23037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23037; decide +kernel
    rw [ha]
    exact (canonical23037 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1517 + difference 0 4) (sourceB1517 + difference 4 0) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1517 + difference 0 4) (sourceB1517 + difference 4 0) sourceC1517) = raw3054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw3054; decide +kernel
    rw [ha]
    exact (canonical3054 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1517 + difference 0 5) (sourceB1517 + difference 5 0) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA1517 + difference 0 5) (sourceB1517 + difference 5 0) sourceC1517) = raw3049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw3049; decide +kernel
    rw [ha]
    exact (canonical3049 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1517 + difference 1 0) (sourceB1517 + difference 0 1) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4132) := by
    have ha : (tripleCharges (sourceA1517 + difference 1 0) (sourceB1517 + difference 0 1) sourceC1517) = raw23038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23038; decide +kernel
    rw [ha]
    exact (canonical23038 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1517 + difference 1 2) (sourceB1517 + difference 2 1) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4313) := by
    have ha : (tripleCharges (sourceA1517 + difference 1 2) (sourceB1517 + difference 2 1) sourceC1517) = raw23039 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23039; decide +kernel
    rw [ha]
    exact (canonical23039 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1517 + difference 1 3) (sourceB1517 + difference 3 1) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4313) := by
    have ha : (tripleCharges (sourceA1517 + difference 1 3) (sourceB1517 + difference 3 1) sourceC1517) = raw23040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23040; decide +kernel
    rw [ha]
    exact (canonical23040 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1517 + difference 1 4) (sourceB1517 + difference 4 1) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1517 + difference 1 4) (sourceB1517 + difference 4 1) sourceC1517) = raw21243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw21243; decide +kernel
    rw [ha]
    exact (canonical21243 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1517 + difference 1 5) (sourceB1517 + difference 5 1) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4491) := by
    have ha : (tripleCharges (sourceA1517 + difference 1 5) (sourceB1517 + difference 5 1) sourceC1517) = raw23041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23041; decide +kernel
    rw [ha]
    exact (canonical23041 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1517 + difference 2 0) (sourceB1517 + difference 0 2) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4106) := by
    have ha : (tripleCharges (sourceA1517 + difference 2 0) (sourceB1517 + difference 0 2) sourceC1517) = raw23042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23042; decide +kernel
    rw [ha]
    exact (canonical23042 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1517 + difference 2 1) (sourceB1517 + difference 1 2) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA1517 + difference 2 1) (sourceB1517 + difference 1 2) sourceC1517) = raw23043 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23043; decide +kernel
    rw [ha]
    exact (canonical23043 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1517 + difference 2 3) (sourceB1517 + difference 3 2) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4291) := by
    have ha : (tripleCharges (sourceA1517 + difference 2 3) (sourceB1517 + difference 3 2) sourceC1517) = raw23044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23044; decide +kernel
    rw [ha]
    exact (canonical23044 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1517 + difference 2 4) (sourceB1517 + difference 4 2) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1517 + difference 2 4) (sourceB1517 + difference 4 2) sourceC1517) = raw21248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw21248; decide +kernel
    rw [ha]
    exact (canonical21248 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1517 + difference 2 5) (sourceB1517 + difference 5 2) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA1517 + difference 2 5) (sourceB1517 + difference 5 2) sourceC1517) = raw23045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23045; decide +kernel
    rw [ha]
    exact (canonical23045 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1517 + difference 3 0) (sourceB1517 + difference 0 3) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4106) := by
    have ha : (tripleCharges (sourceA1517 + difference 3 0) (sourceB1517 + difference 0 3) sourceC1517) = raw23046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23046; decide +kernel
    rw [ha]
    exact (canonical23046 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1517 + difference 3 1) (sourceB1517 + difference 1 3) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA1517 + difference 3 1) (sourceB1517 + difference 1 3) sourceC1517) = raw23047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23047; decide +kernel
    rw [ha]
    exact (canonical23047 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1517 + difference 3 2) (sourceB1517 + difference 2 3) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4291) := by
    have ha : (tripleCharges (sourceA1517 + difference 3 2) (sourceB1517 + difference 2 3) sourceC1517) = raw23048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23048; decide +kernel
    rw [ha]
    exact (canonical23048 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1517 + difference 3 4) (sourceB1517 + difference 4 3) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1517 + difference 3 4) (sourceB1517 + difference 4 3) sourceC1517) = raw13591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw13591; decide +kernel
    rw [ha]
    exact (canonical13591 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1517 + difference 3 5) (sourceB1517 + difference 5 3) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA1517 + difference 3 5) (sourceB1517 + difference 5 3) sourceC1517) = raw13587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw13587; decide +kernel
    rw [ha]
    exact (canonical13587 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1517 + difference 4 0) (sourceB1517 + difference 0 4) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4109) := by
    have ha : (tripleCharges (sourceA1517 + difference 4 0) (sourceB1517 + difference 0 4) sourceC1517) = raw23049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23049; decide +kernel
    rw [ha]
    exact (canonical23049 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1517 + difference 4 1) (sourceB1517 + difference 1 4) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4359) := by
    have ha : (tripleCharges (sourceA1517 + difference 4 1) (sourceB1517 + difference 1 4) sourceC1517) = raw23050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23050; decide +kernel
    rw [ha]
    exact (canonical23050 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1517 + difference 4 2) (sourceB1517 + difference 2 4) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4294) := by
    have ha : (tripleCharges (sourceA1517 + difference 4 2) (sourceB1517 + difference 2 4) sourceC1517) = raw23051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23051; decide +kernel
    rw [ha]
    exact (canonical23051 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1517 + difference 4 3) (sourceB1517 + difference 3 4) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4294) := by
    have ha : (tripleCharges (sourceA1517 + difference 4 3) (sourceB1517 + difference 3 4) sourceC1517) = raw23052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23052; decide +kernel
    rw [ha]
    exact (canonical23052 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1517 + difference 4 5) (sourceB1517 + difference 5 4) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4454) := by
    have ha : (tripleCharges (sourceA1517 + difference 4 5) (sourceB1517 + difference 5 4) sourceC1517) = raw23053 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23053; decide +kernel
    rw [ha]
    exact (canonical23053 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1517 + difference 5 0) (sourceB1517 + difference 0 5) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4111) := by
    have ha : (tripleCharges (sourceA1517 + difference 5 0) (sourceB1517 + difference 0 5) sourceC1517) = raw21253 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw21253; decide +kernel
    rw [ha]
    exact (canonical21253 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1517 + difference 5 1) (sourceB1517 + difference 1 5) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4361) := by
    have ha : (tripleCharges (sourceA1517 + difference 5 1) (sourceB1517 + difference 1 5) sourceC1517) = raw21254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw21254; decide +kernel
    rw [ha]
    exact (canonical21254 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1517 + difference 5 2) (sourceB1517 + difference 2 5) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4296) := by
    have ha : (tripleCharges (sourceA1517 + difference 5 2) (sourceB1517 + difference 2 5) sourceC1517) = raw21255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw21255; decide +kernel
    rw [ha]
    exact (canonical21255 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1517 + difference 5 3) (sourceB1517 + difference 3 5) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4296) := by
    have ha : (tripleCharges (sourceA1517 + difference 5 3) (sourceB1517 + difference 3 5) sourceC1517) = raw21256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw21256; decide +kernel
    rw [ha]
    exact (canonical21256 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1517 + difference 5 4) (sourceB1517 + difference 4 5) sourceC1517) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1517 + difference 5 4) (sourceB1517 + difference 4 5) sourceC1517) = raw23054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1517 sourceB1517 sourceC1517 difference raw23054; decide +kernel
    rw [ha]
    exact (canonical23054 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1517 sourceB1517 sourceC1517
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1517, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1300 : Integer.Sparse.reindex keyMap MixedData.row1300 = numericRow1300 := by decide +kernel

theorem numericCheck1300 (x : Master → ℝ) : Integer.Sparse.eval numericRow1300 x =
    (4320 : ℝ) * reducedSource1300 x := by
  norm_num [numericRow1300, reducedSource1300, Integer.Sparse.eval, Sparse.eval, nodeValue4106, nodeValue4109, nodeValue4111, nodeValue4132, nodeValue4291, nodeValue4294, nodeValue4296, nodeValue4313, nodeValue4354, nodeValue4359, nodeValue4361, nodeValue4452, nodeValue4454, nodeValue4461, nodeValue4463, nodeValue4491, nodeValue4503, nodeValue5080, nodeValue5176, nodeValue5291, nodeValue5294] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1300 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1300 (mixedVector B) = 0 := by
  have h4106 : mixedVector B (Sum.inr 4106) = Sparse.eval nodeValue4106 (mixedVector B) := by
    change mixedMoment B node4106 node4106Labels = _
    exact sound4106 B hB hF
  have h4109 : mixedVector B (Sum.inr 4109) = Sparse.eval nodeValue4109 (mixedVector B) := by
    change mixedMoment B node4109 node4109Labels = _
    exact sound4109 B hB hF
  have h4111 : mixedVector B (Sum.inr 4111) = Sparse.eval nodeValue4111 (mixedVector B) := by
    change mixedMoment B node4111 node4111Labels = _
    exact sound4111 B hB hF
  have h4132 : mixedVector B (Sum.inr 4132) = Sparse.eval nodeValue4132 (mixedVector B) := by
    change mixedMoment B node4132 node4132Labels = _
    exact sound4132 B hB hF
  have h4291 : mixedVector B (Sum.inr 4291) = Sparse.eval nodeValue4291 (mixedVector B) := by
    change mixedMoment B node4291 node4291Labels = _
    exact sound4291 B hB hF
  have h4294 : mixedVector B (Sum.inr 4294) = Sparse.eval nodeValue4294 (mixedVector B) := by
    change mixedMoment B node4294 node4294Labels = _
    exact sound4294 B hB hF
  have h4296 : mixedVector B (Sum.inr 4296) = Sparse.eval nodeValue4296 (mixedVector B) := by
    change mixedMoment B node4296 node4296Labels = _
    exact sound4296 B hB hF
  have h4313 : mixedVector B (Sum.inr 4313) = Sparse.eval nodeValue4313 (mixedVector B) := by
    change mixedMoment B node4313 node4313Labels = _
    exact sound4313 B hB hF
  have h4354 : mixedVector B (Sum.inr 4354) = Sparse.eval nodeValue4354 (mixedVector B) := by
    change mixedMoment B node4354 node4354Labels = _
    exact sound4354 B hB hF
  have h4359 : mixedVector B (Sum.inr 4359) = Sparse.eval nodeValue4359 (mixedVector B) := by
    change mixedMoment B node4359 node4359Labels = _
    exact sound4359 B hB hF
  have h4361 : mixedVector B (Sum.inr 4361) = Sparse.eval nodeValue4361 (mixedVector B) := by
    change mixedMoment B node4361 node4361Labels = _
    exact sound4361 B hB hF
  have h4452 : mixedVector B (Sum.inr 4452) = Sparse.eval nodeValue4452 (mixedVector B) := by
    change mixedMoment B node4452 node4452Labels = _
    exact sound4452 B hB hF
  have h4454 : mixedVector B (Sum.inr 4454) = Sparse.eval nodeValue4454 (mixedVector B) := by
    change mixedMoment B node4454 node4454Labels = _
    exact sound4454 B hB hF
  have h4461 : mixedVector B (Sum.inr 4461) = Sparse.eval nodeValue4461 (mixedVector B) := by
    change mixedMoment B node4461 node4461Labels = _
    exact sound4461 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4491 : mixedVector B (Sum.inr 4491) = Sparse.eval nodeValue4491 (mixedVector B) := by
    change mixedMoment B node4491 node4491Labels = _
    exact sound4491 B hB hF
  have h4503 : mixedVector B (Sum.inr 4503) = Sparse.eval nodeValue4503 (mixedVector B) := by
    change mixedMoment B node4503 node4503Labels = _
    exact sound4503 B hB hF
  have h5080 : mixedVector B (Sum.inr 5080) = Sparse.eval nodeValue5080 (mixedVector B) := by
    change mixedMoment B node5080 node5080Labels = _
    exact sound5080 B hB hF
  have h5176 : mixedVector B (Sum.inr 5176) = Sparse.eval nodeValue5176 (mixedVector B) := by
    change mixedMoment B node5176 node5176Labels = _
    exact sound5176 B hB hF
  have h5291 : mixedVector B (Sum.inr 5291) = Sparse.eval nodeValue5291 (mixedVector B) := by
    change mixedMoment B node5291 node5291Labels = _
    exact sound5291 B hB hF
  have h5294 : mixedVector B (Sum.inr 5294) = Sparse.eval nodeValue5294 (mixedVector B) := by
    change mixedMoment B node5294 node5294Labels = _
    exact sound5294 B hB hF
  simpa only [sourceForm1517, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4106, h4109, h4111, h4132, h4291, h4294, h4296, h4313, h4354, h4359, h4361, h4452, h4454, h4461, h4463, h4491, h4503, h5080, h5176, h5291, h5294, reducedSource1300] using sourceEq1517 B hB

theorem rowSound1300_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1300 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1300, numericCheck1300, reducedZero1300 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e_oai
