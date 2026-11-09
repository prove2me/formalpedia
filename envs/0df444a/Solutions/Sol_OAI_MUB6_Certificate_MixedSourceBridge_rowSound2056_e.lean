-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:54:12.238336+00:00
-- url     : https://prove2.me/submissions/ab26ffe3-f9a0-467b-8eb4-caa183f6a7e7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E104
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical140
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17978 raw17978Labels = mixedMoment B node5413 node5413Labels := by
  calc
    mixedMoment B raw17978 raw17978Labels = mixedMoment B raw17978step0 raw17978step0Labels := by
      have hz : ∀ j, raw17978 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17978step0 = (fun i j => raw17978 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17978step0 raw17978; decide +kernel
      have hl : raw17978step0Labels = raw17978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17978 raw17978Labels permutation434 hz
    mixedMoment B raw17978step0 raw17978step0Labels = mixedMoment B raw17978step1 raw17978step1Labels := by
      have hz : ∀ j, raw17978step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17978step1 = (fun i j => raw17978step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17978step1 raw17978step0; decide +kernel
      have hl : raw17978step1Labels = raw17978step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17978step0 raw17978step0Labels permutation80 hz
    mixedMoment B raw17978step1 raw17978step1Labels = mixedMoment B raw17978step2 raw17978step2Labels := by
      have ha : raw17978step2 = (fun i j => raw17978step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17978step2 raw17978step1; decide +kernel
      have hl : raw17978step2Labels = raw17978step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17978step1 raw17978step1Labels permutation14 permutation2
    _ = mixedMoment B node5413 node5413Labels := by rfl

theorem canonical17989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17989 raw17989Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw17989 raw17989Labels = mixedMoment B raw17989step0 raw17989step0Labels := by
      have hz : ∀ j, raw17989 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17989step0 = (fun i j => raw17989 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17989step0 raw17989; decide +kernel
      have hl : raw17989step0Labels = raw17989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17989 raw17989Labels permutation434 hz
    mixedMoment B raw17989step0 raw17989step0Labels = mixedMoment B raw17989step1 raw17989step1Labels := by
      have ha : raw17989step1 = (fun i j => raw17989step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17989step1 raw17989step0; decide +kernel
      have hl : raw17989step1Labels = raw17989step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17989step0 raw17989step0Labels permutation56 permutation2
    _ = mixedMoment B node5368 node5368Labels := by rfl

theorem canonical17994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17994 raw17994Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw17994 raw17994Labels = mixedMoment B raw17994step0 raw17994step0Labels := by
      have hz : ∀ j, raw17994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17994step0 = (fun i j => raw17994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17994step0 raw17994; decide +kernel
      have hl : raw17994step0Labels = raw17994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17994 raw17994Labels permutation346 hz
    mixedMoment B raw17994step0 raw17994step0Labels = mixedMoment B raw17994step1 raw17994step1Labels := by
      have ha : raw17994step1 = (fun i j => raw17994step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17994step1 raw17994step0; decide +kernel
      have hl : raw17994step1Labels = raw17994step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17994step0 raw17994step0Labels permutation56 permutation2
    _ = mixedMoment B node5368 node5368Labels := by rfl

theorem canonical17998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17998 raw17998Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw17998 raw17998Labels = mixedMoment B raw17998step0 raw17998step0Labels := by
      have hz : ∀ j, raw17998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17998step0 = (fun i j => raw17998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17998step0 raw17998; decide +kernel
      have hl : raw17998step0Labels = raw17998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17998 raw17998Labels permutation434 hz
    mixedMoment B raw17998step0 raw17998step0Labels = mixedMoment B raw17998step1 raw17998step1Labels := by
      have hz : ∀ j, raw17998step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17998step1 = (fun i j => raw17998step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17998step1 raw17998step0; decide +kernel
      have hl : raw17998step1Labels = raw17998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17998step0 raw17998step0Labels permutation80 hz
    mixedMoment B raw17998step1 raw17998step1Labels = mixedMoment B raw17998step2 raw17998step2Labels := by
      have ha : raw17998step2 = (fun i j => raw17998step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17998step2 raw17998step1; decide +kernel
      have hl : raw17998step2Labels = raw17998step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17998step1 raw17998step1Labels permutation8 permutation3
    mixedMoment B raw17998step2 raw17998step2Labels = mixedMoment B raw17998step3 raw17998step3Labels := by
      have ha : raw17998step3 = raw17998step2 := by apply Matrix.ext; unfold raw17998step3 raw17998step2; decide +kernel
      have hl : raw17998step2Labels = labelEmbedding6 ∘ raw17998step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17998step2 raw17998step2Labels raw17998step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

theorem canonical18000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18000 raw18000Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw18000 raw18000Labels = mixedMoment B raw18000step0 raw18000step0Labels := by
      have hz : ∀ j, raw18000 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18000step0 = (fun i j => raw18000 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18000step0 raw18000; decide +kernel
      have hl : raw18000step0Labels = raw18000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18000 raw18000Labels permutation434 hz
    mixedMoment B raw18000step0 raw18000step0Labels = mixedMoment B raw18000step1 raw18000step1Labels := by
      have ha : raw18000step1 = (fun i j => raw18000step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18000step1 raw18000step0; decide +kernel
      have hl : raw18000step1Labels = raw18000step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18000step0 raw18000step0Labels permutation127 permutation2
    mixedMoment B raw18000step1 raw18000step1Labels = mixedMoment B raw18000step2 raw18000step2Labels := by
      have ha : raw18000step2 = -raw18000step1 := by apply Matrix.ext; change ∀ i j, raw18000step2 i j = -(raw18000step1 i j); unfold raw18000step2 raw18000step1; decide +kernel
      have hl : raw18000step2Labels = raw18000step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5368 node5368Labels := by rfl

theorem canonical18001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18001 raw18001Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw18001 raw18001Labels = mixedMoment B raw18001step0 raw18001step0Labels := by
      have hz : ∀ j, raw18001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18001step0 = (fun i j => raw18001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18001step0 raw18001; decide +kernel
      have hl : raw18001step0Labels = raw18001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18001 raw18001Labels permutation346 hz
    mixedMoment B raw18001step0 raw18001step0Labels = mixedMoment B raw18001step1 raw18001step1Labels := by
      have ha : raw18001step1 = (fun i j => raw18001step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18001step1 raw18001step0; decide +kernel
      have hl : raw18001step1Labels = raw18001step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18001step0 raw18001step0Labels permutation127 permutation2
    mixedMoment B raw18001step1 raw18001step1Labels = mixedMoment B raw18001step2 raw18001step2Labels := by
      have ha : raw18001step2 = -raw18001step1 := by apply Matrix.ext; change ∀ i j, raw18001step2 i j = -(raw18001step1 i j); unfold raw18001step2 raw18001step1; decide +kernel
      have hl : raw18001step2Labels = raw18001step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5368 node5368Labels := by rfl

theorem canonical18002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18002 raw18002Labels = mixedMoment B node5413 node5413Labels := by
  calc
    mixedMoment B raw18002 raw18002Labels = mixedMoment B raw18002step0 raw18002step0Labels := by
      have hz : ∀ j, raw18002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18002step0 = (fun i j => raw18002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18002step0 raw18002; decide +kernel
      have hl : raw18002step0Labels = raw18002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18002 raw18002Labels permutation434 hz
    mixedMoment B raw18002step0 raw18002step0Labels = mixedMoment B raw18002step1 raw18002step1Labels := by
      have hz : ∀ j, raw18002step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18002step1 = (fun i j => raw18002step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18002step1 raw18002step0; decide +kernel
      have hl : raw18002step1Labels = raw18002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18002step0 raw18002step0Labels permutation80 hz
    mixedMoment B raw18002step1 raw18002step1Labels = mixedMoment B raw18002step2 raw18002step2Labels := by
      have ha : raw18002step2 = (fun i j => raw18002step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18002step2 raw18002step1; decide +kernel
      have hl : raw18002step2Labels = raw18002step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18002step1 raw18002step1Labels permutation25 permutation2
    mixedMoment B raw18002step2 raw18002step2Labels = mixedMoment B raw18002step3 raw18002step3Labels := by
      have ha : raw18002step3 = -raw18002step2 := by apply Matrix.ext; change ∀ i j, raw18002step3 i j = -(raw18002step2 i j); unfold raw18002step3 raw18002step2; decide +kernel
      have hl : raw18002step3Labels = raw18002step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5413 node5413Labels := by rfl

theorem canonical18004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18004 raw18004Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw18004 raw18004Labels = mixedMoment B raw18004step0 raw18004step0Labels := by
      have hz : ∀ j, raw18004 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18004step0 = (fun i j => raw18004 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18004step0 raw18004; decide +kernel
      have hl : raw18004step0Labels = raw18004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18004 raw18004Labels permutation434 hz
    mixedMoment B raw18004step0 raw18004step0Labels = mixedMoment B raw18004step1 raw18004step1Labels := by
      have hz : ∀ j, raw18004step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18004step1 = (fun i j => raw18004step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18004step1 raw18004step0; decide +kernel
      have hl : raw18004step1Labels = raw18004step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18004step0 raw18004step0Labels permutation80 hz
    mixedMoment B raw18004step1 raw18004step1Labels = mixedMoment B raw18004step2 raw18004step2Labels := by
      have ha : raw18004step2 = (fun i j => raw18004step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18004step2 raw18004step1; decide +kernel
      have hl : raw18004step2Labels = raw18004step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18004step1 raw18004step1Labels permutation31 permutation3
    mixedMoment B raw18004step2 raw18004step2Labels = mixedMoment B raw18004step3 raw18004step3Labels := by
      have ha : raw18004step3 = -raw18004step2 := by apply Matrix.ext; change ∀ i j, raw18004step3 i j = -(raw18004step2 i j); unfold raw18004step3 raw18004step2; decide +kernel
      have hl : raw18004step3Labels = raw18004step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18004step3 raw18004step3Labels = mixedMoment B raw18004step4 raw18004step4Labels := by
      have ha : raw18004step4 = raw18004step3 := by apply Matrix.ext; unfold raw18004step4 raw18004step3; decide +kernel
      have hl : raw18004step3Labels = labelEmbedding6 ∘ raw18004step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18004step3 raw18004step3Labels raw18004step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

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

theorem canonical1926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1926 raw1926Labels = mixedMoment B node4952 node4952Labels := by
  calc
    mixedMoment B raw1926 raw1926Labels = mixedMoment B raw1926step0 raw1926step0Labels := by
      have ha : raw1926step0 = (fun i j => raw1926 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1926step0 raw1926; decide +kernel
      have hl : raw1926step0Labels = raw1926Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1926 raw1926Labels permutation8 permutation4
    mixedMoment B raw1926step0 raw1926step0Labels = mixedMoment B raw1926step1 raw1926step1Labels := by
      have ha : raw1926step1 = raw1926step0 := by apply Matrix.ext; unfold raw1926step1 raw1926step0; decide +kernel
      have hl : raw1926step0Labels = labelEmbedding7 ∘ raw1926step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1926step0 raw1926step0Labels raw1926step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4952 node4952Labels := by rfl

theorem canonical1927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1927 raw1927Labels = mixedMoment B node2344 node2344Labels := by
  calc
    mixedMoment B raw1927 raw1927Labels = mixedMoment B raw1927step0 raw1927step0Labels := by
      have ha : raw1927step0 = (fun i j => raw1927 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1927step0 raw1927; decide +kernel
      have hl : raw1927step0Labels = raw1927Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1927 raw1927Labels permutation8 permutation4
    _ = mixedMoment B node2344 node2344Labels := by rfl

theorem canonical1928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1928 raw1928Labels = mixedMoment B node3422 node3422Labels := by
  calc
    mixedMoment B raw1928 raw1928Labels = mixedMoment B raw1928step0 raw1928step0Labels := by
      have ha : raw1928step0 = (fun i j => raw1928 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1928step0 raw1928; decide +kernel
      have hl : raw1928step0Labels = raw1928Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1928 raw1928Labels permutation31 permutation6
    mixedMoment B raw1928step0 raw1928step0Labels = mixedMoment B raw1928step1 raw1928step1Labels := by
      have ha : raw1928step1 = raw1928step0 := by apply Matrix.ext; unfold raw1928step1 raw1928step0; decide +kernel
      have hl : raw1928step0Labels = labelEmbedding1 ∘ raw1928step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1928step0 raw1928step0Labels raw1928step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3422 node3422Labels := by rfl

theorem canonical1929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1929 raw1929Labels = mixedMoment B node4953 node4953Labels := by
  calc
    mixedMoment B raw1929 raw1929Labels = mixedMoment B raw1929step0 raw1929step0Labels := by
      have ha : raw1929step0 = (fun i j => raw1929 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1929step0 raw1929; decide +kernel
      have hl : raw1929step0Labels = raw1929Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1929 raw1929Labels permutation8 permutation4
    mixedMoment B raw1929step0 raw1929step0Labels = mixedMoment B raw1929step1 raw1929step1Labels := by
      have ha : raw1929step1 = raw1929step0 := by apply Matrix.ext; unfold raw1929step1 raw1929step0; decide +kernel
      have hl : raw1929step0Labels = labelEmbedding7 ∘ raw1929step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1929step0 raw1929step0Labels raw1929step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4953 node4953Labels := by rfl

theorem canonical1930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1930 raw1930Labels = mixedMoment B node2345 node2345Labels := by
  calc
    mixedMoment B raw1930 raw1930Labels = mixedMoment B raw1930step0 raw1930step0Labels := by
      have ha : raw1930step0 = (fun i j => raw1930 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1930step0 raw1930; decide +kernel
      have hl : raw1930step0Labels = raw1930Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1930 raw1930Labels permutation8 permutation4
    _ = mixedMoment B node2345 node2345Labels := by rfl

theorem canonical1931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1931 raw1931Labels = mixedMoment B node3423 node3423Labels := by
  calc
    mixedMoment B raw1931 raw1931Labels = mixedMoment B raw1931step0 raw1931step0Labels := by
      have ha : raw1931step0 = (fun i j => raw1931 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1931step0 raw1931; decide +kernel
      have hl : raw1931step0Labels = raw1931Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1931 raw1931Labels permutation9 permutation6
    mixedMoment B raw1931step0 raw1931step0Labels = mixedMoment B raw1931step1 raw1931step1Labels := by
      have ha : raw1931step1 = -raw1931step0 := by apply Matrix.ext; change ∀ i j, raw1931step1 i j = -(raw1931step0 i j); unfold raw1931step1 raw1931step0; decide +kernel
      have hl : raw1931step1Labels = raw1931step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1931step1 raw1931step1Labels = mixedMoment B raw1931step2 raw1931step2Labels := by
      have ha : raw1931step2 = raw1931step1 := by apply Matrix.ext; unfold raw1931step2 raw1931step1; decide +kernel
      have hl : raw1931step1Labels = labelEmbedding1 ∘ raw1931step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1931step1 raw1931step1Labels raw1931step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3423 node3423Labels := by rfl

theorem canonical1965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1965 raw1965Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw1965 raw1965Labels = mixedMoment B raw1965step0 raw1965step0Labels := by
      have ha : raw1965step0 = (fun i j => raw1965 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1965step0 raw1965; decide +kernel
      have hl : raw1965step0Labels = raw1965Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1965 raw1965Labels permutation32 permutation5
    mixedMoment B raw1965step0 raw1965step0Labels = mixedMoment B raw1965step1 raw1965step1Labels := by
      have ha : raw1965step1 = raw1965step0 := by apply Matrix.ext; unfold raw1965step1 raw1965step0; decide +kernel
      have hl : raw1965step0Labels = labelEmbedding8 ∘ raw1965step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1965step0 raw1965step0Labels raw1965step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4977 node4977Labels := by rfl

theorem canonical1966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1966 raw1966Labels = mixedMoment B node2813 node2813Labels := by
  calc
    mixedMoment B raw1966 raw1966Labels = mixedMoment B raw1966step0 raw1966step0Labels := by
      have ha : raw1966step0 = (fun i j => raw1966 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1966step0 raw1966; decide +kernel
      have hl : raw1966step0Labels = raw1966Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1966 raw1966Labels permutation33 permutation4
    _ = mixedMoment B node2813 node2813Labels := by rfl

theorem canonical1967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1967 raw1967Labels = mixedMoment B node3595 node3595Labels := by
  calc
    mixedMoment B raw1967 raw1967Labels = mixedMoment B raw1967step0 raw1967step0Labels := by
      have ha : raw1967step0 = (fun i j => raw1967 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1967step0 raw1967; decide +kernel
      have hl : raw1967step0Labels = raw1967Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1967 raw1967Labels permutation34 permutation3
    mixedMoment B raw1967step0 raw1967step0Labels = mixedMoment B raw1967step1 raw1967step1Labels := by
      have ha : raw1967step1 = -raw1967step0 := by apply Matrix.ext; change ∀ i j, raw1967step1 i j = -(raw1967step0 i j); unfold raw1967step1 raw1967step0; decide +kernel
      have hl : raw1967step1Labels = raw1967step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1967step1 raw1967step1Labels = mixedMoment B raw1967step2 raw1967step2Labels := by
      have ha : raw1967step2 = raw1967step1 := by apply Matrix.ext; unfold raw1967step2 raw1967step1; decide +kernel
      have hl : raw1967step1Labels = labelEmbedding1 ∘ raw1967step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1967step1 raw1967step1Labels raw1967step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3595 node3595Labels := by rfl

theorem canonical1971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1971 raw1971Labels = mixedMoment B node4979 node4979Labels := by
  calc
    mixedMoment B raw1971 raw1971Labels = mixedMoment B raw1971step0 raw1971step0Labels := by
      have ha : raw1971step0 = (fun i j => raw1971 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1971step0 raw1971; decide +kernel
      have hl : raw1971step0Labels = raw1971Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1971 raw1971Labels permutation8 permutation5
    mixedMoment B raw1971step0 raw1971step0Labels = mixedMoment B raw1971step1 raw1971step1Labels := by
      have ha : raw1971step1 = raw1971step0 := by apply Matrix.ext; unfold raw1971step1 raw1971step0; decide +kernel
      have hl : raw1971step0Labels = labelEmbedding8 ∘ raw1971step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1971step0 raw1971step0Labels raw1971step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4979 node4979Labels := by rfl

theorem canonical1972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1972 raw1972Labels = mixedMoment B node2820 node2820Labels := by
  calc
    mixedMoment B raw1972 raw1972Labels = mixedMoment B raw1972step0 raw1972step0Labels := by
      have ha : raw1972step0 = (fun i j => raw1972 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1972step0 raw1972; decide +kernel
      have hl : raw1972step0Labels = raw1972Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1972 raw1972Labels permutation8 permutation4
    _ = mixedMoment B node2820 node2820Labels := by rfl

theorem canonical1973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1973 raw1973Labels = mixedMoment B node3596 node3596Labels := by
  calc
    mixedMoment B raw1973 raw1973Labels = mixedMoment B raw1973step0 raw1973step0Labels := by
      have ha : raw1973step0 = (fun i j => raw1973 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1973step0 raw1973; decide +kernel
      have hl : raw1973step0Labels = raw1973Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1973 raw1973Labels permutation31 permutation3
    mixedMoment B raw1973step0 raw1973step0Labels = mixedMoment B raw1973step1 raw1973step1Labels := by
      have ha : raw1973step1 = raw1973step0 := by apply Matrix.ext; unfold raw1973step1 raw1973step0; decide +kernel
      have hl : raw1973step0Labels = labelEmbedding1 ∘ raw1973step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1973step0 raw1973step0Labels raw1973step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3596 node3596Labels := by rfl

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

theorem canonical2235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2235 raw2235Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw2235 raw2235Labels = mixedMoment B raw2235step0 raw2235step0Labels := by
      have ha : raw2235step0 = (fun i j => raw2235 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2235step0 raw2235; decide +kernel
      have hl : raw2235step0Labels = raw2235Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2235 raw2235Labels permutation8 permutation5
    mixedMoment B raw2235step0 raw2235step0Labels = mixedMoment B raw2235step1 raw2235step1Labels := by
      have ha : raw2235step1 = raw2235step0 := by apply Matrix.ext; unfold raw2235step1 raw2235step0; decide +kernel
      have hl : raw2235step0Labels = labelEmbedding8 ∘ raw2235step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2235step0 raw2235step0Labels raw2235step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

theorem canonical2236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2236 raw2236Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw2236 raw2236Labels = mixedMoment B raw2236step0 raw2236step0Labels := by
      have ha : raw2236step0 = (fun i j => raw2236 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2236step0 raw2236; decide +kernel
      have hl : raw2236step0Labels = raw2236Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2236 raw2236Labels permutation9 permutation4
    _ = mixedMoment B node2889 node2889Labels := by rfl

theorem canonical2237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2237 raw2237Labels = mixedMoment B node3631 node3631Labels := by
  calc
    mixedMoment B raw2237 raw2237Labels = mixedMoment B raw2237step0 raw2237step0Labels := by
      have ha : raw2237step0 = (fun i j => raw2237 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2237step0 raw2237; decide +kernel
      have hl : raw2237step0Labels = raw2237Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2237 raw2237Labels permutation10 permutation3
    mixedMoment B raw2237step0 raw2237step0Labels = mixedMoment B raw2237step1 raw2237step1Labels := by
      have ha : raw2237step1 = -raw2237step0 := by apply Matrix.ext; change ∀ i j, raw2237step1 i j = -(raw2237step0 i j); unfold raw2237step1 raw2237step0; decide +kernel
      have hl : raw2237step1Labels = raw2237step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2237step1 raw2237step1Labels = mixedMoment B raw2237step2 raw2237step2Labels := by
      have ha : raw2237step2 = raw2237step1 := by apply Matrix.ext; unfold raw2237step2 raw2237step1; decide +kernel
      have hl : raw2237step1Labels = labelEmbedding1 ∘ raw2237step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2237step1 raw2237step1Labels raw2237step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3631 node3631Labels := by rfl

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

theorem canonical2370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2370 raw2370Labels = mixedMoment B node5335 node5335Labels := by
  calc
    mixedMoment B raw2370 raw2370Labels = mixedMoment B raw2370step0 raw2370step0Labels := by
      have ha : raw2370step0 = (fun i j => raw2370 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2370step0 raw2370; decide +kernel
      have hl : raw2370step0Labels = raw2370Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2370 raw2370Labels permutation152 permutation4
    mixedMoment B raw2370step0 raw2370step0Labels = mixedMoment B raw2370step1 raw2370step1Labels := by
      have ha : raw2370step1 = raw2370step0 := by apply Matrix.ext; unfold raw2370step1 raw2370step0; decide +kernel
      have hl : raw2370step0Labels = labelEmbedding7 ∘ raw2370step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2370step0 raw2370step0Labels raw2370step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5335 node5335Labels := by rfl

theorem canonical2371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2371 raw2371Labels = mixedMoment B node3670 node3670Labels := by
  calc
    mixedMoment B raw2371 raw2371Labels = mixedMoment B raw2371step0 raw2371step0Labels := by
      have ha : raw2371step0 = (fun i j => raw2371 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2371step0 raw2371; decide +kernel
      have hl : raw2371step0Labels = raw2371Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2371 raw2371Labels permutation152 permutation4
    _ = mixedMoment B node3670 node3670Labels := by rfl

theorem canonical2372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2372 raw2372Labels = mixedMoment B node3753 node3753Labels := by
  calc
    mixedMoment B raw2372 raw2372Labels = mixedMoment B raw2372step0 raw2372step0Labels := by
      have ha : raw2372step0 = (fun i j => raw2372 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2372step0 raw2372; decide +kernel
      have hl : raw2372step0Labels = raw2372Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2372 raw2372Labels permutation688 permutation6
    mixedMoment B raw2372step0 raw2372step0Labels = mixedMoment B raw2372step1 raw2372step1Labels := by
      have ha : raw2372step1 = raw2372step0 := by apply Matrix.ext; unfold raw2372step1 raw2372step0; decide +kernel
      have hl : raw2372step0Labels = labelEmbedding1 ∘ raw2372step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2372step0 raw2372step0Labels raw2372step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3753 node3753Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2592 raw2592Labels = mixedMoment B node5475 node5475Labels := by
  calc
    mixedMoment B raw2592 raw2592Labels = mixedMoment B raw2592step0 raw2592step0Labels := by
      have ha : raw2592step0 = (fun i j => raw2592 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2592step0 raw2592; decide +kernel
      have hl : raw2592step0Labels = raw2592Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2592 raw2592Labels permutation8 permutation4
    mixedMoment B raw2592step0 raw2592step0Labels = mixedMoment B raw2592step1 raw2592step1Labels := by
      have ha : raw2592step1 = raw2592step0 := by apply Matrix.ext; unfold raw2592step1 raw2592step0; decide +kernel
      have hl : raw2592step0Labels = labelEmbedding7 ∘ raw2592step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2592step0 raw2592step0Labels raw2592step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5475 node5475Labels := by rfl

theorem canonical2593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2593 raw2593Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw2593 raw2593Labels = mixedMoment B raw2593step0 raw2593step0Labels := by
      have ha : raw2593step0 = (fun i j => raw2593 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2593step0 raw2593; decide +kernel
      have hl : raw2593step0Labels = raw2593Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2593 raw2593Labels permutation8 permutation4
    _ = mixedMoment B node3963 node3963Labels := by rfl

theorem canonical2594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2594 raw2594Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw2594 raw2594Labels = mixedMoment B raw2594step0 raw2594step0Labels := by
      have ha : raw2594step0 = (fun i j => raw2594 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2594step0 raw2594; decide +kernel
      have hl : raw2594step0Labels = raw2594Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2594 raw2594Labels permutation24 permutation6
    mixedMoment B raw2594step0 raw2594step0Labels = mixedMoment B raw2594step1 raw2594step1Labels := by
      have ha : raw2594step1 = raw2594step0 := by apply Matrix.ext; unfold raw2594step1 raw2594step0; decide +kernel
      have hl : raw2594step0Labels = labelEmbedding1 ∘ raw2594step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2594step0 raw2594step0Labels raw2594step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3963 node3963Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical234
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29979 raw29979Labels = mixedMoment B node5475 node5475Labels := by
  calc
    mixedMoment B raw29979 raw29979Labels = mixedMoment B raw29979step0 raw29979step0Labels := by
      have hz : ∀ j, raw29979 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29979step0 = (fun i j => raw29979 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29979step0 raw29979; decide +kernel
      have hl : raw29979step0Labels = raw29979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29979 raw29979Labels permutation434 hz
    mixedMoment B raw29979step0 raw29979step0Labels = mixedMoment B raw29979step1 raw29979step1Labels := by
      have hz : ∀ j, raw29979step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29979step1 = (fun i j => raw29979step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29979step1 raw29979step0; decide +kernel
      have hl : raw29979step1Labels = raw29979step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29979step0 raw29979step0Labels permutation80 hz
    _ = mixedMoment B node5475 node5475Labels := by rfl

theorem canonical29985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29985 raw29985Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw29985 raw29985Labels = mixedMoment B raw29985step0 raw29985step0Labels := by
      have hz : ∀ j, raw29985 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29985step0 = (fun i j => raw29985 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29985step0 raw29985; decide +kernel
      have hl : raw29985step0Labels = raw29985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29985 raw29985Labels permutation434 hz
    mixedMoment B raw29985step0 raw29985step0Labels = mixedMoment B raw29985step1 raw29985step1Labels := by
      have ha : raw29985step1 = (fun i j => raw29985step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29985step1 raw29985step0; decide +kernel
      have hl : raw29985step1Labels = raw29985step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29985step0 raw29985step0Labels permutation32 permutation3
    mixedMoment B raw29985step1 raw29985step1Labels = mixedMoment B raw29985step2 raw29985step2Labels := by
      have ha : raw29985step2 = raw29985step1 := by apply Matrix.ext; unfold raw29985step2 raw29985step1; decide +kernel
      have hl : raw29985step1Labels = labelEmbedding6 ∘ raw29985step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29985step1 raw29985step1Labels raw29985step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4977 node4977Labels := by rfl

theorem canonical29989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29989 raw29989Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw29989 raw29989Labels = mixedMoment B raw29989step0 raw29989step0Labels := by
      have hz : ∀ j, raw29989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29989step0 = (fun i j => raw29989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29989step0 raw29989; decide +kernel
      have hl : raw29989step0Labels = raw29989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29989 raw29989Labels permutation346 hz
    mixedMoment B raw29989step0 raw29989step0Labels = mixedMoment B raw29989step1 raw29989step1Labels := by
      have ha : raw29989step1 = (fun i j => raw29989step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29989step1 raw29989step0; decide +kernel
      have hl : raw29989step1Labels = raw29989step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29989step0 raw29989step0Labels permutation32 permutation3
    mixedMoment B raw29989step1 raw29989step1Labels = mixedMoment B raw29989step2 raw29989step2Labels := by
      have ha : raw29989step2 = raw29989step1 := by apply Matrix.ext; unfold raw29989step2 raw29989step1; decide +kernel
      have hl : raw29989step1Labels = labelEmbedding6 ∘ raw29989step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29989step1 raw29989step1Labels raw29989step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4977 node4977Labels := by rfl

theorem canonical29993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29993 raw29993Labels = mixedMoment B node4953 node4953Labels := by
  calc
    mixedMoment B raw29993 raw29993Labels = mixedMoment B raw29993step0 raw29993step0Labels := by
      have hz : ∀ j, raw29993 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29993step0 = (fun i j => raw29993 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29993step0 raw29993; decide +kernel
      have hl : raw29993step0Labels = raw29993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29993 raw29993Labels permutation434 hz
    mixedMoment B raw29993step0 raw29993step0Labels = mixedMoment B raw29993step1 raw29993step1Labels := by
      have hz : ∀ j, raw29993step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29993step1 = (fun i j => raw29993step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29993step1 raw29993step0; decide +kernel
      have hl : raw29993step1Labels = raw29993step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29993step0 raw29993step0Labels permutation80 hz
    mixedMoment B raw29993step1 raw29993step1Labels = mixedMoment B raw29993step2 raw29993step2Labels := by
      have ha : raw29993step2 = (fun i j => raw29993step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29993step2 raw29993step1; decide +kernel
      have hl : raw29993step2Labels = raw29993step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29993step1 raw29993step1Labels permutation25 permutation2
    mixedMoment B raw29993step2 raw29993step2Labels = mixedMoment B raw29993step3 raw29993step3Labels := by
      have ha : raw29993step3 = -raw29993step2 := by apply Matrix.ext; change ∀ i j, raw29993step3 i j = -(raw29993step2 i j); unfold raw29993step3 raw29993step2; decide +kernel
      have hl : raw29993step3Labels = raw29993step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4953 node4953Labels := by rfl

theorem canonical29998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29998 raw29998Labels = mixedMoment B node4979 node4979Labels := by
  calc
    mixedMoment B raw29998 raw29998Labels = mixedMoment B raw29998step0 raw29998step0Labels := by
      have hz : ∀ j, raw29998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29998step0 = (fun i j => raw29998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29998step0 raw29998; decide +kernel
      have hl : raw29998step0Labels = raw29998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29998 raw29998Labels permutation434 hz
    mixedMoment B raw29998step0 raw29998step0Labels = mixedMoment B raw29998step1 raw29998step1Labels := by
      have hz : ∀ j, raw29998step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29998step1 = (fun i j => raw29998step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29998step1 raw29998step0; decide +kernel
      have hl : raw29998step1Labels = raw29998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29998step0 raw29998step0Labels permutation80 hz
    mixedMoment B raw29998step1 raw29998step1Labels = mixedMoment B raw29998step2 raw29998step2Labels := by
      have ha : raw29998step2 = (fun i j => raw29998step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29998step2 raw29998step1; decide +kernel
      have hl : raw29998step2Labels = raw29998step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29998step1 raw29998step1Labels permutation8 permutation3
    mixedMoment B raw29998step2 raw29998step2Labels = mixedMoment B raw29998step3 raw29998step3Labels := by
      have ha : raw29998step3 = raw29998step2 := by apply Matrix.ext; unfold raw29998step3 raw29998step2; decide +kernel
      have hl : raw29998step2Labels = labelEmbedding6 ∘ raw29998step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29998step2 raw29998step2Labels raw29998step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4979 node4979Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical276
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical35416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35416 raw35416Labels = mixedMoment B node5111 node5111Labels := by
  calc
    mixedMoment B raw35416 raw35416Labels = mixedMoment B raw35416step0 raw35416step0Labels := by
      have hz : ∀ j, raw35416 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35416step0 = (fun i j => raw35416 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35416step0 raw35416; decide +kernel
      have hl : raw35416step0Labels = raw35416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35416 raw35416Labels permutation434 hz
    mixedMoment B raw35416step0 raw35416step0Labels = mixedMoment B raw35416step1 raw35416step1Labels := by
      have hz : ∀ j, raw35416step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35416step1 = (fun i j => raw35416step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35416step1 raw35416step0; decide +kernel
      have hl : raw35416step1Labels = raw35416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35416step0 raw35416step0Labels permutation80 hz
    mixedMoment B raw35416step1 raw35416step1Labels = mixedMoment B raw35416step2 raw35416step2Labels := by
      have ha : raw35416step2 = (fun i j => raw35416step1 (permutation15 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35416step2 raw35416step1; decide +kernel
      have hl : raw35416step2Labels = raw35416step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35416step1 raw35416step1Labels permutation15 permutation2
    _ = mixedMoment B node5111 node5111Labels := by rfl

theorem canonical35417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35417 raw35417Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw35417 raw35417Labels = mixedMoment B raw35417step0 raw35417step0Labels := by
      have hz : ∀ j, raw35417 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35417step0 = (fun i j => raw35417 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35417step0 raw35417; decide +kernel
      have hl : raw35417step0Labels = raw35417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35417 raw35417Labels permutation434 hz
    mixedMoment B raw35417step0 raw35417step0Labels = mixedMoment B raw35417step1 raw35417step1Labels := by
      have ha : raw35417step1 = (fun i j => raw35417step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35417step1 raw35417step0; decide +kernel
      have hl : raw35417step1Labels = raw35417step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35417step0 raw35417step0Labels permutation126 permutation2
    mixedMoment B raw35417step1 raw35417step1Labels = mixedMoment B raw35417step2 raw35417step2Labels := by
      have ha : raw35417step2 = -raw35417step1 := by apply Matrix.ext; change ∀ i j, raw35417step2 i j = -(raw35417step1 i j); unfold raw35417step2 raw35417step1; decide +kernel
      have hl : raw35417step2Labels = raw35417step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5367 node5367Labels := by rfl

theorem canonical35418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35418 raw35418Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw35418 raw35418Labels = mixedMoment B raw35418step0 raw35418step0Labels := by
      have hz : ∀ j, raw35418 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35418step0 = (fun i j => raw35418 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35418step0 raw35418; decide +kernel
      have hl : raw35418step0Labels = raw35418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35418 raw35418Labels permutation346 hz
    mixedMoment B raw35418step0 raw35418step0Labels = mixedMoment B raw35418step1 raw35418step1Labels := by
      have ha : raw35418step1 = (fun i j => raw35418step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35418step1 raw35418step0; decide +kernel
      have hl : raw35418step1Labels = raw35418step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35418step0 raw35418step0Labels permutation126 permutation2
    mixedMoment B raw35418step1 raw35418step1Labels = mixedMoment B raw35418step2 raw35418step2Labels := by
      have ha : raw35418step2 = -raw35418step1 := by apply Matrix.ext; change ∀ i j, raw35418step2 i j = -(raw35418step1 i j); unfold raw35418step2 raw35418step1; decide +kernel
      have hl : raw35418step2Labels = raw35418step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5367 node5367Labels := by rfl

theorem canonical35419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35419 raw35419Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw35419 raw35419Labels = mixedMoment B raw35419step0 raw35419step0Labels := by
      have hz : ∀ j, raw35419 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35419step0 = (fun i j => raw35419 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35419step0 raw35419; decide +kernel
      have hl : raw35419step0Labels = raw35419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35419 raw35419Labels permutation434 hz
    mixedMoment B raw35419step0 raw35419step0Labels = mixedMoment B raw35419step1 raw35419step1Labels := by
      have hz : ∀ j, raw35419step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35419step1 = (fun i j => raw35419step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35419step1 raw35419step0; decide +kernel
      have hl : raw35419step1Labels = raw35419step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35419step0 raw35419step0Labels permutation80 hz
    mixedMoment B raw35419step1 raw35419step1Labels = mixedMoment B raw35419step2 raw35419step2Labels := by
      have hz : ∀ i, raw35419step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw35419step2 = (fun i j => raw35419step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw35419step2 raw35419step1; decide +kernel
      have hl : raw35419step2Labels = (fun j => raw35419step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35419step1 raw35419step1Labels permutation4 hz
    mixedMoment B raw35419step2 raw35419step2Labels = mixedMoment B raw35419step3 raw35419step3Labels := by
      have ha : raw35419step3 = (fun i j => raw35419step2 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35419step3 raw35419step2; decide +kernel
      have hl : raw35419step3Labels = raw35419step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35419step2 raw35419step2Labels permutation15 permutation0
    mixedMoment B raw35419step3 raw35419step3Labels = mixedMoment B raw35419step4 raw35419step4Labels := by
      have ha : raw35419step4 = raw35419step3 := by apply Matrix.ext; unfold raw35419step4 raw35419step3; decide +kernel
      have hl : raw35419step3Labels = labelEmbedding2 ∘ raw35419step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35419step3 raw35419step3Labels raw35419step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical35420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35420 raw35420Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw35420 raw35420Labels = mixedMoment B raw35420step0 raw35420step0Labels := by
      have hz : ∀ j, raw35420 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35420step0 = (fun i j => raw35420 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35420step0 raw35420; decide +kernel
      have hl : raw35420step0Labels = raw35420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35420 raw35420Labels permutation434 hz
    mixedMoment B raw35420step0 raw35420step0Labels = mixedMoment B raw35420step1 raw35420step1Labels := by
      have ha : raw35420step1 = (fun i j => raw35420step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35420step1 raw35420step0; decide +kernel
      have hl : raw35420step1Labels = raw35420step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35420step0 raw35420step0Labels permutation57 permutation2
    _ = mixedMoment B node4946 node4946Labels := by rfl

theorem canonical35421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35421 raw35421Labels = mixedMoment B node5335 node5335Labels := by
  calc
    mixedMoment B raw35421 raw35421Labels = mixedMoment B raw35421step0 raw35421step0Labels := by
      have ha : raw35421step0 = (fun i j => raw35421 (permutation272 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35421step0 raw35421; decide +kernel
      have hl : raw35421step0Labels = raw35421Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35421 raw35421Labels permutation272 permutation2
    _ = mixedMoment B node5335 node5335Labels := by rfl

theorem canonical35422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35422 raw35422Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw35422 raw35422Labels = mixedMoment B raw35422step0 raw35422step0Labels := by
      have hz : ∀ j, raw35422 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35422step0 = (fun i j => raw35422 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35422step0 raw35422; decide +kernel
      have hl : raw35422step0Labels = raw35422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35422 raw35422Labels permutation434 hz
    mixedMoment B raw35422step0 raw35422step0Labels = mixedMoment B raw35422step1 raw35422step1Labels := by
      have ha : raw35422step1 = (fun i j => raw35422step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35422step1 raw35422step0; decide +kernel
      have hl : raw35422step1Labels = raw35422step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35422step0 raw35422step0Labels permutation57 permutation2
    _ = mixedMoment B node5367 node5367Labels := by rfl

theorem canonical35423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35423 raw35423Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw35423 raw35423Labels = mixedMoment B raw35423step0 raw35423step0Labels := by
      have hz : ∀ j, raw35423 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35423step0 = (fun i j => raw35423 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35423step0 raw35423; decide +kernel
      have hl : raw35423step0Labels = raw35423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35423 raw35423Labels permutation346 hz
    mixedMoment B raw35423step0 raw35423step0Labels = mixedMoment B raw35423step1 raw35423step1Labels := by
      have ha : raw35423step1 = (fun i j => raw35423step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35423step1 raw35423step0; decide +kernel
      have hl : raw35423step1Labels = raw35423step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35423step0 raw35423step0Labels permutation57 permutation2
    _ = mixedMoment B node4946 node4946Labels := by rfl

theorem canonical35424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35424 raw35424Labels = mixedMoment B node5335 node5335Labels := by
  calc
    mixedMoment B raw35424 raw35424Labels = mixedMoment B raw35424step0 raw35424step0Labels := by
      have ha : raw35424step0 = (fun i j => raw35424 (permutation266 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35424step0 raw35424; decide +kernel
      have hl : raw35424step0Labels = raw35424Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35424 raw35424Labels permutation266 permutation2
    _ = mixedMoment B node5335 node5335Labels := by rfl

theorem canonical35425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35425 raw35425Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw35425 raw35425Labels = mixedMoment B raw35425step0 raw35425step0Labels := by
      have hz : ∀ j, raw35425 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35425step0 = (fun i j => raw35425 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35425step0 raw35425; decide +kernel
      have hl : raw35425step0Labels = raw35425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35425 raw35425Labels permutation346 hz
    mixedMoment B raw35425step0 raw35425step0Labels = mixedMoment B raw35425step1 raw35425step1Labels := by
      have ha : raw35425step1 = (fun i j => raw35425step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35425step1 raw35425step0; decide +kernel
      have hl : raw35425step1Labels = raw35425step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35425step0 raw35425step0Labels permutation57 permutation2
    _ = mixedMoment B node5367 node5367Labels := by rfl

theorem canonical35426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35426 raw35426Labels = mixedMoment B node4952 node4952Labels := by
  calc
    mixedMoment B raw35426 raw35426Labels = mixedMoment B raw35426step0 raw35426step0Labels := by
      have hz : ∀ j, raw35426 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35426step0 = (fun i j => raw35426 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35426step0 raw35426; decide +kernel
      have hl : raw35426step0Labels = raw35426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35426 raw35426Labels permutation434 hz
    mixedMoment B raw35426step0 raw35426step0Labels = mixedMoment B raw35426step1 raw35426step1Labels := by
      have hz : ∀ j, raw35426step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35426step1 = (fun i j => raw35426step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35426step1 raw35426step0; decide +kernel
      have hl : raw35426step1Labels = raw35426step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35426step0 raw35426step0Labels permutation80 hz
    mixedMoment B raw35426step1 raw35426step1Labels = mixedMoment B raw35426step2 raw35426step2Labels := by
      have ha : raw35426step2 = (fun i j => raw35426step1 (permutation15 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35426step2 raw35426step1; decide +kernel
      have hl : raw35426step2Labels = raw35426step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35426step1 raw35426step1Labels permutation15 permutation2
    _ = mixedMoment B node4952 node4952Labels := by rfl

theorem canonical35427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35427 raw35427Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw35427 raw35427Labels = mixedMoment B raw35427step0 raw35427step0Labels := by
      have hz : ∀ j, raw35427 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35427step0 = (fun i j => raw35427 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35427step0 raw35427; decide +kernel
      have hl : raw35427step0Labels = raw35427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35427 raw35427Labels permutation434 hz
    mixedMoment B raw35427step0 raw35427step0Labels = mixedMoment B raw35427step1 raw35427step1Labels := by
      have ha : raw35427step1 = (fun i j => raw35427step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35427step1 raw35427step0; decide +kernel
      have hl : raw35427step1Labels = raw35427step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35427step0 raw35427step0Labels permutation126 permutation2
    mixedMoment B raw35427step1 raw35427step1Labels = mixedMoment B raw35427step2 raw35427step2Labels := by
      have ha : raw35427step2 = -raw35427step1 := by apply Matrix.ext; change ∀ i j, raw35427step2 i j = -(raw35427step1 i j); unfold raw35427step2 raw35427step1; decide +kernel
      have hl : raw35427step2Labels = raw35427step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4946 node4946Labels := by rfl

theorem canonical35428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35428 raw35428Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw35428 raw35428Labels = mixedMoment B raw35428step0 raw35428step0Labels := by
      have hz : ∀ j, raw35428 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35428step0 = (fun i j => raw35428 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35428step0 raw35428; decide +kernel
      have hl : raw35428step0Labels = raw35428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35428 raw35428Labels permutation346 hz
    mixedMoment B raw35428step0 raw35428step0Labels = mixedMoment B raw35428step1 raw35428step1Labels := by
      have ha : raw35428step1 = (fun i j => raw35428step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35428step1 raw35428step0; decide +kernel
      have hl : raw35428step1Labels = raw35428step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35428step0 raw35428step0Labels permutation126 permutation2
    mixedMoment B raw35428step1 raw35428step1Labels = mixedMoment B raw35428step2 raw35428step2Labels := by
      have ha : raw35428step2 = -raw35428step1 := by apply Matrix.ext; change ∀ i j, raw35428step2 i j = -(raw35428step1 i j); unfold raw35428step2 raw35428step1; decide +kernel
      have hl : raw35428step2Labels = raw35428step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4946 node4946Labels := by rfl

theorem canonical35429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35429 raw35429Labels = mixedMoment B node5111 node5111Labels := by
  calc
    mixedMoment B raw35429 raw35429Labels = mixedMoment B raw35429step0 raw35429step0Labels := by
      have hz : ∀ j, raw35429 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35429step0 = (fun i j => raw35429 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35429step0 raw35429; decide +kernel
      have hl : raw35429step0Labels = raw35429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35429 raw35429Labels permutation434 hz
    mixedMoment B raw35429step0 raw35429step0Labels = mixedMoment B raw35429step1 raw35429step1Labels := by
      have hz : ∀ j, raw35429step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35429step1 = (fun i j => raw35429step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35429step1 raw35429step0; decide +kernel
      have hl : raw35429step1Labels = raw35429step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35429step0 raw35429step0Labels permutation80 hz
    mixedMoment B raw35429step1 raw35429step1Labels = mixedMoment B raw35429step2 raw35429step2Labels := by
      have ha : raw35429step2 = (fun i j => raw35429step1 (permutation24 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35429step2 raw35429step1; decide +kernel
      have hl : raw35429step2Labels = raw35429step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35429step1 raw35429step1Labels permutation24 permutation2
    mixedMoment B raw35429step2 raw35429step2Labels = mixedMoment B raw35429step3 raw35429step3Labels := by
      have ha : raw35429step3 = -raw35429step2 := by apply Matrix.ext; change ∀ i j, raw35429step3 i j = -(raw35429step2 i j); unfold raw35429step3 raw35429step2; decide +kernel
      have hl : raw35429step3Labels = raw35429step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5111 node5111Labels := by rfl

theorem canonical35430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35430 raw35430Labels = mixedMoment B node4953 node4953Labels := by
  calc
    mixedMoment B raw35430 raw35430Labels = mixedMoment B raw35430step0 raw35430step0Labels := by
      have hz : ∀ j, raw35430 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35430step0 = (fun i j => raw35430 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35430step0 raw35430; decide +kernel
      have hl : raw35430step0Labels = raw35430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35430 raw35430Labels permutation434 hz
    mixedMoment B raw35430step0 raw35430step0Labels = mixedMoment B raw35430step1 raw35430step1Labels := by
      have hz : ∀ j, raw35430step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35430step1 = (fun i j => raw35430step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35430step1 raw35430step0; decide +kernel
      have hl : raw35430step1Labels = raw35430step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35430step0 raw35430step0Labels permutation80 hz
    mixedMoment B raw35430step1 raw35430step1Labels = mixedMoment B raw35430step2 raw35430step2Labels := by
      have ha : raw35430step2 = (fun i j => raw35430step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35430step2 raw35430step1; decide +kernel
      have hl : raw35430step2Labels = raw35430step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35430step1 raw35430step1Labels permutation14 permutation2
    _ = mixedMoment B node4953 node4953Labels := by rfl

theorem canonical35431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35431 raw35431Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw35431 raw35431Labels = mixedMoment B raw35431step0 raw35431step0Labels := by
      have hz : ∀ j, raw35431 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35431step0 = (fun i j => raw35431 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35431step0 raw35431; decide +kernel
      have hl : raw35431step0Labels = raw35431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35431 raw35431Labels permutation434 hz
    mixedMoment B raw35431step0 raw35431step0Labels = mixedMoment B raw35431step1 raw35431step1Labels := by
      have ha : raw35431step1 = (fun i j => raw35431step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35431step1 raw35431step0; decide +kernel
      have hl : raw35431step1Labels = raw35431step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35431step0 raw35431step0Labels permutation151 permutation3
    mixedMoment B raw35431step1 raw35431step1Labels = mixedMoment B raw35431step2 raw35431step2Labels := by
      have ha : raw35431step2 = -raw35431step1 := by apply Matrix.ext; change ∀ i j, raw35431step2 i j = -(raw35431step1 i j); unfold raw35431step2 raw35431step1; decide +kernel
      have hl : raw35431step2Labels = raw35431step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35431step2 raw35431step2Labels = mixedMoment B raw35431step3 raw35431step3Labels := by
      have ha : raw35431step3 = raw35431step2 := by apply Matrix.ext; unfold raw35431step3 raw35431step2; decide +kernel
      have hl : raw35431step2Labels = labelEmbedding6 ∘ raw35431step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35431step2 raw35431step2Labels raw35431step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4977 node4977Labels := by rfl

theorem canonical35432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35432 raw35432Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw35432 raw35432Labels = mixedMoment B raw35432step0 raw35432step0Labels := by
      have hz : ∀ j, raw35432 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35432step0 = (fun i j => raw35432 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35432step0 raw35432; decide +kernel
      have hl : raw35432step0Labels = raw35432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35432 raw35432Labels permutation346 hz
    mixedMoment B raw35432step0 raw35432step0Labels = mixedMoment B raw35432step1 raw35432step1Labels := by
      have ha : raw35432step1 = (fun i j => raw35432step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35432step1 raw35432step0; decide +kernel
      have hl : raw35432step1Labels = raw35432step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35432step0 raw35432step0Labels permutation151 permutation3
    mixedMoment B raw35432step1 raw35432step1Labels = mixedMoment B raw35432step2 raw35432step2Labels := by
      have ha : raw35432step2 = -raw35432step1 := by apply Matrix.ext; change ∀ i j, raw35432step2 i j = -(raw35432step1 i j); unfold raw35432step2 raw35432step1; decide +kernel
      have hl : raw35432step2Labels = raw35432step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35432step2 raw35432step2Labels = mixedMoment B raw35432step3 raw35432step3Labels := by
      have ha : raw35432step3 = raw35432step2 := by apply Matrix.ext; unfold raw35432step3 raw35432step2; decide +kernel
      have hl : raw35432step2Labels = labelEmbedding6 ∘ raw35432step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35432step2 raw35432step2Labels raw35432step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4977 node4977Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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

theorem singleton4952 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4952 node4952Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2344 node2344Labels + mixedMoment B node3422 node3422Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1926 singletonSmall4952
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4952) = raw1926Labels := by decide +kernel
  rw [hl, canonical1926 B hB] at h
  have hc0 : mixedMoment B raw1926 (Fin.cases (0 : Fin 2) singletonSmall4952) =
      mixedMoment B node2344 node2344Labels := by
    have ha : raw1926 = raw1927 := by apply Matrix.ext; unfold raw1926 raw1927; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4952 = raw1927Labels := by decide +kernel
    rw [ha, hj, canonical1927 B hB]
  have hc1 : mixedMoment B raw1926 (Fin.cases (1 : Fin 2) singletonSmall4952) =
      mixedMoment B node3422 node3422Labels := by
    have ha : raw1926 = raw1928 := by apply Matrix.ext; unfold raw1926 raw1928; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4952 = raw1928Labels := by decide +kernel
    rw [ha, hj, canonical1928 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4953 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4953 node4953Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2345 node2345Labels + mixedMoment B node3423 node3423Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1929 singletonSmall4953
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4953) = raw1929Labels := by decide +kernel
  rw [hl, canonical1929 B hB] at h
  have hc0 : mixedMoment B raw1929 (Fin.cases (0 : Fin 2) singletonSmall4953) =
      mixedMoment B node2345 node2345Labels := by
    have ha : raw1929 = raw1930 := by apply Matrix.ext; unfold raw1929 raw1930; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4953 = raw1930Labels := by decide +kernel
    rw [ha, hj, canonical1930 B hB]
  have hc1 : mixedMoment B raw1929 (Fin.cases (1 : Fin 2) singletonSmall4953) =
      mixedMoment B node3423 node3423Labels := by
    have ha : raw1929 = raw1931 := by apply Matrix.ext; unfold raw1929 raw1931; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4953 = raw1931Labels := by decide +kernel
    rw [ha, hj, canonical1931 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4977 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4977 node4977Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2813 node2813Labels + mixedMoment B node3595 node3595Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1965 singletonSmall4977
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4977) = raw1965Labels := by decide +kernel
  rw [hl, canonical1965 B hB] at h
  have hc0 : mixedMoment B raw1965 (Fin.cases (0 : Fin 2) singletonSmall4977) =
      mixedMoment B node2813 node2813Labels := by
    have ha : raw1965 = raw1966 := by apply Matrix.ext; unfold raw1965 raw1966; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4977 = raw1966Labels := by decide +kernel
    rw [ha, hj, canonical1966 B hB]
  have hc1 : mixedMoment B raw1965 (Fin.cases (1 : Fin 2) singletonSmall4977) =
      mixedMoment B node3595 node3595Labels := by
    have ha : raw1965 = raw1967 := by apply Matrix.ext; unfold raw1965 raw1967; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4977 = raw1967Labels := by decide +kernel
    rw [ha, hj, canonical1967 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4979 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4979 node4979Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2820 node2820Labels + mixedMoment B node3596 node3596Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1971 singletonSmall4979
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4979) = raw1971Labels := by decide +kernel
  rw [hl, canonical1971 B hB] at h
  have hc0 : mixedMoment B raw1971 (Fin.cases (0 : Fin 2) singletonSmall4979) =
      mixedMoment B node2820 node2820Labels := by
    have ha : raw1971 = raw1972 := by apply Matrix.ext; unfold raw1971 raw1972; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4979 = raw1972Labels := by decide +kernel
    rw [ha, hj, canonical1972 B hB]
  have hc1 : mixedMoment B raw1971 (Fin.cases (1 : Fin 2) singletonSmall4979) =
      mixedMoment B node3596 node3596Labels := by
    have ha : raw1971 = raw1973 := by apply Matrix.ext; unfold raw1971 raw1973; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4979 = raw1973Labels := by decide +kernel
    rw [ha, hj, canonical1973 B hB]
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

theorem singleton5207 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5207 node5207Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2889 node2889Labels + mixedMoment B node3631 node3631Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2235 singletonSmall5207
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5207) = raw2235Labels := by decide +kernel
  rw [hl, canonical2235 B hB] at h
  have hc0 : mixedMoment B raw2235 (Fin.cases (0 : Fin 2) singletonSmall5207) =
      mixedMoment B node2889 node2889Labels := by
    have ha : raw2235 = raw2236 := by apply Matrix.ext; unfold raw2235 raw2236; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5207 = raw2236Labels := by decide +kernel
    rw [ha, hj, canonical2236 B hB]
  have hc1 : mixedMoment B raw2235 (Fin.cases (1 : Fin 2) singletonSmall5207) =
      mixedMoment B node3631 node3631Labels := by
    have ha : raw2235 = raw2237 := by apply Matrix.ext; unfold raw2235 raw2237; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5207 = raw2237Labels := by decide +kernel
    rw [ha, hj, canonical2237 B hB]
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

theorem singleton5335 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5335 node5335Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3670 node3670Labels + mixedMoment B node3753 node3753Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2370 singletonSmall5335
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5335) = raw2370Labels := by decide +kernel
  rw [hl, canonical2370 B hB] at h
  have hc0 : mixedMoment B raw2370 (Fin.cases (0 : Fin 2) singletonSmall5335) =
      mixedMoment B node3670 node3670Labels := by
    have ha : raw2370 = raw2371 := by apply Matrix.ext; unfold raw2370 raw2371; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5335 = raw2371Labels := by decide +kernel
    rw [ha, hj, canonical2371 B hB]
  have hc1 : mixedMoment B raw2370 (Fin.cases (1 : Fin 2) singletonSmall5335) =
      mixedMoment B node3753 node3753Labels := by
    have ha : raw2370 = raw2372 := by apply Matrix.ext; unfold raw2370 raw2372; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5335 = raw2372Labels := by decide +kernel
    rw [ha, hj, canonical2372 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5475 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5475 node5475Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3963 node3963Labels + mixedMoment B node3963 node3963Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2592 singletonSmall5475
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5475) = raw2592Labels := by decide +kernel
  rw [hl, canonical2592 B hB] at h
  have hc0 : mixedMoment B raw2592 (Fin.cases (0 : Fin 2) singletonSmall5475) =
      mixedMoment B node3963 node3963Labels := by
    have ha : raw2592 = raw2593 := by apply Matrix.ext; unfold raw2592 raw2593; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5475 = raw2593Labels := by decide +kernel
    rw [ha, hj, canonical2593 B hB]
  have hc1 : mixedMoment B raw2592 (Fin.cases (1 : Fin 2) singletonSmall5475) =
      mixedMoment B node3963 node3963Labels := by
    have ha : raw2592 = raw2594 := by apply Matrix.ext; unfold raw2592 raw2594; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5475 = raw2594Labels := by decide +kernel
    rw [ha, hj, canonical2594 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound2337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2337 node2337Labels = Sparse.eval nodeValue2337 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2337) = mixedMoment B node2337 node2337Labels := rfl
  simpa [nodeValue2337, Sparse.eval] using hc.symm

theorem sound2344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2344 node2344Labels = Sparse.eval nodeValue2344 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2344) = mixedMoment B node2344 node2344Labels := rfl
  simpa [nodeValue2344, Sparse.eval] using hc.symm

theorem sound2345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2345 node2345Labels = Sparse.eval nodeValue2345 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2345) = mixedMoment B node2345 node2345Labels := rfl
  simpa [nodeValue2345, Sparse.eval] using hc.symm

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

theorem sound2813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2813 node2813Labels = Sparse.eval nodeValue2813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2813) = mixedMoment B node2813 node2813Labels := rfl
  simpa [nodeValue2813, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2820 node2820Labels = Sparse.eval nodeValue2820 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2820) = mixedMoment B node2820 node2820Labels := rfl
  simpa [nodeValue2820, Sparse.eval] using hc.symm

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

theorem sound2889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2889 node2889Labels = Sparse.eval nodeValue2889 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2889) = mixedMoment B node2889 node2889Labels := rfl
  simpa [nodeValue2889, Sparse.eval] using hc.symm

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

theorem sound3412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3412 node3412Labels = Sparse.eval nodeValue3412 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3412) = mixedMoment B node3412 node3412Labels := rfl
  simpa [nodeValue3412, Sparse.eval] using hc.symm

theorem sound3422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3422 node3422Labels = Sparse.eval nodeValue3422 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3422) = mixedMoment B node3422 node3422Labels := rfl
  simpa [nodeValue3422, Sparse.eval] using hc.symm

theorem sound3423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3423 node3423Labels = Sparse.eval nodeValue3423 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3423) = mixedMoment B node3423 node3423Labels := rfl
  simpa [nodeValue3423, Sparse.eval] using hc.symm

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

theorem sound3595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3595 node3595Labels = Sparse.eval nodeValue3595 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3595) = mixedMoment B node3595 node3595Labels := rfl
  simpa [nodeValue3595, Sparse.eval] using hc.symm

theorem sound3596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3596 node3596Labels = Sparse.eval nodeValue3596 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3596) = mixedMoment B node3596 node3596Labels := rfl
  simpa [nodeValue3596, Sparse.eval] using hc.symm

theorem sound3631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3631 node3631Labels = Sparse.eval nodeValue3631 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3631) = mixedMoment B node3631 node3631Labels := rfl
  simpa [nodeValue3631, Sparse.eval] using hc.symm

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

theorem sound3670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3670 node3670Labels = Sparse.eval nodeValue3670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3670) = mixedMoment B node3670 node3670Labels := rfl
  simpa [nodeValue3670, Sparse.eval] using hc.symm

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

theorem sound3753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3753 node3753Labels = Sparse.eval nodeValue3753 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3753) = mixedMoment B node3753 node3753Labels := rfl
  simpa [nodeValue3753, Sparse.eval] using hc.symm

theorem sound3767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3767 node3767Labels = Sparse.eval nodeValue3767 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3767) = mixedMoment B node3767 node3767Labels := rfl
  simpa [nodeValue3767, Sparse.eval] using hc.symm

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

theorem sound3963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3963 node3963Labels = Sparse.eval nodeValue3963 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3963) = mixedMoment B node3963 node3963Labels := rfl
  simpa [nodeValue3963, Sparse.eval] using hc.symm

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

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

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

theorem sound4946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4946 node4946Labels = Sparse.eval nodeValue4946 (mixedVector B) := by
  have h := singleton4946 B _hB
  rw [sound2337 B _hB _hF, sound3412 B _hB _hF] at h
  norm_num [nodeValue4946, nodeValue2337, nodeValue3412, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4952 node4952Labels = Sparse.eval nodeValue4952 (mixedVector B) := by
  have h := singleton4952 B _hB
  rw [sound2344 B _hB _hF, sound3422 B _hB _hF] at h
  norm_num [nodeValue4952, nodeValue2344, nodeValue3422, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4953 node4953Labels = Sparse.eval nodeValue4953 (mixedVector B) := by
  have h := singleton4953 B _hB
  rw [sound2345 B _hB _hF, sound3423 B _hB _hF] at h
  norm_num [nodeValue4953, nodeValue2345, nodeValue3423, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4977 node4977Labels = Sparse.eval nodeValue4977 (mixedVector B) := by
  have h := singleton4977 B _hB
  rw [sound2813 B _hB _hF, sound3595 B _hB _hF] at h
  norm_num [nodeValue4977, nodeValue2813, nodeValue3595, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4979 node4979Labels = Sparse.eval nodeValue4979 (mixedVector B) := by
  have h := singleton4979 B _hB
  rw [sound2820 B _hB _hF, sound3596 B _hB _hF] at h
  norm_num [nodeValue4979, nodeValue2820, nodeValue3596, Sparse.eval] at h ⊢
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

theorem zero5111 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5111 node5111Labels = 0 := by
  exact mixedMoment_order_one B hB node5111 node5111Labels 1
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

theorem sound5111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5111 node5111Labels = Sparse.eval nodeValue5111 (mixedVector B) := by
  simpa only [nodeValue5111, Sparse.eval_nil] using zero5111 B _hB _hF

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

theorem sound5207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5207 node5207Labels = Sparse.eval nodeValue5207 (mixedVector B) := by
  have h := singleton5207 B _hB
  rw [sound2889 B _hB _hF, sound3631 B _hB _hF] at h
  norm_num [nodeValue5207, nodeValue2889, nodeValue3631, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5367 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5367 node5367Labels = 0 := by
  exact mixedMoment_order_one B hB node5367 node5367Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5335 node5335Labels = Sparse.eval nodeValue5335 (mixedVector B) := by
  have h := singleton5335 B _hB
  rw [sound3670 B _hB _hF, sound3753 B _hB _hF] at h
  norm_num [nodeValue5335, nodeValue3670, nodeValue3753, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5367 node5367Labels = Sparse.eval nodeValue5367 (mixedVector B) := by
  simpa only [nodeValue5367, Sparse.eval_nil] using zero5367 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5413 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5413 node5413Labels = 0 := by
  exact mixedMoment_order_one B hB node5413 node5413Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5413 node5413Labels = Sparse.eval nodeValue5413 (mixedVector B) := by
  simpa only [nodeValue5413, Sparse.eval_nil] using zero5413 B _hB _hF

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

theorem sound5475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5475 node5475Labels = Sparse.eval nodeValue5475 (mixedVector B) := by
  have h := singleton5475 B _hB
  rw [sound3963 B _hB _hF] at h
  norm_num [nodeValue5475, nodeValue3963, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources80
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2565 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2565 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2565 + difference 0 1) (sourceB2565 + difference 1 0) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2565 + difference 0 1) (sourceB2565 + difference 1 0) sourceC2565) = raw35416 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35416; decide +kernel
    rw [ha]
    exact (canonical35416 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2565 + difference 0 2) (sourceB2565 + difference 2 0) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2565 + difference 0 2) (sourceB2565 + difference 2 0) sourceC2565) = raw35417 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35417; decide +kernel
    rw [ha]
    exact (canonical35417 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2565 + difference 0 3) (sourceB2565 + difference 3 0) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2565 + difference 0 3) (sourceB2565 + difference 3 0) sourceC2565) = raw35418 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35418; decide +kernel
    rw [ha]
    exact (canonical35418 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2565 + difference 0 4) (sourceB2565 + difference 4 0) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA2565 + difference 0 4) (sourceB2565 + difference 4 0) sourceC2565) = raw17978 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw17978; decide +kernel
    rw [ha]
    exact (canonical17978 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2565 + difference 0 5) (sourceB2565 + difference 5 0) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2565 + difference 0 5) (sourceB2565 + difference 5 0) sourceC2565) = raw35419 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35419; decide +kernel
    rw [ha]
    exact (canonical35419 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2565 + difference 1 0) (sourceB2565 + difference 0 1) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2565 + difference 1 0) (sourceB2565 + difference 0 1) sourceC2565) = raw17998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw17998; decide +kernel
    rw [ha]
    exact (canonical17998 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2565 + difference 1 2) (sourceB2565 + difference 2 1) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2565 + difference 1 2) (sourceB2565 + difference 2 1) sourceC2565) = raw18000 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw18000; decide +kernel
    rw [ha]
    exact (canonical18000 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2565 + difference 1 3) (sourceB2565 + difference 3 1) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2565 + difference 1 3) (sourceB2565 + difference 3 1) sourceC2565) = raw18001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw18001; decide +kernel
    rw [ha]
    exact (canonical18001 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2565 + difference 1 4) (sourceB2565 + difference 4 1) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5475) := by
    have ha : (tripleCharges (sourceA2565 + difference 1 4) (sourceB2565 + difference 4 1) sourceC2565) = raw29979 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw29979; decide +kernel
    rw [ha]
    exact (canonical29979 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2565 + difference 1 5) (sourceB2565 + difference 5 1) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA2565 + difference 1 5) (sourceB2565 + difference 5 1) sourceC2565) = raw18002 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw18002; decide +kernel
    rw [ha]
    exact (canonical18002 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2565 + difference 2 0) (sourceB2565 + difference 0 2) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2565 + difference 2 0) (sourceB2565 + difference 0 2) sourceC2565) = raw29985 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw29985; decide +kernel
    rw [ha]
    exact (canonical29985 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2565 + difference 2 1) (sourceB2565 + difference 1 2) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2565 + difference 2 1) (sourceB2565 + difference 1 2) sourceC2565) = raw35420 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35420; decide +kernel
    rw [ha]
    exact (canonical35420 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2565 + difference 2 3) (sourceB2565 + difference 3 2) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5335) := by
    have ha : (tripleCharges (sourceA2565 + difference 2 3) (sourceB2565 + difference 3 2) sourceC2565) = raw35421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35421; decide +kernel
    rw [ha]
    exact (canonical35421 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2565 + difference 2 4) (sourceB2565 + difference 4 2) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2565 + difference 2 4) (sourceB2565 + difference 4 2) sourceC2565) = raw17989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw17989; decide +kernel
    rw [ha]
    exact (canonical17989 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2565 + difference 2 5) (sourceB2565 + difference 5 2) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2565 + difference 2 5) (sourceB2565 + difference 5 2) sourceC2565) = raw35422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35422; decide +kernel
    rw [ha]
    exact (canonical35422 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2565 + difference 3 0) (sourceB2565 + difference 0 3) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2565 + difference 3 0) (sourceB2565 + difference 0 3) sourceC2565) = raw29989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw29989; decide +kernel
    rw [ha]
    exact (canonical29989 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2565 + difference 3 1) (sourceB2565 + difference 1 3) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2565 + difference 3 1) (sourceB2565 + difference 1 3) sourceC2565) = raw35423 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35423; decide +kernel
    rw [ha]
    exact (canonical35423 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2565 + difference 3 2) (sourceB2565 + difference 2 3) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5335) := by
    have ha : (tripleCharges (sourceA2565 + difference 3 2) (sourceB2565 + difference 2 3) sourceC2565) = raw35424 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35424; decide +kernel
    rw [ha]
    exact (canonical35424 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2565 + difference 3 4) (sourceB2565 + difference 4 3) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2565 + difference 3 4) (sourceB2565 + difference 4 3) sourceC2565) = raw17994 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw17994; decide +kernel
    rw [ha]
    exact (canonical17994 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2565 + difference 3 5) (sourceB2565 + difference 5 3) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2565 + difference 3 5) (sourceB2565 + difference 5 3) sourceC2565) = raw35425 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35425; decide +kernel
    rw [ha]
    exact (canonical35425 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2565 + difference 4 0) (sourceB2565 + difference 0 4) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4953) := by
    have ha : (tripleCharges (sourceA2565 + difference 4 0) (sourceB2565 + difference 0 4) sourceC2565) = raw29993 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw29993; decide +kernel
    rw [ha]
    exact (canonical29993 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2565 + difference 4 1) (sourceB2565 + difference 1 4) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4952) := by
    have ha : (tripleCharges (sourceA2565 + difference 4 1) (sourceB2565 + difference 1 4) sourceC2565) = raw35426 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35426; decide +kernel
    rw [ha]
    exact (canonical35426 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2565 + difference 4 2) (sourceB2565 + difference 2 4) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2565 + difference 4 2) (sourceB2565 + difference 2 4) sourceC2565) = raw35427 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35427; decide +kernel
    rw [ha]
    exact (canonical35427 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2565 + difference 4 3) (sourceB2565 + difference 3 4) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2565 + difference 4 3) (sourceB2565 + difference 3 4) sourceC2565) = raw35428 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35428; decide +kernel
    rw [ha]
    exact (canonical35428 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2565 + difference 4 5) (sourceB2565 + difference 5 4) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2565 + difference 4 5) (sourceB2565 + difference 5 4) sourceC2565) = raw35429 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35429; decide +kernel
    rw [ha]
    exact (canonical35429 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2565 + difference 5 0) (sourceB2565 + difference 0 5) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4979) := by
    have ha : (tripleCharges (sourceA2565 + difference 5 0) (sourceB2565 + difference 0 5) sourceC2565) = raw29998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw29998; decide +kernel
    rw [ha]
    exact (canonical29998 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2565 + difference 5 1) (sourceB2565 + difference 1 5) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4953) := by
    have ha : (tripleCharges (sourceA2565 + difference 5 1) (sourceB2565 + difference 1 5) sourceC2565) = raw35430 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35430; decide +kernel
    rw [ha]
    exact (canonical35430 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2565 + difference 5 2) (sourceB2565 + difference 2 5) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2565 + difference 5 2) (sourceB2565 + difference 2 5) sourceC2565) = raw35431 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35431; decide +kernel
    rw [ha]
    exact (canonical35431 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2565 + difference 5 3) (sourceB2565 + difference 3 5) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2565 + difference 5 3) (sourceB2565 + difference 3 5) sourceC2565) = raw35432 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw35432; decide +kernel
    rw [ha]
    exact (canonical35432 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2565 + difference 5 4) (sourceB2565 + difference 4 5) sourceC2565) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2565 + difference 5 4) (sourceB2565 + difference 4 5) sourceC2565) = raw18004 := by
      apply Matrix.ext; unfold tripleCharges sourceA2565 sourceB2565 sourceC2565 difference raw18004; decide +kernel
    rw [ha]
    exact (canonical18004 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2565 sourceB2565 sourceC2565
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2565, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2056 : Integer.Sparse.reindex keyMap MixedData.row2056 = numericRow2056 := by decide +kernel

theorem numericCheck2056 (x : Master → ℝ) : Integer.Sparse.eval numericRow2056 x =
    (4 : ℝ) * reducedSource2056 x := by
  norm_num [numericRow2056, reducedSource2056, Integer.Sparse.eval, Sparse.eval, nodeValue4092, nodeValue4946, nodeValue4952, nodeValue4953, nodeValue4977, nodeValue4979, nodeValue5111, nodeValue5207, nodeValue5335, nodeValue5367, nodeValue5368, nodeValue5413, nodeValue5475]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2056 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2056 (mixedVector B) = 0 := by
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  have h4946 : mixedVector B (Sum.inr 4946) = Sparse.eval nodeValue4946 (mixedVector B) := by
    change mixedMoment B node4946 node4946Labels = _
    exact sound4946 B hB hF
  have h4952 : mixedVector B (Sum.inr 4952) = Sparse.eval nodeValue4952 (mixedVector B) := by
    change mixedMoment B node4952 node4952Labels = _
    exact sound4952 B hB hF
  have h4953 : mixedVector B (Sum.inr 4953) = Sparse.eval nodeValue4953 (mixedVector B) := by
    change mixedMoment B node4953 node4953Labels = _
    exact sound4953 B hB hF
  have h4977 : mixedVector B (Sum.inr 4977) = Sparse.eval nodeValue4977 (mixedVector B) := by
    change mixedMoment B node4977 node4977Labels = _
    exact sound4977 B hB hF
  have h4979 : mixedVector B (Sum.inr 4979) = Sparse.eval nodeValue4979 (mixedVector B) := by
    change mixedMoment B node4979 node4979Labels = _
    exact sound4979 B hB hF
  have h5111 : mixedVector B (Sum.inr 5111) = Sparse.eval nodeValue5111 (mixedVector B) := by
    change mixedMoment B node5111 node5111Labels = _
    exact sound5111 B hB hF
  have h5207 : mixedVector B (Sum.inr 5207) = Sparse.eval nodeValue5207 (mixedVector B) := by
    change mixedMoment B node5207 node5207Labels = _
    exact sound5207 B hB hF
  have h5335 : mixedVector B (Sum.inr 5335) = Sparse.eval nodeValue5335 (mixedVector B) := by
    change mixedMoment B node5335 node5335Labels = _
    exact sound5335 B hB hF
  have h5367 : mixedVector B (Sum.inr 5367) = Sparse.eval nodeValue5367 (mixedVector B) := by
    change mixedMoment B node5367 node5367Labels = _
    exact sound5367 B hB hF
  have h5368 : mixedVector B (Sum.inr 5368) = Sparse.eval nodeValue5368 (mixedVector B) := by
    change mixedMoment B node5368 node5368Labels = _
    exact sound5368 B hB hF
  have h5413 : mixedVector B (Sum.inr 5413) = Sparse.eval nodeValue5413 (mixedVector B) := by
    change mixedMoment B node5413 node5413Labels = _
    exact sound5413 B hB hF
  have h5475 : mixedVector B (Sum.inr 5475) = Sparse.eval nodeValue5475 (mixedVector B) := by
    change mixedMoment B node5475 node5475Labels = _
    exact sound5475 B hB hF
  simpa only [sourceForm2565, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4092, h4946, h4952, h4953, h4977, h4979, h5111, h5207, h5335, h5367, h5368, h5413, h5475, reducedSource2056] using sourceEq2565 B hB

theorem rowSound2056_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2056 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2056, numericCheck2056, reducedZero2056 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056_e_oai
