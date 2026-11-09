-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:51:30.967973+00:00
-- url     : https://prove2.me/submissions/f123e180-7931-4942-a280-7537cff3b1f4

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E110
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1374 raw1374Labels = mixedMoment B node4549 node4549Labels := by
  calc
    mixedMoment B raw1374 raw1374Labels = mixedMoment B raw1374step0 raw1374step0Labels := by
      have ha : raw1374step0 = (fun i j => raw1374 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1374step0 raw1374; decide +kernel
      have hl : raw1374step0Labels = raw1374Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1374 raw1374Labels permutation32 permutation4
    mixedMoment B raw1374step0 raw1374step0Labels = mixedMoment B raw1374step1 raw1374step1Labels := by
      have ha : raw1374step1 = raw1374step0 := by apply Matrix.ext; unfold raw1374step1 raw1374step0; decide +kernel
      have hl : raw1374step0Labels = labelEmbedding7 ∘ raw1374step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1374step0 raw1374step0Labels raw1374step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4549 node4549Labels := by rfl

theorem canonical1375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1375 raw1375Labels = mixedMoment B node1134 node1134Labels := by
  calc
    mixedMoment B raw1375 raw1375Labels = mixedMoment B raw1375step0 raw1375step0Labels := by
      have ha : raw1375step0 = (fun i j => raw1375 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1375step0 raw1375; decide +kernel
      have hl : raw1375step0Labels = raw1375Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1375 raw1375Labels permutation32 permutation4
    _ = mixedMoment B node1134 node1134Labels := by rfl

theorem canonical1376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1376 raw1376Labels = mixedMoment B node3265 node3265Labels := by
  calc
    mixedMoment B raw1376 raw1376Labels = mixedMoment B raw1376step0 raw1376step0Labels := by
      have ha : raw1376step0 = (fun i j => raw1376 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1376step0 raw1376; decide +kernel
      have hl : raw1376step0Labels = raw1376Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1376 raw1376Labels permutation32 permutation6
    mixedMoment B raw1376step0 raw1376step0Labels = mixedMoment B raw1376step1 raw1376step1Labels := by
      have ha : raw1376step1 = -raw1376step0 := by apply Matrix.ext; change ∀ i j, raw1376step1 i j = -(raw1376step0 i j); unfold raw1376step1 raw1376step0; decide +kernel
      have hl : raw1376step1Labels = raw1376step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1376step1 raw1376step1Labels = mixedMoment B raw1376step2 raw1376step2Labels := by
      have ha : raw1376step2 = raw1376step1 := by apply Matrix.ext; unfold raw1376step2 raw1376step1; decide +kernel
      have hl : raw1376step1Labels = labelEmbedding1 ∘ raw1376step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1376step1 raw1376step1Labels raw1376step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3265 node3265Labels := by rfl

theorem canonical1395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1395 raw1395Labels = mixedMoment B node4558 node4558Labels := by
  calc
    mixedMoment B raw1395 raw1395Labels = mixedMoment B raw1395step0 raw1395step0Labels := by
      have ha : raw1395step0 = (fun i j => raw1395 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1395step0 raw1395; decide +kernel
      have hl : raw1395step0Labels = raw1395Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1395 raw1395Labels permutation8 permutation4
    mixedMoment B raw1395step0 raw1395step0Labels = mixedMoment B raw1395step1 raw1395step1Labels := by
      have ha : raw1395step1 = raw1395step0 := by apply Matrix.ext; unfold raw1395step1 raw1395step0; decide +kernel
      have hl : raw1395step0Labels = labelEmbedding7 ∘ raw1395step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1395step0 raw1395step0Labels raw1395step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4558 node4558Labels := by rfl

theorem canonical1396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1396 raw1396Labels = mixedMoment B node1144 node1144Labels := by
  calc
    mixedMoment B raw1396 raw1396Labels = mixedMoment B raw1396step0 raw1396step0Labels := by
      have ha : raw1396step0 = (fun i j => raw1396 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1396step0 raw1396; decide +kernel
      have hl : raw1396step0Labels = raw1396Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1396 raw1396Labels permutation8 permutation4
    _ = mixedMoment B node1144 node1144Labels := by rfl

theorem canonical1397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1397 raw1397Labels = mixedMoment B node3276 node3276Labels := by
  calc
    mixedMoment B raw1397 raw1397Labels = mixedMoment B raw1397step0 raw1397step0Labels := by
      have ha : raw1397step0 = (fun i j => raw1397 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1397step0 raw1397; decide +kernel
      have hl : raw1397step0Labels = raw1397Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1397 raw1397Labels permutation8 permutation6
    mixedMoment B raw1397step0 raw1397step0Labels = mixedMoment B raw1397step1 raw1397step1Labels := by
      have ha : raw1397step1 = -raw1397step0 := by apply Matrix.ext; change ∀ i j, raw1397step1 i j = -(raw1397step0 i j); unfold raw1397step1 raw1397step0; decide +kernel
      have hl : raw1397step1Labels = raw1397step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1397step1 raw1397step1Labels = mixedMoment B raw1397step2 raw1397step2Labels := by
      have ha : raw1397step2 = raw1397step1 := by apply Matrix.ext; unfold raw1397step2 raw1397step1; decide +kernel
      have hl : raw1397step1Labels = labelEmbedding1 ∘ raw1397step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1397step1 raw1397step1Labels raw1397step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3276 node3276Labels := by rfl

theorem canonical1398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1398 raw1398Labels = mixedMoment B node4559 node4559Labels := by
  calc
    mixedMoment B raw1398 raw1398Labels = mixedMoment B raw1398step0 raw1398step0Labels := by
      have ha : raw1398step0 = (fun i j => raw1398 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1398step0 raw1398; decide +kernel
      have hl : raw1398step0Labels = raw1398Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1398 raw1398Labels permutation8 permutation4
    mixedMoment B raw1398step0 raw1398step0Labels = mixedMoment B raw1398step1 raw1398step1Labels := by
      have ha : raw1398step1 = raw1398step0 := by apply Matrix.ext; unfold raw1398step1 raw1398step0; decide +kernel
      have hl : raw1398step0Labels = labelEmbedding7 ∘ raw1398step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1398step0 raw1398step0Labels raw1398step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4559 node4559Labels := by rfl

theorem canonical1399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1399 raw1399Labels = mixedMoment B node1145 node1145Labels := by
  calc
    mixedMoment B raw1399 raw1399Labels = mixedMoment B raw1399step0 raw1399step0Labels := by
      have ha : raw1399step0 = (fun i j => raw1399 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1399step0 raw1399; decide +kernel
      have hl : raw1399step0Labels = raw1399Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1399 raw1399Labels permutation8 permutation4
    _ = mixedMoment B node1145 node1145Labels := by rfl

theorem canonical1400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1400 raw1400Labels = mixedMoment B node3277 node3277Labels := by
  calc
    mixedMoment B raw1400 raw1400Labels = mixedMoment B raw1400step0 raw1400step0Labels := by
      have ha : raw1400step0 = (fun i j => raw1400 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1400step0 raw1400; decide +kernel
      have hl : raw1400step0Labels = raw1400Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1400 raw1400Labels permutation9 permutation6
    mixedMoment B raw1400step0 raw1400step0Labels = mixedMoment B raw1400step1 raw1400step1Labels := by
      have ha : raw1400step1 = -raw1400step0 := by apply Matrix.ext; change ∀ i j, raw1400step1 i j = -(raw1400step0 i j); unfold raw1400step1 raw1400step0; decide +kernel
      have hl : raw1400step1Labels = raw1400step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1400step1 raw1400step1Labels = mixedMoment B raw1400step2 raw1400step2Labels := by
      have ha : raw1400step2 = raw1400step1 := by apply Matrix.ext; unfold raw1400step2 raw1400step1; decide +kernel
      have hl : raw1400step1Labels = labelEmbedding1 ∘ raw1400step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1400step1 raw1400step1Labels raw1400step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3277 node3277Labels := by rfl

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

theorem canonical1908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1908 raw1908Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw1908 raw1908Labels = mixedMoment B raw1908step0 raw1908step0Labels := by
      have ha : raw1908step0 = (fun i j => raw1908 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1908step0 raw1908; decide +kernel
      have hl : raw1908step0Labels = raw1908Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1908 raw1908Labels permutation32 permutation4
    mixedMoment B raw1908step0 raw1908step0Labels = mixedMoment B raw1908step1 raw1908step1Labels := by
      have ha : raw1908step1 = raw1908step0 := by apply Matrix.ext; unfold raw1908step1 raw1908step0; decide +kernel
      have hl : raw1908step0Labels = labelEmbedding7 ∘ raw1908step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1908step0 raw1908step0Labels raw1908step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4943 node4943Labels := by rfl

theorem canonical1909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1909 raw1909Labels = mixedMoment B node2334 node2334Labels := by
  calc
    mixedMoment B raw1909 raw1909Labels = mixedMoment B raw1909step0 raw1909step0Labels := by
      have ha : raw1909step0 = (fun i j => raw1909 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1909step0 raw1909; decide +kernel
      have hl : raw1909step0Labels = raw1909Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1909 raw1909Labels permutation32 permutation4
    _ = mixedMoment B node2334 node2334Labels := by rfl

theorem canonical1910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1910 raw1910Labels = mixedMoment B node3411 node3411Labels := by
  calc
    mixedMoment B raw1910 raw1910Labels = mixedMoment B raw1910step0 raw1910step0Labels := by
      have ha : raw1910step0 = (fun i j => raw1910 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1910step0 raw1910; decide +kernel
      have hl : raw1910step0Labels = raw1910Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1910 raw1910Labels permutation32 permutation6
    mixedMoment B raw1910step0 raw1910step0Labels = mixedMoment B raw1910step1 raw1910step1Labels := by
      have ha : raw1910step1 = -raw1910step0 := by apply Matrix.ext; change ∀ i j, raw1910step1 i j = -(raw1910step0 i j); unfold raw1910step1 raw1910step0; decide +kernel
      have hl : raw1910step1Labels = raw1910step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1910step1 raw1910step1Labels = mixedMoment B raw1910step2 raw1910step2Labels := by
      have ha : raw1910step2 = raw1910step1 := by apply Matrix.ext; unfold raw1910step2 raw1910step1; decide +kernel
      have hl : raw1910step1Labels = labelEmbedding1 ∘ raw1910step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1910step1 raw1910step1Labels raw1910step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3411 node3411Labels := by rfl

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

theorem canonical1956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1956 raw1956Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw1956 raw1956Labels = mixedMoment B raw1956step0 raw1956step0Labels := by
      have ha : raw1956step0 = (fun i j => raw1956 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1956step0 raw1956; decide +kernel
      have hl : raw1956step0Labels = raw1956Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1956 raw1956Labels permutation32 permutation5
    mixedMoment B raw1956step0 raw1956step0Labels = mixedMoment B raw1956step1 raw1956step1Labels := by
      have ha : raw1956step1 = raw1956step0 := by apply Matrix.ext; unfold raw1956step1 raw1956step0; decide +kernel
      have hl : raw1956step0Labels = labelEmbedding8 ∘ raw1956step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1956step0 raw1956step0Labels raw1956step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4972 node4972Labels := by rfl

theorem canonical1957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1957 raw1957Labels = mixedMoment B node2434 node2434Labels := by
  calc
    mixedMoment B raw1957 raw1957Labels = mixedMoment B raw1957step0 raw1957step0Labels := by
      have ha : raw1957step0 = (fun i j => raw1957 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1957step0 raw1957; decide +kernel
      have hl : raw1957step0Labels = raw1957Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1957 raw1957Labels permutation145 permutation4
    mixedMoment B raw1957step0 raw1957step0Labels = mixedMoment B raw1957step1 raw1957step1Labels := by
      have ha : raw1957step1 = -raw1957step0 := by apply Matrix.ext; change ∀ i j, raw1957step1 i j = -(raw1957step0 i j); unfold raw1957step1 raw1957step0; decide +kernel
      have hl : raw1957step1Labels = raw1957step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2434 node2434Labels := by rfl

theorem canonical1958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1958 raw1958Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw1958 raw1958Labels = mixedMoment B raw1958step0 raw1958step0Labels := by
      have ha : raw1958step0 = (fun i j => raw1958 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1958step0 raw1958; decide +kernel
      have hl : raw1958step0Labels = raw1958Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1958 raw1958Labels permutation144 permutation6
    mixedMoment B raw1958step0 raw1958step0Labels = mixedMoment B raw1958step1 raw1958step1Labels := by
      have ha : raw1958step1 = raw1958step0 := by apply Matrix.ext; unfold raw1958step1 raw1958step0; decide +kernel
      have hl : raw1958step0Labels = labelEmbedding1 ∘ raw1958step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1958step0 raw1958step0Labels raw1958step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3457 node3457Labels := by rfl

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

theorem canonical2055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2055 raw2055Labels = mixedMoment B node5036 node5036Labels := by
  calc
    mixedMoment B raw2055 raw2055Labels = mixedMoment B raw2055step0 raw2055step0Labels := by
      have ha : raw2055step0 = (fun i j => raw2055 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2055step0 raw2055; decide +kernel
      have hl : raw2055step0Labels = raw2055Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2055 raw2055Labels permutation152 permutation4
    mixedMoment B raw2055step0 raw2055step0Labels = mixedMoment B raw2055step1 raw2055step1Labels := by
      have ha : raw2055step1 = raw2055step0 := by apply Matrix.ext; unfold raw2055step1 raw2055step0; decide +kernel
      have hl : raw2055step0Labels = labelEmbedding7 ∘ raw2055step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2055step0 raw2055step0Labels raw2055step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5036 node5036Labels := by rfl

theorem canonical2056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2056 raw2056Labels = mixedMoment B node2428 node2428Labels := by
  calc
    mixedMoment B raw2056 raw2056Labels = mixedMoment B raw2056step0 raw2056step0Labels := by
      have ha : raw2056step0 = (fun i j => raw2056 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2056step0 raw2056; decide +kernel
      have hl : raw2056step0Labels = raw2056Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2056 raw2056Labels permutation152 permutation4
    _ = mixedMoment B node2428 node2428Labels := by rfl

theorem canonical2057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2057 raw2057Labels = mixedMoment B node3450 node3450Labels := by
  calc
    mixedMoment B raw2057 raw2057Labels = mixedMoment B raw2057step0 raw2057step0Labels := by
      have ha : raw2057step0 = (fun i j => raw2057 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2057step0 raw2057; decide +kernel
      have hl : raw2057step0Labels = raw2057Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2057 raw2057Labels permutation152 permutation6
    mixedMoment B raw2057step0 raw2057step0Labels = mixedMoment B raw2057step1 raw2057step1Labels := by
      have ha : raw2057step1 = -raw2057step0 := by apply Matrix.ext; change ∀ i j, raw2057step1 i j = -(raw2057step0 i j); unfold raw2057step1 raw2057step0; decide +kernel
      have hl : raw2057step1Labels = raw2057step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2057step1 raw2057step1Labels = mixedMoment B raw2057step2 raw2057step2Labels := by
      have ha : raw2057step2 = raw2057step1 := by apply Matrix.ext; unfold raw2057step2 raw2057step1; decide +kernel
      have hl : raw2057step1Labels = labelEmbedding1 ∘ raw2057step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2057step1 raw2057step1Labels raw2057step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3450 node3450Labels := by rfl

theorem canonical2127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2127 raw2127Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw2127 raw2127Labels = mixedMoment B raw2127step0 raw2127step0Labels := by
      have ha : raw2127step0 = (fun i j => raw2127 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2127step0 raw2127; decide +kernel
      have hl : raw2127step0Labels = raw2127Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2127 raw2127Labels permutation32 permutation4
    mixedMoment B raw2127step0 raw2127step0Labels = mixedMoment B raw2127step1 raw2127step1Labels := by
      have ha : raw2127step1 = raw2127step0 := by apply Matrix.ext; unfold raw2127step1 raw2127step0; decide +kernel
      have hl : raw2127step0Labels = labelEmbedding7 ∘ raw2127step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2127step0 raw2127step0Labels raw2127step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

theorem canonical2128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2128 raw2128Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw2128 raw2128Labels = mixedMoment B raw2128step0 raw2128step0Labels := by
      have ha : raw2128step0 = (fun i j => raw2128 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2128step0 raw2128; decide +kernel
      have hl : raw2128step0Labels = raw2128Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2128 raw2128Labels permutation32 permutation4
    _ = mixedMoment B node2512 node2512Labels := by rfl

theorem canonical2129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2129 raw2129Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw2129 raw2129Labels = mixedMoment B raw2129step0 raw2129step0Labels := by
      have ha : raw2129step0 = (fun i j => raw2129 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2129step0 raw2129; decide +kernel
      have hl : raw2129step0Labels = raw2129Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2129 raw2129Labels permutation33 permutation6
    mixedMoment B raw2129step0 raw2129step0Labels = mixedMoment B raw2129step1 raw2129step1Labels := by
      have ha : raw2129step1 = -raw2129step0 := by apply Matrix.ext; change ∀ i j, raw2129step1 i j = -(raw2129step0 i j); unfold raw2129step1 raw2129step0; decide +kernel
      have hl : raw2129step1Labels = raw2129step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2129step1 raw2129step1Labels = mixedMoment B raw2129step2 raw2129step2Labels := by
      have ha : raw2129step2 = raw2129step1 := by apply Matrix.ext; unfold raw2129step2 raw2129step1; decide +kernel
      have hl : raw2129step1Labels = labelEmbedding1 ∘ raw2129step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2129step1 raw2129step1Labels raw2129step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

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

theorem canonical2169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2169 raw2169Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw2169 raw2169Labels = mixedMoment B raw2169step0 raw2169step0Labels := by
      have ha : raw2169step0 = (fun i j => raw2169 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2169step0 raw2169; decide +kernel
      have hl : raw2169step0Labels = raw2169Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2169 raw2169Labels permutation32 permutation4
    mixedMoment B raw2169step0 raw2169step0Labels = mixedMoment B raw2169step1 raw2169step1Labels := by
      have ha : raw2169step1 = raw2169step0 := by apply Matrix.ext; unfold raw2169step1 raw2169step0; decide +kernel
      have hl : raw2169step0Labels = labelEmbedding7 ∘ raw2169step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2169step0 raw2169step0Labels raw2169step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical2170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2170 raw2170Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw2170 raw2170Labels = mixedMoment B raw2170step0 raw2170step0Labels := by
      have ha : raw2170step0 = (fun i j => raw2170 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2170step0 raw2170; decide +kernel
      have hl : raw2170step0Labels = raw2170Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2170 raw2170Labels permutation32 permutation4
    _ = mixedMoment B node2561 node2561Labels := by rfl

theorem canonical2171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2171 raw2171Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw2171 raw2171Labels = mixedMoment B raw2171step0 raw2171step0Labels := by
      have ha : raw2171step0 = (fun i j => raw2171 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2171step0 raw2171; decide +kernel
      have hl : raw2171step0Labels = raw2171Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2171 raw2171Labels permutation38 permutation6
    mixedMoment B raw2171step0 raw2171step0Labels = mixedMoment B raw2171step1 raw2171step1Labels := by
      have ha : raw2171step1 = -raw2171step0 := by apply Matrix.ext; change ∀ i j, raw2171step1 i j = -(raw2171step0 i j); unfold raw2171step1 raw2171step0; decide +kernel
      have hl : raw2171step1Labels = raw2171step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2171step1 raw2171step1Labels = mixedMoment B raw2171step2 raw2171step2Labels := by
      have ha : raw2171step2 = raw2171step1 := by apply Matrix.ext; unfold raw2171step2 raw2171step1; decide +kernel
      have hl : raw2171step1Labels = labelEmbedding1 ∘ raw2171step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2171step1 raw2171step1Labels raw2171step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

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

theorem canonical2286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2286 raw2286Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw2286 raw2286Labels = mixedMoment B raw2286step0 raw2286step0Labels := by
      have ha : raw2286step0 = (fun i j => raw2286 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2286step0 raw2286; decide +kernel
      have hl : raw2286step0Labels = raw2286Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2286 raw2286Labels permutation8 permutation4
    mixedMoment B raw2286step0 raw2286step0Labels = mixedMoment B raw2286step1 raw2286step1Labels := by
      have ha : raw2286step1 = raw2286step0 := by apply Matrix.ext; unfold raw2286step1 raw2286step0; decide +kernel
      have hl : raw2286step0Labels = labelEmbedding7 ∘ raw2286step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2286step0 raw2286step0Labels raw2286step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

theorem canonical2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2287 raw2287Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw2287 raw2287Labels = mixedMoment B raw2287step0 raw2287step0Labels := by
      have ha : raw2287step0 = (fun i j => raw2287 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2287step0 raw2287; decide +kernel
      have hl : raw2287step0Labels = raw2287Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2287 raw2287Labels permutation8 permutation4
    _ = mixedMoment B node2743 node2743Labels := by rfl

theorem canonical2288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2288 raw2288Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw2288 raw2288Labels = mixedMoment B raw2288step0 raw2288step0Labels := by
      have ha : raw2288step0 = (fun i j => raw2288 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2288step0 raw2288; decide +kernel
      have hl : raw2288step0Labels = raw2288Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2288 raw2288Labels permutation9 permutation6
    mixedMoment B raw2288step0 raw2288step0Labels = mixedMoment B raw2288step1 raw2288step1Labels := by
      have ha : raw2288step1 = -raw2288step0 := by apply Matrix.ext; change ∀ i j, raw2288step1 i j = -(raw2288step0 i j); unfold raw2288step1 raw2288step0; decide +kernel
      have hl : raw2288step1Labels = raw2288step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2288step1 raw2288step1Labels = mixedMoment B raw2288step2 raw2288step2Labels := by
      have ha : raw2288step2 = raw2288step1 := by apply Matrix.ext; unfold raw2288step2 raw2288step1; decide +kernel
      have hl : raw2288step1Labels = labelEmbedding1 ∘ raw2288step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2288step1 raw2288step1Labels raw2288step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical239
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30702 raw30702Labels = mixedMoment B node5371 node5371Labels := by
  calc
    mixedMoment B raw30702 raw30702Labels = mixedMoment B raw30702step0 raw30702step0Labels := by
      have hz : ∀ j, raw30702 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30702step0 = (fun i j => raw30702 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30702step0 raw30702; decide +kernel
      have hl : raw30702step0Labels = raw30702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30702 raw30702Labels permutation434 hz
    mixedMoment B raw30702step0 raw30702step0Labels = mixedMoment B raw30702step1 raw30702step1Labels := by
      have hz : ∀ j, raw30702step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30702step1 = (fun i j => raw30702step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30702step1 raw30702step0; decide +kernel
      have hl : raw30702step1Labels = raw30702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30702step0 raw30702step0Labels permutation80 hz
    mixedMoment B raw30702step1 raw30702step1Labels = mixedMoment B raw30702step2 raw30702step2Labels := by
      have ha : raw30702step2 = (fun i j => raw30702step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30702step2 raw30702step1; decide +kernel
      have hl : raw30702step2Labels = raw30702step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30702step1 raw30702step1Labels permutation9 permutation2
    _ = mixedMoment B node5371 node5371Labels := by rfl

theorem canonical30703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30703 raw30703Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw30703 raw30703Labels = mixedMoment B raw30703step0 raw30703step0Labels := by
      have hz : ∀ j, raw30703 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30703step0 = (fun i j => raw30703 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30703step0 raw30703; decide +kernel
      have hl : raw30703step0Labels = raw30703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30703 raw30703Labels permutation434 hz
    mixedMoment B raw30703step0 raw30703step0Labels = mixedMoment B raw30703step1 raw30703step1Labels := by
      have ha : raw30703step1 = (fun i j => raw30703step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30703step1 raw30703step0; decide +kernel
      have hl : raw30703step1Labels = raw30703step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30703step0 raw30703step0Labels permutation127 permutation2
    mixedMoment B raw30703step1 raw30703step1Labels = mixedMoment B raw30703step2 raw30703step2Labels := by
      have ha : raw30703step2 = -raw30703step1 := by apply Matrix.ext; change ∀ i j, raw30703step2 i j = -(raw30703step1 i j); unfold raw30703step2 raw30703step1; decide +kernel
      have hl : raw30703step2Labels = raw30703step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5367 node5367Labels := by rfl

theorem canonical30704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30704 raw30704Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw30704 raw30704Labels = mixedMoment B raw30704step0 raw30704step0Labels := by
      have hz : ∀ j, raw30704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30704step0 = (fun i j => raw30704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30704step0 raw30704; decide +kernel
      have hl : raw30704step0Labels = raw30704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30704 raw30704Labels permutation346 hz
    mixedMoment B raw30704step0 raw30704step0Labels = mixedMoment B raw30704step1 raw30704step1Labels := by
      have ha : raw30704step1 = (fun i j => raw30704step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30704step1 raw30704step0; decide +kernel
      have hl : raw30704step1Labels = raw30704step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30704step0 raw30704step0Labels permutation127 permutation2
    mixedMoment B raw30704step1 raw30704step1Labels = mixedMoment B raw30704step2 raw30704step2Labels := by
      have ha : raw30704step2 = -raw30704step1 := by apply Matrix.ext; change ∀ i j, raw30704step2 i j = -(raw30704step1 i j); unfold raw30704step2 raw30704step1; decide +kernel
      have hl : raw30704step2Labels = raw30704step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5367 node5367Labels := by rfl

theorem canonical30705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30705 raw30705Labels = mixedMoment B node5413 node5413Labels := by
  calc
    mixedMoment B raw30705 raw30705Labels = mixedMoment B raw30705step0 raw30705step0Labels := by
      have hz : ∀ j, raw30705 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30705step0 = (fun i j => raw30705 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30705step0 raw30705; decide +kernel
      have hl : raw30705step0Labels = raw30705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30705 raw30705Labels permutation434 hz
    mixedMoment B raw30705step0 raw30705step0Labels = mixedMoment B raw30705step1 raw30705step1Labels := by
      have hz : ∀ j, raw30705step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30705step1 = (fun i j => raw30705step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30705step1 raw30705step0; decide +kernel
      have hl : raw30705step1Labels = raw30705step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30705step0 raw30705step0Labels permutation80 hz
    _ = mixedMoment B node5413 node5413Labels := by rfl

theorem canonical30706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30706 raw30706Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw30706 raw30706Labels = mixedMoment B raw30706step0 raw30706step0Labels := by
      have hz : ∀ j, raw30706 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30706step0 = (fun i j => raw30706 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30706step0 raw30706; decide +kernel
      have hl : raw30706step0Labels = raw30706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30706 raw30706Labels permutation434 hz
    mixedMoment B raw30706step0 raw30706step0Labels = mixedMoment B raw30706step1 raw30706step1Labels := by
      have hz : ∀ j, raw30706step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30706step1 = (fun i j => raw30706step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30706step1 raw30706step0; decide +kernel
      have hl : raw30706step1Labels = raw30706step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30706step0 raw30706step0Labels permutation80 hz
    mixedMoment B raw30706step1 raw30706step1Labels = mixedMoment B raw30706step2 raw30706step2Labels := by
      have hz : ∀ i, raw30706step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw30706step2 = (fun i j => raw30706step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw30706step2 raw30706step1; decide +kernel
      have hl : raw30706step2Labels = (fun j => raw30706step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw30706step1 raw30706step1Labels permutation4 hz
    mixedMoment B raw30706step2 raw30706step2Labels = mixedMoment B raw30706step3 raw30706step3Labels := by
      have ha : raw30706step3 = (fun i j => raw30706step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30706step3 raw30706step2; decide +kernel
      have hl : raw30706step3Labels = raw30706step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30706step2 raw30706step2Labels permutation9 permutation0
    mixedMoment B raw30706step3 raw30706step3Labels = mixedMoment B raw30706step4 raw30706step4Labels := by
      have ha : raw30706step4 = raw30706step3 := by apply Matrix.ext; unfold raw30706step4 raw30706step3; decide +kernel
      have hl : raw30706step3Labels = labelEmbedding2 ∘ raw30706step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30706step3 raw30706step3Labels raw30706step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical30707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30707 raw30707Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw30707 raw30707Labels = mixedMoment B raw30707step0 raw30707step0Labels := by
      have hz : ∀ j, raw30707 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30707step0 = (fun i j => raw30707 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30707step0 raw30707; decide +kernel
      have hl : raw30707step0Labels = raw30707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30707 raw30707Labels permutation434 hz
    mixedMoment B raw30707step0 raw30707step0Labels = mixedMoment B raw30707step1 raw30707step1Labels := by
      have hz : ∀ j, raw30707step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30707step1 = (fun i j => raw30707step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30707step1 raw30707step0; decide +kernel
      have hl : raw30707step1Labels = raw30707step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30707step0 raw30707step0Labels permutation80 hz
    mixedMoment B raw30707step1 raw30707step1Labels = mixedMoment B raw30707step2 raw30707step2Labels := by
      have ha : raw30707step2 = (fun i j => raw30707step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30707step2 raw30707step1; decide +kernel
      have hl : raw30707step2Labels = raw30707step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30707step1 raw30707step1Labels permutation9 permutation2
    _ = mixedMoment B node4612 node4612Labels := by rfl

theorem canonical30708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30708 raw30708Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw30708 raw30708Labels = mixedMoment B raw30708step0 raw30708step0Labels := by
      have hz : ∀ j, raw30708 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30708step0 = (fun i j => raw30708 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30708step0 raw30708; decide +kernel
      have hl : raw30708step0Labels = raw30708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30708 raw30708Labels permutation434 hz
    mixedMoment B raw30708step0 raw30708step0Labels = mixedMoment B raw30708step1 raw30708step1Labels := by
      have ha : raw30708step1 = (fun i j => raw30708step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30708step1 raw30708step0; decide +kernel
      have hl : raw30708step1Labels = raw30708step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30708step0 raw30708step0Labels permutation39 permutation2
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical30709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30709 raw30709Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw30709 raw30709Labels = mixedMoment B raw30709step0 raw30709step0Labels := by
      have hz : ∀ j, raw30709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30709step0 = (fun i j => raw30709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30709step0 raw30709; decide +kernel
      have hl : raw30709step0Labels = raw30709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30709 raw30709Labels permutation346 hz
    mixedMoment B raw30709step0 raw30709step0Labels = mixedMoment B raw30709step1 raw30709step1Labels := by
      have ha : raw30709step1 = (fun i j => raw30709step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30709step1 raw30709step0; decide +kernel
      have hl : raw30709step1Labels = raw30709step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30709step0 raw30709step0Labels permutation39 permutation2
    _ = mixedMoment B node5141 node5141Labels := by rfl

theorem canonical30710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30710 raw30710Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw30710 raw30710Labels = mixedMoment B raw30710step0 raw30710step0Labels := by
      have hz : ∀ j, raw30710 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30710step0 = (fun i j => raw30710 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30710step0 raw30710; decide +kernel
      have hl : raw30710step0Labels = raw30710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30710 raw30710Labels permutation434 hz
    mixedMoment B raw30710step0 raw30710step0Labels = mixedMoment B raw30710step1 raw30710step1Labels := by
      have hz : ∀ j, raw30710step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30710step1 = (fun i j => raw30710step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30710step1 raw30710step0; decide +kernel
      have hl : raw30710step1Labels = raw30710step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30710step0 raw30710step0Labels permutation80 hz
    mixedMoment B raw30710step1 raw30710step1Labels = mixedMoment B raw30710step2 raw30710step2Labels := by
      have ha : raw30710step2 = (fun i j => raw30710step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30710step2 raw30710step1; decide +kernel
      have hl : raw30710step2Labels = raw30710step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30710step1 raw30710step1Labels permutation9 permutation2
    _ = mixedMoment B node5274 node5274Labels := by rfl

theorem canonical30711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30711 raw30711Labels = mixedMoment B node4549 node4549Labels := by
  calc
    mixedMoment B raw30711 raw30711Labels = mixedMoment B raw30711step0 raw30711step0Labels := by
      have hz : ∀ j, raw30711 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30711step0 = (fun i j => raw30711 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30711step0 raw30711; decide +kernel
      have hl : raw30711step0Labels = raw30711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30711 raw30711Labels permutation434 hz
    mixedMoment B raw30711step0 raw30711step0Labels = mixedMoment B raw30711step1 raw30711step1Labels := by
      have ha : raw30711step1 = (fun i j => raw30711step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30711step1 raw30711step0; decide +kernel
      have hl : raw30711step1Labels = raw30711step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30711step0 raw30711step0Labels permutation33 permutation2
    _ = mixedMoment B node4549 node4549Labels := by rfl

theorem canonical30712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30712 raw30712Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw30712 raw30712Labels = mixedMoment B raw30712step0 raw30712step0Labels := by
      have hz : ∀ j, raw30712 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30712step0 = (fun i j => raw30712 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30712step0 raw30712; decide +kernel
      have hl : raw30712step0Labels = raw30712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30712 raw30712Labels permutation434 hz
    mixedMoment B raw30712step0 raw30712step0Labels = mixedMoment B raw30712step1 raw30712step1Labels := by
      have ha : raw30712step1 = (fun i j => raw30712step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30712step1 raw30712step0; decide +kernel
      have hl : raw30712step1Labels = raw30712step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30712step0 raw30712step0Labels permutation33 permutation2
    _ = mixedMoment B node4946 node4946Labels := by rfl

theorem canonical30713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30713 raw30713Labels = mixedMoment B node5036 node5036Labels := by
  calc
    mixedMoment B raw30713 raw30713Labels = mixedMoment B raw30713step0 raw30713step0Labels := by
      have ha : raw30713step0 = (fun i j => raw30713 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30713step0 raw30713; decide +kernel
      have hl : raw30713step0Labels = raw30713Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30713 raw30713Labels permutation159 permutation2
    _ = mixedMoment B node5036 node5036Labels := by rfl

theorem canonical30714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30714 raw30714Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw30714 raw30714Labels = mixedMoment B raw30714step0 raw30714step0Labels := by
      have hz : ∀ j, raw30714 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30714step0 = (fun i j => raw30714 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30714step0 raw30714; decide +kernel
      have hl : raw30714step0Labels = raw30714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30714 raw30714Labels permutation434 hz
    _ = mixedMoment B node5102 node5102Labels := by rfl

theorem canonical30715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30715 raw30715Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw30715 raw30715Labels = mixedMoment B raw30715step0 raw30715step0Labels := by
      have hz : ∀ j, raw30715 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30715step0 = (fun i j => raw30715 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30715step0 raw30715; decide +kernel
      have hl : raw30715step0Labels = raw30715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30715 raw30715Labels permutation434 hz
    mixedMoment B raw30715step0 raw30715step0Labels = mixedMoment B raw30715step1 raw30715step1Labels := by
      have ha : raw30715step1 = (fun i j => raw30715step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30715step1 raw30715step0; decide +kernel
      have hl : raw30715step1Labels = raw30715step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30715step0 raw30715step0Labels permutation33 permutation2
    _ = mixedMoment B node5101 node5101Labels := by rfl

theorem canonical30716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30716 raw30716Labels = mixedMoment B node4549 node4549Labels := by
  calc
    mixedMoment B raw30716 raw30716Labels = mixedMoment B raw30716step0 raw30716step0Labels := by
      have hz : ∀ j, raw30716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30716step0 = (fun i j => raw30716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30716step0 raw30716; decide +kernel
      have hl : raw30716step0Labels = raw30716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30716 raw30716Labels permutation346 hz
    mixedMoment B raw30716step0 raw30716step0Labels = mixedMoment B raw30716step1 raw30716step1Labels := by
      have ha : raw30716step1 = (fun i j => raw30716step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30716step1 raw30716step0; decide +kernel
      have hl : raw30716step1Labels = raw30716step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30716step0 raw30716step0Labels permutation33 permutation2
    _ = mixedMoment B node4549 node4549Labels := by rfl

theorem canonical30717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30717 raw30717Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw30717 raw30717Labels = mixedMoment B raw30717step0 raw30717step0Labels := by
      have hz : ∀ j, raw30717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30717step0 = (fun i j => raw30717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30717step0 raw30717; decide +kernel
      have hl : raw30717step0Labels = raw30717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30717 raw30717Labels permutation346 hz
    mixedMoment B raw30717step0 raw30717step0Labels = mixedMoment B raw30717step1 raw30717step1Labels := by
      have ha : raw30717step1 = (fun i j => raw30717step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30717step1 raw30717step0; decide +kernel
      have hl : raw30717step1Labels = raw30717step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30717step0 raw30717step0Labels permutation33 permutation2
    _ = mixedMoment B node4946 node4946Labels := by rfl

theorem canonical30718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30718 raw30718Labels = mixedMoment B node5036 node5036Labels := by
  calc
    mixedMoment B raw30718 raw30718Labels = mixedMoment B raw30718step0 raw30718step0Labels := by
      have ha : raw30718step0 = (fun i j => raw30718 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30718step0 raw30718; decide +kernel
      have hl : raw30718step0Labels = raw30718Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30718 raw30718Labels permutation153 permutation2
    _ = mixedMoment B node5036 node5036Labels := by rfl

theorem canonical30719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30719 raw30719Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw30719 raw30719Labels = mixedMoment B raw30719step0 raw30719step0Labels := by
      have hz : ∀ j, raw30719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30719step0 = (fun i j => raw30719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30719step0 raw30719; decide +kernel
      have hl : raw30719step0Labels = raw30719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30719 raw30719Labels permutation346 hz
    _ = mixedMoment B node5102 node5102Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30720 raw30720Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw30720 raw30720Labels = mixedMoment B raw30720step0 raw30720step0Labels := by
      have hz : ∀ j, raw30720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30720step0 = (fun i j => raw30720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30720step0 raw30720; decide +kernel
      have hl : raw30720step0Labels = raw30720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30720 raw30720Labels permutation346 hz
    mixedMoment B raw30720step0 raw30720step0Labels = mixedMoment B raw30720step1 raw30720step1Labels := by
      have ha : raw30720step1 = (fun i j => raw30720step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30720step1 raw30720step0; decide +kernel
      have hl : raw30720step1Labels = raw30720step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30720step0 raw30720step0Labels permutation33 permutation2
    _ = mixedMoment B node5101 node5101Labels := by rfl

theorem canonical30721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30721 raw30721Labels = mixedMoment B node4558 node4558Labels := by
  calc
    mixedMoment B raw30721 raw30721Labels = mixedMoment B raw30721step0 raw30721step0Labels := by
      have hz : ∀ j, raw30721 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30721step0 = (fun i j => raw30721 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30721step0 raw30721; decide +kernel
      have hl : raw30721step0Labels = raw30721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30721 raw30721Labels permutation434 hz
    mixedMoment B raw30721step0 raw30721step0Labels = mixedMoment B raw30721step1 raw30721step1Labels := by
      have hz : ∀ j, raw30721step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30721step1 = (fun i j => raw30721step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30721step1 raw30721step0; decide +kernel
      have hl : raw30721step1Labels = raw30721step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30721step0 raw30721step0Labels permutation80 hz
    mixedMoment B raw30721step1 raw30721step1Labels = mixedMoment B raw30721step2 raw30721step2Labels := by
      have ha : raw30721step2 = (fun i j => raw30721step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30721step2 raw30721step1; decide +kernel
      have hl : raw30721step2Labels = raw30721step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30721step1 raw30721step1Labels permutation9 permutation2
    _ = mixedMoment B node4558 node4558Labels := by rfl

theorem canonical30722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30722 raw30722Labels = mixedMoment B node4952 node4952Labels := by
  calc
    mixedMoment B raw30722 raw30722Labels = mixedMoment B raw30722step0 raw30722step0Labels := by
      have hz : ∀ j, raw30722 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30722step0 = (fun i j => raw30722 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30722step0 raw30722; decide +kernel
      have hl : raw30722step0Labels = raw30722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30722 raw30722Labels permutation434 hz
    mixedMoment B raw30722step0 raw30722step0Labels = mixedMoment B raw30722step1 raw30722step1Labels := by
      have hz : ∀ j, raw30722step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30722step1 = (fun i j => raw30722step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30722step1 raw30722step0; decide +kernel
      have hl : raw30722step1Labels = raw30722step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30722step0 raw30722step0Labels permutation80 hz
    mixedMoment B raw30722step1 raw30722step1Labels = mixedMoment B raw30722step2 raw30722step2Labels := by
      have ha : raw30722step2 = (fun i j => raw30722step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30722step2 raw30722step1; decide +kernel
      have hl : raw30722step2Labels = raw30722step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30722step1 raw30722step1Labels permutation9 permutation2
    _ = mixedMoment B node4952 node4952Labels := by rfl

theorem canonical30723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30723 raw30723Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw30723 raw30723Labels = mixedMoment B raw30723step0 raw30723step0Labels := by
      have hz : ∀ j, raw30723 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30723step0 = (fun i j => raw30723 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30723step0 raw30723; decide +kernel
      have hl : raw30723step0Labels = raw30723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30723 raw30723Labels permutation434 hz
    mixedMoment B raw30723step0 raw30723step0Labels = mixedMoment B raw30723step1 raw30723step1Labels := by
      have ha : raw30723step1 = (fun i j => raw30723step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30723step1 raw30723step0; decide +kernel
      have hl : raw30723step1Labels = raw30723step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30723step0 raw30723step0Labels permutation127 permutation2
    mixedMoment B raw30723step1 raw30723step1Labels = mixedMoment B raw30723step2 raw30723step2Labels := by
      have ha : raw30723step2 = -raw30723step1 := by apply Matrix.ext; change ∀ i j, raw30723step2 i j = -(raw30723step1 i j); unfold raw30723step2 raw30723step1; decide +kernel
      have hl : raw30723step2Labels = raw30723step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4943 node4943Labels := by rfl

theorem canonical30724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30724 raw30724Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw30724 raw30724Labels = mixedMoment B raw30724step0 raw30724step0Labels := by
      have hz : ∀ j, raw30724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30724step0 = (fun i j => raw30724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30724step0 raw30724; decide +kernel
      have hl : raw30724step0Labels = raw30724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30724 raw30724Labels permutation346 hz
    mixedMoment B raw30724step0 raw30724step0Labels = mixedMoment B raw30724step1 raw30724step1Labels := by
      have ha : raw30724step1 = (fun i j => raw30724step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30724step1 raw30724step0; decide +kernel
      have hl : raw30724step1Labels = raw30724step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30724step0 raw30724step0Labels permutation127 permutation2
    mixedMoment B raw30724step1 raw30724step1Labels = mixedMoment B raw30724step2 raw30724step2Labels := by
      have ha : raw30724step2 = -raw30724step1 := by apply Matrix.ext; change ∀ i j, raw30724step2 i j = -(raw30724step1 i j); unfold raw30724step2 raw30724step1; decide +kernel
      have hl : raw30724step2Labels = raw30724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4943 node4943Labels := by rfl

theorem canonical30725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30725 raw30725Labels = mixedMoment B node5107 node5107Labels := by
  calc
    mixedMoment B raw30725 raw30725Labels = mixedMoment B raw30725step0 raw30725step0Labels := by
      have hz : ∀ j, raw30725 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30725step0 = (fun i j => raw30725 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30725step0 raw30725; decide +kernel
      have hl : raw30725step0Labels = raw30725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30725 raw30725Labels permutation434 hz
    mixedMoment B raw30725step0 raw30725step0Labels = mixedMoment B raw30725step1 raw30725step1Labels := by
      have hz : ∀ j, raw30725step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30725step1 = (fun i j => raw30725step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30725step1 raw30725step0; decide +kernel
      have hl : raw30725step1Labels = raw30725step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30725step0 raw30725step0Labels permutation80 hz
    mixedMoment B raw30725step1 raw30725step1Labels = mixedMoment B raw30725step2 raw30725step2Labels := by
      have ha : raw30725step2 = (fun i j => raw30725step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30725step2 raw30725step1; decide +kernel
      have hl : raw30725step2Labels = raw30725step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30725step1 raw30725step1Labels permutation9 permutation2
    _ = mixedMoment B node5107 node5107Labels := by rfl

theorem canonical30726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30726 raw30726Labels = mixedMoment B node4559 node4559Labels := by
  calc
    mixedMoment B raw30726 raw30726Labels = mixedMoment B raw30726step0 raw30726step0Labels := by
      have hz : ∀ j, raw30726 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30726step0 = (fun i j => raw30726 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30726step0 raw30726; decide +kernel
      have hl : raw30726step0Labels = raw30726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30726 raw30726Labels permutation434 hz
    mixedMoment B raw30726step0 raw30726step0Labels = mixedMoment B raw30726step1 raw30726step1Labels := by
      have hz : ∀ j, raw30726step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30726step1 = (fun i j => raw30726step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30726step1 raw30726step0; decide +kernel
      have hl : raw30726step1Labels = raw30726step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30726step0 raw30726step0Labels permutation80 hz
    _ = mixedMoment B node4559 node4559Labels := by rfl

theorem canonical30727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30727 raw30727Labels = mixedMoment B node4953 node4953Labels := by
  calc
    mixedMoment B raw30727 raw30727Labels = mixedMoment B raw30727step0 raw30727step0Labels := by
      have hz : ∀ j, raw30727 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30727step0 = (fun i j => raw30727 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30727step0 raw30727; decide +kernel
      have hl : raw30727step0Labels = raw30727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30727 raw30727Labels permutation434 hz
    mixedMoment B raw30727step0 raw30727step0Labels = mixedMoment B raw30727step1 raw30727step1Labels := by
      have hz : ∀ j, raw30727step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30727step1 = (fun i j => raw30727step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30727step1 raw30727step0; decide +kernel
      have hl : raw30727step1Labels = raw30727step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30727step0 raw30727step0Labels permutation80 hz
    _ = mixedMoment B node4953 node4953Labels := by rfl

theorem canonical30728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30728 raw30728Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw30728 raw30728Labels = mixedMoment B raw30728step0 raw30728step0Labels := by
      have hz : ∀ j, raw30728 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30728step0 = (fun i j => raw30728 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30728step0 raw30728; decide +kernel
      have hl : raw30728step0Labels = raw30728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30728 raw30728Labels permutation434 hz
    mixedMoment B raw30728step0 raw30728step0Labels = mixedMoment B raw30728step1 raw30728step1Labels := by
      have ha : raw30728step1 = (fun i j => raw30728step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30728step1 raw30728step0; decide +kernel
      have hl : raw30728step1Labels = raw30728step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30728step0 raw30728step0Labels permutation149 permutation3
    mixedMoment B raw30728step1 raw30728step1Labels = mixedMoment B raw30728step2 raw30728step2Labels := by
      have ha : raw30728step2 = -raw30728step1 := by apply Matrix.ext; change ∀ i j, raw30728step2 i j = -(raw30728step1 i j); unfold raw30728step2 raw30728step1; decide +kernel
      have hl : raw30728step2Labels = raw30728step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30728step2 raw30728step2Labels = mixedMoment B raw30728step3 raw30728step3Labels := by
      have ha : raw30728step3 = raw30728step2 := by apply Matrix.ext; unfold raw30728step3 raw30728step2; decide +kernel
      have hl : raw30728step2Labels = labelEmbedding6 ∘ raw30728step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30728step2 raw30728step2Labels raw30728step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4972 node4972Labels := by rfl

theorem canonical30729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30729 raw30729Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw30729 raw30729Labels = mixedMoment B raw30729step0 raw30729step0Labels := by
      have hz : ∀ j, raw30729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30729step0 = (fun i j => raw30729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30729step0 raw30729; decide +kernel
      have hl : raw30729step0Labels = raw30729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30729 raw30729Labels permutation346 hz
    mixedMoment B raw30729step0 raw30729step0Labels = mixedMoment B raw30729step1 raw30729step1Labels := by
      have ha : raw30729step1 = (fun i j => raw30729step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30729step1 raw30729step0; decide +kernel
      have hl : raw30729step1Labels = raw30729step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30729step0 raw30729step0Labels permutation149 permutation3
    mixedMoment B raw30729step1 raw30729step1Labels = mixedMoment B raw30729step2 raw30729step2Labels := by
      have ha : raw30729step2 = -raw30729step1 := by apply Matrix.ext; change ∀ i j, raw30729step2 i j = -(raw30729step1 i j); unfold raw30729step2 raw30729step1; decide +kernel
      have hl : raw30729step2Labels = raw30729step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30729step2 raw30729step2Labels = mixedMoment B raw30729step3 raw30729step3Labels := by
      have ha : raw30729step3 = raw30729step2 := by apply Matrix.ext; unfold raw30729step3 raw30729step2; decide +kernel
      have hl : raw30729step2Labels = labelEmbedding6 ∘ raw30729step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30729step2 raw30729step2Labels raw30729step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4972 node4972Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3933 raw3933Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw3933 raw3933Labels = mixedMoment B raw3933step0 raw3933step0Labels := by
      have hz : ∀ j, raw3933 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3933step0 = (fun i j => raw3933 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3933step0 raw3933; decide +kernel
      have hl : raw3933step0Labels = raw3933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3933 raw3933Labels permutation434 hz
    mixedMoment B raw3933step0 raw3933step0Labels = mixedMoment B raw3933step1 raw3933step1Labels := by
      have hz : ∀ j, raw3933step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3933step1 = (fun i j => raw3933step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3933step1 raw3933step0; decide +kernel
      have hl : raw3933step1Labels = raw3933step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3933step0 raw3933step0Labels permutation80 hz
    _ = mixedMoment B node5109 node5109Labels := by rfl

theorem canonical3936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3936 raw3936Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw3936 raw3936Labels = mixedMoment B raw3936step0 raw3936step0Labels := by
      have hz : ∀ j, raw3936 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3936step0 = (fun i j => raw3936 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3936step0 raw3936; decide +kernel
      have hl : raw3936step0Labels = raw3936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3936 raw3936Labels permutation434 hz
    mixedMoment B raw3936step0 raw3936step0Labels = mixedMoment B raw3936step1 raw3936step1Labels := by
      have hz : ∀ j, raw3936step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3936step1 = (fun i j => raw3936step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3936step1 raw3936step0; decide +kernel
      have hl : raw3936step1Labels = raw3936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3936step0 raw3936step0Labels permutation80 hz
    _ = mixedMoment B node5275 node5275Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4549 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4549 node4549Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1134 node1134Labels + mixedMoment B node3265 node3265Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1374 singletonSmall4549
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4549) = raw1374Labels := by decide +kernel
  rw [hl, canonical1374 B hB] at h
  have hc0 : mixedMoment B raw1374 (Fin.cases (0 : Fin 2) singletonSmall4549) =
      mixedMoment B node1134 node1134Labels := by
    have ha : raw1374 = raw1375 := by apply Matrix.ext; unfold raw1374 raw1375; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4549 = raw1375Labels := by decide +kernel
    rw [ha, hj, canonical1375 B hB]
  have hc1 : mixedMoment B raw1374 (Fin.cases (1 : Fin 2) singletonSmall4549) =
      mixedMoment B node3265 node3265Labels := by
    have ha : raw1374 = raw1376 := by apply Matrix.ext; unfold raw1374 raw1376; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4549 = raw1376Labels := by decide +kernel
    rw [ha, hj, canonical1376 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4558 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4558 node4558Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1144 node1144Labels + mixedMoment B node3276 node3276Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1395 singletonSmall4558
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4558) = raw1395Labels := by decide +kernel
  rw [hl, canonical1395 B hB] at h
  have hc0 : mixedMoment B raw1395 (Fin.cases (0 : Fin 2) singletonSmall4558) =
      mixedMoment B node1144 node1144Labels := by
    have ha : raw1395 = raw1396 := by apply Matrix.ext; unfold raw1395 raw1396; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4558 = raw1396Labels := by decide +kernel
    rw [ha, hj, canonical1396 B hB]
  have hc1 : mixedMoment B raw1395 (Fin.cases (1 : Fin 2) singletonSmall4558) =
      mixedMoment B node3276 node3276Labels := by
    have ha : raw1395 = raw1397 := by apply Matrix.ext; unfold raw1395 raw1397; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4558 = raw1397Labels := by decide +kernel
    rw [ha, hj, canonical1397 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4559 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4559 node4559Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1145 node1145Labels + mixedMoment B node3277 node3277Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1398 singletonSmall4559
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4559) = raw1398Labels := by decide +kernel
  rw [hl, canonical1398 B hB] at h
  have hc0 : mixedMoment B raw1398 (Fin.cases (0 : Fin 2) singletonSmall4559) =
      mixedMoment B node1145 node1145Labels := by
    have ha : raw1398 = raw1399 := by apply Matrix.ext; unfold raw1398 raw1399; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4559 = raw1399Labels := by decide +kernel
    rw [ha, hj, canonical1399 B hB]
  have hc1 : mixedMoment B raw1398 (Fin.cases (1 : Fin 2) singletonSmall4559) =
      mixedMoment B node3277 node3277Labels := by
    have ha : raw1398 = raw1400 := by apply Matrix.ext; unfold raw1398 raw1400; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4559 = raw1400Labels := by decide +kernel
    rw [ha, hj, canonical1400 B hB]
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

theorem singleton4943 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4943 node4943Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2334 node2334Labels + mixedMoment B node3411 node3411Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1908 singletonSmall4943
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4943) = raw1908Labels := by decide +kernel
  rw [hl, canonical1908 B hB] at h
  have hc0 : mixedMoment B raw1908 (Fin.cases (0 : Fin 2) singletonSmall4943) =
      mixedMoment B node2334 node2334Labels := by
    have ha : raw1908 = raw1909 := by apply Matrix.ext; unfold raw1908 raw1909; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4943 = raw1909Labels := by decide +kernel
    rw [ha, hj, canonical1909 B hB]
  have hc1 : mixedMoment B raw1908 (Fin.cases (1 : Fin 2) singletonSmall4943) =
      mixedMoment B node3411 node3411Labels := by
    have ha : raw1908 = raw1910 := by apply Matrix.ext; unfold raw1908 raw1910; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4943 = raw1910Labels := by decide +kernel
    rw [ha, hj, canonical1910 B hB]
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

theorem singleton4972 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4972 node4972Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2434 node2434Labels + mixedMoment B node3457 node3457Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1956 singletonSmall4972
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4972) = raw1956Labels := by decide +kernel
  rw [hl, canonical1956 B hB] at h
  have hc0 : mixedMoment B raw1956 (Fin.cases (0 : Fin 2) singletonSmall4972) =
      mixedMoment B node2434 node2434Labels := by
    have ha : raw1956 = raw1957 := by apply Matrix.ext; unfold raw1956 raw1957; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4972 = raw1957Labels := by decide +kernel
    rw [ha, hj, canonical1957 B hB]
  have hc1 : mixedMoment B raw1956 (Fin.cases (1 : Fin 2) singletonSmall4972) =
      mixedMoment B node3457 node3457Labels := by
    have ha : raw1956 = raw1958 := by apply Matrix.ext; unfold raw1956 raw1958; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4972 = raw1958Labels := by decide +kernel
    rw [ha, hj, canonical1958 B hB]
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

theorem singleton5036 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5036 node5036Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2428 node2428Labels + mixedMoment B node3450 node3450Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2055 singletonSmall5036
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5036) = raw2055Labels := by decide +kernel
  rw [hl, canonical2055 B hB] at h
  have hc0 : mixedMoment B raw2055 (Fin.cases (0 : Fin 2) singletonSmall5036) =
      mixedMoment B node2428 node2428Labels := by
    have ha : raw2055 = raw2056 := by apply Matrix.ext; unfold raw2055 raw2056; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5036 = raw2056Labels := by decide +kernel
    rw [ha, hj, canonical2056 B hB]
  have hc1 : mixedMoment B raw2055 (Fin.cases (1 : Fin 2) singletonSmall5036) =
      mixedMoment B node3450 node3450Labels := by
    have ha : raw2055 = raw2057 := by apply Matrix.ext; unfold raw2055 raw2057; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5036 = raw2057Labels := by decide +kernel
    rw [ha, hj, canonical2057 B hB]
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

theorem singleton5102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5102 node5102Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2512 node2512Labels + mixedMoment B node3471 node3471Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2127 singletonSmall5102
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5102) = raw2127Labels := by decide +kernel
  rw [hl, canonical2127 B hB] at h
  have hc0 : mixedMoment B raw2127 (Fin.cases (0 : Fin 2) singletonSmall5102) =
      mixedMoment B node2512 node2512Labels := by
    have ha : raw2127 = raw2128 := by apply Matrix.ext; unfold raw2127 raw2128; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5102 = raw2128Labels := by decide +kernel
    rw [ha, hj, canonical2128 B hB]
  have hc1 : mixedMoment B raw2127 (Fin.cases (1 : Fin 2) singletonSmall5102) =
      mixedMoment B node3471 node3471Labels := by
    have ha : raw2127 = raw2129 := by apply Matrix.ext; unfold raw2127 raw2129; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5102 = raw2129Labels := by decide +kernel
    rw [ha, hj, canonical2129 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5141 node5141Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2561 node2561Labels + mixedMoment B node3522 node3522Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2169 singletonSmall5141
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5141) = raw2169Labels := by decide +kernel
  rw [hl, canonical2169 B hB] at h
  have hc0 : mixedMoment B raw2169 (Fin.cases (0 : Fin 2) singletonSmall5141) =
      mixedMoment B node2561 node2561Labels := by
    have ha : raw2169 = raw2170 := by apply Matrix.ext; unfold raw2169 raw2170; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5141 = raw2170Labels := by decide +kernel
    rw [ha, hj, canonical2170 B hB]
  have hc1 : mixedMoment B raw2169 (Fin.cases (1 : Fin 2) singletonSmall5141) =
      mixedMoment B node3522 node3522Labels := by
    have ha : raw2169 = raw2171 := by apply Matrix.ext; unfold raw2169 raw2171; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5141 = raw2171Labels := by decide +kernel
    rw [ha, hj, canonical2171 B hB]
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

theorem singleton5275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5275 node5275Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2743 node2743Labels + mixedMoment B node3548 node3548Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2286 singletonSmall5275
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5275) = raw2286Labels := by decide +kernel
  rw [hl, canonical2286 B hB] at h
  have hc0 : mixedMoment B raw2286 (Fin.cases (0 : Fin 2) singletonSmall5275) =
      mixedMoment B node2743 node2743Labels := by
    have ha : raw2286 = raw2287 := by apply Matrix.ext; unfold raw2286 raw2287; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5275 = raw2287Labels := by decide +kernel
    rw [ha, hj, canonical2287 B hB]
  have hc1 : mixedMoment B raw2286 (Fin.cases (1 : Fin 2) singletonSmall5275) =
      mixedMoment B node3548 node3548Labels := by
    have ha : raw2286 = raw2288 := by apply Matrix.ext; unfold raw2286 raw2288; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5275 = raw2288Labels := by decide +kernel
    rw [ha, hj, canonical2288 B hB]
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

theorem sound1134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1134 node1134Labels = Sparse.eval nodeValue1134 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1134) = mixedMoment B node1134 node1134Labels := rfl
  simpa [nodeValue1134, Sparse.eval] using hc.symm

theorem sound1144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1144 node1144Labels = Sparse.eval nodeValue1144 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1144) = mixedMoment B node1144 node1144Labels := rfl
  simpa [nodeValue1144, Sparse.eval] using hc.symm

theorem sound1145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1145 node1145Labels = Sparse.eval nodeValue1145 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1145) = mixedMoment B node1145 node1145Labels := rfl
  simpa [nodeValue1145, Sparse.eval] using hc.symm

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

theorem sound1246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1246 node1246Labels = Sparse.eval nodeValue1246 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1246) = mixedMoment B node1246 node1246Labels := rfl
  simpa [nodeValue1246, Sparse.eval] using hc.symm

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

theorem sound2334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2334 node2334Labels = Sparse.eval nodeValue2334 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2334) = mixedMoment B node2334 node2334Labels := rfl
  simpa [nodeValue2334, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2428 node2428Labels = Sparse.eval nodeValue2428 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2428) = mixedMoment B node2428 node2428Labels := rfl
  simpa [nodeValue2428, Sparse.eval] using hc.symm

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

theorem sound2434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2434 node2434Labels = Sparse.eval nodeValue2434 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2434) = mixedMoment B node2434 node2434Labels := rfl
  simpa [nodeValue2434, Sparse.eval] using hc.symm

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

theorem sound2512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2512 node2512Labels = Sparse.eval nodeValue2512 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2512) = mixedMoment B node2512 node2512Labels := rfl
  simpa [nodeValue2512, Sparse.eval] using hc.symm

theorem sound2519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2519 node2519Labels = Sparse.eval nodeValue2519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2519) = mixedMoment B node2519 node2519Labels := rfl
  simpa [nodeValue2519, Sparse.eval] using hc.symm

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

theorem sound2561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2561 node2561Labels = Sparse.eval nodeValue2561 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2561) = mixedMoment B node2561 node2561Labels := rfl
  simpa [nodeValue2561, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2743 node2743Labels = Sparse.eval nodeValue2743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2743) = mixedMoment B node2743 node2743Labels := rfl
  simpa [nodeValue2743, Sparse.eval] using hc.symm

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

theorem sound3265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3265 node3265Labels = Sparse.eval nodeValue3265 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3265) = mixedMoment B node3265 node3265Labels := rfl
  simpa [nodeValue3265, Sparse.eval] using hc.symm

theorem sound3276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3276 node3276Labels = Sparse.eval nodeValue3276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3276) = mixedMoment B node3276 node3276Labels := rfl
  simpa [nodeValue3276, Sparse.eval] using hc.symm

theorem sound3277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3277 node3277Labels = Sparse.eval nodeValue3277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3277) = mixedMoment B node3277 node3277Labels := rfl
  simpa [nodeValue3277, Sparse.eval] using hc.symm

theorem sound3301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3301 node3301Labels = Sparse.eval nodeValue3301 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3301) = mixedMoment B node3301 node3301Labels := rfl
  simpa [nodeValue3301, Sparse.eval] using hc.symm

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

theorem sound3411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3411 node3411Labels = Sparse.eval nodeValue3411 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3411) = mixedMoment B node3411 node3411Labels := rfl
  simpa [nodeValue3411, Sparse.eval] using hc.symm

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

theorem sound3450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3450 node3450Labels = Sparse.eval nodeValue3450 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3450) = mixedMoment B node3450 node3450Labels := rfl
  simpa [nodeValue3450, Sparse.eval] using hc.symm

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

theorem sound3457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3457 node3457Labels = Sparse.eval nodeValue3457 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3457) = mixedMoment B node3457 node3457Labels := rfl
  simpa [nodeValue3457, Sparse.eval] using hc.symm

theorem sound3471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3471 node3471Labels = Sparse.eval nodeValue3471 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3471) = mixedMoment B node3471 node3471Labels := rfl
  simpa [nodeValue3471, Sparse.eval] using hc.symm

theorem sound3486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3486 node3486Labels = Sparse.eval nodeValue3486 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3486) = mixedMoment B node3486 node3486Labels := rfl
  simpa [nodeValue3486, Sparse.eval] using hc.symm

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

theorem sound3522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3522 node3522Labels = Sparse.eval nodeValue3522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3522) = mixedMoment B node3522 node3522Labels := rfl
  simpa [nodeValue3522, Sparse.eval] using hc.symm

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4549 node4549Labels = Sparse.eval nodeValue4549 (mixedVector B) := by
  have h := singleton4549 B _hB
  rw [sound1134 B _hB _hF, sound3265 B _hB _hF] at h
  norm_num [nodeValue4549, nodeValue1134, nodeValue3265, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4558 node4558Labels = Sparse.eval nodeValue4558 (mixedVector B) := by
  have h := singleton4558 B _hB
  rw [sound1144 B _hB _hF, sound3276 B _hB _hF] at h
  norm_num [nodeValue4558, nodeValue1144, nodeValue3276, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4559 node4559Labels = Sparse.eval nodeValue4559 (mixedVector B) := by
  have h := singleton4559 B _hB
  rw [sound1145 B _hB _hF, sound3277 B _hB _hF] at h
  norm_num [nodeValue4559, nodeValue1145, nodeValue3277, Sparse.eval] at h ⊢
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

theorem sound4612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4612 node4612Labels = Sparse.eval nodeValue4612 (mixedVector B) := by
  have h := singleton4612 B _hB
  rw [sound1246 B _hB _hF, sound3301 B _hB _hF] at h
  norm_num [nodeValue4612, nodeValue1246, nodeValue3301, Sparse.eval] at h ⊢
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

theorem sound4943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4943 node4943Labels = Sparse.eval nodeValue4943 (mixedVector B) := by
  have h := singleton4943 B _hB
  rw [sound2334 B _hB _hF, sound3411 B _hB _hF] at h
  norm_num [nodeValue4943, nodeValue2334, nodeValue3411, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4972 node4972Labels = Sparse.eval nodeValue4972 (mixedVector B) := by
  have h := singleton4972 B _hB
  rw [sound2434 B _hB _hF, sound3457 B _hB _hF] at h
  norm_num [nodeValue4972, nodeValue2434, nodeValue3457, Sparse.eval] at h ⊢
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

theorem sound5036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5036 node5036Labels = Sparse.eval nodeValue5036 (mixedVector B) := by
  have h := singleton5036 B _hB
  rw [sound2428 B _hB _hF, sound3450 B _hB _hF] at h
  norm_num [nodeValue5036, nodeValue2428, nodeValue3450, Sparse.eval] at h ⊢
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

theorem zero5101 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5101 node5101Labels = 0 := by
  exact mixedMoment_order_one B hB node5101 node5101Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5101 node5101Labels = Sparse.eval nodeValue5101 (mixedVector B) := by
  simpa only [nodeValue5101, Sparse.eval_nil] using zero5101 B _hB _hF

theorem sound5102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5102 node5102Labels = Sparse.eval nodeValue5102 (mixedVector B) := by
  have h := singleton5102 B _hB
  rw [sound2512 B _hB _hF, sound3471 B _hB _hF] at h
  norm_num [nodeValue5102, nodeValue2512, nodeValue3471, Sparse.eval] at h ⊢
  linarith only [h]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5141 node5141Labels = Sparse.eval nodeValue5141 (mixedVector B) := by
  have h := singleton5141 B _hB
  rw [sound2561 B _hB _hF, sound3522 B _hB _hF] at h
  norm_num [nodeValue5141, nodeValue2561, nodeValue3522, Sparse.eval] at h ⊢
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

theorem zero5274 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5274 node5274Labels = 0 := by
  exact mixedMoment_order_one B hB node5274 node5274Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5274 node5274Labels = Sparse.eval nodeValue5274 (mixedVector B) := by
  simpa only [nodeValue5274, Sparse.eval_nil] using zero5274 B _hB _hF

theorem sound5275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5275 node5275Labels = Sparse.eval nodeValue5275 (mixedVector B) := by
  have h := singleton5275 B _hB
  rw [sound2743 B _hB _hF, sound3548 B _hB _hF] at h
  norm_num [nodeValue5275, nodeValue2743, nodeValue3548, Sparse.eval] at h ⊢
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

theorem zero5371 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5371 node5371Labels = 0 := by
  exact mixedMoment_order_one B hB node5371 node5371Labels 1
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

theorem sound5367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5367 node5367Labels = Sparse.eval nodeValue5367 (mixedVector B) := by
  simpa only [nodeValue5367, Sparse.eval_nil] using zero5367 B _hB _hF

theorem sound5371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5371 node5371Labels = Sparse.eval nodeValue5371 (mixedVector B) := by
  simpa only [nodeValue5371, Sparse.eval_nil] using zero5371 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources69
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2235 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2235 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2235 + difference 0 1) (sourceB2235 + difference 1 0) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2235 + difference 0 1) (sourceB2235 + difference 1 0) sourceC2235) = raw30702 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30702; decide +kernel
    rw [ha]
    exact (canonical30702 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2235 + difference 0 2) (sourceB2235 + difference 2 0) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2235 + difference 0 2) (sourceB2235 + difference 2 0) sourceC2235) = raw30703 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30703; decide +kernel
    rw [ha]
    exact (canonical30703 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2235 + difference 0 3) (sourceB2235 + difference 3 0) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2235 + difference 0 3) (sourceB2235 + difference 3 0) sourceC2235) = raw30704 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30704; decide +kernel
    rw [ha]
    exact (canonical30704 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2235 + difference 0 4) (sourceB2235 + difference 4 0) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA2235 + difference 0 4) (sourceB2235 + difference 4 0) sourceC2235) = raw30705 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30705; decide +kernel
    rw [ha]
    exact (canonical30705 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2235 + difference 0 5) (sourceB2235 + difference 5 0) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2235 + difference 0 5) (sourceB2235 + difference 5 0) sourceC2235) = raw30706 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30706; decide +kernel
    rw [ha]
    exact (canonical30706 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2235 + difference 1 0) (sourceB2235 + difference 0 1) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA2235 + difference 1 0) (sourceB2235 + difference 0 1) sourceC2235) = raw30707 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30707; decide +kernel
    rw [ha]
    exact (canonical30707 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2235 + difference 1 2) (sourceB2235 + difference 2 1) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2235 + difference 1 2) (sourceB2235 + difference 2 1) sourceC2235) = raw30708 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30708; decide +kernel
    rw [ha]
    exact (canonical30708 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2235 + difference 1 3) (sourceB2235 + difference 3 1) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2235 + difference 1 3) (sourceB2235 + difference 3 1) sourceC2235) = raw30709 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30709; decide +kernel
    rw [ha]
    exact (canonical30709 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2235 + difference 1 4) (sourceB2235 + difference 4 1) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA2235 + difference 1 4) (sourceB2235 + difference 4 1) sourceC2235) = raw3936 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw3936; decide +kernel
    rw [ha]
    exact (canonical3936 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2235 + difference 1 5) (sourceB2235 + difference 5 1) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2235 + difference 1 5) (sourceB2235 + difference 5 1) sourceC2235) = raw30710 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30710; decide +kernel
    rw [ha]
    exact (canonical30710 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2235 + difference 2 0) (sourceB2235 + difference 0 2) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4549) := by
    have ha : (tripleCharges (sourceA2235 + difference 2 0) (sourceB2235 + difference 0 2) sourceC2235) = raw30711 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30711; decide +kernel
    rw [ha]
    exact (canonical30711 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2235 + difference 2 1) (sourceB2235 + difference 1 2) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2235 + difference 2 1) (sourceB2235 + difference 1 2) sourceC2235) = raw30712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30712; decide +kernel
    rw [ha]
    exact (canonical30712 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2235 + difference 2 3) (sourceB2235 + difference 3 2) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5036) := by
    have ha : (tripleCharges (sourceA2235 + difference 2 3) (sourceB2235 + difference 3 2) sourceC2235) = raw30713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30713; decide +kernel
    rw [ha]
    exact (canonical30713 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2235 + difference 2 4) (sourceB2235 + difference 4 2) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA2235 + difference 2 4) (sourceB2235 + difference 4 2) sourceC2235) = raw30714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30714; decide +kernel
    rw [ha]
    exact (canonical30714 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2235 + difference 2 5) (sourceB2235 + difference 5 2) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2235 + difference 2 5) (sourceB2235 + difference 5 2) sourceC2235) = raw30715 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30715; decide +kernel
    rw [ha]
    exact (canonical30715 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2235 + difference 3 0) (sourceB2235 + difference 0 3) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4549) := by
    have ha : (tripleCharges (sourceA2235 + difference 3 0) (sourceB2235 + difference 0 3) sourceC2235) = raw30716 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30716; decide +kernel
    rw [ha]
    exact (canonical30716 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2235 + difference 3 1) (sourceB2235 + difference 1 3) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2235 + difference 3 1) (sourceB2235 + difference 1 3) sourceC2235) = raw30717 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30717; decide +kernel
    rw [ha]
    exact (canonical30717 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2235 + difference 3 2) (sourceB2235 + difference 2 3) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5036) := by
    have ha : (tripleCharges (sourceA2235 + difference 3 2) (sourceB2235 + difference 2 3) sourceC2235) = raw30718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30718; decide +kernel
    rw [ha]
    exact (canonical30718 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2235 + difference 3 4) (sourceB2235 + difference 4 3) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA2235 + difference 3 4) (sourceB2235 + difference 4 3) sourceC2235) = raw30719 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30719; decide +kernel
    rw [ha]
    exact (canonical30719 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2235 + difference 3 5) (sourceB2235 + difference 5 3) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2235 + difference 3 5) (sourceB2235 + difference 5 3) sourceC2235) = raw30720 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30720; decide +kernel
    rw [ha]
    exact (canonical30720 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2235 + difference 4 0) (sourceB2235 + difference 0 4) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4558) := by
    have ha : (tripleCharges (sourceA2235 + difference 4 0) (sourceB2235 + difference 0 4) sourceC2235) = raw30721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30721; decide +kernel
    rw [ha]
    exact (canonical30721 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2235 + difference 4 1) (sourceB2235 + difference 1 4) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4952) := by
    have ha : (tripleCharges (sourceA2235 + difference 4 1) (sourceB2235 + difference 1 4) sourceC2235) = raw30722 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30722; decide +kernel
    rw [ha]
    exact (canonical30722 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2235 + difference 4 2) (sourceB2235 + difference 2 4) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA2235 + difference 4 2) (sourceB2235 + difference 2 4) sourceC2235) = raw30723 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30723; decide +kernel
    rw [ha]
    exact (canonical30723 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2235 + difference 4 3) (sourceB2235 + difference 3 4) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA2235 + difference 4 3) (sourceB2235 + difference 3 4) sourceC2235) = raw30724 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30724; decide +kernel
    rw [ha]
    exact (canonical30724 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2235 + difference 4 5) (sourceB2235 + difference 5 4) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5107) := by
    have ha : (tripleCharges (sourceA2235 + difference 4 5) (sourceB2235 + difference 5 4) sourceC2235) = raw30725 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30725; decide +kernel
    rw [ha]
    exact (canonical30725 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2235 + difference 5 0) (sourceB2235 + difference 0 5) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4559) := by
    have ha : (tripleCharges (sourceA2235 + difference 5 0) (sourceB2235 + difference 0 5) sourceC2235) = raw30726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30726; decide +kernel
    rw [ha]
    exact (canonical30726 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2235 + difference 5 1) (sourceB2235 + difference 1 5) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4953) := by
    have ha : (tripleCharges (sourceA2235 + difference 5 1) (sourceB2235 + difference 1 5) sourceC2235) = raw30727 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30727; decide +kernel
    rw [ha]
    exact (canonical30727 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2235 + difference 5 2) (sourceB2235 + difference 2 5) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4972) := by
    have ha : (tripleCharges (sourceA2235 + difference 5 2) (sourceB2235 + difference 2 5) sourceC2235) = raw30728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30728; decide +kernel
    rw [ha]
    exact (canonical30728 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2235 + difference 5 3) (sourceB2235 + difference 3 5) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4972) := by
    have ha : (tripleCharges (sourceA2235 + difference 5 3) (sourceB2235 + difference 3 5) sourceC2235) = raw30729 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30729; decide +kernel
    rw [ha]
    exact (canonical30729 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2235 + difference 5 4) (sourceB2235 + difference 4 5) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA2235 + difference 5 4) (sourceB2235 + difference 4 5) sourceC2235) = raw3933 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw3933; decide +kernel
    rw [ha]
    exact (canonical3933 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2235 sourceB2235 sourceC2235
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2235, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1833 : Integer.Sparse.reindex keyMap MixedData.row1833 = numericRow1833 := by decide +kernel

theorem numericCheck1833 (x : Master → ℝ) : Integer.Sparse.eval numericRow1833 x =
    (4 : ℝ) * reducedSource1833 x := by
  norm_num [numericRow1833, reducedSource1833, Integer.Sparse.eval, Sparse.eval, nodeValue4092, nodeValue4549, nodeValue4558, nodeValue4559, nodeValue4612, nodeValue4943, nodeValue4946, nodeValue4952, nodeValue4953, nodeValue4972, nodeValue5036, nodeValue5101, nodeValue5102, nodeValue5107, nodeValue5109, nodeValue5141, nodeValue5274, nodeValue5275, nodeValue5367, nodeValue5371, nodeValue5413]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1833 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1833 (mixedVector B) = 0 := by
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  have h4549 : mixedVector B (Sum.inr 4549) = Sparse.eval nodeValue4549 (mixedVector B) := by
    change mixedMoment B node4549 node4549Labels = _
    exact sound4549 B hB hF
  have h4558 : mixedVector B (Sum.inr 4558) = Sparse.eval nodeValue4558 (mixedVector B) := by
    change mixedMoment B node4558 node4558Labels = _
    exact sound4558 B hB hF
  have h4559 : mixedVector B (Sum.inr 4559) = Sparse.eval nodeValue4559 (mixedVector B) := by
    change mixedMoment B node4559 node4559Labels = _
    exact sound4559 B hB hF
  have h4612 : mixedVector B (Sum.inr 4612) = Sparse.eval nodeValue4612 (mixedVector B) := by
    change mixedMoment B node4612 node4612Labels = _
    exact sound4612 B hB hF
  have h4943 : mixedVector B (Sum.inr 4943) = Sparse.eval nodeValue4943 (mixedVector B) := by
    change mixedMoment B node4943 node4943Labels = _
    exact sound4943 B hB hF
  have h4946 : mixedVector B (Sum.inr 4946) = Sparse.eval nodeValue4946 (mixedVector B) := by
    change mixedMoment B node4946 node4946Labels = _
    exact sound4946 B hB hF
  have h4952 : mixedVector B (Sum.inr 4952) = Sparse.eval nodeValue4952 (mixedVector B) := by
    change mixedMoment B node4952 node4952Labels = _
    exact sound4952 B hB hF
  have h4953 : mixedVector B (Sum.inr 4953) = Sparse.eval nodeValue4953 (mixedVector B) := by
    change mixedMoment B node4953 node4953Labels = _
    exact sound4953 B hB hF
  have h4972 : mixedVector B (Sum.inr 4972) = Sparse.eval nodeValue4972 (mixedVector B) := by
    change mixedMoment B node4972 node4972Labels = _
    exact sound4972 B hB hF
  have h5036 : mixedVector B (Sum.inr 5036) = Sparse.eval nodeValue5036 (mixedVector B) := by
    change mixedMoment B node5036 node5036Labels = _
    exact sound5036 B hB hF
  have h5101 : mixedVector B (Sum.inr 5101) = Sparse.eval nodeValue5101 (mixedVector B) := by
    change mixedMoment B node5101 node5101Labels = _
    exact sound5101 B hB hF
  have h5102 : mixedVector B (Sum.inr 5102) = Sparse.eval nodeValue5102 (mixedVector B) := by
    change mixedMoment B node5102 node5102Labels = _
    exact sound5102 B hB hF
  have h5107 : mixedVector B (Sum.inr 5107) = Sparse.eval nodeValue5107 (mixedVector B) := by
    change mixedMoment B node5107 node5107Labels = _
    exact sound5107 B hB hF
  have h5109 : mixedVector B (Sum.inr 5109) = Sparse.eval nodeValue5109 (mixedVector B) := by
    change mixedMoment B node5109 node5109Labels = _
    exact sound5109 B hB hF
  have h5141 : mixedVector B (Sum.inr 5141) = Sparse.eval nodeValue5141 (mixedVector B) := by
    change mixedMoment B node5141 node5141Labels = _
    exact sound5141 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  have h5367 : mixedVector B (Sum.inr 5367) = Sparse.eval nodeValue5367 (mixedVector B) := by
    change mixedMoment B node5367 node5367Labels = _
    exact sound5367 B hB hF
  have h5371 : mixedVector B (Sum.inr 5371) = Sparse.eval nodeValue5371 (mixedVector B) := by
    change mixedMoment B node5371 node5371Labels = _
    exact sound5371 B hB hF
  have h5413 : mixedVector B (Sum.inr 5413) = Sparse.eval nodeValue5413 (mixedVector B) := by
    change mixedMoment B node5413 node5413Labels = _
    exact sound5413 B hB hF
  simpa only [sourceForm2235, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4092, h4549, h4558, h4559, h4612, h4943, h4946, h4952, h4953, h4972, h5036, h5101, h5102, h5107, h5109, h5141, h5274, h5275, h5367, h5371, h5413, reducedSource1833] using sourceEq2235 B hB

theorem rowSound1833_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1833 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1833, numericCheck1833, reducedZero1833 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833_e_oai
