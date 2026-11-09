-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1321_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:07:43.054448+00:00
-- url     : https://prove2.me/submissions/ce6f3a0a-0ff5-4194-b46d-55d2fe5e2bfa

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E124
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

theorem canonical1299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1299 raw1299Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw1299 raw1299Labels = mixedMoment B raw1299step0 raw1299step0Labels := by
      have ha : raw1299step0 = (fun i j => raw1299 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1299step0 raw1299; decide +kernel
      have hl : raw1299step0Labels = raw1299Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1299 raw1299Labels permutation8 permutation4
    mixedMoment B raw1299step0 raw1299step0Labels = mixedMoment B raw1299step1 raw1299step1Labels := by
      have ha : raw1299step1 = raw1299step0 := by apply Matrix.ext; unfold raw1299step1 raw1299step0; decide +kernel
      have hl : raw1299step0Labels = labelEmbedding7 ∘ raw1299step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1299step0 raw1299step0Labels raw1299step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

theorem canonical1300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1300 raw1300Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw1300 raw1300Labels = mixedMoment B raw1300step0 raw1300step0Labels := by
      have ha : raw1300step0 = (fun i j => raw1300 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1300step0 raw1300; decide +kernel
      have hl : raw1300step0Labels = raw1300Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1300 raw1300Labels permutation8 permutation4
    _ = mixedMoment B node1083 node1083Labels := by rfl

theorem canonical1301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1301 raw1301Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw1301 raw1301Labels = mixedMoment B raw1301step0 raw1301step0Labels := by
      have ha : raw1301step0 = (fun i j => raw1301 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1301step0 raw1301; decide +kernel
      have hl : raw1301step0Labels = raw1301Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1301 raw1301Labels permutation9 permutation6
    mixedMoment B raw1301step0 raw1301step0Labels = mixedMoment B raw1301step1 raw1301step1Labels := by
      have ha : raw1301step1 = -raw1301step0 := by apply Matrix.ext; change ∀ i j, raw1301step1 i j = -(raw1301step0 i j); unfold raw1301step1 raw1301step0; decide +kernel
      have hl : raw1301step1Labels = raw1301step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1301step1 raw1301step1Labels = mixedMoment B raw1301step2 raw1301step2Labels := by
      have ha : raw1301step2 = raw1301step1 := by apply Matrix.ext; unfold raw1301step2 raw1301step1; decide +kernel
      have hl : raw1301step1Labels = labelEmbedding1 ∘ raw1301step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1301step1 raw1301step1Labels raw1301step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

theorem canonical1305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1305 raw1305Labels = mixedMoment B node4507 node4507Labels := by
  calc
    mixedMoment B raw1305 raw1305Labels = mixedMoment B raw1305step0 raw1305step0Labels := by
      have ha : raw1305step0 = (fun i j => raw1305 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1305step0 raw1305; decide +kernel
      have hl : raw1305step0Labels = raw1305Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1305 raw1305Labels permutation2 permutation4
    mixedMoment B raw1305step0 raw1305step0Labels = mixedMoment B raw1305step1 raw1305step1Labels := by
      have ha : raw1305step1 = raw1305step0 := by apply Matrix.ext; unfold raw1305step1 raw1305step0; decide +kernel
      have hl : raw1305step0Labels = labelEmbedding7 ∘ raw1305step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1305step0 raw1305step0Labels raw1305step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4507 node4507Labels := by rfl

theorem canonical1306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1306 raw1306Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw1306 raw1306Labels = mixedMoment B raw1306step0 raw1306step0Labels := by
      have ha : raw1306step0 = (fun i j => raw1306 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1306step0 raw1306; decide +kernel
      have hl : raw1306step0Labels = raw1306Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1306 raw1306Labels permutation2 permutation4
    _ = mixedMoment B node1091 node1091Labels := by rfl

theorem canonical1307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1307 raw1307Labels = mixedMoment B node1756 node1756Labels := by
  calc
    mixedMoment B raw1307 raw1307Labels = mixedMoment B raw1307step0 raw1307step0Labels := by
      have ha : raw1307step0 = (fun i j => raw1307 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1307step0 raw1307; decide +kernel
      have hl : raw1307step0Labels = raw1307Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1307 raw1307Labels permutation3 permutation6
    mixedMoment B raw1307step0 raw1307step0Labels = mixedMoment B raw1307step1 raw1307step1Labels := by
      have ha : raw1307step1 = -raw1307step0 := by apply Matrix.ext; change ∀ i j, raw1307step1 i j = -(raw1307step0 i j); unfold raw1307step1 raw1307step0; decide +kernel
      have hl : raw1307step1Labels = raw1307step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1307step1 raw1307step1Labels = mixedMoment B raw1307step2 raw1307step2Labels := by
      have ha : raw1307step2 = raw1307step1 := by apply Matrix.ext; unfold raw1307step2 raw1307step1; decide +kernel
      have hl : raw1307step1Labels = labelEmbedding1 ∘ raw1307step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1307step1 raw1307step1Labels raw1307step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1756 node1756Labels := by rfl

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

theorem canonical21634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21634 raw21634Labels = mixedMoment B node4901 node4901Labels := by
  calc
    mixedMoment B raw21634 raw21634Labels = mixedMoment B raw21634step0 raw21634step0Labels := by
      have hz : ∀ j, raw21634 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21634step0 = (fun i j => raw21634 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21634step0 raw21634; decide +kernel
      have hl : raw21634step0Labels = raw21634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21634 raw21634Labels permutation434 hz
    mixedMoment B raw21634step0 raw21634step0Labels = mixedMoment B raw21634step1 raw21634step1Labels := by
      have hz : ∀ j, raw21634step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21634step1 = (fun i j => raw21634step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21634step1 raw21634step0; decide +kernel
      have hl : raw21634step1Labels = raw21634step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21634step0 raw21634step0Labels permutation80 hz
    mixedMoment B raw21634step1 raw21634step1Labels = mixedMoment B raw21634step2 raw21634step2Labels := by
      have hz : ∀ j, raw21634step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21634step2 = (fun i j => raw21634step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21634step2 raw21634step1; decide +kernel
      have hl : raw21634step2Labels = raw21634step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21634step1 raw21634step1Labels permutation14 hz
    _ = mixedMoment B node4901 node4901Labels := by rfl

theorem canonical21647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21647 raw21647Labels = mixedMoment B node4192 node4192Labels := by
  calc
    mixedMoment B raw21647 raw21647Labels = mixedMoment B raw21647step0 raw21647step0Labels := by
      have hz : ∀ j, raw21647 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21647step0 = (fun i j => raw21647 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21647step0 raw21647; decide +kernel
      have hl : raw21647step0Labels = raw21647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21647 raw21647Labels permutation434 hz
    mixedMoment B raw21647step0 raw21647step0Labels = mixedMoment B raw21647step1 raw21647step1Labels := by
      have hz : ∀ j, raw21647step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21647step1 = (fun i j => raw21647step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21647step1 raw21647step0; decide +kernel
      have hl : raw21647step1Labels = raw21647step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21647step0 raw21647step0Labels permutation80 hz
    mixedMoment B raw21647step1 raw21647step1Labels = mixedMoment B raw21647step2 raw21647step2Labels := by
      have hz : ∀ j, raw21647step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21647step2 = (fun i j => raw21647step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21647step2 raw21647step1; decide +kernel
      have hl : raw21647step2Labels = raw21647step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21647step1 raw21647step1Labels permutation14 hz
    _ = mixedMoment B node4192 node4192Labels := by rfl

theorem canonical21648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21648 raw21648Labels = mixedMoment B node4361 node4361Labels := by
  calc
    mixedMoment B raw21648 raw21648Labels = mixedMoment B raw21648step0 raw21648step0Labels := by
      have hz : ∀ j, raw21648 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21648step0 = (fun i j => raw21648 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21648step0 raw21648; decide +kernel
      have hl : raw21648step0Labels = raw21648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21648 raw21648Labels permutation434 hz
    mixedMoment B raw21648step0 raw21648step0Labels = mixedMoment B raw21648step1 raw21648step1Labels := by
      have hz : ∀ j, raw21648step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21648step1 = (fun i j => raw21648step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21648step1 raw21648step0; decide +kernel
      have hl : raw21648step1Labels = raw21648step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21648step0 raw21648step0Labels permutation80 hz
    _ = mixedMoment B node4361 node4361Labels := by rfl

theorem canonical21649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21649 raw21649Labels = mixedMoment B node4361 node4361Labels := by
  calc
    mixedMoment B raw21649 raw21649Labels = mixedMoment B raw21649step0 raw21649step0Labels := by
      have hz : ∀ j, raw21649 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21649step0 = (fun i j => raw21649 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21649step0 raw21649; decide +kernel
      have hl : raw21649step0Labels = raw21649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21649 raw21649Labels permutation434 hz
    mixedMoment B raw21649step0 raw21649step0Labels = mixedMoment B raw21649step1 raw21649step1Labels := by
      have hz : ∀ j, raw21649step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21649step1 = (fun i j => raw21649step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21649step1 raw21649step0; decide +kernel
      have hl : raw21649step1Labels = raw21649step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21649step0 raw21649step0Labels permutation56 hz
    _ = mixedMoment B node4361 node4361Labels := by rfl

theorem canonical21650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21650 raw21650Labels = mixedMoment B node4361 node4361Labels := by
  calc
    mixedMoment B raw21650 raw21650Labels = mixedMoment B raw21650step0 raw21650step0Labels := by
      have hz : ∀ j, raw21650 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21650step0 = (fun i j => raw21650 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21650step0 raw21650; decide +kernel
      have hl : raw21650step0Labels = raw21650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21650 raw21650Labels permutation346 hz
    mixedMoment B raw21650step0 raw21650step0Labels = mixedMoment B raw21650step1 raw21650step1Labels := by
      have hz : ∀ j, raw21650step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21650step1 = (fun i j => raw21650step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21650step1 raw21650step0; decide +kernel
      have hl : raw21650step1Labels = raw21650step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21650step0 raw21650step0Labels permutation56 hz
    _ = mixedMoment B node4361 node4361Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical183
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23518 raw23518Labels = mixedMoment B node4180 node4180Labels := by
  calc
    mixedMoment B raw23518 raw23518Labels = mixedMoment B raw23518step0 raw23518step0Labels := by
      have hz : ∀ j, raw23518 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23518step0 = (fun i j => raw23518 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23518step0 raw23518; decide +kernel
      have hl : raw23518step0Labels = raw23518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23518 raw23518Labels permutation434 hz
    mixedMoment B raw23518step0 raw23518step0Labels = mixedMoment B raw23518step1 raw23518step1Labels := by
      have hz : ∀ j, raw23518step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23518step1 = (fun i j => raw23518step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23518step1 raw23518step0; decide +kernel
      have hl : raw23518step1Labels = raw23518step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23518step0 raw23518step0Labels permutation80 hz
    mixedMoment B raw23518step1 raw23518step1Labels = mixedMoment B raw23518step2 raw23518step2Labels := by
      have ha : raw23518step2 = (fun i j => raw23518step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23518step2 raw23518step1; decide +kernel
      have hl : raw23518step2Labels = raw23518step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23518step1 raw23518step1Labels permutation9 permutation2
    _ = mixedMoment B node4180 node4180Labels := by rfl

theorem canonical23519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23519 raw23519Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw23519 raw23519Labels = mixedMoment B raw23519step0 raw23519step0Labels := by
      have hz : ∀ j, raw23519 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23519step0 = (fun i j => raw23519 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23519step0 raw23519; decide +kernel
      have hl : raw23519step0Labels = raw23519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23519 raw23519Labels permutation434 hz
    mixedMoment B raw23519step0 raw23519step0Labels = mixedMoment B raw23519step1 raw23519step1Labels := by
      have ha : raw23519step1 = (fun i j => raw23519step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23519step1 raw23519step0; decide +kernel
      have hl : raw23519step1Labels = raw23519step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23519step0 raw23519step0Labels permutation39 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

theorem canonical23520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23520 raw23520Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw23520 raw23520Labels = mixedMoment B raw23520step0 raw23520step0Labels := by
      have hz : ∀ j, raw23520 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23520step0 = (fun i j => raw23520 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23520step0 raw23520; decide +kernel
      have hl : raw23520step0Labels = raw23520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23520 raw23520Labels permutation346 hz
    mixedMoment B raw23520step0 raw23520step0Labels = mixedMoment B raw23520step1 raw23520step1Labels := by
      have ha : raw23520step1 = (fun i j => raw23520step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23520step1 raw23520step0; decide +kernel
      have hl : raw23520step1Labels = raw23520step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23520step0 raw23520step0Labels permutation39 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

theorem canonical23521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23521 raw23521Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw23521 raw23521Labels = mixedMoment B raw23521step0 raw23521step0Labels := by
      have hz : ∀ j, raw23521 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23521step0 = (fun i j => raw23521 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23521step0 raw23521; decide +kernel
      have hl : raw23521step0Labels = raw23521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23521 raw23521Labels permutation434 hz
    mixedMoment B raw23521step0 raw23521step0Labels = mixedMoment B raw23521step1 raw23521step1Labels := by
      have hz : ∀ j, raw23521step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23521step1 = (fun i j => raw23521step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23521step1 raw23521step0; decide +kernel
      have hl : raw23521step1Labels = raw23521step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23521step0 raw23521step0Labels permutation80 hz
    mixedMoment B raw23521step1 raw23521step1Labels = mixedMoment B raw23521step2 raw23521step2Labels := by
      have ha : raw23521step2 = (fun i j => raw23521step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23521step2 raw23521step1; decide +kernel
      have hl : raw23521step2Labels = raw23521step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23521step1 raw23521step1Labels permutation9 permutation2
    _ = mixedMoment B node4498 node4498Labels := by rfl

theorem canonical23522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23522 raw23522Labels = mixedMoment B node4180 node4180Labels := by
  calc
    mixedMoment B raw23522 raw23522Labels = mixedMoment B raw23522step0 raw23522step0Labels := by
      have hz : ∀ j, raw23522 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23522step0 = (fun i j => raw23522 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23522step0 raw23522; decide +kernel
      have hl : raw23522step0Labels = raw23522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23522 raw23522Labels permutation434 hz
    mixedMoment B raw23522step0 raw23522step0Labels = mixedMoment B raw23522step1 raw23522step1Labels := by
      have hz : ∀ j, raw23522step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23522step1 = (fun i j => raw23522step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23522step1 raw23522step0; decide +kernel
      have hl : raw23522step1Labels = raw23522step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23522step0 raw23522step0Labels permutation56 hz
    mixedMoment B raw23522step1 raw23522step1Labels = mixedMoment B raw23522step2 raw23522step2Labels := by
      have ha : raw23522step2 = (fun i j => raw23522step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23522step2 raw23522step1; decide +kernel
      have hl : raw23522step2Labels = raw23522step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23522step1 raw23522step1Labels permutation9 permutation2
    _ = mixedMoment B node4180 node4180Labels := by rfl

theorem canonical23523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23523 raw23523Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw23523 raw23523Labels = mixedMoment B raw23523step0 raw23523step0Labels := by
      have hz : ∀ j, raw23523 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23523step0 = (fun i j => raw23523 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23523step0 raw23523; decide +kernel
      have hl : raw23523step0Labels = raw23523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23523 raw23523Labels permutation434 hz
    mixedMoment B raw23523step0 raw23523step0Labels = mixedMoment B raw23523step1 raw23523step1Labels := by
      have ha : raw23523step1 = (fun i j => raw23523step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23523step1 raw23523step0; decide +kernel
      have hl : raw23523step1Labels = raw23523step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23523step0 raw23523step0Labels permutation33 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

theorem canonical23524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23524 raw23524Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw23524 raw23524Labels = mixedMoment B raw23524step0 raw23524step0Labels := by
      have hz : ∀ j, raw23524 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23524step0 = (fun i j => raw23524 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23524step0 raw23524; decide +kernel
      have hl : raw23524step0Labels = raw23524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23524 raw23524Labels permutation265 hz
    mixedMoment B raw23524step0 raw23524step0Labels = mixedMoment B raw23524step1 raw23524step1Labels := by
      have ha : raw23524step1 = (fun i j => raw23524step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23524step1 raw23524step0; decide +kernel
      have hl : raw23524step1Labels = raw23524step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23524step0 raw23524step0Labels permutation39 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

theorem canonical23525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23525 raw23525Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw23525 raw23525Labels = mixedMoment B raw23525step0 raw23525step0Labels := by
      have hz : ∀ j, raw23525 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23525step0 = (fun i j => raw23525 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23525step0 raw23525; decide +kernel
      have hl : raw23525step0Labels = raw23525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23525 raw23525Labels permutation434 hz
    mixedMoment B raw23525step0 raw23525step0Labels = mixedMoment B raw23525step1 raw23525step1Labels := by
      have hz : ∀ j, raw23525step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23525step1 = (fun i j => raw23525step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23525step1 raw23525step0; decide +kernel
      have hl : raw23525step1Labels = raw23525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23525step0 raw23525step0Labels permutation56 hz
    mixedMoment B raw23525step1 raw23525step1Labels = mixedMoment B raw23525step2 raw23525step2Labels := by
      have ha : raw23525step2 = (fun i j => raw23525step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23525step2 raw23525step1; decide +kernel
      have hl : raw23525step2Labels = raw23525step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23525step1 raw23525step1Labels permutation9 permutation2
    _ = mixedMoment B node4498 node4498Labels := by rfl

theorem canonical23526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23526 raw23526Labels = mixedMoment B node4180 node4180Labels := by
  calc
    mixedMoment B raw23526 raw23526Labels = mixedMoment B raw23526step0 raw23526step0Labels := by
      have hz : ∀ j, raw23526 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23526step0 = (fun i j => raw23526 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23526step0 raw23526; decide +kernel
      have hl : raw23526step0Labels = raw23526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23526 raw23526Labels permutation346 hz
    mixedMoment B raw23526step0 raw23526step0Labels = mixedMoment B raw23526step1 raw23526step1Labels := by
      have hz : ∀ j, raw23526step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23526step1 = (fun i j => raw23526step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23526step1 raw23526step0; decide +kernel
      have hl : raw23526step1Labels = raw23526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23526step0 raw23526step0Labels permutation56 hz
    mixedMoment B raw23526step1 raw23526step1Labels = mixedMoment B raw23526step2 raw23526step2Labels := by
      have ha : raw23526step2 = (fun i j => raw23526step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23526step2 raw23526step1; decide +kernel
      have hl : raw23526step2Labels = raw23526step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23526step1 raw23526step1Labels permutation9 permutation2
    _ = mixedMoment B node4180 node4180Labels := by rfl

theorem canonical23527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23527 raw23527Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw23527 raw23527Labels = mixedMoment B raw23527step0 raw23527step0Labels := by
      have hz : ∀ j, raw23527 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23527step0 = (fun i j => raw23527 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23527step0 raw23527; decide +kernel
      have hl : raw23527step0Labels = raw23527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23527 raw23527Labels permutation346 hz
    mixedMoment B raw23527step0 raw23527step0Labels = mixedMoment B raw23527step1 raw23527step1Labels := by
      have ha : raw23527step1 = (fun i j => raw23527step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23527step1 raw23527step0; decide +kernel
      have hl : raw23527step1Labels = raw23527step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23527step0 raw23527step0Labels permutation33 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

theorem canonical23528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23528 raw23528Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw23528 raw23528Labels = mixedMoment B raw23528step0 raw23528step0Labels := by
      have hz : ∀ j, raw23528 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23528step0 = (fun i j => raw23528 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23528step0 raw23528; decide +kernel
      have hl : raw23528step0Labels = raw23528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23528 raw23528Labels permutation265 hz
    mixedMoment B raw23528step0 raw23528step0Labels = mixedMoment B raw23528step1 raw23528step1Labels := by
      have ha : raw23528step1 = (fun i j => raw23528step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23528step1 raw23528step0; decide +kernel
      have hl : raw23528step1Labels = raw23528step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23528step0 raw23528step0Labels permutation33 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

theorem canonical23529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23529 raw23529Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw23529 raw23529Labels = mixedMoment B raw23529step0 raw23529step0Labels := by
      have hz : ∀ j, raw23529 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23529step0 = (fun i j => raw23529 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23529step0 raw23529; decide +kernel
      have hl : raw23529step0Labels = raw23529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23529 raw23529Labels permutation346 hz
    mixedMoment B raw23529step0 raw23529step0Labels = mixedMoment B raw23529step1 raw23529step1Labels := by
      have hz : ∀ j, raw23529step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23529step1 = (fun i j => raw23529step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23529step1 raw23529step0; decide +kernel
      have hl : raw23529step1Labels = raw23529step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23529step0 raw23529step0Labels permutation56 hz
    mixedMoment B raw23529step1 raw23529step1Labels = mixedMoment B raw23529step2 raw23529step2Labels := by
      have ha : raw23529step2 = (fun i j => raw23529step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23529step2 raw23529step1; decide +kernel
      have hl : raw23529step2Labels = raw23529step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23529step1 raw23529step1Labels permutation9 permutation2
    _ = mixedMoment B node4498 node4498Labels := by rfl

theorem canonical23530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23530 raw23530Labels = mixedMoment B node4191 node4191Labels := by
  calc
    mixedMoment B raw23530 raw23530Labels = mixedMoment B raw23530step0 raw23530step0Labels := by
      have hz : ∀ j, raw23530 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23530step0 = (fun i j => raw23530 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23530step0 raw23530; decide +kernel
      have hl : raw23530step0Labels = raw23530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23530 raw23530Labels permutation434 hz
    mixedMoment B raw23530step0 raw23530step0Labels = mixedMoment B raw23530step1 raw23530step1Labels := by
      have hz : ∀ j, raw23530step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23530step1 = (fun i j => raw23530step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23530step1 raw23530step0; decide +kernel
      have hl : raw23530step1Labels = raw23530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23530step0 raw23530step0Labels permutation80 hz
    mixedMoment B raw23530step1 raw23530step1Labels = mixedMoment B raw23530step2 raw23530step2Labels := by
      have hz : ∀ j, raw23530step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23530step2 = (fun i j => raw23530step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23530step2 raw23530step1; decide +kernel
      have hl : raw23530step2Labels = raw23530step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23530step1 raw23530step1Labels permutation14 hz
    mixedMoment B raw23530step2 raw23530step2Labels = mixedMoment B raw23530step3 raw23530step3Labels := by
      have ha : raw23530step3 = (fun i j => raw23530step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23530step3 raw23530step2; decide +kernel
      have hl : raw23530step3Labels = raw23530step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23530step2 raw23530step2Labels permutation3 permutation2
    _ = mixedMoment B node4191 node4191Labels := by rfl

theorem canonical23531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23531 raw23531Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw23531 raw23531Labels = mixedMoment B raw23531step0 raw23531step0Labels := by
      have hz : ∀ j, raw23531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23531step0 = (fun i j => raw23531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23531step0 raw23531; decide +kernel
      have hl : raw23531step0Labels = raw23531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23531 raw23531Labels permutation434 hz
    mixedMoment B raw23531step0 raw23531step0Labels = mixedMoment B raw23531step1 raw23531step1Labels := by
      have hz : ∀ j, raw23531step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23531step1 = (fun i j => raw23531step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23531step1 raw23531step0; decide +kernel
      have hl : raw23531step1Labels = raw23531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23531step0 raw23531step0Labels permutation80 hz
    mixedMoment B raw23531step1 raw23531step1Labels = mixedMoment B raw23531step2 raw23531step2Labels := by
      have ha : raw23531step2 = (fun i j => raw23531step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23531step2 raw23531step1; decide +kernel
      have hl : raw23531step2Labels = raw23531step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23531step1 raw23531step1Labels permutation9 permutation2
    _ = mixedMoment B node4360 node4360Labels := by rfl

theorem canonical23532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23532 raw23532Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw23532 raw23532Labels = mixedMoment B raw23532step0 raw23532step0Labels := by
      have hz : ∀ j, raw23532 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23532step0 = (fun i j => raw23532 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23532step0 raw23532; decide +kernel
      have hl : raw23532step0Labels = raw23532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23532 raw23532Labels permutation434 hz
    mixedMoment B raw23532step0 raw23532step0Labels = mixedMoment B raw23532step1 raw23532step1Labels := by
      have hz : ∀ j, raw23532step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23532step1 = (fun i j => raw23532step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23532step1 raw23532step0; decide +kernel
      have hl : raw23532step1Labels = raw23532step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23532step0 raw23532step0Labels permutation56 hz
    mixedMoment B raw23532step1 raw23532step1Labels = mixedMoment B raw23532step2 raw23532step2Labels := by
      have ha : raw23532step2 = (fun i j => raw23532step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23532step2 raw23532step1; decide +kernel
      have hl : raw23532step2Labels = raw23532step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23532step1 raw23532step1Labels permutation9 permutation2
    _ = mixedMoment B node4360 node4360Labels := by rfl

theorem canonical23533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23533 raw23533Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw23533 raw23533Labels = mixedMoment B raw23533step0 raw23533step0Labels := by
      have hz : ∀ j, raw23533 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23533step0 = (fun i j => raw23533 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23533step0 raw23533; decide +kernel
      have hl : raw23533step0Labels = raw23533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23533 raw23533Labels permutation346 hz
    mixedMoment B raw23533step0 raw23533step0Labels = mixedMoment B raw23533step1 raw23533step1Labels := by
      have hz : ∀ j, raw23533step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23533step1 = (fun i j => raw23533step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23533step1 raw23533step0; decide +kernel
      have hl : raw23533step1Labels = raw23533step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23533step0 raw23533step0Labels permutation56 hz
    mixedMoment B raw23533step1 raw23533step1Labels = mixedMoment B raw23533step2 raw23533step2Labels := by
      have ha : raw23533step2 = (fun i j => raw23533step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23533step2 raw23533step1; decide +kernel
      have hl : raw23533step2Labels = raw23533step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23533step1 raw23533step1Labels permutation9 permutation2
    _ = mixedMoment B node4360 node4360Labels := by rfl

theorem canonical23534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23534 raw23534Labels = mixedMoment B node4505 node4505Labels := by
  calc
    mixedMoment B raw23534 raw23534Labels = mixedMoment B raw23534step0 raw23534step0Labels := by
      have hz : ∀ j, raw23534 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23534step0 = (fun i j => raw23534 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23534step0 raw23534; decide +kernel
      have hl : raw23534step0Labels = raw23534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23534 raw23534Labels permutation434 hz
    mixedMoment B raw23534step0 raw23534step0Labels = mixedMoment B raw23534step1 raw23534step1Labels := by
      have hz : ∀ j, raw23534step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23534step1 = (fun i j => raw23534step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23534step1 raw23534step0; decide +kernel
      have hl : raw23534step1Labels = raw23534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23534step0 raw23534step0Labels permutation80 hz
    mixedMoment B raw23534step1 raw23534step1Labels = mixedMoment B raw23534step2 raw23534step2Labels := by
      have hz : ∀ j, raw23534step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23534step2 = (fun i j => raw23534step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23534step2 raw23534step1; decide +kernel
      have hl : raw23534step2Labels = raw23534step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23534step1 raw23534step1Labels permutation14 hz
    mixedMoment B raw23534step2 raw23534step2Labels = mixedMoment B raw23534step3 raw23534step3Labels := by
      have ha : raw23534step3 = (fun i j => raw23534step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23534step3 raw23534step2; decide +kernel
      have hl : raw23534step3Labels = raw23534step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23534step2 raw23534step2Labels permutation3 permutation2
    _ = mixedMoment B node4505 node4505Labels := by rfl

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

theorem canonical816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw816 raw816Labels = mixedMoment B node4180 node4180Labels := by
  calc
    mixedMoment B raw816 raw816Labels = mixedMoment B raw816step0 raw816step0Labels := by
      have ha : raw816step0 = (fun i j => raw816 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw816step0 raw816; decide +kernel
      have hl : raw816step0Labels = raw816Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw816 raw816Labels permutation8 permutation4
    mixedMoment B raw816step0 raw816step0Labels = mixedMoment B raw816step1 raw816step1Labels := by
      have ha : raw816step1 = raw816step0 := by apply Matrix.ext; unfold raw816step1 raw816step0; decide +kernel
      have hl : raw816step0Labels = labelEmbedding7 ∘ raw816step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw816step0 raw816step0Labels raw816step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4180 node4180Labels := by rfl

theorem canonical817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw817 raw817Labels = mixedMoment B node608 node608Labels := by
  calc
    mixedMoment B raw817 raw817Labels = mixedMoment B raw817step0 raw817step0Labels := by
      have ha : raw817step0 = (fun i j => raw817 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw817step0 raw817; decide +kernel
      have hl : raw817step0Labels = raw817Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw817 raw817Labels permutation8 permutation4
    _ = mixedMoment B node608 node608Labels := by rfl

theorem canonical818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw818 raw818Labels = mixedMoment B node1519 node1519Labels := by
  calc
    mixedMoment B raw818 raw818Labels = mixedMoment B raw818step0 raw818step0Labels := by
      have ha : raw818step0 = (fun i j => raw818 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw818step0 raw818; decide +kernel
      have hl : raw818step0Labels = raw818Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw818 raw818Labels permutation8 permutation6
    mixedMoment B raw818step0 raw818step0Labels = mixedMoment B raw818step1 raw818step1Labels := by
      have ha : raw818step1 = -raw818step0 := by apply Matrix.ext; change ∀ i j, raw818step1 i j = -(raw818step0 i j); unfold raw818step1 raw818step0; decide +kernel
      have hl : raw818step1Labels = raw818step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw818step1 raw818step1Labels = mixedMoment B raw818step2 raw818step2Labels := by
      have ha : raw818step2 = raw818step1 := by apply Matrix.ext; unfold raw818step2 raw818step1; decide +kernel
      have hl : raw818step1Labels = labelEmbedding1 ∘ raw818step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw818step1 raw818step1Labels raw818step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1519 node1519Labels := by rfl

theorem canonical840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw840 raw840Labels = mixedMoment B node4191 node4191Labels := by
  calc
    mixedMoment B raw840 raw840Labels = mixedMoment B raw840step0 raw840step0Labels := by
      have ha : raw840step0 = (fun i j => raw840 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw840step0 raw840; decide +kernel
      have hl : raw840step0Labels = raw840Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw840 raw840Labels permutation2 permutation4
    mixedMoment B raw840step0 raw840step0Labels = mixedMoment B raw840step1 raw840step1Labels := by
      have ha : raw840step1 = raw840step0 := by apply Matrix.ext; unfold raw840step1 raw840step0; decide +kernel
      have hl : raw840step0Labels = labelEmbedding7 ∘ raw840step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw840step0 raw840step0Labels raw840step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4191 node4191Labels := by rfl

theorem canonical841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw841 raw841Labels = mixedMoment B node619 node619Labels := by
  calc
    mixedMoment B raw841 raw841Labels = mixedMoment B raw841step0 raw841step0Labels := by
      have ha : raw841step0 = (fun i j => raw841 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw841step0 raw841; decide +kernel
      have hl : raw841step0Labels = raw841Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw841 raw841Labels permutation2 permutation4
    _ = mixedMoment B node619 node619Labels := by rfl

theorem canonical842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw842 raw842Labels = mixedMoment B node1538 node1538Labels := by
  calc
    mixedMoment B raw842 raw842Labels = mixedMoment B raw842step0 raw842step0Labels := by
      have ha : raw842step0 = (fun i j => raw842 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw842step0 raw842; decide +kernel
      have hl : raw842step0Labels = raw842Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw842 raw842Labels permutation2 permutation6
    mixedMoment B raw842step0 raw842step0Labels = mixedMoment B raw842step1 raw842step1Labels := by
      have ha : raw842step1 = -raw842step0 := by apply Matrix.ext; change ∀ i j, raw842step1 i j = -(raw842step0 i j); unfold raw842step1 raw842step0; decide +kernel
      have hl : raw842step1Labels = raw842step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw842step1 raw842step1Labels = mixedMoment B raw842step2 raw842step2Labels := by
      have ha : raw842step2 = raw842step1 := by apply Matrix.ext; unfold raw842step2 raw842step1; decide +kernel
      have hl : raw842step1Labels = labelEmbedding1 ∘ raw842step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw842step1 raw842step1Labels raw842step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1538 node1538Labels := by rfl

theorem canonical843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw843 raw843Labels = mixedMoment B node4192 node4192Labels := by
  calc
    mixedMoment B raw843 raw843Labels = mixedMoment B raw843step0 raw843step0Labels := by
      have ha : raw843step0 = (fun i j => raw843 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw843step0 raw843; decide +kernel
      have hl : raw843step0Labels = raw843Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw843 raw843Labels permutation2 permutation4
    mixedMoment B raw843step0 raw843step0Labels = mixedMoment B raw843step1 raw843step1Labels := by
      have ha : raw843step1 = raw843step0 := by apply Matrix.ext; unfold raw843step1 raw843step0; decide +kernel
      have hl : raw843step0Labels = labelEmbedding7 ∘ raw843step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw843step0 raw843step0Labels raw843step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4192 node4192Labels := by rfl

theorem canonical844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw844 raw844Labels = mixedMoment B node620 node620Labels := by
  calc
    mixedMoment B raw844 raw844Labels = mixedMoment B raw844step0 raw844step0Labels := by
      have ha : raw844step0 = (fun i j => raw844 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw844step0 raw844; decide +kernel
      have hl : raw844step0Labels = raw844Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw844 raw844Labels permutation2 permutation4
    _ = mixedMoment B node620 node620Labels := by rfl

theorem canonical845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw845 raw845Labels = mixedMoment B node1539 node1539Labels := by
  calc
    mixedMoment B raw845 raw845Labels = mixedMoment B raw845step0 raw845step0Labels := by
      have ha : raw845step0 = (fun i j => raw845 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw845step0 raw845; decide +kernel
      have hl : raw845step0Labels = raw845Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw845 raw845Labels permutation3 permutation6
    mixedMoment B raw845step0 raw845step0Labels = mixedMoment B raw845step1 raw845step1Labels := by
      have ha : raw845step1 = -raw845step0 := by apply Matrix.ext; change ∀ i j, raw845step1 i j = -(raw845step0 i j); unfold raw845step1 raw845step0; decide +kernel
      have hl : raw845step1Labels = raw845step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw845step1 raw845step1Labels = mixedMoment B raw845step2 raw845step2Labels := by
      have ha : raw845step2 = raw845step1 := by apply Matrix.ext; unfold raw845step2 raw845step1; decide +kernel
      have hl : raw845step1Labels = labelEmbedding1 ∘ raw845step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw845step1 raw845step1Labels raw845step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1539 node1539Labels := by rfl

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

theorem canonical1134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1134 raw1134Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw1134 raw1134Labels = mixedMoment B raw1134step0 raw1134step0Labels := by
      have ha : raw1134step0 = (fun i j => raw1134 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1134step0 raw1134; decide +kernel
      have hl : raw1134step0Labels = raw1134Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1134 raw1134Labels permutation32 permutation4
    mixedMoment B raw1134step0 raw1134step0Labels = mixedMoment B raw1134step1 raw1134step1Labels := by
      have ha : raw1134step1 = raw1134step0 := by apply Matrix.ext; unfold raw1134step1 raw1134step0; decide +kernel
      have hl : raw1134step0Labels = labelEmbedding7 ∘ raw1134step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1134step0 raw1134step0Labels raw1134step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4349 node4349Labels := by rfl

theorem canonical1135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1135 raw1135Labels = mixedMoment B node927 node927Labels := by
  calc
    mixedMoment B raw1135 raw1135Labels = mixedMoment B raw1135step0 raw1135step0Labels := by
      have ha : raw1135step0 = (fun i j => raw1135 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1135step0 raw1135; decide +kernel
      have hl : raw1135step0Labels = raw1135Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1135 raw1135Labels permutation32 permutation4
    _ = mixedMoment B node927 node927Labels := by rfl

theorem canonical1136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1136 raw1136Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw1136 raw1136Labels = mixedMoment B raw1136step0 raw1136step0Labels := by
      have ha : raw1136step0 = (fun i j => raw1136 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1136step0 raw1136; decide +kernel
      have hl : raw1136step0Labels = raw1136Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1136 raw1136Labels permutation32 permutation6
    mixedMoment B raw1136step0 raw1136step0Labels = mixedMoment B raw1136step1 raw1136step1Labels := by
      have ha : raw1136step1 = -raw1136step0 := by apply Matrix.ext; change ∀ i j, raw1136step1 i j = -(raw1136step0 i j); unfold raw1136step1 raw1136step0; decide +kernel
      have hl : raw1136step1Labels = raw1136step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1136step1 raw1136step1Labels = mixedMoment B raw1136step2 raw1136step2Labels := by
      have ha : raw1136step2 = raw1136step1 := by apply Matrix.ext; unfold raw1136step2 raw1136step1; decide +kernel
      have hl : raw1136step1Labels = labelEmbedding1 ∘ raw1136step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1136step1 raw1136step1Labels raw1136step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11506 raw11506Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw11506 raw11506Labels = mixedMoment B raw11506step0 raw11506step0Labels := by
      have hz : ∀ j, raw11506 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11506step0 = (fun i j => raw11506 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11506step0 raw11506; decide +kernel
      have hl : raw11506step0Labels = raw11506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11506 raw11506Labels permutation434 hz
    mixedMoment B raw11506step0 raw11506step0Labels = mixedMoment B raw11506step1 raw11506step1Labels := by
      have hz : ∀ j, raw11506step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11506step1 = (fun i j => raw11506step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11506step1 raw11506step0; decide +kernel
      have hl : raw11506step1Labels = raw11506step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11506step0 raw11506step0Labels permutation80 hz
    _ = mixedMoment B node4499 node4499Labels := by rfl

theorem canonical11511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11511 raw11511Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw11511 raw11511Labels = mixedMoment B raw11511step0 raw11511step0Labels := by
      have hz : ∀ j, raw11511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11511step0 = (fun i j => raw11511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11511step0 raw11511; decide +kernel
      have hl : raw11511step0Labels = raw11511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11511 raw11511Labels permutation434 hz
    mixedMoment B raw11511step0 raw11511step0Labels = mixedMoment B raw11511step1 raw11511step1Labels := by
      have hz : ∀ j, raw11511step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11511step1 = (fun i j => raw11511step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11511step1 raw11511step0; decide +kernel
      have hl : raw11511step1Labels = raw11511step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11511step0 raw11511step0Labels permutation56 hz
    _ = mixedMoment B node4499 node4499Labels := by rfl

theorem canonical11516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11516 raw11516Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw11516 raw11516Labels = mixedMoment B raw11516step0 raw11516step0Labels := by
      have hz : ∀ j, raw11516 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11516step0 = (fun i j => raw11516 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11516step0 raw11516; decide +kernel
      have hl : raw11516step0Labels = raw11516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11516 raw11516Labels permutation346 hz
    mixedMoment B raw11516step0 raw11516step0Labels = mixedMoment B raw11516step1 raw11516step1Labels := by
      have hz : ∀ j, raw11516step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11516step1 = (fun i j => raw11516step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11516step1 raw11516step0; decide +kernel
      have hl : raw11516step1Labels = raw11516step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11516step0 raw11516step0Labels permutation56 hz
    _ = mixedMoment B node4499 node4499Labels := by rfl

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

theorem canonical1158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1158 raw1158Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw1158 raw1158Labels = mixedMoment B raw1158step0 raw1158step0Labels := by
      have ha : raw1158step0 = (fun i j => raw1158 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1158step0 raw1158; decide +kernel
      have hl : raw1158step0Labels = raw1158Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1158 raw1158Labels permutation8 permutation4
    mixedMoment B raw1158step0 raw1158step0Labels = mixedMoment B raw1158step1 raw1158step1Labels := by
      have ha : raw1158step1 = raw1158step0 := by apply Matrix.ext; unfold raw1158step1 raw1158step0; decide +kernel
      have hl : raw1158step0Labels = labelEmbedding7 ∘ raw1158step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1158step0 raw1158step0Labels raw1158step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4360 node4360Labels := by rfl

theorem canonical1159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1159 raw1159Labels = mixedMoment B node938 node938Labels := by
  calc
    mixedMoment B raw1159 raw1159Labels = mixedMoment B raw1159step0 raw1159step0Labels := by
      have ha : raw1159step0 = (fun i j => raw1159 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1159step0 raw1159; decide +kernel
      have hl : raw1159step0Labels = raw1159Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1159 raw1159Labels permutation8 permutation4
    _ = mixedMoment B node938 node938Labels := by rfl

theorem canonical1160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1160 raw1160Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw1160 raw1160Labels = mixedMoment B raw1160step0 raw1160step0Labels := by
      have ha : raw1160step0 = (fun i j => raw1160 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1160step0 raw1160; decide +kernel
      have hl : raw1160step0Labels = raw1160Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1160 raw1160Labels permutation8 permutation6
    mixedMoment B raw1160step0 raw1160step0Labels = mixedMoment B raw1160step1 raw1160step1Labels := by
      have ha : raw1160step1 = -raw1160step0 := by apply Matrix.ext; change ∀ i j, raw1160step1 i j = -(raw1160step0 i j); unfold raw1160step1 raw1160step0; decide +kernel
      have hl : raw1160step1Labels = raw1160step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1160step1 raw1160step1Labels = mixedMoment B raw1160step2 raw1160step2Labels := by
      have ha : raw1160step2 = raw1160step1 := by apply Matrix.ext; unfold raw1160step2 raw1160step1; decide +kernel
      have hl : raw1160step1Labels = labelEmbedding1 ∘ raw1160step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1160step1 raw1160step1Labels raw1160step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1693 node1693Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11522 raw11522Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw11522 raw11522Labels = mixedMoment B raw11522step0 raw11522step0Labels := by
      have hz : ∀ j, raw11522 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11522step0 = (fun i j => raw11522 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11522step0 raw11522; decide +kernel
      have hl : raw11522step0Labels = raw11522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11522 raw11522Labels permutation434 hz
    mixedMoment B raw11522step0 raw11522step0Labels = mixedMoment B raw11522step1 raw11522step1Labels := by
      have hz : ∀ j, raw11522step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11522step1 = (fun i j => raw11522step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11522step1 raw11522step0; decide +kernel
      have hl : raw11522step1Labels = raw11522step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11522step0 raw11522step0Labels permutation80 hz
    mixedMoment B raw11522step1 raw11522step1Labels = mixedMoment B raw11522step2 raw11522step2Labels := by
      have ha : raw11522step2 = (fun i j => raw11522step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11522step2 raw11522step1; decide +kernel
      have hl : raw11522step2Labels = raw11522step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11522step1 raw11522step1Labels permutation9 permutation2
    _ = mixedMoment B node4846 node4846Labels := by rfl

theorem canonical11523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11523 raw11523Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw11523 raw11523Labels = mixedMoment B raw11523step0 raw11523step0Labels := by
      have hz : ∀ j, raw11523 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11523step0 = (fun i j => raw11523 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11523step0 raw11523; decide +kernel
      have hl : raw11523step0Labels = raw11523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11523 raw11523Labels permutation434 hz
    mixedMoment B raw11523step0 raw11523step0Labels = mixedMoment B raw11523step1 raw11523step1Labels := by
      have hz : ∀ j, raw11523step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11523step1 = (fun i j => raw11523step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11523step1 raw11523step0; decide +kernel
      have hl : raw11523step1Labels = raw11523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11523step0 raw11523step0Labels permutation56 hz
    mixedMoment B raw11523step1 raw11523step1Labels = mixedMoment B raw11523step2 raw11523step2Labels := by
      have ha : raw11523step2 = (fun i j => raw11523step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11523step2 raw11523step1; decide +kernel
      have hl : raw11523step2Labels = raw11523step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11523step1 raw11523step1Labels permutation9 permutation2
    _ = mixedMoment B node4846 node4846Labels := by rfl

theorem canonical11524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11524 raw11524Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw11524 raw11524Labels = mixedMoment B raw11524step0 raw11524step0Labels := by
      have hz : ∀ j, raw11524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11524step0 = (fun i j => raw11524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11524step0 raw11524; decide +kernel
      have hl : raw11524step0Labels = raw11524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11524 raw11524Labels permutation346 hz
    mixedMoment B raw11524step0 raw11524step0Labels = mixedMoment B raw11524step1 raw11524step1Labels := by
      have hz : ∀ j, raw11524step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11524step1 = (fun i j => raw11524step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11524step1 raw11524step0; decide +kernel
      have hl : raw11524step1Labels = raw11524step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11524step0 raw11524step0Labels permutation56 hz
    mixedMoment B raw11524step1 raw11524step1Labels = mixedMoment B raw11524step2 raw11524step2Labels := by
      have ha : raw11524step2 = (fun i j => raw11524step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11524step2 raw11524step1; decide +kernel
      have hl : raw11524step2Labels = raw11524step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11524step1 raw11524step1Labels permutation9 permutation2
    _ = mixedMoment B node4846 node4846Labels := by rfl

theorem canonical11525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11525 raw11525Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw11525 raw11525Labels = mixedMoment B raw11525step0 raw11525step0Labels := by
      have hz : ∀ j, raw11525 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11525step0 = (fun i j => raw11525 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11525step0 raw11525; decide +kernel
      have hl : raw11525step0Labels = raw11525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11525 raw11525Labels permutation434 hz
    mixedMoment B raw11525step0 raw11525step0Labels = mixedMoment B raw11525step1 raw11525step1Labels := by
      have hz : ∀ j, raw11525step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11525step1 = (fun i j => raw11525step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11525step1 raw11525step0; decide +kernel
      have hl : raw11525step1Labels = raw11525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11525step0 raw11525step0Labels permutation80 hz
    mixedMoment B raw11525step1 raw11525step1Labels = mixedMoment B raw11525step2 raw11525step2Labels := by
      have hz : ∀ j, raw11525step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw11525step2 = (fun i j => raw11525step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw11525step2 raw11525step1; decide +kernel
      have hl : raw11525step2Labels = raw11525step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11525step1 raw11525step1Labels permutation14 hz
    mixedMoment B raw11525step2 raw11525step2Labels = mixedMoment B raw11525step3 raw11525step3Labels := by
      have hz : ∀ i, raw11525step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw11525step3 = (fun i j => raw11525step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw11525step3 raw11525step2; decide +kernel
      have hl : raw11525step3Labels = (fun j => raw11525step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw11525step2 raw11525step2Labels permutation4 hz
    mixedMoment B raw11525step3 raw11525step3Labels = mixedMoment B raw11525step4 raw11525step4Labels := by
      have ha : raw11525step4 = (fun i j => raw11525step3 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw11525step4 raw11525step3; decide +kernel
      have hl : raw11525step4Labels = raw11525step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11525step3 raw11525step3Labels permutation3 permutation0
    mixedMoment B raw11525step4 raw11525step4Labels = mixedMoment B raw11525step5 raw11525step5Labels := by
      have ha : raw11525step5 = raw11525step4 := by apply Matrix.ext; unfold raw11525step5 raw11525step4; decide +kernel
      have hl : raw11525step4Labels = labelEmbedding2 ∘ raw11525step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11525step4 raw11525step4Labels raw11525step5Labels labelEmbedding2 hl
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical11526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11526 raw11526Labels = mixedMoment B node4507 node4507Labels := by
  calc
    mixedMoment B raw11526 raw11526Labels = mixedMoment B raw11526step0 raw11526step0Labels := by
      have hz : ∀ j, raw11526 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11526step0 = (fun i j => raw11526 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11526step0 raw11526; decide +kernel
      have hl : raw11526step0Labels = raw11526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11526 raw11526Labels permutation434 hz
    mixedMoment B raw11526step0 raw11526step0Labels = mixedMoment B raw11526step1 raw11526step1Labels := by
      have hz : ∀ j, raw11526step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11526step1 = (fun i j => raw11526step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11526step1 raw11526step0; decide +kernel
      have hl : raw11526step1Labels = raw11526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11526step0 raw11526step0Labels permutation80 hz
    mixedMoment B raw11526step1 raw11526step1Labels = mixedMoment B raw11526step2 raw11526step2Labels := by
      have hz : ∀ j, raw11526step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw11526step2 = (fun i j => raw11526step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw11526step2 raw11526step1; decide +kernel
      have hl : raw11526step2Labels = raw11526step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11526step1 raw11526step1Labels permutation14 hz
    _ = mixedMoment B node4507 node4507Labels := by rfl

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

theorem singleton4180 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4180 node4180Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node608 node608Labels + mixedMoment B node1519 node1519Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw816 singletonSmall4180
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4180) = raw816Labels := by decide +kernel
  rw [hl, canonical816 B hB] at h
  have hc0 : mixedMoment B raw816 (Fin.cases (0 : Fin 2) singletonSmall4180) =
      mixedMoment B node608 node608Labels := by
    have ha : raw816 = raw817 := by apply Matrix.ext; unfold raw816 raw817; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4180 = raw817Labels := by decide +kernel
    rw [ha, hj, canonical817 B hB]
  have hc1 : mixedMoment B raw816 (Fin.cases (1 : Fin 2) singletonSmall4180) =
      mixedMoment B node1519 node1519Labels := by
    have ha : raw816 = raw818 := by apply Matrix.ext; unfold raw816 raw818; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4180 = raw818Labels := by decide +kernel
    rw [ha, hj, canonical818 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4191 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4191 node4191Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node619 node619Labels + mixedMoment B node1538 node1538Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw840 singletonSmall4191
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4191) = raw840Labels := by decide +kernel
  rw [hl, canonical840 B hB] at h
  have hc0 : mixedMoment B raw840 (Fin.cases (0 : Fin 2) singletonSmall4191) =
      mixedMoment B node619 node619Labels := by
    have ha : raw840 = raw841 := by apply Matrix.ext; unfold raw840 raw841; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4191 = raw841Labels := by decide +kernel
    rw [ha, hj, canonical841 B hB]
  have hc1 : mixedMoment B raw840 (Fin.cases (1 : Fin 2) singletonSmall4191) =
      mixedMoment B node1538 node1538Labels := by
    have ha : raw840 = raw842 := by apply Matrix.ext; unfold raw840 raw842; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4191 = raw842Labels := by decide +kernel
    rw [ha, hj, canonical842 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4192 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4192 node4192Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node620 node620Labels + mixedMoment B node1539 node1539Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw843 singletonSmall4192
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4192) = raw843Labels := by decide +kernel
  rw [hl, canonical843 B hB] at h
  have hc0 : mixedMoment B raw843 (Fin.cases (0 : Fin 2) singletonSmall4192) =
      mixedMoment B node620 node620Labels := by
    have ha : raw843 = raw844 := by apply Matrix.ext; unfold raw843 raw844; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4192 = raw844Labels := by decide +kernel
    rw [ha, hj, canonical844 B hB]
  have hc1 : mixedMoment B raw843 (Fin.cases (1 : Fin 2) singletonSmall4192) =
      mixedMoment B node1539 node1539Labels := by
    have ha : raw843 = raw845 := by apply Matrix.ext; unfold raw843 raw845; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4192 = raw845Labels := by decide +kernel
    rw [ha, hj, canonical845 B hB]
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

theorem singleton4349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4349 node4349Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node927 node927Labels + mixedMoment B node1675 node1675Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1134 singletonSmall4349
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4349) = raw1134Labels := by decide +kernel
  rw [hl, canonical1134 B hB] at h
  have hc0 : mixedMoment B raw1134 (Fin.cases (0 : Fin 2) singletonSmall4349) =
      mixedMoment B node927 node927Labels := by
    have ha : raw1134 = raw1135 := by apply Matrix.ext; unfold raw1134 raw1135; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4349 = raw1135Labels := by decide +kernel
    rw [ha, hj, canonical1135 B hB]
  have hc1 : mixedMoment B raw1134 (Fin.cases (1 : Fin 2) singletonSmall4349) =
      mixedMoment B node1675 node1675Labels := by
    have ha : raw1134 = raw1136 := by apply Matrix.ext; unfold raw1134 raw1136; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4349 = raw1136Labels := by decide +kernel
    rw [ha, hj, canonical1136 B hB]
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

theorem singleton4360 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4360 node4360Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node938 node938Labels + mixedMoment B node1693 node1693Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1158 singletonSmall4360
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4360) = raw1158Labels := by decide +kernel
  rw [hl, canonical1158 B hB] at h
  have hc0 : mixedMoment B raw1158 (Fin.cases (0 : Fin 2) singletonSmall4360) =
      mixedMoment B node938 node938Labels := by
    have ha : raw1158 = raw1159 := by apply Matrix.ext; unfold raw1158 raw1159; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4360 = raw1159Labels := by decide +kernel
    rw [ha, hj, canonical1159 B hB]
  have hc1 : mixedMoment B raw1158 (Fin.cases (1 : Fin 2) singletonSmall4360) =
      mixedMoment B node1693 node1693Labels := by
    have ha : raw1158 = raw1160 := by apply Matrix.ext; unfold raw1158 raw1160; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4360 = raw1160Labels := by decide +kernel
    rw [ha, hj, canonical1160 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4499 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4499 node4499Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1083 node1083Labels + mixedMoment B node1728 node1728Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1299 singletonSmall4499
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4499) = raw1299Labels := by decide +kernel
  rw [hl, canonical1299 B hB] at h
  have hc0 : mixedMoment B raw1299 (Fin.cases (0 : Fin 2) singletonSmall4499) =
      mixedMoment B node1083 node1083Labels := by
    have ha : raw1299 = raw1300 := by apply Matrix.ext; unfold raw1299 raw1300; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4499 = raw1300Labels := by decide +kernel
    rw [ha, hj, canonical1300 B hB]
  have hc1 : mixedMoment B raw1299 (Fin.cases (1 : Fin 2) singletonSmall4499) =
      mixedMoment B node1728 node1728Labels := by
    have ha : raw1299 = raw1301 := by apply Matrix.ext; unfold raw1299 raw1301; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4499 = raw1301Labels := by decide +kernel
    rw [ha, hj, canonical1301 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4507 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4507 node4507Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1091 node1091Labels + mixedMoment B node1756 node1756Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1305 singletonSmall4507
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4507) = raw1305Labels := by decide +kernel
  rw [hl, canonical1305 B hB] at h
  have hc0 : mixedMoment B raw1305 (Fin.cases (0 : Fin 2) singletonSmall4507) =
      mixedMoment B node1091 node1091Labels := by
    have ha : raw1305 = raw1306 := by apply Matrix.ext; unfold raw1305 raw1306; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4507 = raw1306Labels := by decide +kernel
    rw [ha, hj, canonical1306 B hB]
  have hc1 : mixedMoment B raw1305 (Fin.cases (1 : Fin 2) singletonSmall4507) =
      mixedMoment B node1756 node1756Labels := by
    have ha : raw1305 = raw1307 := by apply Matrix.ext; unfold raw1305 raw1307; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4507 = raw1307Labels := by decide +kernel
    rw [ha, hj, canonical1307 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node927 node927Labels = Sparse.eval nodeValue927 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 927) = mixedMoment B node927 node927Labels := rfl
  simpa [nodeValue927, Sparse.eval] using hc.symm

theorem sound938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node938 node938Labels = Sparse.eval nodeValue938 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 938) = mixedMoment B node938 node938Labels := rfl
  simpa [nodeValue938, Sparse.eval] using hc.symm

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

theorem sound1083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1083 node1083Labels = Sparse.eval nodeValue1083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1083) = mixedMoment B node1083 node1083Labels := rfl
  simpa [nodeValue1083, Sparse.eval] using hc.symm

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

theorem sound1091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1091 node1091Labels = Sparse.eval nodeValue1091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1091) = mixedMoment B node1091 node1091Labels := rfl
  simpa [nodeValue1091, Sparse.eval] using hc.symm

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

theorem sound1519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1519 node1519Labels = Sparse.eval nodeValue1519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1519) = mixedMoment B node1519 node1519Labels := rfl
  simpa [nodeValue1519, Sparse.eval] using hc.symm

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

theorem sound1538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1538 node1538Labels = Sparse.eval nodeValue1538 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1538) = mixedMoment B node1538 node1538Labels := rfl
  simpa [nodeValue1538, Sparse.eval] using hc.symm

theorem sound1539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1539 node1539Labels = Sparse.eval nodeValue1539 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1539) = mixedMoment B node1539 node1539Labels := rfl
  simpa [nodeValue1539, Sparse.eval] using hc.symm

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

theorem sound1675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1675 node1675Labels = Sparse.eval nodeValue1675 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1675) = mixedMoment B node1675 node1675Labels := rfl
  simpa [nodeValue1675, Sparse.eval] using hc.symm

theorem sound1693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1693 node1693Labels = Sparse.eval nodeValue1693 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1693) = mixedMoment B node1693 node1693Labels := rfl
  simpa [nodeValue1693, Sparse.eval] using hc.symm

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

theorem sound1728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1728 node1728Labels = Sparse.eval nodeValue1728 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1728) = mixedMoment B node1728 node1728Labels := rfl
  simpa [nodeValue1728, Sparse.eval] using hc.symm

theorem sound1756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1756 node1756Labels = Sparse.eval nodeValue1756 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1756) = mixedMoment B node1756 node1756Labels := rfl
  simpa [nodeValue1756, Sparse.eval] using hc.symm

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

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

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

theorem sound608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node608 node608Labels = Sparse.eval nodeValue608 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 608) = mixedMoment B node608 node608Labels := rfl
  simpa [nodeValue608, Sparse.eval] using hc.symm

theorem sound619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node619 node619Labels = Sparse.eval nodeValue619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 619) = mixedMoment B node619 node619Labels := rfl
  simpa [nodeValue619, Sparse.eval] using hc.symm

theorem sound620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node620 node620Labels = Sparse.eval nodeValue620 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 620) = mixedMoment B node620 node620Labels := rfl
  simpa [nodeValue620, Sparse.eval] using hc.symm

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

theorem sound4180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4180 node4180Labels = Sparse.eval nodeValue4180 (mixedVector B) := by
  have h := singleton4180 B _hB
  rw [sound608 B _hB _hF, sound1519 B _hB _hF] at h
  norm_num [nodeValue4180, nodeValue608, nodeValue1519, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4191 node4191Labels = Sparse.eval nodeValue4191 (mixedVector B) := by
  have h := singleton4191 B _hB
  rw [sound619 B _hB _hF, sound1538 B _hB _hF] at h
  norm_num [nodeValue4191, nodeValue619, nodeValue1538, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4192 node4192Labels = Sparse.eval nodeValue4192 (mixedVector B) := by
  have h := singleton4192 B _hB
  rw [sound620 B _hB _hF, sound1539 B _hB _hF] at h
  norm_num [nodeValue4192, nodeValue620, nodeValue1539, Sparse.eval] at h ⊢
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

theorem sound4349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4349 node4349Labels = Sparse.eval nodeValue4349 (mixedVector B) := by
  have h := singleton4349 B _hB
  rw [sound927 B _hB _hF, sound1675 B _hB _hF] at h
  norm_num [nodeValue4349, nodeValue927, nodeValue1675, Sparse.eval] at h ⊢
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

theorem sound4360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4360 node4360Labels = Sparse.eval nodeValue4360 (mixedVector B) := by
  have h := singleton4360 B _hB
  rw [sound938 B _hB _hF, sound1693 B _hB _hF] at h
  norm_num [nodeValue4360, nodeValue938, nodeValue1693, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4498 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4498 node4498Labels = 0 := by
  exact mixedMoment_order_one B hB node4498 node4498Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4505 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4505 node4505Labels = 0 := by
  exact mixedMoment_order_one B hB node4505 node4505Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4498 node4498Labels = Sparse.eval nodeValue4498 (mixedVector B) := by
  simpa only [nodeValue4498, Sparse.eval_nil] using zero4498 B _hB _hF

theorem sound4499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4499 node4499Labels = Sparse.eval nodeValue4499 (mixedVector B) := by
  have h := singleton4499 B _hB
  rw [sound1083 B _hB _hF, sound1728 B _hB _hF] at h
  norm_num [nodeValue4499, nodeValue1083, nodeValue1728, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4505 node4505Labels = Sparse.eval nodeValue4505 (mixedVector B) := by
  simpa only [nodeValue4505, Sparse.eval_nil] using zero4505 B _hB _hF

theorem sound4507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4507 node4507Labels = Sparse.eval nodeValue4507 (mixedVector B) := by
  have h := singleton4507 B _hB
  rw [sound1091 B _hB _hF, sound1756 B _hB _hF] at h
  norm_num [nodeValue4507, nodeValue1091, nodeValue1756, Sparse.eval] at h ⊢
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

theorem zero4846 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4846 node4846Labels = 0 := by
  exact mixedMoment_order_one B hB node4846 node4846Labels 1
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

theorem sound4846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4846 node4846Labels = Sparse.eval nodeValue4846 (mixedVector B) := by
  simpa only [nodeValue4846, Sparse.eval_nil] using zero4846 B _hB _hF

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

theorem zero4901 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4901 node4901Labels = 0 := by
  exact mixedMoment_order_one B hB node4901 node4901Labels 1
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

theorem sound4901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4901 node4901Labels = Sparse.eval nodeValue4901 (mixedVector B) := by
  simpa only [nodeValue4901, Sparse.eval_nil] using zero4901 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources48
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1550 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1550 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1550 + difference 0 1) (sourceB1550 + difference 1 0) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA1550 + difference 0 1) (sourceB1550 + difference 1 0) sourceC1550) = raw11522 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw11522; decide +kernel
    rw [ha]
    exact (canonical11522 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1550 + difference 0 2) (sourceB1550 + difference 2 0) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA1550 + difference 0 2) (sourceB1550 + difference 2 0) sourceC1550) = raw11523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw11523; decide +kernel
    rw [ha]
    exact (canonical11523 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1550 + difference 0 3) (sourceB1550 + difference 3 0) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA1550 + difference 0 3) (sourceB1550 + difference 3 0) sourceC1550) = raw11524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw11524; decide +kernel
    rw [ha]
    exact (canonical11524 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1550 + difference 0 4) (sourceB1550 + difference 4 0) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4901) := by
    have ha : (tripleCharges (sourceA1550 + difference 0 4) (sourceB1550 + difference 4 0) sourceC1550) = raw21634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw21634; decide +kernel
    rw [ha]
    exact (canonical21634 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1550 + difference 0 5) (sourceB1550 + difference 5 0) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1550 + difference 0 5) (sourceB1550 + difference 5 0) sourceC1550) = raw11525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw11525; decide +kernel
    rw [ha]
    exact (canonical11525 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1550 + difference 1 0) (sourceB1550 + difference 0 1) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4180) := by
    have ha : (tripleCharges (sourceA1550 + difference 1 0) (sourceB1550 + difference 0 1) sourceC1550) = raw23518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23518; decide +kernel
    rw [ha]
    exact (canonical23518 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1550 + difference 1 2) (sourceB1550 + difference 2 1) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1550 + difference 1 2) (sourceB1550 + difference 2 1) sourceC1550) = raw23519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23519; decide +kernel
    rw [ha]
    exact (canonical23519 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1550 + difference 1 3) (sourceB1550 + difference 3 1) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1550 + difference 1 3) (sourceB1550 + difference 3 1) sourceC1550) = raw23520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23520; decide +kernel
    rw [ha]
    exact (canonical23520 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1550 + difference 1 4) (sourceB1550 + difference 4 1) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1550 + difference 1 4) (sourceB1550 + difference 4 1) sourceC1550) = raw11506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw11506; decide +kernel
    rw [ha]
    exact (canonical11506 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1550 + difference 1 5) (sourceB1550 + difference 5 1) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1550 + difference 1 5) (sourceB1550 + difference 5 1) sourceC1550) = raw23521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23521; decide +kernel
    rw [ha]
    exact (canonical23521 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1550 + difference 2 0) (sourceB1550 + difference 0 2) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4180) := by
    have ha : (tripleCharges (sourceA1550 + difference 2 0) (sourceB1550 + difference 0 2) sourceC1550) = raw23522 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23522; decide +kernel
    rw [ha]
    exact (canonical23522 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1550 + difference 2 1) (sourceB1550 + difference 1 2) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1550 + difference 2 1) (sourceB1550 + difference 1 2) sourceC1550) = raw23523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23523; decide +kernel
    rw [ha]
    exact (canonical23523 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1550 + difference 2 3) (sourceB1550 + difference 3 2) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1550 + difference 2 3) (sourceB1550 + difference 3 2) sourceC1550) = raw23524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23524; decide +kernel
    rw [ha]
    exact (canonical23524 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1550 + difference 2 4) (sourceB1550 + difference 4 2) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1550 + difference 2 4) (sourceB1550 + difference 4 2) sourceC1550) = raw11511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw11511; decide +kernel
    rw [ha]
    exact (canonical11511 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1550 + difference 2 5) (sourceB1550 + difference 5 2) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1550 + difference 2 5) (sourceB1550 + difference 5 2) sourceC1550) = raw23525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23525; decide +kernel
    rw [ha]
    exact (canonical23525 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1550 + difference 3 0) (sourceB1550 + difference 0 3) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4180) := by
    have ha : (tripleCharges (sourceA1550 + difference 3 0) (sourceB1550 + difference 0 3) sourceC1550) = raw23526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23526; decide +kernel
    rw [ha]
    exact (canonical23526 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1550 + difference 3 1) (sourceB1550 + difference 1 3) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1550 + difference 3 1) (sourceB1550 + difference 1 3) sourceC1550) = raw23527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23527; decide +kernel
    rw [ha]
    exact (canonical23527 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1550 + difference 3 2) (sourceB1550 + difference 2 3) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1550 + difference 3 2) (sourceB1550 + difference 2 3) sourceC1550) = raw23528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23528; decide +kernel
    rw [ha]
    exact (canonical23528 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1550 + difference 3 4) (sourceB1550 + difference 4 3) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1550 + difference 3 4) (sourceB1550 + difference 4 3) sourceC1550) = raw11516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw11516; decide +kernel
    rw [ha]
    exact (canonical11516 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1550 + difference 3 5) (sourceB1550 + difference 5 3) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1550 + difference 3 5) (sourceB1550 + difference 5 3) sourceC1550) = raw23529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23529; decide +kernel
    rw [ha]
    exact (canonical23529 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1550 + difference 4 0) (sourceB1550 + difference 0 4) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4191) := by
    have ha : (tripleCharges (sourceA1550 + difference 4 0) (sourceB1550 + difference 0 4) sourceC1550) = raw23530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23530; decide +kernel
    rw [ha]
    exact (canonical23530 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1550 + difference 4 1) (sourceB1550 + difference 1 4) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA1550 + difference 4 1) (sourceB1550 + difference 1 4) sourceC1550) = raw23531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23531; decide +kernel
    rw [ha]
    exact (canonical23531 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1550 + difference 4 2) (sourceB1550 + difference 2 4) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA1550 + difference 4 2) (sourceB1550 + difference 2 4) sourceC1550) = raw23532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23532; decide +kernel
    rw [ha]
    exact (canonical23532 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1550 + difference 4 3) (sourceB1550 + difference 3 4) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA1550 + difference 4 3) (sourceB1550 + difference 3 4) sourceC1550) = raw23533 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23533; decide +kernel
    rw [ha]
    exact (canonical23533 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1550 + difference 4 5) (sourceB1550 + difference 5 4) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA1550 + difference 4 5) (sourceB1550 + difference 5 4) sourceC1550) = raw23534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23534; decide +kernel
    rw [ha]
    exact (canonical23534 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1550 + difference 5 0) (sourceB1550 + difference 0 5) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4192) := by
    have ha : (tripleCharges (sourceA1550 + difference 5 0) (sourceB1550 + difference 0 5) sourceC1550) = raw21647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw21647; decide +kernel
    rw [ha]
    exact (canonical21647 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1550 + difference 5 1) (sourceB1550 + difference 1 5) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4361) := by
    have ha : (tripleCharges (sourceA1550 + difference 5 1) (sourceB1550 + difference 1 5) sourceC1550) = raw21648 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw21648; decide +kernel
    rw [ha]
    exact (canonical21648 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1550 + difference 5 2) (sourceB1550 + difference 2 5) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4361) := by
    have ha : (tripleCharges (sourceA1550 + difference 5 2) (sourceB1550 + difference 2 5) sourceC1550) = raw21649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw21649; decide +kernel
    rw [ha]
    exact (canonical21649 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1550 + difference 5 3) (sourceB1550 + difference 3 5) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4361) := by
    have ha : (tripleCharges (sourceA1550 + difference 5 3) (sourceB1550 + difference 3 5) sourceC1550) = raw21650 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw21650; decide +kernel
    rw [ha]
    exact (canonical21650 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1550 + difference 5 4) (sourceB1550 + difference 4 5) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4507) := by
    have ha : (tripleCharges (sourceA1550 + difference 5 4) (sourceB1550 + difference 4 5) sourceC1550) = raw11526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw11526; decide +kernel
    rw [ha]
    exact (canonical11526 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1550 sourceB1550 sourceC1550
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1550, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1321 : Integer.Sparse.reindex keyMap MixedData.row1321 = numericRow1321 := by decide +kernel

theorem numericCheck1321 (x : Master → ℝ) : Integer.Sparse.eval numericRow1321 x =
    (4 : ℝ) * reducedSource1321 x := by
  norm_num [numericRow1321, reducedSource1321, Integer.Sparse.eval, Sparse.eval, nodeValue4084, nodeValue4180, nodeValue4191, nodeValue4192, nodeValue4349, nodeValue4360, nodeValue4361, nodeValue4498, nodeValue4499, nodeValue4505, nodeValue4507, nodeValue4846, nodeValue4901]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1321 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1321 (mixedVector B) = 0 := by
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4180 : mixedVector B (Sum.inr 4180) = Sparse.eval nodeValue4180 (mixedVector B) := by
    change mixedMoment B node4180 node4180Labels = _
    exact sound4180 B hB hF
  have h4191 : mixedVector B (Sum.inr 4191) = Sparse.eval nodeValue4191 (mixedVector B) := by
    change mixedMoment B node4191 node4191Labels = _
    exact sound4191 B hB hF
  have h4192 : mixedVector B (Sum.inr 4192) = Sparse.eval nodeValue4192 (mixedVector B) := by
    change mixedMoment B node4192 node4192Labels = _
    exact sound4192 B hB hF
  have h4349 : mixedVector B (Sum.inr 4349) = Sparse.eval nodeValue4349 (mixedVector B) := by
    change mixedMoment B node4349 node4349Labels = _
    exact sound4349 B hB hF
  have h4360 : mixedVector B (Sum.inr 4360) = Sparse.eval nodeValue4360 (mixedVector B) := by
    change mixedMoment B node4360 node4360Labels = _
    exact sound4360 B hB hF
  have h4361 : mixedVector B (Sum.inr 4361) = Sparse.eval nodeValue4361 (mixedVector B) := by
    change mixedMoment B node4361 node4361Labels = _
    exact sound4361 B hB hF
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
  have h4499 : mixedVector B (Sum.inr 4499) = Sparse.eval nodeValue4499 (mixedVector B) := by
    change mixedMoment B node4499 node4499Labels = _
    exact sound4499 B hB hF
  have h4505 : mixedVector B (Sum.inr 4505) = Sparse.eval nodeValue4505 (mixedVector B) := by
    change mixedMoment B node4505 node4505Labels = _
    exact sound4505 B hB hF
  have h4507 : mixedVector B (Sum.inr 4507) = Sparse.eval nodeValue4507 (mixedVector B) := by
    change mixedMoment B node4507 node4507Labels = _
    exact sound4507 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h4901 : mixedVector B (Sum.inr 4901) = Sparse.eval nodeValue4901 (mixedVector B) := by
    change mixedMoment B node4901 node4901Labels = _
    exact sound4901 B hB hF
  simpa only [sourceForm1550, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4084, h4180, h4191, h4192, h4349, h4360, h4361, h4498, h4499, h4505, h4507, h4846, h4901, reducedSource1321] using sourceEq1550 B hB

theorem rowSound1321_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1321 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1321, numericCheck1321, reducedZero1321 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1321_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1321_e_oai
