-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1335_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T20:43:32.893303+00:00
-- url     : https://prove2.me/submissions/67895aef-ab63-41f0-88d4-91b82b01dc2b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E118
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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical185
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23694 raw23694Labels = mixedMoment B node4491 node4491Labels := by
  calc
    mixedMoment B raw23694 raw23694Labels = mixedMoment B raw23694step0 raw23694step0Labels := by
      have hz : ∀ j, raw23694 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23694step0 = (fun i j => raw23694 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23694step0 raw23694; decide +kernel
      have hl : raw23694step0Labels = raw23694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23694 raw23694Labels permutation434 hz
    mixedMoment B raw23694step0 raw23694step0Labels = mixedMoment B raw23694step1 raw23694step1Labels := by
      have hz : ∀ j, raw23694step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23694step1 = (fun i j => raw23694step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23694step1 raw23694step0; decide +kernel
      have hl : raw23694step1Labels = raw23694step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23694step0 raw23694step0Labels permutation80 hz
    mixedMoment B raw23694step1 raw23694step1Labels = mixedMoment B raw23694step2 raw23694step2Labels := by
      have ha : raw23694step2 = (fun i j => raw23694step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23694step2 raw23694step1; decide +kernel
      have hl : raw23694step2Labels = raw23694step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23694step1 raw23694step1Labels permutation9 permutation7
    mixedMoment B raw23694step2 raw23694step2Labels = mixedMoment B raw23694step3 raw23694step3Labels := by
      have ha : raw23694step3 = -raw23694step2 := by apply Matrix.ext; change ∀ i j, raw23694step3 i j = -(raw23694step2 i j); unfold raw23694step3 raw23694step2; decide +kernel
      have hl : raw23694step3Labels = raw23694step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23694step3 raw23694step3Labels = mixedMoment B raw23694step4 raw23694step4Labels := by
      have ha : raw23694step4 = raw23694step3 := by apply Matrix.ext; unfold raw23694step4 raw23694step3; decide +kernel
      have hl : raw23694step3Labels = labelEmbedding10 ∘ raw23694step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23694step3 raw23694step3Labels raw23694step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4491 node4491Labels := by rfl

theorem canonical23695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23695 raw23695Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw23695 raw23695Labels = mixedMoment B raw23695step0 raw23695step0Labels := by
      have hz : ∀ j, raw23695 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23695step0 = (fun i j => raw23695 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23695step0 raw23695; decide +kernel
      have hl : raw23695step0Labels = raw23695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23695 raw23695Labels permutation434 hz
    mixedMoment B raw23695step0 raw23695step0Labels = mixedMoment B raw23695step1 raw23695step1Labels := by
      have ha : raw23695step1 = (fun i j => raw23695step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23695step1 raw23695step0; decide +kernel
      have hl : raw23695step1Labels = raw23695step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23695step0 raw23695step0Labels permutation39 permutation7
    mixedMoment B raw23695step1 raw23695step1Labels = mixedMoment B raw23695step2 raw23695step2Labels := by
      have ha : raw23695step2 = -raw23695step1 := by apply Matrix.ext; change ∀ i j, raw23695step2 i j = -(raw23695step1 i j); unfold raw23695step2 raw23695step1; decide +kernel
      have hl : raw23695step2Labels = raw23695step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23695step2 raw23695step2Labels = mixedMoment B raw23695step3 raw23695step3Labels := by
      have ha : raw23695step3 = raw23695step2 := by apply Matrix.ext; unfold raw23695step3 raw23695step2; decide +kernel
      have hl : raw23695step2Labels = labelEmbedding10 ∘ raw23695step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23695step2 raw23695step2Labels raw23695step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

theorem canonical23696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23696 raw23696Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw23696 raw23696Labels = mixedMoment B raw23696step0 raw23696step0Labels := by
      have hz : ∀ j, raw23696 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23696step0 = (fun i j => raw23696 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23696step0 raw23696; decide +kernel
      have hl : raw23696step0Labels = raw23696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23696 raw23696Labels permutation346 hz
    mixedMoment B raw23696step0 raw23696step0Labels = mixedMoment B raw23696step1 raw23696step1Labels := by
      have ha : raw23696step1 = (fun i j => raw23696step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23696step1 raw23696step0; decide +kernel
      have hl : raw23696step1Labels = raw23696step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23696step0 raw23696step0Labels permutation39 permutation7
    mixedMoment B raw23696step1 raw23696step1Labels = mixedMoment B raw23696step2 raw23696step2Labels := by
      have ha : raw23696step2 = -raw23696step1 := by apply Matrix.ext; change ∀ i j, raw23696step2 i j = -(raw23696step1 i j); unfold raw23696step2 raw23696step1; decide +kernel
      have hl : raw23696step2Labels = raw23696step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23696step2 raw23696step2Labels = mixedMoment B raw23696step3 raw23696step3Labels := by
      have ha : raw23696step3 = raw23696step2 := by apply Matrix.ext; unfold raw23696step3 raw23696step2; decide +kernel
      have hl : raw23696step2Labels = labelEmbedding10 ∘ raw23696step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23696step2 raw23696step2Labels raw23696step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

theorem canonical23697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23697 raw23697Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw23697 raw23697Labels = mixedMoment B raw23697step0 raw23697step0Labels := by
      have hz : ∀ j, raw23697 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23697step0 = (fun i j => raw23697 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23697step0 raw23697; decide +kernel
      have hl : raw23697step0Labels = raw23697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23697 raw23697Labels permutation434 hz
    mixedMoment B raw23697step0 raw23697step0Labels = mixedMoment B raw23697step1 raw23697step1Labels := by
      have hz : ∀ j, raw23697step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23697step1 = (fun i j => raw23697step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23697step1 raw23697step0; decide +kernel
      have hl : raw23697step1Labels = raw23697step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23697step0 raw23697step0Labels permutation80 hz
    mixedMoment B raw23697step1 raw23697step1Labels = mixedMoment B raw23697step2 raw23697step2Labels := by
      have ha : raw23697step2 = (fun i j => raw23697step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23697step2 raw23697step1; decide +kernel
      have hl : raw23697step2Labels = raw23697step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23697step1 raw23697step1Labels permutation9 permutation7
    mixedMoment B raw23697step2 raw23697step2Labels = mixedMoment B raw23697step3 raw23697step3Labels := by
      have ha : raw23697step3 = -raw23697step2 := by apply Matrix.ext; change ∀ i j, raw23697step3 i j = -(raw23697step2 i j); unfold raw23697step3 raw23697step2; decide +kernel
      have hl : raw23697step3Labels = raw23697step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23697step3 raw23697step3Labels = mixedMoment B raw23697step4 raw23697step4Labels := by
      have ha : raw23697step4 = raw23697step3 := by apply Matrix.ext; unfold raw23697step4 raw23697step3; decide +kernel
      have hl : raw23697step3Labels = labelEmbedding10 ∘ raw23697step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23697step3 raw23697step3Labels raw23697step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

theorem canonical23698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23698 raw23698Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw23698 raw23698Labels = mixedMoment B raw23698step0 raw23698step0Labels := by
      have hz : ∀ j, raw23698 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23698step0 = (fun i j => raw23698 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23698step0 raw23698; decide +kernel
      have hl : raw23698step0Labels = raw23698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23698 raw23698Labels permutation434 hz
    mixedMoment B raw23698step0 raw23698step0Labels = mixedMoment B raw23698step1 raw23698step1Labels := by
      have hz : ∀ j, raw23698step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23698step1 = (fun i j => raw23698step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23698step1 raw23698step0; decide +kernel
      have hl : raw23698step1Labels = raw23698step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23698step0 raw23698step0Labels permutation80 hz
    mixedMoment B raw23698step1 raw23698step1Labels = mixedMoment B raw23698step2 raw23698step2Labels := by
      have ha : raw23698step2 = (fun i j => raw23698step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23698step2 raw23698step1; decide +kernel
      have hl : raw23698step2Labels = raw23698step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23698step1 raw23698step1Labels permutation9 permutation7
    mixedMoment B raw23698step2 raw23698step2Labels = mixedMoment B raw23698step3 raw23698step3Labels := by
      have ha : raw23698step3 = -raw23698step2 := by apply Matrix.ext; change ∀ i j, raw23698step3 i j = -(raw23698step2 i j); unfold raw23698step3 raw23698step2; decide +kernel
      have hl : raw23698step3Labels = raw23698step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23698step3 raw23698step3Labels = mixedMoment B raw23698step4 raw23698step4Labels := by
      have ha : raw23698step4 = raw23698step3 := by apply Matrix.ext; unfold raw23698step4 raw23698step3; decide +kernel
      have hl : raw23698step3Labels = labelEmbedding10 ∘ raw23698step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23698step3 raw23698step3Labels raw23698step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4498 node4498Labels := by rfl

theorem canonical23699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23699 raw23699Labels = mixedMoment B node4130 node4130Labels := by
  calc
    mixedMoment B raw23699 raw23699Labels = mixedMoment B raw23699step0 raw23699step0Labels := by
      have hz : ∀ j, raw23699 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23699step0 = (fun i j => raw23699 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23699step0 raw23699; decide +kernel
      have hl : raw23699step0Labels = raw23699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23699 raw23699Labels permutation434 hz
    mixedMoment B raw23699step0 raw23699step0Labels = mixedMoment B raw23699step1 raw23699step1Labels := by
      have hz : ∀ j, raw23699step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23699step1 = (fun i j => raw23699step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23699step1 raw23699step0; decide +kernel
      have hl : raw23699step1Labels = raw23699step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23699step0 raw23699step0Labels permutation80 hz
    mixedMoment B raw23699step1 raw23699step1Labels = mixedMoment B raw23699step2 raw23699step2Labels := by
      have ha : raw23699step2 = (fun i j => raw23699step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23699step2 raw23699step1; decide +kernel
      have hl : raw23699step2Labels = raw23699step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23699step1 raw23699step1Labels permutation9 permutation2
    _ = mixedMoment B node4130 node4130Labels := by rfl

theorem canonical23700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23700 raw23700Labels = mixedMoment B node4221 node4221Labels := by
  calc
    mixedMoment B raw23700 raw23700Labels = mixedMoment B raw23700step0 raw23700step0Labels := by
      have hz : ∀ j, raw23700 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23700step0 = (fun i j => raw23700 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23700step0 raw23700; decide +kernel
      have hl : raw23700step0Labels = raw23700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23700 raw23700Labels permutation434 hz
    mixedMoment B raw23700step0 raw23700step0Labels = mixedMoment B raw23700step1 raw23700step1Labels := by
      have ha : raw23700step1 = (fun i j => raw23700step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23700step1 raw23700step0; decide +kernel
      have hl : raw23700step1Labels = raw23700step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23700step0 raw23700step0Labels permutation39 permutation2
    _ = mixedMoment B node4221 node4221Labels := by rfl

theorem canonical23701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23701 raw23701Labels = mixedMoment B node4221 node4221Labels := by
  calc
    mixedMoment B raw23701 raw23701Labels = mixedMoment B raw23701step0 raw23701step0Labels := by
      have hz : ∀ j, raw23701 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23701step0 = (fun i j => raw23701 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23701step0 raw23701; decide +kernel
      have hl : raw23701step0Labels = raw23701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23701 raw23701Labels permutation346 hz
    mixedMoment B raw23701step0 raw23701step0Labels = mixedMoment B raw23701step1 raw23701step1Labels := by
      have ha : raw23701step1 = (fun i j => raw23701step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23701step1 raw23701step0; decide +kernel
      have hl : raw23701step1Labels = raw23701step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23701step0 raw23701step0Labels permutation39 permutation2
    _ = mixedMoment B node4221 node4221Labels := by rfl

theorem canonical23702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23702 raw23702Labels = mixedMoment B node4283 node4283Labels := by
  calc
    mixedMoment B raw23702 raw23702Labels = mixedMoment B raw23702step0 raw23702step0Labels := by
      have hz : ∀ j, raw23702 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23702step0 = (fun i j => raw23702 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23702step0 raw23702; decide +kernel
      have hl : raw23702step0Labels = raw23702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23702 raw23702Labels permutation434 hz
    mixedMoment B raw23702step0 raw23702step0Labels = mixedMoment B raw23702step1 raw23702step1Labels := by
      have hz : ∀ j, raw23702step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23702step1 = (fun i j => raw23702step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23702step1 raw23702step0; decide +kernel
      have hl : raw23702step1Labels = raw23702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23702step0 raw23702step0Labels permutation80 hz
    _ = mixedMoment B node4283 node4283Labels := by rfl

theorem canonical23703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23703 raw23703Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw23703 raw23703Labels = mixedMoment B raw23703step0 raw23703step0Labels := by
      have hz : ∀ j, raw23703 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23703step0 = (fun i j => raw23703 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23703step0 raw23703; decide +kernel
      have hl : raw23703step0Labels = raw23703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23703 raw23703Labels permutation434 hz
    mixedMoment B raw23703step0 raw23703step0Labels = mixedMoment B raw23703step1 raw23703step1Labels := by
      have hz : ∀ j, raw23703step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23703step1 = (fun i j => raw23703step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23703step1 raw23703step0; decide +kernel
      have hl : raw23703step1Labels = raw23703step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23703step0 raw23703step0Labels permutation80 hz
    mixedMoment B raw23703step1 raw23703step1Labels = mixedMoment B raw23703step2 raw23703step2Labels := by
      have hz : ∀ i, raw23703step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw23703step2 = (fun i j => raw23703step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw23703step2 raw23703step1; decide +kernel
      have hl : raw23703step2Labels = (fun j => raw23703step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23703step1 raw23703step1Labels permutation4 hz
    mixedMoment B raw23703step2 raw23703step2Labels = mixedMoment B raw23703step3 raw23703step3Labels := by
      have ha : raw23703step3 = (fun i j => raw23703step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23703step3 raw23703step2; decide +kernel
      have hl : raw23703step3Labels = raw23703step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23703step2 raw23703step2Labels permutation9 permutation0
    mixedMoment B raw23703step3 raw23703step3Labels = mixedMoment B raw23703step4 raw23703step4Labels := by
      have ha : raw23703step4 = raw23703step3 := by apply Matrix.ext; unfold raw23703step4 raw23703step3; decide +kernel
      have hl : raw23703step3Labels = labelEmbedding2 ∘ raw23703step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23703step3 raw23703step3Labels raw23703step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical23704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23704 raw23704Labels = mixedMoment B node4102 node4102Labels := by
  calc
    mixedMoment B raw23704 raw23704Labels = mixedMoment B raw23704step0 raw23704step0Labels := by
      have hz : ∀ j, raw23704 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23704step0 = (fun i j => raw23704 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23704step0 raw23704; decide +kernel
      have hl : raw23704step0Labels = raw23704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23704 raw23704Labels permutation434 hz
    mixedMoment B raw23704step0 raw23704step0Labels = mixedMoment B raw23704step1 raw23704step1Labels := by
      have ha : raw23704step1 = (fun i j => raw23704step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23704step1 raw23704step0; decide +kernel
      have hl : raw23704step1Labels = raw23704step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23704step0 raw23704step0Labels permutation33 permutation2
    _ = mixedMoment B node4102 node4102Labels := by rfl

theorem canonical23705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23705 raw23705Labels = mixedMoment B node4234 node4234Labels := by
  calc
    mixedMoment B raw23705 raw23705Labels = mixedMoment B raw23705step0 raw23705step0Labels := by
      have hz : ∀ j, raw23705 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23705step0 = (fun i j => raw23705 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23705step0 raw23705; decide +kernel
      have hl : raw23705step0Labels = raw23705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23705 raw23705Labels permutation434 hz
    mixedMoment B raw23705step0 raw23705step0Labels = mixedMoment B raw23705step1 raw23705step1Labels := by
      have ha : raw23705step1 = (fun i j => raw23705step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23705step1 raw23705step0; decide +kernel
      have hl : raw23705step1Labels = raw23705step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23705step0 raw23705step0Labels permutation33 permutation2
    _ = mixedMoment B node4234 node4234Labels := by rfl

theorem canonical23706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23706 raw23706Labels = mixedMoment B node4197 node4197Labels := by
  calc
    mixedMoment B raw23706 raw23706Labels = mixedMoment B raw23706step0 raw23706step0Labels := by
      have ha : raw23706step0 = (fun i j => raw23706 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23706step0 raw23706; decide +kernel
      have hl : raw23706step0Labels = raw23706Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23706 raw23706Labels permutation201 permutation2
    _ = mixedMoment B node4197 node4197Labels := by rfl

theorem canonical23707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23707 raw23707Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw23707 raw23707Labels = mixedMoment B raw23707step0 raw23707step0Labels := by
      have hz : ∀ j, raw23707 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23707step0 = (fun i j => raw23707 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23707step0 raw23707; decide +kernel
      have hl : raw23707step0Labels = raw23707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23707 raw23707Labels permutation434 hz
    _ = mixedMoment B node4265 node4265Labels := by rfl

theorem canonical23708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23708 raw23708Labels = mixedMoment B node4264 node4264Labels := by
  calc
    mixedMoment B raw23708 raw23708Labels = mixedMoment B raw23708step0 raw23708step0Labels := by
      have hz : ∀ j, raw23708 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23708step0 = (fun i j => raw23708 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23708step0 raw23708; decide +kernel
      have hl : raw23708step0Labels = raw23708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23708 raw23708Labels permutation434 hz
    mixedMoment B raw23708step0 raw23708step0Labels = mixedMoment B raw23708step1 raw23708step1Labels := by
      have ha : raw23708step1 = (fun i j => raw23708step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23708step1 raw23708step0; decide +kernel
      have hl : raw23708step1Labels = raw23708step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23708step0 raw23708step0Labels permutation33 permutation2
    _ = mixedMoment B node4264 node4264Labels := by rfl

theorem canonical23709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23709 raw23709Labels = mixedMoment B node4102 node4102Labels := by
  calc
    mixedMoment B raw23709 raw23709Labels = mixedMoment B raw23709step0 raw23709step0Labels := by
      have hz : ∀ j, raw23709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23709step0 = (fun i j => raw23709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23709step0 raw23709; decide +kernel
      have hl : raw23709step0Labels = raw23709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23709 raw23709Labels permutation346 hz
    mixedMoment B raw23709step0 raw23709step0Labels = mixedMoment B raw23709step1 raw23709step1Labels := by
      have ha : raw23709step1 = (fun i j => raw23709step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23709step1 raw23709step0; decide +kernel
      have hl : raw23709step1Labels = raw23709step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23709step0 raw23709step0Labels permutation33 permutation2
    _ = mixedMoment B node4102 node4102Labels := by rfl

theorem canonical23710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23710 raw23710Labels = mixedMoment B node4234 node4234Labels := by
  calc
    mixedMoment B raw23710 raw23710Labels = mixedMoment B raw23710step0 raw23710step0Labels := by
      have hz : ∀ j, raw23710 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23710step0 = (fun i j => raw23710 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23710step0 raw23710; decide +kernel
      have hl : raw23710step0Labels = raw23710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23710 raw23710Labels permutation346 hz
    mixedMoment B raw23710step0 raw23710step0Labels = mixedMoment B raw23710step1 raw23710step1Labels := by
      have ha : raw23710step1 = (fun i j => raw23710step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23710step1 raw23710step0; decide +kernel
      have hl : raw23710step1Labels = raw23710step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23710step0 raw23710step0Labels permutation33 permutation2
    _ = mixedMoment B node4234 node4234Labels := by rfl

theorem canonical23711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23711 raw23711Labels = mixedMoment B node4197 node4197Labels := by
  calc
    mixedMoment B raw23711 raw23711Labels = mixedMoment B raw23711step0 raw23711step0Labels := by
      have ha : raw23711step0 = (fun i j => raw23711 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23711step0 raw23711; decide +kernel
      have hl : raw23711step0Labels = raw23711Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23711 raw23711Labels permutation177 permutation2
    _ = mixedMoment B node4197 node4197Labels := by rfl

theorem canonical23712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23712 raw23712Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw23712 raw23712Labels = mixedMoment B raw23712step0 raw23712step0Labels := by
      have hz : ∀ j, raw23712 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23712step0 = (fun i j => raw23712 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23712step0 raw23712; decide +kernel
      have hl : raw23712step0Labels = raw23712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23712 raw23712Labels permutation346 hz
    _ = mixedMoment B node4265 node4265Labels := by rfl

theorem canonical23713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23713 raw23713Labels = mixedMoment B node4264 node4264Labels := by
  calc
    mixedMoment B raw23713 raw23713Labels = mixedMoment B raw23713step0 raw23713step0Labels := by
      have hz : ∀ j, raw23713 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23713step0 = (fun i j => raw23713 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23713step0 raw23713; decide +kernel
      have hl : raw23713step0Labels = raw23713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23713 raw23713Labels permutation346 hz
    mixedMoment B raw23713step0 raw23713step0Labels = mixedMoment B raw23713step1 raw23713step1Labels := by
      have ha : raw23713step1 = (fun i j => raw23713step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23713step1 raw23713step0; decide +kernel
      have hl : raw23713step1Labels = raw23713step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23713step0 raw23713step0Labels permutation33 permutation2
    _ = mixedMoment B node4264 node4264Labels := by rfl

theorem canonical23714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23714 raw23714Labels = mixedMoment B node4110 node4110Labels := by
  calc
    mixedMoment B raw23714 raw23714Labels = mixedMoment B raw23714step0 raw23714step0Labels := by
      have hz : ∀ j, raw23714 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23714step0 = (fun i j => raw23714 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23714step0 raw23714; decide +kernel
      have hl : raw23714step0Labels = raw23714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23714 raw23714Labels permutation434 hz
    mixedMoment B raw23714step0 raw23714step0Labels = mixedMoment B raw23714step1 raw23714step1Labels := by
      have hz : ∀ j, raw23714step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23714step1 = (fun i j => raw23714step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23714step1 raw23714step0; decide +kernel
      have hl : raw23714step1Labels = raw23714step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23714step0 raw23714step0Labels permutation80 hz
    mixedMoment B raw23714step1 raw23714step1Labels = mixedMoment B raw23714step2 raw23714step2Labels := by
      have ha : raw23714step2 = (fun i j => raw23714step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23714step2 raw23714step1; decide +kernel
      have hl : raw23714step2Labels = raw23714step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23714step1 raw23714step1Labels permutation9 permutation2
    _ = mixedMoment B node4110 node4110Labels := by rfl

theorem canonical23715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23715 raw23715Labels = mixedMoment B node4242 node4242Labels := by
  calc
    mixedMoment B raw23715 raw23715Labels = mixedMoment B raw23715step0 raw23715step0Labels := by
      have hz : ∀ j, raw23715 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23715step0 = (fun i j => raw23715 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23715step0 raw23715; decide +kernel
      have hl : raw23715step0Labels = raw23715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23715 raw23715Labels permutation434 hz
    mixedMoment B raw23715step0 raw23715step0Labels = mixedMoment B raw23715step1 raw23715step1Labels := by
      have hz : ∀ j, raw23715step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23715step1 = (fun i j => raw23715step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23715step1 raw23715step0; decide +kernel
      have hl : raw23715step1Labels = raw23715step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23715step0 raw23715step0Labels permutation80 hz
    mixedMoment B raw23715step1 raw23715step1Labels = mixedMoment B raw23715step2 raw23715step2Labels := by
      have ha : raw23715step2 = (fun i j => raw23715step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23715step2 raw23715step1; decide +kernel
      have hl : raw23715step2Labels = raw23715step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23715step1 raw23715step1Labels permutation9 permutation2
    _ = mixedMoment B node4242 node4242Labels := by rfl

theorem canonical23716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23716 raw23716Labels = mixedMoment B node4204 node4204Labels := by
  calc
    mixedMoment B raw23716 raw23716Labels = mixedMoment B raw23716step0 raw23716step0Labels := by
      have hz : ∀ j, raw23716 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23716step0 = (fun i j => raw23716 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23716step0 raw23716; decide +kernel
      have hl : raw23716step0Labels = raw23716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23716 raw23716Labels permutation434 hz
    mixedMoment B raw23716step0 raw23716step0Labels = mixedMoment B raw23716step1 raw23716step1Labels := by
      have ha : raw23716step1 = (fun i j => raw23716step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23716step1 raw23716step0; decide +kernel
      have hl : raw23716step1Labels = raw23716step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23716step0 raw23716step0Labels permutation39 permutation2
    _ = mixedMoment B node4204 node4204Labels := by rfl

theorem canonical23717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23717 raw23717Labels = mixedMoment B node4204 node4204Labels := by
  calc
    mixedMoment B raw23717 raw23717Labels = mixedMoment B raw23717step0 raw23717step0Labels := by
      have hz : ∀ j, raw23717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23717step0 = (fun i j => raw23717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23717step0 raw23717; decide +kernel
      have hl : raw23717step0Labels = raw23717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23717 raw23717Labels permutation346 hz
    mixedMoment B raw23717step0 raw23717step0Labels = mixedMoment B raw23717step1 raw23717step1Labels := by
      have ha : raw23717step1 = (fun i j => raw23717step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23717step1 raw23717step0; decide +kernel
      have hl : raw23717step1Labels = raw23717step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23717step0 raw23717step0Labels permutation39 permutation2
    _ = mixedMoment B node4204 node4204Labels := by rfl

theorem canonical23718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23718 raw23718Labels = mixedMoment B node4269 node4269Labels := by
  calc
    mixedMoment B raw23718 raw23718Labels = mixedMoment B raw23718step0 raw23718step0Labels := by
      have hz : ∀ j, raw23718 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23718step0 = (fun i j => raw23718 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23718step0 raw23718; decide +kernel
      have hl : raw23718step0Labels = raw23718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23718 raw23718Labels permutation434 hz
    mixedMoment B raw23718step0 raw23718step0Labels = mixedMoment B raw23718step1 raw23718step1Labels := by
      have hz : ∀ j, raw23718step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23718step1 = (fun i j => raw23718step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23718step1 raw23718step0; decide +kernel
      have hl : raw23718step1Labels = raw23718step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23718step0 raw23718step0Labels permutation80 hz
    mixedMoment B raw23718step1 raw23718step1Labels = mixedMoment B raw23718step2 raw23718step2Labels := by
      have ha : raw23718step2 = (fun i j => raw23718step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23718step2 raw23718step1; decide +kernel
      have hl : raw23718step2Labels = raw23718step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23718step1 raw23718step1Labels permutation9 permutation2
    _ = mixedMoment B node4269 node4269Labels := by rfl

theorem canonical23719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23719 raw23719Labels = mixedMoment B node4111 node4111Labels := by
  calc
    mixedMoment B raw23719 raw23719Labels = mixedMoment B raw23719step0 raw23719step0Labels := by
      have hz : ∀ j, raw23719 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23719step0 = (fun i j => raw23719 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23719step0 raw23719; decide +kernel
      have hl : raw23719step0Labels = raw23719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23719 raw23719Labels permutation434 hz
    mixedMoment B raw23719step0 raw23719step0Labels = mixedMoment B raw23719step1 raw23719step1Labels := by
      have hz : ∀ j, raw23719step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23719step1 = (fun i j => raw23719step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23719step1 raw23719step0; decide +kernel
      have hl : raw23719step1Labels = raw23719step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23719step0 raw23719step0Labels permutation80 hz
    _ = mixedMoment B node4111 node4111Labels := by rfl

theorem canonical23720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23720 raw23720Labels = mixedMoment B node4243 node4243Labels := by
  calc
    mixedMoment B raw23720 raw23720Labels = mixedMoment B raw23720step0 raw23720step0Labels := by
      have hz : ∀ j, raw23720 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23720step0 = (fun i j => raw23720 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23720step0 raw23720; decide +kernel
      have hl : raw23720step0Labels = raw23720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23720 raw23720Labels permutation434 hz
    mixedMoment B raw23720step0 raw23720step0Labels = mixedMoment B raw23720step1 raw23720step1Labels := by
      have hz : ∀ j, raw23720step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23720step1 = (fun i j => raw23720step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23720step1 raw23720step0; decide +kernel
      have hl : raw23720step1Labels = raw23720step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23720step0 raw23720step0Labels permutation80 hz
    _ = mixedMoment B node4243 node4243Labels := by rfl

theorem canonical23721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23721 raw23721Labels = mixedMoment B node4205 node4205Labels := by
  calc
    mixedMoment B raw23721 raw23721Labels = mixedMoment B raw23721step0 raw23721step0Labels := by
      have hz : ∀ j, raw23721 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23721step0 = (fun i j => raw23721 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23721step0 raw23721; decide +kernel
      have hl : raw23721step0Labels = raw23721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23721 raw23721Labels permutation434 hz
    mixedMoment B raw23721step0 raw23721step0Labels = mixedMoment B raw23721step1 raw23721step1Labels := by
      have ha : raw23721step1 = (fun i j => raw23721step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23721step1 raw23721step0; decide +kernel
      have hl : raw23721step1Labels = raw23721step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23721step0 raw23721step0Labels permutation38 permutation2
    _ = mixedMoment B node4205 node4205Labels := by rfl

theorem canonical23722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23722 raw23722Labels = mixedMoment B node4205 node4205Labels := by
  calc
    mixedMoment B raw23722 raw23722Labels = mixedMoment B raw23722step0 raw23722step0Labels := by
      have hz : ∀ j, raw23722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23722step0 = (fun i j => raw23722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23722step0 raw23722; decide +kernel
      have hl : raw23722step0Labels = raw23722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23722 raw23722Labels permutation346 hz
    mixedMoment B raw23722step0 raw23722step0Labels = mixedMoment B raw23722step1 raw23722step1Labels := by
      have ha : raw23722step1 = (fun i j => raw23722step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23722step1 raw23722step0; decide +kernel
      have hl : raw23722step1Labels = raw23722step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23722step0 raw23722step0Labels permutation38 permutation2
    _ = mixedMoment B node4205 node4205Labels := by rfl

theorem canonical23723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23723 raw23723Labels = mixedMoment B node4270 node4270Labels := by
  calc
    mixedMoment B raw23723 raw23723Labels = mixedMoment B raw23723step0 raw23723step0Labels := by
      have hz : ∀ j, raw23723 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23723step0 = (fun i j => raw23723 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23723step0 raw23723; decide +kernel
      have hl : raw23723step0Labels = raw23723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23723 raw23723Labels permutation434 hz
    mixedMoment B raw23723step0 raw23723step0Labels = mixedMoment B raw23723step1 raw23723step1Labels := by
      have hz : ∀ j, raw23723step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23723step1 = (fun i j => raw23723step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23723step1 raw23723step0; decide +kernel
      have hl : raw23723step1Labels = raw23723step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23723step0 raw23723step0Labels permutation80 hz
    _ = mixedMoment B node4270 node4270Labels := by rfl

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

theorem canonical678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw678 raw678Labels = mixedMoment B node4102 node4102Labels := by
  calc
    mixedMoment B raw678 raw678Labels = mixedMoment B raw678step0 raw678step0Labels := by
      have ha : raw678step0 = (fun i j => raw678 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw678step0 raw678; decide +kernel
      have hl : raw678step0Labels = raw678Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw678 raw678Labels permutation32 permutation4
    mixedMoment B raw678step0 raw678step0Labels = mixedMoment B raw678step1 raw678step1Labels := by
      have ha : raw678step1 = raw678step0 := by apply Matrix.ext; unfold raw678step1 raw678step0; decide +kernel
      have hl : raw678step0Labels = labelEmbedding7 ∘ raw678step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw678step0 raw678step0Labels raw678step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4102 node4102Labels := by rfl

theorem canonical679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw679 raw679Labels = mixedMoment B node539 node539Labels := by
  calc
    mixedMoment B raw679 raw679Labels = mixedMoment B raw679step0 raw679step0Labels := by
      have ha : raw679step0 = (fun i j => raw679 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw679step0 raw679; decide +kernel
      have hl : raw679step0Labels = raw679Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw679 raw679Labels permutation32 permutation4
    _ = mixedMoment B node539 node539Labels := by rfl

theorem canonical680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw680 raw680Labels = mixedMoment B node664 node664Labels := by
  calc
    mixedMoment B raw680 raw680Labels = mixedMoment B raw680step0 raw680step0Labels := by
      have ha : raw680step0 = (fun i j => raw680 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw680step0 raw680; decide +kernel
      have hl : raw680step0Labels = raw680Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw680 raw680Labels permutation38 permutation6
    mixedMoment B raw680step0 raw680step0Labels = mixedMoment B raw680step1 raw680step1Labels := by
      have ha : raw680step1 = -raw680step0 := by apply Matrix.ext; change ∀ i j, raw680step1 i j = -(raw680step0 i j); unfold raw680step1 raw680step0; decide +kernel
      have hl : raw680step1Labels = raw680step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw680step1 raw680step1Labels = mixedMoment B raw680step2 raw680step2Labels := by
      have ha : raw680step2 = raw680step1 := by apply Matrix.ext; unfold raw680step2 raw680step1; decide +kernel
      have hl : raw680step1Labels = labelEmbedding1 ∘ raw680step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw680step1 raw680step1Labels raw680step2Labels labelEmbedding1 hl
    _ = mixedMoment B node664 node664Labels := by rfl

theorem canonical702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw702 raw702Labels = mixedMoment B node4110 node4110Labels := by
  calc
    mixedMoment B raw702 raw702Labels = mixedMoment B raw702step0 raw702step0Labels := by
      have ha : raw702step0 = (fun i j => raw702 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw702step0 raw702; decide +kernel
      have hl : raw702step0Labels = raw702Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw702 raw702Labels permutation8 permutation4
    mixedMoment B raw702step0 raw702step0Labels = mixedMoment B raw702step1 raw702step1Labels := by
      have ha : raw702step1 = raw702step0 := by apply Matrix.ext; unfold raw702step1 raw702step0; decide +kernel
      have hl : raw702step0Labels = labelEmbedding7 ∘ raw702step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw702step0 raw702step0Labels raw702step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4110 node4110Labels := by rfl

theorem canonical703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw703 raw703Labels = mixedMoment B node547 node547Labels := by
  calc
    mixedMoment B raw703 raw703Labels = mixedMoment B raw703step0 raw703step0Labels := by
      have ha : raw703step0 = (fun i j => raw703 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw703step0 raw703; decide +kernel
      have hl : raw703step0Labels = raw703Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw703 raw703Labels permutation8 permutation4
    _ = mixedMoment B node547 node547Labels := by rfl

theorem canonical704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw704 raw704Labels = mixedMoment B node684 node684Labels := by
  calc
    mixedMoment B raw704 raw704Labels = mixedMoment B raw704step0 raw704step0Labels := by
      have ha : raw704step0 = (fun i j => raw704 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw704step0 raw704; decide +kernel
      have hl : raw704step0Labels = raw704Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw704 raw704Labels permutation8 permutation6
    mixedMoment B raw704step0 raw704step0Labels = mixedMoment B raw704step1 raw704step1Labels := by
      have ha : raw704step1 = -raw704step0 := by apply Matrix.ext; change ∀ i j, raw704step1 i j = -(raw704step0 i j); unfold raw704step1 raw704step0; decide +kernel
      have hl : raw704step1Labels = raw704step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw704step1 raw704step1Labels = mixedMoment B raw704step2 raw704step2Labels := by
      have ha : raw704step2 = raw704step1 := by apply Matrix.ext; unfold raw704step2 raw704step1; decide +kernel
      have hl : raw704step1Labels = labelEmbedding1 ∘ raw704step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw704step1 raw704step1Labels raw704step2Labels labelEmbedding1 hl
    _ = mixedMoment B node684 node684Labels := by rfl

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

theorem canonical855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw855 raw855Labels = mixedMoment B node4197 node4197Labels := by
  calc
    mixedMoment B raw855 raw855Labels = mixedMoment B raw855step0 raw855step0Labels := by
      have ha : raw855step0 = (fun i j => raw855 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw855step0 raw855; decide +kernel
      have hl : raw855step0Labels = raw855Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw855 raw855Labels permutation152 permutation4
    mixedMoment B raw855step0 raw855step0Labels = mixedMoment B raw855step1 raw855step1Labels := by
      have ha : raw855step1 = raw855step0 := by apply Matrix.ext; unfold raw855step1 raw855step0; decide +kernel
      have hl : raw855step0Labels = labelEmbedding7 ∘ raw855step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw855step0 raw855step0Labels raw855step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4197 node4197Labels := by rfl

theorem canonical856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw856 raw856Labels = mixedMoment B node700 node700Labels := by
  calc
    mixedMoment B raw856 raw856Labels = mixedMoment B raw856step0 raw856step0Labels := by
      have ha : raw856step0 = (fun i j => raw856 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw856step0 raw856; decide +kernel
      have hl : raw856step0Labels = raw856Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw856 raw856Labels permutation152 permutation4
    _ = mixedMoment B node700 node700Labels := by rfl

theorem canonical857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw857 raw857Labels = mixedMoment B node749 node749Labels := by
  calc
    mixedMoment B raw857 raw857Labels = mixedMoment B raw857step0 raw857step0Labels := by
      have ha : raw857step0 = (fun i j => raw857 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw857step0 raw857; decide +kernel
      have hl : raw857step0Labels = raw857Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw857 raw857Labels permutation158 permutation6
    mixedMoment B raw857step0 raw857step0Labels = mixedMoment B raw857step1 raw857step1Labels := by
      have ha : raw857step1 = -raw857step0 := by apply Matrix.ext; change ∀ i j, raw857step1 i j = -(raw857step0 i j); unfold raw857step1 raw857step0; decide +kernel
      have hl : raw857step1Labels = raw857step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw857step1 raw857step1Labels = mixedMoment B raw857step2 raw857step2Labels := by
      have ha : raw857step2 = raw857step1 := by apply Matrix.ext; unfold raw857step2 raw857step1; decide +kernel
      have hl : raw857step1Labels = labelEmbedding1 ∘ raw857step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw857step1 raw857step1Labels raw857step2Labels labelEmbedding1 hl
    _ = mixedMoment B node749 node749Labels := by rfl

theorem canonical876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw876 raw876Labels = mixedMoment B node4204 node4204Labels := by
  calc
    mixedMoment B raw876 raw876Labels = mixedMoment B raw876step0 raw876step0Labels := by
      have ha : raw876step0 = (fun i j => raw876 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw876step0 raw876; decide +kernel
      have hl : raw876step0Labels = raw876Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw876 raw876Labels permutation32 permutation4
    mixedMoment B raw876step0 raw876step0Labels = mixedMoment B raw876step1 raw876step1Labels := by
      have ha : raw876step1 = raw876step0 := by apply Matrix.ext; unfold raw876step1 raw876step0; decide +kernel
      have hl : raw876step0Labels = labelEmbedding7 ∘ raw876step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw876step0 raw876step0Labels raw876step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4204 node4204Labels := by rfl

theorem canonical877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw877 raw877Labels = mixedMoment B node707 node707Labels := by
  calc
    mixedMoment B raw877 raw877Labels = mixedMoment B raw877step0 raw877step0Labels := by
      have ha : raw877step0 = (fun i j => raw877 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw877step0 raw877; decide +kernel
      have hl : raw877step0Labels = raw877Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw877 raw877Labels permutation32 permutation4
    _ = mixedMoment B node707 node707Labels := by rfl

theorem canonical878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw878 raw878Labels = mixedMoment B node763 node763Labels := by
  calc
    mixedMoment B raw878 raw878Labels = mixedMoment B raw878step0 raw878step0Labels := by
      have ha : raw878step0 = (fun i j => raw878 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw878step0 raw878; decide +kernel
      have hl : raw878step0Labels = raw878Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw878 raw878Labels permutation32 permutation6
    mixedMoment B raw878step0 raw878step0Labels = mixedMoment B raw878step1 raw878step1Labels := by
      have ha : raw878step1 = -raw878step0 := by apply Matrix.ext; change ∀ i j, raw878step1 i j = -(raw878step0 i j); unfold raw878step1 raw878step0; decide +kernel
      have hl : raw878step1Labels = raw878step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw878step1 raw878step1Labels = mixedMoment B raw878step2 raw878step2Labels := by
      have ha : raw878step2 = raw878step1 := by apply Matrix.ext; unfold raw878step2 raw878step1; decide +kernel
      have hl : raw878step1Labels = labelEmbedding1 ∘ raw878step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw878step1 raw878step1Labels raw878step2Labels labelEmbedding1 hl
    _ = mixedMoment B node763 node763Labels := by rfl

theorem canonical879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw879 raw879Labels = mixedMoment B node4205 node4205Labels := by
  calc
    mixedMoment B raw879 raw879Labels = mixedMoment B raw879step0 raw879step0Labels := by
      have ha : raw879step0 = (fun i j => raw879 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw879step0 raw879; decide +kernel
      have hl : raw879step0Labels = raw879Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw879 raw879Labels permutation32 permutation4
    mixedMoment B raw879step0 raw879step0Labels = mixedMoment B raw879step1 raw879step1Labels := by
      have ha : raw879step1 = raw879step0 := by apply Matrix.ext; unfold raw879step1 raw879step0; decide +kernel
      have hl : raw879step0Labels = labelEmbedding7 ∘ raw879step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw879step0 raw879step0Labels raw879step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4205 node4205Labels := by rfl

theorem canonical880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw880 raw880Labels = mixedMoment B node708 node708Labels := by
  calc
    mixedMoment B raw880 raw880Labels = mixedMoment B raw880step0 raw880step0Labels := by
      have ha : raw880step0 = (fun i j => raw880 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw880step0 raw880; decide +kernel
      have hl : raw880step0Labels = raw880Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw880 raw880Labels permutation32 permutation4
    _ = mixedMoment B node708 node708Labels := by rfl

theorem canonical881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw881 raw881Labels = mixedMoment B node764 node764Labels := by
  calc
    mixedMoment B raw881 raw881Labels = mixedMoment B raw881step0 raw881step0Labels := by
      have ha : raw881step0 = (fun i j => raw881 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw881step0 raw881; decide +kernel
      have hl : raw881step0Labels = raw881Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw881 raw881Labels permutation33 permutation6
    mixedMoment B raw881step0 raw881step0Labels = mixedMoment B raw881step1 raw881step1Labels := by
      have ha : raw881step1 = -raw881step0 := by apply Matrix.ext; change ∀ i j, raw881step1 i j = -(raw881step0 i j); unfold raw881step1 raw881step0; decide +kernel
      have hl : raw881step1Labels = raw881step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw881step1 raw881step1Labels = mixedMoment B raw881step2 raw881step2Labels := by
      have ha : raw881step2 = raw881step1 := by apply Matrix.ext; unfold raw881step2 raw881step1; decide +kernel
      have hl : raw881step1Labels = labelEmbedding1 ∘ raw881step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw881step1 raw881step1Labels raw881step2Labels labelEmbedding1 hl
    _ = mixedMoment B node764 node764Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw936 raw936Labels = mixedMoment B node4234 node4234Labels := by
  calc
    mixedMoment B raw936 raw936Labels = mixedMoment B raw936step0 raw936step0Labels := by
      have ha : raw936step0 = (fun i j => raw936 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw936step0 raw936; decide +kernel
      have hl : raw936step0Labels = raw936Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw936 raw936Labels permutation32 permutation4
    mixedMoment B raw936step0 raw936step0Labels = mixedMoment B raw936step1 raw936step1Labels := by
      have ha : raw936step1 = raw936step0 := by apply Matrix.ext; unfold raw936step1 raw936step0; decide +kernel
      have hl : raw936step0Labels = labelEmbedding7 ∘ raw936step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw936step0 raw936step0Labels raw936step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4234 node4234Labels := by rfl

theorem canonical937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw937 raw937Labels = mixedMoment B node734 node734Labels := by
  calc
    mixedMoment B raw937 raw937Labels = mixedMoment B raw937step0 raw937step0Labels := by
      have ha : raw937step0 = (fun i j => raw937 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw937step0 raw937; decide +kernel
      have hl : raw937step0Labels = raw937Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw937 raw937Labels permutation32 permutation4
    _ = mixedMoment B node734 node734Labels := by rfl

theorem canonical938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw938 raw938Labels = mixedMoment B node800 node800Labels := by
  calc
    mixedMoment B raw938 raw938Labels = mixedMoment B raw938step0 raw938step0Labels := by
      have ha : raw938step0 = (fun i j => raw938 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw938step0 raw938; decide +kernel
      have hl : raw938step0Labels = raw938Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw938 raw938Labels permutation38 permutation6
    mixedMoment B raw938step0 raw938step0Labels = mixedMoment B raw938step1 raw938step1Labels := by
      have ha : raw938step1 = -raw938step0 := by apply Matrix.ext; change ∀ i j, raw938step1 i j = -(raw938step0 i j); unfold raw938step1 raw938step0; decide +kernel
      have hl : raw938step1Labels = raw938step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw938step1 raw938step1Labels = mixedMoment B raw938step2 raw938step2Labels := by
      have ha : raw938step2 = raw938step1 := by apply Matrix.ext; unfold raw938step2 raw938step1; decide +kernel
      have hl : raw938step1Labels = labelEmbedding1 ∘ raw938step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw938step1 raw938step1Labels raw938step2Labels labelEmbedding1 hl
    _ = mixedMoment B node800 node800Labels := by rfl

theorem canonical960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw960 raw960Labels = mixedMoment B node4242 node4242Labels := by
  calc
    mixedMoment B raw960 raw960Labels = mixedMoment B raw960step0 raw960step0Labels := by
      have ha : raw960step0 = (fun i j => raw960 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw960step0 raw960; decide +kernel
      have hl : raw960step0Labels = raw960Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw960 raw960Labels permutation8 permutation4
    mixedMoment B raw960step0 raw960step0Labels = mixedMoment B raw960step1 raw960step1Labels := by
      have ha : raw960step1 = raw960step0 := by apply Matrix.ext; unfold raw960step1 raw960step0; decide +kernel
      have hl : raw960step0Labels = labelEmbedding7 ∘ raw960step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw960step0 raw960step0Labels raw960step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4242 node4242Labels := by rfl

theorem canonical961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw961 raw961Labels = mixedMoment B node742 node742Labels := by
  calc
    mixedMoment B raw961 raw961Labels = mixedMoment B raw961step0 raw961step0Labels := by
      have ha : raw961step0 = (fun i j => raw961 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw961step0 raw961; decide +kernel
      have hl : raw961step0Labels = raw961Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw961 raw961Labels permutation8 permutation4
    _ = mixedMoment B node742 node742Labels := by rfl

theorem canonical962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw962 raw962Labels = mixedMoment B node843 node843Labels := by
  calc
    mixedMoment B raw962 raw962Labels = mixedMoment B raw962step0 raw962step0Labels := by
      have ha : raw962step0 = (fun i j => raw962 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw962step0 raw962; decide +kernel
      have hl : raw962step0Labels = raw962Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw962 raw962Labels permutation8 permutation6
    mixedMoment B raw962step0 raw962step0Labels = mixedMoment B raw962step1 raw962step1Labels := by
      have ha : raw962step1 = -raw962step0 := by apply Matrix.ext; change ∀ i j, raw962step1 i j = -(raw962step0 i j); unfold raw962step1 raw962step0; decide +kernel
      have hl : raw962step1Labels = raw962step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw962step1 raw962step1Labels = mixedMoment B raw962step2 raw962step2Labels := by
      have ha : raw962step2 = raw962step1 := by apply Matrix.ext; unfold raw962step2 raw962step1; decide +kernel
      have hl : raw962step1Labels = labelEmbedding1 ∘ raw962step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw962step1 raw962step1Labels raw962step2Labels labelEmbedding1 hl
    _ = mixedMoment B node843 node843Labels := by rfl

theorem canonical963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw963 raw963Labels = mixedMoment B node4243 node4243Labels := by
  calc
    mixedMoment B raw963 raw963Labels = mixedMoment B raw963step0 raw963step0Labels := by
      have ha : raw963step0 = (fun i j => raw963 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw963step0 raw963; decide +kernel
      have hl : raw963step0Labels = raw963Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw963 raw963Labels permutation8 permutation4
    mixedMoment B raw963step0 raw963step0Labels = mixedMoment B raw963step1 raw963step1Labels := by
      have ha : raw963step1 = raw963step0 := by apply Matrix.ext; unfold raw963step1 raw963step0; decide +kernel
      have hl : raw963step0Labels = labelEmbedding7 ∘ raw963step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw963step0 raw963step0Labels raw963step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4243 node4243Labels := by rfl

theorem canonical964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw964 raw964Labels = mixedMoment B node743 node743Labels := by
  calc
    mixedMoment B raw964 raw964Labels = mixedMoment B raw964step0 raw964step0Labels := by
      have ha : raw964step0 = (fun i j => raw964 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw964step0 raw964; decide +kernel
      have hl : raw964step0Labels = raw964Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw964 raw964Labels permutation8 permutation4
    _ = mixedMoment B node743 node743Labels := by rfl

theorem canonical965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw965 raw965Labels = mixedMoment B node844 node844Labels := by
  calc
    mixedMoment B raw965 raw965Labels = mixedMoment B raw965step0 raw965step0Labels := by
      have ha : raw965step0 = (fun i j => raw965 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw965step0 raw965; decide +kernel
      have hl : raw965step0Labels = raw965Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw965 raw965Labels permutation9 permutation6
    mixedMoment B raw965step0 raw965step0Labels = mixedMoment B raw965step1 raw965step1Labels := by
      have ha : raw965step1 = -raw965step0 := by apply Matrix.ext; change ∀ i j, raw965step1 i j = -(raw965step0 i j); unfold raw965step1 raw965step0; decide +kernel
      have hl : raw965step1Labels = raw965step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw965step1 raw965step1Labels = mixedMoment B raw965step2 raw965step2Labels := by
      have ha : raw965step2 = raw965step1 := by apply Matrix.ext; unfold raw965step2 raw965step1; decide +kernel
      have hl : raw965step1Labels = labelEmbedding1 ∘ raw965step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw965step1 raw965step1Labels raw965step2Labels labelEmbedding1 hl
    _ = mixedMoment B node844 node844Labels := by rfl

theorem canonical990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw990 raw990Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw990 raw990Labels = mixedMoment B raw990step0 raw990step0Labels := by
      have ha : raw990step0 = (fun i j => raw990 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw990step0 raw990; decide +kernel
      have hl : raw990step0Labels = raw990Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw990 raw990Labels permutation32 permutation4
    mixedMoment B raw990step0 raw990step0Labels = mixedMoment B raw990step1 raw990step1Labels := by
      have ha : raw990step1 = raw990step0 := by apply Matrix.ext; unfold raw990step1 raw990step0; decide +kernel
      have hl : raw990step0Labels = labelEmbedding7 ∘ raw990step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw990step0 raw990step0Labels raw990step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4265 node4265Labels := by rfl

theorem canonical991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw991 raw991Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw991 raw991Labels = mixedMoment B raw991step0 raw991step0Labels := by
      have ha : raw991step0 = (fun i j => raw991 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw991step0 raw991; decide +kernel
      have hl : raw991step0Labels = raw991Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw991 raw991Labels permutation32 permutation4
    _ = mixedMoment B node807 node807Labels := by rfl

theorem canonical992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw992 raw992Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw992 raw992Labels = mixedMoment B raw992step0 raw992step0Labels := by
      have ha : raw992step0 = (fun i j => raw992 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw992step0 raw992; decide +kernel
      have hl : raw992step0Labels = raw992Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw992 raw992Labels permutation39 permutation6
    mixedMoment B raw992step0 raw992step0Labels = mixedMoment B raw992step1 raw992step1Labels := by
      have ha : raw992step1 = -raw992step0 := by apply Matrix.ext; change ∀ i j, raw992step1 i j = -(raw992step0 i j); unfold raw992step1 raw992step0; decide +kernel
      have hl : raw992step1Labels = raw992step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw992step1 raw992step1Labels = mixedMoment B raw992step2 raw992step2Labels := by
      have ha : raw992step2 = raw992step1 := by apply Matrix.ext; unfold raw992step2 raw992step1; decide +kernel
      have hl : raw992step1Labels = labelEmbedding1 ∘ raw992step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw992step1 raw992step1Labels raw992step2Labels labelEmbedding1 hl
    _ = mixedMoment B node807 node807Labels := by rfl

theorem canonical996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw996 raw996Labels = mixedMoment B node4270 node4270Labels := by
  calc
    mixedMoment B raw996 raw996Labels = mixedMoment B raw996step0 raw996step0Labels := by
      have ha : raw996step0 = (fun i j => raw996 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw996step0 raw996; decide +kernel
      have hl : raw996step0Labels = raw996Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw996 raw996Labels permutation8 permutation4
    mixedMoment B raw996step0 raw996step0Labels = mixedMoment B raw996step1 raw996step1Labels := by
      have ha : raw996step1 = raw996step0 := by apply Matrix.ext; unfold raw996step1 raw996step0; decide +kernel
      have hl : raw996step0Labels = labelEmbedding7 ∘ raw996step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw996step0 raw996step0Labels raw996step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4270 node4270Labels := by rfl

theorem canonical997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw997 raw997Labels = mixedMoment B node813 node813Labels := by
  calc
    mixedMoment B raw997 raw997Labels = mixedMoment B raw997step0 raw997step0Labels := by
      have ha : raw997step0 = (fun i j => raw997 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw997step0 raw997; decide +kernel
      have hl : raw997step0Labels = raw997Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw997 raw997Labels permutation8 permutation4
    _ = mixedMoment B node813 node813Labels := by rfl

theorem canonical998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw998 raw998Labels = mixedMoment B node853 node853Labels := by
  calc
    mixedMoment B raw998 raw998Labels = mixedMoment B raw998step0 raw998step0Labels := by
      have ha : raw998step0 = (fun i j => raw998 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw998step0 raw998; decide +kernel
      have hl : raw998step0Labels = raw998Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw998 raw998Labels permutation9 permutation6
    mixedMoment B raw998step0 raw998step0Labels = mixedMoment B raw998step1 raw998step1Labels := by
      have ha : raw998step1 = -raw998step0 := by apply Matrix.ext; change ∀ i j, raw998step1 i j = -(raw998step0 i j); unfold raw998step1 raw998step0; decide +kernel
      have hl : raw998step1Labels = raw998step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw998step1 raw998step1Labels = mixedMoment B raw998step2 raw998step2Labels := by
      have ha : raw998step2 = raw998step1 := by apply Matrix.ext; unfold raw998step2 raw998step1; decide +kernel
      have hl : raw998step1Labels = labelEmbedding1 ∘ raw998step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw998step1 raw998step1Labels raw998step2Labels labelEmbedding1 hl
    _ = mixedMoment B node853 node853Labels := by rfl

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

theorem canonical1230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1230 raw1230Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw1230 raw1230Labels = mixedMoment B raw1230step0 raw1230step0Labels := by
      have ha : raw1230step0 = (fun i j => raw1230 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1230step0 raw1230; decide +kernel
      have hl : raw1230step0Labels = raw1230Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1230 raw1230Labels permutation32 permutation4
    mixedMoment B raw1230step0 raw1230step0Labels = mixedMoment B raw1230step1 raw1230step1Labels := by
      have ha : raw1230step1 = raw1230step0 := by apply Matrix.ext; unfold raw1230step1 raw1230step0; decide +kernel
      have hl : raw1230step0Labels = labelEmbedding7 ∘ raw1230step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1230step0 raw1230step0Labels raw1230step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

theorem canonical1231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1231 raw1231Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw1231 raw1231Labels = mixedMoment B raw1231step0 raw1231step0Labels := by
      have ha : raw1231step0 = (fun i j => raw1231 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1231step0 raw1231; decide +kernel
      have hl : raw1231step0Labels = raw1231Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1231 raw1231Labels permutation32 permutation4
    _ = mixedMoment B node1000 node1000Labels := by rfl

theorem canonical1232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1232 raw1232Labels = mixedMoment B node1605 node1605Labels := by
  calc
    mixedMoment B raw1232 raw1232Labels = mixedMoment B raw1232step0 raw1232step0Labels := by
      have ha : raw1232step0 = (fun i j => raw1232 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1232step0 raw1232; decide +kernel
      have hl : raw1232step0Labels = raw1232Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1232 raw1232Labels permutation32 permutation6
    mixedMoment B raw1232step0 raw1232step0Labels = mixedMoment B raw1232step1 raw1232step1Labels := by
      have ha : raw1232step1 = -raw1232step0 := by apply Matrix.ext; change ∀ i j, raw1232step1 i j = -(raw1232step0 i j); unfold raw1232step1 raw1232step0; decide +kernel
      have hl : raw1232step1Labels = raw1232step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1232step1 raw1232step1Labels = mixedMoment B raw1232step2 raw1232step2Labels := by
      have ha : raw1232step2 = raw1232step1 := by apply Matrix.ext; unfold raw1232step2 raw1232step1; decide +kernel
      have hl : raw1232step1Labels = labelEmbedding1 ∘ raw1232step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1232step1 raw1232step1Labels raw1232step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1605 node1605Labels := by rfl

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

theorem singleton4102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4102 node4102Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node539 node539Labels + mixedMoment B node664 node664Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw678 singletonSmall4102
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4102) = raw678Labels := by decide +kernel
  rw [hl, canonical678 B hB] at h
  have hc0 : mixedMoment B raw678 (Fin.cases (0 : Fin 2) singletonSmall4102) =
      mixedMoment B node539 node539Labels := by
    have ha : raw678 = raw679 := by apply Matrix.ext; unfold raw678 raw679; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4102 = raw679Labels := by decide +kernel
    rw [ha, hj, canonical679 B hB]
  have hc1 : mixedMoment B raw678 (Fin.cases (1 : Fin 2) singletonSmall4102) =
      mixedMoment B node664 node664Labels := by
    have ha : raw678 = raw680 := by apply Matrix.ext; unfold raw678 raw680; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4102 = raw680Labels := by decide +kernel
    rw [ha, hj, canonical680 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4110 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4110 node4110Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node547 node547Labels + mixedMoment B node684 node684Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw702 singletonSmall4110
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4110) = raw702Labels := by decide +kernel
  rw [hl, canonical702 B hB] at h
  have hc0 : mixedMoment B raw702 (Fin.cases (0 : Fin 2) singletonSmall4110) =
      mixedMoment B node547 node547Labels := by
    have ha : raw702 = raw703 := by apply Matrix.ext; unfold raw702 raw703; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4110 = raw703Labels := by decide +kernel
    rw [ha, hj, canonical703 B hB]
  have hc1 : mixedMoment B raw702 (Fin.cases (1 : Fin 2) singletonSmall4110) =
      mixedMoment B node684 node684Labels := by
    have ha : raw702 = raw704 := by apply Matrix.ext; unfold raw702 raw704; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4110 = raw704Labels := by decide +kernel
    rw [ha, hj, canonical704 B hB]
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

theorem singleton4197 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4197 node4197Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node700 node700Labels + mixedMoment B node749 node749Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw855 singletonSmall4197
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4197) = raw855Labels := by decide +kernel
  rw [hl, canonical855 B hB] at h
  have hc0 : mixedMoment B raw855 (Fin.cases (0 : Fin 2) singletonSmall4197) =
      mixedMoment B node700 node700Labels := by
    have ha : raw855 = raw856 := by apply Matrix.ext; unfold raw855 raw856; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4197 = raw856Labels := by decide +kernel
    rw [ha, hj, canonical856 B hB]
  have hc1 : mixedMoment B raw855 (Fin.cases (1 : Fin 2) singletonSmall4197) =
      mixedMoment B node749 node749Labels := by
    have ha : raw855 = raw857 := by apply Matrix.ext; unfold raw855 raw857; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4197 = raw857Labels := by decide +kernel
    rw [ha, hj, canonical857 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4204 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4204 node4204Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node707 node707Labels + mixedMoment B node763 node763Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw876 singletonSmall4204
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4204) = raw876Labels := by decide +kernel
  rw [hl, canonical876 B hB] at h
  have hc0 : mixedMoment B raw876 (Fin.cases (0 : Fin 2) singletonSmall4204) =
      mixedMoment B node707 node707Labels := by
    have ha : raw876 = raw877 := by apply Matrix.ext; unfold raw876 raw877; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4204 = raw877Labels := by decide +kernel
    rw [ha, hj, canonical877 B hB]
  have hc1 : mixedMoment B raw876 (Fin.cases (1 : Fin 2) singletonSmall4204) =
      mixedMoment B node763 node763Labels := by
    have ha : raw876 = raw878 := by apply Matrix.ext; unfold raw876 raw878; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4204 = raw878Labels := by decide +kernel
    rw [ha, hj, canonical878 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4205 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4205 node4205Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node708 node708Labels + mixedMoment B node764 node764Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw879 singletonSmall4205
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4205) = raw879Labels := by decide +kernel
  rw [hl, canonical879 B hB] at h
  have hc0 : mixedMoment B raw879 (Fin.cases (0 : Fin 2) singletonSmall4205) =
      mixedMoment B node708 node708Labels := by
    have ha : raw879 = raw880 := by apply Matrix.ext; unfold raw879 raw880; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4205 = raw880Labels := by decide +kernel
    rw [ha, hj, canonical880 B hB]
  have hc1 : mixedMoment B raw879 (Fin.cases (1 : Fin 2) singletonSmall4205) =
      mixedMoment B node764 node764Labels := by
    have ha : raw879 = raw881 := by apply Matrix.ext; unfold raw879 raw881; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4205 = raw881Labels := by decide +kernel
    rw [ha, hj, canonical881 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4234 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4234 node4234Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node734 node734Labels + mixedMoment B node800 node800Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw936 singletonSmall4234
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4234) = raw936Labels := by decide +kernel
  rw [hl, canonical936 B hB] at h
  have hc0 : mixedMoment B raw936 (Fin.cases (0 : Fin 2) singletonSmall4234) =
      mixedMoment B node734 node734Labels := by
    have ha : raw936 = raw937 := by apply Matrix.ext; unfold raw936 raw937; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4234 = raw937Labels := by decide +kernel
    rw [ha, hj, canonical937 B hB]
  have hc1 : mixedMoment B raw936 (Fin.cases (1 : Fin 2) singletonSmall4234) =
      mixedMoment B node800 node800Labels := by
    have ha : raw936 = raw938 := by apply Matrix.ext; unfold raw936 raw938; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4234 = raw938Labels := by decide +kernel
    rw [ha, hj, canonical938 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4242 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4242 node4242Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node742 node742Labels + mixedMoment B node843 node843Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw960 singletonSmall4242
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4242) = raw960Labels := by decide +kernel
  rw [hl, canonical960 B hB] at h
  have hc0 : mixedMoment B raw960 (Fin.cases (0 : Fin 2) singletonSmall4242) =
      mixedMoment B node742 node742Labels := by
    have ha : raw960 = raw961 := by apply Matrix.ext; unfold raw960 raw961; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4242 = raw961Labels := by decide +kernel
    rw [ha, hj, canonical961 B hB]
  have hc1 : mixedMoment B raw960 (Fin.cases (1 : Fin 2) singletonSmall4242) =
      mixedMoment B node843 node843Labels := by
    have ha : raw960 = raw962 := by apply Matrix.ext; unfold raw960 raw962; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4242 = raw962Labels := by decide +kernel
    rw [ha, hj, canonical962 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4243 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4243 node4243Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node743 node743Labels + mixedMoment B node844 node844Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw963 singletonSmall4243
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4243) = raw963Labels := by decide +kernel
  rw [hl, canonical963 B hB] at h
  have hc0 : mixedMoment B raw963 (Fin.cases (0 : Fin 2) singletonSmall4243) =
      mixedMoment B node743 node743Labels := by
    have ha : raw963 = raw964 := by apply Matrix.ext; unfold raw963 raw964; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4243 = raw964Labels := by decide +kernel
    rw [ha, hj, canonical964 B hB]
  have hc1 : mixedMoment B raw963 (Fin.cases (1 : Fin 2) singletonSmall4243) =
      mixedMoment B node844 node844Labels := by
    have ha : raw963 = raw965 := by apply Matrix.ext; unfold raw963 raw965; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4243 = raw965Labels := by decide +kernel
    rw [ha, hj, canonical965 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4265 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4265 node4265Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node807 node807Labels + mixedMoment B node807 node807Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw990 singletonSmall4265
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4265) = raw990Labels := by decide +kernel
  rw [hl, canonical990 B hB] at h
  have hc0 : mixedMoment B raw990 (Fin.cases (0 : Fin 2) singletonSmall4265) =
      mixedMoment B node807 node807Labels := by
    have ha : raw990 = raw991 := by apply Matrix.ext; unfold raw990 raw991; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4265 = raw991Labels := by decide +kernel
    rw [ha, hj, canonical991 B hB]
  have hc1 : mixedMoment B raw990 (Fin.cases (1 : Fin 2) singletonSmall4265) =
      mixedMoment B node807 node807Labels := by
    have ha : raw990 = raw992 := by apply Matrix.ext; unfold raw990 raw992; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4265 = raw992Labels := by decide +kernel
    rw [ha, hj, canonical992 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4270 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4270 node4270Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node813 node813Labels + mixedMoment B node853 node853Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw996 singletonSmall4270
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4270) = raw996Labels := by decide +kernel
  rw [hl, canonical996 B hB] at h
  have hc0 : mixedMoment B raw996 (Fin.cases (0 : Fin 2) singletonSmall4270) =
      mixedMoment B node813 node813Labels := by
    have ha : raw996 = raw997 := by apply Matrix.ext; unfold raw996 raw997; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4270 = raw997Labels := by decide +kernel
    rw [ha, hj, canonical997 B hB]
  have hc1 : mixedMoment B raw996 (Fin.cases (1 : Fin 2) singletonSmall4270) =
      mixedMoment B node853 node853Labels := by
    have ha : raw996 = raw998 := by apply Matrix.ext; unfold raw996 raw998; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4270 = raw998Labels := by decide +kernel
    rw [ha, hj, canonical998 B hB]
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

theorem singleton4419 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4419 node4419Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1000 node1000Labels + mixedMoment B node1605 node1605Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1230 singletonSmall4419
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4419) = raw1230Labels := by decide +kernel
  rw [hl, canonical1230 B hB] at h
  have hc0 : mixedMoment B raw1230 (Fin.cases (0 : Fin 2) singletonSmall4419) =
      mixedMoment B node1000 node1000Labels := by
    have ha : raw1230 = raw1231 := by apply Matrix.ext; unfold raw1230 raw1231; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4419 = raw1231Labels := by decide +kernel
    rw [ha, hj, canonical1231 B hB]
  have hc1 : mixedMoment B raw1230 (Fin.cases (1 : Fin 2) singletonSmall4419) =
      mixedMoment B node1605 node1605Labels := by
    have ha : raw1230 = raw1232 := by apply Matrix.ext; unfold raw1230 raw1232; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4419 = raw1232Labels := by decide +kernel
    rw [ha, hj, canonical1232 B hB]
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

theorem sound664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node664 node664Labels = Sparse.eval nodeValue664 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 664) = mixedMoment B node664 node664Labels := rfl
  simpa [nodeValue664, Sparse.eval] using hc.symm

theorem sound684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node684 node684Labels = Sparse.eval nodeValue684 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 684) = mixedMoment B node684 node684Labels := rfl
  simpa [nodeValue684, Sparse.eval] using hc.symm

theorem sound685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node685 node685Labels = Sparse.eval nodeValue685 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 685) = mixedMoment B node685 node685Labels := rfl
  simpa [nodeValue685, Sparse.eval] using hc.symm

theorem sound700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node700 node700Labels = Sparse.eval nodeValue700 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 700) = mixedMoment B node700 node700Labels := rfl
  simpa [nodeValue700, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node707 node707Labels = Sparse.eval nodeValue707 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 707) = mixedMoment B node707 node707Labels := rfl
  simpa [nodeValue707, Sparse.eval] using hc.symm

theorem sound708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node708 node708Labels = Sparse.eval nodeValue708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 708) = mixedMoment B node708 node708Labels := rfl
  simpa [nodeValue708, Sparse.eval] using hc.symm

theorem sound734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node734 node734Labels = Sparse.eval nodeValue734 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 734) = mixedMoment B node734 node734Labels := rfl
  simpa [nodeValue734, Sparse.eval] using hc.symm

theorem sound742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node742 node742Labels = Sparse.eval nodeValue742 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 742) = mixedMoment B node742 node742Labels := rfl
  simpa [nodeValue742, Sparse.eval] using hc.symm

theorem sound743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node743 node743Labels = Sparse.eval nodeValue743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 743) = mixedMoment B node743 node743Labels := rfl
  simpa [nodeValue743, Sparse.eval] using hc.symm

theorem sound749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node749 node749Labels = Sparse.eval nodeValue749 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 749) = mixedMoment B node749 node749Labels := rfl
  simpa [nodeValue749, Sparse.eval] using hc.symm

theorem sound763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node763 node763Labels = Sparse.eval nodeValue763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 763) = mixedMoment B node763 node763Labels := rfl
  simpa [nodeValue763, Sparse.eval] using hc.symm

theorem sound764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node764 node764Labels = Sparse.eval nodeValue764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 764) = mixedMoment B node764 node764Labels := rfl
  simpa [nodeValue764, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node800 node800Labels = Sparse.eval nodeValue800 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 800) = mixedMoment B node800 node800Labels := rfl
  simpa [nodeValue800, Sparse.eval] using hc.symm

theorem sound807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node807 node807Labels = Sparse.eval nodeValue807 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 807) = mixedMoment B node807 node807Labels := rfl
  simpa [nodeValue807, Sparse.eval] using hc.symm

theorem sound813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node813 node813Labels = Sparse.eval nodeValue813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 813) = mixedMoment B node813 node813Labels := rfl
  simpa [nodeValue813, Sparse.eval] using hc.symm

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

theorem sound843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node843 node843Labels = Sparse.eval nodeValue843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 843) = mixedMoment B node843 node843Labels := rfl
  simpa [nodeValue843, Sparse.eval] using hc.symm

theorem sound844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node844 node844Labels = Sparse.eval nodeValue844 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 844) = mixedMoment B node844 node844Labels := rfl
  simpa [nodeValue844, Sparse.eval] using hc.symm

theorem sound853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node853 node853Labels = Sparse.eval nodeValue853 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 853) = mixedMoment B node853 node853Labels := rfl
  simpa [nodeValue853, Sparse.eval] using hc.symm

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

theorem sound1000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1000 node1000Labels = Sparse.eval nodeValue1000 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1000) = mixedMoment B node1000 node1000Labels := rfl
  simpa [nodeValue1000, Sparse.eval] using hc.symm

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

theorem sound1075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1075 node1075Labels = Sparse.eval nodeValue1075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1075) = mixedMoment B node1075 node1075Labels := rfl
  simpa [nodeValue1075, Sparse.eval] using hc.symm

theorem sound1083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1083 node1083Labels = Sparse.eval nodeValue1083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1083) = mixedMoment B node1083 node1083Labels := rfl
  simpa [nodeValue1083, Sparse.eval] using hc.symm

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

theorem sound1605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1605 node1605Labels = Sparse.eval nodeValue1605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1605) = mixedMoment B node1605 node1605Labels := rfl
  simpa [nodeValue1605, Sparse.eval] using hc.symm

theorem sound1653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1653 node1653Labels = Sparse.eval nodeValue1653 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1653) = mixedMoment B node1653 node1653Labels := rfl
  simpa [nodeValue1653, Sparse.eval] using hc.symm

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

theorem sound539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node539 node539Labels = Sparse.eval nodeValue539 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 539) = mixedMoment B node539 node539Labels := rfl
  simpa [nodeValue539, Sparse.eval] using hc.symm

theorem sound547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node547 node547Labels = Sparse.eval nodeValue547 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 547) = mixedMoment B node547 node547Labels := rfl
  simpa [nodeValue547, Sparse.eval] using hc.symm

theorem sound548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node548 node548Labels = Sparse.eval nodeValue548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 548) = mixedMoment B node548 node548Labels := rfl
  simpa [nodeValue548, Sparse.eval] using hc.symm

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

theorem sound4069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4069 node4069Labels = Sparse.eval nodeValue4069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4069) = mixedMoment B node4069 node4069Labels := rfl
  simpa [nodeValue4069, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4130 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4130 node4130Labels = 0 := by
  exact mixedMoment_order_one B hB node4130 node4130Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4102 node4102Labels = Sparse.eval nodeValue4102 (mixedVector B) := by
  have h := singleton4102 B _hB
  rw [sound539 B _hB _hF, sound664 B _hB _hF] at h
  norm_num [nodeValue4102, nodeValue539, nodeValue664, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4110 node4110Labels = Sparse.eval nodeValue4110 (mixedVector B) := by
  have h := singleton4110 B _hB
  rw [sound547 B _hB _hF, sound684 B _hB _hF] at h
  norm_num [nodeValue4110, nodeValue547, nodeValue684, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4111 node4111Labels = Sparse.eval nodeValue4111 (mixedVector B) := by
  have h := singleton4111 B _hB
  rw [sound548 B _hB _hF, sound685 B _hB _hF] at h
  norm_num [nodeValue4111, nodeValue548, nodeValue685, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4130 node4130Labels = Sparse.eval nodeValue4130 (mixedVector B) := by
  simpa only [nodeValue4130, Sparse.eval_nil] using zero4130 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4221 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4221 node4221Labels = 0 := by
  exact mixedMoment_order_one B hB node4221 node4221Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4197 node4197Labels = Sparse.eval nodeValue4197 (mixedVector B) := by
  have h := singleton4197 B _hB
  rw [sound700 B _hB _hF, sound749 B _hB _hF] at h
  norm_num [nodeValue4197, nodeValue700, nodeValue749, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4204 node4204Labels = Sparse.eval nodeValue4204 (mixedVector B) := by
  have h := singleton4204 B _hB
  rw [sound707 B _hB _hF, sound763 B _hB _hF] at h
  norm_num [nodeValue4204, nodeValue707, nodeValue763, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4205 node4205Labels = Sparse.eval nodeValue4205 (mixedVector B) := by
  have h := singleton4205 B _hB
  rw [sound708 B _hB _hF, sound764 B _hB _hF] at h
  norm_num [nodeValue4205, nodeValue708, nodeValue764, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4221 node4221Labels = Sparse.eval nodeValue4221 (mixedVector B) := by
  simpa only [nodeValue4221, Sparse.eval_nil] using zero4221 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4264 node4264Labels = 0 := by
  exact mixedMoment_order_one B hB node4264 node4264Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4269 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4269 node4269Labels = 0 := by
  exact mixedMoment_order_one B hB node4269 node4269Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4283 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4283 node4283Labels = 0 := by
  exact mixedMoment_order_one B hB node4283 node4283Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4234 node4234Labels = Sparse.eval nodeValue4234 (mixedVector B) := by
  have h := singleton4234 B _hB
  rw [sound734 B _hB _hF, sound800 B _hB _hF] at h
  norm_num [nodeValue4234, nodeValue734, nodeValue800, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4242 node4242Labels = Sparse.eval nodeValue4242 (mixedVector B) := by
  have h := singleton4242 B _hB
  rw [sound742 B _hB _hF, sound843 B _hB _hF] at h
  norm_num [nodeValue4242, nodeValue742, nodeValue843, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4243 node4243Labels = Sparse.eval nodeValue4243 (mixedVector B) := by
  have h := singleton4243 B _hB
  rw [sound743 B _hB _hF, sound844 B _hB _hF] at h
  norm_num [nodeValue4243, nodeValue743, nodeValue844, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4264 node4264Labels = Sparse.eval nodeValue4264 (mixedVector B) := by
  simpa only [nodeValue4264, Sparse.eval_nil] using zero4264 B _hB _hF

theorem sound4265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4265 node4265Labels = Sparse.eval nodeValue4265 (mixedVector B) := by
  have h := singleton4265 B _hB
  rw [sound807 B _hB _hF] at h
  norm_num [nodeValue4265, nodeValue807, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4269 node4269Labels = Sparse.eval nodeValue4269 (mixedVector B) := by
  simpa only [nodeValue4269, Sparse.eval_nil] using zero4269 B _hB _hF

theorem sound4270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4270 node4270Labels = Sparse.eval nodeValue4270 (mixedVector B) := by
  have h := singleton4270 B _hB
  rw [sound813 B _hB _hF, sound853 B _hB _hF] at h
  norm_num [nodeValue4270, nodeValue813, nodeValue853, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4283 node4283Labels = Sparse.eval nodeValue4283 (mixedVector B) := by
  simpa only [nodeValue4283, Sparse.eval_nil] using zero4283 B _hB _hF

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

theorem sound4419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4419 node4419Labels = Sparse.eval nodeValue4419 (mixedVector B) := by
  have h := singleton4419 B _hB
  rw [sound1000 B _hB _hF, sound1605 B _hB _hF] at h
  norm_num [nodeValue4419, nodeValue1000, nodeValue1605, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources49
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1569 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1569 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1569 + difference 0 1) (sourceB1569 + difference 1 0) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4491) := by
    have ha : (tripleCharges (sourceA1569 + difference 0 1) (sourceB1569 + difference 1 0) sourceC1569) = raw23694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23694; decide +kernel
    rw [ha]
    exact (canonical23694 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1569 + difference 0 2) (sourceB1569 + difference 2 0) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1569 + difference 0 2) (sourceB1569 + difference 2 0) sourceC1569) = raw23695 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23695; decide +kernel
    rw [ha]
    exact (canonical23695 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1569 + difference 0 3) (sourceB1569 + difference 3 0) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1569 + difference 0 3) (sourceB1569 + difference 3 0) sourceC1569) = raw23696 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23696; decide +kernel
    rw [ha]
    exact (canonical23696 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1569 + difference 0 4) (sourceB1569 + difference 4 0) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1569 + difference 0 4) (sourceB1569 + difference 4 0) sourceC1569) = raw23697 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23697; decide +kernel
    rw [ha]
    exact (canonical23697 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1569 + difference 0 5) (sourceB1569 + difference 5 0) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1569 + difference 0 5) (sourceB1569 + difference 5 0) sourceC1569) = raw23698 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23698; decide +kernel
    rw [ha]
    exact (canonical23698 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1569 + difference 1 0) (sourceB1569 + difference 0 1) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4130) := by
    have ha : (tripleCharges (sourceA1569 + difference 1 0) (sourceB1569 + difference 0 1) sourceC1569) = raw23699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23699; decide +kernel
    rw [ha]
    exact (canonical23699 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1569 + difference 1 2) (sourceB1569 + difference 2 1) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4221) := by
    have ha : (tripleCharges (sourceA1569 + difference 1 2) (sourceB1569 + difference 2 1) sourceC1569) = raw23700 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23700; decide +kernel
    rw [ha]
    exact (canonical23700 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1569 + difference 1 3) (sourceB1569 + difference 3 1) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4221) := by
    have ha : (tripleCharges (sourceA1569 + difference 1 3) (sourceB1569 + difference 3 1) sourceC1569) = raw23701 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23701; decide +kernel
    rw [ha]
    exact (canonical23701 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1569 + difference 1 4) (sourceB1569 + difference 4 1) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4283) := by
    have ha : (tripleCharges (sourceA1569 + difference 1 4) (sourceB1569 + difference 4 1) sourceC1569) = raw23702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23702; decide +kernel
    rw [ha]
    exact (canonical23702 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1569 + difference 1 5) (sourceB1569 + difference 5 1) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1569 + difference 1 5) (sourceB1569 + difference 5 1) sourceC1569) = raw23703 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23703; decide +kernel
    rw [ha]
    exact (canonical23703 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1569 + difference 2 0) (sourceB1569 + difference 0 2) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4102) := by
    have ha : (tripleCharges (sourceA1569 + difference 2 0) (sourceB1569 + difference 0 2) sourceC1569) = raw23704 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23704; decide +kernel
    rw [ha]
    exact (canonical23704 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1569 + difference 2 1) (sourceB1569 + difference 1 2) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4234) := by
    have ha : (tripleCharges (sourceA1569 + difference 2 1) (sourceB1569 + difference 1 2) sourceC1569) = raw23705 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23705; decide +kernel
    rw [ha]
    exact (canonical23705 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1569 + difference 2 3) (sourceB1569 + difference 3 2) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4197) := by
    have ha : (tripleCharges (sourceA1569 + difference 2 3) (sourceB1569 + difference 3 2) sourceC1569) = raw23706 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23706; decide +kernel
    rw [ha]
    exact (canonical23706 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1569 + difference 2 4) (sourceB1569 + difference 4 2) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4265) := by
    have ha : (tripleCharges (sourceA1569 + difference 2 4) (sourceB1569 + difference 4 2) sourceC1569) = raw23707 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23707; decide +kernel
    rw [ha]
    exact (canonical23707 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1569 + difference 2 5) (sourceB1569 + difference 5 2) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4264) := by
    have ha : (tripleCharges (sourceA1569 + difference 2 5) (sourceB1569 + difference 5 2) sourceC1569) = raw23708 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23708; decide +kernel
    rw [ha]
    exact (canonical23708 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1569 + difference 3 0) (sourceB1569 + difference 0 3) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4102) := by
    have ha : (tripleCharges (sourceA1569 + difference 3 0) (sourceB1569 + difference 0 3) sourceC1569) = raw23709 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23709; decide +kernel
    rw [ha]
    exact (canonical23709 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1569 + difference 3 1) (sourceB1569 + difference 1 3) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4234) := by
    have ha : (tripleCharges (sourceA1569 + difference 3 1) (sourceB1569 + difference 1 3) sourceC1569) = raw23710 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23710; decide +kernel
    rw [ha]
    exact (canonical23710 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1569 + difference 3 2) (sourceB1569 + difference 2 3) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4197) := by
    have ha : (tripleCharges (sourceA1569 + difference 3 2) (sourceB1569 + difference 2 3) sourceC1569) = raw23711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23711; decide +kernel
    rw [ha]
    exact (canonical23711 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1569 + difference 3 4) (sourceB1569 + difference 4 3) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4265) := by
    have ha : (tripleCharges (sourceA1569 + difference 3 4) (sourceB1569 + difference 4 3) sourceC1569) = raw23712 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23712; decide +kernel
    rw [ha]
    exact (canonical23712 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1569 + difference 3 5) (sourceB1569 + difference 5 3) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4264) := by
    have ha : (tripleCharges (sourceA1569 + difference 3 5) (sourceB1569 + difference 5 3) sourceC1569) = raw23713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23713; decide +kernel
    rw [ha]
    exact (canonical23713 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1569 + difference 4 0) (sourceB1569 + difference 0 4) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4110) := by
    have ha : (tripleCharges (sourceA1569 + difference 4 0) (sourceB1569 + difference 0 4) sourceC1569) = raw23714 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23714; decide +kernel
    rw [ha]
    exact (canonical23714 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1569 + difference 4 1) (sourceB1569 + difference 1 4) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4242) := by
    have ha : (tripleCharges (sourceA1569 + difference 4 1) (sourceB1569 + difference 1 4) sourceC1569) = raw23715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23715; decide +kernel
    rw [ha]
    exact (canonical23715 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1569 + difference 4 2) (sourceB1569 + difference 2 4) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4204) := by
    have ha : (tripleCharges (sourceA1569 + difference 4 2) (sourceB1569 + difference 2 4) sourceC1569) = raw23716 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23716; decide +kernel
    rw [ha]
    exact (canonical23716 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1569 + difference 4 3) (sourceB1569 + difference 3 4) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4204) := by
    have ha : (tripleCharges (sourceA1569 + difference 4 3) (sourceB1569 + difference 3 4) sourceC1569) = raw23717 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23717; decide +kernel
    rw [ha]
    exact (canonical23717 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1569 + difference 4 5) (sourceB1569 + difference 5 4) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4269) := by
    have ha : (tripleCharges (sourceA1569 + difference 4 5) (sourceB1569 + difference 5 4) sourceC1569) = raw23718 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23718; decide +kernel
    rw [ha]
    exact (canonical23718 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1569 + difference 5 0) (sourceB1569 + difference 0 5) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4111) := by
    have ha : (tripleCharges (sourceA1569 + difference 5 0) (sourceB1569 + difference 0 5) sourceC1569) = raw23719 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23719; decide +kernel
    rw [ha]
    exact (canonical23719 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1569 + difference 5 1) (sourceB1569 + difference 1 5) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4243) := by
    have ha : (tripleCharges (sourceA1569 + difference 5 1) (sourceB1569 + difference 1 5) sourceC1569) = raw23720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23720; decide +kernel
    rw [ha]
    exact (canonical23720 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1569 + difference 5 2) (sourceB1569 + difference 2 5) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4205) := by
    have ha : (tripleCharges (sourceA1569 + difference 5 2) (sourceB1569 + difference 2 5) sourceC1569) = raw23721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23721; decide +kernel
    rw [ha]
    exact (canonical23721 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1569 + difference 5 3) (sourceB1569 + difference 3 5) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4205) := by
    have ha : (tripleCharges (sourceA1569 + difference 5 3) (sourceB1569 + difference 3 5) sourceC1569) = raw23722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23722; decide +kernel
    rw [ha]
    exact (canonical23722 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1569 + difference 5 4) (sourceB1569 + difference 4 5) sourceC1569) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4270) := by
    have ha : (tripleCharges (sourceA1569 + difference 5 4) (sourceB1569 + difference 4 5) sourceC1569) = raw23723 := by
      apply Matrix.ext; unfold tripleCharges sourceA1569 sourceB1569 sourceC1569 difference raw23723; decide +kernel
    rw [ha]
    exact (canonical23723 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1569 sourceB1569 sourceC1569
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1569, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1335 : Integer.Sparse.reindex keyMap MixedData.row1335 = numericRow1335 := by decide +kernel

theorem numericCheck1335 (x : Master → ℝ) : Integer.Sparse.eval numericRow1335 x =
    (4 : ℝ) * reducedSource1335 x := by
  norm_num [numericRow1335, reducedSource1335, Integer.Sparse.eval, Sparse.eval, nodeValue4069, nodeValue4102, nodeValue4110, nodeValue4111, nodeValue4130, nodeValue4197, nodeValue4204, nodeValue4205, nodeValue4221, nodeValue4234, nodeValue4242, nodeValue4243, nodeValue4264, nodeValue4265, nodeValue4269, nodeValue4270, nodeValue4283, nodeValue4419, nodeValue4491, nodeValue4498, nodeValue4499] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1335 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1335 (mixedVector B) = 0 := by
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  have h4102 : mixedVector B (Sum.inr 4102) = Sparse.eval nodeValue4102 (mixedVector B) := by
    change mixedMoment B node4102 node4102Labels = _
    exact sound4102 B hB hF
  have h4110 : mixedVector B (Sum.inr 4110) = Sparse.eval nodeValue4110 (mixedVector B) := by
    change mixedMoment B node4110 node4110Labels = _
    exact sound4110 B hB hF
  have h4111 : mixedVector B (Sum.inr 4111) = Sparse.eval nodeValue4111 (mixedVector B) := by
    change mixedMoment B node4111 node4111Labels = _
    exact sound4111 B hB hF
  have h4130 : mixedVector B (Sum.inr 4130) = Sparse.eval nodeValue4130 (mixedVector B) := by
    change mixedMoment B node4130 node4130Labels = _
    exact sound4130 B hB hF
  have h4197 : mixedVector B (Sum.inr 4197) = Sparse.eval nodeValue4197 (mixedVector B) := by
    change mixedMoment B node4197 node4197Labels = _
    exact sound4197 B hB hF
  have h4204 : mixedVector B (Sum.inr 4204) = Sparse.eval nodeValue4204 (mixedVector B) := by
    change mixedMoment B node4204 node4204Labels = _
    exact sound4204 B hB hF
  have h4205 : mixedVector B (Sum.inr 4205) = Sparse.eval nodeValue4205 (mixedVector B) := by
    change mixedMoment B node4205 node4205Labels = _
    exact sound4205 B hB hF
  have h4221 : mixedVector B (Sum.inr 4221) = Sparse.eval nodeValue4221 (mixedVector B) := by
    change mixedMoment B node4221 node4221Labels = _
    exact sound4221 B hB hF
  have h4234 : mixedVector B (Sum.inr 4234) = Sparse.eval nodeValue4234 (mixedVector B) := by
    change mixedMoment B node4234 node4234Labels = _
    exact sound4234 B hB hF
  have h4242 : mixedVector B (Sum.inr 4242) = Sparse.eval nodeValue4242 (mixedVector B) := by
    change mixedMoment B node4242 node4242Labels = _
    exact sound4242 B hB hF
  have h4243 : mixedVector B (Sum.inr 4243) = Sparse.eval nodeValue4243 (mixedVector B) := by
    change mixedMoment B node4243 node4243Labels = _
    exact sound4243 B hB hF
  have h4264 : mixedVector B (Sum.inr 4264) = Sparse.eval nodeValue4264 (mixedVector B) := by
    change mixedMoment B node4264 node4264Labels = _
    exact sound4264 B hB hF
  have h4265 : mixedVector B (Sum.inr 4265) = Sparse.eval nodeValue4265 (mixedVector B) := by
    change mixedMoment B node4265 node4265Labels = _
    exact sound4265 B hB hF
  have h4269 : mixedVector B (Sum.inr 4269) = Sparse.eval nodeValue4269 (mixedVector B) := by
    change mixedMoment B node4269 node4269Labels = _
    exact sound4269 B hB hF
  have h4270 : mixedVector B (Sum.inr 4270) = Sparse.eval nodeValue4270 (mixedVector B) := by
    change mixedMoment B node4270 node4270Labels = _
    exact sound4270 B hB hF
  have h4283 : mixedVector B (Sum.inr 4283) = Sparse.eval nodeValue4283 (mixedVector B) := by
    change mixedMoment B node4283 node4283Labels = _
    exact sound4283 B hB hF
  have h4419 : mixedVector B (Sum.inr 4419) = Sparse.eval nodeValue4419 (mixedVector B) := by
    change mixedMoment B node4419 node4419Labels = _
    exact sound4419 B hB hF
  have h4491 : mixedVector B (Sum.inr 4491) = Sparse.eval nodeValue4491 (mixedVector B) := by
    change mixedMoment B node4491 node4491Labels = _
    exact sound4491 B hB hF
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
  have h4499 : mixedVector B (Sum.inr 4499) = Sparse.eval nodeValue4499 (mixedVector B) := by
    change mixedMoment B node4499 node4499Labels = _
    exact sound4499 B hB hF
  simpa only [sourceForm1569, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4069, h4102, h4110, h4111, h4130, h4197, h4204, h4205, h4221, h4234, h4242, h4243, h4264, h4265, h4269, h4270, h4283, h4419, h4491, h4498, h4499, reducedSource1335] using sourceEq1569 B hB

theorem rowSound1335_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1335 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1335, numericCheck1335, reducedZero1335 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1335_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1335_e_oai
