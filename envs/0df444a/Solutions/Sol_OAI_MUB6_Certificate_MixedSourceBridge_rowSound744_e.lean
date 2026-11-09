-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound744_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T02:23:10.76528+00:00
-- url     : https://prove2.me/submissions/7ad4d88a-c4c0-43fd-b68a-08fe1c235191

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
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

theorem canonical1422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1422 raw1422Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw1422 raw1422Labels = mixedMoment B raw1422step0 raw1422step0Labels := by
      have ha : raw1422step0 = (fun i j => raw1422 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1422step0 raw1422; decide +kernel
      have hl : raw1422step0Labels = raw1422Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1422 raw1422Labels permutation152 permutation4
    mixedMoment B raw1422step0 raw1422step0Labels = mixedMoment B raw1422step1 raw1422step1Labels := by
      have ha : raw1422step1 = raw1422step0 := by apply Matrix.ext; unfold raw1422step1 raw1422step0; decide +kernel
      have hl : raw1422step0Labels = labelEmbedding7 ∘ raw1422step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1422step0 raw1422step0Labels raw1422step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

theorem canonical1423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1423 raw1423Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw1423 raw1423Labels = mixedMoment B raw1423step0 raw1423step0Labels := by
      have ha : raw1423step0 = (fun i j => raw1423 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1423step0 raw1423; decide +kernel
      have hl : raw1423step0Labels = raw1423Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1423 raw1423Labels permutation152 permutation4
    _ = mixedMoment B node1235 node1235Labels := by rfl

theorem canonical1424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1424 raw1424Labels = mixedMoment B node3292 node3292Labels := by
  calc
    mixedMoment B raw1424 raw1424Labels = mixedMoment B raw1424step0 raw1424step0Labels := by
      have ha : raw1424step0 = (fun i j => raw1424 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1424step0 raw1424; decide +kernel
      have hl : raw1424step0Labels = raw1424Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1424 raw1424Labels permutation152 permutation6
    mixedMoment B raw1424step0 raw1424step0Labels = mixedMoment B raw1424step1 raw1424step1Labels := by
      have ha : raw1424step1 = -raw1424step0 := by apply Matrix.ext; change ∀ i j, raw1424step1 i j = -(raw1424step0 i j); unfold raw1424step1 raw1424step0; decide +kernel
      have hl : raw1424step1Labels = raw1424step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1424step1 raw1424step1Labels = mixedMoment B raw1424step2 raw1424step2Labels := by
      have ha : raw1424step2 = raw1424step1 := by apply Matrix.ext; unfold raw1424step2 raw1424step1; decide +kernel
      have hl : raw1424step1Labels = labelEmbedding1 ∘ raw1424step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1424step1 raw1424step1Labels raw1424step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3292 node3292Labels := by rfl

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

theorem canonical1440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1440 raw1440Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw1440 raw1440Labels = mixedMoment B raw1440step0 raw1440step0Labels := by
      have ha : raw1440step0 = (fun i j => raw1440 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1440step0 raw1440; decide +kernel
      have hl : raw1440step0Labels = raw1440Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1440 raw1440Labels permutation32 permutation4
    mixedMoment B raw1440step0 raw1440step0Labels = mixedMoment B raw1440step1 raw1440step1Labels := by
      have ha : raw1440step1 = raw1440step0 := by apply Matrix.ext; unfold raw1440step1 raw1440step0; decide +kernel
      have hl : raw1440step0Labels = labelEmbedding7 ∘ raw1440step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1440step0 raw1440step0Labels raw1440step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4618 node4618Labels := by rfl

theorem canonical1441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1441 raw1441Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw1441 raw1441Labels = mixedMoment B raw1441step0 raw1441step0Labels := by
      have ha : raw1441step0 = (fun i j => raw1441 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1441step0 raw1441; decide +kernel
      have hl : raw1441step0Labels = raw1441Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1441 raw1441Labels permutation32 permutation4
    _ = mixedMoment B node1293 node1293Labels := by rfl

theorem canonical1442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1442 raw1442Labels = mixedMoment B node3304 node3304Labels := by
  calc
    mixedMoment B raw1442 raw1442Labels = mixedMoment B raw1442step0 raw1442step0Labels := by
      have ha : raw1442step0 = (fun i j => raw1442 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1442step0 raw1442; decide +kernel
      have hl : raw1442step0Labels = raw1442Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1442 raw1442Labels permutation32 permutation6
    mixedMoment B raw1442step0 raw1442step0Labels = mixedMoment B raw1442step1 raw1442step1Labels := by
      have ha : raw1442step1 = -raw1442step0 := by apply Matrix.ext; change ∀ i j, raw1442step1 i j = -(raw1442step0 i j); unfold raw1442step1 raw1442step0; decide +kernel
      have hl : raw1442step1Labels = raw1442step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1442step1 raw1442step1Labels = mixedMoment B raw1442step2 raw1442step2Labels := by
      have ha : raw1442step2 = raw1442step1 := by apply Matrix.ext; unfold raw1442step2 raw1442step1; decide +kernel
      have hl : raw1442step1Labels = labelEmbedding1 ∘ raw1442step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1442step1 raw1442step1Labels raw1442step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3304 node3304Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14221 raw14221Labels = mixedMoment B node5427 node5427Labels := by
  calc
    _ = mixedMoment B node5427 node5427Labels := by rfl

theorem canonical14222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14222 raw14222Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw14222 raw14222Labels = mixedMoment B raw14222step0 raw14222step0Labels := by
      have hz : ∀ j, raw14222 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14222step0 = (fun i j => raw14222 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14222step0 raw14222; decide +kernel
      have hl : raw14222step0Labels = raw14222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14222 raw14222Labels permutation265 hz
    mixedMoment B raw14222step0 raw14222step0Labels = mixedMoment B raw14222step1 raw14222step1Labels := by
      have hz : ∀ i, raw14222step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw14222step1 = (fun i j => raw14222step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw14222step1 raw14222step0; decide +kernel
      have hl : raw14222step1Labels = (fun j => raw14222step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14222step0 raw14222step0Labels permutation4 hz
    mixedMoment B raw14222step1 raw14222step1Labels = mixedMoment B raw14222step2 raw14222step2Labels := by
      have ha : raw14222step2 = raw14222step1 := by apply Matrix.ext; unfold raw14222step2 raw14222step1; decide +kernel
      have hl : raw14222step1Labels = labelEmbedding2 ∘ raw14222step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14222step1 raw14222step1Labels raw14222step2Labels labelEmbedding2 hl
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical14223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14223 raw14223Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw14223 raw14223Labels = mixedMoment B raw14223step0 raw14223step0Labels := by
      have hz : ∀ j, raw14223 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14223step0 = (fun i j => raw14223 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14223step0 raw14223; decide +kernel
      have hl : raw14223step0Labels = raw14223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14223 raw14223Labels permutation265 hz
    mixedMoment B raw14223step0 raw14223step0Labels = mixedMoment B raw14223step1 raw14223step1Labels := by
      have ha : raw14223step1 = (fun i j => raw14223step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14223step1 raw14223step0; decide +kernel
      have hl : raw14223step1Labels = raw14223step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14223step0 raw14223step0Labels permutation32 permutation7
    mixedMoment B raw14223step1 raw14223step1Labels = mixedMoment B raw14223step2 raw14223step2Labels := by
      have ha : raw14223step2 = -raw14223step1 := by apply Matrix.ext; change ∀ i j, raw14223step2 i j = -(raw14223step1 i j); unfold raw14223step2 raw14223step1; decide +kernel
      have hl : raw14223step2Labels = raw14223step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14223step2 raw14223step2Labels = mixedMoment B raw14223step3 raw14223step3Labels := by
      have ha : raw14223step3 = raw14223step2 := by apply Matrix.ext; unfold raw14223step3 raw14223step2; decide +kernel
      have hl : raw14223step2Labels = labelEmbedding10 ∘ raw14223step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14223step2 raw14223step2Labels raw14223step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

theorem canonical14224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14224 raw14224Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw14224 raw14224Labels = mixedMoment B raw14224step0 raw14224step0Labels := by
      have hz : ∀ j, raw14224 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14224step0 = (fun i j => raw14224 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14224step0 raw14224; decide +kernel
      have hl : raw14224step0Labels = raw14224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14224 raw14224Labels permutation265 hz
    mixedMoment B raw14224step0 raw14224step0Labels = mixedMoment B raw14224step1 raw14224step1Labels := by
      have ha : raw14224step1 = (fun i j => raw14224step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14224step1 raw14224step0; decide +kernel
      have hl : raw14224step1Labels = raw14224step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14224step0 raw14224step0Labels permutation34 permutation7
    mixedMoment B raw14224step1 raw14224step1Labels = mixedMoment B raw14224step2 raw14224step2Labels := by
      have ha : raw14224step2 = -raw14224step1 := by apply Matrix.ext; change ∀ i j, raw14224step2 i j = -(raw14224step1 i j); unfold raw14224step2 raw14224step1; decide +kernel
      have hl : raw14224step2Labels = raw14224step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14224step2 raw14224step2Labels = mixedMoment B raw14224step3 raw14224step3Labels := by
      have ha : raw14224step3 = raw14224step2 := by apply Matrix.ext; unfold raw14224step3 raw14224step2; decide +kernel
      have hl : raw14224step2Labels = labelEmbedding10 ∘ raw14224step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14224step2 raw14224step2Labels raw14224step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

theorem canonical14225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14225 raw14225Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw14225 raw14225Labels = mixedMoment B raw14225step0 raw14225step0Labels := by
      have hz : ∀ j, raw14225 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14225step0 = (fun i j => raw14225 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14225step0 raw14225; decide +kernel
      have hl : raw14225step0Labels = raw14225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14225 raw14225Labels permutation265 hz
    mixedMoment B raw14225step0 raw14225step0Labels = mixedMoment B raw14225step1 raw14225step1Labels := by
      have ha : raw14225step1 = (fun i j => raw14225step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14225step1 raw14225step0; decide +kernel
      have hl : raw14225step1Labels = raw14225step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14225step0 raw14225step0Labels permutation36 permutation7
    mixedMoment B raw14225step1 raw14225step1Labels = mixedMoment B raw14225step2 raw14225step2Labels := by
      have ha : raw14225step2 = -raw14225step1 := by apply Matrix.ext; change ∀ i j, raw14225step2 i j = -(raw14225step1 i j); unfold raw14225step2 raw14225step1; decide +kernel
      have hl : raw14225step2Labels = raw14225step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14225step2 raw14225step2Labels = mixedMoment B raw14225step3 raw14225step3Labels := by
      have ha : raw14225step3 = raw14225step2 := by apply Matrix.ext; unfold raw14225step3 raw14225step2; decide +kernel
      have hl : raw14225step2Labels = labelEmbedding10 ∘ raw14225step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14225step2 raw14225step2Labels raw14225step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

theorem canonical14226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14226 raw14226Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw14226 raw14226Labels = mixedMoment B raw14226step0 raw14226step0Labels := by
      have ha : raw14226step0 = (fun i j => raw14226 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14226step0 raw14226; decide +kernel
      have hl : raw14226step0Labels = raw14226Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14226 raw14226Labels permutation176 permutation2
    _ = mixedMoment B node4601 node4601Labels := by rfl

theorem canonical14227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14227 raw14227Labels = mixedMoment B node5100 node5100Labels := by
  calc
    mixedMoment B raw14227 raw14227Labels = mixedMoment B raw14227step0 raw14227step0Labels := by
      have ha : raw14227step0 = (fun i j => raw14227 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14227step0 raw14227; decide +kernel
      have hl : raw14227step0Labels = raw14227Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14227 raw14227Labels permutation176 permutation2
    _ = mixedMoment B node5100 node5100Labels := by rfl

theorem canonical14228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14228 raw14228Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw14228 raw14228Labels = mixedMoment B raw14228step0 raw14228step0Labels := by
      have ha : raw14228step0 = (fun i j => raw14228 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14228step0 raw14228; decide +kernel
      have hl : raw14228step0Labels = raw14228Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14228 raw14228Labels permutation182 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical14229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14229 raw14229Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw14229 raw14229Labels = mixedMoment B raw14229step0 raw14229step0Labels := by
      have ha : raw14229step0 = (fun i j => raw14229 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14229step0 raw14229; decide +kernel
      have hl : raw14229step0Labels = raw14229Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14229 raw14229Labels permutation188 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical14230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14230 raw14230Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw14230 raw14230Labels = mixedMoment B raw14230step0 raw14230step0Labels := by
      have ha : raw14230step0 = (fun i j => raw14230 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14230step0 raw14230; decide +kernel
      have hl : raw14230step0Labels = raw14230Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14230 raw14230Labels permutation194 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical14231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14231 raw14231Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw14231 raw14231Labels = mixedMoment B raw14231step0 raw14231step0Labels := by
      have hz : ∀ j, raw14231 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14231step0 = (fun i j => raw14231 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14231step0 raw14231; decide +kernel
      have hl : raw14231step0Labels = raw14231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14231 raw14231Labels permutation265 hz
    _ = mixedMoment B node4618 node4618Labels := by rfl

theorem canonical14232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14232 raw14232Labels = mixedMoment B node5162 node5162Labels := by
  calc
    _ = mixedMoment B node5162 node5162Labels := by rfl

theorem canonical14233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14233 raw14233Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw14233 raw14233Labels = mixedMoment B raw14233step0 raw14233step0Labels := by
      have hz : ∀ j, raw14233 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14233step0 = (fun i j => raw14233 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14233step0 raw14233; decide +kernel
      have hl : raw14233step0Labels = raw14233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14233 raw14233Labels permutation265 hz
    mixedMoment B raw14233step0 raw14233step0Labels = mixedMoment B raw14233step1 raw14233step1Labels := by
      have ha : raw14233step1 = (fun i j => raw14233step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14233step1 raw14233step0; decide +kernel
      have hl : raw14233step1Labels = raw14233step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14233step0 raw14233step0Labels permutation38 permutation2
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical14234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14234 raw14234Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw14234 raw14234Labels = mixedMoment B raw14234step0 raw14234step0Labels := by
      have hz : ∀ j, raw14234 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14234step0 = (fun i j => raw14234 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14234step0 raw14234; decide +kernel
      have hl : raw14234step0Labels = raw14234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14234 raw14234Labels permutation265 hz
    mixedMoment B raw14234step0 raw14234step0Labels = mixedMoment B raw14234step1 raw14234step1Labels := by
      have ha : raw14234step1 = (fun i j => raw14234step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14234step1 raw14234step0; decide +kernel
      have hl : raw14234step1Labels = raw14234step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14234step0 raw14234step0Labels permutation44 permutation2
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical14235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14235 raw14235Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw14235 raw14235Labels = mixedMoment B raw14235step0 raw14235step0Labels := by
      have hz : ∀ j, raw14235 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14235step0 = (fun i j => raw14235 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14235step0 raw14235; decide +kernel
      have hl : raw14235step0Labels = raw14235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14235 raw14235Labels permutation265 hz
    mixedMoment B raw14235step0 raw14235step0Labels = mixedMoment B raw14235step1 raw14235step1Labels := by
      have ha : raw14235step1 = (fun i j => raw14235step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14235step1 raw14235step0; decide +kernel
      have hl : raw14235step1Labels = raw14235step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14235step0 raw14235step0Labels permutation50 permutation2
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical14236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14236 raw14236Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw14236 raw14236Labels = mixedMoment B raw14236step0 raw14236step0Labels := by
      have hz : ∀ j, raw14236 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14236step0 = (fun i j => raw14236 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14236step0 raw14236; decide +kernel
      have hl : raw14236step0Labels = raw14236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14236 raw14236Labels permutation265 hz
    mixedMoment B raw14236step0 raw14236step0Labels = mixedMoment B raw14236step1 raw14236step1Labels := by
      have ha : raw14236step1 = (fun i j => raw14236step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14236step1 raw14236step0; decide +kernel
      have hl : raw14236step1Labels = raw14236step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14236step0 raw14236step0Labels permutation35 permutation2
    _ = mixedMoment B node4606 node4606Labels := by rfl

theorem canonical14237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14237 raw14237Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw14237 raw14237Labels = mixedMoment B raw14237step0 raw14237step0Labels := by
      have ha : raw14237step0 = (fun i j => raw14237 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14237step0 raw14237; decide +kernel
      have hl : raw14237step0Labels = raw14237Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14237 raw14237Labels permutation155 permutation2
    _ = mixedMoment B node5137 node5137Labels := by rfl

theorem canonical14238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14238 raw14238Labels = mixedMoment B node5104 node5104Labels := by
  calc
    mixedMoment B raw14238 raw14238Labels = mixedMoment B raw14238step0 raw14238step0Labels := by
      have hz : ∀ j, raw14238 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14238step0 = (fun i j => raw14238 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14238step0 raw14238; decide +kernel
      have hl : raw14238step0Labels = raw14238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14238 raw14238Labels permutation265 hz
    mixedMoment B raw14238step0 raw14238step0Labels = mixedMoment B raw14238step1 raw14238step1Labels := by
      have ha : raw14238step1 = (fun i j => raw14238step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14238step1 raw14238step0; decide +kernel
      have hl : raw14238step1Labels = raw14238step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14238step0 raw14238step0Labels permutation35 permutation2
    _ = mixedMoment B node5104 node5104Labels := by rfl

theorem canonical14239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14239 raw14239Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw14239 raw14239Labels = mixedMoment B raw14239step0 raw14239step0Labels := by
      have hz : ∀ j, raw14239 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14239step0 = (fun i j => raw14239 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14239step0 raw14239; decide +kernel
      have hl : raw14239step0Labels = raw14239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14239 raw14239Labels permutation265 hz
    mixedMoment B raw14239step0 raw14239step0Labels = mixedMoment B raw14239step1 raw14239step1Labels := by
      have ha : raw14239step1 = (fun i j => raw14239step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14239step1 raw14239step0; decide +kernel
      have hl : raw14239step1Labels = raw14239step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14239step0 raw14239step0Labels permutation35 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical14240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14240 raw14240Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw14240 raw14240Labels = mixedMoment B raw14240step0 raw14240step0Labels := by
      have hz : ∀ j, raw14240 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14240step0 = (fun i j => raw14240 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14240step0 raw14240; decide +kernel
      have hl : raw14240step0Labels = raw14240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14240 raw14240Labels permutation265 hz
    mixedMoment B raw14240step0 raw14240step0Labels = mixedMoment B raw14240step1 raw14240step1Labels := by
      have ha : raw14240step1 = (fun i j => raw14240step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14240step1 raw14240step0; decide +kernel
      have hl : raw14240step1Labels = raw14240step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14240step0 raw14240step0Labels permutation37 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical14241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14241 raw14241Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw14241 raw14241Labels = mixedMoment B raw14241step0 raw14241step0Labels := by
      have hz : ∀ j, raw14241 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14241step0 = (fun i j => raw14241 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14241step0 raw14241; decide +kernel
      have hl : raw14241step0Labels = raw14241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14241 raw14241Labels permutation265 hz
    mixedMoment B raw14241step0 raw14241step0Labels = mixedMoment B raw14241step1 raw14241step1Labels := by
      have ha : raw14241step1 = (fun i j => raw14241step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14241step1 raw14241step0; decide +kernel
      have hl : raw14241step1Labels = raw14241step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14241step0 raw14241step0Labels permutation33 permutation2
    _ = mixedMoment B node4606 node4606Labels := by rfl

theorem canonical14242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14242 raw14242Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw14242 raw14242Labels = mixedMoment B raw14242step0 raw14242step0Labels := by
      have ha : raw14242step0 = (fun i j => raw14242 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14242step0 raw14242; decide +kernel
      have hl : raw14242step0Labels = raw14242Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14242 raw14242Labels permutation153 permutation2
    _ = mixedMoment B node5137 node5137Labels := by rfl

theorem canonical14243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14243 raw14243Labels = mixedMoment B node5104 node5104Labels := by
  calc
    mixedMoment B raw14243 raw14243Labels = mixedMoment B raw14243step0 raw14243step0Labels := by
      have hz : ∀ j, raw14243 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14243step0 = (fun i j => raw14243 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14243step0 raw14243; decide +kernel
      have hl : raw14243step0Labels = raw14243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14243 raw14243Labels permutation265 hz
    mixedMoment B raw14243step0 raw14243step0Labels = mixedMoment B raw14243step1 raw14243step1Labels := by
      have ha : raw14243step1 = (fun i j => raw14243step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14243step1 raw14243step0; decide +kernel
      have hl : raw14243step1Labels = raw14243step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14243step0 raw14243step0Labels permutation33 permutation2
    _ = mixedMoment B node5104 node5104Labels := by rfl

theorem canonical14244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14244 raw14244Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw14244 raw14244Labels = mixedMoment B raw14244step0 raw14244step0Labels := by
      have hz : ∀ j, raw14244 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14244step0 = (fun i j => raw14244 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14244step0 raw14244; decide +kernel
      have hl : raw14244step0Labels = raw14244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14244 raw14244Labels permutation265 hz
    mixedMoment B raw14244step0 raw14244step0Labels = mixedMoment B raw14244step1 raw14244step1Labels := by
      have ha : raw14244step1 = (fun i j => raw14244step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14244step1 raw14244step0; decide +kernel
      have hl : raw14244step1Labels = raw14244step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14244step0 raw14244step0Labels permutation33 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical14245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14245 raw14245Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw14245 raw14245Labels = mixedMoment B raw14245step0 raw14245step0Labels := by
      have hz : ∀ j, raw14245 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14245step0 = (fun i j => raw14245 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14245step0 raw14245; decide +kernel
      have hl : raw14245step0Labels = raw14245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14245 raw14245Labels permutation265 hz
    mixedMoment B raw14245step0 raw14245step0Labels = mixedMoment B raw14245step1 raw14245step1Labels := by
      have ha : raw14245step1 = (fun i j => raw14245step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14245step1 raw14245step0; decide +kernel
      have hl : raw14245step1Labels = raw14245step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14245step0 raw14245step0Labels permutation36 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical14246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14246 raw14246Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw14246 raw14246Labels = mixedMoment B raw14246step0 raw14246step0Labels := by
      have hz : ∀ j, raw14246 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14246step0 = (fun i j => raw14246 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14246step0 raw14246; decide +kernel
      have hl : raw14246step0Labels = raw14246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14246 raw14246Labels permutation265 hz
    _ = mixedMoment B node4606 node4606Labels := by rfl

theorem canonical14247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14247 raw14247Labels = mixedMoment B node5137 node5137Labels := by
  calc
    _ = mixedMoment B node5137 node5137Labels := by rfl

theorem canonical14248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14248 raw14248Labels = mixedMoment B node5104 node5104Labels := by
  calc
    mixedMoment B raw14248 raw14248Labels = mixedMoment B raw14248step0 raw14248step0Labels := by
      have hz : ∀ j, raw14248 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14248step0 = (fun i j => raw14248 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14248step0 raw14248; decide +kernel
      have hl : raw14248step0Labels = raw14248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14248 raw14248Labels permutation265 hz
    _ = mixedMoment B node5104 node5104Labels := by rfl

theorem canonical14249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14249 raw14249Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw14249 raw14249Labels = mixedMoment B raw14249step0 raw14249step0Labels := by
      have hz : ∀ j, raw14249 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14249step0 = (fun i j => raw14249 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14249step0 raw14249; decide +kernel
      have hl : raw14249step0Labels = raw14249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14249 raw14249Labels permutation265 hz
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical14250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14250 raw14250Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw14250 raw14250Labels = mixedMoment B raw14250step0 raw14250step0Labels := by
      have hz : ∀ j, raw14250 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14250step0 = (fun i j => raw14250 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14250step0 raw14250; decide +kernel
      have hl : raw14250step0Labels = raw14250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14250 raw14250Labels permutation265 hz
    mixedMoment B raw14250step0 raw14250step0Labels = mixedMoment B raw14250step1 raw14250step1Labels := by
      have ha : raw14250step1 = (fun i j => raw14250step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14250step1 raw14250step0; decide +kernel
      have hl : raw14250step1Labels = raw14250step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14250step0 raw14250step0Labels permutation34 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

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

theorem canonical2166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2166 raw2166Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw2166 raw2166Labels = mixedMoment B raw2166step0 raw2166step0Labels := by
      have ha : raw2166step0 = (fun i j => raw2166 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2166step0 raw2166; decide +kernel
      have hl : raw2166step0Labels = raw2166Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2166 raw2166Labels permutation152 permutation4
    mixedMoment B raw2166step0 raw2166step0Labels = mixedMoment B raw2166step1 raw2166step1Labels := by
      have ha : raw2166step1 = raw2166step0 := by apply Matrix.ext; unfold raw2166step1 raw2166step0; decide +kernel
      have hl : raw2166step0Labels = labelEmbedding7 ∘ raw2166step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2166step0 raw2166step0Labels raw2166step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5137 node5137Labels := by rfl

theorem canonical2167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2167 raw2167Labels = mixedMoment B node2556 node2556Labels := by
  calc
    mixedMoment B raw2167 raw2167Labels = mixedMoment B raw2167step0 raw2167step0Labels := by
      have ha : raw2167step0 = (fun i j => raw2167 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2167step0 raw2167; decide +kernel
      have hl : raw2167step0Labels = raw2167Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2167 raw2167Labels permutation152 permutation4
    _ = mixedMoment B node2556 node2556Labels := by rfl

theorem canonical2168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2168 raw2168Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw2168 raw2168Labels = mixedMoment B raw2168step0 raw2168step0Labels := by
      have ha : raw2168step0 = (fun i j => raw2168 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2168step0 raw2168; decide +kernel
      have hl : raw2168step0Labels = raw2168Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2168 raw2168Labels permutation176 permutation6
    mixedMoment B raw2168step0 raw2168step0Labels = mixedMoment B raw2168step1 raw2168step1Labels := by
      have ha : raw2168step1 = -raw2168step0 := by apply Matrix.ext; change ∀ i j, raw2168step1 i j = -(raw2168step0 i j); unfold raw2168step1 raw2168step0; decide +kernel
      have hl : raw2168step1Labels = raw2168step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2168step1 raw2168step1Labels = mixedMoment B raw2168step2 raw2168step2Labels := by
      have ha : raw2168step2 = raw2168step1 := by apply Matrix.ext; unfold raw2168step2 raw2168step1; decide +kernel
      have hl : raw2168step1Labels = labelEmbedding1 ∘ raw2168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2168step1 raw2168step1Labels raw2168step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

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

theorem canonical2187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2187 raw2187Labels = mixedMoment B node5162 node5162Labels := by
  calc
    mixedMoment B raw2187 raw2187Labels = mixedMoment B raw2187step0 raw2187step0Labels := by
      have ha : raw2187step0 = (fun i j => raw2187 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2187step0 raw2187; decide +kernel
      have hl : raw2187step0Labels = raw2187Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2187 raw2187Labels permutation152 permutation4
    mixedMoment B raw2187step0 raw2187step0Labels = mixedMoment B raw2187step1 raw2187step1Labels := by
      have ha : raw2187step1 = raw2187step0 := by apply Matrix.ext; unfold raw2187step1 raw2187step0; decide +kernel
      have hl : raw2187step0Labels = labelEmbedding7 ∘ raw2187step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2187step0 raw2187step0Labels raw2187step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5162 node5162Labels := by rfl

theorem canonical2188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2188 raw2188Labels = mixedMoment B node2589 node2589Labels := by
  calc
    mixedMoment B raw2188 raw2188Labels = mixedMoment B raw2188step0 raw2188step0Labels := by
      have ha : raw2188step0 = (fun i j => raw2188 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2188step0 raw2188; decide +kernel
      have hl : raw2188step0Labels = raw2188Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2188 raw2188Labels permutation152 permutation4
    _ = mixedMoment B node2589 node2589Labels := by rfl

theorem canonical2189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2189 raw2189Labels = mixedMoment B node3563 node3563Labels := by
  calc
    mixedMoment B raw2189 raw2189Labels = mixedMoment B raw2189step0 raw2189step0Labels := by
      have ha : raw2189step0 = (fun i j => raw2189 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2189step0 raw2189; decide +kernel
      have hl : raw2189step0Labels = raw2189Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2189 raw2189Labels permutation176 permutation6
    mixedMoment B raw2189step0 raw2189step0Labels = mixedMoment B raw2189step1 raw2189step1Labels := by
      have ha : raw2189step1 = -raw2189step0 := by apply Matrix.ext; change ∀ i j, raw2189step1 i j = -(raw2189step0 i j); unfold raw2189step1 raw2189step0; decide +kernel
      have hl : raw2189step1Labels = raw2189step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2189step1 raw2189step1Labels = mixedMoment B raw2189step2 raw2189step2Labels := by
      have ha : raw2189step2 = raw2189step1 := by apply Matrix.ext; unfold raw2189step2 raw2189step1; decide +kernel
      have hl : raw2189step1Labels = labelEmbedding1 ∘ raw2189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2189step1 raw2189step1Labels raw2189step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3563 node3563Labels := by rfl

theorem canonical2268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2268 raw2268Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw2268 raw2268Labels = mixedMoment B raw2268step0 raw2268step0Labels := by
      have ha : raw2268step0 = (fun i j => raw2268 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2268step0 raw2268; decide +kernel
      have hl : raw2268step0Labels = raw2268Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2268 raw2268Labels permutation152 permutation4
    mixedMoment B raw2268step0 raw2268step0Labels = mixedMoment B raw2268step1 raw2268step1Labels := by
      have ha : raw2268step1 = raw2268step0 := by apply Matrix.ext; unfold raw2268step1 raw2268step0; decide +kernel
      have hl : raw2268step0Labels = labelEmbedding7 ∘ raw2268step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2268step0 raw2268step0Labels raw2268step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical2269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2269 raw2269Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw2269 raw2269Labels = mixedMoment B raw2269step0 raw2269step0Labels := by
      have ha : raw2269step0 = (fun i j => raw2269 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2269step0 raw2269; decide +kernel
      have hl : raw2269step0Labels = raw2269Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2269 raw2269Labels permutation152 permutation4
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical2270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2270 raw2270Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw2270 raw2270Labels = mixedMoment B raw2270step0 raw2270step0Labels := by
      have ha : raw2270step0 = (fun i j => raw2270 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2270step0 raw2270; decide +kernel
      have hl : raw2270step0Labels = raw2270Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2270 raw2270Labels permutation158 permutation6
    mixedMoment B raw2270step0 raw2270step0Labels = mixedMoment B raw2270step1 raw2270step1Labels := by
      have ha : raw2270step1 = -raw2270step0 := by apply Matrix.ext; change ∀ i j, raw2270step1 i j = -(raw2270step0 i j); unfold raw2270step1 raw2270step0; decide +kernel
      have hl : raw2270step1Labels = raw2270step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2270step1 raw2270step1Labels = mixedMoment B raw2270step2 raw2270step2Labels := by
      have ha : raw2270step2 = raw2270step1 := by apply Matrix.ext; unfold raw2270step2 raw2270step1; decide +kernel
      have hl : raw2270step1Labels = labelEmbedding1 ∘ raw2270step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2270step1 raw2270step1Labels raw2270step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

theorem canonical2274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2274 raw2274Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw2274 raw2274Labels = mixedMoment B raw2274step0 raw2274step0Labels := by
      have ha : raw2274step0 = (fun i j => raw2274 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2274step0 raw2274; decide +kernel
      have hl : raw2274step0Labels = raw2274Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2274 raw2274Labels permutation32 permutation4
    mixedMoment B raw2274step0 raw2274step0Labels = mixedMoment B raw2274step1 raw2274step1Labels := by
      have ha : raw2274step1 = raw2274step0 := by apply Matrix.ext; unfold raw2274step1 raw2274step0; decide +kernel
      have hl : raw2274step0Labels = labelEmbedding7 ∘ raw2274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2274step0 raw2274step0Labels raw2274step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2275 raw2275Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw2275 raw2275Labels = mixedMoment B raw2275step0 raw2275step0Labels := by
      have ha : raw2275step0 = (fun i j => raw2275 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2275step0 raw2275; decide +kernel
      have hl : raw2275step0Labels = raw2275Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2275 raw2275Labels permutation32 permutation4
    _ = mixedMoment B node2723 node2723Labels := by rfl

theorem canonical2276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2276 raw2276Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw2276 raw2276Labels = mixedMoment B raw2276step0 raw2276step0Labels := by
      have ha : raw2276step0 = (fun i j => raw2276 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2276step0 raw2276; decide +kernel
      have hl : raw2276step0Labels = raw2276Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2276 raw2276Labels permutation32 permutation6
    mixedMoment B raw2276step0 raw2276step0Labels = mixedMoment B raw2276step1 raw2276step1Labels := by
      have ha : raw2276step1 = -raw2276step0 := by apply Matrix.ext; change ∀ i j, raw2276step1 i j = -(raw2276step0 i j); unfold raw2276step1 raw2276step0; decide +kernel
      have hl : raw2276step1Labels = raw2276step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2276step1 raw2276step1Labels = mixedMoment B raw2276step2 raw2276step2Labels := by
      have ha : raw2276step2 = raw2276step1 := by apply Matrix.ext; unfold raw2276step2 raw2276step1; decide +kernel
      have hl : raw2276step1Labels = labelEmbedding1 ∘ raw2276step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2276step1 raw2276step1Labels raw2276step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical2292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2292 raw2292Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw2292 raw2292Labels = mixedMoment B raw2292step0 raw2292step0Labels := by
      have ha : raw2292step0 = (fun i j => raw2292 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2292step0 raw2292; decide +kernel
      have hl : raw2292step0Labels = raw2292Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2292 raw2292Labels permutation32 permutation4
    mixedMoment B raw2292step0 raw2292step0Labels = mixedMoment B raw2292step1 raw2292step1Labels := by
      have ha : raw2292step1 = raw2292step0 := by apply Matrix.ext; unfold raw2292step1 raw2292step0; decide +kernel
      have hl : raw2292step0Labels = labelEmbedding7 ∘ raw2292step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2292step0 raw2292step0Labels raw2292step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical2293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2293 raw2293Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw2293 raw2293Labels = mixedMoment B raw2293step0 raw2293step0Labels := by
      have ha : raw2293step0 = (fun i j => raw2293 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2293step0 raw2293; decide +kernel
      have hl : raw2293step0Labels = raw2293Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2293 raw2293Labels permutation32 permutation4
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2294 raw2294Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw2294 raw2294Labels = mixedMoment B raw2294step0 raw2294step0Labels := by
      have ha : raw2294step0 = (fun i j => raw2294 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2294step0 raw2294; decide +kernel
      have hl : raw2294step0Labels = raw2294Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2294 raw2294Labels permutation38 permutation6
    mixedMoment B raw2294step0 raw2294step0Labels = mixedMoment B raw2294step1 raw2294step1Labels := by
      have ha : raw2294step1 = -raw2294step0 := by apply Matrix.ext; change ∀ i j, raw2294step1 i j = -(raw2294step0 i j); unfold raw2294step1 raw2294step0; decide +kernel
      have hl : raw2294step1Labels = raw2294step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2294step1 raw2294step1Labels = mixedMoment B raw2294step2 raw2294step2Labels := by
      have ha : raw2294step2 = raw2294step1 := by apply Matrix.ext; unfold raw2294step2 raw2294step1; decide +kernel
      have hl : raw2294step1Labels = labelEmbedding1 ∘ raw2294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2294step1 raw2294step1Labels raw2294step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

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

theorem singleton4601 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4601 node4601Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1235 node1235Labels + mixedMoment B node3292 node3292Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1422 singletonSmall4601
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4601) = raw1422Labels := by decide +kernel
  rw [hl, canonical1422 B hB] at h
  have hc0 : mixedMoment B raw1422 (Fin.cases (0 : Fin 2) singletonSmall4601) =
      mixedMoment B node1235 node1235Labels := by
    have ha : raw1422 = raw1423 := by apply Matrix.ext; unfold raw1422 raw1423; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4601 = raw1423Labels := by decide +kernel
    rw [ha, hj, canonical1423 B hB]
  have hc1 : mixedMoment B raw1422 (Fin.cases (1 : Fin 2) singletonSmall4601) =
      mixedMoment B node3292 node3292Labels := by
    have ha : raw1422 = raw1424 := by apply Matrix.ext; unfold raw1422 raw1424; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4601 = raw1424Labels := by decide +kernel
    rw [ha, hj, canonical1424 B hB]
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

theorem singleton4618 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4618 node4618Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1293 node1293Labels + mixedMoment B node3304 node3304Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1440 singletonSmall4618
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4618) = raw1440Labels := by decide +kernel
  rw [hl, canonical1440 B hB] at h
  have hc0 : mixedMoment B raw1440 (Fin.cases (0 : Fin 2) singletonSmall4618) =
      mixedMoment B node1293 node1293Labels := by
    have ha : raw1440 = raw1441 := by apply Matrix.ext; unfold raw1440 raw1441; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4618 = raw1441Labels := by decide +kernel
    rw [ha, hj, canonical1441 B hB]
  have hc1 : mixedMoment B raw1440 (Fin.cases (1 : Fin 2) singletonSmall4618) =
      mixedMoment B node3304 node3304Labels := by
    have ha : raw1440 = raw1442 := by apply Matrix.ext; unfold raw1440 raw1442; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4618 = raw1442Labels := by decide +kernel
    rw [ha, hj, canonical1442 B hB]
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

theorem singleton5137 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5137 node5137Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2556 node2556Labels + mixedMoment B node3521 node3521Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2166 singletonSmall5137
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5137) = raw2166Labels := by decide +kernel
  rw [hl, canonical2166 B hB] at h
  have hc0 : mixedMoment B raw2166 (Fin.cases (0 : Fin 2) singletonSmall5137) =
      mixedMoment B node2556 node2556Labels := by
    have ha : raw2166 = raw2167 := by apply Matrix.ext; unfold raw2166 raw2167; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5137 = raw2167Labels := by decide +kernel
    rw [ha, hj, canonical2167 B hB]
  have hc1 : mixedMoment B raw2166 (Fin.cases (1 : Fin 2) singletonSmall5137) =
      mixedMoment B node3521 node3521Labels := by
    have ha : raw2166 = raw2168 := by apply Matrix.ext; unfold raw2166 raw2168; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5137 = raw2168Labels := by decide +kernel
    rw [ha, hj, canonical2168 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5162 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5162 node5162Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2589 node2589Labels + mixedMoment B node3563 node3563Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2187 singletonSmall5162
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5162) = raw2187Labels := by decide +kernel
  rw [hl, canonical2187 B hB] at h
  have hc0 : mixedMoment B raw2187 (Fin.cases (0 : Fin 2) singletonSmall5162) =
      mixedMoment B node2589 node2589Labels := by
    have ha : raw2187 = raw2188 := by apply Matrix.ext; unfold raw2187 raw2188; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5162 = raw2188Labels := by decide +kernel
    rw [ha, hj, canonical2188 B hB]
  have hc1 : mixedMoment B raw2187 (Fin.cases (1 : Fin 2) singletonSmall5162) =
      mixedMoment B node3563 node3563Labels := by
    have ha : raw2187 = raw2189 := by apply Matrix.ext; unfold raw2187 raw2189; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5162 = raw2189Labels := by decide +kernel
    rw [ha, hj, canonical2189 B hB]
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

theorem singleton5257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5257 node5257Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2721 node2721Labels + mixedMoment B node3532 node3532Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2268 singletonSmall5257
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5257) = raw2268Labels := by decide +kernel
  rw [hl, canonical2268 B hB] at h
  have hc0 : mixedMoment B raw2268 (Fin.cases (0 : Fin 2) singletonSmall5257) =
      mixedMoment B node2721 node2721Labels := by
    have ha : raw2268 = raw2269 := by apply Matrix.ext; unfold raw2268 raw2269; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5257 = raw2269Labels := by decide +kernel
    rw [ha, hj, canonical2269 B hB]
  have hc1 : mixedMoment B raw2268 (Fin.cases (1 : Fin 2) singletonSmall5257) =
      mixedMoment B node3532 node3532Labels := by
    have ha : raw2268 = raw2270 := by apply Matrix.ext; unfold raw2268 raw2270; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5257 = raw2270Labels := by decide +kernel
    rw [ha, hj, canonical2270 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5259 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5259 node5259Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2723 node2723Labels + mixedMoment B node3544 node3544Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2274 singletonSmall5259
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5259) = raw2274Labels := by decide +kernel
  rw [hl, canonical2274 B hB] at h
  have hc0 : mixedMoment B raw2274 (Fin.cases (0 : Fin 2) singletonSmall5259) =
      mixedMoment B node2723 node2723Labels := by
    have ha : raw2274 = raw2275 := by apply Matrix.ext; unfold raw2274 raw2275; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5259 = raw2275Labels := by decide +kernel
    rw [ha, hj, canonical2275 B hB]
  have hc1 : mixedMoment B raw2274 (Fin.cases (1 : Fin 2) singletonSmall5259) =
      mixedMoment B node3544 node3544Labels := by
    have ha : raw2274 = raw2276 := by apply Matrix.ext; unfold raw2274 raw2276; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5259 = raw2276Labels := by decide +kernel
    rw [ha, hj, canonical2276 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5290 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5290 node5290Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2764 node2764Labels + mixedMoment B node3581 node3581Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2292 singletonSmall5290
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5290) = raw2292Labels := by decide +kernel
  rw [hl, canonical2292 B hB] at h
  have hc0 : mixedMoment B raw2292 (Fin.cases (0 : Fin 2) singletonSmall5290) =
      mixedMoment B node2764 node2764Labels := by
    have ha : raw2292 = raw2293 := by apply Matrix.ext; unfold raw2292 raw2293; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5290 = raw2293Labels := by decide +kernel
    rw [ha, hj, canonical2293 B hB]
  have hc1 : mixedMoment B raw2292 (Fin.cases (1 : Fin 2) singletonSmall5290) =
      mixedMoment B node3581 node3581Labels := by
    have ha : raw2292 = raw2294 := by apply Matrix.ext; unfold raw2292 raw2294; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5290 = raw2294Labels := by decide +kernel
    rw [ha, hj, canonical2294 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5440 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5440 node5440Labels = 0 := by
  exact mixedMoment_order_one B hB node5440 node5440Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1235 node1235Labels = Sparse.eval nodeValue1235 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1235) = mixedMoment B node1235 node1235Labels := rfl
  simpa [nodeValue1235, Sparse.eval] using hc.symm

theorem sound1240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1240 node1240Labels = Sparse.eval nodeValue1240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1240) = mixedMoment B node1240 node1240Labels := rfl
  simpa [nodeValue1240, Sparse.eval] using hc.symm

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

theorem sound1293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1293 node1293Labels = Sparse.eval nodeValue1293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1293) = mixedMoment B node1293 node1293Labels := rfl
  simpa [nodeValue1293, Sparse.eval] using hc.symm

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

theorem sound2556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2556 node2556Labels = Sparse.eval nodeValue2556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2556) = mixedMoment B node2556 node2556Labels := rfl
  simpa [nodeValue2556, Sparse.eval] using hc.symm

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

theorem sound2589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2589 node2589Labels = Sparse.eval nodeValue2589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2589) = mixedMoment B node2589 node2589Labels := rfl
  simpa [nodeValue2589, Sparse.eval] using hc.symm

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

theorem sound2721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2721 node2721Labels = Sparse.eval nodeValue2721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2721) = mixedMoment B node2721 node2721Labels := rfl
  simpa [nodeValue2721, Sparse.eval] using hc.symm

theorem sound2723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2723 node2723Labels = Sparse.eval nodeValue2723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2723) = mixedMoment B node2723 node2723Labels := rfl
  simpa [nodeValue2723, Sparse.eval] using hc.symm

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

theorem sound2764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2764 node2764Labels = Sparse.eval nodeValue2764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2764) = mixedMoment B node2764 node2764Labels := rfl
  simpa [nodeValue2764, Sparse.eval] using hc.symm

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

theorem sound3292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3292 node3292Labels = Sparse.eval nodeValue3292 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3292) = mixedMoment B node3292 node3292Labels := rfl
  simpa [nodeValue3292, Sparse.eval] using hc.symm

theorem sound3299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3299 node3299Labels = Sparse.eval nodeValue3299 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3299) = mixedMoment B node3299 node3299Labels := rfl
  simpa [nodeValue3299, Sparse.eval] using hc.symm

theorem sound3304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3304 node3304Labels = Sparse.eval nodeValue3304 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3304) = mixedMoment B node3304 node3304Labels := rfl
  simpa [nodeValue3304, Sparse.eval] using hc.symm

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

theorem sound3521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3521 node3521Labels = Sparse.eval nodeValue3521 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3521) = mixedMoment B node3521 node3521Labels := rfl
  simpa [nodeValue3521, Sparse.eval] using hc.symm

theorem sound3532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3532 node3532Labels = Sparse.eval nodeValue3532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3532) = mixedMoment B node3532 node3532Labels := rfl
  simpa [nodeValue3532, Sparse.eval] using hc.symm

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

theorem sound3563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3563 node3563Labels = Sparse.eval nodeValue3563 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3563) = mixedMoment B node3563 node3563Labels := rfl
  simpa [nodeValue3563, Sparse.eval] using hc.symm

theorem sound3581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3581 node3581Labels = Sparse.eval nodeValue3581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3581) = mixedMoment B node3581 node3581Labels := rfl
  simpa [nodeValue3581, Sparse.eval] using hc.symm

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

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

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

theorem sound4601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4601 node4601Labels = Sparse.eval nodeValue4601 (mixedVector B) := by
  have h := singleton4601 B _hB
  rw [sound1235 B _hB _hF, sound3292 B _hB _hF] at h
  norm_num [nodeValue4601, nodeValue1235, nodeValue3292, Sparse.eval] at h ⊢
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

theorem sound4618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4618 node4618Labels = Sparse.eval nodeValue4618 (mixedVector B) := by
  have h := singleton4618 B _hB
  rw [sound1293 B _hB _hF, sound3304 B _hB _hF] at h
  norm_num [nodeValue4618, nodeValue1293, nodeValue3304, Sparse.eval] at h ⊢
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

theorem zero5100 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5100 node5100Labels = 0 := by
  exact mixedMoment_order_one B hB node5100 node5100Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5100 node5100Labels = Sparse.eval nodeValue5100 (mixedVector B) := by
  simpa only [nodeValue5100, Sparse.eval_nil] using zero5100 B _hB _hF

theorem sound5104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5104 node5104Labels = Sparse.eval nodeValue5104 (mixedVector B) := by
  simpa only [nodeValue5104, Sparse.eval_nil] using zero5104 B _hB _hF

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

theorem sound5137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5137 node5137Labels = Sparse.eval nodeValue5137 (mixedVector B) := by
  have h := singleton5137 B _hB
  rw [sound2556 B _hB _hF, sound3521 B _hB _hF] at h
  norm_num [nodeValue5137, nodeValue2556, nodeValue3521, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5162 node5162Labels = Sparse.eval nodeValue5162 (mixedVector B) := by
  have h := singleton5162 B _hB
  rw [sound2589 B _hB _hF, sound3563 B _hB _hF] at h
  norm_num [nodeValue5162, nodeValue2589, nodeValue3563, Sparse.eval] at h ⊢
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

theorem sound5257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5257 node5257Labels = Sparse.eval nodeValue5257 (mixedVector B) := by
  have h := singleton5257 B _hB
  rw [sound2721 B _hB _hF, sound3532 B _hB _hF] at h
  norm_num [nodeValue5257, nodeValue2721, nodeValue3532, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5259 node5259Labels = Sparse.eval nodeValue5259 (mixedVector B) := by
  have h := singleton5259 B _hB
  rw [sound2723 B _hB _hF, sound3544 B _hB _hF] at h
  norm_num [nodeValue5259, nodeValue2723, nodeValue3544, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5290 node5290Labels = Sparse.eval nodeValue5290 (mixedVector B) := by
  have h := singleton5290 B _hB
  rw [sound2764 B _hB _hF, sound3581 B _hB _hF] at h
  norm_num [nodeValue5290, nodeValue2764, nodeValue3581, Sparse.eval] at h ⊢
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

theorem zero5427 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5427 node5427Labels = 0 := by
  exact mixedMoment_order_one B hB node5427 node5427Labels 1
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

theorem sound5427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5427 node5427Labels = Sparse.eval nodeValue5427 (mixedVector B) := by
  simpa only [nodeValue5427, Sparse.eval_nil] using zero5427 B _hB _hF

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

theorem sound5440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5440 node5440Labels = Sparse.eval nodeValue5440 (mixedVector B) := by
  simpa only [nodeValue5440, Sparse.eval_nil] using zero5440 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources26
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq854 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm854 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA854 + difference 0 1) (sourceB854 + difference 1 0) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5427) := by
    have ha : (tripleCharges (sourceA854 + difference 0 1) (sourceB854 + difference 1 0) sourceC854) = raw14221 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14221; decide +kernel
    rw [ha]
    exact (canonical14221 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA854 + difference 0 2) (sourceB854 + difference 2 0) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (tripleCharges (sourceA854 + difference 0 2) (sourceB854 + difference 2 0) sourceC854) = raw14222 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14222; decide +kernel
    rw [ha]
    exact (canonical14222 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA854 + difference 0 3) (sourceB854 + difference 3 0) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA854 + difference 0 3) (sourceB854 + difference 3 0) sourceC854) = raw14223 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14223; decide +kernel
    rw [ha]
    exact (canonical14223 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA854 + difference 0 4) (sourceB854 + difference 4 0) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA854 + difference 0 4) (sourceB854 + difference 4 0) sourceC854) = raw14224 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14224; decide +kernel
    rw [ha]
    exact (canonical14224 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA854 + difference 0 5) (sourceB854 + difference 5 0) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA854 + difference 0 5) (sourceB854 + difference 5 0) sourceC854) = raw14225 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14225; decide +kernel
    rw [ha]
    exact (canonical14225 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA854 + difference 1 0) (sourceB854 + difference 0 1) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA854 + difference 1 0) (sourceB854 + difference 0 1) sourceC854) = raw14226 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14226; decide +kernel
    rw [ha]
    exact (canonical14226 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA854 + difference 1 2) (sourceB854 + difference 2 1) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5100) := by
    have ha : (tripleCharges (sourceA854 + difference 1 2) (sourceB854 + difference 2 1) sourceC854) = raw14227 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14227; decide +kernel
    rw [ha]
    exact (canonical14227 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA854 + difference 1 3) (sourceB854 + difference 3 1) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA854 + difference 1 3) (sourceB854 + difference 3 1) sourceC854) = raw14228 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14228; decide +kernel
    rw [ha]
    exact (canonical14228 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA854 + difference 1 4) (sourceB854 + difference 4 1) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA854 + difference 1 4) (sourceB854 + difference 4 1) sourceC854) = raw14229 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14229; decide +kernel
    rw [ha]
    exact (canonical14229 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA854 + difference 1 5) (sourceB854 + difference 5 1) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA854 + difference 1 5) (sourceB854 + difference 5 1) sourceC854) = raw14230 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14230; decide +kernel
    rw [ha]
    exact (canonical14230 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA854 + difference 2 0) (sourceB854 + difference 0 2) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA854 + difference 2 0) (sourceB854 + difference 0 2) sourceC854) = raw14231 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14231; decide +kernel
    rw [ha]
    exact (canonical14231 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA854 + difference 2 1) (sourceB854 + difference 1 2) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5162) := by
    have ha : (tripleCharges (sourceA854 + difference 2 1) (sourceB854 + difference 1 2) sourceC854) = raw14232 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14232; decide +kernel
    rw [ha]
    exact (canonical14232 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA854 + difference 2 3) (sourceB854 + difference 3 2) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA854 + difference 2 3) (sourceB854 + difference 3 2) sourceC854) = raw14233 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14233; decide +kernel
    rw [ha]
    exact (canonical14233 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA854 + difference 2 4) (sourceB854 + difference 4 2) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA854 + difference 2 4) (sourceB854 + difference 4 2) sourceC854) = raw14234 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14234; decide +kernel
    rw [ha]
    exact (canonical14234 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA854 + difference 2 5) (sourceB854 + difference 5 2) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA854 + difference 2 5) (sourceB854 + difference 5 2) sourceC854) = raw14235 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14235; decide +kernel
    rw [ha]
    exact (canonical14235 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA854 + difference 3 0) (sourceB854 + difference 0 3) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA854 + difference 3 0) (sourceB854 + difference 0 3) sourceC854) = raw14236 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14236; decide +kernel
    rw [ha]
    exact (canonical14236 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA854 + difference 3 1) (sourceB854 + difference 1 3) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA854 + difference 3 1) (sourceB854 + difference 1 3) sourceC854) = raw14237 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14237; decide +kernel
    rw [ha]
    exact (canonical14237 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA854 + difference 3 2) (sourceB854 + difference 2 3) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA854 + difference 3 2) (sourceB854 + difference 2 3) sourceC854) = raw14238 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14238; decide +kernel
    rw [ha]
    exact (canonical14238 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA854 + difference 3 4) (sourceB854 + difference 4 3) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA854 + difference 3 4) (sourceB854 + difference 4 3) sourceC854) = raw14239 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14239; decide +kernel
    rw [ha]
    exact (canonical14239 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA854 + difference 3 5) (sourceB854 + difference 5 3) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA854 + difference 3 5) (sourceB854 + difference 5 3) sourceC854) = raw14240 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14240; decide +kernel
    rw [ha]
    exact (canonical14240 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA854 + difference 4 0) (sourceB854 + difference 0 4) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA854 + difference 4 0) (sourceB854 + difference 0 4) sourceC854) = raw14241 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14241; decide +kernel
    rw [ha]
    exact (canonical14241 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA854 + difference 4 1) (sourceB854 + difference 1 4) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA854 + difference 4 1) (sourceB854 + difference 1 4) sourceC854) = raw14242 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14242; decide +kernel
    rw [ha]
    exact (canonical14242 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA854 + difference 4 2) (sourceB854 + difference 2 4) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA854 + difference 4 2) (sourceB854 + difference 2 4) sourceC854) = raw14243 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14243; decide +kernel
    rw [ha]
    exact (canonical14243 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA854 + difference 4 3) (sourceB854 + difference 3 4) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA854 + difference 4 3) (sourceB854 + difference 3 4) sourceC854) = raw14244 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14244; decide +kernel
    rw [ha]
    exact (canonical14244 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA854 + difference 4 5) (sourceB854 + difference 5 4) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA854 + difference 4 5) (sourceB854 + difference 5 4) sourceC854) = raw14245 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14245; decide +kernel
    rw [ha]
    exact (canonical14245 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA854 + difference 5 0) (sourceB854 + difference 0 5) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA854 + difference 5 0) (sourceB854 + difference 0 5) sourceC854) = raw14246 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14246; decide +kernel
    rw [ha]
    exact (canonical14246 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA854 + difference 5 1) (sourceB854 + difference 1 5) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA854 + difference 5 1) (sourceB854 + difference 1 5) sourceC854) = raw14247 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14247; decide +kernel
    rw [ha]
    exact (canonical14247 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA854 + difference 5 2) (sourceB854 + difference 2 5) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA854 + difference 5 2) (sourceB854 + difference 2 5) sourceC854) = raw14248 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14248; decide +kernel
    rw [ha]
    exact (canonical14248 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA854 + difference 5 3) (sourceB854 + difference 3 5) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA854 + difference 5 3) (sourceB854 + difference 3 5) sourceC854) = raw14249 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14249; decide +kernel
    rw [ha]
    exact (canonical14249 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA854 + difference 5 4) (sourceB854 + difference 4 5) sourceC854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA854 + difference 5 4) (sourceB854 + difference 4 5) sourceC854) = raw14250 := by
      apply Matrix.ext; unfold tripleCharges sourceA854 sourceB854 sourceC854 difference raw14250; decide +kernel
    rw [ha]
    exact (canonical14250 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA854 sourceB854 sourceC854
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm854, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck744 : Integer.Sparse.reindex keyMap MixedData.row744 = numericRow744 := by decide +kernel

theorem numericCheck744 (x : Master → ℝ) : Integer.Sparse.eval numericRow744 x =
    (4 : ℝ) * reducedSource744 x := by
  norm_num [numericRow744, reducedSource744, Integer.Sparse.eval, Sparse.eval, nodeValue4091, nodeValue4601, nodeValue4606, nodeValue4618, nodeValue5100, nodeValue5104, nodeValue5137, nodeValue5162, nodeValue5257, nodeValue5259, nodeValue5290, nodeValue5427, nodeValue5440] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero744 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource744 (mixedVector B) = 0 := by
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  have h4601 : mixedVector B (Sum.inr 4601) = Sparse.eval nodeValue4601 (mixedVector B) := by
    change mixedMoment B node4601 node4601Labels = _
    exact sound4601 B hB hF
  have h4606 : mixedVector B (Sum.inr 4606) = Sparse.eval nodeValue4606 (mixedVector B) := by
    change mixedMoment B node4606 node4606Labels = _
    exact sound4606 B hB hF
  have h4618 : mixedVector B (Sum.inr 4618) = Sparse.eval nodeValue4618 (mixedVector B) := by
    change mixedMoment B node4618 node4618Labels = _
    exact sound4618 B hB hF
  have h5100 : mixedVector B (Sum.inr 5100) = Sparse.eval nodeValue5100 (mixedVector B) := by
    change mixedMoment B node5100 node5100Labels = _
    exact sound5100 B hB hF
  have h5104 : mixedVector B (Sum.inr 5104) = Sparse.eval nodeValue5104 (mixedVector B) := by
    change mixedMoment B node5104 node5104Labels = _
    exact sound5104 B hB hF
  have h5137 : mixedVector B (Sum.inr 5137) = Sparse.eval nodeValue5137 (mixedVector B) := by
    change mixedMoment B node5137 node5137Labels = _
    exact sound5137 B hB hF
  have h5162 : mixedVector B (Sum.inr 5162) = Sparse.eval nodeValue5162 (mixedVector B) := by
    change mixedMoment B node5162 node5162Labels = _
    exact sound5162 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  have h5427 : mixedVector B (Sum.inr 5427) = Sparse.eval nodeValue5427 (mixedVector B) := by
    change mixedMoment B node5427 node5427Labels = _
    exact sound5427 B hB hF
  have h5440 : mixedVector B (Sum.inr 5440) = Sparse.eval nodeValue5440 (mixedVector B) := by
    change mixedMoment B node5440 node5440Labels = _
    exact sound5440 B hB hF
  simpa only [sourceForm854, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4091, h4601, h4606, h4618, h5100, h5104, h5137, h5162, h5257, h5259, h5290, h5427, h5440, reducedSource744] using sourceEq854 B hB

theorem rowSound744_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row744 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck744, numericCheck744, reducedZero744 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound744_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound744_e_oai
