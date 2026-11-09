-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1197_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T20:40:40.688707+00:00
-- url     : https://prove2.me/submissions/3a43ad06-a073-42c6-be64-b7f5c747ec1b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E189
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

theorem canonical1296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1296 raw1296Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw1296 raw1296Labels = mixedMoment B raw1296step0 raw1296step0Labels := by
      have ha : raw1296step0 = (fun i j => raw1296 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1296step0 raw1296; decide +kernel
      have hl : raw1296step0Labels = raw1296Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1296 raw1296Labels permutation8 permutation4
    mixedMoment B raw1296step0 raw1296step0Labels = mixedMoment B raw1296step1 raw1296step1Labels := by
      have ha : raw1296step1 = raw1296step0 := by apply Matrix.ext; unfold raw1296step1 raw1296step0; decide +kernel
      have hl : raw1296step0Labels = labelEmbedding7 ∘ raw1296step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1296step0 raw1296step0Labels raw1296step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4496 node4496Labels := by rfl

theorem canonical1297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1297 raw1297Labels = mixedMoment B node1080 node1080Labels := by
  calc
    mixedMoment B raw1297 raw1297Labels = mixedMoment B raw1297step0 raw1297step0Labels := by
      have ha : raw1297step0 = (fun i j => raw1297 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1297step0 raw1297; decide +kernel
      have hl : raw1297step0Labels = raw1297Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1297 raw1297Labels permutation8 permutation4
    _ = mixedMoment B node1080 node1080Labels := by rfl

theorem canonical1298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1298 raw1298Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw1298 raw1298Labels = mixedMoment B raw1298step0 raw1298step0Labels := by
      have ha : raw1298step0 = (fun i j => raw1298 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1298step0 raw1298; decide +kernel
      have hl : raw1298step0Labels = raw1298Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1298 raw1298Labels permutation8 permutation6
    mixedMoment B raw1298step0 raw1298step0Labels = mixedMoment B raw1298step1 raw1298step1Labels := by
      have ha : raw1298step1 = -raw1298step0 := by apply Matrix.ext; change ∀ i j, raw1298step1 i j = -(raw1298step0 i j); unfold raw1298step1 raw1298step0; decide +kernel
      have hl : raw1298step1Labels = raw1298step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1298step1 raw1298step1Labels = mixedMoment B raw1298step2 raw1298step2Labels := by
      have ha : raw1298step2 = raw1298step1 := by apply Matrix.ext; unfold raw1298step2 raw1298step1; decide +kernel
      have hl : raw1298step1Labels = labelEmbedding1 ∘ raw1298step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1298step1 raw1298step1Labels raw1298step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19891 raw19891Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw19891 raw19891Labels = mixedMoment B raw19891step0 raw19891step0Labels := by
      have hz : ∀ j, raw19891 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19891step0 = (fun i j => raw19891 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19891step0 raw19891; decide +kernel
      have hl : raw19891step0Labels = raw19891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19891 raw19891Labels permutation520 hz
    mixedMoment B raw19891step0 raw19891step0Labels = mixedMoment B raw19891step1 raw19891step1Labels := by
      have hz : ∀ j, raw19891step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19891step1 = (fun i j => raw19891step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19891step1 raw19891step0; decide +kernel
      have hl : raw19891step1Labels = raw19891step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19891step0 raw19891step0Labels permutation104 hz
    mixedMoment B raw19891step1 raw19891step1Labels = mixedMoment B raw19891step2 raw19891step2Labels := by
      have hz : ∀ j, raw19891step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19891step2 = (fun i j => raw19891step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19891step2 raw19891step1; decide +kernel
      have hl : raw19891step2Labels = raw19891step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19891step1 raw19891step1Labels permutation20 hz
    mixedMoment B raw19891step2 raw19891step2Labels = mixedMoment B raw19891step3 raw19891step3Labels := by
      have hz : ∀ j, raw19891step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19891step3 = (fun i j => raw19891step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19891step3 raw19891step2; decide +kernel
      have hl : raw19891step3Labels = raw19891step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19891step2 raw19891step2Labels permutation4 hz
    mixedMoment B raw19891step3 raw19891step3Labels = mixedMoment B raw19891step4 raw19891step4Labels := by
      have hz : ∀ i, raw19891step3 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw19891step4 = (fun i j => raw19891step3 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw19891step4 raw19891step3; decide +kernel
      have hl : raw19891step4Labels = (fun j => raw19891step3Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19891step3 raw19891step3Labels permutation4 hz
    mixedMoment B raw19891step4 raw19891step4Labels = mixedMoment B raw19891step5 raw19891step5Labels := by
      have ha : raw19891step5 = raw19891step4 := by apply Matrix.ext; unfold raw19891step5 raw19891step4; decide +kernel
      have hl : raw19891step4Labels = labelEmbedding2 ∘ raw19891step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19891step4 raw19891step4Labels raw19891step5Labels labelEmbedding2 hl
    _ = mixedMoment B node4085 node4085Labels := by rfl

theorem canonical19896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19896 raw19896Labels = mixedMoment B node4501 node4501Labels := by
  calc
    mixedMoment B raw19896 raw19896Labels = mixedMoment B raw19896step0 raw19896step0Labels := by
      have hz : ∀ j, raw19896 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19896step0 = (fun i j => raw19896 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19896step0 raw19896; decide +kernel
      have hl : raw19896step0Labels = raw19896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19896 raw19896Labels permutation520 hz
    mixedMoment B raw19896step0 raw19896step0Labels = mixedMoment B raw19896step1 raw19896step1Labels := by
      have hz : ∀ j, raw19896step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19896step1 = (fun i j => raw19896step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19896step1 raw19896step0; decide +kernel
      have hl : raw19896step1Labels = raw19896step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19896step0 raw19896step0Labels permutation104 hz
    mixedMoment B raw19896step1 raw19896step1Labels = mixedMoment B raw19896step2 raw19896step2Labels := by
      have hz : ∀ j, raw19896step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19896step2 = (fun i j => raw19896step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19896step2 raw19896step1; decide +kernel
      have hl : raw19896step2Labels = raw19896step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19896step1 raw19896step1Labels permutation20 hz
    _ = mixedMoment B node4501 node4501Labels := by rfl

theorem canonical19901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19901 raw19901Labels = mixedMoment B node4501 node4501Labels := by
  calc
    mixedMoment B raw19901 raw19901Labels = mixedMoment B raw19901step0 raw19901step0Labels := by
      have hz : ∀ j, raw19901 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19901step0 = (fun i j => raw19901 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19901step0 raw19901; decide +kernel
      have hl : raw19901step0Labels = raw19901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19901 raw19901Labels permutation520 hz
    mixedMoment B raw19901step0 raw19901step0Labels = mixedMoment B raw19901step1 raw19901step1Labels := by
      have hz : ∀ j, raw19901step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19901step1 = (fun i j => raw19901step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19901step1 raw19901step0; decide +kernel
      have hl : raw19901step1Labels = raw19901step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19901step0 raw19901step0Labels permutation104 hz
    mixedMoment B raw19901step1 raw19901step1Labels = mixedMoment B raw19901step2 raw19901step2Labels := by
      have hz : ∀ j, raw19901step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19901step2 = (fun i j => raw19901step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19901step2 raw19901step1; decide +kernel
      have hl : raw19901step2Labels = raw19901step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19901step1 raw19901step1Labels permutation14 hz
    _ = mixedMoment B node4501 node4501Labels := by rfl

theorem canonical19906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19906 raw19906Labels = mixedMoment B node4501 node4501Labels := by
  calc
    mixedMoment B raw19906 raw19906Labels = mixedMoment B raw19906step0 raw19906step0Labels := by
      have hz : ∀ j, raw19906 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19906step0 = (fun i j => raw19906 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19906step0 raw19906; decide +kernel
      have hl : raw19906step0Labels = raw19906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19906 raw19906Labels permutation520 hz
    mixedMoment B raw19906step0 raw19906step0Labels = mixedMoment B raw19906step1 raw19906step1Labels := by
      have hz : ∀ j, raw19906step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19906step1 = (fun i j => raw19906step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19906step1 raw19906step0; decide +kernel
      have hl : raw19906step1Labels = raw19906step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19906step0 raw19906step0Labels permutation80 hz
    mixedMoment B raw19906step1 raw19906step1Labels = mixedMoment B raw19906step2 raw19906step2Labels := by
      have hz : ∀ j, raw19906step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19906step2 = (fun i j => raw19906step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19906step2 raw19906step1; decide +kernel
      have hl : raw19906step2Labels = raw19906step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19906step1 raw19906step1Labels permutation14 hz
    _ = mixedMoment B node4501 node4501Labels := by rfl

theorem canonical19907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19907 raw19907Labels = mixedMoment B node4181 node4181Labels := by
  calc
    mixedMoment B raw19907 raw19907Labels = mixedMoment B raw19907step0 raw19907step0Labels := by
      have hz : ∀ j, raw19907 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19907step0 = (fun i j => raw19907 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19907step0 raw19907; decide +kernel
      have hl : raw19907step0Labels = raw19907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19907 raw19907Labels permutation434 hz
    mixedMoment B raw19907step0 raw19907step0Labels = mixedMoment B raw19907step1 raw19907step1Labels := by
      have hz : ∀ j, raw19907step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19907step1 = (fun i j => raw19907step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19907step1 raw19907step0; decide +kernel
      have hl : raw19907step1Labels = raw19907step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19907step0 raw19907step0Labels permutation80 hz
    mixedMoment B raw19907step1 raw19907step1Labels = mixedMoment B raw19907step2 raw19907step2Labels := by
      have hz : ∀ j, raw19907step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19907step2 = (fun i j => raw19907step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19907step2 raw19907step1; decide +kernel
      have hl : raw19907step2Labels = raw19907step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19907step1 raw19907step1Labels permutation14 hz
    _ = mixedMoment B node4181 node4181Labels := by rfl

theorem canonical19908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19908 raw19908Labels = mixedMoment B node4350 node4350Labels := by
  calc
    mixedMoment B raw19908 raw19908Labels = mixedMoment B raw19908step0 raw19908step0Labels := by
      have hz : ∀ j, raw19908 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19908step0 = (fun i j => raw19908 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19908step0 raw19908; decide +kernel
      have hl : raw19908step0Labels = raw19908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19908 raw19908Labels permutation434 hz
    mixedMoment B raw19908step0 raw19908step0Labels = mixedMoment B raw19908step1 raw19908step1Labels := by
      have hz : ∀ j, raw19908step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19908step1 = (fun i j => raw19908step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19908step1 raw19908step0; decide +kernel
      have hl : raw19908step1Labels = raw19908step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19908step0 raw19908step0Labels permutation80 hz
    _ = mixedMoment B node4350 node4350Labels := by rfl

theorem canonical19909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19909 raw19909Labels = mixedMoment B node4350 node4350Labels := by
  calc
    mixedMoment B raw19909 raw19909Labels = mixedMoment B raw19909step0 raw19909step0Labels := by
      have hz : ∀ j, raw19909 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19909step0 = (fun i j => raw19909 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19909step0 raw19909; decide +kernel
      have hl : raw19909step0Labels = raw19909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19909 raw19909Labels permutation434 hz
    mixedMoment B raw19909step0 raw19909step0Labels = mixedMoment B raw19909step1 raw19909step1Labels := by
      have hz : ∀ j, raw19909step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19909step1 = (fun i j => raw19909step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19909step1 raw19909step0; decide +kernel
      have hl : raw19909step1Labels = raw19909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19909step0 raw19909step0Labels permutation56 hz
    _ = mixedMoment B node4350 node4350Labels := by rfl

theorem canonical19910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19910 raw19910Labels = mixedMoment B node4350 node4350Labels := by
  calc
    mixedMoment B raw19910 raw19910Labels = mixedMoment B raw19910step0 raw19910step0Labels := by
      have hz : ∀ j, raw19910 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19910step0 = (fun i j => raw19910 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19910step0 raw19910; decide +kernel
      have hl : raw19910step0Labels = raw19910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19910 raw19910Labels permutation346 hz
    mixedMoment B raw19910step0 raw19910step0Labels = mixedMoment B raw19910step1 raw19910step1Labels := by
      have hz : ∀ j, raw19910step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19910step1 = (fun i j => raw19910step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19910step1 raw19910step0; decide +kernel
      have hl : raw19910step1Labels = raw19910step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19910step0 raw19910step0Labels permutation56 hz
    _ = mixedMoment B node4350 node4350Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21831 raw21831Labels = mixedMoment B node4837 node4837Labels := by
  calc
    mixedMoment B raw21831 raw21831Labels = mixedMoment B raw21831step0 raw21831step0Labels := by
      have hz : ∀ j, raw21831 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21831step0 = (fun i j => raw21831 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21831step0 raw21831; decide +kernel
      have hl : raw21831step0Labels = raw21831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21831 raw21831Labels permutation434 hz
    mixedMoment B raw21831step0 raw21831step0Labels = mixedMoment B raw21831step1 raw21831step1Labels := by
      have hz : ∀ j, raw21831step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21831step1 = (fun i j => raw21831step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21831step1 raw21831step0; decide +kernel
      have hl : raw21831step1Labels = raw21831step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21831step0 raw21831step0Labels permutation80 hz
    _ = mixedMoment B node4837 node4837Labels := by rfl

theorem canonical21832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21832 raw21832Labels = mixedMoment B node4837 node4837Labels := by
  calc
    mixedMoment B raw21832 raw21832Labels = mixedMoment B raw21832step0 raw21832step0Labels := by
      have hz : ∀ j, raw21832 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21832step0 = (fun i j => raw21832 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21832step0 raw21832; decide +kernel
      have hl : raw21832step0Labels = raw21832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21832 raw21832Labels permutation434 hz
    mixedMoment B raw21832step0 raw21832step0Labels = mixedMoment B raw21832step1 raw21832step1Labels := by
      have hz : ∀ j, raw21832step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21832step1 = (fun i j => raw21832step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21832step1 raw21832step0; decide +kernel
      have hl : raw21832step1Labels = raw21832step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21832step0 raw21832step0Labels permutation56 hz
    _ = mixedMoment B node4837 node4837Labels := by rfl

theorem canonical21833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21833 raw21833Labels = mixedMoment B node4837 node4837Labels := by
  calc
    mixedMoment B raw21833 raw21833Labels = mixedMoment B raw21833step0 raw21833step0Labels := by
      have hz : ∀ j, raw21833 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21833step0 = (fun i j => raw21833 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21833step0 raw21833; decide +kernel
      have hl : raw21833step0Labels = raw21833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21833 raw21833Labels permutation346 hz
    mixedMoment B raw21833step0 raw21833step0Labels = mixedMoment B raw21833step1 raw21833step1Labels := by
      have hz : ∀ j, raw21833step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21833step1 = (fun i j => raw21833step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21833step1 raw21833step0; decide +kernel
      have hl : raw21833step1Labels = raw21833step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21833step0 raw21833step0Labels permutation56 hz
    _ = mixedMoment B node4837 node4837Labels := by rfl

theorem canonical21834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21834 raw21834Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw21834 raw21834Labels = mixedMoment B raw21834step0 raw21834step0Labels := by
      have hz : ∀ j, raw21834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21834step0 = (fun i j => raw21834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21834step0 raw21834; decide +kernel
      have hl : raw21834step0Labels = raw21834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21834 raw21834Labels permutation434 hz
    mixedMoment B raw21834step0 raw21834step0Labels = mixedMoment B raw21834step1 raw21834step1Labels := by
      have hz : ∀ j, raw21834step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21834step1 = (fun i j => raw21834step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21834step1 raw21834step0; decide +kernel
      have hl : raw21834step1Labels = raw21834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21834step0 raw21834step0Labels permutation80 hz
    mixedMoment B raw21834step1 raw21834step1Labels = mixedMoment B raw21834step2 raw21834step2Labels := by
      have hz : ∀ j, raw21834step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21834step2 = (fun i j => raw21834step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21834step2 raw21834step1; decide +kernel
      have hl : raw21834step2Labels = raw21834step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21834step1 raw21834step1Labels permutation14 hz
    mixedMoment B raw21834step2 raw21834step2Labels = mixedMoment B raw21834step3 raw21834step3Labels := by
      have ha : raw21834step3 = (fun i j => raw21834step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21834step3 raw21834step2; decide +kernel
      have hl : raw21834step3Labels = raw21834step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21834step2 raw21834step2Labels permutation2 permutation7
    mixedMoment B raw21834step3 raw21834step3Labels = mixedMoment B raw21834step4 raw21834step4Labels := by
      have ha : raw21834step4 = -raw21834step3 := by apply Matrix.ext; change ∀ i j, raw21834step4 i j = -(raw21834step3 i j); unfold raw21834step4 raw21834step3; decide +kernel
      have hl : raw21834step4Labels = raw21834step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21834step4 raw21834step4Labels = mixedMoment B raw21834step5 raw21834step5Labels := by
      have ha : raw21834step5 = raw21834step4 := by apply Matrix.ext; unfold raw21834step5 raw21834step4; decide +kernel
      have hl : raw21834step4Labels = labelEmbedding10 ∘ raw21834step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21834step4 raw21834step4Labels raw21834step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

theorem canonical21835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21835 raw21835Labels = mixedMoment B node4174 node4174Labels := by
  calc
    mixedMoment B raw21835 raw21835Labels = mixedMoment B raw21835step0 raw21835step0Labels := by
      have hz : ∀ j, raw21835 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21835step0 = (fun i j => raw21835 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21835step0 raw21835; decide +kernel
      have hl : raw21835step0Labels = raw21835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21835 raw21835Labels permutation434 hz
    mixedMoment B raw21835step0 raw21835step0Labels = mixedMoment B raw21835step1 raw21835step1Labels := by
      have hz : ∀ j, raw21835step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21835step1 = (fun i j => raw21835step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21835step1 raw21835step0; decide +kernel
      have hl : raw21835step1Labels = raw21835step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21835step0 raw21835step0Labels permutation80 hz
    _ = mixedMoment B node4174 node4174Labels := by rfl

theorem canonical21836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21836 raw21836Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw21836 raw21836Labels = mixedMoment B raw21836step0 raw21836step0Labels := by
      have hz : ∀ j, raw21836 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21836step0 = (fun i j => raw21836 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21836step0 raw21836; decide +kernel
      have hl : raw21836step0Labels = raw21836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21836 raw21836Labels permutation434 hz
    mixedMoment B raw21836step0 raw21836step0Labels = mixedMoment B raw21836step1 raw21836step1Labels := by
      have ha : raw21836step1 = (fun i j => raw21836step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21836step1 raw21836step0; decide +kernel
      have hl : raw21836step1Labels = raw21836step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21836step0 raw21836step0Labels permutation38 permutation2
    _ = mixedMoment B node4343 node4343Labels := by rfl

theorem canonical21837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21837 raw21837Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw21837 raw21837Labels = mixedMoment B raw21837step0 raw21837step0Labels := by
      have hz : ∀ j, raw21837 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21837step0 = (fun i j => raw21837 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21837step0 raw21837; decide +kernel
      have hl : raw21837step0Labels = raw21837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21837 raw21837Labels permutation346 hz
    mixedMoment B raw21837step0 raw21837step0Labels = mixedMoment B raw21837step1 raw21837step1Labels := by
      have ha : raw21837step1 = (fun i j => raw21837step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21837step1 raw21837step0; decide +kernel
      have hl : raw21837step1Labels = raw21837step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21837step0 raw21837step0Labels permutation38 permutation2
    _ = mixedMoment B node4343 node4343Labels := by rfl

theorem canonical21838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21838 raw21838Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw21838 raw21838Labels = mixedMoment B raw21838step0 raw21838step0Labels := by
      have hz : ∀ j, raw21838 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21838step0 = (fun i j => raw21838 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21838step0 raw21838; decide +kernel
      have hl : raw21838step0Labels = raw21838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21838 raw21838Labels permutation434 hz
    mixedMoment B raw21838step0 raw21838step0Labels = mixedMoment B raw21838step1 raw21838step1Labels := by
      have hz : ∀ j, raw21838step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21838step1 = (fun i j => raw21838step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21838step1 raw21838step0; decide +kernel
      have hl : raw21838step1Labels = raw21838step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21838step0 raw21838step0Labels permutation80 hz
    _ = mixedMoment B node4496 node4496Labels := by rfl

theorem canonical21839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21839 raw21839Labels = mixedMoment B node4174 node4174Labels := by
  calc
    mixedMoment B raw21839 raw21839Labels = mixedMoment B raw21839step0 raw21839step0Labels := by
      have hz : ∀ j, raw21839 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21839step0 = (fun i j => raw21839 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21839step0 raw21839; decide +kernel
      have hl : raw21839step0Labels = raw21839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21839 raw21839Labels permutation434 hz
    mixedMoment B raw21839step0 raw21839step0Labels = mixedMoment B raw21839step1 raw21839step1Labels := by
      have hz : ∀ j, raw21839step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21839step1 = (fun i j => raw21839step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21839step1 raw21839step0; decide +kernel
      have hl : raw21839step1Labels = raw21839step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21839step0 raw21839step0Labels permutation56 hz
    _ = mixedMoment B node4174 node4174Labels := by rfl

theorem canonical21840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21840 raw21840Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw21840 raw21840Labels = mixedMoment B raw21840step0 raw21840step0Labels := by
      have hz : ∀ j, raw21840 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21840step0 = (fun i j => raw21840 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21840step0 raw21840; decide +kernel
      have hl : raw21840step0Labels = raw21840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21840 raw21840Labels permutation434 hz
    _ = mixedMoment B node4343 node4343Labels := by rfl

theorem canonical21841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21841 raw21841Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw21841 raw21841Labels = mixedMoment B raw21841step0 raw21841step0Labels := by
      have hz : ∀ j, raw21841 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21841step0 = (fun i j => raw21841 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21841step0 raw21841; decide +kernel
      have hl : raw21841step0Labels = raw21841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21841 raw21841Labels permutation265 hz
    mixedMoment B raw21841step0 raw21841step0Labels = mixedMoment B raw21841step1 raw21841step1Labels := by
      have ha : raw21841step1 = (fun i j => raw21841step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21841step1 raw21841step0; decide +kernel
      have hl : raw21841step1Labels = raw21841step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21841step0 raw21841step0Labels permutation38 permutation2
    _ = mixedMoment B node4343 node4343Labels := by rfl

theorem canonical21842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21842 raw21842Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw21842 raw21842Labels = mixedMoment B raw21842step0 raw21842step0Labels := by
      have hz : ∀ j, raw21842 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21842step0 = (fun i j => raw21842 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21842step0 raw21842; decide +kernel
      have hl : raw21842step0Labels = raw21842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21842 raw21842Labels permutation434 hz
    mixedMoment B raw21842step0 raw21842step0Labels = mixedMoment B raw21842step1 raw21842step1Labels := by
      have hz : ∀ j, raw21842step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21842step1 = (fun i j => raw21842step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21842step1 raw21842step0; decide +kernel
      have hl : raw21842step1Labels = raw21842step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21842step0 raw21842step0Labels permutation56 hz
    _ = mixedMoment B node4496 node4496Labels := by rfl

theorem canonical21843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21843 raw21843Labels = mixedMoment B node4174 node4174Labels := by
  calc
    mixedMoment B raw21843 raw21843Labels = mixedMoment B raw21843step0 raw21843step0Labels := by
      have hz : ∀ j, raw21843 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21843step0 = (fun i j => raw21843 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21843step0 raw21843; decide +kernel
      have hl : raw21843step0Labels = raw21843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21843 raw21843Labels permutation346 hz
    mixedMoment B raw21843step0 raw21843step0Labels = mixedMoment B raw21843step1 raw21843step1Labels := by
      have hz : ∀ j, raw21843step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21843step1 = (fun i j => raw21843step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21843step1 raw21843step0; decide +kernel
      have hl : raw21843step1Labels = raw21843step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21843step0 raw21843step0Labels permutation56 hz
    _ = mixedMoment B node4174 node4174Labels := by rfl

theorem canonical21844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21844 raw21844Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw21844 raw21844Labels = mixedMoment B raw21844step0 raw21844step0Labels := by
      have hz : ∀ j, raw21844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21844step0 = (fun i j => raw21844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21844step0 raw21844; decide +kernel
      have hl : raw21844step0Labels = raw21844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21844 raw21844Labels permutation346 hz
    _ = mixedMoment B node4343 node4343Labels := by rfl

theorem canonical21845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21845 raw21845Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw21845 raw21845Labels = mixedMoment B raw21845step0 raw21845step0Labels := by
      have hz : ∀ j, raw21845 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21845step0 = (fun i j => raw21845 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21845step0 raw21845; decide +kernel
      have hl : raw21845step0Labels = raw21845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21845 raw21845Labels permutation265 hz
    _ = mixedMoment B node4343 node4343Labels := by rfl

theorem canonical21846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21846 raw21846Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw21846 raw21846Labels = mixedMoment B raw21846step0 raw21846step0Labels := by
      have hz : ∀ j, raw21846 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21846step0 = (fun i j => raw21846 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21846step0 raw21846; decide +kernel
      have hl : raw21846step0Labels = raw21846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21846 raw21846Labels permutation346 hz
    mixedMoment B raw21846step0 raw21846step0Labels = mixedMoment B raw21846step1 raw21846step1Labels := by
      have hz : ∀ j, raw21846step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21846step1 = (fun i j => raw21846step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21846step1 raw21846step0; decide +kernel
      have hl : raw21846step1Labels = raw21846step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21846step0 raw21846step0Labels permutation56 hz
    _ = mixedMoment B node4496 node4496Labels := by rfl

theorem canonical21847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21847 raw21847Labels = mixedMoment B node4190 node4190Labels := by
  calc
    mixedMoment B raw21847 raw21847Labels = mixedMoment B raw21847step0 raw21847step0Labels := by
      have hz : ∀ j, raw21847 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21847step0 = (fun i j => raw21847 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21847step0 raw21847; decide +kernel
      have hl : raw21847step0Labels = raw21847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21847 raw21847Labels permutation434 hz
    mixedMoment B raw21847step0 raw21847step0Labels = mixedMoment B raw21847step1 raw21847step1Labels := by
      have hz : ∀ j, raw21847step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21847step1 = (fun i j => raw21847step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21847step1 raw21847step0; decide +kernel
      have hl : raw21847step1Labels = raw21847step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21847step0 raw21847step0Labels permutation80 hz
    mixedMoment B raw21847step1 raw21847step1Labels = mixedMoment B raw21847step2 raw21847step2Labels := by
      have hz : ∀ j, raw21847step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21847step2 = (fun i j => raw21847step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21847step2 raw21847step1; decide +kernel
      have hl : raw21847step2Labels = raw21847step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21847step1 raw21847step1Labels permutation14 hz
    _ = mixedMoment B node4190 node4190Labels := by rfl

theorem canonical21848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21848 raw21848Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw21848 raw21848Labels = mixedMoment B raw21848step0 raw21848step0Labels := by
      have hz : ∀ j, raw21848 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21848step0 = (fun i j => raw21848 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21848step0 raw21848; decide +kernel
      have hl : raw21848step0Labels = raw21848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21848 raw21848Labels permutation434 hz
    mixedMoment B raw21848step0 raw21848step0Labels = mixedMoment B raw21848step1 raw21848step1Labels := by
      have hz : ∀ j, raw21848step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21848step1 = (fun i j => raw21848step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21848step1 raw21848step0; decide +kernel
      have hl : raw21848step1Labels = raw21848step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21848step0 raw21848step0Labels permutation80 hz
    _ = mixedMoment B node4359 node4359Labels := by rfl

theorem canonical21849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21849 raw21849Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw21849 raw21849Labels = mixedMoment B raw21849step0 raw21849step0Labels := by
      have hz : ∀ j, raw21849 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21849step0 = (fun i j => raw21849 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21849step0 raw21849; decide +kernel
      have hl : raw21849step0Labels = raw21849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21849 raw21849Labels permutation434 hz
    mixedMoment B raw21849step0 raw21849step0Labels = mixedMoment B raw21849step1 raw21849step1Labels := by
      have hz : ∀ j, raw21849step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21849step1 = (fun i j => raw21849step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21849step1 raw21849step0; decide +kernel
      have hl : raw21849step1Labels = raw21849step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21849step0 raw21849step0Labels permutation56 hz
    _ = mixedMoment B node4359 node4359Labels := by rfl

theorem canonical21850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21850 raw21850Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw21850 raw21850Labels = mixedMoment B raw21850step0 raw21850step0Labels := by
      have hz : ∀ j, raw21850 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21850step0 = (fun i j => raw21850 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21850step0 raw21850; decide +kernel
      have hl : raw21850step0Labels = raw21850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21850 raw21850Labels permutation346 hz
    mixedMoment B raw21850step0 raw21850step0Labels = mixedMoment B raw21850step1 raw21850step1Labels := by
      have hz : ∀ j, raw21850step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21850step1 = (fun i j => raw21850step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21850step1 raw21850step0; decide +kernel
      have hl : raw21850step1Labels = raw21850step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21850step0 raw21850step0Labels permutation56 hz
    _ = mixedMoment B node4359 node4359Labels := by rfl

theorem canonical21851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21851 raw21851Labels = mixedMoment B node4510 node4510Labels := by
  calc
    mixedMoment B raw21851 raw21851Labels = mixedMoment B raw21851step0 raw21851step0Labels := by
      have hz : ∀ j, raw21851 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21851step0 = (fun i j => raw21851 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21851step0 raw21851; decide +kernel
      have hl : raw21851step0Labels = raw21851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21851 raw21851Labels permutation434 hz
    mixedMoment B raw21851step0 raw21851step0Labels = mixedMoment B raw21851step1 raw21851step1Labels := by
      have hz : ∀ j, raw21851step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21851step1 = (fun i j => raw21851step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21851step1 raw21851step0; decide +kernel
      have hl : raw21851step1Labels = raw21851step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21851step0 raw21851step0Labels permutation80 hz
    mixedMoment B raw21851step1 raw21851step1Labels = mixedMoment B raw21851step2 raw21851step2Labels := by
      have hz : ∀ j, raw21851step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21851step2 = (fun i j => raw21851step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21851step2 raw21851step1; decide +kernel
      have hl : raw21851step2Labels = raw21851step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21851step1 raw21851step1Labels permutation14 hz
    _ = mixedMoment B node4510 node4510Labels := by rfl

theorem canonical21852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21852 raw21852Labels = mixedMoment B node4512 node4512Labels := by
  calc
    mixedMoment B raw21852 raw21852Labels = mixedMoment B raw21852step0 raw21852step0Labels := by
      have hz : ∀ j, raw21852 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21852step0 = (fun i j => raw21852 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21852step0 raw21852; decide +kernel
      have hl : raw21852step0Labels = raw21852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21852 raw21852Labels permutation520 hz
    mixedMoment B raw21852step0 raw21852step0Labels = mixedMoment B raw21852step1 raw21852step1Labels := by
      have hz : ∀ j, raw21852step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21852step1 = (fun i j => raw21852step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21852step1 raw21852step0; decide +kernel
      have hl : raw21852step1Labels = raw21852step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21852step0 raw21852step0Labels permutation104 hz
    mixedMoment B raw21852step1 raw21852step1Labels = mixedMoment B raw21852step2 raw21852step2Labels := by
      have hz : ∀ j, raw21852step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21852step2 = (fun i j => raw21852step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21852step2 raw21852step1; decide +kernel
      have hl : raw21852step2Labels = raw21852step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21852step1 raw21852step1Labels permutation20 hz
    mixedMoment B raw21852step2 raw21852step2Labels = mixedMoment B raw21852step3 raw21852step3Labels := by
      have hz : ∀ j, raw21852step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw21852step3 = (fun i j => raw21852step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw21852step3 raw21852step2; decide +kernel
      have hl : raw21852step3Labels = raw21852step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21852step2 raw21852step2Labels permutation4 hz
    _ = mixedMoment B node4512 node4512Labels := by rfl

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

theorem canonical807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw807 raw807Labels = mixedMoment B node4174 node4174Labels := by
  calc
    mixedMoment B raw807 raw807Labels = mixedMoment B raw807step0 raw807step0Labels := by
      have ha : raw807step0 = (fun i j => raw807 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw807step0 raw807; decide +kernel
      have hl : raw807step0Labels = raw807Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw807 raw807Labels permutation8 permutation4
    mixedMoment B raw807step0 raw807step0Labels = mixedMoment B raw807step1 raw807step1Labels := by
      have ha : raw807step1 = raw807step0 := by apply Matrix.ext; unfold raw807step1 raw807step0; decide +kernel
      have hl : raw807step0Labels = labelEmbedding7 ∘ raw807step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw807step0 raw807step0Labels raw807step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4174 node4174Labels := by rfl

theorem canonical808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw808 raw808Labels = mixedMoment B node602 node602Labels := by
  calc
    mixedMoment B raw808 raw808Labels = mixedMoment B raw808step0 raw808step0Labels := by
      have ha : raw808step0 = (fun i j => raw808 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw808step0 raw808; decide +kernel
      have hl : raw808step0Labels = raw808Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw808 raw808Labels permutation8 permutation4
    _ = mixedMoment B node602 node602Labels := by rfl

theorem canonical809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw809 raw809Labels = mixedMoment B node1509 node1509Labels := by
  calc
    mixedMoment B raw809 raw809Labels = mixedMoment B raw809step0 raw809step0Labels := by
      have ha : raw809step0 = (fun i j => raw809 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw809step0 raw809; decide +kernel
      have hl : raw809step0Labels = raw809Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw809 raw809Labels permutation8 permutation6
    mixedMoment B raw809step0 raw809step0Labels = mixedMoment B raw809step1 raw809step1Labels := by
      have ha : raw809step1 = -raw809step0 := by apply Matrix.ext; change ∀ i j, raw809step1 i j = -(raw809step0 i j); unfold raw809step1 raw809step0; decide +kernel
      have hl : raw809step1Labels = raw809step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw809step1 raw809step1Labels = mixedMoment B raw809step2 raw809step2Labels := by
      have ha : raw809step2 = raw809step1 := by apply Matrix.ext; unfold raw809step2 raw809step1; decide +kernel
      have hl : raw809step1Labels = labelEmbedding1 ∘ raw809step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw809step1 raw809step1Labels raw809step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1509 node1509Labels := by rfl

theorem canonical819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw819 raw819Labels = mixedMoment B node4181 node4181Labels := by
  calc
    mixedMoment B raw819 raw819Labels = mixedMoment B raw819step0 raw819step0Labels := by
      have ha : raw819step0 = (fun i j => raw819 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw819step0 raw819; decide +kernel
      have hl : raw819step0Labels = raw819Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw819 raw819Labels permutation2 permutation4
    mixedMoment B raw819step0 raw819step0Labels = mixedMoment B raw819step1 raw819step1Labels := by
      have ha : raw819step1 = raw819step0 := by apply Matrix.ext; unfold raw819step1 raw819step0; decide +kernel
      have hl : raw819step0Labels = labelEmbedding7 ∘ raw819step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw819step0 raw819step0Labels raw819step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4181 node4181Labels := by rfl

theorem canonical820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw820 raw820Labels = mixedMoment B node609 node609Labels := by
  calc
    mixedMoment B raw820 raw820Labels = mixedMoment B raw820step0 raw820step0Labels := by
      have ha : raw820step0 = (fun i j => raw820 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw820step0 raw820; decide +kernel
      have hl : raw820step0Labels = raw820Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw820 raw820Labels permutation2 permutation4
    _ = mixedMoment B node609 node609Labels := by rfl

theorem canonical821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw821 raw821Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw821 raw821Labels = mixedMoment B raw821step0 raw821step0Labels := by
      have ha : raw821step0 = (fun i j => raw821 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw821step0 raw821; decide +kernel
      have hl : raw821step0Labels = raw821Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw821 raw821Labels permutation2 permutation6
    mixedMoment B raw821step0 raw821step0Labels = mixedMoment B raw821step1 raw821step1Labels := by
      have ha : raw821step1 = -raw821step0 := by apply Matrix.ext; change ∀ i j, raw821step1 i j = -(raw821step0 i j); unfold raw821step1 raw821step0; decide +kernel
      have hl : raw821step1Labels = raw821step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw821step1 raw821step1Labels = mixedMoment B raw821step2 raw821step2Labels := by
      have ha : raw821step2 = raw821step1 := by apply Matrix.ext; unfold raw821step2 raw821step1; decide +kernel
      have hl : raw821step1Labels = labelEmbedding1 ∘ raw821step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw821step1 raw821step1Labels raw821step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1521 node1521Labels := by rfl

theorem canonical837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw837 raw837Labels = mixedMoment B node4190 node4190Labels := by
  calc
    mixedMoment B raw837 raw837Labels = mixedMoment B raw837step0 raw837step0Labels := by
      have ha : raw837step0 = (fun i j => raw837 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw837step0 raw837; decide +kernel
      have hl : raw837step0Labels = raw837Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw837 raw837Labels permutation2 permutation4
    mixedMoment B raw837step0 raw837step0Labels = mixedMoment B raw837step1 raw837step1Labels := by
      have ha : raw837step1 = raw837step0 := by apply Matrix.ext; unfold raw837step1 raw837step0; decide +kernel
      have hl : raw837step0Labels = labelEmbedding7 ∘ raw837step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw837step0 raw837step0Labels raw837step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4190 node4190Labels := by rfl

theorem canonical838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw838 raw838Labels = mixedMoment B node618 node618Labels := by
  calc
    mixedMoment B raw838 raw838Labels = mixedMoment B raw838step0 raw838step0Labels := by
      have ha : raw838step0 = (fun i j => raw838 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw838step0 raw838; decide +kernel
      have hl : raw838step0Labels = raw838Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw838 raw838Labels permutation2 permutation4
    _ = mixedMoment B node618 node618Labels := by rfl

theorem canonical839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw839 raw839Labels = mixedMoment B node1527 node1527Labels := by
  calc
    mixedMoment B raw839 raw839Labels = mixedMoment B raw839step0 raw839step0Labels := by
      have ha : raw839step0 = (fun i j => raw839 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw839step0 raw839; decide +kernel
      have hl : raw839step0Labels = raw839Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw839 raw839Labels permutation2 permutation6
    mixedMoment B raw839step0 raw839step0Labels = mixedMoment B raw839step1 raw839step1Labels := by
      have ha : raw839step1 = -raw839step0 := by apply Matrix.ext; change ∀ i j, raw839step1 i j = -(raw839step0 i j); unfold raw839step1 raw839step0; decide +kernel
      have hl : raw839step1Labels = raw839step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw839step1 raw839step1Labels = mixedMoment B raw839step2 raw839step2Labels := by
      have ha : raw839step2 = raw839step1 := by apply Matrix.ext; unfold raw839step2 raw839step1; decide +kernel
      have hl : raw839step1Labels = labelEmbedding1 ∘ raw839step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw839step1 raw839step1Labels raw839step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1527 node1527Labels := by rfl

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

theorem canonical1125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1125 raw1125Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw1125 raw1125Labels = mixedMoment B raw1125step0 raw1125step0Labels := by
      have ha : raw1125step0 = (fun i j => raw1125 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1125step0 raw1125; decide +kernel
      have hl : raw1125step0Labels = raw1125Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1125 raw1125Labels permutation32 permutation4
    mixedMoment B raw1125step0 raw1125step0Labels = mixedMoment B raw1125step1 raw1125step1Labels := by
      have ha : raw1125step1 = raw1125step0 := by apply Matrix.ext; unfold raw1125step1 raw1125step0; decide +kernel
      have hl : raw1125step0Labels = labelEmbedding7 ∘ raw1125step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1125step0 raw1125step0Labels raw1125step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4343 node4343Labels := by rfl

theorem canonical1126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1126 raw1126Labels = mixedMoment B node921 node921Labels := by
  calc
    mixedMoment B raw1126 raw1126Labels = mixedMoment B raw1126step0 raw1126step0Labels := by
      have ha : raw1126step0 = (fun i j => raw1126 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1126step0 raw1126; decide +kernel
      have hl : raw1126step0Labels = raw1126Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1126 raw1126Labels permutation32 permutation4
    _ = mixedMoment B node921 node921Labels := by rfl

theorem canonical1127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1127 raw1127Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw1127 raw1127Labels = mixedMoment B raw1127step0 raw1127step0Labels := by
      have ha : raw1127step0 = (fun i j => raw1127 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1127step0 raw1127; decide +kernel
      have hl : raw1127step0Labels = raw1127Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1127 raw1127Labels permutation32 permutation6
    mixedMoment B raw1127step0 raw1127step0Labels = mixedMoment B raw1127step1 raw1127step1Labels := by
      have ha : raw1127step1 = -raw1127step0 := by apply Matrix.ext; change ∀ i j, raw1127step1 i j = -(raw1127step0 i j); unfold raw1127step1 raw1127step0; decide +kernel
      have hl : raw1127step1Labels = raw1127step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1127step1 raw1127step1Labels = mixedMoment B raw1127step2 raw1127step2Labels := by
      have ha : raw1127step2 = raw1127step1 := by apply Matrix.ext; unfold raw1127step2 raw1127step1; decide +kernel
      have hl : raw1127step1Labels = labelEmbedding1 ∘ raw1127step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1127step1 raw1127step1Labels raw1127step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

theorem canonical1137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1137 raw1137Labels = mixedMoment B node4350 node4350Labels := by
  calc
    mixedMoment B raw1137 raw1137Labels = mixedMoment B raw1137step0 raw1137step0Labels := by
      have ha : raw1137step0 = (fun i j => raw1137 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1137step0 raw1137; decide +kernel
      have hl : raw1137step0Labels = raw1137Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1137 raw1137Labels permutation8 permutation4
    mixedMoment B raw1137step0 raw1137step0Labels = mixedMoment B raw1137step1 raw1137step1Labels := by
      have ha : raw1137step1 = raw1137step0 := by apply Matrix.ext; unfold raw1137step1 raw1137step0; decide +kernel
      have hl : raw1137step0Labels = labelEmbedding7 ∘ raw1137step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1137step0 raw1137step0Labels raw1137step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4350 node4350Labels := by rfl

theorem canonical1138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1138 raw1138Labels = mixedMoment B node928 node928Labels := by
  calc
    mixedMoment B raw1138 raw1138Labels = mixedMoment B raw1138step0 raw1138step0Labels := by
      have ha : raw1138step0 = (fun i j => raw1138 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1138step0 raw1138; decide +kernel
      have hl : raw1138step0Labels = raw1138Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1138 raw1138Labels permutation8 permutation4
    _ = mixedMoment B node928 node928Labels := by rfl

theorem canonical1139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1139 raw1139Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw1139 raw1139Labels = mixedMoment B raw1139step0 raw1139step0Labels := by
      have ha : raw1139step0 = (fun i j => raw1139 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1139step0 raw1139; decide +kernel
      have hl : raw1139step0Labels = raw1139Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1139 raw1139Labels permutation31 permutation6
    mixedMoment B raw1139step0 raw1139step0Labels = mixedMoment B raw1139step1 raw1139step1Labels := by
      have ha : raw1139step1 = raw1139step0 := by apply Matrix.ext; unfold raw1139step1 raw1139step0; decide +kernel
      have hl : raw1139step0Labels = labelEmbedding1 ∘ raw1139step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1139step0 raw1139step0Labels raw1139step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

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

theorem singleton4174 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4174 node4174Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node602 node602Labels + mixedMoment B node1509 node1509Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw807 singletonSmall4174
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4174) = raw807Labels := by decide +kernel
  rw [hl, canonical807 B hB] at h
  have hc0 : mixedMoment B raw807 (Fin.cases (0 : Fin 2) singletonSmall4174) =
      mixedMoment B node602 node602Labels := by
    have ha : raw807 = raw808 := by apply Matrix.ext; unfold raw807 raw808; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4174 = raw808Labels := by decide +kernel
    rw [ha, hj, canonical808 B hB]
  have hc1 : mixedMoment B raw807 (Fin.cases (1 : Fin 2) singletonSmall4174) =
      mixedMoment B node1509 node1509Labels := by
    have ha : raw807 = raw809 := by apply Matrix.ext; unfold raw807 raw809; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4174 = raw809Labels := by decide +kernel
    rw [ha, hj, canonical809 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4181 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4181 node4181Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node609 node609Labels + mixedMoment B node1521 node1521Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw819 singletonSmall4181
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4181) = raw819Labels := by decide +kernel
  rw [hl, canonical819 B hB] at h
  have hc0 : mixedMoment B raw819 (Fin.cases (0 : Fin 2) singletonSmall4181) =
      mixedMoment B node609 node609Labels := by
    have ha : raw819 = raw820 := by apply Matrix.ext; unfold raw819 raw820; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4181 = raw820Labels := by decide +kernel
    rw [ha, hj, canonical820 B hB]
  have hc1 : mixedMoment B raw819 (Fin.cases (1 : Fin 2) singletonSmall4181) =
      mixedMoment B node1521 node1521Labels := by
    have ha : raw819 = raw821 := by apply Matrix.ext; unfold raw819 raw821; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4181 = raw821Labels := by decide +kernel
    rw [ha, hj, canonical821 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4190 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4190 node4190Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node618 node618Labels + mixedMoment B node1527 node1527Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw837 singletonSmall4190
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4190) = raw837Labels := by decide +kernel
  rw [hl, canonical837 B hB] at h
  have hc0 : mixedMoment B raw837 (Fin.cases (0 : Fin 2) singletonSmall4190) =
      mixedMoment B node618 node618Labels := by
    have ha : raw837 = raw838 := by apply Matrix.ext; unfold raw837 raw838; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4190 = raw838Labels := by decide +kernel
    rw [ha, hj, canonical838 B hB]
  have hc1 : mixedMoment B raw837 (Fin.cases (1 : Fin 2) singletonSmall4190) =
      mixedMoment B node1527 node1527Labels := by
    have ha : raw837 = raw839 := by apply Matrix.ext; unfold raw837 raw839; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4190 = raw839Labels := by decide +kernel
    rw [ha, hj, canonical839 B hB]
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

theorem singleton4343 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4343 node4343Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node921 node921Labels + mixedMoment B node1666 node1666Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1125 singletonSmall4343
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4343) = raw1125Labels := by decide +kernel
  rw [hl, canonical1125 B hB] at h
  have hc0 : mixedMoment B raw1125 (Fin.cases (0 : Fin 2) singletonSmall4343) =
      mixedMoment B node921 node921Labels := by
    have ha : raw1125 = raw1126 := by apply Matrix.ext; unfold raw1125 raw1126; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4343 = raw1126Labels := by decide +kernel
    rw [ha, hj, canonical1126 B hB]
  have hc1 : mixedMoment B raw1125 (Fin.cases (1 : Fin 2) singletonSmall4343) =
      mixedMoment B node1666 node1666Labels := by
    have ha : raw1125 = raw1127 := by apply Matrix.ext; unfold raw1125 raw1127; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4343 = raw1127Labels := by decide +kernel
    rw [ha, hj, canonical1127 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4350 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4350 node4350Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node928 node928Labels + mixedMoment B node1677 node1677Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1137 singletonSmall4350
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4350) = raw1137Labels := by decide +kernel
  rw [hl, canonical1137 B hB] at h
  have hc0 : mixedMoment B raw1137 (Fin.cases (0 : Fin 2) singletonSmall4350) =
      mixedMoment B node928 node928Labels := by
    have ha : raw1137 = raw1138 := by apply Matrix.ext; unfold raw1137 raw1138; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4350 = raw1138Labels := by decide +kernel
    rw [ha, hj, canonical1138 B hB]
  have hc1 : mixedMoment B raw1137 (Fin.cases (1 : Fin 2) singletonSmall4350) =
      mixedMoment B node1677 node1677Labels := by
    have ha : raw1137 = raw1139 := by apply Matrix.ext; unfold raw1137 raw1139; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4350 = raw1139Labels := by decide +kernel
    rw [ha, hj, canonical1139 B hB]
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

theorem singleton4496 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4496 node4496Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1080 node1080Labels + mixedMoment B node1710 node1710Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1296 singletonSmall4496
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4496) = raw1296Labels := by decide +kernel
  rw [hl, canonical1296 B hB] at h
  have hc0 : mixedMoment B raw1296 (Fin.cases (0 : Fin 2) singletonSmall4496) =
      mixedMoment B node1080 node1080Labels := by
    have ha : raw1296 = raw1297 := by apply Matrix.ext; unfold raw1296 raw1297; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4496 = raw1297Labels := by decide +kernel
    rw [ha, hj, canonical1297 B hB]
  have hc1 : mixedMoment B raw1296 (Fin.cases (1 : Fin 2) singletonSmall4496) =
      mixedMoment B node1710 node1710Labels := by
    have ha : raw1296 = raw1298 := by apply Matrix.ext; unfold raw1296 raw1298; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4496 = raw1298Labels := by decide +kernel
    rw [ha, hj, canonical1298 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node921 node921Labels = Sparse.eval nodeValue921 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 921) = mixedMoment B node921 node921Labels := rfl
  simpa [nodeValue921, Sparse.eval] using hc.symm

theorem sound928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node928 node928Labels = Sparse.eval nodeValue928 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 928) = mixedMoment B node928 node928Labels := rfl
  simpa [nodeValue928, Sparse.eval] using hc.symm

theorem sound937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node937 node937Labels = Sparse.eval nodeValue937 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 937) = mixedMoment B node937 node937Labels := rfl
  simpa [nodeValue937, Sparse.eval] using hc.symm

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

theorem sound1080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1080 node1080Labels = Sparse.eval nodeValue1080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1080) = mixedMoment B node1080 node1080Labels := rfl
  simpa [nodeValue1080, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1509 node1509Labels = Sparse.eval nodeValue1509 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1509) = mixedMoment B node1509 node1509Labels := rfl
  simpa [nodeValue1509, Sparse.eval] using hc.symm

theorem sound1521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1521 node1521Labels = Sparse.eval nodeValue1521 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1521) = mixedMoment B node1521 node1521Labels := rfl
  simpa [nodeValue1521, Sparse.eval] using hc.symm

theorem sound1527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1527 node1527Labels = Sparse.eval nodeValue1527 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1527) = mixedMoment B node1527 node1527Labels := rfl
  simpa [nodeValue1527, Sparse.eval] using hc.symm

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

theorem sound1666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1666 node1666Labels = Sparse.eval nodeValue1666 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1666) = mixedMoment B node1666 node1666Labels := rfl
  simpa [nodeValue1666, Sparse.eval] using hc.symm

theorem sound1677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1677 node1677Labels = Sparse.eval nodeValue1677 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1677) = mixedMoment B node1677 node1677Labels := rfl
  simpa [nodeValue1677, Sparse.eval] using hc.symm

theorem sound1683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1683 node1683Labels = Sparse.eval nodeValue1683 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1683) = mixedMoment B node1683 node1683Labels := rfl
  simpa [nodeValue1683, Sparse.eval] using hc.symm

theorem sound1710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1710 node1710Labels = Sparse.eval nodeValue1710 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1710) = mixedMoment B node1710 node1710Labels := rfl
  simpa [nodeValue1710, Sparse.eval] using hc.symm

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

theorem sound1741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1741 node1741Labels = Sparse.eval nodeValue1741 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1741) = mixedMoment B node1741 node1741Labels := rfl
  simpa [nodeValue1741, Sparse.eval] using hc.symm

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

theorem sound4085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4085 node4085Labels = Sparse.eval nodeValue4085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4085) = mixedMoment B node4085 node4085Labels := rfl
  simpa [nodeValue4085, Sparse.eval] using hc.symm

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

theorem sound602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node602 node602Labels = Sparse.eval nodeValue602 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 602) = mixedMoment B node602 node602Labels := rfl
  simpa [nodeValue602, Sparse.eval] using hc.symm

theorem sound609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node609 node609Labels = Sparse.eval nodeValue609 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 609) = mixedMoment B node609 node609Labels := rfl
  simpa [nodeValue609, Sparse.eval] using hc.symm

theorem sound618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node618 node618Labels = Sparse.eval nodeValue618 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 618) = mixedMoment B node618 node618Labels := rfl
  simpa [nodeValue618, Sparse.eval] using hc.symm

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

theorem sound4174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4174 node4174Labels = Sparse.eval nodeValue4174 (mixedVector B) := by
  have h := singleton4174 B _hB
  rw [sound602 B _hB _hF, sound1509 B _hB _hF] at h
  norm_num [nodeValue4174, nodeValue602, nodeValue1509, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4181 node4181Labels = Sparse.eval nodeValue4181 (mixedVector B) := by
  have h := singleton4181 B _hB
  rw [sound609 B _hB _hF, sound1521 B _hB _hF] at h
  norm_num [nodeValue4181, nodeValue609, nodeValue1521, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4190 node4190Labels = Sparse.eval nodeValue4190 (mixedVector B) := by
  have h := singleton4190 B _hB
  rw [sound618 B _hB _hF, sound1527 B _hB _hF] at h
  norm_num [nodeValue4190, nodeValue618, nodeValue1527, Sparse.eval] at h ⊢
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

theorem sound4343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4343 node4343Labels = Sparse.eval nodeValue4343 (mixedVector B) := by
  have h := singleton4343 B _hB
  rw [sound921 B _hB _hF, sound1666 B _hB _hF] at h
  norm_num [nodeValue4343, nodeValue921, nodeValue1666, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4350 node4350Labels = Sparse.eval nodeValue4350 (mixedVector B) := by
  have h := singleton4350 B _hB
  rw [sound928 B _hB _hF, sound1677 B _hB _hF] at h
  norm_num [nodeValue4350, nodeValue928, nodeValue1677, Sparse.eval] at h ⊢
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

theorem sound4359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4359 node4359Labels = Sparse.eval nodeValue4359 (mixedVector B) := by
  have h := singleton4359 B _hB
  rw [sound937 B _hB _hF, sound1683 B _hB _hF] at h
  norm_num [nodeValue4359, nodeValue937, nodeValue1683, Sparse.eval] at h ⊢
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

theorem zero4501 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4501 node4501Labels = 0 := by
  exact mixedMoment_order_one B hB node4501 node4501Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4512 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4512 node4512Labels = 0 := by
  exact mixedMoment_order_one B hB node4512 node4512Labels 1
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

theorem sound4496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4496 node4496Labels = Sparse.eval nodeValue4496 (mixedVector B) := by
  have h := singleton4496 B _hB
  rw [sound1080 B _hB _hF, sound1710 B _hB _hF] at h
  norm_num [nodeValue4496, nodeValue1080, nodeValue1710, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4501 node4501Labels = Sparse.eval nodeValue4501 (mixedVector B) := by
  simpa only [nodeValue4501, Sparse.eval_nil] using zero4501 B _hB _hF

theorem sound4510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4510 node4510Labels = Sparse.eval nodeValue4510 (mixedVector B) := by
  have h := singleton4510 B _hB
  rw [sound1094 B _hB _hF, sound1741 B _hB _hF] at h
  norm_num [nodeValue4510, nodeValue1094, nodeValue1741, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4512 node4512Labels = Sparse.eval nodeValue4512 (mixedVector B) := by
  simpa only [nodeValue4512, Sparse.eval_nil] using zero4512 B _hB _hF

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

theorem zero4837 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4837 node4837Labels = 0 := by
  exact mixedMoment_order_one B hB node4837 node4837Labels 1
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

theorem sound4837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4837 node4837Labels = Sparse.eval nodeValue4837 (mixedVector B) := by
  simpa only [nodeValue4837, Sparse.eval_nil] using zero4837 B _hB _hF

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

theorem zero4897 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4897 node4897Labels = 0 := by
  exact mixedMoment_order_one B hB node4897 node4897Labels 1
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

theorem sound4897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4897 node4897Labels = Sparse.eval nodeValue4897 (mixedVector B) := by
  simpa only [nodeValue4897, Sparse.eval_nil] using zero4897 B _hB _hF

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

theorem sourceEq1387 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1387 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1387 + difference 0 1) (sourceB1387 + difference 1 0) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA1387 + difference 0 1) (sourceB1387 + difference 1 0) sourceC1387) = raw21831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21831; decide +kernel
    rw [ha]
    exact (canonical21831 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1387 + difference 0 2) (sourceB1387 + difference 2 0) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA1387 + difference 0 2) (sourceB1387 + difference 2 0) sourceC1387) = raw21832 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21832; decide +kernel
    rw [ha]
    exact (canonical21832 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1387 + difference 0 3) (sourceB1387 + difference 3 0) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA1387 + difference 0 3) (sourceB1387 + difference 3 0) sourceC1387) = raw21833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21833; decide +kernel
    rw [ha]
    exact (canonical21833 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1387 + difference 0 4) (sourceB1387 + difference 4 0) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA1387 + difference 0 4) (sourceB1387 + difference 4 0) sourceC1387) = raw19891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw19891; decide +kernel
    rw [ha]
    exact (canonical19891 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1387 + difference 0 5) (sourceB1387 + difference 5 0) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA1387 + difference 0 5) (sourceB1387 + difference 5 0) sourceC1387) = raw21834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21834; decide +kernel
    rw [ha]
    exact (canonical21834 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1387 + difference 1 0) (sourceB1387 + difference 0 1) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4174) := by
    have ha : (tripleCharges (sourceA1387 + difference 1 0) (sourceB1387 + difference 0 1) sourceC1387) = raw21835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21835; decide +kernel
    rw [ha]
    exact (canonical21835 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1387 + difference 1 2) (sourceB1387 + difference 2 1) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA1387 + difference 1 2) (sourceB1387 + difference 2 1) sourceC1387) = raw21836 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21836; decide +kernel
    rw [ha]
    exact (canonical21836 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1387 + difference 1 3) (sourceB1387 + difference 3 1) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA1387 + difference 1 3) (sourceB1387 + difference 3 1) sourceC1387) = raw21837 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21837; decide +kernel
    rw [ha]
    exact (canonical21837 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1387 + difference 1 4) (sourceB1387 + difference 4 1) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1387 + difference 1 4) (sourceB1387 + difference 4 1) sourceC1387) = raw19896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw19896; decide +kernel
    rw [ha]
    exact (canonical19896 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1387 + difference 1 5) (sourceB1387 + difference 5 1) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1387 + difference 1 5) (sourceB1387 + difference 5 1) sourceC1387) = raw21838 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21838; decide +kernel
    rw [ha]
    exact (canonical21838 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1387 + difference 2 0) (sourceB1387 + difference 0 2) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4174) := by
    have ha : (tripleCharges (sourceA1387 + difference 2 0) (sourceB1387 + difference 0 2) sourceC1387) = raw21839 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21839; decide +kernel
    rw [ha]
    exact (canonical21839 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1387 + difference 2 1) (sourceB1387 + difference 1 2) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA1387 + difference 2 1) (sourceB1387 + difference 1 2) sourceC1387) = raw21840 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21840; decide +kernel
    rw [ha]
    exact (canonical21840 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1387 + difference 2 3) (sourceB1387 + difference 3 2) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA1387 + difference 2 3) (sourceB1387 + difference 3 2) sourceC1387) = raw21841 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21841; decide +kernel
    rw [ha]
    exact (canonical21841 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1387 + difference 2 4) (sourceB1387 + difference 4 2) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1387 + difference 2 4) (sourceB1387 + difference 4 2) sourceC1387) = raw19901 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw19901; decide +kernel
    rw [ha]
    exact (canonical19901 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1387 + difference 2 5) (sourceB1387 + difference 5 2) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1387 + difference 2 5) (sourceB1387 + difference 5 2) sourceC1387) = raw21842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21842; decide +kernel
    rw [ha]
    exact (canonical21842 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1387 + difference 3 0) (sourceB1387 + difference 0 3) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4174) := by
    have ha : (tripleCharges (sourceA1387 + difference 3 0) (sourceB1387 + difference 0 3) sourceC1387) = raw21843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21843; decide +kernel
    rw [ha]
    exact (canonical21843 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1387 + difference 3 1) (sourceB1387 + difference 1 3) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA1387 + difference 3 1) (sourceB1387 + difference 1 3) sourceC1387) = raw21844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21844; decide +kernel
    rw [ha]
    exact (canonical21844 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1387 + difference 3 2) (sourceB1387 + difference 2 3) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA1387 + difference 3 2) (sourceB1387 + difference 2 3) sourceC1387) = raw21845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21845; decide +kernel
    rw [ha]
    exact (canonical21845 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1387 + difference 3 4) (sourceB1387 + difference 4 3) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1387 + difference 3 4) (sourceB1387 + difference 4 3) sourceC1387) = raw19906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw19906; decide +kernel
    rw [ha]
    exact (canonical19906 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1387 + difference 3 5) (sourceB1387 + difference 5 3) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1387 + difference 3 5) (sourceB1387 + difference 5 3) sourceC1387) = raw21846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21846; decide +kernel
    rw [ha]
    exact (canonical21846 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1387 + difference 4 0) (sourceB1387 + difference 0 4) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4190) := by
    have ha : (tripleCharges (sourceA1387 + difference 4 0) (sourceB1387 + difference 0 4) sourceC1387) = raw21847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21847; decide +kernel
    rw [ha]
    exact (canonical21847 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1387 + difference 4 1) (sourceB1387 + difference 1 4) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4359) := by
    have ha : (tripleCharges (sourceA1387 + difference 4 1) (sourceB1387 + difference 1 4) sourceC1387) = raw21848 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21848; decide +kernel
    rw [ha]
    exact (canonical21848 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1387 + difference 4 2) (sourceB1387 + difference 2 4) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4359) := by
    have ha : (tripleCharges (sourceA1387 + difference 4 2) (sourceB1387 + difference 2 4) sourceC1387) = raw21849 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21849; decide +kernel
    rw [ha]
    exact (canonical21849 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1387 + difference 4 3) (sourceB1387 + difference 3 4) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4359) := by
    have ha : (tripleCharges (sourceA1387 + difference 4 3) (sourceB1387 + difference 3 4) sourceC1387) = raw21850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21850; decide +kernel
    rw [ha]
    exact (canonical21850 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1387 + difference 4 5) (sourceB1387 + difference 5 4) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4510) := by
    have ha : (tripleCharges (sourceA1387 + difference 4 5) (sourceB1387 + difference 5 4) sourceC1387) = raw21851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21851; decide +kernel
    rw [ha]
    exact (canonical21851 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1387 + difference 5 0) (sourceB1387 + difference 0 5) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4181) := by
    have ha : (tripleCharges (sourceA1387 + difference 5 0) (sourceB1387 + difference 0 5) sourceC1387) = raw19907 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw19907; decide +kernel
    rw [ha]
    exact (canonical19907 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1387 + difference 5 1) (sourceB1387 + difference 1 5) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA1387 + difference 5 1) (sourceB1387 + difference 1 5) sourceC1387) = raw19908 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw19908; decide +kernel
    rw [ha]
    exact (canonical19908 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1387 + difference 5 2) (sourceB1387 + difference 2 5) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA1387 + difference 5 2) (sourceB1387 + difference 2 5) sourceC1387) = raw19909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw19909; decide +kernel
    rw [ha]
    exact (canonical19909 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1387 + difference 5 3) (sourceB1387 + difference 3 5) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA1387 + difference 5 3) (sourceB1387 + difference 3 5) sourceC1387) = raw19910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw19910; decide +kernel
    rw [ha]
    exact (canonical19910 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1387 + difference 5 4) (sourceB1387 + difference 4 5) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4512) := by
    have ha : (tripleCharges (sourceA1387 + difference 5 4) (sourceB1387 + difference 4 5) sourceC1387) = raw21852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21852; decide +kernel
    rw [ha]
    exact (canonical21852 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1387 sourceB1387 sourceC1387
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1387, Integer.Sparse.eval]
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

theorem reindexCheck1197 : Integer.Sparse.reindex keyMap MixedData.row1197 = numericRow1197 := by decide +kernel

theorem numericCheck1197 (x : Master → ℝ) : Integer.Sparse.eval numericRow1197 x =
    (4 : ℝ) * reducedSource1197 x := by
  norm_num [numericRow1197, reducedSource1197, Integer.Sparse.eval, Sparse.eval, nodeValue4085, nodeValue4174, nodeValue4181, nodeValue4190, nodeValue4343, nodeValue4350, nodeValue4359, nodeValue4496, nodeValue4501, nodeValue4510, nodeValue4512, nodeValue4837, nodeValue4897] <;> ring

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

theorem reducedZero1197 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1197 (mixedVector B) = 0 := by
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  have h4174 : mixedVector B (Sum.inr 4174) = Sparse.eval nodeValue4174 (mixedVector B) := by
    change mixedMoment B node4174 node4174Labels = _
    exact sound4174 B hB hF
  have h4181 : mixedVector B (Sum.inr 4181) = Sparse.eval nodeValue4181 (mixedVector B) := by
    change mixedMoment B node4181 node4181Labels = _
    exact sound4181 B hB hF
  have h4190 : mixedVector B (Sum.inr 4190) = Sparse.eval nodeValue4190 (mixedVector B) := by
    change mixedMoment B node4190 node4190Labels = _
    exact sound4190 B hB hF
  have h4343 : mixedVector B (Sum.inr 4343) = Sparse.eval nodeValue4343 (mixedVector B) := by
    change mixedMoment B node4343 node4343Labels = _
    exact sound4343 B hB hF
  have h4350 : mixedVector B (Sum.inr 4350) = Sparse.eval nodeValue4350 (mixedVector B) := by
    change mixedMoment B node4350 node4350Labels = _
    exact sound4350 B hB hF
  have h4359 : mixedVector B (Sum.inr 4359) = Sparse.eval nodeValue4359 (mixedVector B) := by
    change mixedMoment B node4359 node4359Labels = _
    exact sound4359 B hB hF
  have h4496 : mixedVector B (Sum.inr 4496) = Sparse.eval nodeValue4496 (mixedVector B) := by
    change mixedMoment B node4496 node4496Labels = _
    exact sound4496 B hB hF
  have h4501 : mixedVector B (Sum.inr 4501) = Sparse.eval nodeValue4501 (mixedVector B) := by
    change mixedMoment B node4501 node4501Labels = _
    exact sound4501 B hB hF
  have h4510 : mixedVector B (Sum.inr 4510) = Sparse.eval nodeValue4510 (mixedVector B) := by
    change mixedMoment B node4510 node4510Labels = _
    exact sound4510 B hB hF
  have h4512 : mixedVector B (Sum.inr 4512) = Sparse.eval nodeValue4512 (mixedVector B) := by
    change mixedMoment B node4512 node4512Labels = _
    exact sound4512 B hB hF
  have h4837 : mixedVector B (Sum.inr 4837) = Sparse.eval nodeValue4837 (mixedVector B) := by
    change mixedMoment B node4837 node4837Labels = _
    exact sound4837 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  simpa only [sourceForm1387, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4085, h4174, h4181, h4190, h4343, h4350, h4359, h4496, h4501, h4510, h4512, h4837, h4897, reducedSource1197] using sourceEq1387 B hB

theorem rowSound1197_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1197 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1197, numericCheck1197, reducedZero1197 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1197_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1197_e_oai
