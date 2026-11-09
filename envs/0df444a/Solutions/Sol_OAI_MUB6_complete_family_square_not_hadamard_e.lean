-- Prove2me | solution 1 for OAI.MUB6.complete_family_square_not_hadamard_e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T15:27:33.627518+00:00
-- url     : https://prove2.me/submissions/de504a11-c19c-4b05-9ceb-5cb07f855067
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E154
import Definitions.Def_OAIQ106E156
import Definitions.Def_OAIQ106E157
import Definitions.Def_OAIQ106E168
import Definitions.Def_OAIQ106E169
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_TaoCertificate_combined474_zero_e

section
-- module Solutions.OAIQ106_MUB.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
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
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
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

theorem character_mul (x y : Coord → ℂ) (a : Charge) :
    character (x * y) a = character x a * character y a := by
  simp only [character, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem character_constant (z : ℂ) (hz : z ≠ 0) (a : Charge) (ha : Balanced a) :
    character (fun _ => z) a = 1 := by
  have hp (s : Finset Coord) : (∏ i ∈ s, z ^ a i) = z ^ (∑ i ∈ s, a i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hz]
  rw [character, hp, ha, zpow_zero]

theorem g_row_phase (H : CMatrix) (u : Coord → ℂ) (a : Charge) :
    g (fun i j => u i * H i j) a = character u a * g H a := by
  simp only [g]
  simp_rw [show ∀ k, character (fun i => u i * H i k) a =
    character u a * character (fun i => H i k) a from
      fun k => character_mul u (fun i => H i k) a]
  rw [← Finset.mul_sum]
  ring

theorem g_column_phase (H : CMatrix) (v : Coord → ℂ) (hv : ∀ j, v j ≠ 0)
    (a : Charge) (ha : Balanced a) :
    g (fun i j => H i j * v j) a = g H a := by
  simp only [g]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact (character_mul (fun i => H i k) (fun _ => v k) a).trans
    (by rw [character_constant (v k) (hv k) a ha, mul_one])

theorem g_column_permutation (H : CMatrix) (π : Equiv.Perm Coord) (a : Charge) :
    g (fun i j => H i (π j)) a = g H a := by
  exact congrArg ((6 : ℂ)⁻¹ * ·) (Equiv.sum_comp π (fun k => character (fun i => H i k) a))

theorem character_permutation (x : Coord → ℂ) (π : Equiv.Perm Coord) (a : Charge) :
    character (x ∘ π) a = character x (permuteCharge π.symm a) := by
  unfold character permuteCharge
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp π (fun i => x i ^ a (π.symm i))

theorem g_row_permutation (H : CMatrix) (π : Equiv.Perm Coord) (a : Charge) :
    g (fun i j => H (π i) j) a = g H (permuteCharge π.symm a) := by
  simp only [g]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact character_permutation (fun i => H i k) π a

theorem equivalent_trans {H K L : CMatrix} (h₁ : Equivalent H K)
    (h₂ : Equivalent K L) : Equivalent H L := by
  rcases h₁ with ⟨r, c, u, v, hu, hv, h₁⟩
  rcases h₂ with ⟨r', c', u', v', hu', hv', h₂⟩
  refine ⟨r'.trans r, c'.trans c, (fun i => u' i * u (r' i)),
    (fun j => v (c' j) * v' j), ?_, ?_, ?_⟩
  · intro i
    simp [map_mul, hu, hu']
  · intro j
    simp [map_mul, hv, hv']
  · intro i j
    rw [h₂, h₁]
    simp [mul_assoc]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_IntegerMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation-preserving sparse integer merge. Its soundness needs no sorting
hypothesis: ordering is only used to make generated witnesses short. Each merge
can be checked independently by a finite integer-list equality. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*}

theorem eval_mergeFuel [LinearOrder ι] (fuel : ℕ) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeFuel fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeFuel]
      | cons b bs =>
        simp only [mergeFuel]
        split_ifs with hlt heq hz
        · simp only [eval_cons, ih]
          ring
        · simp only [ih, eval_cons]
          have hc : (a.2 : ℝ) + (b.2 : ℝ) = 0 := by exact_mod_cast hz
          have hcx := congrArg (fun z : ℝ => z * x b.1) hc
          simp only [add_mul, zero_mul] at hcx
          rw [heq]
          linarith
        · simp only [eval_cons, ih, Int.cast_add]
          rw [heq]
          ring
        · simp only [eval_cons, ih]
          ring

@[simp] theorem eval_merge [LinearOrder ι] (a b : Sparse ι) (x : ι → ℝ) :
    eval (merge a b) x = eval a x + eval b x := eval_mergeFuel _ _ _ _

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three-by-three block obstruction in cubic classification, proved by
Newton's determinant identity instead of a dimension argument. -/

noncomputable section
open scoped BigOperators ComplexConjugate Matrix

namespace MUB6

theorem trace_newton_three (C : Matrix (Fin 3) (Fin 3) ℂ) :
    6 * C.det = C.trace ^ 3 - 3 * C.trace * (C * C).trace +
      2 * (C * C * C).trace := by
  simp [Matrix.det_fin_three, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fin.sum_univ_succ]
  ring

/-- A three-dimensional projection cannot have rank three halves.  This
formulation needs only polynomial identities over the complex numbers. -/
theorem no_three_by_three_scaled_projection (C : Matrix (Fin 3) (Fin 3) ℂ)
    (hC : C * C = (6 : ℂ) • C) (ht : C.trace = 9) : False := by
  have ht2 : (C * C).trace = 54 := by rw [hC, Matrix.trace_smul, ht]; norm_num
  have ht3 : (C * C * C).trace = 324 := by
    rw [hC, Matrix.smul_mul, hC, Matrix.trace_smul, Matrix.trace_smul, ht]
    norm_num
  have hn := trace_newton_three C
  rw [ht, ht2, ht3] at hn
  have hd : C.det = (-27 / 2 : ℂ) := by linear_combination hn / 6
  have hdm := congrArg Matrix.det hC
  rw [Matrix.det_mul, Matrix.det_smul, hd] at hdm
  norm_num at hdm

/-- The two classes of three restricted rows cannot be mutually orthogonal
when their combined columns are orthogonal and every entry has modulus one. -/
theorem no_cubic_three_by_three_block
    (A B : Matrix (Fin 3) (Fin 3) ℂ)
    (hunit : ∀ i j, Complex.normSq (A i j) = 1)
    (hcross : A * B.conjTranspose = 0)
    (hcol : A.conjTranspose * A + B.conjTranspose * B = (6 : ℂ) • 1) : False := by
  let C := A.conjTranspose * A
  have hCD : C * (B.conjTranspose * B) = 0 := by
    dsimp [C]
    calc
      A.conjTranspose * A * (B.conjTranspose * B) =
          A.conjTranspose * (A * B.conjTranspose) * B := by
            simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hcross, Matrix.mul_zero, Matrix.zero_mul]
  have hC : C * C = (6 : ℂ) • C := by
    calc
      C * C = C * (C + B.conjTranspose * B) := by rw [Matrix.mul_add, hCD, add_zero]
      _ = C * ((6 : ℂ) • 1) := by rw [hcol]
      _ = (6 : ℂ) • C := by rw [Matrix.mul_smul, Matrix.mul_one]
  have ht : C.trace = 9 := by
    have hh (i j : Fin 3) : conj (A i j) * A i j = (1 : ℂ) := by
      rw [mul_comm, Complex.mul_conj, hunit]
      rfl
    change (∑ i, ∑ j, conj (A j i) * A j i) = 9
    norm_num [hh]
  exact no_three_by_three_scaled_projection C hC ht

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common-support step of the cubic classification in §3.

These lemmas concern two three-element supports avoiding coordinate zero.
The last theorem states that a quotient having the cubed-value pattern proved
for Hadamard row ratios forces the supports to coincide.
-/

noncomputable section

namespace MUB6

theorem value_pair_exhausts (f : (Fin 6) → ℂ)
    (hf : ∃ a b : ℂ, ∀ i, f i = a ∨ f i = b)
    (i j : (Fin 6)) (hij : f i ≠ f j) : ∀ k, f k = f i ∨ f k = f j := by
  obtain ⟨a, b, hf⟩ := hf
  rcases hf i with hi | hi
  · rcases hf j with hj | hj
    · exact False.elim (hij (hi.trans hj.symm))
    · intro k
      exact (hf k).imp (fun h => h.trans hi.symm) (fun h => h.trans hj.symm)
  · rcases hf j with hj | hj
    · intro k
      exact (hf k).symm.imp (fun h => h.trans hi.symm) (fun h => h.trans hj.symm)
    · exact False.elim (hij (hi.trans hj.symm))

theorem three_supports_have_witnesses (S U : Finset (Fin 6))
    (hS : S.card = 3) (hU : U.card = 3)
    (hS0 : (0 : (Fin 6)) ∉ S) (hU0 : (0 : (Fin 6)) ∉ U) (hne : S ≠ U) :
    (S \ U).Nonempty ∧ (U \ S).Nonempty ∧ (S ∩ U).Nonempty := by
  have hSU : (S \ U).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    apply hne
    exact Finset.eq_of_subset_of_card_le
      (Finset.sdiff_eq_empty_iff_subset.mp h) (by omega)
  have hUS : (U \ S).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    apply hne
    exact (Finset.eq_of_subset_of_card_le
      (Finset.sdiff_eq_empty_iff_subset.mp h) (by omega)).symm
  have hbound : (S ∪ U).card ≤ 5 := by
    have hsub : S ∪ U ⊆ (Finset.univ : Finset (Fin 6)).erase 0 := by
      intro i hi
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ i⟩
      intro heq
      subst i
      rcases Finset.mem_union.mp hi with hi | hi
      · exact hS0 hi
      · exact hU0 hi
    simpa using Finset.card_le_card hsub
  have hcount : (S ∪ U).card + (S ∩ U).card = 6 := by
    simpa [hS, hU] using Finset.card_union_add_card_inter S U
  have hpos : 0 < (S ∩ U).card := by omega
  exact ⟨hSU, hUS, Finset.card_pos.mp hpos⟩

/-- For two subsets of size three in a six-element set, the number of
coordinates on which membership agrees is even, hence cannot be three. -/
theorem same_membership_card_ne_three (S U : Finset (Fin 6))
    (hS : S.card = 3) (hU : U.card = 3) :
    (Finset.univ.filter (fun i => (i ∈ S ↔ i ∈ U))).card ≠ 3 := by
  have heq : Finset.univ.filter (fun i => (i ∈ S ↔ i ∈ U)) =
      (S ∩ U) ∪ (S ∪ U)ᶜ := by
    ext i
    by_cases hs : i ∈ S <;> by_cases hu : i ∈ U <;> simp [hs, hu]
  have hdisj : Disjoint (S ∩ U) (S ∪ U)ᶜ := by
    apply Finset.disjoint_left.mpr
    intro i hi hnot
    exact (Finset.mem_compl.mp hnot)
      (Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hi).1))
  have hcount : (S ∪ U).card + (S ∩ U).card = 6 := by
    simpa [hS, hU] using Finset.card_union_add_card_inter S U
  intro hbad
  rw [heq, Finset.card_union_of_disjoint hdisj, Finset.card_compl] at hbad
  change (S ∩ U).card + (6 - (S ∪ U).card) = 3 at hbad
  omega

/-- The exact common-support claim: a ratio of two nonconstant cubed rows
cannot have the necessary three-and-three multiplicities on distinct supports. -/
theorem common_support_of_twoValuePattern (S U : Finset (Fin 6))
    (hS : S.card = 3) (hU : U.card = 3)
    (hS0 : (0 : (Fin 6)) ∉ S) (hU0 : (0 : (Fin 6)) ∉ U)
    (x y : ℂ) (hx0 : x ≠ 0)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hp : TwoValuePattern (supportedRatio S U x y)) : S = U := by
  classical
  by_contra hne
  obtain ⟨⟨s, hs⟩, ⟨t, ht⟩, ⟨u, hu⟩⟩ :=
    three_supports_have_witnesses S U hS hU hS0 hU0 hne
  obtain ⟨hsS, hsU⟩ := Finset.mem_sdiff.mp hs
  obtain ⟨htU, htS⟩ := Finset.mem_sdiff.mp ht
  obtain ⟨huS, huU⟩ := Finset.mem_inter.mp hu
  let f := supportedRatio S U x y
  have hf0 : f 0 = 1 := by simp [f, supportedRatio, supportedValue, hS0, hU0]
  have hfs : f s = x := by simp [f, supportedRatio, supportedValue, hsS, hsU]
  have hft : f t = y⁻¹ := by simp [f, supportedRatio, supportedValue, htS, htU]
  have hfu : f u = x / y := by simp [f, supportedRatio, supportedValue, huS, huU]
  have hdist : f 0 ≠ f s := by simpa [hf0, hfs] using Ne.symm hx1
  have hvalues : ∀ i, f i = 1 ∨ f i = x := by
    simpa [hf0, hfs] using value_pair_exhausts f hp.1 0 s hdist
  have hinv : y⁻¹ = x := by
    have htvalues := hvalues t
    rw [hft] at htvalues
    exact htvalues.resolve_left (by simpa using hy1)
  have hxx : x ^ 2 = 1 ∨ x ^ 2 = x := by
    have huvalues := hvalues u
    simpa [hfu, div_eq_mul_inv, hinv, pow_two] using huvalues
  have hsq : x ^ 2 = 1 := by
    rcases hxx with h | h
    · exact h
    · have hprod : x * (x - 1) = 0 := by linear_combination h
      exact False.elim (hx1 (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hx0)))
  have hxminus : x = -1 := (sq_eq_one_iff.mp hsq).resolve_left hx1
  have hyminus : y = -1 := by
    have h := congrArg (fun z : ℂ => z⁻¹) hinv
    simpa [hxminus] using h
  have hones : (Finset.univ.filter (fun i => f i = 1)).card = 3 :=
    hp.2 1 ⟨0, hf0⟩ ⟨s, by change f s ≠ 1; rw [hfs]; exact hx1⟩
  have hset : Finset.univ.filter (fun i => f i = 1) =
      Finset.univ.filter (fun i => (i ∈ S ↔ i ∈ U)) := by
    ext i
    by_cases hs : i ∈ S <;> by_cases hu : i ∈ U <;>
      norm_num [f, supportedRatio, supportedValue, hxminus, hyminus, hs, hu]
  rw [hset] at hones
  exact same_membership_card_ne_three S U hS hU hones

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! From cubed row-ratio patterns to the single three-by-three exceptional block. -/

noncomputable section

namespace MUB6

theorem twoValuePattern_supported (f : Fin 6 → ℂ) (hf : TwoValuePattern f)
    (hf0 : f 0 = 1) (j : Fin 6) (hj : f j ≠ 1) :
    (nonOneSupport f).card = 3 ∧ (0 : Fin 6) ∉ nonOneSupport f ∧
      ∀ i, f i = supportedValue (nonOneSupport f) (f j) i := by
  classical
  have hd : f 0 ≠ f j := by rw [hf0]; exact Ne.symm hj
  have hv : ∀ i, f i = 1 ∨ f i = f j := by
    simpa only [hf0] using value_pair_exhausts f hf.1 0 j hd
  have hs : nonOneSupport f = Finset.univ.filter (fun i => f i = f j) := by
    ext i
    simp only [mem_nonOneSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => (hv i).resolve_left h
    · intro h
      simpa only [h] using hj
  refine ⟨?_, by simp [hf0], ?_⟩
  · rw [hs]
    exact hf.2 (f j) ⟨j, rfl⟩ ⟨0, hd⟩
  · intro i
    by_cases hi : f i = 1
    · simp [supportedValue, hi]
    · simp [supportedValue, (hv i).resolve_left hi]

theorem dephased_pattern_single_block (F : Fin 6 → Fin 6 → ℂ)
    (h0row : ∀ j, F 0 j = 1) (h0col : ∀ i, F i 0 = 1)
    (hnz : ∀ i j, F i j ≠ 0)
    (hrow : ∀ i, TwoValuePattern (F i))
    (hcol : ∀ j, TwoValuePattern (fun i => F i j))
    (hratio : ∀ i r, i ≠ r → TwoValuePattern (fun j => F i j / F r j))
    (i j : Fin 6) (hij : F i j ≠ 1) :
    ∃ (R S : Finset (Fin 6)) (x : ℂ),
      R.card = 3 ∧ S.card = 3 ∧ (0 : Fin 6) ∉ R ∧ (0 : Fin 6) ∉ S ∧
      x ≠ 0 ∧ x ≠ 1 ∧
      ∀ r c, F r c = if r ∈ R ∧ c ∈ S then x else 1 := by
  classical
  let R := nonOneSupport (fun r => F r j)
  let S := nonOneSupport (F i)
  obtain ⟨hScard, hS0, hSvalue⟩ :=
    twoValuePattern_supported (F i) (hrow i) (h0col i) j hij
  obtain ⟨hRcard, hR0, hRvalue⟩ :=
    twoValuePattern_supported (fun r => F r j) (hcol j) (h0row j) i hij
  have hsamesupport (r c : Fin 6) (hrc : F r c ≠ 1) : nonOneSupport (F r) = S := by
    by_cases hri : r = i
    · subst r
      rfl
    obtain ⟨hUcard, hU0, hUvalue⟩ :=
      twoValuePattern_supported (F r) (hrow r) (h0col r) c hrc
    apply common_support_of_twoValuePattern _ _ hUcard hScard hU0 hS0
      (F r c) (F i j) (hnz r c) hrc hij
    have hq := hratio r i hri
    have heq : (fun k => F r k / F i k) =
        supportedRatio (nonOneSupport (F r)) S (F r c) (F i j) := by
      funext k
      rw [hUvalue k, hSvalue k]
      rfl
    rwa [← heq]
  refine ⟨R, S, F i j, hRcard, hScard, hR0, hS0, hnz i j, hij, ?_⟩
  intro r c
  by_cases hr : r ∈ R
  · have hr' : r ∈ nonOneSupport (fun r => F r j) := hr
    have hrj : F r j ≠ 1 := (mem_nonOneSupport (fun r => F r j) r).mp hr'
    obtain ⟨_, _, hv⟩ :=
      twoValuePattern_supported (F r) (hrow r) (h0col r) j hrj
    have hval : F r j = F i j := by
      simpa only [supportedValue, ite_eq_left hr'] using hRvalue r
    rw [hv c, hsamesupport r j hrj, hval]
    simp [supportedValue, hr]
  · have hrc : F r c = 1 := by
      by_contra hc
      have hs := hsamesupport r c hc
      have hjS : j ∈ S := (mem_nonOneSupport _ _).mpr hij
      have hjU : j ∈ nonOneSupport (F r) := by rwa [hs]
      exact hr ((mem_nonOneSupport (fun r => F r j) r).mpr
        ((mem_nonOneSupport (F r) j).mp hjU))
    simp [hr, hrc]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicSymmetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary symmetric sums for the six-entry cubic classification. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_product_complement (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1) (s : Finset (Fin 6)) :
    (∏ i, v i) * conj (∏ i ∈ s, v i) = ∏ i ∈ sᶜ, v i := by
  rw [← Finset.prod_mul_prod_compl s v, map_prod]
  calc
    ((∏ i ∈ s, v i) * ∏ i ∈ sᶜ, v i) * ∏ i ∈ s, conj (v i) =
        (∏ i ∈ sᶜ, v i) * ∏ i ∈ s, (v i * conj (v i)) := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = ∏ i ∈ sᶜ, v i := by simp [Complex.mul_conj, hv]

theorem elementarySum_reciprocal (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1) (k : ℕ) (hk : k ≤ 6) :
    (∏ i, v i) * conj (elementarySum v k) = elementarySum v (6 - k) := by
  unfold elementarySum
  rw [map_sum, Finset.mul_sum]
  simp_rw [unit_product_complement v hv]
  refine Finset.sum_bij (fun s _ => sᶜ) ?_ ?_ ?_ ?_
  · intro s hs
    have hc := (Finset.mem_powersetCard.mp hs).2
    simp [Finset.mem_powersetCard, Finset.card_compl, hc]
  · intro s _hs t _ht h
    simpa using congrArg (fun u : Finset (Fin 6) => uᶜ) h
  · intro t ht
    refine ⟨tᶜ, ?_, by simp⟩
    have hc := (Finset.mem_powersetCard.mp ht).2
    have hsub : 6 - (6 - k) = k := by omega
    simp [Finset.mem_powersetCard, Finset.card_compl, hc, hsub]
  · intro _subset _membership
    rfl

theorem elementarySum_zero (v : (Fin 6) → ℂ) : elementarySum v 0 = 1 := by
  simp [elementarySum]

theorem elementarySum_six (v : (Fin 6) → ℂ) : elementarySum v 6 = ∏ i, v i := by
  have h : (Finset.univ : Finset (Fin 6)).powersetCard 6 = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin 6))
  simp [elementarySum, h]

theorem elementarySum_one (v : (Fin 6) → ℂ) : elementarySum v 1 = ∑ i, v i := by
  simp [elementarySum, Finset.powersetCard_one]

private theorem coordinate_pairs :
    (Finset.univ : Finset (Fin 6)).powersetCard 2 =
      {{0, 1}, {0, 2}, {0, 3}, {0, 4}, {0, 5},
       {1, 2}, {1, 3}, {1, 4}, {1, 5},
       {2, 3}, {2, 4}, {2, 5}, {3, 4}, {3, 5}, {4, 5}} := by
  decide

/-- Newton's identity at degree two, specialized to exactly six entries. -/
theorem elementarySum_two_identity (v : (Fin 6) → ℂ) :
    (∑ i, v i) ^ 2 = (∑ i, v i ^ 2) + 2 * elementarySum v 2 := by
  simp (disch := decide) [elementarySum, coordinate_pairs, Fin.sum_univ_succ]
  ring

theorem elementarySum_one_two_zero (v : (Fin 6) → ℂ)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) :
    elementarySum v 1 = 0 ∧ elementarySum v 2 = 0 := by
  refine ⟨by simpa [elementarySum_one] using h1, ?_⟩
  have h := elementarySum_two_identity v
  rw [h1, h2] at h
  linear_combination -h / 2

theorem elementarySum_four_five_zero (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) :
    elementarySum v 4 = 0 ∧ elementarySum v 5 = 0 := by
  obtain ⟨h1', h2'⟩ := elementarySum_one_two_zero v h1 h2
  constructor
  · simpa [h2'] using (elementarySum_reciprocal v hv 2 (by decide)).symm
  · simpa [h1'] using (elementarySum_reciprocal v hv 1 (by decide)).symm

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicMultiplicityCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplicity counting once the two possible cubed values are known. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_cube_mul_conj_square {z : ℂ} (hz : Complex.normSq z = 1) :
    z ^ 3 * (conj z) ^ 2 = z := by
  calc
    z ^ 3 * (conj z) ^ 2 = z * (z * conj z) ^ 2 := by ring
    _ = z := by simp [Complex.mul_conj, hz]

/-- A nonempty zero-sum collection of nonzero numbers with the same cube has
at least three members: one term cannot vanish, and two opposite terms have
opposite cubes. -/
theorem same_cube_zero_sum_card_ge_three (v : (Fin 6) → ℂ) (s : Finset (Fin 6))
    (a : ℂ) (ha : a ≠ 0) (hne : s.Nonempty)
    (hcube : ∀ i ∈ s, v i ^ 3 = a) (hsum : ∑ i ∈ s, v i = 0) :
    3 ≤ s.card := by
  by_contra h
  have hp := hne.card_pos
  have hc : s.card = 1 ∨ s.card = 2 := by omega
  rcases hc with hc | hc
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
    have hi := hcube i (by simp)
    simp only [Finset.sum_singleton] at hsum
    exact ha (by simpa [hsum] using hi.symm)
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hc
    have hi := hcube i (by simp)
    have hj := hcube j (by simp)
    have hsum' : v i + v j = 0 := by simpa [hij] using hsum
    have hneg : v i = -v j := eq_neg_of_add_eq_zero_left hsum'
    have hanti : -a = a := by
      calc
        -a = -(v j ^ 3) := by rw [hj]
        _ = (-v j) ^ 3 := by ring
        _ = a := by simpa only [hneg] using hi
    apply ha
    linear_combination -(1 / 2 : ℂ) * hanti

theorem two_cube_classes_card_three (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0)
    (a b : ℂ) (hab : a ≠ b)
    (hvalues : ∀ i, v i ^ 3 = a ∨ v i ^ 3 = b)
    (ia ib : (Fin 6)) (hia : v ia ^ 3 = a) (hib : v ib ^ 3 = b) :
    (cubeClass v a).card = 3 ∧ (cubeClass v b).card = 3 ∧
      (∑ i ∈ cubeClass v a, v i) = 0 ∧ (∑ i ∈ cubeClass v b, v i) = 0 := by
  classical
  let A := cubeClass v a
  have hAcube : ∀ i ∈ A, v i ^ 3 = a := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hBcube : ∀ i ∈ Aᶜ, v i ^ 3 = b := by
    intro i hi
    have hnot : v i ^ 3 ≠ a := by simpa [A, cubeClass] using hi
    exact (hvalues i).resolve_left hnot
  have hB : Aᶜ = cubeClass v b := by
    ext i
    simp only [cubeClass, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact hBcube i
    · intro hi
      have hnot : v i ^ 3 ≠ a := by
        intro heq
        exact hab (heq.symm.trans hi)
      simpa [A, cubeClass] using hnot
  let qa := ∑ i ∈ A, (conj (v i)) ^ 2
  let qb := ∑ i ∈ Aᶜ, (conj (v i)) ^ 2
  have hqa : (∑ i ∈ A, v i) = a * qa := by
    dsimp [qa]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hu := unit_cube_mul_conj_square (hv i)
    rw [hAcube i hi] at hu
    exact hu.symm
  have hqb : (∑ i ∈ Aᶜ, v i) = b * qb := by
    dsimp [qb]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hu := unit_cube_mul_conj_square (hv i)
    rw [hBcube i hi] at hu
    exact hu.symm
  have hq : qa + qb = 0 := by
    calc
      qa + qb = ∑ i, (conj (v i)) ^ 2 :=
        Finset.sum_add_sum_compl A (fun i => (conj (v i)) ^ 2)
      _ = conj (∑ i, v i ^ 2) := by simp
      _ = 0 := by rw [h2, map_zero]
  have hp : a * qa + b * qb = 0 := by
    rw [← hqa, ← hqb, Finset.sum_add_sum_compl, h1]
  have hprod : (a - b) * qa = 0 := by linear_combination hp - b * hq
  have hqa0 : qa = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hab)
  have hqb0 : qb = 0 := by linear_combination hq - hqa0
  have hsumA : (∑ i ∈ A, v i) = 0 := by rw [hqa, hqa0, mul_zero]
  have hsumB : (∑ i ∈ Aᶜ, v i) = 0 := by rw [hqb, hqb0, mul_zero]
  have hia0 : v ia ≠ 0 := by
    intro h
    have hunit := hv ia
    simp [h] at hunit
  have hib0 : v ib ≠ 0 := by
    intro h
    have hunit := hv ib
    simp [h] at hunit
  have ha : a ≠ 0 := hia ▸ pow_ne_zero 3 hia0
  have hb : b ≠ 0 := hib ▸ pow_ne_zero 3 hib0
  have hneA : A.Nonempty := ⟨ia, by simp [A, cubeClass, hia]⟩
  have hneB : (Aᶜ).Nonempty := by
    refine ⟨ib, ?_⟩
    simp [A, cubeClass, hib, Ne.symm hab]
  have hcardA := same_cube_zero_sum_card_ge_three v A a ha hneA hAcube hsumA
  have hcardB := same_cube_zero_sum_card_ge_three v Aᶜ b hb hneB hBcube hsumB
  have hbound : A.card ≤ 6 := by simpa using Finset.card_le_univ A
  have hcompl : (Aᶜ).card = 6 - A.card := by simpa using Finset.card_compl A
  have heqA : A.card = 3 := by omega
  have heqB : (Aᶜ).card = 3 := by omega
  exact ⟨heqA, hB ▸ heqB, hsumA, hB ▸ hsumB⟩

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicPrelim
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Characteristic-polynomial reduction for the cubic classification in §3. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem characteristic_polynomial_expansion (v : (Fin 6) → ℂ) :
    (∏ i, (Polynomial.X - Polynomial.C (v i))) =
      ∑ j ∈ Finset.range 7,
        (-1 : Polynomial ℂ) ^ j *
          (Polynomial.C (elementarySum v j) * Polynomial.X ^ (6 - j)) := by
  have h := Multiset.prod_X_sub_X_eq_sum_esymm
    ((Finset.univ : Finset (Fin 6)).val.map v)
  simpa only [Multiset.map_map, Function.comp_def, Finset.prod_map_val,
    Finset.esymm_map_val, Multiset.card_map, Finset.card_val, Finset.card_univ,
    Fintype.card_fin, elementarySum] using h

/-- Unit entries with first and second power sums zero have a characteristic
polynomial depending only on `X³`, as used at the start of cubic classification. -/
theorem characteristic_polynomial_in_cubes (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) :
    (∏ i, (Polynomial.X - Polynomial.C (v i))) =
      Polynomial.X ^ 6 - Polynomial.C (elementarySum v 3) * Polynomial.X ^ 3 +
        Polynomial.C (∏ i, v i) := by
  obtain ⟨he1, he2⟩ := elementarySum_one_two_zero v h1 h2
  obtain ⟨he4, he5⟩ := elementarySum_four_five_zero v hv h1 h2
  rw [characteristic_polynomial_expansion]
  simp [Finset.sum_range_succ, elementarySum_zero, elementarySum_six,
    he1, he2, he4, he5]
  ring

theorem cubed_entry_quadratic (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) (i : (Fin 6)) :
    (v i ^ 3) ^ 2 - elementarySum v 3 * v i ^ 3 + (∏ j, v j) = 0 := by
  have h := congrArg (Polynomial.eval (v i))
    (characteristic_polynomial_in_cubes v hv h1 h2)
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_mul] at h
  have hz : (∏ j, (v i - v j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (v i))
  rw [hz] at h
  calc
    (v i ^ 3) ^ 2 - elementarySum v 3 * v i ^ 3 + (∏ j, v j) =
        v i ^ 6 - elementarySum v 3 * v i ^ 3 + (∏ j, v j) := by ring
    _ = 0 := h.symm

theorem quadratic_two_values {a b c s p : ℂ}
    (ha : a ^ 2 - s * a + p = 0) (hb : b ^ 2 - s * b + p = 0)
    (hc : c ^ 2 - s * c + p = 0) (hab : a ≠ b) : c = a ∨ c = b := by
  have hprod : (a - b) * (a + b - s) = 0 := by linear_combination ha - hb
  have hsum : a + b - s = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hab)
  have hs : s = a + b := by linear_combination -hsum
  have hp : p = a * b := by rw [hs] at ha; linear_combination ha
  rw [hs, hp] at hc
  have hfactor : (c - a) * (c - b) = 0 := by linear_combination hc
  simpa only [sub_eq_zero] using (mul_eq_zero.mp hfactor)

/-- This gives the first, algebraic part of the two-triples conclusion.
The multiplicity statement is a separate obligation. -/
theorem cube_values_at_most_two (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) :
    ∃ a b : ℂ, ∀ i, v i ^ 3 = a ∨ v i ^ 3 = b := by
  classical
  by_cases h : ∀ i, v i ^ 3 = v 0 ^ 3
  · exact ⟨v 0 ^ 3, v 0 ^ 3, fun i => Or.inl (h i)⟩
  · obtain ⟨j, hj⟩ := not_forall.mp h
    refine ⟨v 0 ^ 3, v j ^ 3, fun i => ?_⟩
    exact quadratic_two_values
      (cubed_entry_quadratic v hv h1 h2 0)
      (cubed_entry_quadratic v hv h1 h2 j)
      (cubed_entry_quadratic v hv h1 h2 i) (Ne.symm hj)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicSupportBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

theorem cubed_entries_twoValuePattern (v : Fin 6 → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) :
    TwoValuePattern (fun i => v i ^ 3) := by
  classical
  have ht := cube_values_at_most_two v hv h1 h2
  refine ⟨ht, ?_⟩
  intro a ha hb
  obtain ⟨ia, hia⟩ := ha
  obtain ⟨ib, hib⟩ := hb
  change v ia ^ 3 = a at hia
  change v ib ^ 3 ≠ a at hib
  have hne : v ia ^ 3 ≠ v ib ^ 3 := by rw [hia]; exact Ne.symm hib
  have hvalues : ∀ i, v i ^ 3 = a ∨ v i ^ 3 = v ib ^ 3 := by
    simpa [hia] using value_pair_exhausts (fun i => v i ^ 3) ht ia ib hne
  have hc := two_cube_classes_card_three v hv h1 h2 a (v ib ^ 3)
    (Ne.symm hib) hvalues ia ib hia rfl
  exact hc.1

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicHadamard
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem hadamard_row_ratio_moments {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2)) (r s : Coord) (hrs : r ≠ s) :
    (∀ j, Complex.normSq (H r j / H s j) = 1) ∧
      (∑ j, H r j / H s j) = 0 ∧ (∑ j, (H r j / H s j) ^ 2) = 0 := by
  refine ⟨fun j => ?_, ?_, ?_⟩
  · simp [hH.1]
  · simp_rw [div_eq_mul_inv, unit_inv_eq_conj (hH.1 s _)]
    simpa [hrs] using hH.row_orthogonal r s
  · have he (j : Coord) : (H r j / H s j) ^ 2 =
        H r j ^ 2 * conj (H s j ^ 2) := by
      rw [div_pow, div_eq_mul_inv, unit_inv_eq_conj (hH2.1 s j)]
    simp_rw [he]
    simpa [hrs] using hH2.row_orthogonal r s

theorem cubed_row_ratio_pattern {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2)) (r s : Coord) (hrs : r ≠ s) :
    TwoValuePattern (fun j => H r j ^ 3 / H s j ^ 3) := by
  obtain ⟨hu, h1, h2⟩ := hadamard_row_ratio_moments hH hH2 r s hrs
  simpa only [div_pow] using cubed_entries_twoValuePattern
    (fun j => H r j / H s j) hu h1 h2

theorem twoValuePattern_constant (a : ℂ) : TwoValuePattern (fun _ : Coord => a) := by
  refine ⟨⟨a, a, fun _ => Or.inl rfl⟩, ?_⟩
  intro b ⟨i, hi⟩ ⟨j, hj⟩
  exact False.elim (hj hi)

theorem cubed_row_pattern {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2)) (h0 : ∀ j, H 0 j = 1)
    (r : Coord) : TwoValuePattern (fun j => H r j ^ 3) := by
  by_cases hr : r = 0
  · subst r
    simpa only [h0, one_pow] using twoValuePattern_constant 1
  · simpa only [h0, one_pow, div_one] using cubed_row_ratio_pattern hH hH2 r 0 hr

/-- Before excluding it with the three-by-three block obstruction, the only
possible failure of cube roots after dephasing has one constant block. -/
theorem dephased_hadamard_cubes_block {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2))
    (h0row : ∀ j, H 0 j = 1) (h0col : ∀ i, H i 0 = 1)
    (i j : Coord) (hij : H i j ^ 3 ≠ 1) :
    ∃ (R S : Finset Coord) (x : ℂ),
      R.card = 3 ∧ S.card = 3 ∧ (0 : Coord) ∉ R ∧ (0 : Coord) ∉ S ∧
      x ≠ 0 ∧ x ≠ 1 ∧
      ∀ r c, H r c ^ 3 = if r ∈ R ∧ c ∈ S then x else 1 := by
  apply dephased_pattern_single_block (fun r c => H r c ^ 3)
    (fun j => by rw [h0row, one_pow]) (fun i => by rw [h0col, one_pow])
    (fun r c => pow_ne_zero _ (unit_ne_zero (hH.1 r c)))
    (cubed_row_pattern hH hH2 h0row) ?_
    (cubed_row_ratio_pattern hH hH2) i j hij
  intro c
  exact cubed_row_pattern hH.transpose hH2.transpose h0col c

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicExclusion
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem sum_enumerateThree (S : Finset Coord) (hS : S.card = 3) (f : Coord → ℂ) :
    (∑ i, f (enumerateThree S hS i)) = ∑ i ∈ S, f i := by
  rw [← Finset.sum_coe_sort S f]
  exact Equiv.sum_comp (enumerateThree S hS) (fun i : S => f i)

theorem no_hadamard_orthogonal_restrictions {H : CMatrix} (hH : IsHadamard H)
    (R S : Finset Coord) (hR : R.card = 3) (hS : S.card = 3)
    (hcross : ∀ r ∈ R, ∀ s ∈ Rᶜ, ∑ c ∈ S, H r c * conj (H s c) = 0) : False := by
  have hRc : Rᶜ.card = 3 := by simp [Finset.card_compl, hR]
  let r := enumerateThree R hR
  let s := enumerateThree Rᶜ hRc
  let c := enumerateThree S hS
  let A : Matrix (Fin 3) (Fin 3) ℂ := fun i j => H (r i) (c j)
  let B : Matrix (Fin 3) (Fin 3) ℂ := fun i j => H (s i) (c j)
  apply no_cubic_three_by_three_block A B (fun i j => hH.1 _ _) ?_ ?_
  · ext i j
    change (∑ k, H (r i) (c k) * conj (H (s j) (c k))) = 0
    rw [sum_enumerateThree S hS (fun k => H (r i) k * conj (H (s j) k))]
    exact hcross (r i) (r i).property (s j) (s j).property
  · ext i j
    change (∑ k, conj (H (r k) (c i)) * H (r k) (c j)) +
        (∑ k, conj (H (s k) (c i)) * H (s k) (c j)) =
      (6 : ℂ) * (if i = j then 1 else 0)
    rw [sum_enumerateThree R hR (fun k => conj (H k (c i)) * H k (c j)),
      sum_enumerateThree Rᶜ hRc (fun k => conj (H k (c i)) * H k (c j)),
      Finset.sum_add_sum_compl, hH.column_orthogonal]
    by_cases hij : i = j
    · simp [hij]
    · have hc : (c i : Coord) ≠ c j := by
        intro h
        exact hij (c.injective (Subtype.ext h))
      simp [hij, hc]

theorem cubic_block_cross_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2))
    (R S : Finset Coord) (hS : S.card = 3) (x : ℂ) (hx : x ≠ 1)
    (hblock : ∀ r c, H r c ^ 3 = if r ∈ R ∧ c ∈ S then x else 1)
    (r : Coord) (hr : r ∈ R) (s : Coord) (hs : s ∈ Rᶜ) :
    ∑ c ∈ S, H r c * conj (H s c) = 0 := by
  classical
  have hsR : s ∉ R := Finset.mem_compl.mp hs
  have hrs : r ≠ s := by intro h; exact hsR (h ▸ hr)
  let v : Coord → ℂ := fun c => H r c / H s c
  obtain ⟨hu, h1, h2⟩ := hadamard_row_ratio_moments hH hH2 r s hrs
  have hv (c : Coord) : v c ^ 3 = if c ∈ S then x else 1 := by
    by_cases hc : c ∈ S <;> simp [v, div_pow, hblock, hr, hsR, hc]
  have hvalues : ∀ c, v c ^ 3 = x ∨ v c ^ 3 = 1 := by
    intro c
    by_cases hc : c ∈ S <;> simp [hv, hc]
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have hSc : Sᶜ.card = 3 := by simp [Finset.card_compl, hS]
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < Sᶜ.card by omega)
  have hav : v a ^ 3 = x := by simp [hv, ha]
  have hbv : v b ^ 3 = 1 := by simp [hv, Finset.mem_compl.mp hb]
  have hm := two_cube_classes_card_three v hu h1 h2 x 1 hx hvalues a b hav hbv
  have hset : cubeClass v x = S := by
    ext c
    by_cases hc : c ∈ S <;> simp [cubeClass, hv, hc, Ne.symm hx]
  have hz : (∑ c ∈ S, v c) = 0 := by simpa only [hset] using hm.2.2.1
  simpa only [v, div_eq_mul_inv, unit_inv_eq_conj (hH.1 s _)] using hz

/-- An arbitrary dephased complex Hadamard matrix whose entrywise square is
Hadamard has only cube roots of unity as entries. -/
theorem dephased_hadamard_cubes_one {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2))
    (h0row : ∀ j, H 0 j = 1) (h0col : ∀ i, H i 0 = 1) :
    ∀ i j, H i j ^ 3 = 1 := by
  intro i j
  by_contra hij
  obtain ⟨R, S, x, hR, hS, _, _, _, hx, hblock⟩ :=
    dephased_hadamard_cubes_block hH hH2 h0row h0col i j hij
  exact no_hadamard_orthogonal_restrictions hH R S hR hS
    (cubic_block_cross_orthogonal hH hH2 R S hS x hx hblock)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Tao_Tao
attribute [-simp] _root_.OAI.MUB6.character_zero _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.g_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit five-cycle representative of Tao's cubic matrix. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem omega_isPrimitiveRoot : IsPrimitiveRoot omega 3 := by
  simpa [omega] using Complex.isPrimitiveRoot_exp 3 (by decide)

theorem omega_cube : omega ^ 3 = 1 := omega_isPrimitiveRoot.pow_eq_one

theorem omega_norm : ‖omega‖ = 1 :=
  omega_isPrimitiveRoot.norm'_eq_one (by decide)

theorem omega_normSq : Complex.normSq omega = 1 := by
  rw [Complex.normSq_eq_norm_sq, omega_norm]
  norm_num

theorem omega_sum : 1 + omega + omega ^ 2 = 0 := by
  simpa [Finset.sum_range_succ] using
    omega_isPrimitiveRoot.geom_sum_eq_zero (by decide : 1 < 3)

theorem omega_conj : conj omega = omega ^ 2 := by
  have homega : omega ≠ 0 := by
    intro hzero
    simpa [hzero] using omega_normSq
  apply mul_left_cancel₀ homega
  calc
    omega * conj omega = 1 := by simp [Complex.mul_conj, omega_normSq]
    _ = omega * omega ^ 2 := by rw [← pow_succ', omega_cube]

theorem omega_four : omega ^ 4 = omega := by
  calc
    omega ^ 4 = omega ^ 3 * omega := by ring
    _ = omega := by rw [omega_cube]; simp

theorem omega_five : omega ^ 5 = omega ^ 2 := by
  calc
    omega ^ 5 = omega ^ 3 * omega ^ 2 := by ring
    _ = omega ^ 2 := by rw [omega_cube]; simp

theorem omega_six : omega ^ 6 = 1 := by
  calc
    omega ^ 6 = (omega ^ 3) ^ 2 := by ring
    _ = 1 := by rw [omega_cube]; norm_num

theorem tao_entries_unit (i j : Coord) : Complex.normSq (tao i j) = 1 := by
  simp [tao, map_pow, omega_normSq]

theorem tao_gram : tao.conjTranspose * tao = (6 : ℂ) • (1 : CMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tao, taoExponent, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ, omega_conj] <;>
    ring_nf <;>
    norm_num [omega_cube, omega_four, omega_five, omega_six] <;>
    linear_combination 2 * omega_sum

theorem tao_isHadamard : IsHadamard tao := ⟨tao_entries_unit, tao_gram⟩

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicRoots
attribute [-simp] _root_.OAI.MUB6.character_zero _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.g_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem omega_ne_one : omega ≠ 1 := omega_isPrimitiveRoot.ne_one (by decide)

theorem omega_sq_ne_one : omega ^ 2 ≠ 1 := by
  intro h
  have he : omega ^ 3 = omega := by rw [pow_succ, h, one_mul]
  exact omega_ne_one (he.symm.trans omega_cube)

theorem omega_sq_ne_omega : omega ^ 2 ≠ omega := by
  intro h
  have he : omega * omega = omega * 1 := by simpa [pow_two] using h
  exact omega_ne_one (mul_left_cancel₀ (omega_isPrimitiveRoot.ne_zero (by decide)) he)

theorem omega_re : omega.re = (-1 / 2 : ℝ) := by
  have h := congrArg Complex.re omega_sum
  rw [← omega_conj] at h
  simp only [Complex.add_re, Complex.one_re, Complex.conj_re, Complex.zero_re] at h
  linarith

theorem omega_sq_re : (omega ^ 2).re = (-1 / 2 : ℝ) := by
  rw [← omega_conj, Complex.conj_re, omega_re]

theorem cube_roots_three (z : ℂ) (hz : z ^ 3 = 1) :
    z = 1 ∨ z = omega ∨ z = omega ^ 2 := by
  have hf : (z - 1) * (z - omega) * (z - omega ^ 2) = 0 := by
    calc
      (z - 1) * (z - omega) * (z - omega ^ 2) = z ^ 3 - 1 := by
        linear_combination (-z ^ 2 + z) * omega_sum + (z - 1) * omega_cube
      _ = 0 := by rw [hz, sub_self]
  rcases mul_eq_zero.mp hf with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

theorem cube_root_real_indicator (z : ℂ) (hz : z ^ 3 = 1) :
    z.re = (3 / 2 : ℝ) * (if z = 1 then 1 else 0) - 1 / 2 := by
  rcases cube_roots_three z hz with rfl | rfl | rfl
  · norm_num
  · rw [ite_eq_right omega_ne_one, omega_re]
    norm_num
  · rw [ite_eq_right omega_sq_ne_one, omega_sq_re]
    norm_num

/-- Six cube roots summing to zero contain the root one exactly twice. -/
theorem cube_roots_one_count (v : Coord → ℂ) (hv : ∀ i, v i ^ 3 = 1)
    (hs : ∑ i, v i = 0) : (Finset.univ.filter (fun i => v i = 1)).card = 2 := by
  classical
  have hre : (∑ i, (v i).re) = 0 := by
    simpa only [Complex.re_sum, Complex.zero_re] using congrArg Complex.re hs
  simp_rw [cube_root_real_indicator _ (hv _)] at hre
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hre
  have hc : (∑ i, if v i = 1 then (1 : ℝ) else 0) =
      ((Finset.univ.filter (fun i => v i = 1)).card : ℝ) := by simp
  rw [hc] at hre
  norm_num at hre
  have hn : ((Finset.univ.filter (fun i => v i = 1)).card : ℝ) = 2 := by
    linarith
  exact_mod_cast hn

/-- Every cube root occurs twice among six cube roots whose sum vanishes. -/
theorem cube_roots_each_count (v : Coord → ℂ) (hv : ∀ i, v i ^ 3 = 1)
    (hs : ∑ i, v i = 0) (a : ℂ) (ha : a ^ 3 = 1) :
    (Finset.univ.filter (fun i => v i = a)).card = 2 := by
  classical
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hv' : ∀ i, (v i / a) ^ 3 = 1 := by intro i; rw [div_pow, hv, ha, div_self one_ne_zero]
  have hs' : (∑ i, v i / a) = 0 := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, hs, zero_mul]
  have hc := cube_roots_one_count (fun i => v i / a) hv' hs'
  simpa only [div_eq_one_iff_eq ha0] using hc

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicMatching
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem cubic_hadamard_row_sum {H : CMatrix} (hH : IsHadamard H)
    (h0row : ∀ j, H 0 j = 1) (r : Coord) (hr : r ≠ 0) : ∑ j, H r j = 0 := by
  simpa [h0row, hr] using hH.row_orthogonal r 0

theorem cubic_hadamard_row_one_count {H : CMatrix} (hH : IsHadamard H)
    (hcube : ∀ i j, H i j ^ 3 = 1)
    (h0row : ∀ j, H 0 j = 1) (h0col : ∀ i, H i 0 = 1) (r : Fin 5) :
    (Finset.univ.filter (fun j : Fin 5 => H r.succ j.succ = 1)).card = 1 := by
  classical
  have hc := cube_roots_one_count (fun j => H r.succ j) (hcube r.succ)
    (cubic_hadamard_row_sum hH h0row r.succ (Fin.succ_ne_zero _))
  rw [Fin.card_filter_univ_succ] at hc
  simp only [h0col, ite_true, if_true] at hc
  omega

theorem existsUnique_of_filter_card_one (p : Fin 5 → Prop) [DecidablePred p]
    (hc : (Finset.univ.filter p).card = 1) : ∃! i, p i := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
  have hmem : ∀ j, p j ↔ j = i := by
    intro j
    have hh := congrArg (fun S : Finset (Fin 5) => j ∈ S) hi
    simpa using hh
  exact ⟨i, (hmem i).mpr rfl, fun j hj => (hmem j).mp hj⟩

/-- The noninitial entries equal to one form a perfect matching. -/
theorem cubic_hadamard_one_matching {H : CMatrix} (hH : IsHadamard H)
    (hcube : ∀ i j, H i j ^ 3 = 1)
    (h0row : ∀ j, H 0 j = 1) (h0col : ∀ i, H i 0 = 1) :
    ∃ p : Equiv.Perm (Fin 5), ∀ i j, H i.succ (p j).succ = 1 ↔ i = j := by
  classical
  have hrow : ∀ i : Fin 5, ∃! j : Fin 5, H i.succ j.succ = 1 := fun i =>
    existsUnique_of_filter_card_one _ (cubic_hadamard_row_one_count hH hcube h0row h0col i)
  have hcol : ∀ j : Fin 5, ∃! i : Fin 5, H i.succ j.succ = 1 := fun j =>
    existsUnique_of_filter_card_one _
      (cubic_hadamard_row_one_count hH.transpose (fun i j => hcube j i) h0col h0row j)
  choose f hf huniq using hrow
  have hinj : Function.Injective f := by
    intro i j hij
    exact (hcol (f i)).unique (hf i) (by rw [hij]; exact hf j)
  let p : Equiv.Perm (Fin 5) :=
    Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨p, fun i j => ?_⟩
  constructor
  · intro hij
    have h : f j = f i := huniq i (f j) hij
    exact (hinj h).symm
  · rintro rfl
    exact hf i

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicGraph
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem cubic_graph_entry {H : CMatrix} (hcube : ∀ i j, H i j ^ 3 = 1)
    (hdiag : ∀ i j : Fin 5, H i.succ j.succ = 1 ↔ i = j) (i j : Fin 5) :
    H i.succ j.succ = if i = j then 1 else
      if cubicGraph H i j then omega else omega ^ 2 := by
  classical
  by_cases hij : i = j
  · simp [hij, (hdiag j j).mpr rfl]
  · have hne : H i.succ j.succ ≠ 1 := fun h => hij ((hdiag i j).mp h)
    rcases cube_roots_three _ (hcube i.succ j.succ) with h | h | h
    · exact False.elim (hne h)
    · simp [hij, cubicGraph, h]
    · simp [hij, cubicGraph, h, omega_sq_ne_omega]

theorem cubic_graph_degree {H : CMatrix} (hH : IsHadamard H)
    (hcube : ∀ i j, H i j ^ 3 = 1)
    (h0row : ∀ j, H 0 j = 1) (h0col : ∀ i, H i 0 = 1) (i : Fin 5) :
    (Finset.univ.filter (fun j => cubicGraph H i j = true)).card = 2 := by
  classical
  have hc := cube_roots_each_count (fun j => H i.succ j) (hcube i.succ)
    (cubic_hadamard_row_sum hH h0row i.succ (Fin.succ_ne_zero _)) omega omega_cube
  rw [Fin.card_filter_univ_succ] at hc
  simpa [h0col, Ne.symm omega_ne_one, cubicGraph] using hc

theorem cubic_rows_agree_two {H : CMatrix} (hH : IsHadamard H)
    (hcube : ∀ i j, H i j ^ 3 = 1) (r s : Coord) (hrs : r ≠ s) :
    (Finset.univ.filter (fun j => H r j = H s j)).card = 2 := by
  classical
  have hv : ∀ j, (H r j / H s j) ^ 3 = 1 := by intro j; simp [div_pow, hcube]
  have hs : (∑ j, H r j / H s j) = 0 := by
    simp_rw [div_eq_mul_inv, unit_inv_eq_conj (hH.1 s _)]
    simpa [hrs] using hH.row_orthogonal r s
  have hc := cube_roots_one_count (fun j => H r j / H s j) hv hs
  simpa only [div_eq_one_iff_eq (unit_ne_zero (hH.1 s _))] using hc

theorem cubic_graph_agreement {H : CMatrix} (hcube : ∀ i j, H i j ^ 3 = 1)
    (hdiag : ∀ i j : Fin 5, H i.succ j.succ = 1 ↔ i = j)
    (i j : Fin 5) (hij : i ≠ j) (k : Fin 5) :
    H i.succ k.succ = H j.succ k.succ ↔
      k ≠ i ∧ k ≠ j ∧ cubicGraph H i k = cubicGraph H j k := by
  by_cases hki : k = i
  · subst k
    have hji : H j.succ i.succ ≠ 1 := fun h => hij ((hdiag j i).mp h).symm
    simp [(hdiag i i).mpr rfl, Ne.symm hji]
  by_cases hkj : k = j
  · subst k
    simp [(hdiag j j).mpr rfl, (hdiag i j), hij]
  rw [cubic_graph_entry hcube hdiag i k, cubic_graph_entry hcube hdiag j k]
  cases hi : cubicGraph H i k <;> cases hj : cubicGraph H j k <;>
    simp [hki, hkj, Ne.symm hki, Ne.symm hkj,
      omega_sq_ne_omega, Ne.symm omega_sq_ne_omega]

theorem cubic_graph_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (hcube : ∀ i j, H i j ^ 3 = 1) (h0col : ∀ i, H i 0 = 1)
    (hdiag : ∀ i j : Fin 5, H i.succ j.succ = 1 ↔ i = j)
    (i j : Fin 5) (hij : i ≠ j) :
    (Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j ∧
      cubicGraph H i k = cubicGraph H j k)).card = 1 := by
  classical
  have hc := cubic_rows_agree_two hH hcube i.succ j.succ
    (fun h => hij (Fin.succ_injective _ h))
  rw [Fin.card_filter_univ_succ] at hc
  simp only [h0col, ite_true, if_true] at hc
  simp_rw [cubic_graph_agreement hcube hdiag i j hij] at hc
  omega

theorem tao_noninitial (i j : Fin 5) :
    tao i.succ j.succ = if i = j then 1 else
      if canonicalFiveCycle i j then omega else omega ^ 2 := by
  fin_cases i <;> fin_cases j <;>
    simp [tao, taoExponent, canonicalFiveCycle, fiveGraph]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_NormalizedCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A second finite presentation of the five-cycle classification.  A row has
two positive signs among four off-diagonal positions, hence six choices. -/

namespace MUB6

theorem rowChoice_complete : ∀ (i : Fin 5) (f : Fin 5 → Bool),
    f i = false → (Finset.univ.filter (fun j => f j = true)).card = 2 →
      ∃ a, ∀ j, fiveRowChoice i a j = f j := by
  decide +kernel

private theorem normalizedCodes_00 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![0, 0, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_01 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![0, 1, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_02 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![0, 2, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_03 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![0, 3, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_04 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![0, 4, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_05 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![0, 5, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_10 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![1, 0, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_11 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![1, 1, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_12 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![1, 2, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_13 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![1, 3, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_14 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![1, 4, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_15 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![1, 5, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_20 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![2, 0, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_21 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![2, 1, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_22 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![2, 2, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_23 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![2, 3, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_24 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![2, 4, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_25 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![2, 5, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_30 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![3, 0, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_31 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![3, 1, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_32 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![3, 2, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_33 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![3, 3, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_34 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![3, 4, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_35 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![3, 5, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_40 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![4, 0, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_41 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![4, 1, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_42 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![4, 2, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_43 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![4, 3, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_44 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![4, 4, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_45 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![4, 5, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_50 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![5, 0, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_51 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![5, 1, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_52 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![5, 2, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_53 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![5, 3, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_54 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![5, 4, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_55 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![5, 5, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

theorem normalizedCodes_classified (a : Fin 5 → Fin 6) : normalizedCodeClassified a := by
  have h (a0 a1 a2 a3 a4 : Fin 6) : normalizedCodeClassified ![a0, a1, a2, a3, a4] := by
    fin_cases a0 <;> fin_cases a1
    · exact normalizedCodes_00 a2 a3 a4
    · exact normalizedCodes_01 a2 a3 a4
    · exact normalizedCodes_02 a2 a3 a4
    · exact normalizedCodes_03 a2 a3 a4
    · exact normalizedCodes_04 a2 a3 a4
    · exact normalizedCodes_05 a2 a3 a4
    · exact normalizedCodes_10 a2 a3 a4
    · exact normalizedCodes_11 a2 a3 a4
    · exact normalizedCodes_12 a2 a3 a4
    · exact normalizedCodes_13 a2 a3 a4
    · exact normalizedCodes_14 a2 a3 a4
    · exact normalizedCodes_15 a2 a3 a4
    · exact normalizedCodes_20 a2 a3 a4
    · exact normalizedCodes_21 a2 a3 a4
    · exact normalizedCodes_22 a2 a3 a4
    · exact normalizedCodes_23 a2 a3 a4
    · exact normalizedCodes_24 a2 a3 a4
    · exact normalizedCodes_25 a2 a3 a4
    · exact normalizedCodes_30 a2 a3 a4
    · exact normalizedCodes_31 a2 a3 a4
    · exact normalizedCodes_32 a2 a3 a4
    · exact normalizedCodes_33 a2 a3 a4
    · exact normalizedCodes_34 a2 a3 a4
    · exact normalizedCodes_35 a2 a3 a4
    · exact normalizedCodes_40 a2 a3 a4
    · exact normalizedCodes_41 a2 a3 a4
    · exact normalizedCodes_42 a2 a3 a4
    · exact normalizedCodes_43 a2 a3 a4
    · exact normalizedCodes_44 a2 a3 a4
    · exact normalizedCodes_45 a2 a3 a4
    · exact normalizedCodes_50 a2 a3 a4
    · exact normalizedCodes_51 a2 a3 a4
    · exact normalizedCodes_52 a2 a3 a4
    · exact normalizedCodes_53 a2 a3 a4
    · exact normalizedCodes_54 a2 a3 a4
    · exact normalizedCodes_55 a2 a3 a4
  have he : a = ![a 0, a 1, a 2, a 3, a 4] := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact h _ _ _ _ _

end MUB6

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_NormalizedCubic
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6

theorem normalized_cubic_equivalent_tao {H : CMatrix} (hH : IsHadamard H)
    (hcube : ∀ i j, H i j ^ 3 = 1)
    (h0row : ∀ j, H 0 j = 1) (h0col : ∀ i, H i 0 = 1)
    (hdiag : ∀ i j : Fin 5, H i.succ j.succ = 1 ↔ i = j) : Equivalent H tao := by
  classical
  have hchoice (i : Fin 5) : ∃ a, ∀ j, fiveRowChoice i a j = cubicGraph H i j := by
    apply rowChoice_complete i (cubicGraph H i) ?_ (cubic_graph_degree hH hcube h0row h0col i)
    simp [cubicGraph, (hdiag i i).mpr rfl, Ne.symm omega_ne_one]
  choose a ha using hchoice
  have hagree : ∀ i j, normalizedCodeGraph a i j = cubicGraph H i j := ha
  have horth : normalizedCodeOrthogonal a := by
    intro i j hij
    simpa only [hagree] using cubic_graph_orthogonal hH hcube h0col hdiag i j hij
  obtain ⟨c, hc⟩ := normalizedCodes_classified a horth
  let q := fiveCyclePermutation c
  have hq (i j : Fin 5) : cubicGraph H (q i) (q j) = canonicalFiveCycle i j := by
    simpa only [q, fiveCyclePermutation, Equiv.ofBijective_apply, hagree] using hc i j
  have heq (i j : Coord) : H (fixZeroPermutation q i) (fixZeroPermutation q j) = tao i j := by
    cases i using Fin.cases with
    | zero => fin_cases j <;> simp [h0row, tao, taoExponent]
    | succ i =>
      cases j using Fin.cases with
      | zero => fin_cases i <;> simp [h0col, tao, taoExponent]
      | succ j =>
        simp only [fixZeroPermutation_succ, cubic_graph_entry hcube hdiag, hq,
          Equiv.apply_eq_iff_eq, tao_noninitial]
  refine ⟨fixZeroPermutation q, fixZeroPermutation q, fun _ => 1, fun _ => 1,
    by simp, by simp, ?_⟩
  intro i j
  simpa using (heq i j).symm

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

theorem IsHadamard.phaseTransform {H : CMatrix} (hH : IsHadamard H)
    (u v : Coord → ℂ) (hu : ∀ i, Complex.normSq (u i) = 1)
    (hv : ∀ j, Complex.normSq (v j) = 1) : IsHadamard (phaseTransform H u v) := by
  refine ⟨?_, ?_⟩
  · intro i j
    change Complex.normSq (u i * H i j * v j) = 1
    simp [map_mul, hu, hv, hH.1]
  · ext i j
    have hsum : (∑ k, conj (MUB6.phaseTransform H u v k i) * MUB6.phaseTransform H u v k j) =
        conj (v i) * v j * ∑ k, conj (H k i) * H k j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have huk : conj (u k) * u k = 1 := by
        rw [mul_comm, Complex.mul_conj, hu]
        rfl
      simp only [MUB6.phaseTransform, map_mul]
      calc
        _ = (conj (u k) * u k) *
          (conj (v i) * v j * (conj (H k i) * H k j)) := by ring
        _ = _ := by rw [huk, one_mul]
    change (∑ k, conj (MUB6.phaseTransform H u v k i) * MUB6.phaseTransform H u v k j) =
      (6 : ℂ) * (if i = j then 1 else 0)
    rw [hsum, hH.column_orthogonal]
    by_cases hij : i = j
    · subst j
      rw [mul_comm (conj (v i)) (v i), Complex.mul_conj, hv]
      simp
    · simp [hij]

theorem IsHadamard.permutations {H : CMatrix} (hH : IsHadamard H)
    (r c : Equiv.Perm Coord) : IsHadamard (fun i j => H (r i) (c j)) := by
  refine ⟨fun i j => hH.1 _ _, ?_⟩
  ext i j
  change (∑ k, conj (H (r k) (c i)) * H (r k) (c j)) =
    (6 : ℂ) * (if i = j then 1 else 0)
  rw [Equiv.sum_comp r (fun k => conj (H k (c i)) * H k (c j)), hH.column_orthogonal]
  simp only [Equiv.apply_eq_iff_eq]
  split_ifs <;> norm_num

theorem Equivalent.isHadamard {H K : CMatrix} (h : Equivalent H K)
    (hH : IsHadamard H) : IsHadamard K := by
  rcases h with ⟨r, c, u, v, hu, hv, he⟩
  have hK : K = phaseTransform (fun i j => H (r i) (c j)) u v := by
    ext i j
    exact he i j
  rw [hK]
  exact (hH.permutations r c).phaseTransform u v hu hv

theorem dephase_equivalent {H : CMatrix} (hH : IsHadamard H) :
    Equivalent H (dephase H) := by
  refine ⟨Equiv.refl _, Equiv.refl _, (fun i => (H i 0)⁻¹),
    (fun j => H 0 0 * (H 0 j)⁻¹), ?_, ?_, ?_⟩
  · intro i
    simp [hH.1]
  · intro j
    simp [map_mul, hH.1]
  · intro i j
    rfl

theorem dephase_isHadamard {H : CMatrix} (hH : IsHadamard H) :
    IsHadamard (dephase H) := (dephase_equivalent hH).isHadamard hH

theorem dephase_row_zero {H : CMatrix} (hH : IsHadamard H) (j : Coord) :
    dephase H 0 j = 1 := by
  unfold dephase phaseTransform
  field_simp [unit_ne_zero (hH.1 0 0), unit_ne_zero (hH.1 0 j)]

theorem dephase_column_zero {H : CMatrix} (hH : IsHadamard H) (i : Coord) :
    dephase H i 0 = 1 := by
  unfold dephase phaseTransform
  field_simp [unit_ne_zero (hH.1 0 0), unit_ne_zero (hH.1 i 0)]

theorem equivalent_squares {H K : CMatrix} (h : Equivalent H K) :
    Equivalent (fun i j => H i j ^ 2) (fun i j => K i j ^ 2) := by
  rcases h with ⟨r, c, u, v, hu, hv, he⟩
  refine ⟨r, c, (fun i => u i ^ 2), (fun j => v j ^ 2), ?_, ?_, ?_⟩
  · intro i
    simp [map_pow, hu]
  · intro j
    simp [map_pow, hv]
  · intro i j
    change K i j ^ 2 = u i ^ 2 * H (r i) (c j) ^ 2 * v j ^ 2
    rw [he]
    ring

theorem dephase_square_isHadamard {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2)) :
    IsHadamard (fun i j => dephase H i j ^ 2) :=
  (equivalent_squares (dephase_equivalent hH)).isHadamard hH2

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicClassification
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6

/-- The cubic classification from the companion: no restriction is imposed
on the complex entries or on the unit phases in the equivalence relation. -/
theorem hadamard_square_equivalent_tao {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2)) : Equivalent H tao := by
  let D := dephase H
  have hD : IsHadamard D := dephase_isHadamard hH
  have hD2 : IsHadamard (fun i j => D i j ^ 2) := dephase_square_isHadamard hH hH2
  have hDr : ∀ j, D 0 j = 1 := dephase_row_zero hH
  have hDc : ∀ i, D i 0 = 1 := dephase_column_zero hH
  have hcube : ∀ i j, D i j ^ 3 = 1 := dephased_hadamard_cubes_one hD hD2 hDr hDc
  obtain ⟨p, hp⟩ := cubic_hadamard_one_matching hD hcube hDr hDc
  let K : CMatrix := fun i j => D i (fixZeroPermutation p j)
  have hK : IsHadamard K := by
    simpa only [Equiv.refl_apply] using hD.permutations (Equiv.refl _) (fixZeroPermutation p)
  have hKr : ∀ j, K 0 j = 1 := fun j => hDr _
  have hKc : ∀ i, K i 0 = 1 := fun i => hDc _
  have hKcube : ∀ i j, K i j ^ 3 = 1 := fun i j => hcube _ _
  have hdiag : ∀ i j : Fin 5, K i.succ j.succ = 1 ↔ i = j := hp
  have hDK : Equivalent D K := by
    refine ⟨Equiv.refl _, fixZeroPermutation p, fun _ => 1, fun _ => 1,
      by simp, by simp, ?_⟩
    intro i j
    simp [K]
  exact equivalent_trans (dephase_equivalent hH)
    (equivalent_trans hDK (normalized_cubic_equivalent_tao hK hKcube hKr hKc hdiag))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Cubic_CubicPositivity
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem triple_difference (i j : Coord) :
    (3 : ℤ) • difference i j = difference i j + difference i j + difference i j := by
  funext k
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem character_triple_difference (x : Coord → ℂ)
    (hx : ∀ i, Complex.normSq (x i) = 1) (i j : Coord) :
    character x ((3 : ℤ) • difference i j) = x i ^ 3 * conj (x j ^ 3) := by
  rw [triple_difference, character_add x (fun i => unit_ne_zero (hx i)),
    character_add x (fun i => unit_ne_zero (hx i)), character_difference x hx, map_pow]
  ring

theorem triple_difference_sum {H : CMatrix} (hH : IsHadamard H) :
    (∑ i, ∑ j, g H ((3 : ℤ) • difference i j)) =
      (6 : ℂ)⁻¹ * ∑ k, (Complex.normSq (∑ i, H i k ^ 3) : ℂ) := by
  simp only [g, character_triple_difference _ (fun i => hH.1 i _)]
  simp only [← Finset.mul_sum]
  congr 1
  calc
    _ = ∑ i, ∑ k, ∑ j, H i k ^ 3 * conj (H j k ^ 3) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, H i k ^ 3 * conj (H j k ^ 3) := Finset.sum_comm
    _ = _ := by simp_rw [sum_mul_conj]

/-- The cubic off-diagonal Fourier sum is bounded below by minus the dimension.
It is the average of squared absolute values of column power sums, minus six. -/
theorem cubic_fourier_nonnegative {H : CMatrix} (hH : IsHadamard H) :
    0 ≤ 6 + offDiagSum (fun i j => (g H ((3 : ℤ) • difference i j)).re) := by
  have h := congrArg Complex.re (offDiagSum_add_diag
    (fun i j => g H ((3 : ℤ) • difference i j)))
  rw [triple_difference_sum hH] at h
  have hd : (∑ i, g H ((3 : ℤ) • difference i i)) = (6 : ℂ) := by
    simp [difference]
  rw [hd] at h
  have hi : (6 : ℂ)⁻¹ = (((6 : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  rw [hi] at h
  simp only [Complex.add_re, offDiagSum, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.re_ofNat] at h
  have hn : 0 ≤ (6 : ℝ)⁻¹ * ∑ k, Complex.normSq (∑ i, H i k ^ 3) := by
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _)
  unfold offDiagSum
  linarith

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Tao_TaoArithmetic
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.character_zero _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.g_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact arithmetic in `ℤ[ω]`, interpreted in the same complex root as Tao's
matrix.  These definitions are for certificate checking, not assumptions. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6.TaoArithmetic

theorem value_mul (z w : Coeff) : value (mul z w) = value z * value w := by
  simp only [value, mul, Int.cast_add, Int.cast_sub, Int.cast_mul]
  linear_combination -(z.2 : ℂ) * (w.2 : ℂ) * omega_sum

theorem value_conjugate (z : Coeff) : value (conjugate z) = conj (value z) := by
  simp only [value, conjugate, Int.cast_sub, Int.cast_neg, map_add, map_mul,
    map_intCast, omega_conj]
  linear_combination -(z.2 : ℂ) * omega_sum

theorem value_sum {ι : Type*} (s : Finset ι) (f : ι → Coeff) :
    value (∑ i ∈ s, f i) = ∑ i ∈ s, value (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

theorem omega_zpow_mod (n : ℤ) : omega ^ n = omega ^ (n % 3) := by
  have hn : n = n % 3 + 3 * (n / 3) := (Int.emod_add_mul_ediv n 3).symm
  have h3 : omega ^ (3 : ℤ) = 1 := by simpa only [zpow_ofNat] using omega_cube
  calc
    omega ^ n = omega ^ (n % 3 + 3 * (n / 3)) := by rw [← hn]
    _ = omega ^ (n % 3) := by
      rw [zpow_add₀ (omega_isPrimitiveRoot.ne_zero (by decide)), zpow_mul, h3,
        one_zpow, mul_one]

theorem value_root (n : ℤ) : value (root n) = omega ^ n := by
  rw [omega_zpow_mod]
  have h0 := Int.emod_nonneg n (by decide : (3 : ℤ) ≠ 0)
  have h3 := Int.emod_lt_of_pos n (by decide : (0 : ℤ) < 3)
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hcases with h | h | h
  · simp [root, h, value]
  · simp [root, h, value]
  · simp only [root, h]
    norm_num [value]
    linear_combination -omega_sum

theorem omega_zpow_sum (a : Charge) : (∏ i, omega ^ a i) = omega ^ (∑ i, a i) := by
  have h (s : Finset Coord) : (∏ i ∈ s, omega ^ a i) = omega ^ (∑ i ∈ s, a i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih,
        zpow_add₀ (omega_isPrimitiveRoot.ne_zero (by decide))]
  exact h Finset.univ

theorem counts_interpretation (a : Charge) : value (counts a) = 6 * g tao a := by
  unfold counts
  rw [value_sum]
  have hc (k : Coord) : character (fun i => tao i k) a =
      omega ^ (∑ i, (taoExponent i k : ℤ) * a i) := by
    unfold character tao
    simp_rw [← zpow_natCast, ← zpow_mul]
    exact omega_zpow_sum _
  simp_rw [value_root]
  simp only [g, hc]
  ring

end MUB6.TaoArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Tao_TaoSparse
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6.TaoArithmetic

theorem eval_monomial (f : Charge → ℂ) (a : Charge) (z : Coeff) :
    Certificate.Integer.Sparse.eval (monomial a z) (momentValues f) =
      (value z * f a).re := by
  simp [Certificate.Integer.Sparse.eval, monomial, momentValues, value,
    add_mul, Complex.add_re, Complex.mul_re]
  ring

theorem offDiagonalPairs_sum (f : Coord → Coord → ℂ) :
    (offDiagonalPairs.map (fun p => f p.1 p.2)).sum = offDiagSum f := by
  simp [offDiagonalPairs, offDiagSum, Finset.sum_erase_eq_sub, Fin.sum_univ_succ]
  ring

theorem eval_flatMap {ι : Type*} (l : List ι) (r : ι → Sparse) (x : List ℤ → ℝ) :
    Certificate.Integer.Sparse.eval (l.flatMap r) x =
      (l.map (fun i => Certificate.Integer.Sparse.eval (r i) x)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [List.flatMap_cons, ih]

theorem re_list_sum (l : List ℂ) : l.sum.re = (l.map Complex.re).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Complex.add_re, ih]

theorem eval_row (f : Charge → ℂ) (a c : Charge) (w : Coeff) :
    Certificate.Integer.Sparse.eval (row a c w) (momentValues f) =
      6 * (value w * offDiagSum
        (fun i j => f (a + difference i j) * conj (g tao (c + difference i j)))).re := by
  rw [row, eval_flatMap]
  simp_rw [eval_monomial, value_mul, value_conjugate, counts_interpretation,
    map_mul, map_ofNat]
  have hs : (offDiagonalPairs.map (fun p =>
      ((value w * (6 * conj (g tao (c + difference p.1 p.2)))) *
        f (a + difference p.1 p.2)).re)).sum =
      (6 * value w * (offDiagonalPairs.map (fun p =>
        f (a + difference p.1 p.2) * conj (g tao (c + difference p.1 p.2)))).sum).re := by
    rw [← List.sum_map_mul_left, re_list_sum, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    congr 1
    ring
  rw [hs, offDiagonalPairs_sum (fun i j =>
    f (a + difference i j) * conj (g tao (c + difference i j)))]
  simp only [mul_assoc, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]

theorem eval_row_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        conj (g tao (c + difference i j))) = 0)
    (a c : Charge) (ha : Balanced a) (hc : Balanced c) (w : Coeff) :
    Certificate.Integer.Sparse.eval (row a c w) (momentValues f) = 0 := by
  rw [eval_row, hcross a c ha hc]
  simp

theorem eval_normalize (r : Sparse) (x : List ℤ → ℝ) :
    Certificate.Integer.Sparse.eval (normalize r) x =
      Certificate.Integer.Sparse.eval r x := by
  induction r with
  | nil => rfl
  | cons p ps ih =>
    simp only [normalize]
    split_ifs with h
    · simp [ih, h]
    · simp [ih]

end MUB6.TaoArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source83_checked : normalize (row ![0, 1, -1, 1, 0, -1] ![0, 1, -1, 1, 0, -1] (-12, 0)) = source83 := by
  decide +kernel

theorem source83_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source83 (momentValues f) = 0 := by
  rw [← source83_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source105_checked : normalize (row ![1, 0, -1, 0, 1, -1] ![1, 0, -1, 0, 1, -1] (-12, 0)) = source105 := by
  decide +kernel

theorem source105_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source105 (momentValues f) = 0 := by
  rw [← source105_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source107_checked : normalize (row ![1, 0, -1, 1, 0, -1] ![1, 0, -1, 1, 0, -1] (-12, 0)) = source107 := by
  decide +kernel

theorem source107_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source107 (momentValues f) = 0 := by
  rw [← source107_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source116_checked : normalize (row ![1, 1, -1, 0, 0, -1] ![1, 1, -1, 0, 0, -1] (-12, 0)) = source116 := by
  decide +kernel

theorem source116_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source116 (momentValues f) = 0 := by
  rw [← source116_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source124_checked : normalize (row ![1, 1, -1, 0, 0, -1] ![-1, 1, 0, 0, 0, 0] (0, -3)) = source124 := by
  decide +kernel

theorem source124_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source124 (momentValues f) = 0 := by
  rw [← source124_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source152_checked : normalize (row ![1, 0, -1, 1, 0, -1] ![-1, 0, 0, 1, 0, 0] (0, -3)) = source152 := by
  decide +kernel

theorem source152_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source152 (momentValues f) = 0 := by
  rw [← source152_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source164_checked : normalize (row ![1, 0, -1, 0, 1, -1] ![-1, 0, 0, 0, 1, 0] (0, -3)) = source164 := by
  decide +kernel

theorem source164_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source164 (momentValues f) = 0 := by
  rw [← source164_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source184_checked : normalize (row ![1, 1, -1, 0, 0, -1] ![1, -1, 0, 0, 0, 0] (0, -3)) = source184 := by
  decide +kernel

theorem source184_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source184 (momentValues f) = 0 := by
  rw [← source184_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source212_checked : normalize (row ![0, 1, -1, 1, 0, -1] ![0, -1, 0, 1, 0, 0] (0, -3)) = source212 := by
  decide +kernel

theorem source212_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source212 (momentValues f) = 0 := by
  rw [← source212_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source289_checked : normalize (row ![1, 1, -1, 0, 0, -1] ![0, 0, 1, 0, 0, -1] (0, -3)) = source289 := by
  decide +kernel

theorem source289_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source289 (momentValues f) = 0 := by
  rw [← source289_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source291_checked : normalize (row ![1, 0, -1, 1, 0, -1] ![0, 0, 1, 0, 0, -1] (0, -3)) = source291 := by
  decide +kernel

theorem source291_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source291 (momentValues f) = 0 := by
  rw [← source291_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source293_checked : normalize (row ![1, 0, -1, 0, 1, -1] ![0, 0, 1, 0, 0, -1] (3, 3)) = source293 := by
  decide +kernel

theorem source293_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source293 (momentValues f) = 0 := by
  rw [← source293_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source295_checked : normalize (row ![0, 1, -1, 1, 0, -1] ![0, 0, 1, 0, 0, -1] (3, 3)) = source295 := by
  decide +kernel

theorem source295_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source295 (momentValues f) = 0 := by
  rw [← source295_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source308_checked : normalize (row ![1, 0, -1, 1, 0, -1] ![1, 0, 0, -1, 0, 0] (3, 3)) = source308 := by
  decide +kernel

theorem source308_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source308 (momentValues f) = 0 := by
  rw [← source308_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source320_checked : normalize (row ![0, 1, -1, 1, 0, -1] ![0, 1, 0, -1, 0, 0] (3, 3)) = source320 := by
  decide +kernel

theorem source320_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source320 (momentValues f) = 0 := by
  rw [← source320_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source368_checked : normalize (row ![1, 0, -1, 0, 1, -1] ![1, 0, 0, 0, -1, 0] (3, 3)) = source368 := by
  decide +kernel

theorem source368_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source368 (momentValues f) = 0 := by
  rw [← source368_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source445_checked : normalize (row ![1, 1, -1, 0, 0, -1] ![0, 0, -1, 0, 0, 1] (0, -3)) = source445 := by
  decide +kernel

theorem source445_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source445 (momentValues f) = 0 := by
  rw [← source445_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source447_checked : normalize (row ![1, 0, -1, 1, 0, -1] ![0, 0, -1, 0, 0, 1] (3, 3)) = source447 := by
  decide +kernel

theorem source447_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source447 (momentValues f) = 0 := by
  rw [← source447_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source449_checked : normalize (row ![1, 0, -1, 0, 1, -1] ![0, 0, -1, 0, 0, 1] (0, -3)) = source449 := by
  decide +kernel

theorem source449_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source449 (momentValues f) = 0 := by
  rw [← source449_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source451_checked : normalize (row ![0, 1, -1, 1, 0, -1] ![0, 0, -1, 0, 0, 1] (0, -3)) = source451 := by
  decide +kernel

theorem source451_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source451 (momentValues f) = 0 := by
  rw [← source451_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined212_checked : Certificate.Integer.Sparse.merge source83 source212 = combined212 := by
  decide +kernel

theorem combined212_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined212 (momentValues f) = 0 := by
  rw [← combined212_checked, Certificate.Integer.Sparse.eval_merge,
    source83_zero f hcross, source212_zero f hcross, add_zero]

theorem combined213_checked : Certificate.Integer.Sparse.merge combined212 source295 = combined213 := by
  decide +kernel

theorem combined213_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined213 (momentValues f) = 0 := by
  rw [← combined213_checked, Certificate.Integer.Sparse.eval_merge,
    combined212_zero f hcross, source295_zero f hcross, add_zero]

theorem combined214_checked : Certificate.Integer.Sparse.merge combined213 source320 = combined214 := by
  decide +kernel

theorem combined214_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined214 (momentValues f) = 0 := by
  rw [← combined214_checked, Certificate.Integer.Sparse.eval_merge,
    combined213_zero f hcross, source320_zero f hcross, add_zero]

theorem combined215_checked : Certificate.Integer.Sparse.merge combined214 source451 = combined215 := by
  decide +kernel

theorem combined215_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined215 (momentValues f) = 0 := by
  rw [← combined215_checked, Certificate.Integer.Sparse.eval_merge,
    combined214_zero f hcross, source451_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined300_checked : Certificate.Integer.Sparse.merge source105 source164 = combined300 := by
  decide +kernel

theorem combined300_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined300 (momentValues f) = 0 := by
  rw [← combined300_checked, Certificate.Integer.Sparse.eval_merge,
    source105_zero f hcross, source164_zero f hcross, add_zero]

theorem combined301_checked : Certificate.Integer.Sparse.merge combined300 source293 = combined301 := by
  decide +kernel

theorem combined301_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined301 (momentValues f) = 0 := by
  rw [← combined301_checked, Certificate.Integer.Sparse.eval_merge,
    combined300_zero f hcross, source293_zero f hcross, add_zero]

theorem combined302_checked : Certificate.Integer.Sparse.merge combined301 source368 = combined302 := by
  decide +kernel

theorem combined302_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined302 (momentValues f) = 0 := by
  rw [← combined302_checked, Certificate.Integer.Sparse.eval_merge,
    combined301_zero f hcross, source368_zero f hcross, add_zero]

theorem combined303_checked : Certificate.Integer.Sparse.merge combined302 source449 = combined303 := by
  decide +kernel

theorem combined303_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined303 (momentValues f) = 0 := by
  rw [← combined303_checked, Certificate.Integer.Sparse.eval_merge,
    combined302_zero f hcross, source449_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined308_checked : Certificate.Integer.Sparse.merge source107 source152 = combined308 := by
  decide +kernel

theorem combined308_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined308 (momentValues f) = 0 := by
  rw [← combined308_checked, Certificate.Integer.Sparse.eval_merge,
    source107_zero f hcross, source152_zero f hcross, add_zero]

theorem combined309_checked : Certificate.Integer.Sparse.merge combined308 source291 = combined309 := by
  decide +kernel

theorem combined309_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined309 (momentValues f) = 0 := by
  rw [← combined309_checked, Certificate.Integer.Sparse.eval_merge,
    combined308_zero f hcross, source291_zero f hcross, add_zero]

theorem combined310_checked : Certificate.Integer.Sparse.merge combined309 source308 = combined310 := by
  decide +kernel

theorem combined310_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined310 (momentValues f) = 0 := by
  rw [← combined310_checked, Certificate.Integer.Sparse.eval_merge,
    combined309_zero f hcross, source308_zero f hcross, add_zero]

theorem combined311_checked : Certificate.Integer.Sparse.merge combined310 source447 = combined311 := by
  decide +kernel

theorem combined311_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined311 (momentValues f) = 0 := by
  rw [← combined311_checked, Certificate.Integer.Sparse.eval_merge,
    combined310_zero f hcross, source447_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined344_checked : Certificate.Integer.Sparse.merge source116 source124 = combined344 := by
  decide +kernel

theorem combined344_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined344 (momentValues f) = 0 := by
  rw [← combined344_checked, Certificate.Integer.Sparse.eval_merge,
    source116_zero f hcross, source124_zero f hcross, add_zero]

theorem combined345_checked : Certificate.Integer.Sparse.merge combined344 source184 = combined345 := by
  decide +kernel

theorem combined345_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined345 (momentValues f) = 0 := by
  rw [← combined345_checked, Certificate.Integer.Sparse.eval_merge,
    combined344_zero f hcross, source184_zero f hcross, add_zero]

theorem combined346_checked : Certificate.Integer.Sparse.merge combined345 source289 = combined346 := by
  decide +kernel

theorem combined346_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined346 (momentValues f) = 0 := by
  rw [← combined346_checked, Certificate.Integer.Sparse.eval_merge,
    combined345_zero f hcross, source289_zero f hcross, add_zero]

theorem combined347_checked : Certificate.Integer.Sparse.merge combined346 source445 = combined347 := by
  decide +kernel

theorem combined347_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined347 (momentValues f) = 0 := by
  rw [← combined347_checked, Certificate.Integer.Sparse.eval_merge,
    combined346_zero f hcross, source445_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined475_checked : Certificate.Integer.Sparse.merge combined474 combined215 = combined475 := by
  decide +kernel

theorem combined475_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined475 (momentValues f) = 0 := by
  rw [← combined475_checked, Certificate.Integer.Sparse.eval_merge,
    combined474_zero_e f hcross, combined215_zero f hcross, add_zero]

theorem combined476_checked : Certificate.Integer.Sparse.merge combined475 combined347 = combined476 := by
  decide +kernel

theorem combined476_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined476 (momentValues f) = 0 := by
  rw [← combined476_checked, Certificate.Integer.Sparse.eval_merge,
    combined475_zero f hcross, combined347_zero f hcross, add_zero]

theorem combined477_checked : Certificate.Integer.Sparse.merge combined476 combined303 = combined477 := by
  decide +kernel

theorem combined477_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined477 (momentValues f) = 0 := by
  rw [← combined477_checked, Certificate.Integer.Sparse.eval_merge,
    combined476_zero f hcross, combined303_zero f hcross, add_zero]

theorem combined478_checked : Certificate.Integer.Sparse.merge combined477 combined311 = combined478 := by
  decide +kernel

theorem combined478_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined478 (momentValues f) = 0 := by
  rw [← combined478_checked, Certificate.Integer.Sparse.eval_merge,
    combined477_zero f hcross, combined311_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Tao_TaoTarget
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6.TaoArithmetic

theorem eval_known_monomial (f : Charge → ℂ) (hf : OrderTwoValues f)
    (a : Charge) (z : Coeff) (n : ℤ)
    (ha : Balanced a) (ho : order a = 2) (hn : mul z (counts a) = (n, 0)) :
    Certificate.Integer.Sparse.eval (monomial a z) (momentValues f) = -(n : ℝ) / 30 := by
  rw [eval_monomial]
  have h := congrArg value hn
  rw [value_mul, counts_interpretation] at h
  have hvn : value (n, 0) = (n : ℂ) := by simp [value]
  rw [hvn] at h
  have he : value z * f a = -(n : ℂ) / 30 := by
    rw [hf a ha ho]
    linear_combination -h / 30
  rw [he]
  simp

theorem eval_knownTerms (f : Charge → ℂ) (hf : OrderTwoValues f)
    (ps : List (Charge × Coeff)) (n : ℤ)
    (hp : ps.Forall (fun p => Balanced p.1 ∧ order p.1 = 2 ∧
      mul p.2 (counts p.1) = (n, 0))) :
    Certificate.Integer.Sparse.eval (knownTerms ps) (momentValues f) =
      -(n : ℝ) / 30 * ps.length := by
  induction ps with
  | nil => simp [knownTerms]
  | cons p ps ih =>
    rw [List.forall_cons] at hp
    obtain ⟨⟨ha, ho, hn⟩, ht⟩ := hp
    rw [knownTerms, List.flatMap_cons, Certificate.Integer.Sparse.eval_append,
      eval_known_monomial f hf p.1 p.2 n ha ho hn]
    rw [show ps.flatMap (fun p => monomial p.1 p.2) = knownTerms ps from rfl, ih ht]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

theorem eval_cubeTerms (f : Charge → ℂ) :
    Certificate.Integer.Sparse.eval cubeTerms (momentValues f) =
      36 * offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re) := by
  rw [cubeTerms, eval_flatMap]
  simp_rw [eval_monomial]
  simp only [value, Int.cast_zero, zero_mul, add_zero, Int.cast_ofNat]
  have hs := congrArg Complex.re
    (offDiagonalPairs_sum (fun i j => (36 : ℂ) * f ((3 : ℤ) • difference i j)))
  simp only [re_list_sum, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero, offDiagSum, Complex.re_sum, List.map_map, Function.comp_def] at hs
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  rw [hs]
  simp only [offDiagSum, Finset.mul_sum]

end MUB6.TaoArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget13
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem knownTarget13_checked : normalize (knownTerms knownParams13) = knownTarget13 := by
  decide +kernel

theorem knownParams13_valid : knownParams13.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (-432, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget13_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget13 (momentValues f) = 216 := by
  rw [← knownTarget13_checked, eval_normalize,
    eval_knownTerms f hf knownParams13 (-432) knownParams13_valid]
  norm_num [knownParams13]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget12
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem knownTarget12_checked : normalize (knownTerms knownParams12) = knownTarget12 := by
  decide +kernel

theorem knownParams12_valid : knownParams12.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (-432, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget12_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget12 (momentValues f) = 216 := by
  rw [← knownTarget12_checked, eval_normalize,
    eval_knownTerms f hf knownParams12 (-432) knownParams12_valid]
  norm_num [knownParams12]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget11
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem knownTarget11_checked : normalize (knownTerms knownParams11) = knownTarget11 := by
  decide +kernel

theorem knownParams11_valid : knownParams11.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (-432, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget11_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget11 (momentValues f) = 216 := by
  rw [← knownTarget11_checked, eval_normalize,
    eval_knownTerms f hf knownParams11 (-432) knownParams11_valid]
  norm_num [knownParams11]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget10
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem knownTarget10_checked : normalize (knownTerms knownParams10) = knownTarget10 := by
  decide +kernel

theorem knownParams10_valid : knownParams10.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (-432, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget10_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget10 (momentValues f) = 216 := by
  rw [← knownTarget10_checked, eval_normalize,
    eval_knownTerms f hf knownParams10 (-432) knownParams10_valid]
  norm_num [knownParams10]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget9
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem knownTarget9_checked : normalize (knownTerms knownParams9) = knownTarget9 := by
  decide +kernel

theorem knownParams9_valid : knownParams9.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (-432, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget9_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget9 (momentValues f) = 216 := by
  rw [← knownTarget9_checked, eval_normalize,
    eval_knownTerms f hf knownParams9 (-432) knownParams9_valid]
  norm_num [knownParams9]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget8
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem knownTarget8_checked : normalize (knownTerms knownParams8) = knownTarget8 := by
  decide +kernel

theorem knownParams8_valid : knownParams8.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (-432, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget8_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget8 (momentValues f) = 216 := by
  rw [← knownTarget8_checked, eval_normalize,
    eval_knownTerms f hf knownParams8 (-432) knownParams8_valid]
  norm_num [knownParams8]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget7
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem knownTarget7_checked : normalize (knownTerms knownParams7) = knownTarget7 := by
  decide +kernel

theorem knownParams7_valid : knownParams7.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (108, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget7_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget7 (momentValues f) = -54 := by
  rw [← knownTarget7_checked, eval_normalize,
    eval_knownTerms f hf knownParams7 (108) knownParams7_valid]
  norm_num [knownParams7]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget6
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem knownTarget6_checked : normalize (knownTerms knownParams6) = knownTarget6 := by
  decide +kernel

theorem knownParams6_valid : knownParams6.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (108, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget6_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget6 (momentValues f) = -54 := by
  rw [← knownTarget6_checked, eval_normalize,
    eval_knownTerms f hf knownParams6 (108) knownParams6_valid]
  norm_num [knownParams6]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget5
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem knownTarget5_checked : normalize (knownTerms knownParams5) = knownTarget5 := by
  decide +kernel

theorem knownParams5_valid : knownParams5.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (108, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget5_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget5 (momentValues f) = -54 := by
  rw [← knownTarget5_checked, eval_normalize,
    eval_knownTerms f hf knownParams5 (108) knownParams5_valid]
  norm_num [knownParams5]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget4
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem knownTarget4_checked : normalize (knownTerms knownParams4) = knownTarget4 := by
  decide +kernel

theorem knownParams4_valid : knownParams4.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (108, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget4_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget4 (momentValues f) = -54 := by
  rw [← knownTarget4_checked, eval_normalize,
    eval_knownTerms f hf knownParams4 (108) knownParams4_valid]
  norm_num [knownParams4]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget3
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem knownTarget3_checked : normalize (knownTerms knownParams3) = knownTarget3 := by
  decide +kernel

theorem knownParams3_valid : knownParams3.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (108, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget3_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget3 (momentValues f) = -54 := by
  rw [← knownTarget3_checked, eval_normalize,
    eval_knownTerms f hf knownParams3 (108) knownParams3_valid]
  norm_num [knownParams3]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget2
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem knownTarget2_checked : normalize (knownTerms knownParams2) = knownTarget2 := by
  decide +kernel

theorem knownParams2_valid : knownParams2.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (108, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget2_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget2 (momentValues f) = -54 := by
  rw [← knownTarget2_checked, eval_normalize,
    eval_knownTerms f hf knownParams2 (108) knownParams2_valid]
  norm_num [knownParams2]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem knownTarget1_checked : normalize (knownTerms knownParams1) = knownTarget1 := by
  decide +kernel

theorem knownParams1_valid : knownParams1.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (108, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget1_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget1 (momentValues f) = -54 := by
  rw [← knownTarget1_checked, eval_normalize,
    eval_knownTerms f hf knownParams1 (108) knownParams1_valid]
  norm_num [knownParams1]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_CubeTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem cubeTarget_checked : normalize cubeTerms = cubeTarget := by decide +kernel

theorem cubeTarget_value (f : Charge → ℂ) :
    Certificate.Integer.Sparse.eval cubeTarget (momentValues f) =
      36 * offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re) := by
  rw [← cubeTarget_checked, eval_normalize, eval_cubeTerms]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_KnownTarget0
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem knownTarget0_checked : normalize (knownTerms knownParams0) = knownTarget0 := by
  decide +kernel

theorem knownParams0_valid : knownParams0.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (108, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget0_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget0 (momentValues f) = -54 := by
  rw [← knownTarget0_checked, eval_normalize,
    eval_knownTerms f hf knownParams0 (108) knownParams0_valid]
  norm_num [knownParams0]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_TargetMerge0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem targetCombined0_checked : Certificate.Integer.Sparse.merge cubeTarget knownTarget0 = targetCombined0 := by
  decide +kernel

theorem targetCombined0_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval targetCombined0 (momentValues f) =
      36 * offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re) + (-54) := by
  rw [← targetCombined0_checked, Certificate.Integer.Sparse.eval_merge,
    cubeTarget_value f, knownTarget0_value f hf]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_TargetMerge1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem targetCombined1_checked : Certificate.Integer.Sparse.merge targetCombined0 knownTarget1 = targetCombined1 := by
  decide +kernel

theorem targetCombined1_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval targetCombined1 (momentValues f) =
      36 * offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re) + (-108) := by
  rw [← targetCombined1_checked, Certificate.Integer.Sparse.eval_merge,
    targetCombined0_value f hf, knownTarget1_value f hf]
  ring

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_TargetMerge2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem targetCombined2_checked : Certificate.Integer.Sparse.merge targetCombined1 knownTarget2 = targetCombined2 := by
  decide +kernel

theorem targetCombined2_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval targetCombined2 (momentValues f) =
      36 * offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re) + (-162) := by
  rw [← targetCombined2_checked, Certificate.Integer.Sparse.eval_merge,
    targetCombined1_value f hf, knownTarget2_value f hf]
  ring

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_TargetMerge3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem targetCombined3_checked : Certificate.Integer.Sparse.merge targetCombined2 knownTarget3 = targetCombined3 := by
  decide +kernel

theorem targetCombined3_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval targetCombined3 (momentValues f) =
      36 * offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re) + (-216) := by
  rw [← targetCombined3_checked, Certificate.Integer.Sparse.eval_merge,
    targetCombined2_value f hf, knownTarget3_value f hf]
  ring

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_TargetMerge4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem targetCombined4_checked : Certificate.Integer.Sparse.merge targetCombined3 knownTarget4 = targetCombined4 := by
  decide +kernel

theorem targetCombined4_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval targetCombined4 (momentValues f) =
      36 * offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re) + (-270) := by
  rw [← targetCombined4_checked, Certificate.Integer.Sparse.eval_merge,
    targetCombined3_value f hf, knownTarget4_value f hf]
  ring

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_TargetMerge5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem targetCombined5_checked : Certificate.Integer.Sparse.merge targetCombined4 knownTarget5 = targetCombined5 := by
  decide +kernel

theorem targetCombined5_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval targetCombined5 (momentValues f) =
      36 * offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re) + (-324) := by
  rw [← targetCombined5_checked, Certificate.Integer.Sparse.eval_merge,
    targetCombined4_value f hf, knownTarget5_value f hf]
  ring

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_TargetMerge6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem targetCombined6_checked : Certificate.Integer.Sparse.merge targetCombined5 knownTarget6 = targetCombined6 := by
  decide +kernel

theorem targetCombined6_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval targetCombined6 (momentValues f) =
      36 * offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re) + (-378) := by
  rw [← targetCombined6_checked, Certificate.Integer.Sparse.eval_merge,
    targetCombined5_value f hf, knownTarget6_value f hf]
  ring

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_TargetMerge7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem targetCombined7_checked : Certificate.Integer.Sparse.merge targetCombined6 knownTarget7 = targetCombined7 := by
  decide +kernel

theorem targetCombined7_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval targetCombined7 (momentValues f) =
      36 * offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re) + (-432) := by
  rw [← targetCombined7_checked, Certificate.Integer.Sparse.eval_merge,
    targetCombined6_value f hf, knownTarget7_value f hf]
  ring

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_TargetMerge8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem targetCombined8_checked : Certificate.Integer.Sparse.merge targetCombined7 knownTarget8 = targetCombined8 := by
  decide +kernel

theorem targetCombined8_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval targetCombined8 (momentValues f) =
      36 * offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re) + (-216) := by
  rw [← targetCombined8_checked, Certificate.Integer.Sparse.eval_merge,
    targetCombined7_value f hf, knownTarget8_value f hf]
  ring

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_TargetMerge9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem targetCombined9_checked : Certificate.Integer.Sparse.merge targetCombined8 knownTarget9 = targetCombined9 := by
  decide +kernel

theorem targetCombined9_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval targetCombined9 (momentValues f) =
      36 * offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re) + (0) := by
  rw [← targetCombined9_checked, Certificate.Integer.Sparse.eval_merge,
    targetCombined8_value f hf, knownTarget9_value f hf]
  ring

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_TargetMerge10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem targetCombined10_checked : Certificate.Integer.Sparse.merge targetCombined9 knownTarget10 = targetCombined10 := by
  decide +kernel

theorem targetCombined10_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval targetCombined10 (momentValues f) =
      36 * offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re) + (216) := by
  rw [← targetCombined10_checked, Certificate.Integer.Sparse.eval_merge,
    targetCombined9_value f hf, knownTarget10_value f hf]
  ring

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_TargetMerge11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem targetCombined11_checked : Certificate.Integer.Sparse.merge targetCombined10 knownTarget11 = targetCombined11 := by
  decide +kernel

theorem targetCombined11_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval targetCombined11 (momentValues f) =
      36 * offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re) + (432) := by
  rw [← targetCombined11_checked, Certificate.Integer.Sparse.eval_merge,
    targetCombined10_value f hf, knownTarget11_value f hf]
  ring

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_TargetMerge12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem targetCombined12_checked : Certificate.Integer.Sparse.merge targetCombined11 knownTarget12 = targetCombined12 := by
  decide +kernel

theorem targetCombined12_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval targetCombined12 (momentValues f) =
      36 * offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re) + (648) := by
  rw [← targetCombined12_checked, Certificate.Integer.Sparse.eval_merge,
    targetCombined11_value f hf, knownTarget12_value f hf]
  ring

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_TargetMerge13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem targetCombined13_checked : Certificate.Integer.Sparse.merge targetCombined12 knownTarget13 = targetCombined13 := by
  decide +kernel

theorem targetCombined13_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval targetCombined13 (momentValues f) =
      36 * offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re) + (864) := by
  rw [← targetCombined13_checked, Certificate.Integer.Sparse.eval_merge,
    targetCombined12_value f hf, knownTarget13_value f hf]
  ring

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Conclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source_eq_target : combined478 = targetCombined13 := by rfl

/-- The exact source-derived Tao exclusion certificate contradicts cubic positivity. -/
theorem tao_exclusion (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0)
    (horder : OrderTwoValues f)
    (hpositive : 0 ≤ 6 + offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re)) : False := by
  have hz := combined478_zero f hcross
  rw [source_eq_target, targetCombined13_value f horder] at hz
  linarith

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Tao_TaoFamily
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem commonRowTransform_isHadamard {H : CMatrix} (hH : IsHadamard H)
    (r : Equiv.Perm Coord) (u : Coord → ℂ) (hu : ∀ i, Complex.normSq (u i) = 1) :
    IsHadamard (commonRowTransform H r u) := by
  have hh := (hH.permutations r (Equiv.refl Coord)).phaseTransform u (fun _ => 1) hu (by simp)
  change IsHadamard (fun i j => u i * H (r i) j * 1) at hh
  change IsHadamard (fun i j => u i * H (r i) j)
  simpa only [mul_one] using hh

theorem g_commonRowTransform (H : CMatrix) (r : Equiv.Perm Coord)
    (u : Coord → ℂ) (a : Charge) :
    g (commonRowTransform H r u) a = character u a * g H (permuteCharge r.symm a) := by
  calc
    _ = character u a * g (fun i j => H (r i) j) a :=
      g_row_phase (fun i j => H (r i) j) u a
    _ = _ := by rw [g_row_permutation H r a]

theorem balanced_permute (r : Equiv.Perm Coord) {a : Charge} (ha : Balanced a) :
    Balanced (permuteCharge r a) := by
  simpa only [Balanced, permuteCharge, Function.comp_apply, Equiv.sum_comp] using ha

theorem order_permute (r : Equiv.Perm Coord) (a : Charge) :
    order (permuteCharge r a) = order a := by
  exact Equiv.sum_comp r (fun i => (a i).toNat)

theorem commonRowTransform_cross (H K : CMatrix) (r : Equiv.Perm Coord)
    (u : Coord → ℂ) (hu : ∀ i, Complex.normSq (u i) = 1) (k l : Coord) :
    (∑ i, commonRowTransform H r u i k * conj (commonRowTransform K r u i l)) =
      ∑ i, H i k * conj (K i l) := by
  calc
    _ = ∑ i, H (r i) k * conj (K (r i) l) := by
      apply Finset.sum_congr rfl
      intro i _
      have hunit : u i * conj (u i) = 1 := by rw [Complex.mul_conj, hu]; rfl
      simp only [commonRowTransform, map_mul]
      calc
        _ = (u i * conj (u i)) * (H (r i) k * conj (K (r i) l)) := by ring
        _ = _ := by rw [hunit, one_mul]
    _ = _ := Equiv.sum_comp r (fun i => H i k * conj (K i l))

theorem columnTransform_cross (H K : CMatrix) (c : Equiv.Perm Coord)
    (v : Coord → ℂ) (hv : ∀ j, Complex.normSq (v j) = 1) (k l : Coord) :
    Complex.normSq (∑ i, H i k * conj (K i (c l) * v l)) =
      Complex.normSq (∑ i, H i k * conj (K i (c l))) := by
  have he : (∑ i, H i k * conj (K i (c l) * v l)) =
      (∑ i, H i k * conj (K i (c l))) * conj (v l) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_mul, mul_assoc]
  rw [he, map_mul, Complex.normSq_conj, hv, mul_one]

theorem averageOtherFourier_order_two (U : Coord → CMatrix) (s : Coord)
    (hs : ∀ a, Balanced a → g (U s) a = g tao a)
    (horder : ∀ a, Balanced a → order a = 2 → ∑ t, g (U t) a = 0) :
    TaoArithmetic.OrderTwoValues (averageOtherFourier U s) := by
  intro a ha ho
  have hsum := horder a ha ho
  rw [Fin.sum_univ_succAbove _ s, hs a ha] at hsum
  have he : (∑ t : Fin 5, g (U (s.succAbove t)) a) = -g tao a := by
    linear_combination hsum
  rw [averageOtherFourier, he]
  ring

theorem averageOtherFourier_positive (U : Coord → CMatrix) (s : Coord)
    (hU : ∀ t, IsHadamard (U t)) :
    0 ≤ 6 + offDiagSum (fun i j =>
      (averageOtherFourier U s ((3 : ℤ) • difference i j)).re) := by
  have hsum := Finset.sum_nonneg (s := Finset.univ) (fun t _ =>
    cubic_fourier_nonnegative (hU (s.succAbove t)))
  have havg (a : Charge) : (averageOtherFourier U s a).re =
      (5 : ℝ)⁻¹ * ∑ t : Fin 5, (g (U (s.succAbove t)) a).re := by
    simp [averageOtherFourier, Complex.mul_re]
  have he : offDiagSum (fun i j =>
      (averageOtherFourier U s ((3 : ℤ) • difference i j)).re) =
      (5 : ℝ)⁻¹ * ∑ t : Fin 5, offDiagSum (fun i j =>
        (g (U (s.succAbove t)) ((3 : ℤ) • difference i j)).re) := by
    simp_rw [havg]
    calc
      _ = (5 : ℝ)⁻¹ * offDiagSum (fun i j => ∑ t : Fin 5,
          (g (U (s.succAbove t)) ((3 : ℤ) • difference i j)).re) := by
        simp only [offDiagSum, Finset.mul_sum]
      _ = _ := by rw [offDiagSum_sum]
  rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  norm_num at hsum ⊢
  linarith

theorem different_matrices_conjugated {H K : CMatrix} (hH : IsHadamard H)
    (hK : IsHadamard K)
    (hc : ∀ k l, Complex.normSq (∑ i, H i k * conj (K i l)) = 6) (a c : Charge) :
    offDiagSum (fun i j => g H (a + difference i j) * conj (g K (c + difference i j))) = 0 := by
  have h := different_matrices_identity hH hK hc a (-c)
  have he (i j : Coord) : -c + difference j i = -(c + difference i j) := by
    rw [difference_reverse j i]
    abel
  simpa only [he, g_neg hK] using h

theorem averageOtherFourier_cross (U : Coord → CMatrix) (s : Coord)
    (hU : ∀ t, IsHadamard (U t))
    (hc : ∀ t : Fin 5, ∀ k l,
      Complex.normSq (∑ i, U (s.succAbove t) i k * conj (tao i l)) = 6)
    (a c : Charge) :
    offDiagSum (fun i j => averageOtherFourier U s (a + difference i j) *
      conj (g tao (c + difference i j))) = 0 := by
  have he (i j : Coord) :
      averageOtherFourier U s (a + difference i j) * conj (g tao (c + difference i j)) =
      (5 : ℂ)⁻¹ * ∑ t : Fin 5,
        g (U (s.succAbove t)) (a + difference i j) * conj (g tao (c + difference i j)) := by
    rw [averageOtherFourier, mul_assoc, Finset.sum_mul]
  simp_rw [he]
  rw [offDiagSum_mul, offDiagSum_sum]
  have hz : (∑ t : Fin 5, offDiagSum (fun i j =>
      g (U (s.succAbove t)) (a + difference i j) * conj (g tao (c + difference i j)))) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    exact different_matrices_conjugated (hU _) tao_isHadamard (hc t) a c
  rw [hz, mul_zero]

/-- A full-equivalence copy of Tao in six candidate Hadamards supplies exactly
    the three hypotheses of the checked Tao certificate. -/
theorem equivalent_tao_average (H : Coord → CMatrix)
    (hH : ∀ t, IsHadamard (H t))
    (hcross : ∀ t s, t ≠ s → ∀ k l,
      Complex.normSq (∑ i, H t i k * conj (H s i l)) = 6)
    (horder : ∀ a, Balanced a → order a = 2 → ∑ t, g (H t) a = 0)
    (s : Coord) (heq : Equivalent (H s) tao) :
    ∃ f : Charge → ℂ,
      (∀ a c, Balanced a → Balanced c →
        offDiagSum (fun i j => f (a + difference i j) *
          star (g tao (c + difference i j))) = 0) ∧
      TaoArithmetic.OrderTwoValues f ∧
      0 ≤ 6 + offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re) := by
  rcases heq with ⟨r, c, u, v, hu, hv, heq⟩
  let U : Coord → CMatrix := fun t => commonRowTransform (H t) r u
  have hU (t : Coord) : IsHadamard (U t) := commonRowTransform_isHadamard (hH t) r u hu
  have htao : tao = fun i j => U s i (c j) * v j := by
    funext i j
    exact heq i j
  have hs (a : Charge) (ha : Balanced a) : g (U s) a = g tao a := by
    calc
      _ = g (fun i j => U s i (c j)) a := (g_column_permutation (U s) c a).symm
      _ = g (fun i j => U s i (c j) * v j) a :=
        (g_column_phase (fun i j => U s i (c j)) v (fun j => unit_ne_zero (hv j)) a ha).symm
      _ = _ := by rw [htao]
  have hUorder (a : Charge) (ha : Balanced a) (ho : order a = 2) : ∑ t, g (U t) a = 0 := by
    change (∑ t, g (commonRowTransform (H t) r u) a) = 0
    simp_rw [g_commonRowTransform]
    rw [← Finset.mul_sum, horder _ (balanced_permute r.symm ha)
      (by rw [order_permute]; exact ho), mul_zero]
  have hUcross (t : Fin 5) (k l : Coord) :
      Complex.normSq (∑ i, U (s.succAbove t) i k * conj (tao i l)) = 6 := by
    calc
      _ = Complex.normSq (∑ i, U (s.succAbove t) i k * conj (U s i (c l) * v l)) := by
        rw [htao]
      _ = Complex.normSq (∑ i, U (s.succAbove t) i k * conj (U s i (c l))) :=
        columnTransform_cross (U (s.succAbove t)) (U s) c v hv k l
      _ = Complex.normSq (∑ i, H (s.succAbove t) i k * conj (H s i (c l))) := by
        rw [commonRowTransform_cross _ _ r u hu]
      _ = 6 := hcross _ _ (s.ne_succAbove t).symm k (c l)
  refine ⟨averageOtherFourier U s, ?_, averageOtherFourier_order_two U s hs hUorder,
    averageOtherFourier_positive U s hU⟩
  intro a c _ _
  exact averageOtherFourier_cross U s hU hUcross a c

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Tao_TaoCompleteFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

/-- The Tao class is excluded by the exact certificate, without choosing a
restricted phase convention for any of the six matrices. -/
theorem matrix_family_not_equivalent_tao (H : Coord → CMatrix)
    (hH : ∀ t, IsHadamard (H t))
    (hcross : ∀ t s, t ≠ s → ∀ k l,
      Complex.normSq (∑ i, H t i k * conj (H s i l)) = 6)
    (horder : ∀ a, Balanced a → order a = 2 → ∑ t, g (H t) a = 0)
    (s : Coord) : ¬Equivalent (H s) tao := by
  intro heq
  obtain ⟨f, hc, ho, hp⟩ := equivalent_tao_average H hH hcross horder s heq
  exact TaoCertificate.tao_exclusion f hc ho hp

/-- No transition matrix of a complete mutually unbiased family can belong to
Tao's cubic equivalence class. -/
theorem complete_family_not_equivalent_tao (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (s : Coord) : ¬Equivalent (relativeMatrix B r s) tao := by
  apply matrix_family_not_equivalent_tao (relativeMatrix B r)
  · exact relativeMatrix_isHadamard B hB r
  · exact relativeMatrix_cross B hB r
  · intro a ha ho
    exact complete_family_order_two B hB r ha ho

/-- Proposition (cubic-exclusion) in the manuscript. -/
theorem complete_family_square_not_hadamard_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (s : Coord) :
    ¬IsHadamard (fun i j => relativeMatrix B r s i j ^ 2) := by
  intro hsquare
  exact complete_family_not_equivalent_tao B hB r s
    (hadamard_square_equivalent_tao (relativeMatrix_isHadamard B hB r s) hsquare)

end MUB6

end

end OAI
end

theorem solution : type_of% @OAI.MUB6.complete_family_square_not_hadamard_e_oai := @OAI.MUB6.complete_family_square_not_hadamard_e_oai
