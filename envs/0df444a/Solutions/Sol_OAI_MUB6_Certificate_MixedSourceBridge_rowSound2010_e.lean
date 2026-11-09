-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:58:11.575303+00:00
-- url     : https://prove2.me/submissions/c3892e25-7e9c-40b7-9900-a844c66277ed

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E101
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1536 raw1536Labels = mixedMoment B node4660 node4660Labels := by
  calc
    mixedMoment B raw1536 raw1536Labels = mixedMoment B raw1536step0 raw1536step0Labels := by
      have ha : raw1536step0 = (fun i j => raw1536 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1536step0 raw1536; decide +kernel
      have hl : raw1536step0Labels = raw1536Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1536 raw1536Labels permutation152 permutation4
    mixedMoment B raw1536step0 raw1536step0Labels = mixedMoment B raw1536step1 raw1536step1Labels := by
      have ha : raw1536step1 = raw1536step0 := by apply Matrix.ext; unfold raw1536step1 raw1536step0; decide +kernel
      have hl : raw1536step0Labels = labelEmbedding7 ∘ raw1536step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1536step0 raw1536step0Labels raw1536step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4660 node4660Labels := by rfl

theorem canonical1537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1537 raw1537Labels = mixedMoment B node1786 node1786Labels := by
  calc
    mixedMoment B raw1537 raw1537Labels = mixedMoment B raw1537step0 raw1537step0Labels := by
      have ha : raw1537step0 = (fun i j => raw1537 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1537step0 raw1537; decide +kernel
      have hl : raw1537step0Labels = raw1537Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1537 raw1537Labels permutation152 permutation4
    _ = mixedMoment B node1786 node1786Labels := by rfl

theorem canonical1538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1538 raw1538Labels = mixedMoment B node1982 node1982Labels := by
  calc
    mixedMoment B raw1538 raw1538Labels = mixedMoment B raw1538step0 raw1538step0Labels := by
      have ha : raw1538step0 = (fun i j => raw1538 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1538step0 raw1538; decide +kernel
      have hl : raw1538step0Labels = raw1538Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1538 raw1538Labels permutation176 permutation6
    mixedMoment B raw1538step0 raw1538step0Labels = mixedMoment B raw1538step1 raw1538step1Labels := by
      have ha : raw1538step1 = -raw1538step0 := by apply Matrix.ext; change ∀ i j, raw1538step1 i j = -(raw1538step0 i j); unfold raw1538step1 raw1538step0; decide +kernel
      have hl : raw1538step1Labels = raw1538step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1538step1 raw1538step1Labels = mixedMoment B raw1538step2 raw1538step2Labels := by
      have ha : raw1538step2 = raw1538step1 := by apply Matrix.ext; unfold raw1538step2 raw1538step1; decide +kernel
      have hl : raw1538step1Labels = labelEmbedding1 ∘ raw1538step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1538step1 raw1538step1Labels raw1538step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1982 node1982Labels := by rfl

theorem canonical1539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1539 raw1539Labels = mixedMoment B node4661 node4661Labels := by
  calc
    mixedMoment B raw1539 raw1539Labels = mixedMoment B raw1539step0 raw1539step0Labels := by
      have ha : raw1539step0 = (fun i j => raw1539 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1539step0 raw1539; decide +kernel
      have hl : raw1539step0Labels = raw1539Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1539 raw1539Labels permutation152 permutation4
    mixedMoment B raw1539step0 raw1539step0Labels = mixedMoment B raw1539step1 raw1539step1Labels := by
      have ha : raw1539step1 = raw1539step0 := by apply Matrix.ext; unfold raw1539step1 raw1539step0; decide +kernel
      have hl : raw1539step0Labels = labelEmbedding7 ∘ raw1539step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1539step0 raw1539step0Labels raw1539step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4661 node4661Labels := by rfl

theorem canonical1540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1540 raw1540Labels = mixedMoment B node1787 node1787Labels := by
  calc
    mixedMoment B raw1540 raw1540Labels = mixedMoment B raw1540step0 raw1540step0Labels := by
      have ha : raw1540step0 = (fun i j => raw1540 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1540step0 raw1540; decide +kernel
      have hl : raw1540step0Labels = raw1540Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1540 raw1540Labels permutation152 permutation4
    _ = mixedMoment B node1787 node1787Labels := by rfl

theorem canonical1541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1541 raw1541Labels = mixedMoment B node1983 node1983Labels := by
  calc
    mixedMoment B raw1541 raw1541Labels = mixedMoment B raw1541step0 raw1541step0Labels := by
      have ha : raw1541step0 = (fun i j => raw1541 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1541step0 raw1541; decide +kernel
      have hl : raw1541step0Labels = raw1541Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1541 raw1541Labels permutation176 permutation6
    mixedMoment B raw1541step0 raw1541step0Labels = mixedMoment B raw1541step1 raw1541step1Labels := by
      have ha : raw1541step1 = -raw1541step0 := by apply Matrix.ext; change ∀ i j, raw1541step1 i j = -(raw1541step0 i j); unfold raw1541step1 raw1541step0; decide +kernel
      have hl : raw1541step1Labels = raw1541step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1541step1 raw1541step1Labels = mixedMoment B raw1541step2 raw1541step2Labels := by
      have ha : raw1541step2 = raw1541step1 := by apply Matrix.ext; unfold raw1541step2 raw1541step1; decide +kernel
      have hl : raw1541step1Labels = labelEmbedding1 ∘ raw1541step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1541step1 raw1541step1Labels raw1541step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1983 node1983Labels := by rfl

theorem canonical1545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1545 raw1545Labels = mixedMoment B node4672 node4672Labels := by
  calc
    mixedMoment B raw1545 raw1545Labels = mixedMoment B raw1545step0 raw1545step0Labels := by
      have ha : raw1545step0 = (fun i j => raw1545 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1545step0 raw1545; decide +kernel
      have hl : raw1545step0Labels = raw1545Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1545 raw1545Labels permutation152 permutation4
    mixedMoment B raw1545step0 raw1545step0Labels = mixedMoment B raw1545step1 raw1545step1Labels := by
      have ha : raw1545step1 = raw1545step0 := by apply Matrix.ext; unfold raw1545step1 raw1545step0; decide +kernel
      have hl : raw1545step0Labels = labelEmbedding7 ∘ raw1545step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1545step0 raw1545step0Labels raw1545step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4672 node4672Labels := by rfl

theorem canonical1546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1546 raw1546Labels = mixedMoment B node1798 node1798Labels := by
  calc
    mixedMoment B raw1546 raw1546Labels = mixedMoment B raw1546step0 raw1546step0Labels := by
      have ha : raw1546step0 = (fun i j => raw1546 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1546step0 raw1546; decide +kernel
      have hl : raw1546step0Labels = raw1546Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1546 raw1546Labels permutation152 permutation4
    _ = mixedMoment B node1798 node1798Labels := by rfl

theorem canonical1547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1547 raw1547Labels = mixedMoment B node2067 node2067Labels := by
  calc
    mixedMoment B raw1547 raw1547Labels = mixedMoment B raw1547step0 raw1547step0Labels := by
      have ha : raw1547step0 = (fun i j => raw1547 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1547step0 raw1547; decide +kernel
      have hl : raw1547step0Labels = raw1547Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1547 raw1547Labels permutation176 permutation6
    mixedMoment B raw1547step0 raw1547step0Labels = mixedMoment B raw1547step1 raw1547step1Labels := by
      have ha : raw1547step1 = -raw1547step0 := by apply Matrix.ext; change ∀ i j, raw1547step1 i j = -(raw1547step0 i j); unfold raw1547step1 raw1547step0; decide +kernel
      have hl : raw1547step1Labels = raw1547step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1547step1 raw1547step1Labels = mixedMoment B raw1547step2 raw1547step2Labels := by
      have ha : raw1547step2 = raw1547step1 := by apply Matrix.ext; unfold raw1547step2 raw1547step1; decide +kernel
      have hl : raw1547step1Labels = labelEmbedding1 ∘ raw1547step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1547step1 raw1547step1Labels raw1547step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2067 node2067Labels := by rfl

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

theorem canonical1713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1713 raw1713Labels = mixedMoment B node4779 node4779Labels := by
  calc
    mixedMoment B raw1713 raw1713Labels = mixedMoment B raw1713step0 raw1713step0Labels := by
      have ha : raw1713step0 = (fun i j => raw1713 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1713step0 raw1713; decide +kernel
      have hl : raw1713step0Labels = raw1713Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1713 raw1713Labels permutation152 permutation4
    mixedMoment B raw1713step0 raw1713step0Labels = mixedMoment B raw1713step1 raw1713step1Labels := by
      have ha : raw1713step1 = raw1713step0 := by apply Matrix.ext; unfold raw1713step1 raw1713step0; decide +kernel
      have hl : raw1713step0Labels = labelEmbedding7 ∘ raw1713step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1713step0 raw1713step0Labels raw1713step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4779 node4779Labels := by rfl

theorem canonical1714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1714 raw1714Labels = mixedMoment B node1987 node1987Labels := by
  calc
    mixedMoment B raw1714 raw1714Labels = mixedMoment B raw1714step0 raw1714step0Labels := by
      have ha : raw1714step0 = (fun i j => raw1714 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1714step0 raw1714; decide +kernel
      have hl : raw1714step0Labels = raw1714Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1714 raw1714Labels permutation152 permutation4
    _ = mixedMoment B node1987 node1987Labels := by rfl

theorem canonical1715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1715 raw1715Labels = mixedMoment B node1996 node1996Labels := by
  calc
    mixedMoment B raw1715 raw1715Labels = mixedMoment B raw1715step0 raw1715step0Labels := by
      have ha : raw1715step0 = (fun i j => raw1715 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1715step0 raw1715; decide +kernel
      have hl : raw1715step0Labels = raw1715Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1715 raw1715Labels permutation176 permutation6
    mixedMoment B raw1715step0 raw1715step0Labels = mixedMoment B raw1715step1 raw1715step1Labels := by
      have ha : raw1715step1 = -raw1715step0 := by apply Matrix.ext; change ∀ i j, raw1715step1 i j = -(raw1715step0 i j); unfold raw1715step1 raw1715step0; decide +kernel
      have hl : raw1715step1Labels = raw1715step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1715step1 raw1715step1Labels = mixedMoment B raw1715step2 raw1715step2Labels := by
      have ha : raw1715step2 = raw1715step1 := by apply Matrix.ext; unfold raw1715step2 raw1715step1; decide +kernel
      have hl : raw1715step1Labels = labelEmbedding1 ∘ raw1715step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1715step1 raw1715step1Labels raw1715step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1996 node1996Labels := by rfl

theorem canonical1716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1716 raw1716Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw1716 raw1716Labels = mixedMoment B raw1716step0 raw1716step0Labels := by
      have ha : raw1716step0 = (fun i j => raw1716 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1716step0 raw1716; decide +kernel
      have hl : raw1716step0Labels = raw1716Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1716 raw1716Labels permutation152 permutation4
    mixedMoment B raw1716step0 raw1716step0Labels = mixedMoment B raw1716step1 raw1716step1Labels := by
      have ha : raw1716step1 = raw1716step0 := by apply Matrix.ext; unfold raw1716step1 raw1716step0; decide +kernel
      have hl : raw1716step0Labels = labelEmbedding7 ∘ raw1716step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1716step0 raw1716step0Labels raw1716step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

theorem canonical1717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1717 raw1717Labels = mixedMoment B node1990 node1990Labels := by
  calc
    mixedMoment B raw1717 raw1717Labels = mixedMoment B raw1717step0 raw1717step0Labels := by
      have ha : raw1717step0 = (fun i j => raw1717 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1717step0 raw1717; decide +kernel
      have hl : raw1717step0Labels = raw1717Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1717 raw1717Labels permutation152 permutation4
    _ = mixedMoment B node1990 node1990Labels := by rfl

theorem canonical1718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1718 raw1718Labels = mixedMoment B node1997 node1997Labels := by
  calc
    mixedMoment B raw1718 raw1718Labels = mixedMoment B raw1718step0 raw1718step0Labels := by
      have ha : raw1718step0 = (fun i j => raw1718 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1718step0 raw1718; decide +kernel
      have hl : raw1718step0Labels = raw1718Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1718 raw1718Labels permutation176 permutation6
    mixedMoment B raw1718step0 raw1718step0Labels = mixedMoment B raw1718step1 raw1718step1Labels := by
      have ha : raw1718step1 = -raw1718step0 := by apply Matrix.ext; change ∀ i j, raw1718step1 i j = -(raw1718step0 i j); unfold raw1718step1 raw1718step0; decide +kernel
      have hl : raw1718step1Labels = raw1718step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1718step1 raw1718step1Labels = mixedMoment B raw1718step2 raw1718step2Labels := by
      have ha : raw1718step2 = raw1718step1 := by apply Matrix.ext; unfold raw1718step2 raw1718step1; decide +kernel
      have hl : raw1718step1Labels = labelEmbedding1 ∘ raw1718step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1718step1 raw1718step1Labels raw1718step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1997 node1997Labels := by rfl

theorem canonical1719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1719 raw1719Labels = mixedMoment B node4787 node4787Labels := by
  calc
    mixedMoment B raw1719 raw1719Labels = mixedMoment B raw1719step0 raw1719step0Labels := by
      have ha : raw1719step0 = (fun i j => raw1719 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1719step0 raw1719; decide +kernel
      have hl : raw1719step0Labels = raw1719Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1719 raw1719Labels permutation152 permutation4
    mixedMoment B raw1719step0 raw1719step0Labels = mixedMoment B raw1719step1 raw1719step1Labels := by
      have ha : raw1719step1 = raw1719step0 := by apply Matrix.ext; unfold raw1719step1 raw1719step0; decide +kernel
      have hl : raw1719step0Labels = labelEmbedding7 ∘ raw1719step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1719step0 raw1719step0Labels raw1719step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4787 node4787Labels := by rfl

theorem canonical1720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1720 raw1720Labels = mixedMoment B node2000 node2000Labels := by
  calc
    mixedMoment B raw1720 raw1720Labels = mixedMoment B raw1720step0 raw1720step0Labels := by
      have ha : raw1720step0 = (fun i j => raw1720 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1720step0 raw1720; decide +kernel
      have hl : raw1720step0Labels = raw1720Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1720 raw1720Labels permutation152 permutation4
    _ = mixedMoment B node2000 node2000Labels := by rfl

theorem canonical1721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1721 raw1721Labels = mixedMoment B node2000 node2000Labels := by
  calc
    mixedMoment B raw1721 raw1721Labels = mixedMoment B raw1721step0 raw1721step0Labels := by
      have ha : raw1721step0 = (fun i j => raw1721 (permutation177 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1721step0 raw1721; decide +kernel
      have hl : raw1721step0Labels = raw1721Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1721 raw1721Labels permutation177 permutation6
    mixedMoment B raw1721step0 raw1721step0Labels = mixedMoment B raw1721step1 raw1721step1Labels := by
      have ha : raw1721step1 = -raw1721step0 := by apply Matrix.ext; change ∀ i j, raw1721step1 i j = -(raw1721step0 i j); unfold raw1721step1 raw1721step0; decide +kernel
      have hl : raw1721step1Labels = raw1721step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1721step1 raw1721step1Labels = mixedMoment B raw1721step2 raw1721step2Labels := by
      have ha : raw1721step2 = raw1721step1 := by apply Matrix.ext; unfold raw1721step2 raw1721step1; decide +kernel
      have hl : raw1721step1Labels = labelEmbedding1 ∘ raw1721step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1721step1 raw1721step1Labels raw1721step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2000 node2000Labels := by rfl

theorem canonical1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1725 raw1725Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw1725 raw1725Labels = mixedMoment B raw1725step0 raw1725step0Labels := by
      have ha : raw1725step0 = (fun i j => raw1725 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1725step0 raw1725; decide +kernel
      have hl : raw1725step0Labels = raw1725Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1725 raw1725Labels permutation152 permutation4
    mixedMoment B raw1725step0 raw1725step0Labels = mixedMoment B raw1725step1 raw1725step1Labels := by
      have ha : raw1725step1 = raw1725step0 := by apply Matrix.ext; unfold raw1725step1 raw1725step0; decide +kernel
      have hl : raw1725step0Labels = labelEmbedding7 ∘ raw1725step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1725step0 raw1725step0Labels raw1725step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical1726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1726 raw1726Labels = mixedMoment B node2016 node2016Labels := by
  calc
    mixedMoment B raw1726 raw1726Labels = mixedMoment B raw1726step0 raw1726step0Labels := by
      have ha : raw1726step0 = (fun i j => raw1726 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1726step0 raw1726; decide +kernel
      have hl : raw1726step0Labels = raw1726Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1726 raw1726Labels permutation152 permutation4
    _ = mixedMoment B node2016 node2016Labels := by rfl

theorem canonical1727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1727 raw1727Labels = mixedMoment B node2075 node2075Labels := by
  calc
    mixedMoment B raw1727 raw1727Labels = mixedMoment B raw1727step0 raw1727step0Labels := by
      have ha : raw1727step0 = (fun i j => raw1727 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1727step0 raw1727; decide +kernel
      have hl : raw1727step0Labels = raw1727Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1727 raw1727Labels permutation200 permutation6
    mixedMoment B raw1727step0 raw1727step0Labels = mixedMoment B raw1727step1 raw1727step1Labels := by
      have ha : raw1727step1 = -raw1727step0 := by apply Matrix.ext; change ∀ i j, raw1727step1 i j = -(raw1727step0 i j); unfold raw1727step1 raw1727step0; decide +kernel
      have hl : raw1727step1Labels = raw1727step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1727step1 raw1727step1Labels = mixedMoment B raw1727step2 raw1727step2Labels := by
      have ha : raw1727step2 = raw1727step1 := by apply Matrix.ext; unfold raw1727step2 raw1727step1; decide +kernel
      have hl : raw1727step1Labels = labelEmbedding1 ∘ raw1727step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1727step1 raw1727step1Labels raw1727step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2075 node2075Labels := by rfl

theorem canonical1752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1752 raw1752Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw1752 raw1752Labels = mixedMoment B raw1752step0 raw1752step0Labels := by
      have ha : raw1752step0 = (fun i j => raw1752 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1752step0 raw1752; decide +kernel
      have hl : raw1752step0Labels = raw1752Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1752 raw1752Labels permutation152 permutation4
    mixedMoment B raw1752step0 raw1752step0Labels = mixedMoment B raw1752step1 raw1752step1Labels := by
      have ha : raw1752step1 = raw1752step0 := by apply Matrix.ext; unfold raw1752step1 raw1752step0; decide +kernel
      have hl : raw1752step0Labels = labelEmbedding7 ∘ raw1752step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1752step0 raw1752step0Labels raw1752step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

theorem canonical1753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1753 raw1753Labels = mixedMoment B node2046 node2046Labels := by
  calc
    mixedMoment B raw1753 raw1753Labels = mixedMoment B raw1753step0 raw1753step0Labels := by
      have ha : raw1753step0 = (fun i j => raw1753 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1753step0 raw1753; decide +kernel
      have hl : raw1753step0Labels = raw1753Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1753 raw1753Labels permutation152 permutation4
    _ = mixedMoment B node2046 node2046Labels := by rfl

theorem canonical1754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1754 raw1754Labels = mixedMoment B node2077 node2077Labels := by
  calc
    mixedMoment B raw1754 raw1754Labels = mixedMoment B raw1754step0 raw1754step0Labels := by
      have ha : raw1754step0 = (fun i j => raw1754 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1754step0 raw1754; decide +kernel
      have hl : raw1754step0Labels = raw1754Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1754 raw1754Labels permutation176 permutation6
    mixedMoment B raw1754step0 raw1754step0Labels = mixedMoment B raw1754step1 raw1754step1Labels := by
      have ha : raw1754step1 = -raw1754step0 := by apply Matrix.ext; change ∀ i j, raw1754step1 i j = -(raw1754step0 i j); unfold raw1754step1 raw1754step0; decide +kernel
      have hl : raw1754step1Labels = raw1754step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1754step1 raw1754step1Labels = mixedMoment B raw1754step2 raw1754step2Labels := by
      have ha : raw1754step2 = raw1754step1 := by apply Matrix.ext; unfold raw1754step2 raw1754step1; decide +kernel
      have hl : raw1754step1Labels = labelEmbedding1 ∘ raw1754step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1754step1 raw1754step1Labels raw1754step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2077 node2077Labels := by rfl

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

theorem canonical2154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2154 raw2154Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw2154 raw2154Labels = mixedMoment B raw2154step0 raw2154step0Labels := by
      have ha : raw2154step0 = (fun i j => raw2154 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2154step0 raw2154; decide +kernel
      have hl : raw2154step0Labels = raw2154Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2154 raw2154Labels permutation152 permutation4
    mixedMoment B raw2154step0 raw2154step0Labels = mixedMoment B raw2154step1 raw2154step1Labels := by
      have ha : raw2154step1 = raw2154step0 := by apply Matrix.ext; unfold raw2154step1 raw2154step0; decide +kernel
      have hl : raw2154step0Labels = labelEmbedding7 ∘ raw2154step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2154step0 raw2154step0Labels raw2154step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

theorem canonical2155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2155 raw2155Labels = mixedMoment B node2536 node2536Labels := by
  calc
    mixedMoment B raw2155 raw2155Labels = mixedMoment B raw2155step0 raw2155step0Labels := by
      have ha : raw2155step0 = (fun i j => raw2155 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2155step0 raw2155; decide +kernel
      have hl : raw2155step0Labels = raw2155Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2155 raw2155Labels permutation152 permutation4
    _ = mixedMoment B node2536 node2536Labels := by rfl

theorem canonical2156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2156 raw2156Labels = mixedMoment B node3370 node3370Labels := by
  calc
    mixedMoment B raw2156 raw2156Labels = mixedMoment B raw2156step0 raw2156step0Labels := by
      have ha : raw2156step0 = (fun i j => raw2156 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2156step0 raw2156; decide +kernel
      have hl : raw2156step0Labels = raw2156Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2156 raw2156Labels permutation176 permutation6
    mixedMoment B raw2156step0 raw2156step0Labels = mixedMoment B raw2156step1 raw2156step1Labels := by
      have ha : raw2156step1 = -raw2156step0 := by apply Matrix.ext; change ∀ i j, raw2156step1 i j = -(raw2156step0 i j); unfold raw2156step1 raw2156step0; decide +kernel
      have hl : raw2156step1Labels = raw2156step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2156step1 raw2156step1Labels = mixedMoment B raw2156step2 raw2156step2Labels := by
      have ha : raw2156step2 = raw2156step1 := by apply Matrix.ext; unfold raw2156step2 raw2156step1; decide +kernel
      have hl : raw2156step1Labels = labelEmbedding1 ∘ raw2156step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2156step1 raw2156step1Labels raw2156step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3370 node3370Labels := by rfl

theorem canonical2163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2163 raw2163Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw2163 raw2163Labels = mixedMoment B raw2163step0 raw2163step0Labels := by
      have ha : raw2163step0 = (fun i j => raw2163 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2163step0 raw2163; decide +kernel
      have hl : raw2163step0Labels = raw2163Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2163 raw2163Labels permutation152 permutation4
    mixedMoment B raw2163step0 raw2163step0Labels = mixedMoment B raw2163step1 raw2163step1Labels := by
      have ha : raw2163step1 = raw2163step0 := by apply Matrix.ext; unfold raw2163step1 raw2163step0; decide +kernel
      have hl : raw2163step0Labels = labelEmbedding7 ∘ raw2163step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2163step0 raw2163step0Labels raw2163step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

theorem canonical2164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2164 raw2164Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw2164 raw2164Labels = mixedMoment B raw2164step0 raw2164step0Labels := by
      have ha : raw2164step0 = (fun i j => raw2164 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2164step0 raw2164; decide +kernel
      have hl : raw2164step0Labels = raw2164Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2164 raw2164Labels permutation152 permutation4
    _ = mixedMoment B node2553 node2553Labels := by rfl

theorem canonical2165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2165 raw2165Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw2165 raw2165Labels = mixedMoment B raw2165step0 raw2165step0Labels := by
      have ha : raw2165step0 = (fun i j => raw2165 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2165step0 raw2165; decide +kernel
      have hl : raw2165step0Labels = raw2165Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2165 raw2165Labels permutation176 permutation6
    mixedMoment B raw2165step0 raw2165step0Labels = mixedMoment B raw2165step1 raw2165step1Labels := by
      have ha : raw2165step1 = -raw2165step0 := by apply Matrix.ext; change ∀ i j, raw2165step1 i j = -(raw2165step0 i j); unfold raw2165step1 raw2165step0; decide +kernel
      have hl : raw2165step1Labels = raw2165step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2165step1 raw2165step1Labels = mixedMoment B raw2165step2 raw2165step2Labels := by
      have ha : raw2165step2 = raw2165step1 := by apply Matrix.ext; unfold raw2165step2 raw2165step1; decide +kernel
      have hl : raw2165step1Labels = labelEmbedding1 ∘ raw2165step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2165step1 raw2165step1Labels raw2165step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical204
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26136 raw26136Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw26136 raw26136Labels = mixedMoment B raw26136step0 raw26136step0Labels := by
      have hz : ∀ j, raw26136 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26136step0 = (fun i j => raw26136 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26136step0 raw26136; decide +kernel
      have hl : raw26136step0Labels = raw26136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26136 raw26136Labels permutation265 hz
    mixedMoment B raw26136step0 raw26136step0Labels = mixedMoment B raw26136step1 raw26136step1Labels := by
      have hz : ∀ i, raw26136step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw26136step1 = (fun i j => raw26136step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw26136step1 raw26136step0; decide +kernel
      have hl : raw26136step1Labels = (fun j => raw26136step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26136step0 raw26136step0Labels permutation4 hz
    mixedMoment B raw26136step1 raw26136step1Labels = mixedMoment B raw26136step2 raw26136step2Labels := by
      have ha : raw26136step2 = raw26136step1 := by apply Matrix.ext; unfold raw26136step2 raw26136step1; decide +kernel
      have hl : raw26136step1Labels = labelEmbedding2 ∘ raw26136step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26136step1 raw26136step1Labels raw26136step2Labels labelEmbedding2 hl
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical26137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26137 raw26137Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw26137 raw26137Labels = mixedMoment B raw26137step0 raw26137step0Labels := by
      have hz : ∀ j, raw26137 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26137step0 = (fun i j => raw26137 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26137step0 raw26137; decide +kernel
      have hl : raw26137step0Labels = raw26137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26137 raw26137Labels permutation265 hz
    mixedMoment B raw26137step0 raw26137step0Labels = mixedMoment B raw26137step1 raw26137step1Labels := by
      have ha : raw26137step1 = (fun i j => raw26137step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26137step1 raw26137step0; decide +kernel
      have hl : raw26137step1Labels = raw26137step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26137step0 raw26137step0Labels permutation32 permutation7
    mixedMoment B raw26137step1 raw26137step1Labels = mixedMoment B raw26137step2 raw26137step2Labels := by
      have ha : raw26137step2 = -raw26137step1 := by apply Matrix.ext; change ∀ i j, raw26137step2 i j = -(raw26137step1 i j); unfold raw26137step2 raw26137step1; decide +kernel
      have hl : raw26137step2Labels = raw26137step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26137step2 raw26137step2Labels = mixedMoment B raw26137step3 raw26137step3Labels := by
      have ha : raw26137step3 = raw26137step2 := by apply Matrix.ext; unfold raw26137step3 raw26137step2; decide +kernel
      have hl : raw26137step2Labels = labelEmbedding10 ∘ raw26137step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26137step2 raw26137step2Labels raw26137step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4834 node4834Labels := by rfl

theorem canonical26138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26138 raw26138Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw26138 raw26138Labels = mixedMoment B raw26138step0 raw26138step0Labels := by
      have hz : ∀ j, raw26138 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26138step0 = (fun i j => raw26138 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26138step0 raw26138; decide +kernel
      have hl : raw26138step0Labels = raw26138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26138 raw26138Labels permutation265 hz
    mixedMoment B raw26138step0 raw26138step0Labels = mixedMoment B raw26138step1 raw26138step1Labels := by
      have ha : raw26138step1 = (fun i j => raw26138step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26138step1 raw26138step0; decide +kernel
      have hl : raw26138step1Labels = raw26138step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26138step0 raw26138step0Labels permutation34 permutation7
    mixedMoment B raw26138step1 raw26138step1Labels = mixedMoment B raw26138step2 raw26138step2Labels := by
      have ha : raw26138step2 = -raw26138step1 := by apply Matrix.ext; change ∀ i j, raw26138step2 i j = -(raw26138step1 i j); unfold raw26138step2 raw26138step1; decide +kernel
      have hl : raw26138step2Labels = raw26138step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26138step2 raw26138step2Labels = mixedMoment B raw26138step3 raw26138step3Labels := by
      have ha : raw26138step3 = raw26138step2 := by apply Matrix.ext; unfold raw26138step3 raw26138step2; decide +kernel
      have hl : raw26138step2Labels = labelEmbedding10 ∘ raw26138step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26138step2 raw26138step2Labels raw26138step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4834 node4834Labels := by rfl

theorem canonical26139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26139 raw26139Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw26139 raw26139Labels = mixedMoment B raw26139step0 raw26139step0Labels := by
      have hz : ∀ j, raw26139 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26139step0 = (fun i j => raw26139 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26139step0 raw26139; decide +kernel
      have hl : raw26139step0Labels = raw26139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26139 raw26139Labels permutation265 hz
    mixedMoment B raw26139step0 raw26139step0Labels = mixedMoment B raw26139step1 raw26139step1Labels := by
      have ha : raw26139step1 = (fun i j => raw26139step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26139step1 raw26139step0; decide +kernel
      have hl : raw26139step1Labels = raw26139step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26139step0 raw26139step0Labels permutation32 permutation7
    mixedMoment B raw26139step1 raw26139step1Labels = mixedMoment B raw26139step2 raw26139step2Labels := by
      have ha : raw26139step2 = -raw26139step1 := by apply Matrix.ext; change ∀ i j, raw26139step2 i j = -(raw26139step1 i j); unfold raw26139step2 raw26139step1; decide +kernel
      have hl : raw26139step2Labels = raw26139step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26139step2 raw26139step2Labels = mixedMoment B raw26139step3 raw26139step3Labels := by
      have ha : raw26139step3 = raw26139step2 := by apply Matrix.ext; unfold raw26139step3 raw26139step2; decide +kernel
      have hl : raw26139step2Labels = labelEmbedding10 ∘ raw26139step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26139step2 raw26139step2Labels raw26139step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4838 node4838Labels := by rfl

theorem canonical26146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26146 raw26146Labels = mixedMoment B node4337 node4337Labels := by
  calc
    _ = mixedMoment B node4337 node4337Labels := by rfl

theorem canonical26151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26151 raw26151Labels = mixedMoment B node4323 node4323Labels := by
  calc
    mixedMoment B raw26151 raw26151Labels = mixedMoment B raw26151step0 raw26151step0Labels := by
      have ha : raw26151step0 = (fun i j => raw26151 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26151step0 raw26151; decide +kernel
      have hl : raw26151step0Labels = raw26151Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26151 raw26151Labels permutation154 permutation2
    _ = mixedMoment B node4323 node4323Labels := by rfl

theorem canonical26156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26156 raw26156Labels = mixedMoment B node4323 node4323Labels := by
  calc
    _ = mixedMoment B node4323 node4323Labels := by rfl

theorem canonical26161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26161 raw26161Labels = mixedMoment B node4322 node4322Labels := by
  calc
    _ = mixedMoment B node4322 node4322Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical268
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34373 raw34373Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw34373 raw34373Labels = mixedMoment B raw34373step0 raw34373step0Labels := by
      have ha : raw34373step0 = (fun i j => raw34373 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34373step0 raw34373; decide +kernel
      have hl : raw34373step0Labels = raw34373Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34373 raw34373Labels permutation176 permutation7
    mixedMoment B raw34373step0 raw34373step0Labels = mixedMoment B raw34373step1 raw34373step1Labels := by
      have ha : raw34373step1 = -raw34373step0 := by apply Matrix.ext; change ∀ i j, raw34373step1 i j = -(raw34373step0 i j); unfold raw34373step1 raw34373step0; decide +kernel
      have hl : raw34373step1Labels = raw34373step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34373step1 raw34373step1Labels = mixedMoment B raw34373step2 raw34373step2Labels := by
      have ha : raw34373step2 = raw34373step1 := by apply Matrix.ext; unfold raw34373step2 raw34373step1; decide +kernel
      have hl : raw34373step1Labels = labelEmbedding10 ∘ raw34373step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34373step1 raw34373step1Labels raw34373step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

theorem canonical34374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34374 raw34374Labels = mixedMoment B node5058 node5058Labels := by
  calc
    mixedMoment B raw34374 raw34374Labels = mixedMoment B raw34374step0 raw34374step0Labels := by
      have ha : raw34374step0 = (fun i j => raw34374 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34374step0 raw34374; decide +kernel
      have hl : raw34374step0Labels = raw34374Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34374 raw34374Labels permutation176 permutation7
    mixedMoment B raw34374step0 raw34374step0Labels = mixedMoment B raw34374step1 raw34374step1Labels := by
      have ha : raw34374step1 = -raw34374step0 := by apply Matrix.ext; change ∀ i j, raw34374step1 i j = -(raw34374step0 i j); unfold raw34374step1 raw34374step0; decide +kernel
      have hl : raw34374step1Labels = raw34374step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34374step1 raw34374step1Labels = mixedMoment B raw34374step2 raw34374step2Labels := by
      have ha : raw34374step2 = raw34374step1 := by apply Matrix.ext; unfold raw34374step2 raw34374step1; decide +kernel
      have hl : raw34374step1Labels = labelEmbedding10 ∘ raw34374step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34374step1 raw34374step1Labels raw34374step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5058 node5058Labels := by rfl

theorem canonical34375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34375 raw34375Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw34375 raw34375Labels = mixedMoment B raw34375step0 raw34375step0Labels := by
      have ha : raw34375step0 = (fun i j => raw34375 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34375step0 raw34375; decide +kernel
      have hl : raw34375step0Labels = raw34375Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34375 raw34375Labels permutation176 permutation7
    mixedMoment B raw34375step0 raw34375step0Labels = mixedMoment B raw34375step1 raw34375step1Labels := by
      have ha : raw34375step1 = -raw34375step0 := by apply Matrix.ext; change ∀ i j, raw34375step1 i j = -(raw34375step0 i j); unfold raw34375step1 raw34375step0; decide +kernel
      have hl : raw34375step1Labels = raw34375step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34375step1 raw34375step1Labels = mixedMoment B raw34375step2 raw34375step2Labels := by
      have ha : raw34375step2 = raw34375step1 := by apply Matrix.ext; unfold raw34375step2 raw34375step1; decide +kernel
      have hl : raw34375step1Labels = labelEmbedding10 ∘ raw34375step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34375step1 raw34375step1Labels raw34375step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

theorem canonical34376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34376 raw34376Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw34376 raw34376Labels = mixedMoment B raw34376step0 raw34376step0Labels := by
      have ha : raw34376step0 = (fun i j => raw34376 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34376step0 raw34376; decide +kernel
      have hl : raw34376step0Labels = raw34376Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34376 raw34376Labels permutation178 permutation7
    mixedMoment B raw34376step0 raw34376step0Labels = mixedMoment B raw34376step1 raw34376step1Labels := by
      have ha : raw34376step1 = -raw34376step0 := by apply Matrix.ext; change ∀ i j, raw34376step1 i j = -(raw34376step0 i j); unfold raw34376step1 raw34376step0; decide +kernel
      have hl : raw34376step1Labels = raw34376step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34376step1 raw34376step1Labels = mixedMoment B raw34376step2 raw34376step2Labels := by
      have ha : raw34376step2 = raw34376step1 := by apply Matrix.ext; unfold raw34376step2 raw34376step1; decide +kernel
      have hl : raw34376step1Labels = labelEmbedding10 ∘ raw34376step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34376step1 raw34376step1Labels raw34376step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

theorem canonical34377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34377 raw34377Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw34377 raw34377Labels = mixedMoment B raw34377step0 raw34377step0Labels := by
      have ha : raw34377step0 = (fun i j => raw34377 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34377step0 raw34377; decide +kernel
      have hl : raw34377step0Labels = raw34377Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34377 raw34377Labels permutation176 permutation7
    mixedMoment B raw34377step0 raw34377step0Labels = mixedMoment B raw34377step1 raw34377step1Labels := by
      have ha : raw34377step1 = -raw34377step0 := by apply Matrix.ext; change ∀ i j, raw34377step1 i j = -(raw34377step0 i j); unfold raw34377step1 raw34377step0; decide +kernel
      have hl : raw34377step1Labels = raw34377step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34377step1 raw34377step1Labels = mixedMoment B raw34377step2 raw34377step2Labels := by
      have ha : raw34377step2 = raw34377step1 := by apply Matrix.ext; unfold raw34377step2 raw34377step1; decide +kernel
      have hl : raw34377step1Labels = labelEmbedding10 ∘ raw34377step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34377step1 raw34377step1Labels raw34377step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5137 node5137Labels := by rfl

theorem canonical34378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34378 raw34378Labels = mixedMoment B node4423 node4423Labels := by
  calc
    mixedMoment B raw34378 raw34378Labels = mixedMoment B raw34378step0 raw34378step0Labels := by
      have hz : ∀ j, raw34378 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw34378step0 = (fun i j => raw34378 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw34378step0 raw34378; decide +kernel
      have hl : raw34378step0Labels = raw34378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34378 raw34378Labels permutation265 hz
    _ = mixedMoment B node4423 node4423Labels := by rfl

theorem canonical34379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34379 raw34379Labels = mixedMoment B node4672 node4672Labels := by
  calc
    _ = mixedMoment B node4672 node4672Labels := by rfl

theorem canonical34380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34380 raw34380Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw34380 raw34380Labels = mixedMoment B raw34380step0 raw34380step0Labels := by
      have ha : raw34380step0 = (fun i j => raw34380 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34380step0 raw34380; decide +kernel
      have hl : raw34380step0Labels = raw34380Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34380 raw34380Labels permutation158 permutation2
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical34381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34381 raw34381Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw34381 raw34381Labels = mixedMoment B raw34381step0 raw34381step0Labels := by
      have ha : raw34381step0 = (fun i j => raw34381 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34381step0 raw34381; decide +kernel
      have hl : raw34381step0Labels = raw34381Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34381 raw34381Labels permutation164 permutation2
    _ = mixedMoment B node4798 node4798Labels := by rfl

theorem canonical34382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34382 raw34382Labels = mixedMoment B node4826 node4826Labels := by
  calc
    _ = mixedMoment B node4826 node4826Labels := by rfl

theorem canonical34383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34383 raw34383Labels = mixedMoment B node4661 node4661Labels := by
  calc
    mixedMoment B raw34383 raw34383Labels = mixedMoment B raw34383step0 raw34383step0Labels := by
      have ha : raw34383step0 = (fun i j => raw34383 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34383step0 raw34383; decide +kernel
      have hl : raw34383step0Labels = raw34383Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34383 raw34383Labels permutation154 permutation2
    _ = mixedMoment B node4661 node4661Labels := by rfl

theorem canonical34384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34384 raw34384Labels = mixedMoment B node4715 node4715Labels := by
  calc
    mixedMoment B raw34384 raw34384Labels = mixedMoment B raw34384step0 raw34384step0Labels := by
      have ha : raw34384step0 = (fun i j => raw34384 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34384step0 raw34384; decide +kernel
      have hl : raw34384step0Labels = raw34384Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34384 raw34384Labels permutation178 permutation2
    _ = mixedMoment B node4715 node4715Labels := by rfl

theorem canonical34385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34385 raw34385Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw34385 raw34385Labels = mixedMoment B raw34385step0 raw34385step0Labels := by
      have ha : raw34385step0 = (fun i j => raw34385 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34385step0 raw34385; decide +kernel
      have hl : raw34385step0Labels = raw34385Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34385 raw34385Labels permutation154 permutation2
    _ = mixedMoment B node4782 node4782Labels := by rfl

theorem canonical34386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34386 raw34386Labels = mixedMoment B node4787 node4787Labels := by
  calc
    mixedMoment B raw34386 raw34386Labels = mixedMoment B raw34386step0 raw34386step0Labels := by
      have ha : raw34386step0 = (fun i j => raw34386 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34386step0 raw34386; decide +kernel
      have hl : raw34386step0Labels = raw34386Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34386 raw34386Labels permutation155 permutation2
    _ = mixedMoment B node4787 node4787Labels := by rfl

theorem canonical34387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34387 raw34387Labels = mixedMoment B node4661 node4661Labels := by
  calc
    _ = mixedMoment B node4661 node4661Labels := by rfl

theorem canonical34388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34388 raw34388Labels = mixedMoment B node4715 node4715Labels := by
  calc
    mixedMoment B raw34388 raw34388Labels = mixedMoment B raw34388step0 raw34388step0Labels := by
      have ha : raw34388step0 = (fun i j => raw34388 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34388step0 raw34388; decide +kernel
      have hl : raw34388step0Labels = raw34388Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34388 raw34388Labels permutation176 permutation2
    _ = mixedMoment B node4715 node4715Labels := by rfl

theorem canonical34389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34389 raw34389Labels = mixedMoment B node4782 node4782Labels := by
  calc
    _ = mixedMoment B node4782 node4782Labels := by rfl

theorem canonical34390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34390 raw34390Labels = mixedMoment B node4787 node4787Labels := by
  calc
    mixedMoment B raw34390 raw34390Labels = mixedMoment B raw34390step0 raw34390step0Labels := by
      have ha : raw34390step0 = (fun i j => raw34390 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34390step0 raw34390; decide +kernel
      have hl : raw34390step0Labels = raw34390Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34390 raw34390Labels permutation153 permutation2
    _ = mixedMoment B node4787 node4787Labels := by rfl

theorem canonical34391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34391 raw34391Labels = mixedMoment B node4660 node4660Labels := by
  calc
    _ = mixedMoment B node4660 node4660Labels := by rfl

theorem canonical34392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34392 raw34392Labels = mixedMoment B node4712 node4712Labels := by
  calc
    mixedMoment B raw34392 raw34392Labels = mixedMoment B raw34392step0 raw34392step0Labels := by
      have ha : raw34392step0 = (fun i j => raw34392 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34392step0 raw34392; decide +kernel
      have hl : raw34392step0Labels = raw34392Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34392 raw34392Labels permutation176 permutation2
    _ = mixedMoment B node4712 node4712Labels := by rfl

theorem canonical34393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34393 raw34393Labels = mixedMoment B node4779 node4779Labels := by
  calc
    _ = mixedMoment B node4779 node4779Labels := by rfl

theorem canonical34394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34394 raw34394Labels = mixedMoment B node4779 node4779Labels := by
  calc
    mixedMoment B raw34394 raw34394Labels = mixedMoment B raw34394step0 raw34394step0Labels := by
      have ha : raw34394step0 = (fun i j => raw34394 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34394step0 raw34394; decide +kernel
      have hl : raw34394step0Labels = raw34394Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34394 raw34394Labels permutation154 permutation2
    _ = mixedMoment B node4779 node4779Labels := by rfl

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

theorem canonical1101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1101 raw1101Labels = mixedMoment B node4322 node4322Labels := by
  calc
    mixedMoment B raw1101 raw1101Labels = mixedMoment B raw1101step0 raw1101step0Labels := by
      have ha : raw1101step0 = (fun i j => raw1101 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1101step0 raw1101; decide +kernel
      have hl : raw1101step0Labels = raw1101Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1101 raw1101Labels permutation152 permutation4
    mixedMoment B raw1101step0 raw1101step0Labels = mixedMoment B raw1101step1 raw1101step1Labels := by
      have ha : raw1101step1 = raw1101step0 := by apply Matrix.ext; unfold raw1101step1 raw1101step0; decide +kernel
      have hl : raw1101step0Labels = labelEmbedding7 ∘ raw1101step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1101step0 raw1101step0Labels raw1101step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4322 node4322Labels := by rfl

theorem canonical1102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1102 raw1102Labels = mixedMoment B node900 node900Labels := by
  calc
    mixedMoment B raw1102 raw1102Labels = mixedMoment B raw1102step0 raw1102step0Labels := by
      have ha : raw1102step0 = (fun i j => raw1102 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1102step0 raw1102; decide +kernel
      have hl : raw1102step0Labels = raw1102Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1102 raw1102Labels permutation152 permutation4
    _ = mixedMoment B node900 node900Labels := by rfl

theorem canonical1103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1103 raw1103Labels = mixedMoment B node1588 node1588Labels := by
  calc
    mixedMoment B raw1103 raw1103Labels = mixedMoment B raw1103step0 raw1103step0Labels := by
      have ha : raw1103step0 = (fun i j => raw1103 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1103step0 raw1103; decide +kernel
      have hl : raw1103step0Labels = raw1103Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1103 raw1103Labels permutation176 permutation6
    mixedMoment B raw1103step0 raw1103step0Labels = mixedMoment B raw1103step1 raw1103step1Labels := by
      have ha : raw1103step1 = -raw1103step0 := by apply Matrix.ext; change ∀ i j, raw1103step1 i j = -(raw1103step0 i j); unfold raw1103step1 raw1103step0; decide +kernel
      have hl : raw1103step1Labels = raw1103step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1103step1 raw1103step1Labels = mixedMoment B raw1103step2 raw1103step2Labels := by
      have ha : raw1103step2 = raw1103step1 := by apply Matrix.ext; unfold raw1103step2 raw1103step1; decide +kernel
      have hl : raw1103step1Labels = labelEmbedding1 ∘ raw1103step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1103step1 raw1103step1Labels raw1103step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1588 node1588Labels := by rfl

theorem canonical1104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1104 raw1104Labels = mixedMoment B node4323 node4323Labels := by
  calc
    mixedMoment B raw1104 raw1104Labels = mixedMoment B raw1104step0 raw1104step0Labels := by
      have ha : raw1104step0 = (fun i j => raw1104 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1104step0 raw1104; decide +kernel
      have hl : raw1104step0Labels = raw1104Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1104 raw1104Labels permutation152 permutation4
    mixedMoment B raw1104step0 raw1104step0Labels = mixedMoment B raw1104step1 raw1104step1Labels := by
      have ha : raw1104step1 = raw1104step0 := by apply Matrix.ext; unfold raw1104step1 raw1104step0; decide +kernel
      have hl : raw1104step0Labels = labelEmbedding7 ∘ raw1104step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1104step0 raw1104step0Labels raw1104step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4323 node4323Labels := by rfl

theorem canonical1105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1105 raw1105Labels = mixedMoment B node901 node901Labels := by
  calc
    mixedMoment B raw1105 raw1105Labels = mixedMoment B raw1105step0 raw1105step0Labels := by
      have ha : raw1105step0 = (fun i j => raw1105 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1105step0 raw1105; decide +kernel
      have hl : raw1105step0Labels = raw1105Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1105 raw1105Labels permutation152 permutation4
    _ = mixedMoment B node901 node901Labels := by rfl

theorem canonical1106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1106 raw1106Labels = mixedMoment B node1589 node1589Labels := by
  calc
    mixedMoment B raw1106 raw1106Labels = mixedMoment B raw1106step0 raw1106step0Labels := by
      have ha : raw1106step0 = (fun i j => raw1106 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1106step0 raw1106; decide +kernel
      have hl : raw1106step0Labels = raw1106Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1106 raw1106Labels permutation176 permutation6
    mixedMoment B raw1106step0 raw1106step0Labels = mixedMoment B raw1106step1 raw1106step1Labels := by
      have ha : raw1106step1 = -raw1106step0 := by apply Matrix.ext; change ∀ i j, raw1106step1 i j = -(raw1106step0 i j); unfold raw1106step1 raw1106step0; decide +kernel
      have hl : raw1106step1Labels = raw1106step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1106step1 raw1106step1Labels = mixedMoment B raw1106step2 raw1106step2Labels := by
      have ha : raw1106step2 = raw1106step1 := by apply Matrix.ext; unfold raw1106step2 raw1106step1; decide +kernel
      have hl : raw1106step1Labels = labelEmbedding1 ∘ raw1106step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1106step1 raw1106step1Labels raw1106step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1589 node1589Labels := by rfl

theorem canonical1113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1113 raw1113Labels = mixedMoment B node4337 node4337Labels := by
  calc
    mixedMoment B raw1113 raw1113Labels = mixedMoment B raw1113step0 raw1113step0Labels := by
      have ha : raw1113step0 = (fun i j => raw1113 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1113step0 raw1113; decide +kernel
      have hl : raw1113step0Labels = raw1113Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1113 raw1113Labels permutation152 permutation4
    mixedMoment B raw1113step0 raw1113step0Labels = mixedMoment B raw1113step1 raw1113step1Labels := by
      have ha : raw1113step1 = raw1113step0 := by apply Matrix.ext; unfold raw1113step1 raw1113step0; decide +kernel
      have hl : raw1113step0Labels = labelEmbedding7 ∘ raw1113step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1113step0 raw1113step0Labels raw1113step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4337 node4337Labels := by rfl

theorem canonical1114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1114 raw1114Labels = mixedMoment B node915 node915Labels := by
  calc
    mixedMoment B raw1114 raw1114Labels = mixedMoment B raw1114step0 raw1114step0Labels := by
      have ha : raw1114step0 = (fun i j => raw1114 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1114step0 raw1114; decide +kernel
      have hl : raw1114step0Labels = raw1114Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1114 raw1114Labels permutation152 permutation4
    _ = mixedMoment B node915 node915Labels := by rfl

theorem canonical1115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1115 raw1115Labels = mixedMoment B node1632 node1632Labels := by
  calc
    mixedMoment B raw1115 raw1115Labels = mixedMoment B raw1115step0 raw1115step0Labels := by
      have ha : raw1115step0 = (fun i j => raw1115 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1115step0 raw1115; decide +kernel
      have hl : raw1115step0Labels = raw1115Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1115 raw1115Labels permutation176 permutation6
    mixedMoment B raw1115step0 raw1115step0Labels = mixedMoment B raw1115step1 raw1115step1Labels := by
      have ha : raw1115step1 = -raw1115step0 := by apply Matrix.ext; change ∀ i j, raw1115step1 i j = -(raw1115step0 i j); unfold raw1115step1 raw1115step0; decide +kernel
      have hl : raw1115step1Labels = raw1115step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1115step1 raw1115step1Labels = mixedMoment B raw1115step2 raw1115step2Labels := by
      have ha : raw1115step2 = raw1115step1 := by apply Matrix.ext; unfold raw1115step2 raw1115step1; decide +kernel
      have hl : raw1115step1Labels = labelEmbedding1 ∘ raw1115step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1115step1 raw1115step1Labels raw1115step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1632 node1632Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4322 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4322 node4322Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node900 node900Labels + mixedMoment B node1588 node1588Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1101 singletonSmall4322
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4322) = raw1101Labels := by decide +kernel
  rw [hl, canonical1101 B hB] at h
  have hc0 : mixedMoment B raw1101 (Fin.cases (0 : Fin 2) singletonSmall4322) =
      mixedMoment B node900 node900Labels := by
    have ha : raw1101 = raw1102 := by apply Matrix.ext; unfold raw1101 raw1102; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4322 = raw1102Labels := by decide +kernel
    rw [ha, hj, canonical1102 B hB]
  have hc1 : mixedMoment B raw1101 (Fin.cases (1 : Fin 2) singletonSmall4322) =
      mixedMoment B node1588 node1588Labels := by
    have ha : raw1101 = raw1103 := by apply Matrix.ext; unfold raw1101 raw1103; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4322 = raw1103Labels := by decide +kernel
    rw [ha, hj, canonical1103 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4323 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4323 node4323Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node901 node901Labels + mixedMoment B node1589 node1589Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1104 singletonSmall4323
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4323) = raw1104Labels := by decide +kernel
  rw [hl, canonical1104 B hB] at h
  have hc0 : mixedMoment B raw1104 (Fin.cases (0 : Fin 2) singletonSmall4323) =
      mixedMoment B node901 node901Labels := by
    have ha : raw1104 = raw1105 := by apply Matrix.ext; unfold raw1104 raw1105; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4323 = raw1105Labels := by decide +kernel
    rw [ha, hj, canonical1105 B hB]
  have hc1 : mixedMoment B raw1104 (Fin.cases (1 : Fin 2) singletonSmall4323) =
      mixedMoment B node1589 node1589Labels := by
    have ha : raw1104 = raw1106 := by apply Matrix.ext; unfold raw1104 raw1106; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4323 = raw1106Labels := by decide +kernel
    rw [ha, hj, canonical1106 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4337 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4337 node4337Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node915 node915Labels + mixedMoment B node1632 node1632Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1113 singletonSmall4337
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4337) = raw1113Labels := by decide +kernel
  rw [hl, canonical1113 B hB] at h
  have hc0 : mixedMoment B raw1113 (Fin.cases (0 : Fin 2) singletonSmall4337) =
      mixedMoment B node915 node915Labels := by
    have ha : raw1113 = raw1114 := by apply Matrix.ext; unfold raw1113 raw1114; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4337 = raw1114Labels := by decide +kernel
    rw [ha, hj, canonical1114 B hB]
  have hc1 : mixedMoment B raw1113 (Fin.cases (1 : Fin 2) singletonSmall4337) =
      mixedMoment B node1632 node1632Labels := by
    have ha : raw1113 = raw1115 := by apply Matrix.ext; unfold raw1113 raw1115; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4337 = raw1115Labels := by decide +kernel
    rw [ha, hj, canonical1115 B hB]
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

theorem singleton4660 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4660 node4660Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1786 node1786Labels + mixedMoment B node1982 node1982Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1536 singletonSmall4660
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4660) = raw1536Labels := by decide +kernel
  rw [hl, canonical1536 B hB] at h
  have hc0 : mixedMoment B raw1536 (Fin.cases (0 : Fin 2) singletonSmall4660) =
      mixedMoment B node1786 node1786Labels := by
    have ha : raw1536 = raw1537 := by apply Matrix.ext; unfold raw1536 raw1537; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4660 = raw1537Labels := by decide +kernel
    rw [ha, hj, canonical1537 B hB]
  have hc1 : mixedMoment B raw1536 (Fin.cases (1 : Fin 2) singletonSmall4660) =
      mixedMoment B node1982 node1982Labels := by
    have ha : raw1536 = raw1538 := by apply Matrix.ext; unfold raw1536 raw1538; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4660 = raw1538Labels := by decide +kernel
    rw [ha, hj, canonical1538 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4661 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4661 node4661Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1787 node1787Labels + mixedMoment B node1983 node1983Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1539 singletonSmall4661
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4661) = raw1539Labels := by decide +kernel
  rw [hl, canonical1539 B hB] at h
  have hc0 : mixedMoment B raw1539 (Fin.cases (0 : Fin 2) singletonSmall4661) =
      mixedMoment B node1787 node1787Labels := by
    have ha : raw1539 = raw1540 := by apply Matrix.ext; unfold raw1539 raw1540; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4661 = raw1540Labels := by decide +kernel
    rw [ha, hj, canonical1540 B hB]
  have hc1 : mixedMoment B raw1539 (Fin.cases (1 : Fin 2) singletonSmall4661) =
      mixedMoment B node1983 node1983Labels := by
    have ha : raw1539 = raw1541 := by apply Matrix.ext; unfold raw1539 raw1541; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4661 = raw1541Labels := by decide +kernel
    rw [ha, hj, canonical1541 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4672 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4672 node4672Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1798 node1798Labels + mixedMoment B node2067 node2067Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1545 singletonSmall4672
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4672) = raw1545Labels := by decide +kernel
  rw [hl, canonical1545 B hB] at h
  have hc0 : mixedMoment B raw1545 (Fin.cases (0 : Fin 2) singletonSmall4672) =
      mixedMoment B node1798 node1798Labels := by
    have ha : raw1545 = raw1546 := by apply Matrix.ext; unfold raw1545 raw1546; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4672 = raw1546Labels := by decide +kernel
    rw [ha, hj, canonical1546 B hB]
  have hc1 : mixedMoment B raw1545 (Fin.cases (1 : Fin 2) singletonSmall4672) =
      mixedMoment B node2067 node2067Labels := by
    have ha : raw1545 = raw1547 := by apply Matrix.ext; unfold raw1545 raw1547; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4672 = raw1547Labels := by decide +kernel
    rw [ha, hj, canonical1547 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4779 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4779 node4779Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1987 node1987Labels + mixedMoment B node1996 node1996Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1713 singletonSmall4779
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4779) = raw1713Labels := by decide +kernel
  rw [hl, canonical1713 B hB] at h
  have hc0 : mixedMoment B raw1713 (Fin.cases (0 : Fin 2) singletonSmall4779) =
      mixedMoment B node1987 node1987Labels := by
    have ha : raw1713 = raw1714 := by apply Matrix.ext; unfold raw1713 raw1714; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4779 = raw1714Labels := by decide +kernel
    rw [ha, hj, canonical1714 B hB]
  have hc1 : mixedMoment B raw1713 (Fin.cases (1 : Fin 2) singletonSmall4779) =
      mixedMoment B node1996 node1996Labels := by
    have ha : raw1713 = raw1715 := by apply Matrix.ext; unfold raw1713 raw1715; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4779 = raw1715Labels := by decide +kernel
    rw [ha, hj, canonical1715 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4782 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4782 node4782Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1990 node1990Labels + mixedMoment B node1997 node1997Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1716 singletonSmall4782
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4782) = raw1716Labels := by decide +kernel
  rw [hl, canonical1716 B hB] at h
  have hc0 : mixedMoment B raw1716 (Fin.cases (0 : Fin 2) singletonSmall4782) =
      mixedMoment B node1990 node1990Labels := by
    have ha : raw1716 = raw1717 := by apply Matrix.ext; unfold raw1716 raw1717; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4782 = raw1717Labels := by decide +kernel
    rw [ha, hj, canonical1717 B hB]
  have hc1 : mixedMoment B raw1716 (Fin.cases (1 : Fin 2) singletonSmall4782) =
      mixedMoment B node1997 node1997Labels := by
    have ha : raw1716 = raw1718 := by apply Matrix.ext; unfold raw1716 raw1718; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4782 = raw1718Labels := by decide +kernel
    rw [ha, hj, canonical1718 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4787 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4787 node4787Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2000 node2000Labels + mixedMoment B node2000 node2000Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1719 singletonSmall4787
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4787) = raw1719Labels := by decide +kernel
  rw [hl, canonical1719 B hB] at h
  have hc0 : mixedMoment B raw1719 (Fin.cases (0 : Fin 2) singletonSmall4787) =
      mixedMoment B node2000 node2000Labels := by
    have ha : raw1719 = raw1720 := by apply Matrix.ext; unfold raw1719 raw1720; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4787 = raw1720Labels := by decide +kernel
    rw [ha, hj, canonical1720 B hB]
  have hc1 : mixedMoment B raw1719 (Fin.cases (1 : Fin 2) singletonSmall4787) =
      mixedMoment B node2000 node2000Labels := by
    have ha : raw1719 = raw1721 := by apply Matrix.ext; unfold raw1719 raw1721; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4787 = raw1721Labels := by decide +kernel
    rw [ha, hj, canonical1721 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4798 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4798 node4798Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2016 node2016Labels + mixedMoment B node2075 node2075Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1725 singletonSmall4798
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4798) = raw1725Labels := by decide +kernel
  rw [hl, canonical1725 B hB] at h
  have hc0 : mixedMoment B raw1725 (Fin.cases (0 : Fin 2) singletonSmall4798) =
      mixedMoment B node2016 node2016Labels := by
    have ha : raw1725 = raw1726 := by apply Matrix.ext; unfold raw1725 raw1726; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4798 = raw1726Labels := by decide +kernel
    rw [ha, hj, canonical1726 B hB]
  have hc1 : mixedMoment B raw1725 (Fin.cases (1 : Fin 2) singletonSmall4798) =
      mixedMoment B node2075 node2075Labels := by
    have ha : raw1725 = raw1727 := by apply Matrix.ext; unfold raw1725 raw1727; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4798 = raw1727Labels := by decide +kernel
    rw [ha, hj, canonical1727 B hB]
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

theorem singleton4826 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4826 node4826Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2046 node2046Labels + mixedMoment B node2077 node2077Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1752 singletonSmall4826
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4826) = raw1752Labels := by decide +kernel
  rw [hl, canonical1752 B hB] at h
  have hc0 : mixedMoment B raw1752 (Fin.cases (0 : Fin 2) singletonSmall4826) =
      mixedMoment B node2046 node2046Labels := by
    have ha : raw1752 = raw1753 := by apply Matrix.ext; unfold raw1752 raw1753; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4826 = raw1753Labels := by decide +kernel
    rw [ha, hj, canonical1753 B hB]
  have hc1 : mixedMoment B raw1752 (Fin.cases (1 : Fin 2) singletonSmall4826) =
      mixedMoment B node2077 node2077Labels := by
    have ha : raw1752 = raw1754 := by apply Matrix.ext; unfold raw1752 raw1754; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4826 = raw1754Labels := by decide +kernel
    rw [ha, hj, canonical1754 B hB]
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

theorem singleton5123 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5123 node5123Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2536 node2536Labels + mixedMoment B node3370 node3370Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2154 singletonSmall5123
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5123) = raw2154Labels := by decide +kernel
  rw [hl, canonical2154 B hB] at h
  have hc0 : mixedMoment B raw2154 (Fin.cases (0 : Fin 2) singletonSmall5123) =
      mixedMoment B node2536 node2536Labels := by
    have ha : raw2154 = raw2155 := by apply Matrix.ext; unfold raw2154 raw2155; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5123 = raw2155Labels := by decide +kernel
    rw [ha, hj, canonical2155 B hB]
  have hc1 : mixedMoment B raw2154 (Fin.cases (1 : Fin 2) singletonSmall5123) =
      mixedMoment B node3370 node3370Labels := by
    have ha : raw2154 = raw2156 := by apply Matrix.ext; unfold raw2154 raw2156; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5123 = raw2156Labels := by decide +kernel
    rw [ha, hj, canonical2156 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5134 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5134 node5134Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2553 node2553Labels + mixedMoment B node3514 node3514Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2163 singletonSmall5134
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5134) = raw2163Labels := by decide +kernel
  rw [hl, canonical2163 B hB] at h
  have hc0 : mixedMoment B raw2163 (Fin.cases (0 : Fin 2) singletonSmall5134) =
      mixedMoment B node2553 node2553Labels := by
    have ha : raw2163 = raw2164 := by apply Matrix.ext; unfold raw2163 raw2164; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5134 = raw2164Labels := by decide +kernel
    rw [ha, hj, canonical2164 B hB]
  have hc1 : mixedMoment B raw2163 (Fin.cases (1 : Fin 2) singletonSmall5134) =
      mixedMoment B node3514 node3514Labels := by
    have ha : raw2163 = raw2165 := by apply Matrix.ext; unfold raw2163 raw2165; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5134 = raw2165Labels := by decide +kernel
    rw [ha, hj, canonical2165 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node900 node900Labels = Sparse.eval nodeValue900 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 900) = mixedMoment B node900 node900Labels := rfl
  simpa [nodeValue900, Sparse.eval] using hc.symm

theorem sound901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node901 node901Labels = Sparse.eval nodeValue901 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 901) = mixedMoment B node901 node901Labels := rfl
  simpa [nodeValue901, Sparse.eval] using hc.symm

theorem sound915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node915 node915Labels = Sparse.eval nodeValue915 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 915) = mixedMoment B node915 node915Labels := rfl
  simpa [nodeValue915, Sparse.eval] using hc.symm

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

theorem sound1588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1588 node1588Labels = Sparse.eval nodeValue1588 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1588) = mixedMoment B node1588 node1588Labels := rfl
  simpa [nodeValue1588, Sparse.eval] using hc.symm

theorem sound1589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1589 node1589Labels = Sparse.eval nodeValue1589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1589) = mixedMoment B node1589 node1589Labels := rfl
  simpa [nodeValue1589, Sparse.eval] using hc.symm

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

theorem sound1632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1632 node1632Labels = Sparse.eval nodeValue1632 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1632) = mixedMoment B node1632 node1632Labels := rfl
  simpa [nodeValue1632, Sparse.eval] using hc.symm

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

theorem sound1786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1786 node1786Labels = Sparse.eval nodeValue1786 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1786) = mixedMoment B node1786 node1786Labels := rfl
  simpa [nodeValue1786, Sparse.eval] using hc.symm

theorem sound1787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1787 node1787Labels = Sparse.eval nodeValue1787 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1787) = mixedMoment B node1787 node1787Labels := rfl
  simpa [nodeValue1787, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1798 node1798Labels = Sparse.eval nodeValue1798 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1798) = mixedMoment B node1798 node1798Labels := rfl
  simpa [nodeValue1798, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1982 node1982Labels = Sparse.eval nodeValue1982 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1982) = mixedMoment B node1982 node1982Labels := rfl
  simpa [nodeValue1982, Sparse.eval] using hc.symm

theorem sound1983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1983 node1983Labels = Sparse.eval nodeValue1983 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1983) = mixedMoment B node1983 node1983Labels := rfl
  simpa [nodeValue1983, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1987 node1987Labels = Sparse.eval nodeValue1987 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1987) = mixedMoment B node1987 node1987Labels := rfl
  simpa [nodeValue1987, Sparse.eval] using hc.symm

theorem sound1990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1990 node1990Labels = Sparse.eval nodeValue1990 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1990) = mixedMoment B node1990 node1990Labels := rfl
  simpa [nodeValue1990, Sparse.eval] using hc.symm

theorem sound1996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1996 node1996Labels = Sparse.eval nodeValue1996 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1996) = mixedMoment B node1996 node1996Labels := rfl
  simpa [nodeValue1996, Sparse.eval] using hc.symm

theorem sound1997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1997 node1997Labels = Sparse.eval nodeValue1997 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1997) = mixedMoment B node1997 node1997Labels := rfl
  simpa [nodeValue1997, Sparse.eval] using hc.symm

theorem sound2000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2000 node2000Labels = Sparse.eval nodeValue2000 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2000) = mixedMoment B node2000 node2000Labels := rfl
  simpa [nodeValue2000, Sparse.eval] using hc.symm

theorem sound2016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2016 node2016Labels = Sparse.eval nodeValue2016 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2016) = mixedMoment B node2016 node2016Labels := rfl
  simpa [nodeValue2016, Sparse.eval] using hc.symm

theorem sound2046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2046 node2046Labels = Sparse.eval nodeValue2046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2046) = mixedMoment B node2046 node2046Labels := rfl
  simpa [nodeValue2046, Sparse.eval] using hc.symm

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

theorem sound2067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2067 node2067Labels = Sparse.eval nodeValue2067 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2067) = mixedMoment B node2067 node2067Labels := rfl
  simpa [nodeValue2067, Sparse.eval] using hc.symm

theorem sound2075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2075 node2075Labels = Sparse.eval nodeValue2075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2075) = mixedMoment B node2075 node2075Labels := rfl
  simpa [nodeValue2075, Sparse.eval] using hc.symm

theorem sound2077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2077 node2077Labels = Sparse.eval nodeValue2077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2077) = mixedMoment B node2077 node2077Labels := rfl
  simpa [nodeValue2077, Sparse.eval] using hc.symm

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

theorem sound2536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2536 node2536Labels = Sparse.eval nodeValue2536 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2536) = mixedMoment B node2536 node2536Labels := rfl
  simpa [nodeValue2536, Sparse.eval] using hc.symm

theorem sound2553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2553 node2553Labels = Sparse.eval nodeValue2553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2553) = mixedMoment B node2553 node2553Labels := rfl
  simpa [nodeValue2553, Sparse.eval] using hc.symm

theorem sound2556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2556 node2556Labels = Sparse.eval nodeValue2556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2556) = mixedMoment B node2556 node2556Labels := rfl
  simpa [nodeValue2556, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3370 node3370Labels = Sparse.eval nodeValue3370 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3370) = mixedMoment B node3370 node3370Labels := rfl
  simpa [nodeValue3370, Sparse.eval] using hc.symm

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

theorem sound3514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3514 node3514Labels = Sparse.eval nodeValue3514 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3514) = mixedMoment B node3514 node3514Labels := rfl
  simpa [nodeValue3514, Sparse.eval] using hc.symm

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

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

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

theorem sound4322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4322 node4322Labels = Sparse.eval nodeValue4322 (mixedVector B) := by
  have h := singleton4322 B _hB
  rw [sound900 B _hB _hF, sound1588 B _hB _hF] at h
  norm_num [nodeValue4322, nodeValue900, nodeValue1588, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4323 node4323Labels = Sparse.eval nodeValue4323 (mixedVector B) := by
  have h := singleton4323 B _hB
  rw [sound901 B _hB _hF, sound1589 B _hB _hF] at h
  norm_num [nodeValue4323, nodeValue901, nodeValue1589, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4337 node4337Labels = Sparse.eval nodeValue4337 (mixedVector B) := by
  have h := singleton4337 B _hB
  rw [sound915 B _hB _hF, sound1632 B _hB _hF] at h
  norm_num [nodeValue4337, nodeValue915, nodeValue1632, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4423 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4423 node4423Labels = 0 := by
  exact mixedMoment_order_one B hB node4423 node4423Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4423 node4423Labels = Sparse.eval nodeValue4423 (mixedVector B) := by
  simpa only [nodeValue4423, Sparse.eval_nil] using zero4423 B _hB _hF

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

theorem sound4660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4660 node4660Labels = Sparse.eval nodeValue4660 (mixedVector B) := by
  have h := singleton4660 B _hB
  rw [sound1786 B _hB _hF, sound1982 B _hB _hF] at h
  norm_num [nodeValue4660, nodeValue1786, nodeValue1982, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4661 node4661Labels = Sparse.eval nodeValue4661 (mixedVector B) := by
  have h := singleton4661 B _hB
  rw [sound1787 B _hB _hF, sound1983 B _hB _hF] at h
  norm_num [nodeValue4661, nodeValue1787, nodeValue1983, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4712 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4712 node4712Labels = 0 := by
  exact mixedMoment_order_one B hB node4712 node4712Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4715 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4715 node4715Labels = 0 := by
  exact mixedMoment_order_one B hB node4715 node4715Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4672 node4672Labels = Sparse.eval nodeValue4672 (mixedVector B) := by
  have h := singleton4672 B _hB
  rw [sound1798 B _hB _hF, sound2067 B _hB _hF] at h
  norm_num [nodeValue4672, nodeValue1798, nodeValue2067, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4712 node4712Labels = Sparse.eval nodeValue4712 (mixedVector B) := by
  simpa only [nodeValue4712, Sparse.eval_nil] using zero4712 B _hB _hF

theorem sound4715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4715 node4715Labels = Sparse.eval nodeValue4715 (mixedVector B) := by
  simpa only [nodeValue4715, Sparse.eval_nil] using zero4715 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4779 node4779Labels = Sparse.eval nodeValue4779 (mixedVector B) := by
  have h := singleton4779 B _hB
  rw [sound1987 B _hB _hF, sound1996 B _hB _hF] at h
  norm_num [nodeValue4779, nodeValue1987, nodeValue1996, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4782 node4782Labels = Sparse.eval nodeValue4782 (mixedVector B) := by
  have h := singleton4782 B _hB
  rw [sound1990 B _hB _hF, sound1997 B _hB _hF] at h
  norm_num [nodeValue4782, nodeValue1990, nodeValue1997, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4787 node4787Labels = Sparse.eval nodeValue4787 (mixedVector B) := by
  have h := singleton4787 B _hB
  rw [sound2000 B _hB _hF] at h
  norm_num [nodeValue4787, nodeValue2000, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4798 node4798Labels = Sparse.eval nodeValue4798 (mixedVector B) := by
  have h := singleton4798 B _hB
  rw [sound2016 B _hB _hF, sound2075 B _hB _hF] at h
  norm_num [nodeValue4798, nodeValue2016, nodeValue2075, Sparse.eval] at h ⊢
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

theorem zero4834 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4834 node4834Labels = 0 := by
  exact mixedMoment_order_one B hB node4834 node4834Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4838 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4838 node4838Labels = 0 := by
  exact mixedMoment_order_one B hB node4838 node4838Labels 1
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

theorem sound4826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4826 node4826Labels = Sparse.eval nodeValue4826 (mixedVector B) := by
  have h := singleton4826 B _hB
  rw [sound2046 B _hB _hF, sound2077 B _hB _hF] at h
  norm_num [nodeValue4826, nodeValue2046, nodeValue2077, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4834 node4834Labels = Sparse.eval nodeValue4834 (mixedVector B) := by
  simpa only [nodeValue4834, Sparse.eval_nil] using zero4834 B _hB _hF

theorem sound4838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4838 node4838Labels = Sparse.eval nodeValue4838 (mixedVector B) := by
  simpa only [nodeValue4838, Sparse.eval_nil] using zero4838 B _hB _hF

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

theorem zero5058 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5058 node5058Labels = 0 := by
  exact mixedMoment_order_one B hB node5058 node5058Labels 1
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

theorem sound5058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5058 node5058Labels = Sparse.eval nodeValue5058 (mixedVector B) := by
  simpa only [nodeValue5058, Sparse.eval_nil] using zero5058 B _hB _hF

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

theorem sound5123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5123 node5123Labels = Sparse.eval nodeValue5123 (mixedVector B) := by
  have h := singleton5123 B _hB
  rw [sound2536 B _hB _hF, sound3370 B _hB _hF] at h
  norm_num [nodeValue5123, nodeValue2536, nodeValue3370, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5134 node5134Labels = Sparse.eval nodeValue5134 (mixedVector B) := by
  have h := singleton5134 B _hB
  rw [sound2553 B _hB _hF, sound3514 B _hB _hF] at h
  norm_num [nodeValue5134, nodeValue2553, nodeValue3514, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5137 node5137Labels = Sparse.eval nodeValue5137 (mixedVector B) := by
  have h := singleton5137 B _hB
  rw [sound2556 B _hB _hF, sound3521 B _hB _hF] at h
  norm_num [nodeValue5137, nodeValue2556, nodeValue3521, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources77
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2494 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2494 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2494 + difference 0 1) (sourceB2494 + difference 1 0) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA2494 + difference 0 1) (sourceB2494 + difference 1 0) sourceC2494) = raw34373 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34373; decide +kernel
    rw [ha]
    exact (canonical34373 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2494 + difference 0 2) (sourceB2494 + difference 2 0) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5058) := by
    have ha : (tripleCharges (sourceA2494 + difference 0 2) (sourceB2494 + difference 2 0) sourceC2494) = raw34374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34374; decide +kernel
    rw [ha]
    exact (canonical34374 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2494 + difference 0 3) (sourceB2494 + difference 3 0) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2494 + difference 0 3) (sourceB2494 + difference 3 0) sourceC2494) = raw34375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34375; decide +kernel
    rw [ha]
    exact (canonical34375 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2494 + difference 0 4) (sourceB2494 + difference 4 0) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2494 + difference 0 4) (sourceB2494 + difference 4 0) sourceC2494) = raw34376 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34376; decide +kernel
    rw [ha]
    exact (canonical34376 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2494 + difference 0 5) (sourceB2494 + difference 5 0) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2494 + difference 0 5) (sourceB2494 + difference 5 0) sourceC2494) = raw34377 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34377; decide +kernel
    rw [ha]
    exact (canonical34377 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2494 + difference 1 0) (sourceB2494 + difference 0 1) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4423) := by
    have ha : (tripleCharges (sourceA2494 + difference 1 0) (sourceB2494 + difference 0 1) sourceC2494) = raw34378 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34378; decide +kernel
    rw [ha]
    exact (canonical34378 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2494 + difference 1 2) (sourceB2494 + difference 2 1) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2494 + difference 1 2) (sourceB2494 + difference 2 1) sourceC2494) = raw26136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw26136; decide +kernel
    rw [ha]
    exact (canonical26136 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2494 + difference 1 3) (sourceB2494 + difference 3 1) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2494 + difference 1 3) (sourceB2494 + difference 3 1) sourceC2494) = raw26137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw26137; decide +kernel
    rw [ha]
    exact (canonical26137 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2494 + difference 1 4) (sourceB2494 + difference 4 1) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2494 + difference 1 4) (sourceB2494 + difference 4 1) sourceC2494) = raw26138 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw26138; decide +kernel
    rw [ha]
    exact (canonical26138 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2494 + difference 1 5) (sourceB2494 + difference 5 1) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2494 + difference 1 5) (sourceB2494 + difference 5 1) sourceC2494) = raw26139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw26139; decide +kernel
    rw [ha]
    exact (canonical26139 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2494 + difference 2 0) (sourceB2494 + difference 0 2) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4337) := by
    have ha : (tripleCharges (sourceA2494 + difference 2 0) (sourceB2494 + difference 0 2) sourceC2494) = raw26146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw26146; decide +kernel
    rw [ha]
    exact (canonical26146 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2494 + difference 2 1) (sourceB2494 + difference 1 2) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4672) := by
    have ha : (tripleCharges (sourceA2494 + difference 2 1) (sourceB2494 + difference 1 2) sourceC2494) = raw34379 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34379; decide +kernel
    rw [ha]
    exact (canonical34379 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2494 + difference 2 3) (sourceB2494 + difference 3 2) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2494 + difference 2 3) (sourceB2494 + difference 3 2) sourceC2494) = raw34380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34380; decide +kernel
    rw [ha]
    exact (canonical34380 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2494 + difference 2 4) (sourceB2494 + difference 4 2) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2494 + difference 2 4) (sourceB2494 + difference 4 2) sourceC2494) = raw34381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34381; decide +kernel
    rw [ha]
    exact (canonical34381 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2494 + difference 2 5) (sourceB2494 + difference 5 2) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4826) := by
    have ha : (tripleCharges (sourceA2494 + difference 2 5) (sourceB2494 + difference 5 2) sourceC2494) = raw34382 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34382; decide +kernel
    rw [ha]
    exact (canonical34382 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2494 + difference 3 0) (sourceB2494 + difference 0 3) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4323) := by
    have ha : (tripleCharges (sourceA2494 + difference 3 0) (sourceB2494 + difference 0 3) sourceC2494) = raw26151 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw26151; decide +kernel
    rw [ha]
    exact (canonical26151 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2494 + difference 3 1) (sourceB2494 + difference 1 3) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4661) := by
    have ha : (tripleCharges (sourceA2494 + difference 3 1) (sourceB2494 + difference 1 3) sourceC2494) = raw34383 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34383; decide +kernel
    rw [ha]
    exact (canonical34383 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2494 + difference 3 2) (sourceB2494 + difference 2 3) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4715) := by
    have ha : (tripleCharges (sourceA2494 + difference 3 2) (sourceB2494 + difference 2 3) sourceC2494) = raw34384 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34384; decide +kernel
    rw [ha]
    exact (canonical34384 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2494 + difference 3 4) (sourceB2494 + difference 4 3) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2494 + difference 3 4) (sourceB2494 + difference 4 3) sourceC2494) = raw34385 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34385; decide +kernel
    rw [ha]
    exact (canonical34385 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2494 + difference 3 5) (sourceB2494 + difference 5 3) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4787) := by
    have ha : (tripleCharges (sourceA2494 + difference 3 5) (sourceB2494 + difference 5 3) sourceC2494) = raw34386 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34386; decide +kernel
    rw [ha]
    exact (canonical34386 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2494 + difference 4 0) (sourceB2494 + difference 0 4) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4323) := by
    have ha : (tripleCharges (sourceA2494 + difference 4 0) (sourceB2494 + difference 0 4) sourceC2494) = raw26156 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw26156; decide +kernel
    rw [ha]
    exact (canonical26156 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2494 + difference 4 1) (sourceB2494 + difference 1 4) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4661) := by
    have ha : (tripleCharges (sourceA2494 + difference 4 1) (sourceB2494 + difference 1 4) sourceC2494) = raw34387 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34387; decide +kernel
    rw [ha]
    exact (canonical34387 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2494 + difference 4 2) (sourceB2494 + difference 2 4) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4715) := by
    have ha : (tripleCharges (sourceA2494 + difference 4 2) (sourceB2494 + difference 2 4) sourceC2494) = raw34388 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34388; decide +kernel
    rw [ha]
    exact (canonical34388 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2494 + difference 4 3) (sourceB2494 + difference 3 4) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2494 + difference 4 3) (sourceB2494 + difference 3 4) sourceC2494) = raw34389 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34389; decide +kernel
    rw [ha]
    exact (canonical34389 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2494 + difference 4 5) (sourceB2494 + difference 5 4) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4787) := by
    have ha : (tripleCharges (sourceA2494 + difference 4 5) (sourceB2494 + difference 5 4) sourceC2494) = raw34390 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34390; decide +kernel
    rw [ha]
    exact (canonical34390 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2494 + difference 5 0) (sourceB2494 + difference 0 5) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4322) := by
    have ha : (tripleCharges (sourceA2494 + difference 5 0) (sourceB2494 + difference 0 5) sourceC2494) = raw26161 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw26161; decide +kernel
    rw [ha]
    exact (canonical26161 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2494 + difference 5 1) (sourceB2494 + difference 1 5) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4660) := by
    have ha : (tripleCharges (sourceA2494 + difference 5 1) (sourceB2494 + difference 1 5) sourceC2494) = raw34391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34391; decide +kernel
    rw [ha]
    exact (canonical34391 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2494 + difference 5 2) (sourceB2494 + difference 2 5) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4712) := by
    have ha : (tripleCharges (sourceA2494 + difference 5 2) (sourceB2494 + difference 2 5) sourceC2494) = raw34392 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34392; decide +kernel
    rw [ha]
    exact (canonical34392 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2494 + difference 5 3) (sourceB2494 + difference 3 5) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA2494 + difference 5 3) (sourceB2494 + difference 3 5) sourceC2494) = raw34393 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34393; decide +kernel
    rw [ha]
    exact (canonical34393 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2494 + difference 5 4) (sourceB2494 + difference 4 5) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA2494 + difference 5 4) (sourceB2494 + difference 4 5) sourceC2494) = raw34394 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34394; decide +kernel
    rw [ha]
    exact (canonical34394 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2494 sourceB2494 sourceC2494
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2494, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic125
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2010 : Integer.Sparse.reindex keyMap MixedData.row2010 = numericRow2010 := by decide +kernel

theorem numericCheck2010 (x : Master → ℝ) : Integer.Sparse.eval numericRow2010 x =
    (4 : ℝ) * reducedSource2010 x := by
  norm_num [numericRow2010, reducedSource2010, Integer.Sparse.eval, Sparse.eval, nodeValue4080, nodeValue4322, nodeValue4323, nodeValue4337, nodeValue4423, nodeValue4660, nodeValue4661, nodeValue4672, nodeValue4712, nodeValue4715, nodeValue4779, nodeValue4782, nodeValue4787, nodeValue4798, nodeValue4826, nodeValue4834, nodeValue4838, nodeValue5058, nodeValue5123, nodeValue5134, nodeValue5137]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows125
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero2010 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2010 (mixedVector B) = 0 := by
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  have h4322 : mixedVector B (Sum.inr 4322) = Sparse.eval nodeValue4322 (mixedVector B) := by
    change mixedMoment B node4322 node4322Labels = _
    exact sound4322 B hB hF
  have h4323 : mixedVector B (Sum.inr 4323) = Sparse.eval nodeValue4323 (mixedVector B) := by
    change mixedMoment B node4323 node4323Labels = _
    exact sound4323 B hB hF
  have h4337 : mixedVector B (Sum.inr 4337) = Sparse.eval nodeValue4337 (mixedVector B) := by
    change mixedMoment B node4337 node4337Labels = _
    exact sound4337 B hB hF
  have h4423 : mixedVector B (Sum.inr 4423) = Sparse.eval nodeValue4423 (mixedVector B) := by
    change mixedMoment B node4423 node4423Labels = _
    exact sound4423 B hB hF
  have h4660 : mixedVector B (Sum.inr 4660) = Sparse.eval nodeValue4660 (mixedVector B) := by
    change mixedMoment B node4660 node4660Labels = _
    exact sound4660 B hB hF
  have h4661 : mixedVector B (Sum.inr 4661) = Sparse.eval nodeValue4661 (mixedVector B) := by
    change mixedMoment B node4661 node4661Labels = _
    exact sound4661 B hB hF
  have h4672 : mixedVector B (Sum.inr 4672) = Sparse.eval nodeValue4672 (mixedVector B) := by
    change mixedMoment B node4672 node4672Labels = _
    exact sound4672 B hB hF
  have h4712 : mixedVector B (Sum.inr 4712) = Sparse.eval nodeValue4712 (mixedVector B) := by
    change mixedMoment B node4712 node4712Labels = _
    exact sound4712 B hB hF
  have h4715 : mixedVector B (Sum.inr 4715) = Sparse.eval nodeValue4715 (mixedVector B) := by
    change mixedMoment B node4715 node4715Labels = _
    exact sound4715 B hB hF
  have h4779 : mixedVector B (Sum.inr 4779) = Sparse.eval nodeValue4779 (mixedVector B) := by
    change mixedMoment B node4779 node4779Labels = _
    exact sound4779 B hB hF
  have h4782 : mixedVector B (Sum.inr 4782) = Sparse.eval nodeValue4782 (mixedVector B) := by
    change mixedMoment B node4782 node4782Labels = _
    exact sound4782 B hB hF
  have h4787 : mixedVector B (Sum.inr 4787) = Sparse.eval nodeValue4787 (mixedVector B) := by
    change mixedMoment B node4787 node4787Labels = _
    exact sound4787 B hB hF
  have h4798 : mixedVector B (Sum.inr 4798) = Sparse.eval nodeValue4798 (mixedVector B) := by
    change mixedMoment B node4798 node4798Labels = _
    exact sound4798 B hB hF
  have h4826 : mixedVector B (Sum.inr 4826) = Sparse.eval nodeValue4826 (mixedVector B) := by
    change mixedMoment B node4826 node4826Labels = _
    exact sound4826 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4838 : mixedVector B (Sum.inr 4838) = Sparse.eval nodeValue4838 (mixedVector B) := by
    change mixedMoment B node4838 node4838Labels = _
    exact sound4838 B hB hF
  have h5058 : mixedVector B (Sum.inr 5058) = Sparse.eval nodeValue5058 (mixedVector B) := by
    change mixedMoment B node5058 node5058Labels = _
    exact sound5058 B hB hF
  have h5123 : mixedVector B (Sum.inr 5123) = Sparse.eval nodeValue5123 (mixedVector B) := by
    change mixedMoment B node5123 node5123Labels = _
    exact sound5123 B hB hF
  have h5134 : mixedVector B (Sum.inr 5134) = Sparse.eval nodeValue5134 (mixedVector B) := by
    change mixedMoment B node5134 node5134Labels = _
    exact sound5134 B hB hF
  have h5137 : mixedVector B (Sum.inr 5137) = Sparse.eval nodeValue5137 (mixedVector B) := by
    change mixedMoment B node5137 node5137Labels = _
    exact sound5137 B hB hF
  simpa only [sourceForm2494, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4080, h4322, h4323, h4337, h4423, h4660, h4661, h4672, h4712, h4715, h4779, h4782, h4787, h4798, h4826, h4834, h4838, h5058, h5123, h5134, h5137, reducedSource2010] using sourceEq2494 B hB

theorem rowSound2010_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2010 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2010, numericCheck2010, reducedZero2010 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2010_e_oai
