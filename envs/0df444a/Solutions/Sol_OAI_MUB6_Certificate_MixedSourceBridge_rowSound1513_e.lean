-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1513_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:14:15.925196+00:00
-- url     : https://prove2.me/submissions/e08cae0c-6706-4016-a148-c672454c774b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E101
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical201
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25855 raw25855Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw25855 raw25855Labels = mixedMoment B raw25855step0 raw25855step0Labels := by
      have hz : ∀ j, raw25855 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25855step0 = (fun i j => raw25855 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25855step0 raw25855; decide +kernel
      have hl : raw25855step0Labels = raw25855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25855 raw25855Labels permutation346 hz
    _ = mixedMoment B node4838 node4838Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical202
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25856 raw25856Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw25856 raw25856Labels = mixedMoment B raw25856step0 raw25856step0Labels := by
      have hz : ∀ j, raw25856 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25856step0 = (fun i j => raw25856 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25856step0 raw25856; decide +kernel
      have hl : raw25856step0Labels = raw25856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25856 raw25856Labels permutation265 hz
    _ = mixedMoment B node4838 node4838Labels := by rfl

theorem canonical25857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25857 raw25857Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw25857 raw25857Labels = mixedMoment B raw25857step0 raw25857step0Labels := by
      have hz : ∀ j, raw25857 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25857step0 = (fun i j => raw25857 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25857step0 raw25857; decide +kernel
      have hl : raw25857step0Labels = raw25857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25857 raw25857Labels permutation346 hz
    mixedMoment B raw25857step0 raw25857step0Labels = mixedMoment B raw25857step1 raw25857step1Labels := by
      have hz : ∀ j, raw25857step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25857step1 = (fun i j => raw25857step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25857step1 raw25857step0; decide +kernel
      have hl : raw25857step1Labels = raw25857step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25857step0 raw25857step0Labels permutation56 hz
    _ = mixedMoment B node4895 node4895Labels := by rfl

theorem canonical25858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25858 raw25858Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw25858 raw25858Labels = mixedMoment B raw25858step0 raw25858step0Labels := by
      have hz : ∀ j, raw25858 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25858step0 = (fun i j => raw25858 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25858step0 raw25858; decide +kernel
      have hl : raw25858step0Labels = raw25858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25858 raw25858Labels permutation346 hz
    mixedMoment B raw25858step0 raw25858step0Labels = mixedMoment B raw25858step1 raw25858step1Labels := by
      have hz : ∀ j, raw25858step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25858step1 = (fun i j => raw25858step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25858step1 raw25858step0; decide +kernel
      have hl : raw25858step1Labels = raw25858step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25858step0 raw25858step0Labels permutation56 hz
    mixedMoment B raw25858step1 raw25858step1Labels = mixedMoment B raw25858step2 raw25858step2Labels := by
      have ha : raw25858step2 = (fun i j => raw25858step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25858step2 raw25858step1; decide +kernel
      have hl : raw25858step2Labels = raw25858step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25858step1 raw25858step1Labels permutation10 permutation2
    _ = mixedMoment B node4895 node4895Labels := by rfl

theorem canonical25859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25859 raw25859Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw25859 raw25859Labels = mixedMoment B raw25859step0 raw25859step0Labels := by
      have hz : ∀ j, raw25859 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25859step0 = (fun i j => raw25859 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25859step0 raw25859; decide +kernel
      have hl : raw25859step0Labels = raw25859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25859 raw25859Labels permutation346 hz
    mixedMoment B raw25859step0 raw25859step0Labels = mixedMoment B raw25859step1 raw25859step1Labels := by
      have hz : ∀ j, raw25859step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25859step1 = (fun i j => raw25859step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25859step1 raw25859step0; decide +kernel
      have hl : raw25859step1Labels = raw25859step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25859step0 raw25859step0Labels permutation56 hz
    mixedMoment B raw25859step1 raw25859step1Labels = mixedMoment B raw25859step2 raw25859step2Labels := by
      have hz : ∀ i, raw25859step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw25859step2 = (fun i j => raw25859step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw25859step2 raw25859step1; decide +kernel
      have hl : raw25859step2Labels = (fun j => raw25859step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw25859step1 raw25859step1Labels permutation4 hz
    mixedMoment B raw25859step2 raw25859step2Labels = mixedMoment B raw25859step3 raw25859step3Labels := by
      have ha : raw25859step3 = raw25859step2 := by apply Matrix.ext; unfold raw25859step3 raw25859step2; decide +kernel
      have hl : raw25859step2Labels = labelEmbedding2 ∘ raw25859step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25859step2 raw25859step2Labels raw25859step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical25860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25860 raw25860Labels = mixedMoment B node4175 node4175Labels := by
  calc
    mixedMoment B raw25860 raw25860Labels = mixedMoment B raw25860step0 raw25860step0Labels := by
      have hz : ∀ j, raw25860 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25860step0 = (fun i j => raw25860 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25860step0 raw25860; decide +kernel
      have hl : raw25860step0Labels = raw25860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25860 raw25860Labels permutation346 hz
    _ = mixedMoment B node4175 node4175Labels := by rfl

theorem canonical25861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25861 raw25861Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw25861 raw25861Labels = mixedMoment B raw25861step0 raw25861step0Labels := by
      have ha : raw25861step0 = (fun i j => raw25861 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25861step0 raw25861; decide +kernel
      have hl : raw25861step0Labels = raw25861Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25861 raw25861Labels permutation176 permutation2
    _ = mixedMoment B node4344 node4344Labels := by rfl

theorem canonical25862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25862 raw25862Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw25862 raw25862Labels = mixedMoment B raw25862step0 raw25862step0Labels := by
      have hz : ∀ j, raw25862 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25862step0 = (fun i j => raw25862 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25862step0 raw25862; decide +kernel
      have hl : raw25862step0Labels = raw25862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25862 raw25862Labels permutation346 hz
    mixedMoment B raw25862step0 raw25862step0Labels = mixedMoment B raw25862step1 raw25862step1Labels := by
      have ha : raw25862step1 = (fun i j => raw25862step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25862step1 raw25862step0; decide +kernel
      have hl : raw25862step1Labels = raw25862step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25862step0 raw25862step0Labels permutation38 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical25863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25863 raw25863Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw25863 raw25863Labels = mixedMoment B raw25863step0 raw25863step0Labels := by
      have hz : ∀ j, raw25863 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25863step0 = (fun i j => raw25863 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25863step0 raw25863; decide +kernel
      have hl : raw25863step0Labels = raw25863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25863 raw25863Labels permutation346 hz
    mixedMoment B raw25863step0 raw25863step0Labels = mixedMoment B raw25863step1 raw25863step1Labels := by
      have ha : raw25863step1 = (fun i j => raw25863step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25863step1 raw25863step0; decide +kernel
      have hl : raw25863step1Labels = raw25863step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25863step0 raw25863step0Labels permutation44 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical25864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25864 raw25864Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw25864 raw25864Labels = mixedMoment B raw25864step0 raw25864step0Labels := by
      have hz : ∀ j, raw25864 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25864step0 = (fun i j => raw25864 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25864step0 raw25864; decide +kernel
      have hl : raw25864step0Labels = raw25864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25864 raw25864Labels permutation346 hz
    _ = mixedMoment B node4497 node4497Labels := by rfl

theorem canonical25865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25865 raw25865Labels = mixedMoment B node4175 node4175Labels := by
  calc
    mixedMoment B raw25865 raw25865Labels = mixedMoment B raw25865step0 raw25865step0Labels := by
      have hz : ∀ j, raw25865 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25865step0 = (fun i j => raw25865 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25865step0 raw25865; decide +kernel
      have hl : raw25865step0Labels = raw25865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25865 raw25865Labels permutation265 hz
    _ = mixedMoment B node4175 node4175Labels := by rfl

theorem canonical25866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25866 raw25866Labels = mixedMoment B node4344 node4344Labels := by
  calc
    _ = mixedMoment B node4344 node4344Labels := by rfl

theorem canonical25867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25867 raw25867Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw25867 raw25867Labels = mixedMoment B raw25867step0 raw25867step0Labels := by
      have hz : ∀ j, raw25867 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25867step0 = (fun i j => raw25867 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25867step0 raw25867; decide +kernel
      have hl : raw25867step0Labels = raw25867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25867 raw25867Labels permutation265 hz
    mixedMoment B raw25867step0 raw25867step0Labels = mixedMoment B raw25867step1 raw25867step1Labels := by
      have ha : raw25867step1 = (fun i j => raw25867step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25867step1 raw25867step0; decide +kernel
      have hl : raw25867step1Labels = raw25867step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25867step0 raw25867step0Labels permutation38 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical25868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25868 raw25868Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw25868 raw25868Labels = mixedMoment B raw25868step0 raw25868step0Labels := by
      have hz : ∀ j, raw25868 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25868step0 = (fun i j => raw25868 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25868step0 raw25868; decide +kernel
      have hl : raw25868step0Labels = raw25868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25868 raw25868Labels permutation265 hz
    mixedMoment B raw25868step0 raw25868step0Labels = mixedMoment B raw25868step1 raw25868step1Labels := by
      have ha : raw25868step1 = (fun i j => raw25868step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25868step1 raw25868step0; decide +kernel
      have hl : raw25868step1Labels = raw25868step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25868step0 raw25868step0Labels permutation44 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical25869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25869 raw25869Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw25869 raw25869Labels = mixedMoment B raw25869step0 raw25869step0Labels := by
      have hz : ∀ j, raw25869 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25869step0 = (fun i j => raw25869 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25869step0 raw25869; decide +kernel
      have hl : raw25869step0Labels = raw25869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25869 raw25869Labels permutation265 hz
    _ = mixedMoment B node4497 node4497Labels := by rfl

theorem canonical25870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25870 raw25870Labels = mixedMoment B node4186 node4186Labels := by
  calc
    mixedMoment B raw25870 raw25870Labels = mixedMoment B raw25870step0 raw25870step0Labels := by
      have hz : ∀ j, raw25870 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25870step0 = (fun i j => raw25870 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25870step0 raw25870; decide +kernel
      have hl : raw25870step0Labels = raw25870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25870 raw25870Labels permutation346 hz
    mixedMoment B raw25870step0 raw25870step0Labels = mixedMoment B raw25870step1 raw25870step1Labels := by
      have hz : ∀ j, raw25870step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25870step1 = (fun i j => raw25870step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25870step1 raw25870step0; decide +kernel
      have hl : raw25870step1Labels = raw25870step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25870step0 raw25870step0Labels permutation56 hz
    mixedMoment B raw25870step1 raw25870step1Labels = mixedMoment B raw25870step2 raw25870step2Labels := by
      have ha : raw25870step2 = (fun i j => raw25870step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25870step2 raw25870step1; decide +kernel
      have hl : raw25870step2Labels = raw25870step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25870step1 raw25870step1Labels permutation10 permutation2
    _ = mixedMoment B node4186 node4186Labels := by rfl

theorem canonical25871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25871 raw25871Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw25871 raw25871Labels = mixedMoment B raw25871step0 raw25871step0Labels := by
      have hz : ∀ j, raw25871 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25871step0 = (fun i j => raw25871 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25871step0 raw25871; decide +kernel
      have hl : raw25871step0Labels = raw25871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25871 raw25871Labels permutation346 hz
    mixedMoment B raw25871step0 raw25871step0Labels = mixedMoment B raw25871step1 raw25871step1Labels := by
      have ha : raw25871step1 = (fun i j => raw25871step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25871step1 raw25871step0; decide +kernel
      have hl : raw25871step1Labels = raw25871step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25871step0 raw25871step0Labels permutation34 permutation2
    _ = mixedMoment B node4355 node4355Labels := by rfl

theorem canonical25872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25872 raw25872Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw25872 raw25872Labels = mixedMoment B raw25872step0 raw25872step0Labels := by
      have hz : ∀ j, raw25872 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25872step0 = (fun i j => raw25872 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25872step0 raw25872; decide +kernel
      have hl : raw25872step0Labels = raw25872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25872 raw25872Labels permutation265 hz
    mixedMoment B raw25872step0 raw25872step0Labels = mixedMoment B raw25872step1 raw25872step1Labels := by
      have ha : raw25872step1 = (fun i j => raw25872step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25872step1 raw25872step0; decide +kernel
      have hl : raw25872step1Labels = raw25872step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25872step0 raw25872step0Labels permutation34 permutation2
    _ = mixedMoment B node4355 node4355Labels := by rfl

theorem canonical25873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25873 raw25873Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw25873 raw25873Labels = mixedMoment B raw25873step0 raw25873step0Labels := by
      have hz : ∀ j, raw25873 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25873step0 = (fun i j => raw25873 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25873step0 raw25873; decide +kernel
      have hl : raw25873step0Labels = raw25873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25873 raw25873Labels permutation346 hz
    mixedMoment B raw25873step0 raw25873step0Labels = mixedMoment B raw25873step1 raw25873step1Labels := by
      have hz : ∀ j, raw25873step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25873step1 = (fun i j => raw25873step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25873step1 raw25873step0; decide +kernel
      have hl : raw25873step1Labels = raw25873step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25873step0 raw25873step0Labels permutation56 hz
    mixedMoment B raw25873step1 raw25873step1Labels = mixedMoment B raw25873step2 raw25873step2Labels := by
      have ha : raw25873step2 = (fun i j => raw25873step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25873step2 raw25873step1; decide +kernel
      have hl : raw25873step2Labels = raw25873step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25873step1 raw25873step1Labels permutation10 permutation2
    _ = mixedMoment B node4467 node4467Labels := by rfl

theorem canonical25874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25874 raw25874Labels = mixedMoment B node4502 node4502Labels := by
  calc
    mixedMoment B raw25874 raw25874Labels = mixedMoment B raw25874step0 raw25874step0Labels := by
      have hz : ∀ j, raw25874 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25874step0 = (fun i j => raw25874 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25874step0 raw25874; decide +kernel
      have hl : raw25874step0Labels = raw25874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25874 raw25874Labels permutation346 hz
    mixedMoment B raw25874step0 raw25874step0Labels = mixedMoment B raw25874step1 raw25874step1Labels := by
      have hz : ∀ j, raw25874step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25874step1 = (fun i j => raw25874step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25874step1 raw25874step0; decide +kernel
      have hl : raw25874step1Labels = raw25874step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25874step0 raw25874step0Labels permutation56 hz
    mixedMoment B raw25874step1 raw25874step1Labels = mixedMoment B raw25874step2 raw25874step2Labels := by
      have ha : raw25874step2 = (fun i j => raw25874step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25874step2 raw25874step1; decide +kernel
      have hl : raw25874step2Labels = raw25874step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25874step1 raw25874step1Labels permutation11 permutation2
    _ = mixedMoment B node4502 node4502Labels := by rfl

theorem canonical25875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25875 raw25875Labels = mixedMoment B node4186 node4186Labels := by
  calc
    mixedMoment B raw25875 raw25875Labels = mixedMoment B raw25875step0 raw25875step0Labels := by
      have hz : ∀ j, raw25875 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25875step0 = (fun i j => raw25875 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25875step0 raw25875; decide +kernel
      have hl : raw25875step0Labels = raw25875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25875 raw25875Labels permutation346 hz
    mixedMoment B raw25875step0 raw25875step0Labels = mixedMoment B raw25875step1 raw25875step1Labels := by
      have hz : ∀ j, raw25875step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25875step1 = (fun i j => raw25875step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25875step1 raw25875step0; decide +kernel
      have hl : raw25875step1Labels = raw25875step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25875step0 raw25875step0Labels permutation56 hz
    _ = mixedMoment B node4186 node4186Labels := by rfl

theorem canonical25876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25876 raw25876Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw25876 raw25876Labels = mixedMoment B raw25876step0 raw25876step0Labels := by
      have hz : ∀ j, raw25876 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25876step0 = (fun i j => raw25876 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25876step0 raw25876; decide +kernel
      have hl : raw25876step0Labels = raw25876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25876 raw25876Labels permutation346 hz
    _ = mixedMoment B node4355 node4355Labels := by rfl

theorem canonical25877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25877 raw25877Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw25877 raw25877Labels = mixedMoment B raw25877step0 raw25877step0Labels := by
      have hz : ∀ j, raw25877 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25877step0 = (fun i j => raw25877 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25877step0 raw25877; decide +kernel
      have hl : raw25877step0Labels = raw25877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25877 raw25877Labels permutation265 hz
    _ = mixedMoment B node4355 node4355Labels := by rfl

theorem canonical25878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25878 raw25878Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw25878 raw25878Labels = mixedMoment B raw25878step0 raw25878step0Labels := by
      have hz : ∀ j, raw25878 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25878step0 = (fun i j => raw25878 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25878step0 raw25878; decide +kernel
      have hl : raw25878step0Labels = raw25878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25878 raw25878Labels permutation346 hz
    mixedMoment B raw25878step0 raw25878step0Labels = mixedMoment B raw25878step1 raw25878step1Labels := by
      have hz : ∀ j, raw25878step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25878step1 = (fun i j => raw25878step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25878step1 raw25878step0; decide +kernel
      have hl : raw25878step1Labels = raw25878step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25878step0 raw25878step0Labels permutation56 hz
    _ = mixedMoment B node4467 node4467Labels := by rfl

theorem canonical25879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25879 raw25879Labels = mixedMoment B node4502 node4502Labels := by
  calc
    mixedMoment B raw25879 raw25879Labels = mixedMoment B raw25879step0 raw25879step0Labels := by
      have hz : ∀ j, raw25879 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25879step0 = (fun i j => raw25879 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25879step0 raw25879; decide +kernel
      have hl : raw25879step0Labels = raw25879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25879 raw25879Labels permutation346 hz
    mixedMoment B raw25879step0 raw25879step0Labels = mixedMoment B raw25879step1 raw25879step1Labels := by
      have hz : ∀ j, raw25879step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25879step1 = (fun i j => raw25879step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25879step1 raw25879step0; decide +kernel
      have hl : raw25879step1Labels = raw25879step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25879step0 raw25879step0Labels permutation56 hz
    mixedMoment B raw25879step1 raw25879step1Labels = mixedMoment B raw25879step2 raw25879step2Labels := by
      have ha : raw25879step2 = (fun i j => raw25879step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25879step2 raw25879step1; decide +kernel
      have hl : raw25879step2Labels = raw25879step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25879step1 raw25879step1Labels permutation9 permutation2
    _ = mixedMoment B node4502 node4502Labels := by rfl

theorem canonical25880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25880 raw25880Labels = mixedMoment B node4183 node4183Labels := by
  calc
    mixedMoment B raw25880 raw25880Labels = mixedMoment B raw25880step0 raw25880step0Labels := by
      have hz : ∀ j, raw25880 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25880step0 = (fun i j => raw25880 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25880step0 raw25880; decide +kernel
      have hl : raw25880step0Labels = raw25880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25880 raw25880Labels permutation346 hz
    mixedMoment B raw25880step0 raw25880step0Labels = mixedMoment B raw25880step1 raw25880step1Labels := by
      have hz : ∀ j, raw25880step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25880step1 = (fun i j => raw25880step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25880step1 raw25880step0; decide +kernel
      have hl : raw25880step1Labels = raw25880step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25880step0 raw25880step0Labels permutation56 hz
    _ = mixedMoment B node4183 node4183Labels := by rfl

theorem canonical25881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25881 raw25881Labels = mixedMoment B node4352 node4352Labels := by
  calc
    mixedMoment B raw25881 raw25881Labels = mixedMoment B raw25881step0 raw25881step0Labels := by
      have hz : ∀ j, raw25881 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25881step0 = (fun i j => raw25881 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25881step0 raw25881; decide +kernel
      have hl : raw25881step0Labels = raw25881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25881 raw25881Labels permutation346 hz
    _ = mixedMoment B node4352 node4352Labels := by rfl

theorem canonical25882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25882 raw25882Labels = mixedMoment B node4352 node4352Labels := by
  calc
    mixedMoment B raw25882 raw25882Labels = mixedMoment B raw25882step0 raw25882step0Labels := by
      have hz : ∀ j, raw25882 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25882step0 = (fun i j => raw25882 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25882step0 raw25882; decide +kernel
      have hl : raw25882step0Labels = raw25882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25882 raw25882Labels permutation265 hz
    _ = mixedMoment B node4352 node4352Labels := by rfl

theorem canonical25883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25883 raw25883Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw25883 raw25883Labels = mixedMoment B raw25883step0 raw25883step0Labels := by
      have hz : ∀ j, raw25883 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25883step0 = (fun i j => raw25883 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25883step0 raw25883; decide +kernel
      have hl : raw25883step0Labels = raw25883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25883 raw25883Labels permutation346 hz
    mixedMoment B raw25883step0 raw25883step0Labels = mixedMoment B raw25883step1 raw25883step1Labels := by
      have hz : ∀ j, raw25883step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25883step1 = (fun i j => raw25883step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25883step1 raw25883step0; decide +kernel
      have hl : raw25883step1Labels = raw25883step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25883step0 raw25883step0Labels permutation56 hz
    _ = mixedMoment B node4463 node4463Labels := by rfl

theorem canonical25884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25884 raw25884Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw25884 raw25884Labels = mixedMoment B raw25884step0 raw25884step0Labels := by
      have hz : ∀ j, raw25884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25884step0 = (fun i j => raw25884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25884step0 raw25884; decide +kernel
      have hl : raw25884step0Labels = raw25884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25884 raw25884Labels permutation346 hz
    mixedMoment B raw25884step0 raw25884step0Labels = mixedMoment B raw25884step1 raw25884step1Labels := by
      have hz : ∀ j, raw25884step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25884step1 = (fun i j => raw25884step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25884step1 raw25884step0; decide +kernel
      have hl : raw25884step1Labels = raw25884step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25884step0 raw25884step0Labels permutation56 hz
    mixedMoment B raw25884step1 raw25884step1Labels = mixedMoment B raw25884step2 raw25884step2Labels := by
      have ha : raw25884step2 = (fun i j => raw25884step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25884step2 raw25884step1; decide +kernel
      have hl : raw25884step2Labels = raw25884step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25884step1 raw25884step1Labels permutation10 permutation2
    _ = mixedMoment B node4463 node4463Labels := by rfl

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

theorem canonical810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw810 raw810Labels = mixedMoment B node4175 node4175Labels := by
  calc
    mixedMoment B raw810 raw810Labels = mixedMoment B raw810step0 raw810step0Labels := by
      have ha : raw810step0 = (fun i j => raw810 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw810step0 raw810; decide +kernel
      have hl : raw810step0Labels = raw810Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw810 raw810Labels permutation32 permutation4
    mixedMoment B raw810step0 raw810step0Labels = mixedMoment B raw810step1 raw810step1Labels := by
      have ha : raw810step1 = raw810step0 := by apply Matrix.ext; unfold raw810step1 raw810step0; decide +kernel
      have hl : raw810step0Labels = labelEmbedding7 ∘ raw810step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw810step0 raw810step0Labels raw810step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4175 node4175Labels := by rfl

theorem canonical811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw811 raw811Labels = mixedMoment B node603 node603Labels := by
  calc
    mixedMoment B raw811 raw811Labels = mixedMoment B raw811step0 raw811step0Labels := by
      have ha : raw811step0 = (fun i j => raw811 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw811step0 raw811; decide +kernel
      have hl : raw811step0Labels = raw811Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw811 raw811Labels permutation32 permutation4
    _ = mixedMoment B node603 node603Labels := by rfl

theorem canonical812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw812 raw812Labels = mixedMoment B node1517 node1517Labels := by
  calc
    mixedMoment B raw812 raw812Labels = mixedMoment B raw812step0 raw812step0Labels := by
      have ha : raw812step0 = (fun i j => raw812 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw812step0 raw812; decide +kernel
      have hl : raw812step0Labels = raw812Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw812 raw812Labels permutation32 permutation6
    mixedMoment B raw812step0 raw812step0Labels = mixedMoment B raw812step1 raw812step1Labels := by
      have ha : raw812step1 = -raw812step0 := by apply Matrix.ext; change ∀ i j, raw812step1 i j = -(raw812step0 i j); unfold raw812step1 raw812step0; decide +kernel
      have hl : raw812step1Labels = raw812step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw812step1 raw812step1Labels = mixedMoment B raw812step2 raw812step2Labels := by
      have ha : raw812step2 = raw812step1 := by apply Matrix.ext; unfold raw812step2 raw812step1; decide +kernel
      have hl : raw812step1Labels = labelEmbedding1 ∘ raw812step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw812step1 raw812step1Labels raw812step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1517 node1517Labels := by rfl

theorem canonical825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw825 raw825Labels = mixedMoment B node4183 node4183Labels := by
  calc
    mixedMoment B raw825 raw825Labels = mixedMoment B raw825step0 raw825step0Labels := by
      have ha : raw825step0 = (fun i j => raw825 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw825step0 raw825; decide +kernel
      have hl : raw825step0Labels = raw825Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw825 raw825Labels permutation8 permutation4
    mixedMoment B raw825step0 raw825step0Labels = mixedMoment B raw825step1 raw825step1Labels := by
      have ha : raw825step1 = raw825step0 := by apply Matrix.ext; unfold raw825step1 raw825step0; decide +kernel
      have hl : raw825step0Labels = labelEmbedding7 ∘ raw825step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw825step0 raw825step0Labels raw825step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4183 node4183Labels := by rfl

theorem canonical826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw826 raw826Labels = mixedMoment B node611 node611Labels := by
  calc
    mixedMoment B raw826 raw826Labels = mixedMoment B raw826step0 raw826step0Labels := by
      have ha : raw826step0 = (fun i j => raw826 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw826step0 raw826; decide +kernel
      have hl : raw826step0Labels = raw826Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw826 raw826Labels permutation8 permutation4
    _ = mixedMoment B node611 node611Labels := by rfl

theorem canonical827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw827 raw827Labels = mixedMoment B node1535 node1535Labels := by
  calc
    mixedMoment B raw827 raw827Labels = mixedMoment B raw827step0 raw827step0Labels := by
      have ha : raw827step0 = (fun i j => raw827 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw827step0 raw827; decide +kernel
      have hl : raw827step0Labels = raw827Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw827 raw827Labels permutation8 permutation6
    mixedMoment B raw827step0 raw827step0Labels = mixedMoment B raw827step1 raw827step1Labels := by
      have ha : raw827step1 = -raw827step0 := by apply Matrix.ext; change ∀ i j, raw827step1 i j = -(raw827step0 i j); unfold raw827step1 raw827step0; decide +kernel
      have hl : raw827step1Labels = raw827step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw827step1 raw827step1Labels = mixedMoment B raw827step2 raw827step2Labels := by
      have ha : raw827step2 = raw827step1 := by apply Matrix.ext; unfold raw827step2 raw827step1; decide +kernel
      have hl : raw827step1Labels = labelEmbedding1 ∘ raw827step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw827step1 raw827step1Labels raw827step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1535 node1535Labels := by rfl

theorem canonical831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw831 raw831Labels = mixedMoment B node4186 node4186Labels := by
  calc
    mixedMoment B raw831 raw831Labels = mixedMoment B raw831step0 raw831step0Labels := by
      have ha : raw831step0 = (fun i j => raw831 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw831step0 raw831; decide +kernel
      have hl : raw831step0Labels = raw831Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw831 raw831Labels permutation8 permutation4
    mixedMoment B raw831step0 raw831step0Labels = mixedMoment B raw831step1 raw831step1Labels := by
      have ha : raw831step1 = raw831step0 := by apply Matrix.ext; unfold raw831step1 raw831step0; decide +kernel
      have hl : raw831step0Labels = labelEmbedding7 ∘ raw831step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw831step0 raw831step0Labels raw831step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4186 node4186Labels := by rfl

theorem canonical832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw832 raw832Labels = mixedMoment B node614 node614Labels := by
  calc
    mixedMoment B raw832 raw832Labels = mixedMoment B raw832step0 raw832step0Labels := by
      have ha : raw832step0 = (fun i j => raw832 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw832step0 raw832; decide +kernel
      have hl : raw832step0Labels = raw832Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw832 raw832Labels permutation8 permutation4
    _ = mixedMoment B node614 node614Labels := by rfl

theorem canonical833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw833 raw833Labels = mixedMoment B node1536 node1536Labels := by
  calc
    mixedMoment B raw833 raw833Labels = mixedMoment B raw833step0 raw833step0Labels := by
      have ha : raw833step0 = (fun i j => raw833 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw833step0 raw833; decide +kernel
      have hl : raw833step0Labels = raw833Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw833 raw833Labels permutation8 permutation6
    mixedMoment B raw833step0 raw833step0Labels = mixedMoment B raw833step1 raw833step1Labels := by
      have ha : raw833step1 = -raw833step0 := by apply Matrix.ext; change ∀ i j, raw833step1 i j = -(raw833step0 i j); unfold raw833step1 raw833step0; decide +kernel
      have hl : raw833step1Labels = raw833step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw833step1 raw833step1Labels = mixedMoment B raw833step2 raw833step2Labels := by
      have ha : raw833step2 = raw833step1 := by apply Matrix.ext; unfold raw833step2 raw833step1; decide +kernel
      have hl : raw833step1Labels = labelEmbedding1 ∘ raw833step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw833step1 raw833step1Labels raw833step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1536 node1536Labels := by rfl

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

theorem canonical1128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1128 raw1128Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw1128 raw1128Labels = mixedMoment B raw1128step0 raw1128step0Labels := by
      have ha : raw1128step0 = (fun i j => raw1128 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1128step0 raw1128; decide +kernel
      have hl : raw1128step0Labels = raw1128Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1128 raw1128Labels permutation152 permutation4
    mixedMoment B raw1128step0 raw1128step0Labels = mixedMoment B raw1128step1 raw1128step1Labels := by
      have ha : raw1128step1 = raw1128step0 := by apply Matrix.ext; unfold raw1128step1 raw1128step0; decide +kernel
      have hl : raw1128step0Labels = labelEmbedding7 ∘ raw1128step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1128step0 raw1128step0Labels raw1128step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4344 node4344Labels := by rfl

theorem canonical1129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1129 raw1129Labels = mixedMoment B node922 node922Labels := by
  calc
    mixedMoment B raw1129 raw1129Labels = mixedMoment B raw1129step0 raw1129step0Labels := by
      have ha : raw1129step0 = (fun i j => raw1129 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1129step0 raw1129; decide +kernel
      have hl : raw1129step0Labels = raw1129Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1129 raw1129Labels permutation152 permutation4
    _ = mixedMoment B node922 node922Labels := by rfl

theorem canonical1130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1130 raw1130Labels = mixedMoment B node1673 node1673Labels := by
  calc
    mixedMoment B raw1130 raw1130Labels = mixedMoment B raw1130step0 raw1130step0Labels := by
      have ha : raw1130step0 = (fun i j => raw1130 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1130step0 raw1130; decide +kernel
      have hl : raw1130step0Labels = raw1130Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1130 raw1130Labels permutation152 permutation6
    mixedMoment B raw1130step0 raw1130step0Labels = mixedMoment B raw1130step1 raw1130step1Labels := by
      have ha : raw1130step1 = -raw1130step0 := by apply Matrix.ext; change ∀ i j, raw1130step1 i j = -(raw1130step0 i j); unfold raw1130step1 raw1130step0; decide +kernel
      have hl : raw1130step1Labels = raw1130step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1130step1 raw1130step1Labels = mixedMoment B raw1130step2 raw1130step2Labels := by
      have ha : raw1130step2 = raw1130step1 := by apply Matrix.ext; unfold raw1130step2 raw1130step1; decide +kernel
      have hl : raw1130step1Labels = labelEmbedding1 ∘ raw1130step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1130step1 raw1130step1Labels raw1130step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1673 node1673Labels := by rfl

theorem canonical1143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1143 raw1143Labels = mixedMoment B node4352 node4352Labels := by
  calc
    mixedMoment B raw1143 raw1143Labels = mixedMoment B raw1143step0 raw1143step0Labels := by
      have ha : raw1143step0 = (fun i j => raw1143 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1143step0 raw1143; decide +kernel
      have hl : raw1143step0Labels = raw1143Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1143 raw1143Labels permutation32 permutation4
    mixedMoment B raw1143step0 raw1143step0Labels = mixedMoment B raw1143step1 raw1143step1Labels := by
      have ha : raw1143step1 = raw1143step0 := by apply Matrix.ext; unfold raw1143step1 raw1143step0; decide +kernel
      have hl : raw1143step0Labels = labelEmbedding7 ∘ raw1143step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1143step0 raw1143step0Labels raw1143step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4352 node4352Labels := by rfl

theorem canonical1144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1144 raw1144Labels = mixedMoment B node930 node930Labels := by
  calc
    mixedMoment B raw1144 raw1144Labels = mixedMoment B raw1144step0 raw1144step0Labels := by
      have ha : raw1144step0 = (fun i j => raw1144 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1144step0 raw1144; decide +kernel
      have hl : raw1144step0Labels = raw1144Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1144 raw1144Labels permutation32 permutation4
    _ = mixedMoment B node930 node930Labels := by rfl

theorem canonical1145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1145 raw1145Labels = mixedMoment B node1690 node1690Labels := by
  calc
    mixedMoment B raw1145 raw1145Labels = mixedMoment B raw1145step0 raw1145step0Labels := by
      have ha : raw1145step0 = (fun i j => raw1145 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1145step0 raw1145; decide +kernel
      have hl : raw1145step0Labels = raw1145Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1145 raw1145Labels permutation32 permutation6
    mixedMoment B raw1145step0 raw1145step0Labels = mixedMoment B raw1145step1 raw1145step1Labels := by
      have ha : raw1145step1 = -raw1145step0 := by apply Matrix.ext; change ∀ i j, raw1145step1 i j = -(raw1145step0 i j); unfold raw1145step1 raw1145step0; decide +kernel
      have hl : raw1145step1Labels = raw1145step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1145step1 raw1145step1Labels = mixedMoment B raw1145step2 raw1145step2Labels := by
      have ha : raw1145step2 = raw1145step1 := by apply Matrix.ext; unfold raw1145step2 raw1145step1; decide +kernel
      have hl : raw1145step1Labels = labelEmbedding1 ∘ raw1145step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1145step1 raw1145step1Labels raw1145step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1690 node1690Labels := by rfl

theorem canonical1149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1149 raw1149Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw1149 raw1149Labels = mixedMoment B raw1149step0 raw1149step0Labels := by
      have ha : raw1149step0 = (fun i j => raw1149 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1149step0 raw1149; decide +kernel
      have hl : raw1149step0Labels = raw1149Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1149 raw1149Labels permutation32 permutation4
    mixedMoment B raw1149step0 raw1149step0Labels = mixedMoment B raw1149step1 raw1149step1Labels := by
      have ha : raw1149step1 = raw1149step0 := by apply Matrix.ext; unfold raw1149step1 raw1149step0; decide +kernel
      have hl : raw1149step0Labels = labelEmbedding7 ∘ raw1149step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1149step0 raw1149step0Labels raw1149step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4355 node4355Labels := by rfl

theorem canonical1150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1150 raw1150Labels = mixedMoment B node933 node933Labels := by
  calc
    mixedMoment B raw1150 raw1150Labels = mixedMoment B raw1150step0 raw1150step0Labels := by
      have ha : raw1150step0 = (fun i j => raw1150 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1150step0 raw1150; decide +kernel
      have hl : raw1150step0Labels = raw1150Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1150 raw1150Labels permutation32 permutation4
    _ = mixedMoment B node933 node933Labels := by rfl

theorem canonical1151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1151 raw1151Labels = mixedMoment B node1691 node1691Labels := by
  calc
    mixedMoment B raw1151 raw1151Labels = mixedMoment B raw1151step0 raw1151step0Labels := by
      have ha : raw1151step0 = (fun i j => raw1151 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1151step0 raw1151; decide +kernel
      have hl : raw1151step0Labels = raw1151Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1151 raw1151Labels permutation32 permutation6
    mixedMoment B raw1151step0 raw1151step0Labels = mixedMoment B raw1151step1 raw1151step1Labels := by
      have ha : raw1151step1 = -raw1151step0 := by apply Matrix.ext; change ∀ i j, raw1151step1 i j = -(raw1151step0 i j); unfold raw1151step1 raw1151step0; decide +kernel
      have hl : raw1151step1Labels = raw1151step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1151step1 raw1151step1Labels = mixedMoment B raw1151step2 raw1151step2Labels := by
      have ha : raw1151step2 = raw1151step1 := by apply Matrix.ext; unfold raw1151step2 raw1151step1; decide +kernel
      have hl : raw1151step1Labels = labelEmbedding1 ∘ raw1151step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1151step1 raw1151step1Labels raw1151step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1691 node1691Labels := by rfl

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

theorem canonical1260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1260 raw1260Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw1260 raw1260Labels = mixedMoment B raw1260step0 raw1260step0Labels := by
      have ha : raw1260step0 = (fun i j => raw1260 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1260step0 raw1260; decide +kernel
      have hl : raw1260step0Labels = raw1260Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1260 raw1260Labels permutation32 permutation4
    mixedMoment B raw1260step0 raw1260step0Labels = mixedMoment B raw1260step1 raw1260step1Labels := by
      have ha : raw1260step1 = raw1260step0 := by apply Matrix.ext; unfold raw1260step1 raw1260step0; decide +kernel
      have hl : raw1260step0Labels = labelEmbedding7 ∘ raw1260step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1260step0 raw1260step0Labels raw1260step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

theorem canonical1261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1261 raw1261Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw1261 raw1261Labels = mixedMoment B raw1261step0 raw1261step0Labels := by
      have ha : raw1261step0 = (fun i j => raw1261 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1261step0 raw1261; decide +kernel
      have hl : raw1261step0Labels = raw1261Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1261 raw1261Labels permutation32 permutation4
    _ = mixedMoment B node1041 node1041Labels := by rfl

theorem canonical1262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1262 raw1262Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw1262 raw1262Labels = mixedMoment B raw1262step0 raw1262step0Labels := by
      have ha : raw1262step0 = (fun i j => raw1262 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1262step0 raw1262; decide +kernel
      have hl : raw1262step0Labels = raw1262Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1262 raw1262Labels permutation38 permutation6
    mixedMoment B raw1262step0 raw1262step0Labels = mixedMoment B raw1262step1 raw1262step1Labels := by
      have ha : raw1262step1 = -raw1262step0 := by apply Matrix.ext; change ∀ i j, raw1262step1 i j = -(raw1262step0 i j); unfold raw1262step1 raw1262step0; decide +kernel
      have hl : raw1262step1Labels = raw1262step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1262step1 raw1262step1Labels = mixedMoment B raw1262step2 raw1262step2Labels := by
      have ha : raw1262step2 = raw1262step1 := by apply Matrix.ext; unfold raw1262step2 raw1262step1; decide +kernel
      have hl : raw1262step1Labels = labelEmbedding1 ∘ raw1262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1262step1 raw1262step1Labels raw1262step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

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

theorem canonical1275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1275 raw1275Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw1275 raw1275Labels = mixedMoment B raw1275step0 raw1275step0Labels := by
      have ha : raw1275step0 = (fun i j => raw1275 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1275step0 raw1275; decide +kernel
      have hl : raw1275step0Labels = raw1275Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1275 raw1275Labels permutation8 permutation4
    mixedMoment B raw1275step0 raw1275step0Labels = mixedMoment B raw1275step1 raw1275step1Labels := by
      have ha : raw1275step1 = raw1275step0 := by apply Matrix.ext; unfold raw1275step1 raw1275step0; decide +kernel
      have hl : raw1275step0Labels = labelEmbedding7 ∘ raw1275step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1275step0 raw1275step0Labels raw1275step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

theorem canonical1276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1276 raw1276Labels = mixedMoment B node1050 node1050Labels := by
  calc
    mixedMoment B raw1276 raw1276Labels = mixedMoment B raw1276step0 raw1276step0Labels := by
      have ha : raw1276step0 = (fun i j => raw1276 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1276step0 raw1276; decide +kernel
      have hl : raw1276step0Labels = raw1276Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1276 raw1276Labels permutation8 permutation4
    _ = mixedMoment B node1050 node1050Labels := by rfl

theorem canonical1277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1277 raw1277Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw1277 raw1277Labels = mixedMoment B raw1277step0 raw1277step0Labels := by
      have ha : raw1277step0 = (fun i j => raw1277 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1277step0 raw1277; decide +kernel
      have hl : raw1277step0Labels = raw1277Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1277 raw1277Labels permutation8 permutation6
    mixedMoment B raw1277step0 raw1277step0Labels = mixedMoment B raw1277step1 raw1277step1Labels := by
      have ha : raw1277step1 = -raw1277step0 := by apply Matrix.ext; change ∀ i j, raw1277step1 i j = -(raw1277step0 i j); unfold raw1277step1 raw1277step0; decide +kernel
      have hl : raw1277step1Labels = raw1277step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1277step1 raw1277step1Labels = mixedMoment B raw1277step2 raw1277step2Labels := by
      have ha : raw1277step2 = raw1277step1 := by apply Matrix.ext; unfold raw1277step2 raw1277step1; decide +kernel
      have hl : raw1277step1Labels = labelEmbedding1 ∘ raw1277step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1277step1 raw1277step1Labels raw1277step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1751 node1751Labels := by rfl

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

theorem singleton4175 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4175 node4175Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node603 node603Labels + mixedMoment B node1517 node1517Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw810 singletonSmall4175
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4175) = raw810Labels := by decide +kernel
  rw [hl, canonical810 B hB] at h
  have hc0 : mixedMoment B raw810 (Fin.cases (0 : Fin 2) singletonSmall4175) =
      mixedMoment B node603 node603Labels := by
    have ha : raw810 = raw811 := by apply Matrix.ext; unfold raw810 raw811; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4175 = raw811Labels := by decide +kernel
    rw [ha, hj, canonical811 B hB]
  have hc1 : mixedMoment B raw810 (Fin.cases (1 : Fin 2) singletonSmall4175) =
      mixedMoment B node1517 node1517Labels := by
    have ha : raw810 = raw812 := by apply Matrix.ext; unfold raw810 raw812; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4175 = raw812Labels := by decide +kernel
    rw [ha, hj, canonical812 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4183 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4183 node4183Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node611 node611Labels + mixedMoment B node1535 node1535Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw825 singletonSmall4183
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4183) = raw825Labels := by decide +kernel
  rw [hl, canonical825 B hB] at h
  have hc0 : mixedMoment B raw825 (Fin.cases (0 : Fin 2) singletonSmall4183) =
      mixedMoment B node611 node611Labels := by
    have ha : raw825 = raw826 := by apply Matrix.ext; unfold raw825 raw826; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4183 = raw826Labels := by decide +kernel
    rw [ha, hj, canonical826 B hB]
  have hc1 : mixedMoment B raw825 (Fin.cases (1 : Fin 2) singletonSmall4183) =
      mixedMoment B node1535 node1535Labels := by
    have ha : raw825 = raw827 := by apply Matrix.ext; unfold raw825 raw827; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4183 = raw827Labels := by decide +kernel
    rw [ha, hj, canonical827 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4186 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4186 node4186Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node614 node614Labels + mixedMoment B node1536 node1536Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw831 singletonSmall4186
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4186) = raw831Labels := by decide +kernel
  rw [hl, canonical831 B hB] at h
  have hc0 : mixedMoment B raw831 (Fin.cases (0 : Fin 2) singletonSmall4186) =
      mixedMoment B node614 node614Labels := by
    have ha : raw831 = raw832 := by apply Matrix.ext; unfold raw831 raw832; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4186 = raw832Labels := by decide +kernel
    rw [ha, hj, canonical832 B hB]
  have hc1 : mixedMoment B raw831 (Fin.cases (1 : Fin 2) singletonSmall4186) =
      mixedMoment B node1536 node1536Labels := by
    have ha : raw831 = raw833 := by apply Matrix.ext; unfold raw831 raw833; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4186 = raw833Labels := by decide +kernel
    rw [ha, hj, canonical833 B hB]
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

theorem singleton4344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4344 node4344Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node922 node922Labels + mixedMoment B node1673 node1673Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1128 singletonSmall4344
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4344) = raw1128Labels := by decide +kernel
  rw [hl, canonical1128 B hB] at h
  have hc0 : mixedMoment B raw1128 (Fin.cases (0 : Fin 2) singletonSmall4344) =
      mixedMoment B node922 node922Labels := by
    have ha : raw1128 = raw1129 := by apply Matrix.ext; unfold raw1128 raw1129; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4344 = raw1129Labels := by decide +kernel
    rw [ha, hj, canonical1129 B hB]
  have hc1 : mixedMoment B raw1128 (Fin.cases (1 : Fin 2) singletonSmall4344) =
      mixedMoment B node1673 node1673Labels := by
    have ha : raw1128 = raw1130 := by apply Matrix.ext; unfold raw1128 raw1130; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4344 = raw1130Labels := by decide +kernel
    rw [ha, hj, canonical1130 B hB]
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

theorem singleton4352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4352 node4352Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node930 node930Labels + mixedMoment B node1690 node1690Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1143 singletonSmall4352
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4352) = raw1143Labels := by decide +kernel
  rw [hl, canonical1143 B hB] at h
  have hc0 : mixedMoment B raw1143 (Fin.cases (0 : Fin 2) singletonSmall4352) =
      mixedMoment B node930 node930Labels := by
    have ha : raw1143 = raw1144 := by apply Matrix.ext; unfold raw1143 raw1144; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4352 = raw1144Labels := by decide +kernel
    rw [ha, hj, canonical1144 B hB]
  have hc1 : mixedMoment B raw1143 (Fin.cases (1 : Fin 2) singletonSmall4352) =
      mixedMoment B node1690 node1690Labels := by
    have ha : raw1143 = raw1145 := by apply Matrix.ext; unfold raw1143 raw1145; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4352 = raw1145Labels := by decide +kernel
    rw [ha, hj, canonical1145 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4355 node4355Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node933 node933Labels + mixedMoment B node1691 node1691Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1149 singletonSmall4355
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4355) = raw1149Labels := by decide +kernel
  rw [hl, canonical1149 B hB] at h
  have hc0 : mixedMoment B raw1149 (Fin.cases (0 : Fin 2) singletonSmall4355) =
      mixedMoment B node933 node933Labels := by
    have ha : raw1149 = raw1150 := by apply Matrix.ext; unfold raw1149 raw1150; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4355 = raw1150Labels := by decide +kernel
    rw [ha, hj, canonical1150 B hB]
  have hc1 : mixedMoment B raw1149 (Fin.cases (1 : Fin 2) singletonSmall4355) =
      mixedMoment B node1691 node1691Labels := by
    have ha : raw1149 = raw1151 := by apply Matrix.ext; unfold raw1149 raw1151; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4355 = raw1151Labels := by decide +kernel
    rw [ha, hj, canonical1151 B hB]
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

theorem singleton4458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4458 node4458Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1041 node1041Labels + mixedMoment B node1724 node1724Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1260 singletonSmall4458
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4458) = raw1260Labels := by decide +kernel
  rw [hl, canonical1260 B hB] at h
  have hc0 : mixedMoment B raw1260 (Fin.cases (0 : Fin 2) singletonSmall4458) =
      mixedMoment B node1041 node1041Labels := by
    have ha : raw1260 = raw1261 := by apply Matrix.ext; unfold raw1260 raw1261; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4458 = raw1261Labels := by decide +kernel
    rw [ha, hj, canonical1261 B hB]
  have hc1 : mixedMoment B raw1260 (Fin.cases (1 : Fin 2) singletonSmall4458) =
      mixedMoment B node1724 node1724Labels := by
    have ha : raw1260 = raw1262 := by apply Matrix.ext; unfold raw1260 raw1262; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4458 = raw1262Labels := by decide +kernel
    rw [ha, hj, canonical1262 B hB]
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

theorem singleton4467 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4467 node4467Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1050 node1050Labels + mixedMoment B node1751 node1751Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1275 singletonSmall4467
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4467) = raw1275Labels := by decide +kernel
  rw [hl, canonical1275 B hB] at h
  have hc0 : mixedMoment B raw1275 (Fin.cases (0 : Fin 2) singletonSmall4467) =
      mixedMoment B node1050 node1050Labels := by
    have ha : raw1275 = raw1276 := by apply Matrix.ext; unfold raw1275 raw1276; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4467 = raw1276Labels := by decide +kernel
    rw [ha, hj, canonical1276 B hB]
  have hc1 : mixedMoment B raw1275 (Fin.cases (1 : Fin 2) singletonSmall4467) =
      mixedMoment B node1751 node1751Labels := by
    have ha : raw1275 = raw1277 := by apply Matrix.ext; unfold raw1275 raw1277; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4467 = raw1277Labels := by decide +kernel
    rw [ha, hj, canonical1277 B hB]
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

theorem sound922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node922 node922Labels = Sparse.eval nodeValue922 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 922) = mixedMoment B node922 node922Labels := rfl
  simpa [nodeValue922, Sparse.eval] using hc.symm

theorem sound930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node930 node930Labels = Sparse.eval nodeValue930 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 930) = mixedMoment B node930 node930Labels := rfl
  simpa [nodeValue930, Sparse.eval] using hc.symm

theorem sound933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node933 node933Labels = Sparse.eval nodeValue933 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 933) = mixedMoment B node933 node933Labels := rfl
  simpa [nodeValue933, Sparse.eval] using hc.symm

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

theorem sound1041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1041 node1041Labels = Sparse.eval nodeValue1041 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1041) = mixedMoment B node1041 node1041Labels := rfl
  simpa [nodeValue1041, Sparse.eval] using hc.symm

theorem sound1046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1046 node1046Labels = Sparse.eval nodeValue1046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1046) = mixedMoment B node1046 node1046Labels := rfl
  simpa [nodeValue1046, Sparse.eval] using hc.symm

theorem sound1050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1050 node1050Labels = Sparse.eval nodeValue1050 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1050) = mixedMoment B node1050 node1050Labels := rfl
  simpa [nodeValue1050, Sparse.eval] using hc.symm

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

theorem sound1517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1517 node1517Labels = Sparse.eval nodeValue1517 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1517) = mixedMoment B node1517 node1517Labels := rfl
  simpa [nodeValue1517, Sparse.eval] using hc.symm

theorem sound1535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1535 node1535Labels = Sparse.eval nodeValue1535 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1535) = mixedMoment B node1535 node1535Labels := rfl
  simpa [nodeValue1535, Sparse.eval] using hc.symm

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

theorem sound1536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1536 node1536Labels = Sparse.eval nodeValue1536 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1536) = mixedMoment B node1536 node1536Labels := rfl
  simpa [nodeValue1536, Sparse.eval] using hc.symm

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

theorem sound1673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1673 node1673Labels = Sparse.eval nodeValue1673 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1673) = mixedMoment B node1673 node1673Labels := rfl
  simpa [nodeValue1673, Sparse.eval] using hc.symm

theorem sound1690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1690 node1690Labels = Sparse.eval nodeValue1690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1690) = mixedMoment B node1690 node1690Labels := rfl
  simpa [nodeValue1690, Sparse.eval] using hc.symm

theorem sound1691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1691 node1691Labels = Sparse.eval nodeValue1691 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1691) = mixedMoment B node1691 node1691Labels := rfl
  simpa [nodeValue1691, Sparse.eval] using hc.symm

theorem sound1724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1724 node1724Labels = Sparse.eval nodeValue1724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1724) = mixedMoment B node1724 node1724Labels := rfl
  simpa [nodeValue1724, Sparse.eval] using hc.symm

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

theorem sound1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1750 node1750Labels = Sparse.eval nodeValue1750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1750) = mixedMoment B node1750 node1750Labels := rfl
  simpa [nodeValue1750, Sparse.eval] using hc.symm

theorem sound1751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1751 node1751Labels = Sparse.eval nodeValue1751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1751) = mixedMoment B node1751 node1751Labels := rfl
  simpa [nodeValue1751, Sparse.eval] using hc.symm

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

theorem sound4083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4083 node4083Labels = Sparse.eval nodeValue4083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4083) = mixedMoment B node4083 node4083Labels := rfl
  simpa [nodeValue4083, Sparse.eval] using hc.symm

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

theorem sound603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node603 node603Labels = Sparse.eval nodeValue603 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 603) = mixedMoment B node603 node603Labels := rfl
  simpa [nodeValue603, Sparse.eval] using hc.symm

theorem sound611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node611 node611Labels = Sparse.eval nodeValue611 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 611) = mixedMoment B node611 node611Labels := rfl
  simpa [nodeValue611, Sparse.eval] using hc.symm

theorem sound614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node614 node614Labels = Sparse.eval nodeValue614 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 614) = mixedMoment B node614 node614Labels := rfl
  simpa [nodeValue614, Sparse.eval] using hc.symm

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

theorem sound4175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4175 node4175Labels = Sparse.eval nodeValue4175 (mixedVector B) := by
  have h := singleton4175 B _hB
  rw [sound603 B _hB _hF, sound1517 B _hB _hF] at h
  norm_num [nodeValue4175, nodeValue603, nodeValue1517, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4183 node4183Labels = Sparse.eval nodeValue4183 (mixedVector B) := by
  have h := singleton4183 B _hB
  rw [sound611 B _hB _hF, sound1535 B _hB _hF] at h
  norm_num [nodeValue4183, nodeValue611, nodeValue1535, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4186 node4186Labels = Sparse.eval nodeValue4186 (mixedVector B) := by
  have h := singleton4186 B _hB
  rw [sound614 B _hB _hF, sound1536 B _hB _hF] at h
  norm_num [nodeValue4186, nodeValue614, nodeValue1536, Sparse.eval] at h ⊢
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

theorem sound4344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4344 node4344Labels = Sparse.eval nodeValue4344 (mixedVector B) := by
  have h := singleton4344 B _hB
  rw [sound922 B _hB _hF, sound1673 B _hB _hF] at h
  norm_num [nodeValue4344, nodeValue922, nodeValue1673, Sparse.eval] at h ⊢
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

theorem sound4352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4352 node4352Labels = Sparse.eval nodeValue4352 (mixedVector B) := by
  have h := singleton4352 B _hB
  rw [sound930 B _hB _hF, sound1690 B _hB _hF] at h
  norm_num [nodeValue4352, nodeValue930, nodeValue1690, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4355 node4355Labels = Sparse.eval nodeValue4355 (mixedVector B) := by
  have h := singleton4355 B _hB
  rw [sound933 B _hB _hF, sound1691 B _hB _hF] at h
  norm_num [nodeValue4355, nodeValue933, nodeValue1691, Sparse.eval] at h ⊢
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

theorem sound4458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4458 node4458Labels = Sparse.eval nodeValue4458 (mixedVector B) := by
  have h := singleton4458 B _hB
  rw [sound1041 B _hB _hF, sound1724 B _hB _hF] at h
  norm_num [nodeValue4458, nodeValue1041, nodeValue1724, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4463 node4463Labels = Sparse.eval nodeValue4463 (mixedVector B) := by
  have h := singleton4463 B _hB
  rw [sound1046 B _hB _hF, sound1750 B _hB _hF] at h
  norm_num [nodeValue4463, nodeValue1046, nodeValue1750, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4467 node4467Labels = Sparse.eval nodeValue4467 (mixedVector B) := by
  have h := singleton4467 B _hB
  rw [sound1050 B _hB _hF, sound1751 B _hB _hF] at h
  norm_num [nodeValue4467, nodeValue1050, nodeValue1751, Sparse.eval] at h ⊢
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

theorem zero4497 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4497 node4497Labels = 0 := by
  exact mixedMoment_order_one B hB node4497 node4497Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4502 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4502 node4502Labels = 0 := by
  exact mixedMoment_order_one B hB node4502 node4502Labels 1
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

theorem sound4497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4497 node4497Labels = Sparse.eval nodeValue4497 (mixedVector B) := by
  simpa only [nodeValue4497, Sparse.eval_nil] using zero4497 B _hB _hF

theorem sound4502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4502 node4502Labels = Sparse.eval nodeValue4502 (mixedVector B) := by
  simpa only [nodeValue4502, Sparse.eval_nil] using zero4502 B _hB _hF

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

theorem sound4838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4838 node4838Labels = Sparse.eval nodeValue4838 (mixedVector B) := by
  simpa only [nodeValue4838, Sparse.eval_nil] using zero4838 B _hB _hF

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

theorem sound4895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4895 node4895Labels = Sparse.eval nodeValue4895 (mixedVector B) := by
  simpa only [nodeValue4895, Sparse.eval_nil] using zero4895 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources55
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1781 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1781 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1781 + difference 0 1) (sourceB1781 + difference 1 0) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA1781 + difference 0 1) (sourceB1781 + difference 1 0) sourceC1781) = raw25855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25855; decide +kernel
    rw [ha]
    exact (canonical25855 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1781 + difference 0 2) (sourceB1781 + difference 2 0) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA1781 + difference 0 2) (sourceB1781 + difference 2 0) sourceC1781) = raw25856 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25856; decide +kernel
    rw [ha]
    exact (canonical25856 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1781 + difference 0 3) (sourceB1781 + difference 3 0) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1781 + difference 0 3) (sourceB1781 + difference 3 0) sourceC1781) = raw25857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25857; decide +kernel
    rw [ha]
    exact (canonical25857 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1781 + difference 0 4) (sourceB1781 + difference 4 0) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1781 + difference 0 4) (sourceB1781 + difference 4 0) sourceC1781) = raw25858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25858; decide +kernel
    rw [ha]
    exact (canonical25858 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1781 + difference 0 5) (sourceB1781 + difference 5 0) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA1781 + difference 0 5) (sourceB1781 + difference 5 0) sourceC1781) = raw25859 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25859; decide +kernel
    rw [ha]
    exact (canonical25859 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1781 + difference 1 0) (sourceB1781 + difference 0 1) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4175) := by
    have ha : (tripleCharges (sourceA1781 + difference 1 0) (sourceB1781 + difference 0 1) sourceC1781) = raw25860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25860; decide +kernel
    rw [ha]
    exact (canonical25860 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1781 + difference 1 2) (sourceB1781 + difference 2 1) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4344) := by
    have ha : (tripleCharges (sourceA1781 + difference 1 2) (sourceB1781 + difference 2 1) sourceC1781) = raw25861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25861; decide +kernel
    rw [ha]
    exact (canonical25861 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1781 + difference 1 3) (sourceB1781 + difference 3 1) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1781 + difference 1 3) (sourceB1781 + difference 3 1) sourceC1781) = raw25862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25862; decide +kernel
    rw [ha]
    exact (canonical25862 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1781 + difference 1 4) (sourceB1781 + difference 4 1) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1781 + difference 1 4) (sourceB1781 + difference 4 1) sourceC1781) = raw25863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25863; decide +kernel
    rw [ha]
    exact (canonical25863 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1781 + difference 1 5) (sourceB1781 + difference 5 1) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1781 + difference 1 5) (sourceB1781 + difference 5 1) sourceC1781) = raw25864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25864; decide +kernel
    rw [ha]
    exact (canonical25864 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1781 + difference 2 0) (sourceB1781 + difference 0 2) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4175) := by
    have ha : (tripleCharges (sourceA1781 + difference 2 0) (sourceB1781 + difference 0 2) sourceC1781) = raw25865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25865; decide +kernel
    rw [ha]
    exact (canonical25865 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1781 + difference 2 1) (sourceB1781 + difference 1 2) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4344) := by
    have ha : (tripleCharges (sourceA1781 + difference 2 1) (sourceB1781 + difference 1 2) sourceC1781) = raw25866 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25866; decide +kernel
    rw [ha]
    exact (canonical25866 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1781 + difference 2 3) (sourceB1781 + difference 3 2) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1781 + difference 2 3) (sourceB1781 + difference 3 2) sourceC1781) = raw25867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25867; decide +kernel
    rw [ha]
    exact (canonical25867 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1781 + difference 2 4) (sourceB1781 + difference 4 2) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1781 + difference 2 4) (sourceB1781 + difference 4 2) sourceC1781) = raw25868 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25868; decide +kernel
    rw [ha]
    exact (canonical25868 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1781 + difference 2 5) (sourceB1781 + difference 5 2) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1781 + difference 2 5) (sourceB1781 + difference 5 2) sourceC1781) = raw25869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25869; decide +kernel
    rw [ha]
    exact (canonical25869 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1781 + difference 3 0) (sourceB1781 + difference 0 3) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4186) := by
    have ha : (tripleCharges (sourceA1781 + difference 3 0) (sourceB1781 + difference 0 3) sourceC1781) = raw25870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25870; decide +kernel
    rw [ha]
    exact (canonical25870 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1781 + difference 3 1) (sourceB1781 + difference 1 3) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA1781 + difference 3 1) (sourceB1781 + difference 1 3) sourceC1781) = raw25871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25871; decide +kernel
    rw [ha]
    exact (canonical25871 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1781 + difference 3 2) (sourceB1781 + difference 2 3) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA1781 + difference 3 2) (sourceB1781 + difference 2 3) sourceC1781) = raw25872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25872; decide +kernel
    rw [ha]
    exact (canonical25872 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1781 + difference 3 4) (sourceB1781 + difference 4 3) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1781 + difference 3 4) (sourceB1781 + difference 4 3) sourceC1781) = raw25873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25873; decide +kernel
    rw [ha]
    exact (canonical25873 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1781 + difference 3 5) (sourceB1781 + difference 5 3) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1781 + difference 3 5) (sourceB1781 + difference 5 3) sourceC1781) = raw25874 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25874; decide +kernel
    rw [ha]
    exact (canonical25874 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1781 + difference 4 0) (sourceB1781 + difference 0 4) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4186) := by
    have ha : (tripleCharges (sourceA1781 + difference 4 0) (sourceB1781 + difference 0 4) sourceC1781) = raw25875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25875; decide +kernel
    rw [ha]
    exact (canonical25875 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1781 + difference 4 1) (sourceB1781 + difference 1 4) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA1781 + difference 4 1) (sourceB1781 + difference 1 4) sourceC1781) = raw25876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25876; decide +kernel
    rw [ha]
    exact (canonical25876 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1781 + difference 4 2) (sourceB1781 + difference 2 4) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA1781 + difference 4 2) (sourceB1781 + difference 2 4) sourceC1781) = raw25877 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25877; decide +kernel
    rw [ha]
    exact (canonical25877 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1781 + difference 4 3) (sourceB1781 + difference 3 4) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1781 + difference 4 3) (sourceB1781 + difference 3 4) sourceC1781) = raw25878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25878; decide +kernel
    rw [ha]
    exact (canonical25878 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1781 + difference 4 5) (sourceB1781 + difference 5 4) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1781 + difference 4 5) (sourceB1781 + difference 5 4) sourceC1781) = raw25879 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25879; decide +kernel
    rw [ha]
    exact (canonical25879 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1781 + difference 5 0) (sourceB1781 + difference 0 5) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4183) := by
    have ha : (tripleCharges (sourceA1781 + difference 5 0) (sourceB1781 + difference 0 5) sourceC1781) = raw25880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25880; decide +kernel
    rw [ha]
    exact (canonical25880 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1781 + difference 5 1) (sourceB1781 + difference 1 5) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4352) := by
    have ha : (tripleCharges (sourceA1781 + difference 5 1) (sourceB1781 + difference 1 5) sourceC1781) = raw25881 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25881; decide +kernel
    rw [ha]
    exact (canonical25881 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1781 + difference 5 2) (sourceB1781 + difference 2 5) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4352) := by
    have ha : (tripleCharges (sourceA1781 + difference 5 2) (sourceB1781 + difference 2 5) sourceC1781) = raw25882 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25882; decide +kernel
    rw [ha]
    exact (canonical25882 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1781 + difference 5 3) (sourceB1781 + difference 3 5) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1781 + difference 5 3) (sourceB1781 + difference 3 5) sourceC1781) = raw25883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25883; decide +kernel
    rw [ha]
    exact (canonical25883 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1781 + difference 5 4) (sourceB1781 + difference 4 5) sourceC1781) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1781 + difference 5 4) (sourceB1781 + difference 4 5) sourceC1781) = raw25884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1781 sourceB1781 sourceC1781 difference raw25884; decide +kernel
    rw [ha]
    exact (canonical25884 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1781 sourceB1781 sourceC1781
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1781, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1513 : Integer.Sparse.reindex keyMap MixedData.row1513 = numericRow1513 := by decide +kernel

theorem numericCheck1513 (x : Master → ℝ) : Integer.Sparse.eval numericRow1513 x =
    (4 : ℝ) * reducedSource1513 x := by
  norm_num [numericRow1513, reducedSource1513, Integer.Sparse.eval, Sparse.eval, nodeValue4083, nodeValue4175, nodeValue4183, nodeValue4186, nodeValue4344, nodeValue4352, nodeValue4355, nodeValue4458, nodeValue4463, nodeValue4467, nodeValue4497, nodeValue4502, nodeValue4838, nodeValue4895]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows94
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1513 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1513 (mixedVector B) = 0 := by
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  have h4175 : mixedVector B (Sum.inr 4175) = Sparse.eval nodeValue4175 (mixedVector B) := by
    change mixedMoment B node4175 node4175Labels = _
    exact sound4175 B hB hF
  have h4183 : mixedVector B (Sum.inr 4183) = Sparse.eval nodeValue4183 (mixedVector B) := by
    change mixedMoment B node4183 node4183Labels = _
    exact sound4183 B hB hF
  have h4186 : mixedVector B (Sum.inr 4186) = Sparse.eval nodeValue4186 (mixedVector B) := by
    change mixedMoment B node4186 node4186Labels = _
    exact sound4186 B hB hF
  have h4344 : mixedVector B (Sum.inr 4344) = Sparse.eval nodeValue4344 (mixedVector B) := by
    change mixedMoment B node4344 node4344Labels = _
    exact sound4344 B hB hF
  have h4352 : mixedVector B (Sum.inr 4352) = Sparse.eval nodeValue4352 (mixedVector B) := by
    change mixedMoment B node4352 node4352Labels = _
    exact sound4352 B hB hF
  have h4355 : mixedVector B (Sum.inr 4355) = Sparse.eval nodeValue4355 (mixedVector B) := by
    change mixedMoment B node4355 node4355Labels = _
    exact sound4355 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4467 : mixedVector B (Sum.inr 4467) = Sparse.eval nodeValue4467 (mixedVector B) := by
    change mixedMoment B node4467 node4467Labels = _
    exact sound4467 B hB hF
  have h4497 : mixedVector B (Sum.inr 4497) = Sparse.eval nodeValue4497 (mixedVector B) := by
    change mixedMoment B node4497 node4497Labels = _
    exact sound4497 B hB hF
  have h4502 : mixedVector B (Sum.inr 4502) = Sparse.eval nodeValue4502 (mixedVector B) := by
    change mixedMoment B node4502 node4502Labels = _
    exact sound4502 B hB hF
  have h4838 : mixedVector B (Sum.inr 4838) = Sparse.eval nodeValue4838 (mixedVector B) := by
    change mixedMoment B node4838 node4838Labels = _
    exact sound4838 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  simpa only [sourceForm1781, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4083, h4175, h4183, h4186, h4344, h4352, h4355, h4458, h4463, h4467, h4497, h4502, h4838, h4895, reducedSource1513] using sourceEq1781 B hB

theorem rowSound1513_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1513 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1513, numericCheck1513, reducedZero1513 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1513_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1513_e_oai
