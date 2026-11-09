-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1514_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:13:15.875234+00:00
-- url     : https://prove2.me/submissions/8ad5ac72-460a-4aa4-854b-4ded912caae0

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1293 raw1293Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw1293 raw1293Labels = mixedMoment B raw1293step0 raw1293step0Labels := by
      have ha : raw1293step0 = (fun i j => raw1293 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1293step0 raw1293; decide +kernel
      have hl : raw1293step0Labels = raw1293Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1293 raw1293Labels permutation32 permutation4
    mixedMoment B raw1293step0 raw1293step0Labels = mixedMoment B raw1293step1 raw1293step1Labels := by
      have ha : raw1293step1 = raw1293step0 := by apply Matrix.ext; unfold raw1293step1 raw1293step0; decide +kernel
      have hl : raw1293step0Labels = labelEmbedding7 ∘ raw1293step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1293step0 raw1293step0Labels raw1293step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

theorem canonical1294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1294 raw1294Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw1294 raw1294Labels = mixedMoment B raw1294step0 raw1294step0Labels := by
      have ha : raw1294step0 = (fun i j => raw1294 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1294step0 raw1294; decide +kernel
      have hl : raw1294step0Labels = raw1294Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1294 raw1294Labels permutation32 permutation4
    _ = mixedMoment B node1079 node1079Labels := by rfl

theorem canonical1295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1295 raw1295Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw1295 raw1295Labels = mixedMoment B raw1295step0 raw1295step0Labels := by
      have ha : raw1295step0 = (fun i j => raw1295 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1295step0 raw1295; decide +kernel
      have hl : raw1295step0Labels = raw1295Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1295 raw1295Labels permutation32 permutation6
    mixedMoment B raw1295step0 raw1295step0Labels = mixedMoment B raw1295step1 raw1295step1Labels := by
      have ha : raw1295step1 = -raw1295step0 := by apply Matrix.ext; change ∀ i j, raw1295step1 i j = -(raw1295step0 i j); unfold raw1295step1 raw1295step0; decide +kernel
      have hl : raw1295step1Labels = raw1295step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1295step1 raw1295step1Labels = mixedMoment B raw1295step2 raw1295step2Labels := by
      have ha : raw1295step2 = raw1295step1 := by apply Matrix.ext; unfold raw1295step2 raw1295step1; decide +kernel
      have hl : raw1295step1Labels = labelEmbedding1 ∘ raw1295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1295step1 raw1295step1Labels raw1295step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical202
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25885 raw25885Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw25885 raw25885Labels = mixedMoment B raw25885step0 raw25885step0Labels := by
      have hz : ∀ j, raw25885 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25885step0 = (fun i j => raw25885 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25885step0 raw25885; decide +kernel
      have hl : raw25885step0Labels = raw25885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25885 raw25885Labels permutation346 hz
    mixedMoment B raw25885step0 raw25885step0Labels = mixedMoment B raw25885step1 raw25885step1Labels := by
      have ha : raw25885step1 = (fun i j => raw25885step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25885step1 raw25885step0; decide +kernel
      have hl : raw25885step1Labels = raw25885step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25885step0 raw25885step0Labels permutation34 permutation2
    _ = mixedMoment B node4834 node4834Labels := by rfl

theorem canonical25886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25886 raw25886Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw25886 raw25886Labels = mixedMoment B raw25886step0 raw25886step0Labels := by
      have hz : ∀ j, raw25886 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25886step0 = (fun i j => raw25886 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25886step0 raw25886; decide +kernel
      have hl : raw25886step0Labels = raw25886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25886 raw25886Labels permutation265 hz
    mixedMoment B raw25886step0 raw25886step0Labels = mixedMoment B raw25886step1 raw25886step1Labels := by
      have ha : raw25886step1 = (fun i j => raw25886step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25886step1 raw25886step0; decide +kernel
      have hl : raw25886step1Labels = raw25886step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25886step0 raw25886step0Labels permutation34 permutation2
    _ = mixedMoment B node4834 node4834Labels := by rfl

theorem canonical25887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25887 raw25887Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw25887 raw25887Labels = mixedMoment B raw25887step0 raw25887step0Labels := by
      have hz : ∀ j, raw25887 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25887step0 = (fun i j => raw25887 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25887step0 raw25887; decide +kernel
      have hl : raw25887step0Labels = raw25887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25887 raw25887Labels permutation346 hz
    mixedMoment B raw25887step0 raw25887step0Labels = mixedMoment B raw25887step1 raw25887step1Labels := by
      have hz : ∀ j, raw25887step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25887step1 = (fun i j => raw25887step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25887step1 raw25887step0; decide +kernel
      have hl : raw25887step1Labels = raw25887step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25887step0 raw25887step0Labels permutation56 hz
    _ = mixedMoment B node4894 node4894Labels := by rfl

theorem canonical25888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25888 raw25888Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw25888 raw25888Labels = mixedMoment B raw25888step0 raw25888step0Labels := by
      have hz : ∀ j, raw25888 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25888step0 = (fun i j => raw25888 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25888step0 raw25888; decide +kernel
      have hl : raw25888step0Labels = raw25888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25888 raw25888Labels permutation520 hz
    mixedMoment B raw25888step0 raw25888step0Labels = mixedMoment B raw25888step1 raw25888step1Labels := by
      have hz : ∀ j, raw25888step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25888step1 = (fun i j => raw25888step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25888step1 raw25888step0; decide +kernel
      have hl : raw25888step1Labels = raw25888step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25888step0 raw25888step0Labels permutation80 hz
    mixedMoment B raw25888step1 raw25888step1Labels = mixedMoment B raw25888step2 raw25888step2Labels := by
      have hz : ∀ j, raw25888step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25888step2 = (fun i j => raw25888step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25888step2 raw25888step1; decide +kernel
      have hl : raw25888step2Labels = raw25888step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25888step1 raw25888step1Labels permutation14 hz
    mixedMoment B raw25888step2 raw25888step2Labels = mixedMoment B raw25888step3 raw25888step3Labels := by
      have hz : ∀ i, raw25888step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw25888step3 = (fun i j => raw25888step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw25888step3 raw25888step2; decide +kernel
      have hl : raw25888step3Labels = (fun j => raw25888step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw25888step2 raw25888step2Labels permutation4 hz
    mixedMoment B raw25888step3 raw25888step3Labels = mixedMoment B raw25888step4 raw25888step4Labels := by
      have ha : raw25888step4 = raw25888step3 := by apply Matrix.ext; unfold raw25888step4 raw25888step3; decide +kernel
      have hl : raw25888step3Labels = labelEmbedding2 ∘ raw25888step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25888step3 raw25888step3Labels raw25888step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical25889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25889 raw25889Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw25889 raw25889Labels = mixedMoment B raw25889step0 raw25889step0Labels := by
      have hz : ∀ j, raw25889 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25889step0 = (fun i j => raw25889 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25889step0 raw25889; decide +kernel
      have hl : raw25889step0Labels = raw25889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25889 raw25889Labels permutation346 hz
    mixedMoment B raw25889step0 raw25889step0Labels = mixedMoment B raw25889step1 raw25889step1Labels := by
      have hz : ∀ j, raw25889step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25889step1 = (fun i j => raw25889step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25889step1 raw25889step0; decide +kernel
      have hl : raw25889step1Labels = raw25889step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25889step0 raw25889step0Labels permutation56 hz
    mixedMoment B raw25889step1 raw25889step1Labels = mixedMoment B raw25889step2 raw25889step2Labels := by
      have ha : raw25889step2 = (fun i j => raw25889step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25889step2 raw25889step1; decide +kernel
      have hl : raw25889step2Labels = raw25889step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25889step1 raw25889step1Labels permutation10 permutation7
    mixedMoment B raw25889step2 raw25889step2Labels = mixedMoment B raw25889step3 raw25889step3Labels := by
      have ha : raw25889step3 = -raw25889step2 := by apply Matrix.ext; change ∀ i j, raw25889step3 i j = -(raw25889step2 i j); unfold raw25889step3 raw25889step2; decide +kernel
      have hl : raw25889step3Labels = raw25889step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25889step3 raw25889step3Labels = mixedMoment B raw25889step4 raw25889step4Labels := by
      have ha : raw25889step4 = raw25889step3 := by apply Matrix.ext; unfold raw25889step4 raw25889step3; decide +kernel
      have hl : raw25889step3Labels = labelEmbedding10 ∘ raw25889step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25889step3 raw25889step3Labels raw25889step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

theorem canonical25890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25890 raw25890Labels = mixedMoment B node4172 node4172Labels := by
  calc
    mixedMoment B raw25890 raw25890Labels = mixedMoment B raw25890step0 raw25890step0Labels := by
      have hz : ∀ j, raw25890 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25890step0 = (fun i j => raw25890 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25890step0 raw25890; decide +kernel
      have hl : raw25890step0Labels = raw25890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25890 raw25890Labels permutation346 hz
    mixedMoment B raw25890step0 raw25890step0Labels = mixedMoment B raw25890step1 raw25890step1Labels := by
      have ha : raw25890step1 = (fun i j => raw25890step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25890step1 raw25890step0; decide +kernel
      have hl : raw25890step1Labels = raw25890step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25890step0 raw25890step0Labels permutation34 permutation2
    _ = mixedMoment B node4172 node4172Labels := by rfl

theorem canonical25891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25891 raw25891Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw25891 raw25891Labels = mixedMoment B raw25891step0 raw25891step0Labels := by
      have ha : raw25891step0 = (fun i j => raw25891 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25891step0 raw25891; decide +kernel
      have hl : raw25891step0Labels = raw25891Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25891 raw25891Labels permutation178 permutation2
    _ = mixedMoment B node4341 node4341Labels := by rfl

theorem canonical25892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25892 raw25892Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw25892 raw25892Labels = mixedMoment B raw25892step0 raw25892step0Labels := by
      have hz : ∀ j, raw25892 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25892step0 = (fun i j => raw25892 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25892step0 raw25892; decide +kernel
      have hl : raw25892step0Labels = raw25892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25892 raw25892Labels permutation346 hz
    mixedMoment B raw25892step0 raw25892step0Labels = mixedMoment B raw25892step1 raw25892step1Labels := by
      have ha : raw25892step1 = (fun i j => raw25892step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25892step1 raw25892step0; decide +kernel
      have hl : raw25892step1Labels = raw25892step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25892step0 raw25892step0Labels permutation38 permutation2
    _ = mixedMoment B node4457 node4457Labels := by rfl

theorem canonical25893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25893 raw25893Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw25893 raw25893Labels = mixedMoment B raw25893step0 raw25893step0Labels := by
      have hz : ∀ j, raw25893 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25893step0 = (fun i j => raw25893 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25893step0 raw25893; decide +kernel
      have hl : raw25893step0Labels = raw25893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25893 raw25893Labels permutation520 hz
    mixedMoment B raw25893step0 raw25893step0Labels = mixedMoment B raw25893step1 raw25893step1Labels := by
      have hz : ∀ j, raw25893step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25893step1 = (fun i j => raw25893step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25893step1 raw25893step0; decide +kernel
      have hl : raw25893step1Labels = raw25893step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25893step0 raw25893step0Labels permutation80 hz
    _ = mixedMoment B node4498 node4498Labels := by rfl

theorem canonical25894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25894 raw25894Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw25894 raw25894Labels = mixedMoment B raw25894step0 raw25894step0Labels := by
      have hz : ∀ j, raw25894 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25894step0 = (fun i j => raw25894 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25894step0 raw25894; decide +kernel
      have hl : raw25894step0Labels = raw25894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25894 raw25894Labels permutation346 hz
    mixedMoment B raw25894step0 raw25894step0Labels = mixedMoment B raw25894step1 raw25894step1Labels := by
      have ha : raw25894step1 = (fun i j => raw25894step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25894step1 raw25894step0; decide +kernel
      have hl : raw25894step1Labels = raw25894step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25894step0 raw25894step0Labels permutation34 permutation2
    _ = mixedMoment B node4495 node4495Labels := by rfl

theorem canonical25895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25895 raw25895Labels = mixedMoment B node4172 node4172Labels := by
  calc
    mixedMoment B raw25895 raw25895Labels = mixedMoment B raw25895step0 raw25895step0Labels := by
      have hz : ∀ j, raw25895 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25895step0 = (fun i j => raw25895 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25895step0 raw25895; decide +kernel
      have hl : raw25895step0Labels = raw25895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25895 raw25895Labels permutation265 hz
    mixedMoment B raw25895step0 raw25895step0Labels = mixedMoment B raw25895step1 raw25895step1Labels := by
      have ha : raw25895step1 = (fun i j => raw25895step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25895step1 raw25895step0; decide +kernel
      have hl : raw25895step1Labels = raw25895step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25895step0 raw25895step0Labels permutation34 permutation2
    _ = mixedMoment B node4172 node4172Labels := by rfl

theorem canonical25896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25896 raw25896Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw25896 raw25896Labels = mixedMoment B raw25896step0 raw25896step0Labels := by
      have ha : raw25896step0 = (fun i j => raw25896 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25896step0 raw25896; decide +kernel
      have hl : raw25896step0Labels = raw25896Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25896 raw25896Labels permutation154 permutation2
    _ = mixedMoment B node4341 node4341Labels := by rfl

theorem canonical25897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25897 raw25897Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw25897 raw25897Labels = mixedMoment B raw25897step0 raw25897step0Labels := by
      have hz : ∀ j, raw25897 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25897step0 = (fun i j => raw25897 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25897step0 raw25897; decide +kernel
      have hl : raw25897step0Labels = raw25897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25897 raw25897Labels permutation265 hz
    mixedMoment B raw25897step0 raw25897step0Labels = mixedMoment B raw25897step1 raw25897step1Labels := by
      have ha : raw25897step1 = (fun i j => raw25897step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25897step1 raw25897step0; decide +kernel
      have hl : raw25897step1Labels = raw25897step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25897step0 raw25897step0Labels permutation38 permutation2
    _ = mixedMoment B node4457 node4457Labels := by rfl

theorem canonical25898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25898 raw25898Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw25898 raw25898Labels = mixedMoment B raw25898step0 raw25898step0Labels := by
      have hz : ∀ j, raw25898 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25898step0 = (fun i j => raw25898 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25898step0 raw25898; decide +kernel
      have hl : raw25898step0Labels = raw25898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25898 raw25898Labels permutation520 hz
    mixedMoment B raw25898step0 raw25898step0Labels = mixedMoment B raw25898step1 raw25898step1Labels := by
      have hz : ∀ j, raw25898step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25898step1 = (fun i j => raw25898step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25898step1 raw25898step0; decide +kernel
      have hl : raw25898step1Labels = raw25898step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25898step0 raw25898step0Labels permutation56 hz
    _ = mixedMoment B node4498 node4498Labels := by rfl

theorem canonical25899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25899 raw25899Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw25899 raw25899Labels = mixedMoment B raw25899step0 raw25899step0Labels := by
      have hz : ∀ j, raw25899 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25899step0 = (fun i j => raw25899 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25899step0 raw25899; decide +kernel
      have hl : raw25899step0Labels = raw25899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25899 raw25899Labels permutation265 hz
    mixedMoment B raw25899step0 raw25899step0Labels = mixedMoment B raw25899step1 raw25899step1Labels := by
      have ha : raw25899step1 = (fun i j => raw25899step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25899step1 raw25899step0; decide +kernel
      have hl : raw25899step1Labels = raw25899step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25899step0 raw25899step0Labels permutation34 permutation2
    _ = mixedMoment B node4495 node4495Labels := by rfl

theorem canonical25900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25900 raw25900Labels = mixedMoment B node4180 node4180Labels := by
  calc
    mixedMoment B raw25900 raw25900Labels = mixedMoment B raw25900step0 raw25900step0Labels := by
      have hz : ∀ j, raw25900 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25900step0 = (fun i j => raw25900 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25900step0 raw25900; decide +kernel
      have hl : raw25900step0Labels = raw25900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25900 raw25900Labels permutation346 hz
    mixedMoment B raw25900step0 raw25900step0Labels = mixedMoment B raw25900step1 raw25900step1Labels := by
      have hz : ∀ j, raw25900step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25900step1 = (fun i j => raw25900step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25900step1 raw25900step0; decide +kernel
      have hl : raw25900step1Labels = raw25900step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25900step0 raw25900step0Labels permutation56 hz
    mixedMoment B raw25900step1 raw25900step1Labels = mixedMoment B raw25900step2 raw25900step2Labels := by
      have ha : raw25900step2 = (fun i j => raw25900step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25900step2 raw25900step1; decide +kernel
      have hl : raw25900step2Labels = raw25900step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25900step1 raw25900step1Labels permutation10 permutation2
    _ = mixedMoment B node4180 node4180Labels := by rfl

theorem canonical25901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25901 raw25901Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw25901 raw25901Labels = mixedMoment B raw25901step0 raw25901step0Labels := by
      have hz : ∀ j, raw25901 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25901step0 = (fun i j => raw25901 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25901step0 raw25901; decide +kernel
      have hl : raw25901step0Labels = raw25901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25901 raw25901Labels permutation346 hz
    mixedMoment B raw25901step0 raw25901step0Labels = mixedMoment B raw25901step1 raw25901step1Labels := by
      have ha : raw25901step1 = (fun i j => raw25901step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25901step1 raw25901step0; decide +kernel
      have hl : raw25901step1Labels = raw25901step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25901step0 raw25901step0Labels permutation34 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

theorem canonical25902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25902 raw25902Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw25902 raw25902Labels = mixedMoment B raw25902step0 raw25902step0Labels := by
      have hz : ∀ j, raw25902 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25902step0 = (fun i j => raw25902 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25902step0 raw25902; decide +kernel
      have hl : raw25902step0Labels = raw25902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25902 raw25902Labels permutation265 hz
    mixedMoment B raw25902step0 raw25902step0Labels = mixedMoment B raw25902step1 raw25902step1Labels := by
      have ha : raw25902step1 = (fun i j => raw25902step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25902step1 raw25902step0; decide +kernel
      have hl : raw25902step1Labels = raw25902step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25902step0 raw25902step0Labels permutation34 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

theorem canonical25903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25903 raw25903Labels = mixedMoment B node4511 node4511Labels := by
  calc
    mixedMoment B raw25903 raw25903Labels = mixedMoment B raw25903step0 raw25903step0Labels := by
      have hz : ∀ j, raw25903 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25903step0 = (fun i j => raw25903 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25903step0 raw25903; decide +kernel
      have hl : raw25903step0Labels = raw25903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25903 raw25903Labels permutation520 hz
    mixedMoment B raw25903step0 raw25903step0Labels = mixedMoment B raw25903step1 raw25903step1Labels := by
      have hz : ∀ j, raw25903step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25903step1 = (fun i j => raw25903step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25903step1 raw25903step0; decide +kernel
      have hl : raw25903step1Labels = raw25903step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25903step0 raw25903step0Labels permutation80 hz
    mixedMoment B raw25903step1 raw25903step1Labels = mixedMoment B raw25903step2 raw25903step2Labels := by
      have hz : ∀ j, raw25903step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25903step2 = (fun i j => raw25903step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25903step2 raw25903step1; decide +kernel
      have hl : raw25903step2Labels = raw25903step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25903step1 raw25903step1Labels permutation14 hz
    _ = mixedMoment B node4511 node4511Labels := by rfl

theorem canonical25904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25904 raw25904Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw25904 raw25904Labels = mixedMoment B raw25904step0 raw25904step0Labels := by
      have hz : ∀ j, raw25904 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25904step0 = (fun i j => raw25904 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25904step0 raw25904; decide +kernel
      have hl : raw25904step0Labels = raw25904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25904 raw25904Labels permutation346 hz
    mixedMoment B raw25904step0 raw25904step0Labels = mixedMoment B raw25904step1 raw25904step1Labels := by
      have hz : ∀ j, raw25904step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25904step1 = (fun i j => raw25904step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25904step1 raw25904step0; decide +kernel
      have hl : raw25904step1Labels = raw25904step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25904step0 raw25904step0Labels permutation56 hz
    mixedMoment B raw25904step1 raw25904step1Labels = mixedMoment B raw25904step2 raw25904step2Labels := by
      have ha : raw25904step2 = (fun i j => raw25904step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25904step2 raw25904step1; decide +kernel
      have hl : raw25904step2Labels = raw25904step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25904step1 raw25904step1Labels permutation11 permutation2
    _ = mixedMoment B node4499 node4499Labels := by rfl

theorem canonical25905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25905 raw25905Labels = mixedMoment B node4185 node4185Labels := by
  calc
    mixedMoment B raw25905 raw25905Labels = mixedMoment B raw25905step0 raw25905step0Labels := by
      have hz : ∀ j, raw25905 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25905step0 = (fun i j => raw25905 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25905step0 raw25905; decide +kernel
      have hl : raw25905step0Labels = raw25905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25905 raw25905Labels permutation346 hz
    mixedMoment B raw25905step0 raw25905step0Labels = mixedMoment B raw25905step1 raw25905step1Labels := by
      have hz : ∀ j, raw25905step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25905step1 = (fun i j => raw25905step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25905step1 raw25905step0; decide +kernel
      have hl : raw25905step1Labels = raw25905step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25905step0 raw25905step0Labels permutation56 hz
    _ = mixedMoment B node4185 node4185Labels := by rfl

theorem canonical25906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25906 raw25906Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw25906 raw25906Labels = mixedMoment B raw25906step0 raw25906step0Labels := by
      have hz : ∀ j, raw25906 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25906step0 = (fun i j => raw25906 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25906step0 raw25906; decide +kernel
      have hl : raw25906step0Labels = raw25906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25906 raw25906Labels permutation346 hz
    _ = mixedMoment B node4354 node4354Labels := by rfl

theorem canonical25907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25907 raw25907Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw25907 raw25907Labels = mixedMoment B raw25907step0 raw25907step0Labels := by
      have hz : ∀ j, raw25907 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25907step0 = (fun i j => raw25907 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25907step0 raw25907; decide +kernel
      have hl : raw25907step0Labels = raw25907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25907 raw25907Labels permutation265 hz
    _ = mixedMoment B node4354 node4354Labels := by rfl

theorem canonical25908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25908 raw25908Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw25908 raw25908Labels = mixedMoment B raw25908step0 raw25908step0Labels := by
      have hz : ∀ j, raw25908 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25908step0 = (fun i j => raw25908 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25908step0 raw25908; decide +kernel
      have hl : raw25908step0Labels = raw25908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25908 raw25908Labels permutation346 hz
    mixedMoment B raw25908step0 raw25908step0Labels = mixedMoment B raw25908step1 raw25908step1Labels := by
      have hz : ∀ j, raw25908step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25908step1 = (fun i j => raw25908step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25908step1 raw25908step0; decide +kernel
      have hl : raw25908step1Labels = raw25908step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25908step0 raw25908step0Labels permutation56 hz
    _ = mixedMoment B node4466 node4466Labels := by rfl

theorem canonical25909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25909 raw25909Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw25909 raw25909Labels = mixedMoment B raw25909step0 raw25909step0Labels := by
      have hz : ∀ j, raw25909 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25909step0 = (fun i j => raw25909 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25909step0 raw25909; decide +kernel
      have hl : raw25909step0Labels = raw25909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25909 raw25909Labels permutation346 hz
    mixedMoment B raw25909step0 raw25909step0Labels = mixedMoment B raw25909step1 raw25909step1Labels := by
      have hz : ∀ j, raw25909step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25909step1 = (fun i j => raw25909step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25909step1 raw25909step0; decide +kernel
      have hl : raw25909step1Labels = raw25909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25909step0 raw25909step0Labels permutation56 hz
    mixedMoment B raw25909step1 raw25909step1Labels = mixedMoment B raw25909step2 raw25909step2Labels := by
      have ha : raw25909step2 = (fun i j => raw25909step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25909step2 raw25909step1; decide +kernel
      have hl : raw25909step2Labels = raw25909step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25909step1 raw25909step1Labels permutation9 permutation2
    _ = mixedMoment B node4503 node4503Labels := by rfl

theorem canonical25910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25910 raw25910Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw25910 raw25910Labels = mixedMoment B raw25910step0 raw25910step0Labels := by
      have hz : ∀ j, raw25910 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25910step0 = (fun i j => raw25910 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25910step0 raw25910; decide +kernel
      have hl : raw25910step0Labels = raw25910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25910 raw25910Labels permutation346 hz
    mixedMoment B raw25910step0 raw25910step0Labels = mixedMoment B raw25910step1 raw25910step1Labels := by
      have hz : ∀ j, raw25910step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25910step1 = (fun i j => raw25910step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25910step1 raw25910step0; decide +kernel
      have hl : raw25910step1Labels = raw25910step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25910step0 raw25910step0Labels permutation56 hz
    mixedMoment B raw25910step1 raw25910step1Labels = mixedMoment B raw25910step2 raw25910step2Labels := by
      have ha : raw25910step2 = (fun i j => raw25910step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25910step2 raw25910step1; decide +kernel
      have hl : raw25910step2Labels = raw25910step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25910step1 raw25910step1Labels permutation10 permutation2
    _ = mixedMoment B node4177 node4177Labels := by rfl

theorem canonical25911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25911 raw25911Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw25911 raw25911Labels = mixedMoment B raw25911step0 raw25911step0Labels := by
      have hz : ∀ j, raw25911 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25911step0 = (fun i j => raw25911 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25911step0 raw25911; decide +kernel
      have hl : raw25911step0Labels = raw25911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25911 raw25911Labels permutation346 hz
    mixedMoment B raw25911step0 raw25911step0Labels = mixedMoment B raw25911step1 raw25911step1Labels := by
      have ha : raw25911step1 = (fun i j => raw25911step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25911step1 raw25911step0; decide +kernel
      have hl : raw25911step1Labels = raw25911step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25911step0 raw25911step0Labels permutation34 permutation2
    _ = mixedMoment B node4346 node4346Labels := by rfl

theorem canonical25912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25912 raw25912Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw25912 raw25912Labels = mixedMoment B raw25912step0 raw25912step0Labels := by
      have hz : ∀ j, raw25912 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25912step0 = (fun i j => raw25912 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25912step0 raw25912; decide +kernel
      have hl : raw25912step0Labels = raw25912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25912 raw25912Labels permutation265 hz
    mixedMoment B raw25912step0 raw25912step0Labels = mixedMoment B raw25912step1 raw25912step1Labels := by
      have ha : raw25912step1 = (fun i j => raw25912step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25912step1 raw25912step0; decide +kernel
      have hl : raw25912step1Labels = raw25912step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25912step0 raw25912step0Labels permutation34 permutation2
    _ = mixedMoment B node4346 node4346Labels := by rfl

theorem canonical25913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25913 raw25913Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw25913 raw25913Labels = mixedMoment B raw25913step0 raw25913step0Labels := by
      have hz : ∀ j, raw25913 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25913step0 = (fun i j => raw25913 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25913step0 raw25913; decide +kernel
      have hl : raw25913step0Labels = raw25913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25913 raw25913Labels permutation346 hz
    mixedMoment B raw25913step0 raw25913step0Labels = mixedMoment B raw25913step1 raw25913step1Labels := by
      have hz : ∀ j, raw25913step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25913step1 = (fun i j => raw25913step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25913step1 raw25913step0; decide +kernel
      have hl : raw25913step1Labels = raw25913step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25913step0 raw25913step0Labels permutation56 hz
    _ = mixedMoment B node4460 node4460Labels := by rfl

theorem canonical25914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25914 raw25914Labels = mixedMoment B node4505 node4505Labels := by
  calc
    mixedMoment B raw25914 raw25914Labels = mixedMoment B raw25914step0 raw25914step0Labels := by
      have hz : ∀ j, raw25914 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25914step0 = (fun i j => raw25914 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25914step0 raw25914; decide +kernel
      have hl : raw25914step0Labels = raw25914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25914 raw25914Labels permutation520 hz
    mixedMoment B raw25914step0 raw25914step0Labels = mixedMoment B raw25914step1 raw25914step1Labels := by
      have hz : ∀ j, raw25914step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25914step1 = (fun i j => raw25914step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25914step1 raw25914step0; decide +kernel
      have hl : raw25914step1Labels = raw25914step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25914step0 raw25914step0Labels permutation80 hz
    mixedMoment B raw25914step1 raw25914step1Labels = mixedMoment B raw25914step2 raw25914step2Labels := by
      have hz : ∀ j, raw25914step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25914step2 = (fun i j => raw25914step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25914step2 raw25914step1; decide +kernel
      have hl : raw25914step2Labels = raw25914step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25914step1 raw25914step1Labels permutation14 hz
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

theorem canonical804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw804 raw804Labels = mixedMoment B node4172 node4172Labels := by
  calc
    mixedMoment B raw804 raw804Labels = mixedMoment B raw804step0 raw804step0Labels := by
      have ha : raw804step0 = (fun i j => raw804 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw804step0 raw804; decide +kernel
      have hl : raw804step0Labels = raw804Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw804 raw804Labels permutation32 permutation4
    mixedMoment B raw804step0 raw804step0Labels = mixedMoment B raw804step1 raw804step1Labels := by
      have ha : raw804step1 = raw804step0 := by apply Matrix.ext; unfold raw804step1 raw804step0; decide +kernel
      have hl : raw804step0Labels = labelEmbedding7 ∘ raw804step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw804step0 raw804step0Labels raw804step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4172 node4172Labels := by rfl

theorem canonical805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw805 raw805Labels = mixedMoment B node600 node600Labels := by
  calc
    mixedMoment B raw805 raw805Labels = mixedMoment B raw805step0 raw805step0Labels := by
      have ha : raw805step0 = (fun i j => raw805 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw805step0 raw805; decide +kernel
      have hl : raw805step0Labels = raw805Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw805 raw805Labels permutation32 permutation4
    _ = mixedMoment B node600 node600Labels := by rfl

theorem canonical806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw806 raw806Labels = mixedMoment B node1507 node1507Labels := by
  calc
    mixedMoment B raw806 raw806Labels = mixedMoment B raw806step0 raw806step0Labels := by
      have ha : raw806step0 = (fun i j => raw806 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw806step0 raw806; decide +kernel
      have hl : raw806step0Labels = raw806Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw806 raw806Labels permutation32 permutation6
    mixedMoment B raw806step0 raw806step0Labels = mixedMoment B raw806step1 raw806step1Labels := by
      have ha : raw806step1 = -raw806step0 := by apply Matrix.ext; change ∀ i j, raw806step1 i j = -(raw806step0 i j); unfold raw806step1 raw806step0; decide +kernel
      have hl : raw806step1Labels = raw806step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw806step1 raw806step1Labels = mixedMoment B raw806step2 raw806step2Labels := by
      have ha : raw806step2 = raw806step1 := by apply Matrix.ext; unfold raw806step2 raw806step1; decide +kernel
      have hl : raw806step1Labels = labelEmbedding1 ∘ raw806step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw806step1 raw806step1Labels raw806step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1507 node1507Labels := by rfl

theorem canonical813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw813 raw813Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw813 raw813Labels = mixedMoment B raw813step0 raw813step0Labels := by
      have ha : raw813step0 = (fun i j => raw813 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw813step0 raw813; decide +kernel
      have hl : raw813step0Labels = raw813Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw813 raw813Labels permutation8 permutation4
    mixedMoment B raw813step0 raw813step0Labels = mixedMoment B raw813step1 raw813step1Labels := by
      have ha : raw813step1 = raw813step0 := by apply Matrix.ext; unfold raw813step1 raw813step0; decide +kernel
      have hl : raw813step0Labels = labelEmbedding7 ∘ raw813step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw813step0 raw813step0Labels raw813step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4177 node4177Labels := by rfl

theorem canonical814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw814 raw814Labels = mixedMoment B node605 node605Labels := by
  calc
    mixedMoment B raw814 raw814Labels = mixedMoment B raw814step0 raw814step0Labels := by
      have ha : raw814step0 = (fun i j => raw814 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw814step0 raw814; decide +kernel
      have hl : raw814step0Labels = raw814Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw814 raw814Labels permutation8 permutation4
    _ = mixedMoment B node605 node605Labels := by rfl

theorem canonical815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw815 raw815Labels = mixedMoment B node1518 node1518Labels := by
  calc
    mixedMoment B raw815 raw815Labels = mixedMoment B raw815step0 raw815step0Labels := by
      have ha : raw815step0 = (fun i j => raw815 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw815step0 raw815; decide +kernel
      have hl : raw815step0Labels = raw815Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw815 raw815Labels permutation8 permutation6
    mixedMoment B raw815step0 raw815step0Labels = mixedMoment B raw815step1 raw815step1Labels := by
      have ha : raw815step1 = -raw815step0 := by apply Matrix.ext; change ∀ i j, raw815step1 i j = -(raw815step0 i j); unfold raw815step1 raw815step0; decide +kernel
      have hl : raw815step1Labels = raw815step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw815step1 raw815step1Labels = mixedMoment B raw815step2 raw815step2Labels := by
      have ha : raw815step2 = raw815step1 := by apply Matrix.ext; unfold raw815step2 raw815step1; decide +kernel
      have hl : raw815step1Labels = labelEmbedding1 ∘ raw815step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw815step1 raw815step1Labels raw815step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1518 node1518Labels := by rfl

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

theorem canonical828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw828 raw828Labels = mixedMoment B node4185 node4185Labels := by
  calc
    mixedMoment B raw828 raw828Labels = mixedMoment B raw828step0 raw828step0Labels := by
      have ha : raw828step0 = (fun i j => raw828 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw828step0 raw828; decide +kernel
      have hl : raw828step0Labels = raw828Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw828 raw828Labels permutation8 permutation4
    mixedMoment B raw828step0 raw828step0Labels = mixedMoment B raw828step1 raw828step1Labels := by
      have ha : raw828step1 = raw828step0 := by apply Matrix.ext; unfold raw828step1 raw828step0; decide +kernel
      have hl : raw828step0Labels = labelEmbedding7 ∘ raw828step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw828step0 raw828step0Labels raw828step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4185 node4185Labels := by rfl

theorem canonical829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw829 raw829Labels = mixedMoment B node613 node613Labels := by
  calc
    mixedMoment B raw829 raw829Labels = mixedMoment B raw829step0 raw829step0Labels := by
      have ha : raw829step0 = (fun i j => raw829 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw829step0 raw829; decide +kernel
      have hl : raw829step0Labels = raw829Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw829 raw829Labels permutation8 permutation4
    _ = mixedMoment B node613 node613Labels := by rfl

theorem canonical830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw830 raw830Labels = mixedMoment B node1525 node1525Labels := by
  calc
    mixedMoment B raw830 raw830Labels = mixedMoment B raw830step0 raw830step0Labels := by
      have ha : raw830step0 = (fun i j => raw830 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw830step0 raw830; decide +kernel
      have hl : raw830step0Labels = raw830Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw830 raw830Labels permutation10 permutation6
    mixedMoment B raw830step0 raw830step0Labels = mixedMoment B raw830step1 raw830step1Labels := by
      have ha : raw830step1 = -raw830step0 := by apply Matrix.ext; change ∀ i j, raw830step1 i j = -(raw830step0 i j); unfold raw830step1 raw830step0; decide +kernel
      have hl : raw830step1Labels = raw830step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw830step1 raw830step1Labels = mixedMoment B raw830step2 raw830step2Labels := by
      have ha : raw830step2 = raw830step1 := by apply Matrix.ext; unfold raw830step2 raw830step1; decide +kernel
      have hl : raw830step1Labels = labelEmbedding1 ∘ raw830step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw830step1 raw830step1Labels raw830step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1525 node1525Labels := by rfl

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

theorem canonical1122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1122 raw1122Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw1122 raw1122Labels = mixedMoment B raw1122step0 raw1122step0Labels := by
      have ha : raw1122step0 = (fun i j => raw1122 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1122step0 raw1122; decide +kernel
      have hl : raw1122step0Labels = raw1122Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1122 raw1122Labels permutation152 permutation4
    mixedMoment B raw1122step0 raw1122step0Labels = mixedMoment B raw1122step1 raw1122step1Labels := by
      have ha : raw1122step1 = raw1122step0 := by apply Matrix.ext; unfold raw1122step1 raw1122step0; decide +kernel
      have hl : raw1122step0Labels = labelEmbedding7 ∘ raw1122step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1122step0 raw1122step0Labels raw1122step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4341 node4341Labels := by rfl

theorem canonical1123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1123 raw1123Labels = mixedMoment B node919 node919Labels := by
  calc
    mixedMoment B raw1123 raw1123Labels = mixedMoment B raw1123step0 raw1123step0Labels := by
      have ha : raw1123step0 = (fun i j => raw1123 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1123step0 raw1123; decide +kernel
      have hl : raw1123step0Labels = raw1123Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1123 raw1123Labels permutation152 permutation4
    _ = mixedMoment B node919 node919Labels := by rfl

theorem canonical1124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1124 raw1124Labels = mixedMoment B node1664 node1664Labels := by
  calc
    mixedMoment B raw1124 raw1124Labels = mixedMoment B raw1124step0 raw1124step0Labels := by
      have ha : raw1124step0 = (fun i j => raw1124 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1124step0 raw1124; decide +kernel
      have hl : raw1124step0Labels = raw1124Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1124 raw1124Labels permutation152 permutation6
    mixedMoment B raw1124step0 raw1124step0Labels = mixedMoment B raw1124step1 raw1124step1Labels := by
      have ha : raw1124step1 = -raw1124step0 := by apply Matrix.ext; change ∀ i j, raw1124step1 i j = -(raw1124step0 i j); unfold raw1124step1 raw1124step0; decide +kernel
      have hl : raw1124step1Labels = raw1124step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1124step1 raw1124step1Labels = mixedMoment B raw1124step2 raw1124step2Labels := by
      have ha : raw1124step2 = raw1124step1 := by apply Matrix.ext; unfold raw1124step2 raw1124step1; decide +kernel
      have hl : raw1124step1Labels = labelEmbedding1 ∘ raw1124step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1124step1 raw1124step1Labels raw1124step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1664 node1664Labels := by rfl

theorem canonical1131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1131 raw1131Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw1131 raw1131Labels = mixedMoment B raw1131step0 raw1131step0Labels := by
      have ha : raw1131step0 = (fun i j => raw1131 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1131step0 raw1131; decide +kernel
      have hl : raw1131step0Labels = raw1131Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1131 raw1131Labels permutation32 permutation4
    mixedMoment B raw1131step0 raw1131step0Labels = mixedMoment B raw1131step1 raw1131step1Labels := by
      have ha : raw1131step1 = raw1131step0 := by apply Matrix.ext; unfold raw1131step1 raw1131step0; decide +kernel
      have hl : raw1131step0Labels = labelEmbedding7 ∘ raw1131step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1131step0 raw1131step0Labels raw1131step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4346 node4346Labels := by rfl

theorem canonical1132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1132 raw1132Labels = mixedMoment B node924 node924Labels := by
  calc
    mixedMoment B raw1132 raw1132Labels = mixedMoment B raw1132step0 raw1132step0Labels := by
      have ha : raw1132step0 = (fun i j => raw1132 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1132step0 raw1132; decide +kernel
      have hl : raw1132step0Labels = raw1132Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1132 raw1132Labels permutation32 permutation4
    _ = mixedMoment B node924 node924Labels := by rfl

theorem canonical1133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1133 raw1133Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw1133 raw1133Labels = mixedMoment B raw1133step0 raw1133step0Labels := by
      have ha : raw1133step0 = (fun i j => raw1133 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1133step0 raw1133; decide +kernel
      have hl : raw1133step0Labels = raw1133Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1133 raw1133Labels permutation32 permutation6
    mixedMoment B raw1133step0 raw1133step0Labels = mixedMoment B raw1133step1 raw1133step1Labels := by
      have ha : raw1133step1 = -raw1133step0 := by apply Matrix.ext; change ∀ i j, raw1133step1 i j = -(raw1133step0 i j); unfold raw1133step1 raw1133step0; decide +kernel
      have hl : raw1133step1Labels = raw1133step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1133step1 raw1133step1Labels = mixedMoment B raw1133step2 raw1133step2Labels := by
      have ha : raw1133step2 = raw1133step1 := by apply Matrix.ext; unfold raw1133step2 raw1133step1; decide +kernel
      have hl : raw1133step1Labels = labelEmbedding1 ∘ raw1133step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1133step1 raw1133step1Labels raw1133step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

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

theorem canonical1257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1257 raw1257Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw1257 raw1257Labels = mixedMoment B raw1257step0 raw1257step0Labels := by
      have ha : raw1257step0 = (fun i j => raw1257 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1257step0 raw1257; decide +kernel
      have hl : raw1257step0Labels = raw1257Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1257 raw1257Labels permutation32 permutation4
    mixedMoment B raw1257step0 raw1257step0Labels = mixedMoment B raw1257step1 raw1257step1Labels := by
      have ha : raw1257step1 = raw1257step0 := by apply Matrix.ext; unfold raw1257step1 raw1257step0; decide +kernel
      have hl : raw1257step0Labels = labelEmbedding7 ∘ raw1257step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1257step0 raw1257step0Labels raw1257step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4457 node4457Labels := by rfl

theorem canonical1258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1258 raw1258Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw1258 raw1258Labels = mixedMoment B raw1258step0 raw1258step0Labels := by
      have ha : raw1258step0 = (fun i j => raw1258 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1258step0 raw1258; decide +kernel
      have hl : raw1258step0Labels = raw1258Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1258 raw1258Labels permutation32 permutation4
    _ = mixedMoment B node1040 node1040Labels := by rfl

theorem canonical1259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1259 raw1259Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw1259 raw1259Labels = mixedMoment B raw1259step0 raw1259step0Labels := by
      have ha : raw1259step0 = (fun i j => raw1259 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1259step0 raw1259; decide +kernel
      have hl : raw1259step0Labels = raw1259Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1259 raw1259Labels permutation40 permutation6
    mixedMoment B raw1259step0 raw1259step0Labels = mixedMoment B raw1259step1 raw1259step1Labels := by
      have ha : raw1259step1 = -raw1259step0 := by apply Matrix.ext; change ∀ i j, raw1259step1 i j = -(raw1259step0 i j); unfold raw1259step1 raw1259step0; decide +kernel
      have hl : raw1259step1Labels = raw1259step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1259step1 raw1259step1Labels = mixedMoment B raw1259step2 raw1259step2Labels := by
      have ha : raw1259step2 = raw1259step1 := by apply Matrix.ext; unfold raw1259step2 raw1259step1; decide +kernel
      have hl : raw1259step1Labels = labelEmbedding1 ∘ raw1259step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1259step1 raw1259step1Labels raw1259step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

theorem canonical1263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1263 raw1263Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw1263 raw1263Labels = mixedMoment B raw1263step0 raw1263step0Labels := by
      have ha : raw1263step0 = (fun i j => raw1263 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1263step0 raw1263; decide +kernel
      have hl : raw1263step0Labels = raw1263Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1263 raw1263Labels permutation8 permutation4
    mixedMoment B raw1263step0 raw1263step0Labels = mixedMoment B raw1263step1 raw1263step1Labels := by
      have ha : raw1263step1 = raw1263step0 := by apply Matrix.ext; unfold raw1263step1 raw1263step0; decide +kernel
      have hl : raw1263step0Labels = labelEmbedding7 ∘ raw1263step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1263step0 raw1263step0Labels raw1263step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

theorem canonical1264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1264 raw1264Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw1264 raw1264Labels = mixedMoment B raw1264step0 raw1264step0Labels := by
      have ha : raw1264step0 = (fun i j => raw1264 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1264step0 raw1264; decide +kernel
      have hl : raw1264step0Labels = raw1264Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1264 raw1264Labels permutation8 permutation4
    _ = mixedMoment B node1043 node1043Labels := by rfl

theorem canonical1265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1265 raw1265Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw1265 raw1265Labels = mixedMoment B raw1265step0 raw1265step0Labels := by
      have ha : raw1265step0 = (fun i j => raw1265 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1265step0 raw1265; decide +kernel
      have hl : raw1265step0Labels = raw1265Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1265 raw1265Labels permutation10 permutation6
    mixedMoment B raw1265step0 raw1265step0Labels = mixedMoment B raw1265step1 raw1265step1Labels := by
      have ha : raw1265step1 = -raw1265step0 := by apply Matrix.ext; change ∀ i j, raw1265step1 i j = -(raw1265step0 i j); unfold raw1265step1 raw1265step0; decide +kernel
      have hl : raw1265step1Labels = raw1265step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1265step1 raw1265step1Labels = mixedMoment B raw1265step2 raw1265step2Labels := by
      have ha : raw1265step2 = raw1265step1 := by apply Matrix.ext; unfold raw1265step2 raw1265step1; decide +kernel
      have hl : raw1265step1Labels = labelEmbedding1 ∘ raw1265step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1265step1 raw1265step1Labels raw1265step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical1272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1272 raw1272Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw1272 raw1272Labels = mixedMoment B raw1272step0 raw1272step0Labels := by
      have ha : raw1272step0 = (fun i j => raw1272 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1272step0 raw1272; decide +kernel
      have hl : raw1272step0Labels = raw1272Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1272 raw1272Labels permutation8 permutation4
    mixedMoment B raw1272step0 raw1272step0Labels = mixedMoment B raw1272step1 raw1272step1Labels := by
      have ha : raw1272step1 = raw1272step0 := by apply Matrix.ext; unfold raw1272step1 raw1272step0; decide +kernel
      have hl : raw1272step0Labels = labelEmbedding7 ∘ raw1272step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1272step0 raw1272step0Labels raw1272step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

theorem canonical1273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1273 raw1273Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw1273 raw1273Labels = mixedMoment B raw1273step0 raw1273step0Labels := by
      have ha : raw1273step0 = (fun i j => raw1273 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1273step0 raw1273; decide +kernel
      have hl : raw1273step0Labels = raw1273Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1273 raw1273Labels permutation8 permutation4
    _ = mixedMoment B node1049 node1049Labels := by rfl

theorem canonical1274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1274 raw1274Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw1274 raw1274Labels = mixedMoment B raw1274step0 raw1274step0Labels := by
      have ha : raw1274step0 = (fun i j => raw1274 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1274step0 raw1274; decide +kernel
      have hl : raw1274step0Labels = raw1274Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1274 raw1274Labels permutation10 permutation6
    mixedMoment B raw1274step0 raw1274step0Labels = mixedMoment B raw1274step1 raw1274step1Labels := by
      have ha : raw1274step1 = -raw1274step0 := by apply Matrix.ext; change ∀ i j, raw1274step1 i j = -(raw1274step0 i j); unfold raw1274step1 raw1274step0; decide +kernel
      have hl : raw1274step1Labels = raw1274step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1274step1 raw1274step1Labels = mixedMoment B raw1274step2 raw1274step2Labels := by
      have ha : raw1274step2 = raw1274step1 := by apply Matrix.ext; unfold raw1274step2 raw1274step1; decide +kernel
      have hl : raw1274step1Labels = labelEmbedding1 ∘ raw1274step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1274step1 raw1274step1Labels raw1274step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1738 node1738Labels := by rfl

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

theorem singleton4172 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4172 node4172Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node600 node600Labels + mixedMoment B node1507 node1507Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw804 singletonSmall4172
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4172) = raw804Labels := by decide +kernel
  rw [hl, canonical804 B hB] at h
  have hc0 : mixedMoment B raw804 (Fin.cases (0 : Fin 2) singletonSmall4172) =
      mixedMoment B node600 node600Labels := by
    have ha : raw804 = raw805 := by apply Matrix.ext; unfold raw804 raw805; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4172 = raw805Labels := by decide +kernel
    rw [ha, hj, canonical805 B hB]
  have hc1 : mixedMoment B raw804 (Fin.cases (1 : Fin 2) singletonSmall4172) =
      mixedMoment B node1507 node1507Labels := by
    have ha : raw804 = raw806 := by apply Matrix.ext; unfold raw804 raw806; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4172 = raw806Labels := by decide +kernel
    rw [ha, hj, canonical806 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4177 node4177Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node605 node605Labels + mixedMoment B node1518 node1518Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw813 singletonSmall4177
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4177) = raw813Labels := by decide +kernel
  rw [hl, canonical813 B hB] at h
  have hc0 : mixedMoment B raw813 (Fin.cases (0 : Fin 2) singletonSmall4177) =
      mixedMoment B node605 node605Labels := by
    have ha : raw813 = raw814 := by apply Matrix.ext; unfold raw813 raw814; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4177 = raw814Labels := by decide +kernel
    rw [ha, hj, canonical814 B hB]
  have hc1 : mixedMoment B raw813 (Fin.cases (1 : Fin 2) singletonSmall4177) =
      mixedMoment B node1518 node1518Labels := by
    have ha : raw813 = raw815 := by apply Matrix.ext; unfold raw813 raw815; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4177 = raw815Labels := by decide +kernel
    rw [ha, hj, canonical815 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4185 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4185 node4185Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node613 node613Labels + mixedMoment B node1525 node1525Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw828 singletonSmall4185
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4185) = raw828Labels := by decide +kernel
  rw [hl, canonical828 B hB] at h
  have hc0 : mixedMoment B raw828 (Fin.cases (0 : Fin 2) singletonSmall4185) =
      mixedMoment B node613 node613Labels := by
    have ha : raw828 = raw829 := by apply Matrix.ext; unfold raw828 raw829; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4185 = raw829Labels := by decide +kernel
    rw [ha, hj, canonical829 B hB]
  have hc1 : mixedMoment B raw828 (Fin.cases (1 : Fin 2) singletonSmall4185) =
      mixedMoment B node1525 node1525Labels := by
    have ha : raw828 = raw830 := by apply Matrix.ext; unfold raw828 raw830; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4185 = raw830Labels := by decide +kernel
    rw [ha, hj, canonical830 B hB]
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

theorem singleton4341 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4341 node4341Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node919 node919Labels + mixedMoment B node1664 node1664Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1122 singletonSmall4341
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4341) = raw1122Labels := by decide +kernel
  rw [hl, canonical1122 B hB] at h
  have hc0 : mixedMoment B raw1122 (Fin.cases (0 : Fin 2) singletonSmall4341) =
      mixedMoment B node919 node919Labels := by
    have ha : raw1122 = raw1123 := by apply Matrix.ext; unfold raw1122 raw1123; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4341 = raw1123Labels := by decide +kernel
    rw [ha, hj, canonical1123 B hB]
  have hc1 : mixedMoment B raw1122 (Fin.cases (1 : Fin 2) singletonSmall4341) =
      mixedMoment B node1664 node1664Labels := by
    have ha : raw1122 = raw1124 := by apply Matrix.ext; unfold raw1122 raw1124; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4341 = raw1124Labels := by decide +kernel
    rw [ha, hj, canonical1124 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4346 node4346Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node924 node924Labels + mixedMoment B node1674 node1674Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1131 singletonSmall4346
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4346) = raw1131Labels := by decide +kernel
  rw [hl, canonical1131 B hB] at h
  have hc0 : mixedMoment B raw1131 (Fin.cases (0 : Fin 2) singletonSmall4346) =
      mixedMoment B node924 node924Labels := by
    have ha : raw1131 = raw1132 := by apply Matrix.ext; unfold raw1131 raw1132; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4346 = raw1132Labels := by decide +kernel
    rw [ha, hj, canonical1132 B hB]
  have hc1 : mixedMoment B raw1131 (Fin.cases (1 : Fin 2) singletonSmall4346) =
      mixedMoment B node1674 node1674Labels := by
    have ha : raw1131 = raw1133 := by apply Matrix.ext; unfold raw1131 raw1133; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4346 = raw1133Labels := by decide +kernel
    rw [ha, hj, canonical1133 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4457 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4457 node4457Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1040 node1040Labels + mixedMoment B node1707 node1707Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1257 singletonSmall4457
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4457) = raw1257Labels := by decide +kernel
  rw [hl, canonical1257 B hB] at h
  have hc0 : mixedMoment B raw1257 (Fin.cases (0 : Fin 2) singletonSmall4457) =
      mixedMoment B node1040 node1040Labels := by
    have ha : raw1257 = raw1258 := by apply Matrix.ext; unfold raw1257 raw1258; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4457 = raw1258Labels := by decide +kernel
    rw [ha, hj, canonical1258 B hB]
  have hc1 : mixedMoment B raw1257 (Fin.cases (1 : Fin 2) singletonSmall4457) =
      mixedMoment B node1707 node1707Labels := by
    have ha : raw1257 = raw1259 := by apply Matrix.ext; unfold raw1257 raw1259; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4457 = raw1259Labels := by decide +kernel
    rw [ha, hj, canonical1259 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4460 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4460 node4460Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1043 node1043Labels + mixedMoment B node1725 node1725Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1263 singletonSmall4460
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4460) = raw1263Labels := by decide +kernel
  rw [hl, canonical1263 B hB] at h
  have hc0 : mixedMoment B raw1263 (Fin.cases (0 : Fin 2) singletonSmall4460) =
      mixedMoment B node1043 node1043Labels := by
    have ha : raw1263 = raw1264 := by apply Matrix.ext; unfold raw1263 raw1264; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4460 = raw1264Labels := by decide +kernel
    rw [ha, hj, canonical1264 B hB]
  have hc1 : mixedMoment B raw1263 (Fin.cases (1 : Fin 2) singletonSmall4460) =
      mixedMoment B node1725 node1725Labels := by
    have ha : raw1263 = raw1265 := by apply Matrix.ext; unfold raw1263 raw1265; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4460 = raw1265Labels := by decide +kernel
    rw [ha, hj, canonical1265 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4466 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4466 node4466Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1049 node1049Labels + mixedMoment B node1738 node1738Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1272 singletonSmall4466
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4466) = raw1272Labels := by decide +kernel
  rw [hl, canonical1272 B hB] at h
  have hc0 : mixedMoment B raw1272 (Fin.cases (0 : Fin 2) singletonSmall4466) =
      mixedMoment B node1049 node1049Labels := by
    have ha : raw1272 = raw1273 := by apply Matrix.ext; unfold raw1272 raw1273; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4466 = raw1273Labels := by decide +kernel
    rw [ha, hj, canonical1273 B hB]
  have hc1 : mixedMoment B raw1272 (Fin.cases (1 : Fin 2) singletonSmall4466) =
      mixedMoment B node1738 node1738Labels := by
    have ha : raw1272 = raw1274 := by apply Matrix.ext; unfold raw1272 raw1274; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4466 = raw1274Labels := by decide +kernel
    rw [ha, hj, canonical1274 B hB]
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

theorem singleton4495 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4495 node4495Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1079 node1079Labels + mixedMoment B node1708 node1708Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1293 singletonSmall4495
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4495) = raw1293Labels := by decide +kernel
  rw [hl, canonical1293 B hB] at h
  have hc0 : mixedMoment B raw1293 (Fin.cases (0 : Fin 2) singletonSmall4495) =
      mixedMoment B node1079 node1079Labels := by
    have ha : raw1293 = raw1294 := by apply Matrix.ext; unfold raw1293 raw1294; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4495 = raw1294Labels := by decide +kernel
    rw [ha, hj, canonical1294 B hB]
  have hc1 : mixedMoment B raw1293 (Fin.cases (1 : Fin 2) singletonSmall4495) =
      mixedMoment B node1708 node1708Labels := by
    have ha : raw1293 = raw1295 := by apply Matrix.ext; unfold raw1293 raw1295; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4495 = raw1295Labels := by decide +kernel
    rw [ha, hj, canonical1295 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node919 node919Labels = Sparse.eval nodeValue919 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 919) = mixedMoment B node919 node919Labels := rfl
  simpa [nodeValue919, Sparse.eval] using hc.symm

theorem sound924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node924 node924Labels = Sparse.eval nodeValue924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 924) = mixedMoment B node924 node924Labels := rfl
  simpa [nodeValue924, Sparse.eval] using hc.symm

theorem sound927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node927 node927Labels = Sparse.eval nodeValue927 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 927) = mixedMoment B node927 node927Labels := rfl
  simpa [nodeValue927, Sparse.eval] using hc.symm

theorem sound932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node932 node932Labels = Sparse.eval nodeValue932 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 932) = mixedMoment B node932 node932Labels := rfl
  simpa [nodeValue932, Sparse.eval] using hc.symm

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

theorem sound1040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1040 node1040Labels = Sparse.eval nodeValue1040 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1040) = mixedMoment B node1040 node1040Labels := rfl
  simpa [nodeValue1040, Sparse.eval] using hc.symm

theorem sound1043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1043 node1043Labels = Sparse.eval nodeValue1043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1043) = mixedMoment B node1043 node1043Labels := rfl
  simpa [nodeValue1043, Sparse.eval] using hc.symm

theorem sound1049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1049 node1049Labels = Sparse.eval nodeValue1049 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1049) = mixedMoment B node1049 node1049Labels := rfl
  simpa [nodeValue1049, Sparse.eval] using hc.symm

theorem sound1079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1079 node1079Labels = Sparse.eval nodeValue1079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1079) = mixedMoment B node1079 node1079Labels := rfl
  simpa [nodeValue1079, Sparse.eval] using hc.symm

theorem sound1083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1083 node1083Labels = Sparse.eval nodeValue1083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1083) = mixedMoment B node1083 node1083Labels := rfl
  simpa [nodeValue1083, Sparse.eval] using hc.symm

theorem sound1087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1087 node1087Labels = Sparse.eval nodeValue1087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1087) = mixedMoment B node1087 node1087Labels := rfl
  simpa [nodeValue1087, Sparse.eval] using hc.symm

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

theorem sound1507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1507 node1507Labels = Sparse.eval nodeValue1507 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1507) = mixedMoment B node1507 node1507Labels := rfl
  simpa [nodeValue1507, Sparse.eval] using hc.symm

theorem sound1518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1518 node1518Labels = Sparse.eval nodeValue1518 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1518) = mixedMoment B node1518 node1518Labels := rfl
  simpa [nodeValue1518, Sparse.eval] using hc.symm

theorem sound1519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1519 node1519Labels = Sparse.eval nodeValue1519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1519) = mixedMoment B node1519 node1519Labels := rfl
  simpa [nodeValue1519, Sparse.eval] using hc.symm

theorem sound1525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1525 node1525Labels = Sparse.eval nodeValue1525 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1525) = mixedMoment B node1525 node1525Labels := rfl
  simpa [nodeValue1525, Sparse.eval] using hc.symm

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

theorem sound1664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1664 node1664Labels = Sparse.eval nodeValue1664 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1664) = mixedMoment B node1664 node1664Labels := rfl
  simpa [nodeValue1664, Sparse.eval] using hc.symm

theorem sound1674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1674 node1674Labels = Sparse.eval nodeValue1674 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1674) = mixedMoment B node1674 node1674Labels := rfl
  simpa [nodeValue1674, Sparse.eval] using hc.symm

theorem sound1675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1675 node1675Labels = Sparse.eval nodeValue1675 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1675) = mixedMoment B node1675 node1675Labels := rfl
  simpa [nodeValue1675, Sparse.eval] using hc.symm

theorem sound1681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1681 node1681Labels = Sparse.eval nodeValue1681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1681) = mixedMoment B node1681 node1681Labels := rfl
  simpa [nodeValue1681, Sparse.eval] using hc.symm

theorem sound1707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1707 node1707Labels = Sparse.eval nodeValue1707 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1707) = mixedMoment B node1707 node1707Labels := rfl
  simpa [nodeValue1707, Sparse.eval] using hc.symm

theorem sound1708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1708 node1708Labels = Sparse.eval nodeValue1708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1708) = mixedMoment B node1708 node1708Labels := rfl
  simpa [nodeValue1708, Sparse.eval] using hc.symm

theorem sound1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1725 node1725Labels = Sparse.eval nodeValue1725 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1725) = mixedMoment B node1725 node1725Labels := rfl
  simpa [nodeValue1725, Sparse.eval] using hc.symm

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

theorem sound1738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1738 node1738Labels = Sparse.eval nodeValue1738 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1738) = mixedMoment B node1738 node1738Labels := rfl
  simpa [nodeValue1738, Sparse.eval] using hc.symm

theorem sound1739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1739 node1739Labels = Sparse.eval nodeValue1739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1739) = mixedMoment B node1739 node1739Labels := rfl
  simpa [nodeValue1739, Sparse.eval] using hc.symm

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

theorem sound600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node600 node600Labels = Sparse.eval nodeValue600 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 600) = mixedMoment B node600 node600Labels := rfl
  simpa [nodeValue600, Sparse.eval] using hc.symm

theorem sound605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node605 node605Labels = Sparse.eval nodeValue605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 605) = mixedMoment B node605 node605Labels := rfl
  simpa [nodeValue605, Sparse.eval] using hc.symm

theorem sound608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node608 node608Labels = Sparse.eval nodeValue608 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 608) = mixedMoment B node608 node608Labels := rfl
  simpa [nodeValue608, Sparse.eval] using hc.symm

theorem sound613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node613 node613Labels = Sparse.eval nodeValue613 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 613) = mixedMoment B node613 node613Labels := rfl
  simpa [nodeValue613, Sparse.eval] using hc.symm

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

theorem sound4172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4172 node4172Labels = Sparse.eval nodeValue4172 (mixedVector B) := by
  have h := singleton4172 B _hB
  rw [sound600 B _hB _hF, sound1507 B _hB _hF] at h
  norm_num [nodeValue4172, nodeValue600, nodeValue1507, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4177 node4177Labels = Sparse.eval nodeValue4177 (mixedVector B) := by
  have h := singleton4177 B _hB
  rw [sound605 B _hB _hF, sound1518 B _hB _hF] at h
  norm_num [nodeValue4177, nodeValue605, nodeValue1518, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4180 node4180Labels = Sparse.eval nodeValue4180 (mixedVector B) := by
  have h := singleton4180 B _hB
  rw [sound608 B _hB _hF, sound1519 B _hB _hF] at h
  norm_num [nodeValue4180, nodeValue608, nodeValue1519, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4185 node4185Labels = Sparse.eval nodeValue4185 (mixedVector B) := by
  have h := singleton4185 B _hB
  rw [sound613 B _hB _hF, sound1525 B _hB _hF] at h
  norm_num [nodeValue4185, nodeValue613, nodeValue1525, Sparse.eval] at h ⊢
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

theorem sound4341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4341 node4341Labels = Sparse.eval nodeValue4341 (mixedVector B) := by
  have h := singleton4341 B _hB
  rw [sound919 B _hB _hF, sound1664 B _hB _hF] at h
  norm_num [nodeValue4341, nodeValue919, nodeValue1664, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4346 node4346Labels = Sparse.eval nodeValue4346 (mixedVector B) := by
  have h := singleton4346 B _hB
  rw [sound924 B _hB _hF, sound1674 B _hB _hF] at h
  norm_num [nodeValue4346, nodeValue924, nodeValue1674, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4354 node4354Labels = Sparse.eval nodeValue4354 (mixedVector B) := by
  have h := singleton4354 B _hB
  rw [sound932 B _hB _hF, sound1681 B _hB _hF] at h
  norm_num [nodeValue4354, nodeValue932, nodeValue1681, Sparse.eval] at h ⊢
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

theorem sound4457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4457 node4457Labels = Sparse.eval nodeValue4457 (mixedVector B) := by
  have h := singleton4457 B _hB
  rw [sound1040 B _hB _hF, sound1707 B _hB _hF] at h
  norm_num [nodeValue4457, nodeValue1040, nodeValue1707, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4460 node4460Labels = Sparse.eval nodeValue4460 (mixedVector B) := by
  have h := singleton4460 B _hB
  rw [sound1043 B _hB _hF, sound1725 B _hB _hF] at h
  norm_num [nodeValue4460, nodeValue1043, nodeValue1725, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4466 node4466Labels = Sparse.eval nodeValue4466 (mixedVector B) := by
  have h := singleton4466 B _hB
  rw [sound1049 B _hB _hF, sound1738 B _hB _hF] at h
  norm_num [nodeValue4466, nodeValue1049, nodeValue1738, Sparse.eval] at h ⊢
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

theorem zero4511 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4511 node4511Labels = 0 := by
  exact mixedMoment_order_one B hB node4511 node4511Labels 1
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

theorem sound4495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4495 node4495Labels = Sparse.eval nodeValue4495 (mixedVector B) := by
  have h := singleton4495 B _hB
  rw [sound1079 B _hB _hF, sound1708 B _hB _hF] at h
  norm_num [nodeValue4495, nodeValue1079, nodeValue1708, Sparse.eval] at h ⊢
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

theorem sound4503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4503 node4503Labels = Sparse.eval nodeValue4503 (mixedVector B) := by
  have h := singleton4503 B _hB
  rw [sound1087 B _hB _hF, sound1739 B _hB _hF] at h
  norm_num [nodeValue4503, nodeValue1087, nodeValue1739, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4505 node4505Labels = Sparse.eval nodeValue4505 (mixedVector B) := by
  simpa only [nodeValue4505, Sparse.eval_nil] using zero4505 B _hB _hF

theorem sound4511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4511 node4511Labels = Sparse.eval nodeValue4511 (mixedVector B) := by
  simpa only [nodeValue4511, Sparse.eval_nil] using zero4511 B _hB _hF

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

theorem sound4834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4834 node4834Labels = Sparse.eval nodeValue4834 (mixedVector B) := by
  simpa only [nodeValue4834, Sparse.eval_nil] using zero4834 B _hB _hF

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

theorem zero4894 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4894 node4894Labels = 0 := by
  exact mixedMoment_order_one B hB node4894 node4894Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4894 node4894Labels = Sparse.eval nodeValue4894 (mixedVector B) := by
  simpa only [nodeValue4894, Sparse.eval_nil] using zero4894 B _hB _hF

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

theorem sourceEq1782 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1782 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1782 + difference 0 1) (sourceB1782 + difference 1 0) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA1782 + difference 0 1) (sourceB1782 + difference 1 0) sourceC1782) = raw25885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25885; decide +kernel
    rw [ha]
    exact (canonical25885 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1782 + difference 0 2) (sourceB1782 + difference 2 0) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA1782 + difference 0 2) (sourceB1782 + difference 2 0) sourceC1782) = raw25886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25886; decide +kernel
    rw [ha]
    exact (canonical25886 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1782 + difference 0 3) (sourceB1782 + difference 3 0) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA1782 + difference 0 3) (sourceB1782 + difference 3 0) sourceC1782) = raw25887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25887; decide +kernel
    rw [ha]
    exact (canonical25887 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1782 + difference 0 4) (sourceB1782 + difference 4 0) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1782 + difference 0 4) (sourceB1782 + difference 4 0) sourceC1782) = raw25888 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25888; decide +kernel
    rw [ha]
    exact (canonical25888 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1782 + difference 0 5) (sourceB1782 + difference 5 0) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1782 + difference 0 5) (sourceB1782 + difference 5 0) sourceC1782) = raw25889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25889; decide +kernel
    rw [ha]
    exact (canonical25889 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1782 + difference 1 0) (sourceB1782 + difference 0 1) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4172) := by
    have ha : (tripleCharges (sourceA1782 + difference 1 0) (sourceB1782 + difference 0 1) sourceC1782) = raw25890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25890; decide +kernel
    rw [ha]
    exact (canonical25890 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1782 + difference 1 2) (sourceB1782 + difference 2 1) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4341) := by
    have ha : (tripleCharges (sourceA1782 + difference 1 2) (sourceB1782 + difference 2 1) sourceC1782) = raw25891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25891; decide +kernel
    rw [ha]
    exact (canonical25891 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1782 + difference 1 3) (sourceB1782 + difference 3 1) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1782 + difference 1 3) (sourceB1782 + difference 3 1) sourceC1782) = raw25892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25892; decide +kernel
    rw [ha]
    exact (canonical25892 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1782 + difference 1 4) (sourceB1782 + difference 4 1) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1782 + difference 1 4) (sourceB1782 + difference 4 1) sourceC1782) = raw25893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25893; decide +kernel
    rw [ha]
    exact (canonical25893 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1782 + difference 1 5) (sourceB1782 + difference 5 1) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1782 + difference 1 5) (sourceB1782 + difference 5 1) sourceC1782) = raw25894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25894; decide +kernel
    rw [ha]
    exact (canonical25894 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1782 + difference 2 0) (sourceB1782 + difference 0 2) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4172) := by
    have ha : (tripleCharges (sourceA1782 + difference 2 0) (sourceB1782 + difference 0 2) sourceC1782) = raw25895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25895; decide +kernel
    rw [ha]
    exact (canonical25895 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1782 + difference 2 1) (sourceB1782 + difference 1 2) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4341) := by
    have ha : (tripleCharges (sourceA1782 + difference 2 1) (sourceB1782 + difference 1 2) sourceC1782) = raw25896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25896; decide +kernel
    rw [ha]
    exact (canonical25896 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1782 + difference 2 3) (sourceB1782 + difference 3 2) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1782 + difference 2 3) (sourceB1782 + difference 3 2) sourceC1782) = raw25897 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25897; decide +kernel
    rw [ha]
    exact (canonical25897 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1782 + difference 2 4) (sourceB1782 + difference 4 2) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1782 + difference 2 4) (sourceB1782 + difference 4 2) sourceC1782) = raw25898 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25898; decide +kernel
    rw [ha]
    exact (canonical25898 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1782 + difference 2 5) (sourceB1782 + difference 5 2) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1782 + difference 2 5) (sourceB1782 + difference 5 2) sourceC1782) = raw25899 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25899; decide +kernel
    rw [ha]
    exact (canonical25899 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1782 + difference 3 0) (sourceB1782 + difference 0 3) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4180) := by
    have ha : (tripleCharges (sourceA1782 + difference 3 0) (sourceB1782 + difference 0 3) sourceC1782) = raw25900 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25900; decide +kernel
    rw [ha]
    exact (canonical25900 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1782 + difference 3 1) (sourceB1782 + difference 1 3) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1782 + difference 3 1) (sourceB1782 + difference 1 3) sourceC1782) = raw25901 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25901; decide +kernel
    rw [ha]
    exact (canonical25901 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1782 + difference 3 2) (sourceB1782 + difference 2 3) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1782 + difference 3 2) (sourceB1782 + difference 2 3) sourceC1782) = raw25902 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25902; decide +kernel
    rw [ha]
    exact (canonical25902 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1782 + difference 3 4) (sourceB1782 + difference 4 3) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1782 + difference 3 4) (sourceB1782 + difference 4 3) sourceC1782) = raw25903 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25903; decide +kernel
    rw [ha]
    exact (canonical25903 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1782 + difference 3 5) (sourceB1782 + difference 5 3) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1782 + difference 3 5) (sourceB1782 + difference 5 3) sourceC1782) = raw25904 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25904; decide +kernel
    rw [ha]
    exact (canonical25904 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1782 + difference 4 0) (sourceB1782 + difference 0 4) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4185) := by
    have ha : (tripleCharges (sourceA1782 + difference 4 0) (sourceB1782 + difference 0 4) sourceC1782) = raw25905 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25905; decide +kernel
    rw [ha]
    exact (canonical25905 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1782 + difference 4 1) (sourceB1782 + difference 1 4) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA1782 + difference 4 1) (sourceB1782 + difference 1 4) sourceC1782) = raw25906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25906; decide +kernel
    rw [ha]
    exact (canonical25906 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1782 + difference 4 2) (sourceB1782 + difference 2 4) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA1782 + difference 4 2) (sourceB1782 + difference 2 4) sourceC1782) = raw25907 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25907; decide +kernel
    rw [ha]
    exact (canonical25907 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1782 + difference 4 3) (sourceB1782 + difference 3 4) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1782 + difference 4 3) (sourceB1782 + difference 3 4) sourceC1782) = raw25908 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25908; decide +kernel
    rw [ha]
    exact (canonical25908 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1782 + difference 4 5) (sourceB1782 + difference 5 4) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1782 + difference 4 5) (sourceB1782 + difference 5 4) sourceC1782) = raw25909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25909; decide +kernel
    rw [ha]
    exact (canonical25909 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1782 + difference 5 0) (sourceB1782 + difference 0 5) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4177) := by
    have ha : (tripleCharges (sourceA1782 + difference 5 0) (sourceB1782 + difference 0 5) sourceC1782) = raw25910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25910; decide +kernel
    rw [ha]
    exact (canonical25910 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1782 + difference 5 1) (sourceB1782 + difference 1 5) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1782 + difference 5 1) (sourceB1782 + difference 1 5) sourceC1782) = raw25911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25911; decide +kernel
    rw [ha]
    exact (canonical25911 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1782 + difference 5 2) (sourceB1782 + difference 2 5) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1782 + difference 5 2) (sourceB1782 + difference 2 5) sourceC1782) = raw25912 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25912; decide +kernel
    rw [ha]
    exact (canonical25912 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1782 + difference 5 3) (sourceB1782 + difference 3 5) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1782 + difference 5 3) (sourceB1782 + difference 3 5) sourceC1782) = raw25913 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25913; decide +kernel
    rw [ha]
    exact (canonical25913 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1782 + difference 5 4) (sourceB1782 + difference 4 5) sourceC1782) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA1782 + difference 5 4) (sourceB1782 + difference 4 5) sourceC1782) = raw25914 := by
      apply Matrix.ext; unfold tripleCharges sourceA1782 sourceB1782 sourceC1782 difference raw25914; decide +kernel
    rw [ha]
    exact (canonical25914 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1782 sourceB1782 sourceC1782
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1782, Integer.Sparse.eval]
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

theorem reindexCheck1514 : Integer.Sparse.reindex keyMap MixedData.row1514 = numericRow1514 := by decide +kernel

theorem numericCheck1514 (x : Master → ℝ) : Integer.Sparse.eval numericRow1514 x =
    (4 : ℝ) * reducedSource1514 x := by
  norm_num [numericRow1514, reducedSource1514, Integer.Sparse.eval, Sparse.eval, nodeValue4084, nodeValue4172, nodeValue4177, nodeValue4180, nodeValue4185, nodeValue4341, nodeValue4346, nodeValue4349, nodeValue4354, nodeValue4457, nodeValue4460, nodeValue4466, nodeValue4495, nodeValue4498, nodeValue4499, nodeValue4503, nodeValue4505, nodeValue4511, nodeValue4834, nodeValue4894, nodeValue4895]
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

theorem reducedZero1514 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1514 (mixedVector B) = 0 := by
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4172 : mixedVector B (Sum.inr 4172) = Sparse.eval nodeValue4172 (mixedVector B) := by
    change mixedMoment B node4172 node4172Labels = _
    exact sound4172 B hB hF
  have h4177 : mixedVector B (Sum.inr 4177) = Sparse.eval nodeValue4177 (mixedVector B) := by
    change mixedMoment B node4177 node4177Labels = _
    exact sound4177 B hB hF
  have h4180 : mixedVector B (Sum.inr 4180) = Sparse.eval nodeValue4180 (mixedVector B) := by
    change mixedMoment B node4180 node4180Labels = _
    exact sound4180 B hB hF
  have h4185 : mixedVector B (Sum.inr 4185) = Sparse.eval nodeValue4185 (mixedVector B) := by
    change mixedMoment B node4185 node4185Labels = _
    exact sound4185 B hB hF
  have h4341 : mixedVector B (Sum.inr 4341) = Sparse.eval nodeValue4341 (mixedVector B) := by
    change mixedMoment B node4341 node4341Labels = _
    exact sound4341 B hB hF
  have h4346 : mixedVector B (Sum.inr 4346) = Sparse.eval nodeValue4346 (mixedVector B) := by
    change mixedMoment B node4346 node4346Labels = _
    exact sound4346 B hB hF
  have h4349 : mixedVector B (Sum.inr 4349) = Sparse.eval nodeValue4349 (mixedVector B) := by
    change mixedMoment B node4349 node4349Labels = _
    exact sound4349 B hB hF
  have h4354 : mixedVector B (Sum.inr 4354) = Sparse.eval nodeValue4354 (mixedVector B) := by
    change mixedMoment B node4354 node4354Labels = _
    exact sound4354 B hB hF
  have h4457 : mixedVector B (Sum.inr 4457) = Sparse.eval nodeValue4457 (mixedVector B) := by
    change mixedMoment B node4457 node4457Labels = _
    exact sound4457 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4466 : mixedVector B (Sum.inr 4466) = Sparse.eval nodeValue4466 (mixedVector B) := by
    change mixedMoment B node4466 node4466Labels = _
    exact sound4466 B hB hF
  have h4495 : mixedVector B (Sum.inr 4495) = Sparse.eval nodeValue4495 (mixedVector B) := by
    change mixedMoment B node4495 node4495Labels = _
    exact sound4495 B hB hF
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
  have h4499 : mixedVector B (Sum.inr 4499) = Sparse.eval nodeValue4499 (mixedVector B) := by
    change mixedMoment B node4499 node4499Labels = _
    exact sound4499 B hB hF
  have h4503 : mixedVector B (Sum.inr 4503) = Sparse.eval nodeValue4503 (mixedVector B) := by
    change mixedMoment B node4503 node4503Labels = _
    exact sound4503 B hB hF
  have h4505 : mixedVector B (Sum.inr 4505) = Sparse.eval nodeValue4505 (mixedVector B) := by
    change mixedMoment B node4505 node4505Labels = _
    exact sound4505 B hB hF
  have h4511 : mixedVector B (Sum.inr 4511) = Sparse.eval nodeValue4511 (mixedVector B) := by
    change mixedMoment B node4511 node4511Labels = _
    exact sound4511 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4894 : mixedVector B (Sum.inr 4894) = Sparse.eval nodeValue4894 (mixedVector B) := by
    change mixedMoment B node4894 node4894Labels = _
    exact sound4894 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  simpa only [sourceForm1782, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4084, h4172, h4177, h4180, h4185, h4341, h4346, h4349, h4354, h4457, h4460, h4466, h4495, h4498, h4499, h4503, h4505, h4511, h4834, h4894, h4895, reducedSource1514] using sourceEq1782 B hB

theorem rowSound1514_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1514 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1514, numericCheck1514, reducedZero1514 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1514_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1514_e_oai
