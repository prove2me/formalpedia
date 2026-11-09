-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:54:10.056957+00:00
-- url     : https://prove2.me/submissions/fc117869-fca7-41e0-943c-68a89c0ae155

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E105
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1746 raw1746Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw1746 raw1746Labels = mixedMoment B raw1746step0 raw1746step0Labels := by
      have ha : raw1746step0 = (fun i j => raw1746 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1746step0 raw1746; decide +kernel
      have hl : raw1746step0Labels = raw1746Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1746 raw1746Labels permutation32 permutation4
    mixedMoment B raw1746step0 raw1746step0Labels = mixedMoment B raw1746step1 raw1746step1Labels := by
      have ha : raw1746step1 = raw1746step0 := by apply Matrix.ext; unfold raw1746step1 raw1746step0; decide +kernel
      have hl : raw1746step0Labels = labelEmbedding7 ∘ raw1746step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1746step0 raw1746step0Labels raw1746step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

theorem canonical1747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1747 raw1747Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw1747 raw1747Labels = mixedMoment B raw1747step0 raw1747step0Labels := by
      have ha : raw1747step0 = (fun i j => raw1747 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1747step0 raw1747; decide +kernel
      have hl : raw1747step0Labels = raw1747Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1747 raw1747Labels permutation32 permutation4
    _ = mixedMoment B node2028 node2028Labels := by rfl

theorem canonical1748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1748 raw1748Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw1748 raw1748Labels = mixedMoment B raw1748step0 raw1748step0Labels := by
      have ha : raw1748step0 = (fun i j => raw1748 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1748step0 raw1748; decide +kernel
      have hl : raw1748step0Labels = raw1748Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1748 raw1748Labels permutation34 permutation6
    mixedMoment B raw1748step0 raw1748step0Labels = mixedMoment B raw1748step1 raw1748step1Labels := by
      have ha : raw1748step1 = -raw1748step0 := by apply Matrix.ext; change ∀ i j, raw1748step1 i j = -(raw1748step0 i j); unfold raw1748step1 raw1748step0; decide +kernel
      have hl : raw1748step1Labels = raw1748step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1748step1 raw1748step1Labels = mixedMoment B raw1748step2 raw1748step2Labels := by
      have ha : raw1748step2 = raw1748step1 := by apply Matrix.ext; unfold raw1748step2 raw1748step1; decide +kernel
      have hl : raw1748step1Labels = labelEmbedding1 ∘ raw1748step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1748step1 raw1748step1Labels raw1748step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

theorem canonical1791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1791 raw1791Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw1791 raw1791Labels = mixedMoment B raw1791step0 raw1791step0Labels := by
      have ha : raw1791step0 = (fun i j => raw1791 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1791step0 raw1791; decide +kernel
      have hl : raw1791step0Labels = raw1791Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1791 raw1791Labels permutation32 permutation4
    mixedMoment B raw1791step0 raw1791step0Labels = mixedMoment B raw1791step1 raw1791step1Labels := by
      have ha : raw1791step1 = raw1791step0 := by apply Matrix.ext; unfold raw1791step1 raw1791step0; decide +kernel
      have hl : raw1791step0Labels = labelEmbedding7 ∘ raw1791step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1791step0 raw1791step0Labels raw1791step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

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

theorem canonical1792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1792 raw1792Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw1792 raw1792Labels = mixedMoment B raw1792step0 raw1792step0Labels := by
      have ha : raw1792step0 = (fun i j => raw1792 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1792step0 raw1792; decide +kernel
      have hl : raw1792step0Labels = raw1792Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1792 raw1792Labels permutation32 permutation4
    _ = mixedMoment B node2106 node2106Labels := by rfl

theorem canonical1793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1793 raw1793Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw1793 raw1793Labels = mixedMoment B raw1793step0 raw1793step0Labels := by
      have ha : raw1793step0 = (fun i j => raw1793 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1793step0 raw1793; decide +kernel
      have hl : raw1793step0Labels = raw1793Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1793 raw1793Labels permutation40 permutation6
    mixedMoment B raw1793step0 raw1793step0Labels = mixedMoment B raw1793step1 raw1793step1Labels := by
      have ha : raw1793step1 = -raw1793step0 := by apply Matrix.ext; change ∀ i j, raw1793step1 i j = -(raw1793step0 i j); unfold raw1793step1 raw1793step0; decide +kernel
      have hl : raw1793step1Labels = raw1793step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1793step1 raw1793step1Labels = mixedMoment B raw1793step2 raw1793step2Labels := by
      have ha : raw1793step2 = raw1793step1 := by apply Matrix.ext; unfold raw1793step2 raw1793step1; decide +kernel
      have hl : raw1793step1Labels = labelEmbedding1 ∘ raw1793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1793step1 raw1793step1Labels raw1793step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

theorem canonical1797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1797 raw1797Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw1797 raw1797Labels = mixedMoment B raw1797step0 raw1797step0Labels := by
      have ha : raw1797step0 = (fun i j => raw1797 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1797step0 raw1797; decide +kernel
      have hl : raw1797step0Labels = raw1797Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1797 raw1797Labels permutation8 permutation4
    mixedMoment B raw1797step0 raw1797step0Labels = mixedMoment B raw1797step1 raw1797step1Labels := by
      have ha : raw1797step1 = raw1797step0 := by apply Matrix.ext; unfold raw1797step1 raw1797step0; decide +kernel
      have hl : raw1797step0Labels = labelEmbedding7 ∘ raw1797step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1797step0 raw1797step0Labels raw1797step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4868 node4868Labels := by rfl

theorem canonical1798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1798 raw1798Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw1798 raw1798Labels = mixedMoment B raw1798step0 raw1798step0Labels := by
      have ha : raw1798step0 = (fun i j => raw1798 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1798step0 raw1798; decide +kernel
      have hl : raw1798step0Labels = raw1798Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1798 raw1798Labels permutation8 permutation4
    _ = mixedMoment B node2109 node2109Labels := by rfl

theorem canonical1799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1799 raw1799Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw1799 raw1799Labels = mixedMoment B raw1799step0 raw1799step0Labels := by
      have ha : raw1799step0 = (fun i j => raw1799 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1799step0 raw1799; decide +kernel
      have hl : raw1799step0Labels = raw1799Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1799 raw1799Labels permutation10 permutation6
    mixedMoment B raw1799step0 raw1799step0Labels = mixedMoment B raw1799step1 raw1799step1Labels := by
      have ha : raw1799step1 = -raw1799step0 := by apply Matrix.ext; change ∀ i j, raw1799step1 i j = -(raw1799step0 i j); unfold raw1799step1 raw1799step0; decide +kernel
      have hl : raw1799step1Labels = raw1799step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1799step1 raw1799step1Labels = mixedMoment B raw1799step2 raw1799step2Labels := by
      have ha : raw1799step2 = raw1799step1 := by apply Matrix.ext; unfold raw1799step2 raw1799step1; decide +kernel
      have hl : raw1799step1Labels = labelEmbedding1 ∘ raw1799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1799step1 raw1799step1Labels raw1799step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

theorem canonical1824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1824 raw1824Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw1824 raw1824Labels = mixedMoment B raw1824step0 raw1824step0Labels := by
      have ha : raw1824step0 = (fun i j => raw1824 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1824step0 raw1824; decide +kernel
      have hl : raw1824step0Labels = raw1824Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1824 raw1824Labels permutation8 permutation4
    mixedMoment B raw1824step0 raw1824step0Labels = mixedMoment B raw1824step1 raw1824step1Labels := by
      have ha : raw1824step1 = raw1824step0 := by apply Matrix.ext; unfold raw1824step1 raw1824step0; decide +kernel
      have hl : raw1824step0Labels = labelEmbedding7 ∘ raw1824step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1824step0 raw1824step0Labels raw1824step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

theorem canonical1825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1825 raw1825Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw1825 raw1825Labels = mixedMoment B raw1825step0 raw1825step0Labels := by
      have ha : raw1825step0 = (fun i j => raw1825 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1825step0 raw1825; decide +kernel
      have hl : raw1825step0Labels = raw1825Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1825 raw1825Labels permutation8 permutation4
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical1826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1826 raw1826Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw1826 raw1826Labels = mixedMoment B raw1826step0 raw1826step0Labels := by
      have ha : raw1826step0 = (fun i j => raw1826 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1826step0 raw1826; decide +kernel
      have hl : raw1826step0Labels = raw1826Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1826 raw1826Labels permutation12 permutation6
    mixedMoment B raw1826step0 raw1826step0Labels = mixedMoment B raw1826step1 raw1826step1Labels := by
      have ha : raw1826step1 = -raw1826step0 := by apply Matrix.ext; change ∀ i j, raw1826step1 i j = -(raw1826step0 i j); unfold raw1826step1 raw1826step0; decide +kernel
      have hl : raw1826step1Labels = raw1826step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1826step1 raw1826step1Labels = mixedMoment B raw1826step2 raw1826step2Labels := by
      have ha : raw1826step2 = raw1826step1 := by apply Matrix.ext; unfold raw1826step2 raw1826step1; decide +kernel
      have hl : raw1826step1Labels = labelEmbedding1 ∘ raw1826step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1826step1 raw1826step1Labels raw1826step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2278 node2278Labels := by rfl

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

theorem canonical2295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2295 raw2295Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw2295 raw2295Labels = mixedMoment B raw2295step0 raw2295step0Labels := by
      have ha : raw2295step0 = (fun i j => raw2295 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2295step0 raw2295; decide +kernel
      have hl : raw2295step0Labels = raw2295Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2295 raw2295Labels permutation8 permutation4
    mixedMoment B raw2295step0 raw2295step0Labels = mixedMoment B raw2295step1 raw2295step1Labels := by
      have ha : raw2295step1 = raw2295step0 := by apply Matrix.ext; unfold raw2295step1 raw2295step0; decide +kernel
      have hl : raw2295step0Labels = labelEmbedding7 ∘ raw2295step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2295step0 raw2295step0Labels raw2295step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

theorem canonical2296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2296 raw2296Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw2296 raw2296Labels = mixedMoment B raw2296step0 raw2296step0Labels := by
      have ha : raw2296step0 = (fun i j => raw2296 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2296step0 raw2296; decide +kernel
      have hl : raw2296step0Labels = raw2296Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2296 raw2296Labels permutation8 permutation4
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical2297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2297 raw2297Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw2297 raw2297Labels = mixedMoment B raw2297step0 raw2297step0Labels := by
      have ha : raw2297step0 = (fun i j => raw2297 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2297step0 raw2297; decide +kernel
      have hl : raw2297step0Labels = raw2297Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2297 raw2297Labels permutation10 permutation6
    mixedMoment B raw2297step0 raw2297step0Labels = mixedMoment B raw2297step1 raw2297step1Labels := by
      have ha : raw2297step1 = -raw2297step0 := by apply Matrix.ext; change ∀ i j, raw2297step1 i j = -(raw2297step0 i j); unfold raw2297step1 raw2297step0; decide +kernel
      have hl : raw2297step1Labels = raw2297step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2297step1 raw2297step1Labels = mixedMoment B raw2297step2 raw2297step2Labels := by
      have ha : raw2297step2 = raw2297step1 := by apply Matrix.ext; unfold raw2297step2 raw2297step1; decide +kernel
      have hl : raw2297step1Labels = labelEmbedding1 ∘ raw2297step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2297step1 raw2297step1Labels raw2297step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical179
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22928 raw22928Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw22928 raw22928Labels = mixedMoment B raw22928step0 raw22928step0Labels := by
      have hz : ∀ j, raw22928 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22928step0 = (fun i j => raw22928 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22928step0 raw22928; decide +kernel
      have hl : raw22928step0Labels = raw22928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22928 raw22928Labels permutation434 hz
    mixedMoment B raw22928step0 raw22928step0Labels = mixedMoment B raw22928step1 raw22928step1Labels := by
      have ha : raw22928step1 = (fun i j => raw22928step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22928step1 raw22928step0; decide +kernel
      have hl : raw22928step1Labels = raw22928step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22928step0 raw22928step0Labels permutation39 permutation2
    _ = mixedMoment B node4810 node4810Labels := by rfl

theorem canonical22929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22929 raw22929Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw22929 raw22929Labels = mixedMoment B raw22929step0 raw22929step0Labels := by
      have hz : ∀ j, raw22929 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22929step0 = (fun i j => raw22929 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22929step0 raw22929; decide +kernel
      have hl : raw22929step0Labels = raw22929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22929 raw22929Labels permutation346 hz
    mixedMoment B raw22929step0 raw22929step0Labels = mixedMoment B raw22929step1 raw22929step1Labels := by
      have ha : raw22929step1 = (fun i j => raw22929step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22929step1 raw22929step0; decide +kernel
      have hl : raw22929step1Labels = raw22929step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22929step0 raw22929step0Labels permutation39 permutation2
    _ = mixedMoment B node4810 node4810Labels := by rfl

theorem canonical22930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22930 raw22930Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw22930 raw22930Labels = mixedMoment B raw22930step0 raw22930step0Labels := by
      have hz : ∀ j, raw22930 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22930step0 = (fun i j => raw22930 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22930step0 raw22930; decide +kernel
      have hl : raw22930step0Labels = raw22930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22930 raw22930Labels permutation434 hz
    mixedMoment B raw22930step0 raw22930step0Labels = mixedMoment B raw22930step1 raw22930step1Labels := by
      have hz : ∀ j, raw22930step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22930step1 = (fun i j => raw22930step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22930step1 raw22930step0; decide +kernel
      have hl : raw22930step1Labels = raw22930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22930step0 raw22930step0Labels permutation80 hz
    _ = mixedMoment B node4896 node4896Labels := by rfl

theorem canonical22931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22931 raw22931Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw22931 raw22931Labels = mixedMoment B raw22931step0 raw22931step0Labels := by
      have hz : ∀ j, raw22931 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22931step0 = (fun i j => raw22931 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22931step0 raw22931; decide +kernel
      have hl : raw22931step0Labels = raw22931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22931 raw22931Labels permutation434 hz
    mixedMoment B raw22931step0 raw22931step0Labels = mixedMoment B raw22931step1 raw22931step1Labels := by
      have hz : ∀ j, raw22931step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22931step1 = (fun i j => raw22931step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22931step1 raw22931step0; decide +kernel
      have hl : raw22931step1Labels = raw22931step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22931step0 raw22931step0Labels permutation80 hz
    mixedMoment B raw22931step1 raw22931step1Labels = mixedMoment B raw22931step2 raw22931step2Labels := by
      have ha : raw22931step2 = (fun i j => raw22931step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22931step2 raw22931step1; decide +kernel
      have hl : raw22931step2Labels = raw22931step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22931step1 raw22931step1Labels permutation9 permutation2
    _ = mixedMoment B node4894 node4894Labels := by rfl

theorem canonical22938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22938 raw22938Labels = mixedMoment B node4368 node4368Labels := by
  calc
    mixedMoment B raw22938 raw22938Labels = mixedMoment B raw22938step0 raw22938step0Labels := by
      have hz : ∀ j, raw22938 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22938step0 = (fun i j => raw22938 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22938step0 raw22938; decide +kernel
      have hl : raw22938step0Labels = raw22938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22938 raw22938Labels permutation434 hz
    mixedMoment B raw22938step0 raw22938step0Labels = mixedMoment B raw22938step1 raw22938step1Labels := by
      have ha : raw22938step1 = (fun i j => raw22938step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22938step1 raw22938step0; decide +kernel
      have hl : raw22938step1Labels = raw22938step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22938step0 raw22938step0Labels permutation33 permutation2
    _ = mixedMoment B node4368 node4368Labels := by rfl

theorem canonical22943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22943 raw22943Labels = mixedMoment B node4368 node4368Labels := by
  calc
    mixedMoment B raw22943 raw22943Labels = mixedMoment B raw22943step0 raw22943step0Labels := by
      have hz : ∀ j, raw22943 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22943step0 = (fun i j => raw22943 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22943step0 raw22943; decide +kernel
      have hl : raw22943step0Labels = raw22943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22943 raw22943Labels permutation346 hz
    mixedMoment B raw22943step0 raw22943step0Labels = mixedMoment B raw22943step1 raw22943step1Labels := by
      have ha : raw22943step1 = (fun i j => raw22943step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22943step1 raw22943step0; decide +kernel
      have hl : raw22943step1Labels = raw22943step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22943step0 raw22943step0Labels permutation33 permutation2
    _ = mixedMoment B node4368 node4368Labels := by rfl

theorem canonical22948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22948 raw22948Labels = mixedMoment B node4373 node4373Labels := by
  calc
    mixedMoment B raw22948 raw22948Labels = mixedMoment B raw22948step0 raw22948step0Labels := by
      have hz : ∀ j, raw22948 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22948step0 = (fun i j => raw22948 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22948step0 raw22948; decide +kernel
      have hl : raw22948step0Labels = raw22948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22948 raw22948Labels permutation434 hz
    mixedMoment B raw22948step0 raw22948step0Labels = mixedMoment B raw22948step1 raw22948step1Labels := by
      have hz : ∀ j, raw22948step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22948step1 = (fun i j => raw22948step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22948step1 raw22948step0; decide +kernel
      have hl : raw22948step1Labels = raw22948step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22948step0 raw22948step0Labels permutation80 hz
    mixedMoment B raw22948step1 raw22948step1Labels = mixedMoment B raw22948step2 raw22948step2Labels := by
      have ha : raw22948step2 = (fun i j => raw22948step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22948step2 raw22948step1; decide +kernel
      have hl : raw22948step2Labels = raw22948step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22948step1 raw22948step1Labels permutation9 permutation2
    _ = mixedMoment B node4373 node4373Labels := by rfl

theorem canonical22953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22953 raw22953Labels = mixedMoment B node4375 node4375Labels := by
  calc
    mixedMoment B raw22953 raw22953Labels = mixedMoment B raw22953step0 raw22953step0Labels := by
      have hz : ∀ j, raw22953 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22953step0 = (fun i j => raw22953 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22953step0 raw22953; decide +kernel
      have hl : raw22953step0Labels = raw22953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22953 raw22953Labels permutation434 hz
    mixedMoment B raw22953step0 raw22953step0Labels = mixedMoment B raw22953step1 raw22953step1Labels := by
      have hz : ∀ j, raw22953step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22953step1 = (fun i j => raw22953step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22953step1 raw22953step0; decide +kernel
      have hl : raw22953step1Labels = raw22953step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22953step0 raw22953step0Labels permutation80 hz
    _ = mixedMoment B node4375 node4375Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical241
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30936 raw30936Labels = mixedMoment B node5297 node5297Labels := by
  calc
    mixedMoment B raw30936 raw30936Labels = mixedMoment B raw30936step0 raw30936step0Labels := by
      have hz : ∀ j, raw30936 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30936step0 = (fun i j => raw30936 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30936step0 raw30936; decide +kernel
      have hl : raw30936step0Labels = raw30936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30936 raw30936Labels permutation434 hz
    mixedMoment B raw30936step0 raw30936step0Labels = mixedMoment B raw30936step1 raw30936step1Labels := by
      have hz : ∀ j, raw30936step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30936step1 = (fun i j => raw30936step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30936step1 raw30936step0; decide +kernel
      have hl : raw30936step1Labels = raw30936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30936step0 raw30936step0Labels permutation80 hz
    mixedMoment B raw30936step1 raw30936step1Labels = mixedMoment B raw30936step2 raw30936step2Labels := by
      have ha : raw30936step2 = (fun i j => raw30936step1 (permutation16 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30936step2 raw30936step1; decide +kernel
      have hl : raw30936step2Labels = raw30936step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30936step1 raw30936step1Labels permutation16 permutation5
    mixedMoment B raw30936step2 raw30936step2Labels = mixedMoment B raw30936step3 raw30936step3Labels := by
      have ha : raw30936step3 = -raw30936step2 := by apply Matrix.ext; change ∀ i j, raw30936step3 i j = -(raw30936step2 i j); unfold raw30936step3 raw30936step2; decide +kernel
      have hl : raw30936step3Labels = raw30936step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30936step3 raw30936step3Labels = mixedMoment B raw30936step4 raw30936step4Labels := by
      have ha : raw30936step4 = raw30936step3 := by apply Matrix.ext; unfold raw30936step4 raw30936step3; decide +kernel
      have hl : raw30936step3Labels = labelEmbedding8 ∘ raw30936step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30936step3 raw30936step3Labels raw30936step4Labels labelEmbedding8 hl
    _ = mixedMoment B node5297 node5297Labels := by rfl

theorem canonical30937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30937 raw30937Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw30937 raw30937Labels = mixedMoment B raw30937step0 raw30937step0Labels := by
      have hz : ∀ j, raw30937 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30937step0 = (fun i j => raw30937 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30937step0 raw30937; decide +kernel
      have hl : raw30937step0Labels = raw30937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30937 raw30937Labels permutation434 hz
    mixedMoment B raw30937step0 raw30937step0Labels = mixedMoment B raw30937step1 raw30937step1Labels := by
      have ha : raw30937step1 = (fun i j => raw30937step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30937step1 raw30937step0; decide +kernel
      have hl : raw30937step1Labels = raw30937step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30937step0 raw30937step0Labels permutation42 permutation7
    mixedMoment B raw30937step1 raw30937step1Labels = mixedMoment B raw30937step2 raw30937step2Labels := by
      have ha : raw30937step2 = -raw30937step1 := by apply Matrix.ext; change ∀ i j, raw30937step2 i j = -(raw30937step1 i j); unfold raw30937step2 raw30937step1; decide +kernel
      have hl : raw30937step2Labels = raw30937step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30937step2 raw30937step2Labels = mixedMoment B raw30937step3 raw30937step3Labels := by
      have ha : raw30937step3 = raw30937step2 := by apply Matrix.ext; unfold raw30937step3 raw30937step2; decide +kernel
      have hl : raw30937step2Labels = labelEmbedding10 ∘ raw30937step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30937step2 raw30937step2Labels raw30937step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

theorem canonical30938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30938 raw30938Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw30938 raw30938Labels = mixedMoment B raw30938step0 raw30938step0Labels := by
      have hz : ∀ j, raw30938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30938step0 = (fun i j => raw30938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30938step0 raw30938; decide +kernel
      have hl : raw30938step0Labels = raw30938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30938 raw30938Labels permutation346 hz
    mixedMoment B raw30938step0 raw30938step0Labels = mixedMoment B raw30938step1 raw30938step1Labels := by
      have ha : raw30938step1 = (fun i j => raw30938step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30938step1 raw30938step0; decide +kernel
      have hl : raw30938step1Labels = raw30938step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30938step0 raw30938step0Labels permutation42 permutation7
    mixedMoment B raw30938step1 raw30938step1Labels = mixedMoment B raw30938step2 raw30938step2Labels := by
      have ha : raw30938step2 = -raw30938step1 := by apply Matrix.ext; change ∀ i j, raw30938step2 i j = -(raw30938step1 i j); unfold raw30938step2 raw30938step1; decide +kernel
      have hl : raw30938step2Labels = raw30938step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30938step2 raw30938step2Labels = mixedMoment B raw30938step3 raw30938step3Labels := by
      have ha : raw30938step3 = raw30938step2 := by apply Matrix.ext; unfold raw30938step3 raw30938step2; decide +kernel
      have hl : raw30938step2Labels = labelEmbedding10 ∘ raw30938step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30938step2 raw30938step2Labels raw30938step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

theorem canonical30939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30939 raw30939Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw30939 raw30939Labels = mixedMoment B raw30939step0 raw30939step0Labels := by
      have hz : ∀ j, raw30939 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30939step0 = (fun i j => raw30939 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30939step0 raw30939; decide +kernel
      have hl : raw30939step0Labels = raw30939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30939 raw30939Labels permutation434 hz
    mixedMoment B raw30939step0 raw30939step0Labels = mixedMoment B raw30939step1 raw30939step1Labels := by
      have hz : ∀ j, raw30939step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30939step1 = (fun i j => raw30939step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30939step1 raw30939step0; decide +kernel
      have hl : raw30939step1Labels = raw30939step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30939step0 raw30939step0Labels permutation80 hz
    mixedMoment B raw30939step1 raw30939step1Labels = mixedMoment B raw30939step2 raw30939step2Labels := by
      have ha : raw30939step2 = (fun i j => raw30939step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30939step2 raw30939step1; decide +kernel
      have hl : raw30939step2Labels = raw30939step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30939step1 raw30939step1Labels permutation12 permutation7
    mixedMoment B raw30939step2 raw30939step2Labels = mixedMoment B raw30939step3 raw30939step3Labels := by
      have ha : raw30939step3 = -raw30939step2 := by apply Matrix.ext; change ∀ i j, raw30939step3 i j = -(raw30939step2 i j); unfold raw30939step3 raw30939step2; decide +kernel
      have hl : raw30939step3Labels = raw30939step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30939step3 raw30939step3Labels = mixedMoment B raw30939step4 raw30939step4Labels := by
      have ha : raw30939step4 = raw30939step3 := by apply Matrix.ext; unfold raw30939step4 raw30939step3; decide +kernel
      have hl : raw30939step3Labels = labelEmbedding10 ∘ raw30939step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30939step3 raw30939step3Labels raw30939step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

theorem canonical30940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30940 raw30940Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw30940 raw30940Labels = mixedMoment B raw30940step0 raw30940step0Labels := by
      have hz : ∀ j, raw30940 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30940step0 = (fun i j => raw30940 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30940step0 raw30940; decide +kernel
      have hl : raw30940step0Labels = raw30940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30940 raw30940Labels permutation434 hz
    mixedMoment B raw30940step0 raw30940step0Labels = mixedMoment B raw30940step1 raw30940step1Labels := by
      have hz : ∀ j, raw30940step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30940step1 = (fun i j => raw30940step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30940step1 raw30940step0; decide +kernel
      have hl : raw30940step1Labels = raw30940step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30940step0 raw30940step0Labels permutation80 hz
    mixedMoment B raw30940step1 raw30940step1Labels = mixedMoment B raw30940step2 raw30940step2Labels := by
      have ha : raw30940step2 = (fun i j => raw30940step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30940step2 raw30940step1; decide +kernel
      have hl : raw30940step2Labels = raw30940step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30940step1 raw30940step1Labels permutation12 permutation7
    mixedMoment B raw30940step2 raw30940step2Labels = mixedMoment B raw30940step3 raw30940step3Labels := by
      have ha : raw30940step3 = -raw30940step2 := by apply Matrix.ext; change ∀ i j, raw30940step3 i j = -(raw30940step2 i j); unfold raw30940step3 raw30940step2; decide +kernel
      have hl : raw30940step3Labels = raw30940step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30940step3 raw30940step3Labels = mixedMoment B raw30940step4 raw30940step4Labels := by
      have ha : raw30940step4 = raw30940step3 := by apply Matrix.ext; unfold raw30940step4 raw30940step3; decide +kernel
      have hl : raw30940step3Labels = labelEmbedding10 ∘ raw30940step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30940step3 raw30940step3Labels raw30940step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

theorem canonical30941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30941 raw30941Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw30941 raw30941Labels = mixedMoment B raw30941step0 raw30941step0Labels := by
      have hz : ∀ j, raw30941 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30941step0 = (fun i j => raw30941 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30941step0 raw30941; decide +kernel
      have hl : raw30941step0Labels = raw30941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30941 raw30941Labels permutation434 hz
    mixedMoment B raw30941step0 raw30941step0Labels = mixedMoment B raw30941step1 raw30941step1Labels := by
      have hz : ∀ j, raw30941step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30941step1 = (fun i j => raw30941step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30941step1 raw30941step0; decide +kernel
      have hl : raw30941step1Labels = raw30941step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30941step0 raw30941step0Labels permutation80 hz
    mixedMoment B raw30941step1 raw30941step1Labels = mixedMoment B raw30941step2 raw30941step2Labels := by
      have ha : raw30941step2 = (fun i j => raw30941step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30941step2 raw30941step1; decide +kernel
      have hl : raw30941step2Labels = raw30941step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30941step1 raw30941step1Labels permutation9 permutation2
    _ = mixedMoment B node4466 node4466Labels := by rfl

theorem canonical30942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30942 raw30942Labels = mixedMoment B node4700 node4700Labels := by
  calc
    mixedMoment B raw30942 raw30942Labels = mixedMoment B raw30942step0 raw30942step0Labels := by
      have hz : ∀ j, raw30942 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30942step0 = (fun i j => raw30942 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30942step0 raw30942; decide +kernel
      have hl : raw30942step0Labels = raw30942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30942 raw30942Labels permutation434 hz
    mixedMoment B raw30942step0 raw30942step0Labels = mixedMoment B raw30942step1 raw30942step1Labels := by
      have ha : raw30942step1 = (fun i j => raw30942step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30942step1 raw30942step0; decide +kernel
      have hl : raw30942step1Labels = raw30942step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30942step0 raw30942step0Labels permutation33 permutation2
    _ = mixedMoment B node4700 node4700Labels := by rfl

theorem canonical30943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30943 raw30943Labels = mixedMoment B node4773 node4773Labels := by
  calc
    mixedMoment B raw30943 raw30943Labels = mixedMoment B raw30943step0 raw30943step0Labels := by
      have ha : raw30943step0 = (fun i j => raw30943 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30943step0 raw30943; decide +kernel
      have hl : raw30943step0Labels = raw30943Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30943 raw30943Labels permutation201 permutation2
    _ = mixedMoment B node4773 node4773Labels := by rfl

theorem canonical30944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30944 raw30944Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw30944 raw30944Labels = mixedMoment B raw30944step0 raw30944step0Labels := by
      have hz : ∀ j, raw30944 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30944step0 = (fun i j => raw30944 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30944step0 raw30944; decide +kernel
      have hl : raw30944step0Labels = raw30944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30944 raw30944Labels permutation434 hz
    _ = mixedMoment B node4867 node4867Labels := by rfl

theorem canonical30945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30945 raw30945Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw30945 raw30945Labels = mixedMoment B raw30945step0 raw30945step0Labels := by
      have hz : ∀ j, raw30945 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30945step0 = (fun i j => raw30945 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30945step0 raw30945; decide +kernel
      have hl : raw30945step0Labels = raw30945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30945 raw30945Labels permutation434 hz
    mixedMoment B raw30945step0 raw30945step0Labels = mixedMoment B raw30945step1 raw30945step1Labels := by
      have ha : raw30945step1 = (fun i j => raw30945step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30945step1 raw30945step0; decide +kernel
      have hl : raw30945step1Labels = raw30945step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30945step0 raw30945step0Labels permutation33 permutation2
    _ = mixedMoment B node4865 node4865Labels := by rfl

theorem canonical30946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30946 raw30946Labels = mixedMoment B node4700 node4700Labels := by
  calc
    mixedMoment B raw30946 raw30946Labels = mixedMoment B raw30946step0 raw30946step0Labels := by
      have hz : ∀ j, raw30946 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30946step0 = (fun i j => raw30946 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30946step0 raw30946; decide +kernel
      have hl : raw30946step0Labels = raw30946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30946 raw30946Labels permutation346 hz
    mixedMoment B raw30946step0 raw30946step0Labels = mixedMoment B raw30946step1 raw30946step1Labels := by
      have ha : raw30946step1 = (fun i j => raw30946step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30946step1 raw30946step0; decide +kernel
      have hl : raw30946step1Labels = raw30946step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30946step0 raw30946step0Labels permutation33 permutation2
    _ = mixedMoment B node4700 node4700Labels := by rfl

theorem canonical30947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30947 raw30947Labels = mixedMoment B node4773 node4773Labels := by
  calc
    mixedMoment B raw30947 raw30947Labels = mixedMoment B raw30947step0 raw30947step0Labels := by
      have ha : raw30947step0 = (fun i j => raw30947 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30947step0 raw30947; decide +kernel
      have hl : raw30947step0Labels = raw30947Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30947 raw30947Labels permutation177 permutation2
    _ = mixedMoment B node4773 node4773Labels := by rfl

theorem canonical30948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30948 raw30948Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw30948 raw30948Labels = mixedMoment B raw30948step0 raw30948step0Labels := by
      have hz : ∀ j, raw30948 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30948step0 = (fun i j => raw30948 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30948step0 raw30948; decide +kernel
      have hl : raw30948step0Labels = raw30948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30948 raw30948Labels permutation346 hz
    _ = mixedMoment B node4867 node4867Labels := by rfl

theorem canonical30949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30949 raw30949Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw30949 raw30949Labels = mixedMoment B raw30949step0 raw30949step0Labels := by
      have hz : ∀ j, raw30949 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30949step0 = (fun i j => raw30949 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30949step0 raw30949; decide +kernel
      have hl : raw30949step0Labels = raw30949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30949 raw30949Labels permutation346 hz
    mixedMoment B raw30949step0 raw30949step0Labels = mixedMoment B raw30949step1 raw30949step1Labels := by
      have ha : raw30949step1 = (fun i j => raw30949step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30949step1 raw30949step0; decide +kernel
      have hl : raw30949step1Labels = raw30949step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30949step0 raw30949step0Labels permutation33 permutation2
    _ = mixedMoment B node4865 node4865Labels := by rfl

theorem canonical30950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30950 raw30950Labels = mixedMoment B node4704 node4704Labels := by
  calc
    mixedMoment B raw30950 raw30950Labels = mixedMoment B raw30950step0 raw30950step0Labels := by
      have hz : ∀ j, raw30950 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30950step0 = (fun i j => raw30950 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30950step0 raw30950; decide +kernel
      have hl : raw30950step0Labels = raw30950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30950 raw30950Labels permutation434 hz
    mixedMoment B raw30950step0 raw30950step0Labels = mixedMoment B raw30950step1 raw30950step1Labels := by
      have hz : ∀ j, raw30950step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30950step1 = (fun i j => raw30950step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30950step1 raw30950step0; decide +kernel
      have hl : raw30950step1Labels = raw30950step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30950step0 raw30950step0Labels permutation80 hz
    mixedMoment B raw30950step1 raw30950step1Labels = mixedMoment B raw30950step2 raw30950step2Labels := by
      have ha : raw30950step2 = (fun i j => raw30950step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30950step2 raw30950step1; decide +kernel
      have hl : raw30950step2Labels = raw30950step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30950step1 raw30950step1Labels permutation9 permutation2
    _ = mixedMoment B node4704 node4704Labels := by rfl

theorem canonical30951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30951 raw30951Labels = mixedMoment B node4776 node4776Labels := by
  calc
    mixedMoment B raw30951 raw30951Labels = mixedMoment B raw30951step0 raw30951step0Labels := by
      have hz : ∀ j, raw30951 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30951step0 = (fun i j => raw30951 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30951step0 raw30951; decide +kernel
      have hl : raw30951step0Labels = raw30951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30951 raw30951Labels permutation434 hz
    mixedMoment B raw30951step0 raw30951step0Labels = mixedMoment B raw30951step1 raw30951step1Labels := by
      have ha : raw30951step1 = (fun i j => raw30951step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30951step1 raw30951step0; decide +kernel
      have hl : raw30951step1Labels = raw30951step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30951step0 raw30951step0Labels permutation39 permutation2
    _ = mixedMoment B node4776 node4776Labels := by rfl

theorem canonical30952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30952 raw30952Labels = mixedMoment B node4776 node4776Labels := by
  calc
    mixedMoment B raw30952 raw30952Labels = mixedMoment B raw30952step0 raw30952step0Labels := by
      have hz : ∀ j, raw30952 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30952step0 = (fun i j => raw30952 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30952step0 raw30952; decide +kernel
      have hl : raw30952step0Labels = raw30952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30952 raw30952Labels permutation346 hz
    mixedMoment B raw30952step0 raw30952step0Labels = mixedMoment B raw30952step1 raw30952step1Labels := by
      have ha : raw30952step1 = (fun i j => raw30952step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30952step1 raw30952step0; decide +kernel
      have hl : raw30952step1Labels = raw30952step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30952step0 raw30952step0Labels permutation39 permutation2
    _ = mixedMoment B node4776 node4776Labels := by rfl

theorem canonical30953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30953 raw30953Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw30953 raw30953Labels = mixedMoment B raw30953step0 raw30953step0Labels := by
      have hz : ∀ j, raw30953 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30953step0 = (fun i j => raw30953 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30953step0 raw30953; decide +kernel
      have hl : raw30953step0Labels = raw30953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30953 raw30953Labels permutation434 hz
    mixedMoment B raw30953step0 raw30953step0Labels = mixedMoment B raw30953step1 raw30953step1Labels := by
      have hz : ∀ j, raw30953step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30953step1 = (fun i j => raw30953step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30953step1 raw30953step0; decide +kernel
      have hl : raw30953step1Labels = raw30953step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30953step0 raw30953step0Labels permutation80 hz
    mixedMoment B raw30953step1 raw30953step1Labels = mixedMoment B raw30953step2 raw30953step2Labels := by
      have ha : raw30953step2 = (fun i j => raw30953step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30953step2 raw30953step1; decide +kernel
      have hl : raw30953step2Labels = raw30953step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30953step1 raw30953step1Labels permutation9 permutation2
    _ = mixedMoment B node4868 node4868Labels := by rfl

theorem canonical30954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30954 raw30954Labels = mixedMoment B node4694 node4694Labels := by
  calc
    mixedMoment B raw30954 raw30954Labels = mixedMoment B raw30954step0 raw30954step0Labels := by
      have hz : ∀ j, raw30954 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30954step0 = (fun i j => raw30954 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30954step0 raw30954; decide +kernel
      have hl : raw30954step0Labels = raw30954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30954 raw30954Labels permutation434 hz
    mixedMoment B raw30954step0 raw30954step0Labels = mixedMoment B raw30954step1 raw30954step1Labels := by
      have hz : ∀ j, raw30954step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30954step1 = (fun i j => raw30954step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30954step1 raw30954step0; decide +kernel
      have hl : raw30954step1Labels = raw30954step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30954step0 raw30954step0Labels permutation80 hz
    mixedMoment B raw30954step1 raw30954step1Labels = mixedMoment B raw30954step2 raw30954step2Labels := by
      have ha : raw30954step2 = (fun i j => raw30954step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30954step2 raw30954step1; decide +kernel
      have hl : raw30954step2Labels = raw30954step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30954step1 raw30954step1Labels permutation31 permutation3
    mixedMoment B raw30954step2 raw30954step2Labels = mixedMoment B raw30954step3 raw30954step3Labels := by
      have ha : raw30954step3 = -raw30954step2 := by apply Matrix.ext; change ∀ i j, raw30954step3 i j = -(raw30954step2 i j); unfold raw30954step3 raw30954step2; decide +kernel
      have hl : raw30954step3Labels = raw30954step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30954step3 raw30954step3Labels = mixedMoment B raw30954step4 raw30954step4Labels := by
      have ha : raw30954step4 = raw30954step3 := by apply Matrix.ext; unfold raw30954step4 raw30954step3; decide +kernel
      have hl : raw30954step3Labels = labelEmbedding6 ∘ raw30954step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30954step3 raw30954step3Labels raw30954step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4694 node4694Labels := by rfl

theorem canonical30955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30955 raw30955Labels = mixedMoment B node4687 node4687Labels := by
  calc
    mixedMoment B raw30955 raw30955Labels = mixedMoment B raw30955step0 raw30955step0Labels := by
      have hz : ∀ j, raw30955 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30955step0 = (fun i j => raw30955 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30955step0 raw30955; decide +kernel
      have hl : raw30955step0Labels = raw30955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30955 raw30955Labels permutation434 hz
    mixedMoment B raw30955step0 raw30955step0Labels = mixedMoment B raw30955step1 raw30955step1Labels := by
      have ha : raw30955step1 = (fun i j => raw30955step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30955step1 raw30955step0; decide +kernel
      have hl : raw30955step1Labels = raw30955step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30955step0 raw30955step0Labels permutation151 permutation3
    mixedMoment B raw30955step1 raw30955step1Labels = mixedMoment B raw30955step2 raw30955step2Labels := by
      have ha : raw30955step2 = -raw30955step1 := by apply Matrix.ext; change ∀ i j, raw30955step2 i j = -(raw30955step1 i j); unfold raw30955step2 raw30955step1; decide +kernel
      have hl : raw30955step2Labels = raw30955step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30955step2 raw30955step2Labels = mixedMoment B raw30955step3 raw30955step3Labels := by
      have ha : raw30955step3 = raw30955step2 := by apply Matrix.ext; unfold raw30955step3 raw30955step2; decide +kernel
      have hl : raw30955step2Labels = labelEmbedding6 ∘ raw30955step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30955step2 raw30955step2Labels raw30955step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4687 node4687Labels := by rfl

theorem canonical30956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30956 raw30956Labels = mixedMoment B node4687 node4687Labels := by
  calc
    mixedMoment B raw30956 raw30956Labels = mixedMoment B raw30956step0 raw30956step0Labels := by
      have hz : ∀ j, raw30956 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30956step0 = (fun i j => raw30956 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30956step0 raw30956; decide +kernel
      have hl : raw30956step0Labels = raw30956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30956 raw30956Labels permutation346 hz
    mixedMoment B raw30956step0 raw30956step0Labels = mixedMoment B raw30956step1 raw30956step1Labels := by
      have ha : raw30956step1 = (fun i j => raw30956step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30956step1 raw30956step0; decide +kernel
      have hl : raw30956step1Labels = raw30956step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30956step0 raw30956step0Labels permutation151 permutation3
    mixedMoment B raw30956step1 raw30956step1Labels = mixedMoment B raw30956step2 raw30956step2Labels := by
      have ha : raw30956step2 = -raw30956step1 := by apply Matrix.ext; change ∀ i j, raw30956step2 i j = -(raw30956step1 i j); unfold raw30956step2 raw30956step1; decide +kernel
      have hl : raw30956step2Labels = raw30956step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30956step2 raw30956step2Labels = mixedMoment B raw30956step3 raw30956step3Labels := by
      have ha : raw30956step3 = raw30956step2 := by apply Matrix.ext; unfold raw30956step3 raw30956step2; decide +kernel
      have hl : raw30956step2Labels = labelEmbedding6 ∘ raw30956step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30956step2 raw30956step2Labels raw30956step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4687 node4687Labels := by rfl

theorem canonical30957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30957 raw30957Labels = mixedMoment B node4872 node4872Labels := by
  calc
    mixedMoment B raw30957 raw30957Labels = mixedMoment B raw30957step0 raw30957step0Labels := by
      have hz : ∀ j, raw30957 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30957step0 = (fun i j => raw30957 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30957step0 raw30957; decide +kernel
      have hl : raw30957step0Labels = raw30957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30957 raw30957Labels permutation434 hz
    mixedMoment B raw30957step0 raw30957step0Labels = mixedMoment B raw30957step1 raw30957step1Labels := by
      have hz : ∀ j, raw30957step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30957step1 = (fun i j => raw30957step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30957step1 raw30957step0; decide +kernel
      have hl : raw30957step1Labels = raw30957step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30957step0 raw30957step0Labels permutation80 hz
    _ = mixedMoment B node4872 node4872Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4810 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4810 node4810Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2028 node2028Labels + mixedMoment B node2215 node2215Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1746 singletonSmall4810
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4810) = raw1746Labels := by decide +kernel
  rw [hl, canonical1746 B hB] at h
  have hc0 : mixedMoment B raw1746 (Fin.cases (0 : Fin 2) singletonSmall4810) =
      mixedMoment B node2028 node2028Labels := by
    have ha : raw1746 = raw1747 := by apply Matrix.ext; unfold raw1746 raw1747; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4810 = raw1747Labels := by decide +kernel
    rw [ha, hj, canonical1747 B hB]
  have hc1 : mixedMoment B raw1746 (Fin.cases (1 : Fin 2) singletonSmall4810) =
      mixedMoment B node2215 node2215Labels := by
    have ha : raw1746 = raw1748 := by apply Matrix.ext; unfold raw1746 raw1748; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4810 = raw1748Labels := by decide +kernel
    rw [ha, hj, canonical1748 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4865 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4865 node4865Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2106 node2106Labels + mixedMoment B node2242 node2242Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1791 singletonSmall4865
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4865) = raw1791Labels := by decide +kernel
  rw [hl, canonical1791 B hB] at h
  have hc0 : mixedMoment B raw1791 (Fin.cases (0 : Fin 2) singletonSmall4865) =
      mixedMoment B node2106 node2106Labels := by
    have ha : raw1791 = raw1792 := by apply Matrix.ext; unfold raw1791 raw1792; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4865 = raw1792Labels := by decide +kernel
    rw [ha, hj, canonical1792 B hB]
  have hc1 : mixedMoment B raw1791 (Fin.cases (1 : Fin 2) singletonSmall4865) =
      mixedMoment B node2242 node2242Labels := by
    have ha : raw1791 = raw1793 := by apply Matrix.ext; unfold raw1791 raw1793; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4865 = raw1793Labels := by decide +kernel
    rw [ha, hj, canonical1793 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4868 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4868 node4868Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2109 node2109Labels + mixedMoment B node2261 node2261Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1797 singletonSmall4868
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4868) = raw1797Labels := by decide +kernel
  rw [hl, canonical1797 B hB] at h
  have hc0 : mixedMoment B raw1797 (Fin.cases (0 : Fin 2) singletonSmall4868) =
      mixedMoment B node2109 node2109Labels := by
    have ha : raw1797 = raw1798 := by apply Matrix.ext; unfold raw1797 raw1798; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4868 = raw1798Labels := by decide +kernel
    rw [ha, hj, canonical1798 B hB]
  have hc1 : mixedMoment B raw1797 (Fin.cases (1 : Fin 2) singletonSmall4868) =
      mixedMoment B node2261 node2261Labels := by
    have ha : raw1797 = raw1799 := by apply Matrix.ext; unfold raw1797 raw1799; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4868 = raw1799Labels := by decide +kernel
    rw [ha, hj, canonical1799 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4896 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4896 node4896Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2266 node2266Labels + mixedMoment B node2278 node2278Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1824 singletonSmall4896
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4896) = raw1824Labels := by decide +kernel
  rw [hl, canonical1824 B hB] at h
  have hc0 : mixedMoment B raw1824 (Fin.cases (0 : Fin 2) singletonSmall4896) =
      mixedMoment B node2266 node2266Labels := by
    have ha : raw1824 = raw1825 := by apply Matrix.ext; unfold raw1824 raw1825; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4896 = raw1825Labels := by decide +kernel
    rw [ha, hj, canonical1825 B hB]
  have hc1 : mixedMoment B raw1824 (Fin.cases (1 : Fin 2) singletonSmall4896) =
      mixedMoment B node2278 node2278Labels := by
    have ha : raw1824 = raw1826 := by apply Matrix.ext; unfold raw1824 raw1826; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4896 = raw1826Labels := by decide +kernel
    rw [ha, hj, canonical1826 B hB]
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

theorem singleton5291 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5291 node5291Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2765 node2765Labels + mixedMoment B node3582 node3582Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2295 singletonSmall5291
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5291) = raw2295Labels := by decide +kernel
  rw [hl, canonical2295 B hB] at h
  have hc0 : mixedMoment B raw2295 (Fin.cases (0 : Fin 2) singletonSmall5291) =
      mixedMoment B node2765 node2765Labels := by
    have ha : raw2295 = raw2296 := by apply Matrix.ext; unfold raw2295 raw2296; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5291 = raw2296Labels := by decide +kernel
    rw [ha, hj, canonical2296 B hB]
  have hc1 : mixedMoment B raw2295 (Fin.cases (1 : Fin 2) singletonSmall5291) =
      mixedMoment B node3582 node3582Labels := by
    have ha : raw2295 = raw2297 := by apply Matrix.ext; unfold raw2295 raw2297; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5291 = raw2297Labels := by decide +kernel
    rw [ha, hj, canonical2297 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound1049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1049 node1049Labels = Sparse.eval nodeValue1049 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1049) = mixedMoment B node1049 node1049Labels := rfl
  simpa [nodeValue1049, Sparse.eval] using hc.symm

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

theorem sound1738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1738 node1738Labels = Sparse.eval nodeValue1738 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1738) = mixedMoment B node1738 node1738Labels := rfl
  simpa [nodeValue1738, Sparse.eval] using hc.symm

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

theorem sound2028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2028 node2028Labels = Sparse.eval nodeValue2028 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2028) = mixedMoment B node2028 node2028Labels := rfl
  simpa [nodeValue2028, Sparse.eval] using hc.symm

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

theorem sound2106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2106 node2106Labels = Sparse.eval nodeValue2106 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2106) = mixedMoment B node2106 node2106Labels := rfl
  simpa [nodeValue2106, Sparse.eval] using hc.symm

theorem sound2109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2109 node2109Labels = Sparse.eval nodeValue2109 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2109) = mixedMoment B node2109 node2109Labels := rfl
  simpa [nodeValue2109, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2215 node2215Labels = Sparse.eval nodeValue2215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2215) = mixedMoment B node2215 node2215Labels := rfl
  simpa [nodeValue2215, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2242 node2242Labels = Sparse.eval nodeValue2242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2242) = mixedMoment B node2242 node2242Labels := rfl
  simpa [nodeValue2242, Sparse.eval] using hc.symm

theorem sound2261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2261 node2261Labels = Sparse.eval nodeValue2261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2261) = mixedMoment B node2261 node2261Labels := rfl
  simpa [nodeValue2261, Sparse.eval] using hc.symm

theorem sound2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2266 node2266Labels = Sparse.eval nodeValue2266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2266) = mixedMoment B node2266 node2266Labels := rfl
  simpa [nodeValue2266, Sparse.eval] using hc.symm

theorem sound2278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2278 node2278Labels = Sparse.eval nodeValue2278 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2278) = mixedMoment B node2278 node2278Labels := rfl
  simpa [nodeValue2278, Sparse.eval] using hc.symm

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

theorem sound2765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2765 node2765Labels = Sparse.eval nodeValue2765 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2765) = mixedMoment B node2765 node2765Labels := rfl
  simpa [nodeValue2765, Sparse.eval] using hc.symm

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

theorem sound3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3582 node3582Labels = Sparse.eval nodeValue3582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3582) = mixedMoment B node3582 node3582Labels := rfl
  simpa [nodeValue3582, Sparse.eval] using hc.symm

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

theorem sound4368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4368 node4368Labels = Sparse.eval nodeValue4368 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4368) = mixedMoment B node4368 node4368Labels := rfl
  simpa [nodeValue4368, Sparse.eval] using hc.symm

theorem sound4373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4373 node4373Labels = Sparse.eval nodeValue4373 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4373) = mixedMoment B node4373 node4373Labels := rfl
  simpa [nodeValue4373, Sparse.eval] using hc.symm

theorem sound4375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4375 node4375Labels = Sparse.eval nodeValue4375 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4375) = mixedMoment B node4375 node4375Labels := rfl
  simpa [nodeValue4375, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4687 node4687Labels = Sparse.eval nodeValue4687 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4687) = mixedMoment B node4687 node4687Labels := rfl
  simpa [nodeValue4687, Sparse.eval] using hc.symm

theorem sound4694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4694 node4694Labels = Sparse.eval nodeValue4694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4694) = mixedMoment B node4694 node4694Labels := rfl
  simpa [nodeValue4694, Sparse.eval] using hc.symm

theorem sound4700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4700 node4700Labels = Sparse.eval nodeValue4700 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4700) = mixedMoment B node4700 node4700Labels := rfl
  simpa [nodeValue4700, Sparse.eval] using hc.symm

theorem sound4704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4704 node4704Labels = Sparse.eval nodeValue4704 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4704) = mixedMoment B node4704 node4704Labels := rfl
  simpa [nodeValue4704, Sparse.eval] using hc.symm

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

theorem sound4773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4773 node4773Labels = Sparse.eval nodeValue4773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4773) = mixedMoment B node4773 node4773Labels := rfl
  simpa [nodeValue4773, Sparse.eval] using hc.symm

theorem sound4776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4776 node4776Labels = Sparse.eval nodeValue4776 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4776) = mixedMoment B node4776 node4776Labels := rfl
  simpa [nodeValue4776, Sparse.eval] using hc.symm

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

theorem sound4810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4810 node4810Labels = Sparse.eval nodeValue4810 (mixedVector B) := by
  have h := singleton4810 B _hB
  rw [sound2028 B _hB _hF, sound2215 B _hB _hF] at h
  norm_num [nodeValue4810, nodeValue2028, nodeValue2215, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4865 node4865Labels = Sparse.eval nodeValue4865 (mixedVector B) := by
  have h := singleton4865 B _hB
  rw [sound2106 B _hB _hF, sound2242 B _hB _hF] at h
  norm_num [nodeValue4865, nodeValue2106, nodeValue2242, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4867 node4867Labels = Sparse.eval nodeValue4867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4867) = mixedMoment B node4867 node4867Labels := rfl
  simpa [nodeValue4867, Sparse.eval] using hc.symm

theorem sound4868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4868 node4868Labels = Sparse.eval nodeValue4868 (mixedVector B) := by
  have h := singleton4868 B _hB
  rw [sound2109 B _hB _hF, sound2261 B _hB _hF] at h
  norm_num [nodeValue4868, nodeValue2109, nodeValue2261, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4872 node4872Labels = Sparse.eval nodeValue4872 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4872) = mixedMoment B node4872 node4872Labels := rfl
  simpa [nodeValue4872, Sparse.eval] using hc.symm

theorem sound4894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4894 node4894Labels = Sparse.eval nodeValue4894 (mixedVector B) := by
  simpa only [nodeValue4894, Sparse.eval_nil] using zero4894 B _hB _hF

theorem sound4896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4896 node4896Labels = Sparse.eval nodeValue4896 (mixedVector B) := by
  have h := singleton4896 B _hB
  rw [sound2266 B _hB _hF, sound2278 B _hB _hF] at h
  norm_num [nodeValue4896, nodeValue2266, nodeValue2278, Sparse.eval] at h ⊢
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

theorem sound5264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5264 node5264Labels = Sparse.eval nodeValue5264 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5264) = mixedMoment B node5264 node5264Labels := rfl
  simpa [nodeValue5264, Sparse.eval] using hc.symm

theorem sound5291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5291 node5291Labels = Sparse.eval nodeValue5291 (mixedVector B) := by
  have h := singleton5291 B _hB
  rw [sound2765 B _hB _hF, sound3582 B _hB _hF] at h
  norm_num [nodeValue5291, nodeValue2765, nodeValue3582, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5297 node5297Labels = Sparse.eval nodeValue5297 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5297) = mixedMoment B node5297 node5297Labels := rfl
  simpa [nodeValue5297, Sparse.eval] using hc.symm

theorem sound5300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5300 node5300Labels = Sparse.eval nodeValue5300 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5300) = mixedMoment B node5300 node5300Labels := rfl
  simpa [nodeValue5300, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources70
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2251 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2251 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2251 + difference 0 1) (sourceB2251 + difference 1 0) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5297) := by
    have ha : (tripleCharges (sourceA2251 + difference 0 1) (sourceB2251 + difference 1 0) sourceC2251) = raw30936 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30936; decide +kernel
    rw [ha]
    exact (canonical30936 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2251 + difference 0 2) (sourceB2251 + difference 2 0) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA2251 + difference 0 2) (sourceB2251 + difference 2 0) sourceC2251) = raw30937 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30937; decide +kernel
    rw [ha]
    exact (canonical30937 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2251 + difference 0 3) (sourceB2251 + difference 3 0) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA2251 + difference 0 3) (sourceB2251 + difference 3 0) sourceC2251) = raw30938 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30938; decide +kernel
    rw [ha]
    exact (canonical30938 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2251 + difference 0 4) (sourceB2251 + difference 4 0) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA2251 + difference 0 4) (sourceB2251 + difference 4 0) sourceC2251) = raw30939 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30939; decide +kernel
    rw [ha]
    exact (canonical30939 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2251 + difference 0 5) (sourceB2251 + difference 5 0) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA2251 + difference 0 5) (sourceB2251 + difference 5 0) sourceC2251) = raw30940 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30940; decide +kernel
    rw [ha]
    exact (canonical30940 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2251 + difference 1 0) (sourceB2251 + difference 0 1) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA2251 + difference 1 0) (sourceB2251 + difference 0 1) sourceC2251) = raw30941 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30941; decide +kernel
    rw [ha]
    exact (canonical30941 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2251 + difference 1 2) (sourceB2251 + difference 2 1) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2251 + difference 1 2) (sourceB2251 + difference 2 1) sourceC2251) = raw22928 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw22928; decide +kernel
    rw [ha]
    exact (canonical22928 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2251 + difference 1 3) (sourceB2251 + difference 3 1) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2251 + difference 1 3) (sourceB2251 + difference 3 1) sourceC2251) = raw22929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw22929; decide +kernel
    rw [ha]
    exact (canonical22929 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2251 + difference 1 4) (sourceB2251 + difference 4 1) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA2251 + difference 1 4) (sourceB2251 + difference 4 1) sourceC2251) = raw22930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw22930; decide +kernel
    rw [ha]
    exact (canonical22930 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2251 + difference 1 5) (sourceB2251 + difference 5 1) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA2251 + difference 1 5) (sourceB2251 + difference 5 1) sourceC2251) = raw22931 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw22931; decide +kernel
    rw [ha]
    exact (canonical22931 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2251 + difference 2 0) (sourceB2251 + difference 0 2) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4368) := by
    have ha : (tripleCharges (sourceA2251 + difference 2 0) (sourceB2251 + difference 0 2) sourceC2251) = raw22938 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw22938; decide +kernel
    rw [ha]
    exact (canonical22938 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2251 + difference 2 1) (sourceB2251 + difference 1 2) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4700) := by
    have ha : (tripleCharges (sourceA2251 + difference 2 1) (sourceB2251 + difference 1 2) sourceC2251) = raw30942 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30942; decide +kernel
    rw [ha]
    exact (canonical30942 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2251 + difference 2 3) (sourceB2251 + difference 3 2) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4773) := by
    have ha : (tripleCharges (sourceA2251 + difference 2 3) (sourceB2251 + difference 3 2) sourceC2251) = raw30943 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30943; decide +kernel
    rw [ha]
    exact (canonical30943 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2251 + difference 2 4) (sourceB2251 + difference 4 2) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA2251 + difference 2 4) (sourceB2251 + difference 4 2) sourceC2251) = raw30944 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30944; decide +kernel
    rw [ha]
    exact (canonical30944 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2251 + difference 2 5) (sourceB2251 + difference 5 2) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2251 + difference 2 5) (sourceB2251 + difference 5 2) sourceC2251) = raw30945 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30945; decide +kernel
    rw [ha]
    exact (canonical30945 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2251 + difference 3 0) (sourceB2251 + difference 0 3) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4368) := by
    have ha : (tripleCharges (sourceA2251 + difference 3 0) (sourceB2251 + difference 0 3) sourceC2251) = raw22943 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw22943; decide +kernel
    rw [ha]
    exact (canonical22943 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2251 + difference 3 1) (sourceB2251 + difference 1 3) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4700) := by
    have ha : (tripleCharges (sourceA2251 + difference 3 1) (sourceB2251 + difference 1 3) sourceC2251) = raw30946 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30946; decide +kernel
    rw [ha]
    exact (canonical30946 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2251 + difference 3 2) (sourceB2251 + difference 2 3) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4773) := by
    have ha : (tripleCharges (sourceA2251 + difference 3 2) (sourceB2251 + difference 2 3) sourceC2251) = raw30947 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30947; decide +kernel
    rw [ha]
    exact (canonical30947 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2251 + difference 3 4) (sourceB2251 + difference 4 3) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA2251 + difference 3 4) (sourceB2251 + difference 4 3) sourceC2251) = raw30948 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30948; decide +kernel
    rw [ha]
    exact (canonical30948 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2251 + difference 3 5) (sourceB2251 + difference 5 3) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2251 + difference 3 5) (sourceB2251 + difference 5 3) sourceC2251) = raw30949 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30949; decide +kernel
    rw [ha]
    exact (canonical30949 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2251 + difference 4 0) (sourceB2251 + difference 0 4) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4373) := by
    have ha : (tripleCharges (sourceA2251 + difference 4 0) (sourceB2251 + difference 0 4) sourceC2251) = raw22948 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw22948; decide +kernel
    rw [ha]
    exact (canonical22948 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2251 + difference 4 1) (sourceB2251 + difference 1 4) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4704) := by
    have ha : (tripleCharges (sourceA2251 + difference 4 1) (sourceB2251 + difference 1 4) sourceC2251) = raw30950 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30950; decide +kernel
    rw [ha]
    exact (canonical30950 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2251 + difference 4 2) (sourceB2251 + difference 2 4) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4776) := by
    have ha : (tripleCharges (sourceA2251 + difference 4 2) (sourceB2251 + difference 2 4) sourceC2251) = raw30951 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30951; decide +kernel
    rw [ha]
    exact (canonical30951 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2251 + difference 4 3) (sourceB2251 + difference 3 4) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4776) := by
    have ha : (tripleCharges (sourceA2251 + difference 4 3) (sourceB2251 + difference 3 4) sourceC2251) = raw30952 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30952; decide +kernel
    rw [ha]
    exact (canonical30952 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2251 + difference 4 5) (sourceB2251 + difference 5 4) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA2251 + difference 4 5) (sourceB2251 + difference 5 4) sourceC2251) = raw30953 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30953; decide +kernel
    rw [ha]
    exact (canonical30953 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2251 + difference 5 0) (sourceB2251 + difference 0 5) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4375) := by
    have ha : (tripleCharges (sourceA2251 + difference 5 0) (sourceB2251 + difference 0 5) sourceC2251) = raw22953 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw22953; decide +kernel
    rw [ha]
    exact (canonical22953 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2251 + difference 5 1) (sourceB2251 + difference 1 5) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4694) := by
    have ha : (tripleCharges (sourceA2251 + difference 5 1) (sourceB2251 + difference 1 5) sourceC2251) = raw30954 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30954; decide +kernel
    rw [ha]
    exact (canonical30954 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2251 + difference 5 2) (sourceB2251 + difference 2 5) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4687) := by
    have ha : (tripleCharges (sourceA2251 + difference 5 2) (sourceB2251 + difference 2 5) sourceC2251) = raw30955 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30955; decide +kernel
    rw [ha]
    exact (canonical30955 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2251 + difference 5 3) (sourceB2251 + difference 3 5) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4687) := by
    have ha : (tripleCharges (sourceA2251 + difference 5 3) (sourceB2251 + difference 3 5) sourceC2251) = raw30956 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30956; decide +kernel
    rw [ha]
    exact (canonical30956 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2251 + difference 5 4) (sourceB2251 + difference 4 5) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4872) := by
    have ha : (tripleCharges (sourceA2251 + difference 5 4) (sourceB2251 + difference 4 5) sourceC2251) = raw30957 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30957; decide +kernel
    rw [ha]
    exact (canonical30957 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2251 sourceB2251 sourceC2251
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2251, Integer.Sparse.eval]
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

theorem reindexCheck1839 : Integer.Sparse.reindex keyMap MixedData.row1839 = numericRow1839 := by decide +kernel

theorem numericCheck1839 (x : Master → ℝ) : Integer.Sparse.eval numericRow1839 x =
    (4 : ℝ) * reducedSource1839 x := by
  norm_num [numericRow1839, reducedSource1839, Integer.Sparse.eval, Sparse.eval, nodeValue4368, nodeValue4373, nodeValue4375, nodeValue4466, nodeValue4687, nodeValue4694, nodeValue4700, nodeValue4704, nodeValue4773, nodeValue4776, nodeValue4810, nodeValue4865, nodeValue4867, nodeValue4868, nodeValue4872, nodeValue4894, nodeValue4896, nodeValue5264, nodeValue5291, nodeValue5297, nodeValue5300]
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

theorem reducedZero1839 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1839 (mixedVector B) = 0 := by
  have h4368 : mixedVector B (Sum.inr 4368) = Sparse.eval nodeValue4368 (mixedVector B) := by
    change mixedMoment B node4368 node4368Labels = _
    exact sound4368 B hB hF
  have h4373 : mixedVector B (Sum.inr 4373) = Sparse.eval nodeValue4373 (mixedVector B) := by
    change mixedMoment B node4373 node4373Labels = _
    exact sound4373 B hB hF
  have h4375 : mixedVector B (Sum.inr 4375) = Sparse.eval nodeValue4375 (mixedVector B) := by
    change mixedMoment B node4375 node4375Labels = _
    exact sound4375 B hB hF
  have h4466 : mixedVector B (Sum.inr 4466) = Sparse.eval nodeValue4466 (mixedVector B) := by
    change mixedMoment B node4466 node4466Labels = _
    exact sound4466 B hB hF
  have h4687 : mixedVector B (Sum.inr 4687) = Sparse.eval nodeValue4687 (mixedVector B) := by
    change mixedMoment B node4687 node4687Labels = _
    exact sound4687 B hB hF
  have h4694 : mixedVector B (Sum.inr 4694) = Sparse.eval nodeValue4694 (mixedVector B) := by
    change mixedMoment B node4694 node4694Labels = _
    exact sound4694 B hB hF
  have h4700 : mixedVector B (Sum.inr 4700) = Sparse.eval nodeValue4700 (mixedVector B) := by
    change mixedMoment B node4700 node4700Labels = _
    exact sound4700 B hB hF
  have h4704 : mixedVector B (Sum.inr 4704) = Sparse.eval nodeValue4704 (mixedVector B) := by
    change mixedMoment B node4704 node4704Labels = _
    exact sound4704 B hB hF
  have h4773 : mixedVector B (Sum.inr 4773) = Sparse.eval nodeValue4773 (mixedVector B) := by
    change mixedMoment B node4773 node4773Labels = _
    exact sound4773 B hB hF
  have h4776 : mixedVector B (Sum.inr 4776) = Sparse.eval nodeValue4776 (mixedVector B) := by
    change mixedMoment B node4776 node4776Labels = _
    exact sound4776 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4865 : mixedVector B (Sum.inr 4865) = Sparse.eval nodeValue4865 (mixedVector B) := by
    change mixedMoment B node4865 node4865Labels = _
    exact sound4865 B hB hF
  have h4867 : mixedVector B (Sum.inr 4867) = Sparse.eval nodeValue4867 (mixedVector B) := by
    change mixedMoment B node4867 node4867Labels = _
    exact sound4867 B hB hF
  have h4868 : mixedVector B (Sum.inr 4868) = Sparse.eval nodeValue4868 (mixedVector B) := by
    change mixedMoment B node4868 node4868Labels = _
    exact sound4868 B hB hF
  have h4872 : mixedVector B (Sum.inr 4872) = Sparse.eval nodeValue4872 (mixedVector B) := by
    change mixedMoment B node4872 node4872Labels = _
    exact sound4872 B hB hF
  have h4894 : mixedVector B (Sum.inr 4894) = Sparse.eval nodeValue4894 (mixedVector B) := by
    change mixedMoment B node4894 node4894Labels = _
    exact sound4894 B hB hF
  have h4896 : mixedVector B (Sum.inr 4896) = Sparse.eval nodeValue4896 (mixedVector B) := by
    change mixedMoment B node4896 node4896Labels = _
    exact sound4896 B hB hF
  have h5264 : mixedVector B (Sum.inr 5264) = Sparse.eval nodeValue5264 (mixedVector B) := by
    change mixedMoment B node5264 node5264Labels = _
    exact sound5264 B hB hF
  have h5291 : mixedVector B (Sum.inr 5291) = Sparse.eval nodeValue5291 (mixedVector B) := by
    change mixedMoment B node5291 node5291Labels = _
    exact sound5291 B hB hF
  have h5297 : mixedVector B (Sum.inr 5297) = Sparse.eval nodeValue5297 (mixedVector B) := by
    change mixedMoment B node5297 node5297Labels = _
    exact sound5297 B hB hF
  have h5300 : mixedVector B (Sum.inr 5300) = Sparse.eval nodeValue5300 (mixedVector B) := by
    change mixedMoment B node5300 node5300Labels = _
    exact sound5300 B hB hF
  simpa only [sourceForm2251, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4368, h4373, h4375, h4466, h4687, h4694, h4700, h4704, h4773, h4776, h4810, h4865, h4867, h4868, h4872, h4894, h4896, h5264, h5291, h5297, h5300, reducedSource1839] using sourceEq2251 B hB

theorem rowSound1839_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1839 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1839, numericCheck1839, reducedZero1839 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839_e_oai
