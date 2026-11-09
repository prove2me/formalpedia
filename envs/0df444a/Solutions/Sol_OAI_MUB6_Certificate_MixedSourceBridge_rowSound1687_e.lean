-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:35:00.124216+00:00
-- url     : https://prove2.me/submissions/9e52a14c-37b7-4cae-b821-0a135085eff2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E103
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1587 raw1587Labels = mixedMoment B node4693 node4693Labels := by
  calc
    mixedMoment B raw1587 raw1587Labels = mixedMoment B raw1587step0 raw1587step0Labels := by
      have ha : raw1587step0 = (fun i j => raw1587 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1587step0 raw1587; decide +kernel
      have hl : raw1587step0Labels = raw1587Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1587 raw1587Labels permutation8 permutation4
    mixedMoment B raw1587step0 raw1587step0Labels = mixedMoment B raw1587step1 raw1587step1Labels := by
      have ha : raw1587step1 = raw1587step0 := by apply Matrix.ext; unfold raw1587step1 raw1587step0; decide +kernel
      have hl : raw1587step0Labels = labelEmbedding7 ∘ raw1587step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1587step0 raw1587step0Labels raw1587step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4693 node4693Labels := by rfl

theorem canonical1588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1588 raw1588Labels = mixedMoment B node1819 node1819Labels := by
  calc
    mixedMoment B raw1588 raw1588Labels = mixedMoment B raw1588step0 raw1588step0Labels := by
      have ha : raw1588step0 = (fun i j => raw1588 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1588step0 raw1588; decide +kernel
      have hl : raw1588step0Labels = raw1588Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1588 raw1588Labels permutation8 permutation4
    _ = mixedMoment B node1819 node1819Labels := by rfl

theorem canonical1589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1589 raw1589Labels = mixedMoment B node2169 node2169Labels := by
  calc
    mixedMoment B raw1589 raw1589Labels = mixedMoment B raw1589step0 raw1589step0Labels := by
      have ha : raw1589step0 = (fun i j => raw1589 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1589step0 raw1589; decide +kernel
      have hl : raw1589step0Labels = raw1589Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1589 raw1589Labels permutation9 permutation6
    mixedMoment B raw1589step0 raw1589step0Labels = mixedMoment B raw1589step1 raw1589step1Labels := by
      have ha : raw1589step1 = -raw1589step0 := by apply Matrix.ext; change ∀ i j, raw1589step1 i j = -(raw1589step0 i j); unfold raw1589step1 raw1589step0; decide +kernel
      have hl : raw1589step1Labels = raw1589step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1589step1 raw1589step1Labels = mixedMoment B raw1589step2 raw1589step2Labels := by
      have ha : raw1589step2 = raw1589step1 := by apply Matrix.ext; unfold raw1589step2 raw1589step1; decide +kernel
      have hl : raw1589step1Labels = labelEmbedding1 ∘ raw1589step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1589step1 raw1589step1Labels raw1589step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2169 node2169Labels := by rfl

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

theorem canonical1707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1707 raw1707Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw1707 raw1707Labels = mixedMoment B raw1707step0 raw1707step0Labels := by
      have ha : raw1707step0 = (fun i j => raw1707 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1707step0 raw1707; decide +kernel
      have hl : raw1707step0Labels = raw1707Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1707 raw1707Labels permutation32 permutation4
    mixedMoment B raw1707step0 raw1707step0Labels = mixedMoment B raw1707step1 raw1707step1Labels := by
      have ha : raw1707step1 = raw1707step0 := by apply Matrix.ext; unfold raw1707step1 raw1707step0; decide +kernel
      have hl : raw1707step0Labels = labelEmbedding7 ∘ raw1707step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1707step0 raw1707step0Labels raw1707step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4770 node4770Labels := by rfl

theorem canonical1708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1708 raw1708Labels = mixedMoment B node1970 node1970Labels := by
  calc
    mixedMoment B raw1708 raw1708Labels = mixedMoment B raw1708step0 raw1708step0Labels := by
      have ha : raw1708step0 = (fun i j => raw1708 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1708step0 raw1708; decide +kernel
      have hl : raw1708step0Labels = raw1708Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1708 raw1708Labels permutation32 permutation4
    _ = mixedMoment B node1970 node1970Labels := by rfl

theorem canonical1709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1709 raw1709Labels = mixedMoment B node2186 node2186Labels := by
  calc
    mixedMoment B raw1709 raw1709Labels = mixedMoment B raw1709step0 raw1709step0Labels := by
      have ha : raw1709step0 = (fun i j => raw1709 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1709step0 raw1709; decide +kernel
      have hl : raw1709step0Labels = raw1709Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1709 raw1709Labels permutation33 permutation6
    mixedMoment B raw1709step0 raw1709step0Labels = mixedMoment B raw1709step1 raw1709step1Labels := by
      have ha : raw1709step1 = -raw1709step0 := by apply Matrix.ext; change ∀ i j, raw1709step1 i j = -(raw1709step0 i j); unfold raw1709step1 raw1709step0; decide +kernel
      have hl : raw1709step1Labels = raw1709step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1709step1 raw1709step1Labels = mixedMoment B raw1709step2 raw1709step2Labels := by
      have ha : raw1709step2 = raw1709step1 := by apply Matrix.ext; unfold raw1709step2 raw1709step1; decide +kernel
      have hl : raw1709step1Labels = labelEmbedding1 ∘ raw1709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1709step1 raw1709step1Labels raw1709step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2186 node2186Labels := by rfl

theorem canonical1767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1767 raw1767Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw1767 raw1767Labels = mixedMoment B raw1767step0 raw1767step0Labels := by
      have ha : raw1767step0 = (fun i j => raw1767 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1767step0 raw1767; decide +kernel
      have hl : raw1767step0Labels = raw1767Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1767 raw1767Labels permutation32 permutation4
    mixedMoment B raw1767step0 raw1767step0Labels = mixedMoment B raw1767step1 raw1767step1Labels := by
      have ha : raw1767step1 = raw1767step0 := by apply Matrix.ext; unfold raw1767step1 raw1767step0; decide +kernel
      have hl : raw1767step0Labels = labelEmbedding7 ∘ raw1767step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1767step0 raw1767step0Labels raw1767step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical1768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1768 raw1768Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw1768 raw1768Labels = mixedMoment B raw1768step0 raw1768step0Labels := by
      have ha : raw1768step0 = (fun i j => raw1768 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1768step0 raw1768; decide +kernel
      have hl : raw1768step0Labels = raw1768Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1768 raw1768Labels permutation32 permutation4
    _ = mixedMoment B node2054 node2054Labels := by rfl

theorem canonical1769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1769 raw1769Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw1769 raw1769Labels = mixedMoment B raw1769step0 raw1769step0Labels := by
      have ha : raw1769step0 = (fun i j => raw1769 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1769step0 raw1769; decide +kernel
      have hl : raw1769step0Labels = raw1769Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1769 raw1769Labels permutation33 permutation6
    mixedMoment B raw1769step0 raw1769step0Labels = mixedMoment B raw1769step1 raw1769step1Labels := by
      have ha : raw1769step1 = -raw1769step0 := by apply Matrix.ext; change ∀ i j, raw1769step1 i j = -(raw1769step0 i j); unfold raw1769step1 raw1769step0; decide +kernel
      have hl : raw1769step1Labels = raw1769step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1769step1 raw1769step1Labels = mixedMoment B raw1769step2 raw1769step2Labels := by
      have ha : raw1769step2 = raw1769step1 := by apply Matrix.ext; unfold raw1769step2 raw1769step1; decide +kernel
      have hl : raw1769step1Labels = labelEmbedding1 ∘ raw1769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1769step1 raw1769step1Labels raw1769step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

theorem canonical1773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1773 raw1773Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw1773 raw1773Labels = mixedMoment B raw1773step0 raw1773step0Labels := by
      have ha : raw1773step0 = (fun i j => raw1773 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1773step0 raw1773; decide +kernel
      have hl : raw1773step0Labels = raw1773Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1773 raw1773Labels permutation8 permutation4
    mixedMoment B raw1773step0 raw1773step0Labels = mixedMoment B raw1773step1 raw1773step1Labels := by
      have ha : raw1773step1 = raw1773step0 := by apply Matrix.ext; unfold raw1773step1 raw1773step0; decide +kernel
      have hl : raw1773step0Labels = labelEmbedding7 ∘ raw1773step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1773step0 raw1773step0Labels raw1773step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

theorem canonical1774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1774 raw1774Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw1774 raw1774Labels = mixedMoment B raw1774step0 raw1774step0Labels := by
      have ha : raw1774step0 = (fun i j => raw1774 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1774step0 raw1774; decide +kernel
      have hl : raw1774step0Labels = raw1774Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1774 raw1774Labels permutation8 permutation4
    _ = mixedMoment B node2062 node2062Labels := by rfl

theorem canonical1775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1775 raw1775Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw1775 raw1775Labels = mixedMoment B raw1775step0 raw1775step0Labels := by
      have ha : raw1775step0 = (fun i j => raw1775 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1775step0 raw1775; decide +kernel
      have hl : raw1775step0Labels = raw1775Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1775 raw1775Labels permutation9 permutation6
    mixedMoment B raw1775step0 raw1775step0Labels = mixedMoment B raw1775step1 raw1775step1Labels := by
      have ha : raw1775step1 = -raw1775step0 := by apply Matrix.ext; change ∀ i j, raw1775step1 i j = -(raw1775step0 i j); unfold raw1775step1 raw1775step0; decide +kernel
      have hl : raw1775step1Labels = raw1775step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1775step1 raw1775step1Labels = mixedMoment B raw1775step2 raw1775step2Labels := by
      have ha : raw1775step2 = raw1775step1 := by apply Matrix.ext; unfold raw1775step2 raw1775step1; decide +kernel
      have hl : raw1775step1Labels = labelEmbedding1 ∘ raw1775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1775step1 raw1775step1Labels raw1775step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

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

theorem canonical1830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1830 raw1830Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw1830 raw1830Labels = mixedMoment B raw1830step0 raw1830step0Labels := by
      have ha : raw1830step0 = (fun i j => raw1830 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1830step0 raw1830; decide +kernel
      have hl : raw1830step0Labels = raw1830Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1830 raw1830Labels permutation2 permutation4
    mixedMoment B raw1830step0 raw1830step0Labels = mixedMoment B raw1830step1 raw1830step1Labels := by
      have ha : raw1830step1 = raw1830step0 := by apply Matrix.ext; unfold raw1830step1 raw1830step0; decide +kernel
      have hl : raw1830step0Labels = labelEmbedding7 ∘ raw1830step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1830step0 raw1830step0Labels raw1830step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

theorem canonical1831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1831 raw1831Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw1831 raw1831Labels = mixedMoment B raw1831step0 raw1831step0Labels := by
      have ha : raw1831step0 = (fun i j => raw1831 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1831step0 raw1831; decide +kernel
      have hl : raw1831step0Labels = raw1831Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1831 raw1831Labels permutation2 permutation4
    _ = mixedMoment B node2281 node2281Labels := by rfl

theorem canonical1832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1832 raw1832Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw1832 raw1832Labels = mixedMoment B raw1832step0 raw1832step0Labels := by
      have ha : raw1832step0 = (fun i j => raw1832 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1832step0 raw1832; decide +kernel
      have hl : raw1832step0Labels = raw1832Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1832 raw1832Labels permutation3 permutation6
    mixedMoment B raw1832step0 raw1832step0Labels = mixedMoment B raw1832step1 raw1832step1Labels := by
      have ha : raw1832step1 = -raw1832step0 := by apply Matrix.ext; change ∀ i j, raw1832step1 i j = -(raw1832step0 i j); unfold raw1832step1 raw1832step0; decide +kernel
      have hl : raw1832step1Labels = raw1832step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1832step1 raw1832step1Labels = mixedMoment B raw1832step2 raw1832step2Labels := by
      have ha : raw1832step2 = raw1832step1 := by apply Matrix.ext; unfold raw1832step2 raw1832step1; decide +kernel
      have hl : raw1832step1Labels = labelEmbedding1 ∘ raw1832step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1832step1 raw1832step1Labels raw1832step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2294 node2294Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical221
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28395 raw28395Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw28395 raw28395Labels = mixedMoment B raw28395step0 raw28395step0Labels := by
      have hz : ∀ j, raw28395 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28395step0 = (fun i j => raw28395 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28395step0 raw28395; decide +kernel
      have hl : raw28395step0Labels = raw28395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28395 raw28395Labels permutation434 hz
    mixedMoment B raw28395step0 raw28395step0Labels = mixedMoment B raw28395step1 raw28395step1Labels := by
      have hz : ∀ j, raw28395step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28395step1 = (fun i j => raw28395step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28395step1 raw28395step0; decide +kernel
      have hl : raw28395step1Labels = raw28395step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28395step0 raw28395step0Labels permutation80 hz
    mixedMoment B raw28395step1 raw28395step1Labels = mixedMoment B raw28395step2 raw28395step2Labels := by
      have ha : raw28395step2 = (fun i j => raw28395step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28395step2 raw28395step1; decide +kernel
      have hl : raw28395step2Labels = raw28395step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28395step1 raw28395step1Labels permutation30 permutation2
    mixedMoment B raw28395step2 raw28395step2Labels = mixedMoment B raw28395step3 raw28395step3Labels := by
      have ha : raw28395step3 = -raw28395step2 := by apply Matrix.ext; change ∀ i j, raw28395step3 i j = -(raw28395step2 i j); unfold raw28395step3 raw28395step2; decide +kernel
      have hl : raw28395step3Labels = raw28395step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4846 node4846Labels := by rfl

theorem canonical28396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28396 raw28396Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw28396 raw28396Labels = mixedMoment B raw28396step0 raw28396step0Labels := by
      have hz : ∀ j, raw28396 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28396step0 = (fun i j => raw28396 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28396step0 raw28396; decide +kernel
      have hl : raw28396step0Labels = raw28396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28396 raw28396Labels permutation434 hz
    mixedMoment B raw28396step0 raw28396step0Labels = mixedMoment B raw28396step1 raw28396step1Labels := by
      have ha : raw28396step1 = (fun i j => raw28396step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28396step1 raw28396step0; decide +kernel
      have hl : raw28396step1Labels = raw28396step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28396step0 raw28396step0Labels permutation151 permutation2
    mixedMoment B raw28396step1 raw28396step1Labels = mixedMoment B raw28396step2 raw28396step2Labels := by
      have ha : raw28396step2 = -raw28396step1 := by apply Matrix.ext; change ∀ i j, raw28396step2 i j = -(raw28396step1 i j); unfold raw28396step2 raw28396step1; decide +kernel
      have hl : raw28396step2Labels = raw28396step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical28397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28397 raw28397Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw28397 raw28397Labels = mixedMoment B raw28397step0 raw28397step0Labels := by
      have hz : ∀ j, raw28397 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28397step0 = (fun i j => raw28397 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28397step0 raw28397; decide +kernel
      have hl : raw28397step0Labels = raw28397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28397 raw28397Labels permutation346 hz
    mixedMoment B raw28397step0 raw28397step0Labels = mixedMoment B raw28397step1 raw28397step1Labels := by
      have ha : raw28397step1 = (fun i j => raw28397step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28397step1 raw28397step0; decide +kernel
      have hl : raw28397step1Labels = raw28397step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28397step0 raw28397step0Labels permutation151 permutation2
    mixedMoment B raw28397step1 raw28397step1Labels = mixedMoment B raw28397step2 raw28397step2Labels := by
      have ha : raw28397step2 = -raw28397step1 := by apply Matrix.ext; change ∀ i j, raw28397step2 i j = -(raw28397step1 i j); unfold raw28397step2 raw28397step1; decide +kernel
      have hl : raw28397step2Labels = raw28397step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical28398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28398 raw28398Labels = mixedMoment B node4901 node4901Labels := by
  calc
    mixedMoment B raw28398 raw28398Labels = mixedMoment B raw28398step0 raw28398step0Labels := by
      have hz : ∀ j, raw28398 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28398step0 = (fun i j => raw28398 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28398step0 raw28398; decide +kernel
      have hl : raw28398step0Labels = raw28398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28398 raw28398Labels permutation520 hz
    mixedMoment B raw28398step0 raw28398step0Labels = mixedMoment B raw28398step1 raw28398step1Labels := by
      have hz : ∀ j, raw28398step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28398step1 = (fun i j => raw28398step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28398step1 raw28398step0; decide +kernel
      have hl : raw28398step1Labels = raw28398step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28398step0 raw28398step0Labels permutation104 hz
    mixedMoment B raw28398step1 raw28398step1Labels = mixedMoment B raw28398step2 raw28398step2Labels := by
      have hz : ∀ j, raw28398step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw28398step2 = (fun i j => raw28398step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw28398step2 raw28398step1; decide +kernel
      have hl : raw28398step2Labels = raw28398step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28398step1 raw28398step1Labels permutation20 hz
    mixedMoment B raw28398step2 raw28398step2Labels = mixedMoment B raw28398step3 raw28398step3Labels := by
      have ha : raw28398step3 = (fun i j => raw28398step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28398step3 raw28398step2; decide +kernel
      have hl : raw28398step3Labels = raw28398step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28398step2 raw28398step2Labels permutation7 permutation2
    mixedMoment B raw28398step3 raw28398step3Labels = mixedMoment B raw28398step4 raw28398step4Labels := by
      have ha : raw28398step4 = -raw28398step3 := by apply Matrix.ext; change ∀ i j, raw28398step4 i j = -(raw28398step3 i j); unfold raw28398step4 raw28398step3; decide +kernel
      have hl : raw28398step4Labels = raw28398step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4901 node4901Labels := by rfl

theorem canonical28399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28399 raw28399Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw28399 raw28399Labels = mixedMoment B raw28399step0 raw28399step0Labels := by
      have hz : ∀ j, raw28399 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28399step0 = (fun i j => raw28399 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28399step0 raw28399; decide +kernel
      have hl : raw28399step0Labels = raw28399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28399 raw28399Labels permutation434 hz
    mixedMoment B raw28399step0 raw28399step0Labels = mixedMoment B raw28399step1 raw28399step1Labels := by
      have hz : ∀ j, raw28399step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28399step1 = (fun i j => raw28399step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28399step1 raw28399step0; decide +kernel
      have hl : raw28399step1Labels = raw28399step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28399step0 raw28399step0Labels permutation80 hz
    mixedMoment B raw28399step1 raw28399step1Labels = mixedMoment B raw28399step2 raw28399step2Labels := by
      have ha : raw28399step2 = (fun i j => raw28399step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28399step2 raw28399step1; decide +kernel
      have hl : raw28399step2Labels = raw28399step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28399step1 raw28399step1Labels permutation30 permutation7
    mixedMoment B raw28399step2 raw28399step2Labels = mixedMoment B raw28399step3 raw28399step3Labels := by
      have ha : raw28399step3 = raw28399step2 := by apply Matrix.ext; unfold raw28399step3 raw28399step2; decide +kernel
      have hl : raw28399step2Labels = labelEmbedding10 ∘ raw28399step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28399step2 raw28399step2Labels raw28399step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

theorem canonical28400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28400 raw28400Labels = mixedMoment B node4478 node4478Labels := by
  calc
    mixedMoment B raw28400 raw28400Labels = mixedMoment B raw28400step0 raw28400step0Labels := by
      have hz : ∀ j, raw28400 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28400step0 = (fun i j => raw28400 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28400step0 raw28400; decide +kernel
      have hl : raw28400step0Labels = raw28400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28400 raw28400Labels permutation434 hz
    mixedMoment B raw28400step0 raw28400step0Labels = mixedMoment B raw28400step1 raw28400step1Labels := by
      have hz : ∀ j, raw28400step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28400step1 = (fun i j => raw28400step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28400step1 raw28400step0; decide +kernel
      have hl : raw28400step1Labels = raw28400step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28400step0 raw28400step0Labels permutation80 hz
    mixedMoment B raw28400step1 raw28400step1Labels = mixedMoment B raw28400step2 raw28400step2Labels := by
      have ha : raw28400step2 = (fun i j => raw28400step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28400step2 raw28400step1; decide +kernel
      have hl : raw28400step2Labels = raw28400step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28400step1 raw28400step1Labels permutation8 permutation3
    mixedMoment B raw28400step2 raw28400step2Labels = mixedMoment B raw28400step3 raw28400step3Labels := by
      have ha : raw28400step3 = raw28400step2 := by apply Matrix.ext; unfold raw28400step3 raw28400step2; decide +kernel
      have hl : raw28400step2Labels = labelEmbedding6 ∘ raw28400step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28400step2 raw28400step2Labels raw28400step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4478 node4478Labels := by rfl

theorem canonical28401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28401 raw28401Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw28401 raw28401Labels = mixedMoment B raw28401step0 raw28401step0Labels := by
      have hz : ∀ j, raw28401 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28401step0 = (fun i j => raw28401 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28401step0 raw28401; decide +kernel
      have hl : raw28401step0Labels = raw28401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28401 raw28401Labels permutation434 hz
    mixedMoment B raw28401step0 raw28401step0Labels = mixedMoment B raw28401step1 raw28401step1Labels := by
      have ha : raw28401step1 = (fun i j => raw28401step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28401step1 raw28401step0; decide +kernel
      have hl : raw28401step1Labels = raw28401step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28401step0 raw28401step0Labels permutation149 permutation2
    mixedMoment B raw28401step1 raw28401step1Labels = mixedMoment B raw28401step2 raw28401step2Labels := by
      have ha : raw28401step2 = -raw28401step1 := by apply Matrix.ext; change ∀ i j, raw28401step2 i j = -(raw28401step1 i j); unfold raw28401step2 raw28401step1; decide +kernel
      have hl : raw28401step2Labels = raw28401step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4817 node4817Labels := by rfl

theorem canonical28402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28402 raw28402Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw28402 raw28402Labels = mixedMoment B raw28402step0 raw28402step0Labels := by
      have hz : ∀ j, raw28402 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28402step0 = (fun i j => raw28402 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28402step0 raw28402; decide +kernel
      have hl : raw28402step0Labels = raw28402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28402 raw28402Labels permutation346 hz
    mixedMoment B raw28402step0 raw28402step0Labels = mixedMoment B raw28402step1 raw28402step1Labels := by
      have ha : raw28402step1 = (fun i j => raw28402step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28402step1 raw28402step0; decide +kernel
      have hl : raw28402step1Labels = raw28402step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28402step0 raw28402step0Labels permutation149 permutation2
    mixedMoment B raw28402step1 raw28402step1Labels = mixedMoment B raw28402step2 raw28402step2Labels := by
      have ha : raw28402step2 = -raw28402step1 := by apply Matrix.ext; change ∀ i j, raw28402step2 i j = -(raw28402step1 i j); unfold raw28402step2 raw28402step1; decide +kernel
      have hl : raw28402step2Labels = raw28402step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4817 node4817Labels := by rfl

theorem canonical28403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28403 raw28403Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw28403 raw28403Labels = mixedMoment B raw28403step0 raw28403step0Labels := by
      have hz : ∀ j, raw28403 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28403step0 = (fun i j => raw28403 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28403step0 raw28403; decide +kernel
      have hl : raw28403step0Labels = raw28403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28403 raw28403Labels permutation520 hz
    mixedMoment B raw28403step0 raw28403step0Labels = mixedMoment B raw28403step1 raw28403step1Labels := by
      have hz : ∀ j, raw28403step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28403step1 = (fun i j => raw28403step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28403step1 raw28403step0; decide +kernel
      have hl : raw28403step1Labels = raw28403step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28403step0 raw28403step0Labels permutation104 hz
    mixedMoment B raw28403step1 raw28403step1Labels = mixedMoment B raw28403step2 raw28403step2Labels := by
      have hz : ∀ j, raw28403step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw28403step2 = (fun i j => raw28403step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw28403step2 raw28403step1; decide +kernel
      have hl : raw28403step2Labels = raw28403step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28403step1 raw28403step1Labels permutation20 hz
    mixedMoment B raw28403step2 raw28403step2Labels = mixedMoment B raw28403step3 raw28403step3Labels := by
      have ha : raw28403step3 = (fun i j => raw28403step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28403step3 raw28403step2; decide +kernel
      have hl : raw28403step3Labels = raw28403step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28403step2 raw28403step2Labels permutation7 permutation2
    mixedMoment B raw28403step3 raw28403step3Labels = mixedMoment B raw28403step4 raw28403step4Labels := by
      have ha : raw28403step4 = -raw28403step3 := by apply Matrix.ext; change ∀ i j, raw28403step4 i j = -(raw28403step3 i j); unfold raw28403step4 raw28403step3; decide +kernel
      have hl : raw28403step4Labels = raw28403step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4899 node4899Labels := by rfl

theorem canonical28404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28404 raw28404Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw28404 raw28404Labels = mixedMoment B raw28404step0 raw28404step0Labels := by
      have hz : ∀ j, raw28404 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28404step0 = (fun i j => raw28404 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28404step0 raw28404; decide +kernel
      have hl : raw28404step0Labels = raw28404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28404 raw28404Labels permutation434 hz
    mixedMoment B raw28404step0 raw28404step0Labels = mixedMoment B raw28404step1 raw28404step1Labels := by
      have hz : ∀ j, raw28404step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28404step1 = (fun i j => raw28404step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28404step1 raw28404step0; decide +kernel
      have hl : raw28404step1Labels = raw28404step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28404step0 raw28404step0Labels permutation80 hz
    mixedMoment B raw28404step1 raw28404step1Labels = mixedMoment B raw28404step2 raw28404step2Labels := by
      have ha : raw28404step2 = (fun i j => raw28404step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28404step2 raw28404step1; decide +kernel
      have hl : raw28404step2Labels = raw28404step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28404step1 raw28404step1Labels permutation30 permutation7
    mixedMoment B raw28404step2 raw28404step2Labels = mixedMoment B raw28404step3 raw28404step3Labels := by
      have ha : raw28404step3 = raw28404step2 := by apply Matrix.ext; unfold raw28404step3 raw28404step2; decide +kernel
      have hl : raw28404step2Labels = labelEmbedding10 ∘ raw28404step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28404step2 raw28404step2Labels raw28404step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

theorem canonical28405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28405 raw28405Labels = mixedMoment B node4371 node4371Labels := by
  calc
    mixedMoment B raw28405 raw28405Labels = mixedMoment B raw28405step0 raw28405step0Labels := by
      have hz : ∀ j, raw28405 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28405step0 = (fun i j => raw28405 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28405step0 raw28405; decide +kernel
      have hl : raw28405step0Labels = raw28405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28405 raw28405Labels permutation434 hz
    mixedMoment B raw28405step0 raw28405step0Labels = mixedMoment B raw28405step1 raw28405step1Labels := by
      have ha : raw28405step1 = (fun i j => raw28405step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28405step1 raw28405step0; decide +kernel
      have hl : raw28405step1Labels = raw28405step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28405step0 raw28405step0Labels permutation32 permutation3
    mixedMoment B raw28405step1 raw28405step1Labels = mixedMoment B raw28405step2 raw28405step2Labels := by
      have ha : raw28405step2 = raw28405step1 := by apply Matrix.ext; unfold raw28405step2 raw28405step1; decide +kernel
      have hl : raw28405step1Labels = labelEmbedding6 ∘ raw28405step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28405step1 raw28405step1Labels raw28405step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4371 node4371Labels := by rfl

theorem canonical28406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28406 raw28406Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw28406 raw28406Labels = mixedMoment B raw28406step0 raw28406step0Labels := by
      have hz : ∀ j, raw28406 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28406step0 = (fun i j => raw28406 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28406step0 raw28406; decide +kernel
      have hl : raw28406step0Labels = raw28406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28406 raw28406Labels permutation434 hz
    mixedMoment B raw28406step0 raw28406step0Labels = mixedMoment B raw28406step1 raw28406step1Labels := by
      have ha : raw28406step1 = (fun i j => raw28406step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28406step1 raw28406step0; decide +kernel
      have hl : raw28406step1Labels = raw28406step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28406step0 raw28406step0Labels permutation145 permutation2
    mixedMoment B raw28406step1 raw28406step1Labels = mixedMoment B raw28406step2 raw28406step2Labels := by
      have ha : raw28406step2 = -raw28406step1 := by apply Matrix.ext; change ∀ i j, raw28406step2 i j = -(raw28406step1 i j); unfold raw28406step2 raw28406step1; decide +kernel
      have hl : raw28406step2Labels = raw28406step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4770 node4770Labels := by rfl

theorem canonical28407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28407 raw28407Labels = mixedMoment B node4761 node4761Labels := by
  calc
    mixedMoment B raw28407 raw28407Labels = mixedMoment B raw28407step0 raw28407step0Labels := by
      have ha : raw28407step0 = (fun i j => raw28407 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28407step0 raw28407; decide +kernel
      have hl : raw28407step0Labels = raw28407Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28407 raw28407Labels permutation646 permutation2
    mixedMoment B raw28407step0 raw28407step0Labels = mixedMoment B raw28407step1 raw28407step1Labels := by
      have ha : raw28407step1 = -raw28407step0 := by apply Matrix.ext; change ∀ i j, raw28407step1 i j = -(raw28407step0 i j); unfold raw28407step1 raw28407step0; decide +kernel
      have hl : raw28407step1Labels = raw28407step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4761 node4761Labels := by rfl

theorem canonical28408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28408 raw28408Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw28408 raw28408Labels = mixedMoment B raw28408step0 raw28408step0Labels := by
      have hz : ∀ j, raw28408 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28408step0 = (fun i j => raw28408 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28408step0 raw28408; decide +kernel
      have hl : raw28408step0Labels = raw28408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28408 raw28408Labels permutation520 hz
    mixedMoment B raw28408step0 raw28408step0Labels = mixedMoment B raw28408step1 raw28408step1Labels := by
      have hz : ∀ j, raw28408step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28408step1 = (fun i j => raw28408step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28408step1 raw28408step0; decide +kernel
      have hl : raw28408step1Labels = raw28408step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28408step0 raw28408step0Labels permutation104 hz
    mixedMoment B raw28408step1 raw28408step1Labels = mixedMoment B raw28408step2 raw28408step2Labels := by
      have ha : raw28408step2 = (fun i j => raw28408step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28408step2 raw28408step1; decide +kernel
      have hl : raw28408step2Labels = raw28408step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28408step1 raw28408step1Labels permutation31 permutation2
    mixedMoment B raw28408step2 raw28408step2Labels = mixedMoment B raw28408step3 raw28408step3Labels := by
      have ha : raw28408step3 = -raw28408step2 := by apply Matrix.ext; change ∀ i j, raw28408step3 i j = -(raw28408step2 i j); unfold raw28408step3 raw28408step2; decide +kernel
      have hl : raw28408step3Labels = raw28408step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4843 node4843Labels := by rfl

theorem canonical28409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28409 raw28409Labels = mixedMoment B node5205 node5205Labels := by
  calc
    mixedMoment B raw28409 raw28409Labels = mixedMoment B raw28409step0 raw28409step0Labels := by
      have hz : ∀ j, raw28409 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28409step0 = (fun i j => raw28409 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28409step0 raw28409; decide +kernel
      have hl : raw28409step0Labels = raw28409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28409 raw28409Labels permutation434 hz
    mixedMoment B raw28409step0 raw28409step0Labels = mixedMoment B raw28409step1 raw28409step1Labels := by
      have ha : raw28409step1 = (fun i j => raw28409step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28409step1 raw28409step0; decide +kernel
      have hl : raw28409step1Labels = raw28409step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28409step0 raw28409step0Labels permutation32 permutation3
    mixedMoment B raw28409step1 raw28409step1Labels = mixedMoment B raw28409step2 raw28409step2Labels := by
      have ha : raw28409step2 = raw28409step1 := by apply Matrix.ext; unfold raw28409step2 raw28409step1; decide +kernel
      have hl : raw28409step1Labels = labelEmbedding6 ∘ raw28409step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28409step1 raw28409step1Labels raw28409step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5205 node5205Labels := by rfl

theorem canonical28410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28410 raw28410Labels = mixedMoment B node4371 node4371Labels := by
  calc
    mixedMoment B raw28410 raw28410Labels = mixedMoment B raw28410step0 raw28410step0Labels := by
      have hz : ∀ j, raw28410 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28410step0 = (fun i j => raw28410 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28410step0 raw28410; decide +kernel
      have hl : raw28410step0Labels = raw28410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28410 raw28410Labels permutation346 hz
    mixedMoment B raw28410step0 raw28410step0Labels = mixedMoment B raw28410step1 raw28410step1Labels := by
      have ha : raw28410step1 = (fun i j => raw28410step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28410step1 raw28410step0; decide +kernel
      have hl : raw28410step1Labels = raw28410step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28410step0 raw28410step0Labels permutation32 permutation3
    mixedMoment B raw28410step1 raw28410step1Labels = mixedMoment B raw28410step2 raw28410step2Labels := by
      have ha : raw28410step2 = raw28410step1 := by apply Matrix.ext; unfold raw28410step2 raw28410step1; decide +kernel
      have hl : raw28410step1Labels = labelEmbedding6 ∘ raw28410step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28410step1 raw28410step1Labels raw28410step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4371 node4371Labels := by rfl

theorem canonical28411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28411 raw28411Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw28411 raw28411Labels = mixedMoment B raw28411step0 raw28411step0Labels := by
      have hz : ∀ j, raw28411 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28411step0 = (fun i j => raw28411 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28411step0 raw28411; decide +kernel
      have hl : raw28411step0Labels = raw28411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28411 raw28411Labels permutation346 hz
    mixedMoment B raw28411step0 raw28411step0Labels = mixedMoment B raw28411step1 raw28411step1Labels := by
      have ha : raw28411step1 = (fun i j => raw28411step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28411step1 raw28411step0; decide +kernel
      have hl : raw28411step1Labels = raw28411step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28411step0 raw28411step0Labels permutation145 permutation2
    mixedMoment B raw28411step1 raw28411step1Labels = mixedMoment B raw28411step2 raw28411step2Labels := by
      have ha : raw28411step2 = -raw28411step1 := by apply Matrix.ext; change ∀ i j, raw28411step2 i j = -(raw28411step1 i j); unfold raw28411step2 raw28411step1; decide +kernel
      have hl : raw28411step2Labels = raw28411step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4770 node4770Labels := by rfl

theorem canonical28412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28412 raw28412Labels = mixedMoment B node4761 node4761Labels := by
  calc
    mixedMoment B raw28412 raw28412Labels = mixedMoment B raw28412step0 raw28412step0Labels := by
      have ha : raw28412step0 = (fun i j => raw28412 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28412step0 raw28412; decide +kernel
      have hl : raw28412step0Labels = raw28412Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28412 raw28412Labels permutation664 permutation2
    mixedMoment B raw28412step0 raw28412step0Labels = mixedMoment B raw28412step1 raw28412step1Labels := by
      have ha : raw28412step1 = -raw28412step0 := by apply Matrix.ext; change ∀ i j, raw28412step1 i j = -(raw28412step0 i j); unfold raw28412step1 raw28412step0; decide +kernel
      have hl : raw28412step1Labels = raw28412step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4761 node4761Labels := by rfl

theorem canonical28413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28413 raw28413Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw28413 raw28413Labels = mixedMoment B raw28413step0 raw28413step0Labels := by
      have hz : ∀ j, raw28413 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28413step0 = (fun i j => raw28413 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28413step0 raw28413; decide +kernel
      have hl : raw28413step0Labels = raw28413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28413 raw28413Labels permutation520 hz
    mixedMoment B raw28413step0 raw28413step0Labels = mixedMoment B raw28413step1 raw28413step1Labels := by
      have hz : ∀ j, raw28413step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28413step1 = (fun i j => raw28413step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28413step1 raw28413step0; decide +kernel
      have hl : raw28413step1Labels = raw28413step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28413step0 raw28413step0Labels permutation80 hz
    mixedMoment B raw28413step1 raw28413step1Labels = mixedMoment B raw28413step2 raw28413step2Labels := by
      have ha : raw28413step2 = (fun i j => raw28413step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28413step2 raw28413step1; decide +kernel
      have hl : raw28413step2Labels = raw28413step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28413step1 raw28413step1Labels permutation31 permutation2
    mixedMoment B raw28413step2 raw28413step2Labels = mixedMoment B raw28413step3 raw28413step3Labels := by
      have ha : raw28413step3 = -raw28413step2 := by apply Matrix.ext; change ∀ i j, raw28413step3 i j = -(raw28413step2 i j); unfold raw28413step3 raw28413step2; decide +kernel
      have hl : raw28413step3Labels = raw28413step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4843 node4843Labels := by rfl

theorem canonical28414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28414 raw28414Labels = mixedMoment B node5205 node5205Labels := by
  calc
    mixedMoment B raw28414 raw28414Labels = mixedMoment B raw28414step0 raw28414step0Labels := by
      have hz : ∀ j, raw28414 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28414step0 = (fun i j => raw28414 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28414step0 raw28414; decide +kernel
      have hl : raw28414step0Labels = raw28414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28414 raw28414Labels permutation346 hz
    mixedMoment B raw28414step0 raw28414step0Labels = mixedMoment B raw28414step1 raw28414step1Labels := by
      have ha : raw28414step1 = (fun i j => raw28414step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28414step1 raw28414step0; decide +kernel
      have hl : raw28414step1Labels = raw28414step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28414step0 raw28414step0Labels permutation32 permutation3
    mixedMoment B raw28414step1 raw28414step1Labels = mixedMoment B raw28414step2 raw28414step2Labels := by
      have ha : raw28414step2 = raw28414step1 := by apply Matrix.ext; unfold raw28414step2 raw28414step1; decide +kernel
      have hl : raw28414step1Labels = labelEmbedding6 ∘ raw28414step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28414step1 raw28414step1Labels raw28414step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5205 node5205Labels := by rfl

theorem canonical28415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28415 raw28415Labels = mixedMoment B node4375 node4375Labels := by
  calc
    mixedMoment B raw28415 raw28415Labels = mixedMoment B raw28415step0 raw28415step0Labels := by
      have hz : ∀ j, raw28415 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28415step0 = (fun i j => raw28415 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28415step0 raw28415; decide +kernel
      have hl : raw28415step0Labels = raw28415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28415 raw28415Labels permutation434 hz
    mixedMoment B raw28415step0 raw28415step0Labels = mixedMoment B raw28415step1 raw28415step1Labels := by
      have hz : ∀ j, raw28415step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28415step1 = (fun i j => raw28415step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28415step1 raw28415step0; decide +kernel
      have hl : raw28415step1Labels = raw28415step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28415step0 raw28415step0Labels permutation80 hz
    mixedMoment B raw28415step1 raw28415step1Labels = mixedMoment B raw28415step2 raw28415step2Labels := by
      have ha : raw28415step2 = (fun i j => raw28415step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28415step2 raw28415step1; decide +kernel
      have hl : raw28415step2Labels = raw28415step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28415step1 raw28415step1Labels permutation8 permutation3
    mixedMoment B raw28415step2 raw28415step2Labels = mixedMoment B raw28415step3 raw28415step3Labels := by
      have ha : raw28415step3 = raw28415step2 := by apply Matrix.ext; unfold raw28415step3 raw28415step2; decide +kernel
      have hl : raw28415step2Labels = labelEmbedding6 ∘ raw28415step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28415step2 raw28415step2Labels raw28415step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4375 node4375Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical222
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28416 raw28416Labels = mixedMoment B node4693 node4693Labels := by
  calc
    mixedMoment B raw28416 raw28416Labels = mixedMoment B raw28416step0 raw28416step0Labels := by
      have hz : ∀ j, raw28416 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28416step0 = (fun i j => raw28416 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28416step0 raw28416; decide +kernel
      have hl : raw28416step0Labels = raw28416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28416 raw28416Labels permutation434 hz
    mixedMoment B raw28416step0 raw28416step0Labels = mixedMoment B raw28416step1 raw28416step1Labels := by
      have hz : ∀ j, raw28416step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28416step1 = (fun i j => raw28416step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28416step1 raw28416step0; decide +kernel
      have hl : raw28416step1Labels = raw28416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28416step0 raw28416step0Labels permutation80 hz
    mixedMoment B raw28416step1 raw28416step1Labels = mixedMoment B raw28416step2 raw28416step2Labels := by
      have ha : raw28416step2 = (fun i j => raw28416step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28416step2 raw28416step1; decide +kernel
      have hl : raw28416step2Labels = raw28416step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28416step1 raw28416step1Labels permutation31 permutation2
    mixedMoment B raw28416step2 raw28416step2Labels = mixedMoment B raw28416step3 raw28416step3Labels := by
      have ha : raw28416step3 = -raw28416step2 := by apply Matrix.ext; change ∀ i j, raw28416step3 i j = -(raw28416step2 i j); unfold raw28416step3 raw28416step2; decide +kernel
      have hl : raw28416step3Labels = raw28416step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4693 node4693Labels := by rfl

theorem canonical28417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28417 raw28417Labels = mixedMoment B node4682 node4682Labels := by
  calc
    mixedMoment B raw28417 raw28417Labels = mixedMoment B raw28417step0 raw28417step0Labels := by
      have hz : ∀ j, raw28417 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28417step0 = (fun i j => raw28417 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28417step0 raw28417; decide +kernel
      have hl : raw28417step0Labels = raw28417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28417 raw28417Labels permutation434 hz
    mixedMoment B raw28417step0 raw28417step0Labels = mixedMoment B raw28417step1 raw28417step1Labels := by
      have ha : raw28417step1 = (fun i j => raw28417step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28417step1 raw28417step0; decide +kernel
      have hl : raw28417step1Labels = raw28417step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28417step0 raw28417step0Labels permutation151 permutation2
    mixedMoment B raw28417step1 raw28417step1Labels = mixedMoment B raw28417step2 raw28417step2Labels := by
      have ha : raw28417step2 = -raw28417step1 := by apply Matrix.ext; change ∀ i j, raw28417step2 i j = -(raw28417step1 i j); unfold raw28417step2 raw28417step1; decide +kernel
      have hl : raw28417step2Labels = raw28417step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4682 node4682Labels := by rfl

theorem canonical28418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28418 raw28418Labels = mixedMoment B node4682 node4682Labels := by
  calc
    mixedMoment B raw28418 raw28418Labels = mixedMoment B raw28418step0 raw28418step0Labels := by
      have hz : ∀ j, raw28418 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28418step0 = (fun i j => raw28418 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28418step0 raw28418; decide +kernel
      have hl : raw28418step0Labels = raw28418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28418 raw28418Labels permutation346 hz
    mixedMoment B raw28418step0 raw28418step0Labels = mixedMoment B raw28418step1 raw28418step1Labels := by
      have ha : raw28418step1 = (fun i j => raw28418step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28418step1 raw28418step0; decide +kernel
      have hl : raw28418step1Labels = raw28418step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28418step0 raw28418step0Labels permutation151 permutation2
    mixedMoment B raw28418step1 raw28418step1Labels = mixedMoment B raw28418step2 raw28418step2Labels := by
      have ha : raw28418step2 = -raw28418step1 := by apply Matrix.ext; change ∀ i j, raw28418step2 i j = -(raw28418step1 i j); unfold raw28418step2 raw28418step1; decide +kernel
      have hl : raw28418step2Labels = raw28418step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4682 node4682Labels := by rfl

theorem canonical28419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28419 raw28419Labels = mixedMoment B node5206 node5206Labels := by
  calc
    mixedMoment B raw28419 raw28419Labels = mixedMoment B raw28419step0 raw28419step0Labels := by
      have hz : ∀ j, raw28419 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28419step0 = (fun i j => raw28419 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28419step0 raw28419; decide +kernel
      have hl : raw28419step0Labels = raw28419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28419 raw28419Labels permutation434 hz
    mixedMoment B raw28419step0 raw28419step0Labels = mixedMoment B raw28419step1 raw28419step1Labels := by
      have hz : ∀ j, raw28419step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28419step1 = (fun i j => raw28419step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28419step1 raw28419step0; decide +kernel
      have hl : raw28419step1Labels = raw28419step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28419step0 raw28419step0Labels permutation80 hz
    mixedMoment B raw28419step1 raw28419step1Labels = mixedMoment B raw28419step2 raw28419step2Labels := by
      have ha : raw28419step2 = (fun i j => raw28419step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28419step2 raw28419step1; decide +kernel
      have hl : raw28419step2Labels = raw28419step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28419step1 raw28419step1Labels permutation9 permutation3
    mixedMoment B raw28419step2 raw28419step2Labels = mixedMoment B raw28419step3 raw28419step3Labels := by
      have ha : raw28419step3 = raw28419step2 := by apply Matrix.ext; unfold raw28419step3 raw28419step2; decide +kernel
      have hl : raw28419step2Labels = labelEmbedding6 ∘ raw28419step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28419step2 raw28419step2Labels raw28419step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5206 node5206Labels := by rfl

theorem canonical28420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28420 raw28420Labels = mixedMoment B node4358 node4358Labels := by
  calc
    mixedMoment B raw28420 raw28420Labels = mixedMoment B raw28420step0 raw28420step0Labels := by
      have hz : ∀ j, raw28420 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28420step0 = (fun i j => raw28420 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28420step0 raw28420; decide +kernel
      have hl : raw28420step0Labels = raw28420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28420 raw28420Labels permutation434 hz
    mixedMoment B raw28420step0 raw28420step0Labels = mixedMoment B raw28420step1 raw28420step1Labels := by
      have hz : ∀ j, raw28420step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28420step1 = (fun i j => raw28420step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28420step1 raw28420step0; decide +kernel
      have hl : raw28420step1Labels = raw28420step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28420step0 raw28420step0Labels permutation80 hz
    mixedMoment B raw28420step1 raw28420step1Labels = mixedMoment B raw28420step2 raw28420step2Labels := by
      have ha : raw28420step2 = (fun i j => raw28420step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28420step2 raw28420step1; decide +kernel
      have hl : raw28420step2Labels = raw28420step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28420step1 raw28420step1Labels permutation31 permutation2
    mixedMoment B raw28420step2 raw28420step2Labels = mixedMoment B raw28420step3 raw28420step3Labels := by
      have ha : raw28420step3 = -raw28420step2 := by apply Matrix.ext; change ∀ i j, raw28420step3 i j = -(raw28420step2 i j); unfold raw28420step3 raw28420step2; decide +kernel
      have hl : raw28420step3Labels = raw28420step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4358 node4358Labels := by rfl

theorem canonical28421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28421 raw28421Labels = mixedMoment B node4361 node4361Labels := by
  calc
    mixedMoment B raw28421 raw28421Labels = mixedMoment B raw28421step0 raw28421step0Labels := by
      have hz : ∀ j, raw28421 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28421step0 = (fun i j => raw28421 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28421step0 raw28421; decide +kernel
      have hl : raw28421step0Labels = raw28421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28421 raw28421Labels permutation434 hz
    mixedMoment B raw28421step0 raw28421step0Labels = mixedMoment B raw28421step1 raw28421step1Labels := by
      have hz : ∀ j, raw28421step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28421step1 = (fun i j => raw28421step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28421step1 raw28421step0; decide +kernel
      have hl : raw28421step1Labels = raw28421step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28421step0 raw28421step0Labels permutation80 hz
    mixedMoment B raw28421step1 raw28421step1Labels = mixedMoment B raw28421step2 raw28421step2Labels := by
      have ha : raw28421step2 = (fun i j => raw28421step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28421step2 raw28421step1; decide +kernel
      have hl : raw28421step2Labels = raw28421step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28421step1 raw28421step1Labels permutation31 permutation2
    mixedMoment B raw28421step2 raw28421step2Labels = mixedMoment B raw28421step3 raw28421step3Labels := by
      have ha : raw28421step3 = -raw28421step2 := by apply Matrix.ext; change ∀ i j, raw28421step3 i j = -(raw28421step2 i j); unfold raw28421step3 raw28421step2; decide +kernel
      have hl : raw28421step3Labels = raw28421step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4361 node4361Labels := by rfl

theorem canonical28422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28422 raw28422Labels = mixedMoment B node4347 node4347Labels := by
  calc
    mixedMoment B raw28422 raw28422Labels = mixedMoment B raw28422step0 raw28422step0Labels := by
      have hz : ∀ j, raw28422 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28422step0 = (fun i j => raw28422 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28422step0 raw28422; decide +kernel
      have hl : raw28422step0Labels = raw28422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28422 raw28422Labels permutation434 hz
    mixedMoment B raw28422step0 raw28422step0Labels = mixedMoment B raw28422step1 raw28422step1Labels := by
      have ha : raw28422step1 = (fun i j => raw28422step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28422step1 raw28422step0; decide +kernel
      have hl : raw28422step1Labels = raw28422step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28422step0 raw28422step0Labels permutation151 permutation2
    mixedMoment B raw28422step1 raw28422step1Labels = mixedMoment B raw28422step2 raw28422step2Labels := by
      have ha : raw28422step2 = -raw28422step1 := by apply Matrix.ext; change ∀ i j, raw28422step2 i j = -(raw28422step1 i j); unfold raw28422step2 raw28422step1; decide +kernel
      have hl : raw28422step2Labels = raw28422step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4347 node4347Labels := by rfl

theorem canonical28423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28423 raw28423Labels = mixedMoment B node4347 node4347Labels := by
  calc
    mixedMoment B raw28423 raw28423Labels = mixedMoment B raw28423step0 raw28423step0Labels := by
      have hz : ∀ j, raw28423 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28423step0 = (fun i j => raw28423 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28423step0 raw28423; decide +kernel
      have hl : raw28423step0Labels = raw28423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28423 raw28423Labels permutation346 hz
    mixedMoment B raw28423step0 raw28423step0Labels = mixedMoment B raw28423step1 raw28423step1Labels := by
      have ha : raw28423step1 = (fun i j => raw28423step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28423step1 raw28423step0; decide +kernel
      have hl : raw28423step1Labels = raw28423step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28423step0 raw28423step0Labels permutation151 permutation2
    mixedMoment B raw28423step1 raw28423step1Labels = mixedMoment B raw28423step2 raw28423step2Labels := by
      have ha : raw28423step2 = -raw28423step1 := by apply Matrix.ext; change ∀ i j, raw28423step2 i j = -(raw28423step1 i j); unfold raw28423step2 raw28423step1; decide +kernel
      have hl : raw28423step2Labels = raw28423step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4347 node4347Labels := by rfl

theorem canonical28424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28424 raw28424Labels = mixedMoment B node4507 node4507Labels := by
  calc
    mixedMoment B raw28424 raw28424Labels = mixedMoment B raw28424step0 raw28424step0Labels := by
      have hz : ∀ j, raw28424 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28424step0 = (fun i j => raw28424 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28424step0 raw28424; decide +kernel
      have hl : raw28424step0Labels = raw28424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28424 raw28424Labels permutation520 hz
    mixedMoment B raw28424step0 raw28424step0Labels = mixedMoment B raw28424step1 raw28424step1Labels := by
      have hz : ∀ j, raw28424step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28424step1 = (fun i j => raw28424step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28424step1 raw28424step0; decide +kernel
      have hl : raw28424step1Labels = raw28424step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28424step0 raw28424step0Labels permutation104 hz
    mixedMoment B raw28424step1 raw28424step1Labels = mixedMoment B raw28424step2 raw28424step2Labels := by
      have hz : ∀ j, raw28424step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw28424step2 = (fun i j => raw28424step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw28424step2 raw28424step1; decide +kernel
      have hl : raw28424step2Labels = raw28424step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28424step1 raw28424step1Labels permutation20 hz
    mixedMoment B raw28424step2 raw28424step2Labels = mixedMoment B raw28424step3 raw28424step3Labels := by
      have ha : raw28424step3 = (fun i j => raw28424step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28424step3 raw28424step2; decide +kernel
      have hl : raw28424step3Labels = raw28424step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28424step2 raw28424step2Labels permutation7 permutation2
    mixedMoment B raw28424step3 raw28424step3Labels = mixedMoment B raw28424step4 raw28424step4Labels := by
      have ha : raw28424step4 = -raw28424step3 := by apply Matrix.ext; change ∀ i j, raw28424step4 i j = -(raw28424step3 i j); unfold raw28424step4 raw28424step3; decide +kernel
      have hl : raw28424step4Labels = raw28424step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4507 node4507Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4693 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4693 node4693Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1819 node1819Labels + mixedMoment B node2169 node2169Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1587 singletonSmall4693
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4693) = raw1587Labels := by decide +kernel
  rw [hl, canonical1587 B hB] at h
  have hc0 : mixedMoment B raw1587 (Fin.cases (0 : Fin 2) singletonSmall4693) =
      mixedMoment B node1819 node1819Labels := by
    have ha : raw1587 = raw1588 := by apply Matrix.ext; unfold raw1587 raw1588; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4693 = raw1588Labels := by decide +kernel
    rw [ha, hj, canonical1588 B hB]
  have hc1 : mixedMoment B raw1587 (Fin.cases (1 : Fin 2) singletonSmall4693) =
      mixedMoment B node2169 node2169Labels := by
    have ha : raw1587 = raw1589 := by apply Matrix.ext; unfold raw1587 raw1589; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4693 = raw1589Labels := by decide +kernel
    rw [ha, hj, canonical1589 B hB]
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

theorem singleton4770 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4770 node4770Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1970 node1970Labels + mixedMoment B node2186 node2186Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1707 singletonSmall4770
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4770) = raw1707Labels := by decide +kernel
  rw [hl, canonical1707 B hB] at h
  have hc0 : mixedMoment B raw1707 (Fin.cases (0 : Fin 2) singletonSmall4770) =
      mixedMoment B node1970 node1970Labels := by
    have ha : raw1707 = raw1708 := by apply Matrix.ext; unfold raw1707 raw1708; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4770 = raw1708Labels := by decide +kernel
    rw [ha, hj, canonical1708 B hB]
  have hc1 : mixedMoment B raw1707 (Fin.cases (1 : Fin 2) singletonSmall4770) =
      mixedMoment B node2186 node2186Labels := by
    have ha : raw1707 = raw1709 := by apply Matrix.ext; unfold raw1707 raw1709; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4770 = raw1709Labels := by decide +kernel
    rw [ha, hj, canonical1709 B hB]
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

theorem singleton4835 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4835 node4835Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2054 node2054Labels + mixedMoment B node2206 node2206Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1767 singletonSmall4835
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4835) = raw1767Labels := by decide +kernel
  rw [hl, canonical1767 B hB] at h
  have hc0 : mixedMoment B raw1767 (Fin.cases (0 : Fin 2) singletonSmall4835) =
      mixedMoment B node2054 node2054Labels := by
    have ha : raw1767 = raw1768 := by apply Matrix.ext; unfold raw1767 raw1768; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4835 = raw1768Labels := by decide +kernel
    rw [ha, hj, canonical1768 B hB]
  have hc1 : mixedMoment B raw1767 (Fin.cases (1 : Fin 2) singletonSmall4835) =
      mixedMoment B node2206 node2206Labels := by
    have ha : raw1767 = raw1769 := by apply Matrix.ext; unfold raw1767 raw1769; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4835 = raw1769Labels := by decide +kernel
    rw [ha, hj, canonical1769 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4843 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4843 node4843Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2062 node2062Labels + mixedMoment B node2230 node2230Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1773 singletonSmall4843
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4843) = raw1773Labels := by decide +kernel
  rw [hl, canonical1773 B hB] at h
  have hc0 : mixedMoment B raw1773 (Fin.cases (0 : Fin 2) singletonSmall4843) =
      mixedMoment B node2062 node2062Labels := by
    have ha : raw1773 = raw1774 := by apply Matrix.ext; unfold raw1773 raw1774; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4843 = raw1774Labels := by decide +kernel
    rw [ha, hj, canonical1774 B hB]
  have hc1 : mixedMoment B raw1773 (Fin.cases (1 : Fin 2) singletonSmall4843) =
      mixedMoment B node2230 node2230Labels := by
    have ha : raw1773 = raw1775 := by apply Matrix.ext; unfold raw1773 raw1775; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4843 = raw1775Labels := by decide +kernel
    rw [ha, hj, canonical1775 B hB]
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

theorem singleton4899 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4899 node4899Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2281 node2281Labels + mixedMoment B node2294 node2294Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1830 singletonSmall4899
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4899) = raw1830Labels := by decide +kernel
  rw [hl, canonical1830 B hB] at h
  have hc0 : mixedMoment B raw1830 (Fin.cases (0 : Fin 2) singletonSmall4899) =
      mixedMoment B node2281 node2281Labels := by
    have ha : raw1830 = raw1831 := by apply Matrix.ext; unfold raw1830 raw1831; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4899 = raw1831Labels := by decide +kernel
    rw [ha, hj, canonical1831 B hB]
  have hc1 : mixedMoment B raw1830 (Fin.cases (1 : Fin 2) singletonSmall4899) =
      mixedMoment B node2294 node2294Labels := by
    have ha : raw1830 = raw1832 := by apply Matrix.ext; unfold raw1830 raw1832; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4899 = raw1832Labels := by decide +kernel
    rw [ha, hj, canonical1832 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SoundPriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2281 node2281Labels = Sparse.eval nodeValue2281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2281) = mixedMoment B node2281 node2281Labels := rfl
  simpa [nodeValue2281, Sparse.eval] using hc.symm

theorem sound2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2294 node2294Labels = Sparse.eval nodeValue2294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2294) = mixedMoment B node2294 node2294Labels := rfl
  simpa [nodeValue2294, Sparse.eval] using hc.symm

theorem sound4899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4899 node4899Labels = Sparse.eval nodeValue4899 (mixedVector B) := by
  have h := singleton4899 B _hB
  rw [sound2281 B _hB _hF, sound2294 B _hB _hF] at h
  norm_num [nodeValue4899, nodeValue2281, nodeValue2294, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node939 node939Labels = Sparse.eval nodeValue939 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 939) = mixedMoment B node939 node939Labels := rfl
  simpa [nodeValue939, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem sound1756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1756 node1756Labels = Sparse.eval nodeValue1756 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1756) = mixedMoment B node1756 node1756Labels := rfl
  simpa [nodeValue1756, Sparse.eval] using hc.symm

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

theorem sound1819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1819 node1819Labels = Sparse.eval nodeValue1819 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1819) = mixedMoment B node1819 node1819Labels := rfl
  simpa [nodeValue1819, Sparse.eval] using hc.symm

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

theorem sound1970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1970 node1970Labels = Sparse.eval nodeValue1970 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1970) = mixedMoment B node1970 node1970Labels := rfl
  simpa [nodeValue1970, Sparse.eval] using hc.symm

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

theorem sound2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2054 node2054Labels = Sparse.eval nodeValue2054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2054) = mixedMoment B node2054 node2054Labels := rfl
  simpa [nodeValue2054, Sparse.eval] using hc.symm

theorem sound2062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2062 node2062Labels = Sparse.eval nodeValue2062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2062) = mixedMoment B node2062 node2062Labels := rfl
  simpa [nodeValue2062, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2169 node2169Labels = Sparse.eval nodeValue2169 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2169) = mixedMoment B node2169 node2169Labels := rfl
  simpa [nodeValue2169, Sparse.eval] using hc.symm

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

theorem sound2186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2186 node2186Labels = Sparse.eval nodeValue2186 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2186) = mixedMoment B node2186 node2186Labels := rfl
  simpa [nodeValue2186, Sparse.eval] using hc.symm

theorem sound2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2206 node2206Labels = Sparse.eval nodeValue2206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2206) = mixedMoment B node2206 node2206Labels := rfl
  simpa [nodeValue2206, Sparse.eval] using hc.symm

theorem sound2230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2230 node2230Labels = Sparse.eval nodeValue2230 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2230) = mixedMoment B node2230 node2230Labels := rfl
  simpa [nodeValue2230, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

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

theorem sound4347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4347 node4347Labels = Sparse.eval nodeValue4347 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4347) = mixedMoment B node4347 node4347Labels := rfl
  simpa [nodeValue4347, Sparse.eval] using hc.symm

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

theorem sound4358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4358 node4358Labels = Sparse.eval nodeValue4358 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4358) = mixedMoment B node4358 node4358Labels := rfl
  simpa [nodeValue4358, Sparse.eval] using hc.symm

theorem sound4361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4361 node4361Labels = Sparse.eval nodeValue4361 (mixedVector B) := by
  have h := singleton4361 B _hB
  rw [sound939 B _hB _hF, sound1694 B _hB _hF] at h
  norm_num [nodeValue4361, nodeValue939, nodeValue1694, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4371 node4371Labels = Sparse.eval nodeValue4371 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4371) = mixedMoment B node4371 node4371Labels := rfl
  simpa [nodeValue4371, Sparse.eval] using hc.symm

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

theorem sound4478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4478 node4478Labels = Sparse.eval nodeValue4478 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4478) = mixedMoment B node4478 node4478Labels := rfl
  simpa [nodeValue4478, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4682 node4682Labels = Sparse.eval nodeValue4682 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4682) = mixedMoment B node4682 node4682Labels := rfl
  simpa [nodeValue4682, Sparse.eval] using hc.symm

theorem sound4693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4693 node4693Labels = Sparse.eval nodeValue4693 (mixedVector B) := by
  have h := singleton4693 B _hB
  rw [sound1819 B _hB _hF, sound2169 B _hB _hF] at h
  norm_num [nodeValue4693, nodeValue1819, nodeValue2169, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4761 node4761Labels = Sparse.eval nodeValue4761 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4761) = mixedMoment B node4761 node4761Labels := rfl
  simpa [nodeValue4761, Sparse.eval] using hc.symm

theorem sound4770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4770 node4770Labels = Sparse.eval nodeValue4770 (mixedVector B) := by
  have h := singleton4770 B _hB
  rw [sound1970 B _hB _hF, sound2186 B _hB _hF] at h
  norm_num [nodeValue4770, nodeValue1970, nodeValue2186, Sparse.eval] at h ⊢
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

theorem sound4817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4817 node4817Labels = Sparse.eval nodeValue4817 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4817) = mixedMoment B node4817 node4817Labels := rfl
  simpa [nodeValue4817, Sparse.eval] using hc.symm

theorem sound4835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4835 node4835Labels = Sparse.eval nodeValue4835 (mixedVector B) := by
  have h := singleton4835 B _hB
  rw [sound2054 B _hB _hF, sound2206 B _hB _hF] at h
  norm_num [nodeValue4835, nodeValue2054, nodeValue2206, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4843 node4843Labels = Sparse.eval nodeValue4843 (mixedVector B) := by
  have h := singleton4843 B _hB
  rw [sound2062 B _hB _hF, sound2230 B _hB _hF] at h
  norm_num [nodeValue4843, nodeValue2062, nodeValue2230, Sparse.eval] at h ⊢
  linarith only [h]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5205 node5205Labels = Sparse.eval nodeValue5205 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5205) = mixedMoment B node5205 node5205Labels := rfl
  simpa [nodeValue5205, Sparse.eval] using hc.symm

theorem sound5206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5206 node5206Labels = Sparse.eval nodeValue5206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5206) = mixedMoment B node5206 node5206Labels := rfl
  simpa [nodeValue5206, Sparse.eval] using hc.symm

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

theorem sound5275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5275 node5275Labels = Sparse.eval nodeValue5275 (mixedVector B) := by
  have h := singleton5275 B _hB
  rw [sound2743 B _hB _hF, sound3548 B _hB _hF] at h
  norm_num [nodeValue5275, nodeValue2743, nodeValue3548, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5276 node5276Labels = Sparse.eval nodeValue5276 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5276) = mixedMoment B node5276 node5276Labels := rfl
  simpa [nodeValue5276, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources62
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2000 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2000 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2000 + difference 0 1) (sourceB2000 + difference 1 0) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2000 + difference 0 1) (sourceB2000 + difference 1 0) sourceC2000) = raw28395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28395; decide +kernel
    rw [ha]
    exact (canonical28395 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2000 + difference 0 2) (sourceB2000 + difference 2 0) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2000 + difference 0 2) (sourceB2000 + difference 2 0) sourceC2000) = raw28396 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28396; decide +kernel
    rw [ha]
    exact (canonical28396 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2000 + difference 0 3) (sourceB2000 + difference 3 0) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2000 + difference 0 3) (sourceB2000 + difference 3 0) sourceC2000) = raw28397 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28397; decide +kernel
    rw [ha]
    exact (canonical28397 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2000 + difference 0 4) (sourceB2000 + difference 4 0) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4901) := by
    have ha : (tripleCharges (sourceA2000 + difference 0 4) (sourceB2000 + difference 4 0) sourceC2000) = raw28398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28398; decide +kernel
    rw [ha]
    exact (canonical28398 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2000 + difference 0 5) (sourceB2000 + difference 5 0) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA2000 + difference 0 5) (sourceB2000 + difference 5 0) sourceC2000) = raw28399 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28399; decide +kernel
    rw [ha]
    exact (canonical28399 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2000 + difference 1 0) (sourceB2000 + difference 0 1) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4478) := by
    have ha : (tripleCharges (sourceA2000 + difference 1 0) (sourceB2000 + difference 0 1) sourceC2000) = raw28400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28400; decide +kernel
    rw [ha]
    exact (canonical28400 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2000 + difference 1 2) (sourceB2000 + difference 2 1) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA2000 + difference 1 2) (sourceB2000 + difference 2 1) sourceC2000) = raw28401 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28401; decide +kernel
    rw [ha]
    exact (canonical28401 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2000 + difference 1 3) (sourceB2000 + difference 3 1) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA2000 + difference 1 3) (sourceB2000 + difference 3 1) sourceC2000) = raw28402 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28402; decide +kernel
    rw [ha]
    exact (canonical28402 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2000 + difference 1 4) (sourceB2000 + difference 4 1) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA2000 + difference 1 4) (sourceB2000 + difference 4 1) sourceC2000) = raw28403 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28403; decide +kernel
    rw [ha]
    exact (canonical28403 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2000 + difference 1 5) (sourceB2000 + difference 5 1) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA2000 + difference 1 5) (sourceB2000 + difference 5 1) sourceC2000) = raw28404 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28404; decide +kernel
    rw [ha]
    exact (canonical28404 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2000 + difference 2 0) (sourceB2000 + difference 0 2) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4371) := by
    have ha : (tripleCharges (sourceA2000 + difference 2 0) (sourceB2000 + difference 0 2) sourceC2000) = raw28405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28405; decide +kernel
    rw [ha]
    exact (canonical28405 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2000 + difference 2 1) (sourceB2000 + difference 1 2) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4770) := by
    have ha : (tripleCharges (sourceA2000 + difference 2 1) (sourceB2000 + difference 1 2) sourceC2000) = raw28406 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28406; decide +kernel
    rw [ha]
    exact (canonical28406 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2000 + difference 2 3) (sourceB2000 + difference 3 2) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4761) := by
    have ha : (tripleCharges (sourceA2000 + difference 2 3) (sourceB2000 + difference 3 2) sourceC2000) = raw28407 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28407; decide +kernel
    rw [ha]
    exact (canonical28407 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2000 + difference 2 4) (sourceB2000 + difference 4 2) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA2000 + difference 2 4) (sourceB2000 + difference 4 2) sourceC2000) = raw28408 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28408; decide +kernel
    rw [ha]
    exact (canonical28408 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2000 + difference 2 5) (sourceB2000 + difference 5 2) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5205) := by
    have ha : (tripleCharges (sourceA2000 + difference 2 5) (sourceB2000 + difference 5 2) sourceC2000) = raw28409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28409; decide +kernel
    rw [ha]
    exact (canonical28409 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2000 + difference 3 0) (sourceB2000 + difference 0 3) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4371) := by
    have ha : (tripleCharges (sourceA2000 + difference 3 0) (sourceB2000 + difference 0 3) sourceC2000) = raw28410 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28410; decide +kernel
    rw [ha]
    exact (canonical28410 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2000 + difference 3 1) (sourceB2000 + difference 1 3) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4770) := by
    have ha : (tripleCharges (sourceA2000 + difference 3 1) (sourceB2000 + difference 1 3) sourceC2000) = raw28411 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28411; decide +kernel
    rw [ha]
    exact (canonical28411 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2000 + difference 3 2) (sourceB2000 + difference 2 3) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4761) := by
    have ha : (tripleCharges (sourceA2000 + difference 3 2) (sourceB2000 + difference 2 3) sourceC2000) = raw28412 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28412; decide +kernel
    rw [ha]
    exact (canonical28412 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2000 + difference 3 4) (sourceB2000 + difference 4 3) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA2000 + difference 3 4) (sourceB2000 + difference 4 3) sourceC2000) = raw28413 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28413; decide +kernel
    rw [ha]
    exact (canonical28413 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2000 + difference 3 5) (sourceB2000 + difference 5 3) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5205) := by
    have ha : (tripleCharges (sourceA2000 + difference 3 5) (sourceB2000 + difference 5 3) sourceC2000) = raw28414 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28414; decide +kernel
    rw [ha]
    exact (canonical28414 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2000 + difference 4 0) (sourceB2000 + difference 0 4) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4375) := by
    have ha : (tripleCharges (sourceA2000 + difference 4 0) (sourceB2000 + difference 0 4) sourceC2000) = raw28415 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28415; decide +kernel
    rw [ha]
    exact (canonical28415 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2000 + difference 4 1) (sourceB2000 + difference 1 4) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4693) := by
    have ha : (tripleCharges (sourceA2000 + difference 4 1) (sourceB2000 + difference 1 4) sourceC2000) = raw28416 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28416; decide +kernel
    rw [ha]
    exact (canonical28416 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2000 + difference 4 2) (sourceB2000 + difference 2 4) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4682) := by
    have ha : (tripleCharges (sourceA2000 + difference 4 2) (sourceB2000 + difference 2 4) sourceC2000) = raw28417 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28417; decide +kernel
    rw [ha]
    exact (canonical28417 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2000 + difference 4 3) (sourceB2000 + difference 3 4) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4682) := by
    have ha : (tripleCharges (sourceA2000 + difference 4 3) (sourceB2000 + difference 3 4) sourceC2000) = raw28418 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28418; decide +kernel
    rw [ha]
    exact (canonical28418 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2000 + difference 4 5) (sourceB2000 + difference 5 4) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5206) := by
    have ha : (tripleCharges (sourceA2000 + difference 4 5) (sourceB2000 + difference 5 4) sourceC2000) = raw28419 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28419; decide +kernel
    rw [ha]
    exact (canonical28419 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2000 + difference 5 0) (sourceB2000 + difference 0 5) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4358) := by
    have ha : (tripleCharges (sourceA2000 + difference 5 0) (sourceB2000 + difference 0 5) sourceC2000) = raw28420 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28420; decide +kernel
    rw [ha]
    exact (canonical28420 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2000 + difference 5 1) (sourceB2000 + difference 1 5) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4361) := by
    have ha : (tripleCharges (sourceA2000 + difference 5 1) (sourceB2000 + difference 1 5) sourceC2000) = raw28421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28421; decide +kernel
    rw [ha]
    exact (canonical28421 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2000 + difference 5 2) (sourceB2000 + difference 2 5) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4347) := by
    have ha : (tripleCharges (sourceA2000 + difference 5 2) (sourceB2000 + difference 2 5) sourceC2000) = raw28422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28422; decide +kernel
    rw [ha]
    exact (canonical28422 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2000 + difference 5 3) (sourceB2000 + difference 3 5) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4347) := by
    have ha : (tripleCharges (sourceA2000 + difference 5 3) (sourceB2000 + difference 3 5) sourceC2000) = raw28423 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28423; decide +kernel
    rw [ha]
    exact (canonical28423 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2000 + difference 5 4) (sourceB2000 + difference 4 5) sourceC2000) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4507) := by
    have ha : (tripleCharges (sourceA2000 + difference 5 4) (sourceB2000 + difference 4 5) sourceC2000) = raw28424 := by
      apply Matrix.ext; unfold tripleCharges sourceA2000 sourceB2000 sourceC2000 difference raw28424; decide +kernel
    rw [ha]
    exact (canonical28424 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2000 sourceB2000 sourceC2000
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2000, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1687 : Integer.Sparse.reindex keyMap MixedData.row1687 = numericRow1687 := by decide +kernel

theorem numericCheck1687 (x : Master → ℝ) : Integer.Sparse.eval numericRow1687 x =
    (4 : ℝ) * reducedSource1687 x := by
  norm_num [numericRow1687, reducedSource1687, Integer.Sparse.eval, Sparse.eval, nodeValue4347, nodeValue4358, nodeValue4361, nodeValue4371, nodeValue4375, nodeValue4478, nodeValue4507, nodeValue4682, nodeValue4693, nodeValue4761, nodeValue4770, nodeValue4817, nodeValue4835, nodeValue4843, nodeValue4846, nodeValue4899, nodeValue4901, nodeValue5205, nodeValue5206, nodeValue5275, nodeValue5276] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1687 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1687 (mixedVector B) = 0 := by
  have h4347 : mixedVector B (Sum.inr 4347) = Sparse.eval nodeValue4347 (mixedVector B) := by
    change mixedMoment B node4347 node4347Labels = _
    exact sound4347 B hB hF
  have h4358 : mixedVector B (Sum.inr 4358) = Sparse.eval nodeValue4358 (mixedVector B) := by
    change mixedMoment B node4358 node4358Labels = _
    exact sound4358 B hB hF
  have h4361 : mixedVector B (Sum.inr 4361) = Sparse.eval nodeValue4361 (mixedVector B) := by
    change mixedMoment B node4361 node4361Labels = _
    exact sound4361 B hB hF
  have h4371 : mixedVector B (Sum.inr 4371) = Sparse.eval nodeValue4371 (mixedVector B) := by
    change mixedMoment B node4371 node4371Labels = _
    exact sound4371 B hB hF
  have h4375 : mixedVector B (Sum.inr 4375) = Sparse.eval nodeValue4375 (mixedVector B) := by
    change mixedMoment B node4375 node4375Labels = _
    exact sound4375 B hB hF
  have h4478 : mixedVector B (Sum.inr 4478) = Sparse.eval nodeValue4478 (mixedVector B) := by
    change mixedMoment B node4478 node4478Labels = _
    exact sound4478 B hB hF
  have h4507 : mixedVector B (Sum.inr 4507) = Sparse.eval nodeValue4507 (mixedVector B) := by
    change mixedMoment B node4507 node4507Labels = _
    exact sound4507 B hB hF
  have h4682 : mixedVector B (Sum.inr 4682) = Sparse.eval nodeValue4682 (mixedVector B) := by
    change mixedMoment B node4682 node4682Labels = _
    exact sound4682 B hB hF
  have h4693 : mixedVector B (Sum.inr 4693) = Sparse.eval nodeValue4693 (mixedVector B) := by
    change mixedMoment B node4693 node4693Labels = _
    exact sound4693 B hB hF
  have h4761 : mixedVector B (Sum.inr 4761) = Sparse.eval nodeValue4761 (mixedVector B) := by
    change mixedMoment B node4761 node4761Labels = _
    exact sound4761 B hB hF
  have h4770 : mixedVector B (Sum.inr 4770) = Sparse.eval nodeValue4770 (mixedVector B) := by
    change mixedMoment B node4770 node4770Labels = _
    exact sound4770 B hB hF
  have h4817 : mixedVector B (Sum.inr 4817) = Sparse.eval nodeValue4817 (mixedVector B) := by
    change mixedMoment B node4817 node4817Labels = _
    exact sound4817 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4843 : mixedVector B (Sum.inr 4843) = Sparse.eval nodeValue4843 (mixedVector B) := by
    change mixedMoment B node4843 node4843Labels = _
    exact sound4843 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h4899 : mixedVector B (Sum.inr 4899) = Sparse.eval nodeValue4899 (mixedVector B) := by
    change mixedMoment B node4899 node4899Labels = _
    exact sound4899 B hB hF
  have h4901 : mixedVector B (Sum.inr 4901) = Sparse.eval nodeValue4901 (mixedVector B) := by
    change mixedMoment B node4901 node4901Labels = _
    exact sound4901 B hB hF
  have h5205 : mixedVector B (Sum.inr 5205) = Sparse.eval nodeValue5205 (mixedVector B) := by
    change mixedMoment B node5205 node5205Labels = _
    exact sound5205 B hB hF
  have h5206 : mixedVector B (Sum.inr 5206) = Sparse.eval nodeValue5206 (mixedVector B) := by
    change mixedMoment B node5206 node5206Labels = _
    exact sound5206 B hB hF
  have h5275 : mixedVector B (Sum.inr 5275) = Sparse.eval nodeValue5275 (mixedVector B) := by
    change mixedMoment B node5275 node5275Labels = _
    exact sound5275 B hB hF
  have h5276 : mixedVector B (Sum.inr 5276) = Sparse.eval nodeValue5276 (mixedVector B) := by
    change mixedMoment B node5276 node5276Labels = _
    exact sound5276 B hB hF
  simpa only [sourceForm2000, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4347, h4358, h4361, h4371, h4375, h4478, h4507, h4682, h4693, h4761, h4770, h4817, h4835, h4843, h4846, h4899, h4901, h5205, h5206, h5275, h5276, reducedSource1687] using sourceEq2000 B hB

theorem rowSound1687_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1687 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1687, numericCheck1687, reducedZero1687 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687_e_oai
