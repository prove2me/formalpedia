-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:33:18.258223+00:00
-- url     : https://prove2.me/submissions/8fb4dd4b-be2b-431c-88dd-1f97084f3166

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E190
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1572 raw1572Labels = mixedMoment B node4686 node4686Labels := by
  calc
    mixedMoment B raw1572 raw1572Labels = mixedMoment B raw1572step0 raw1572step0Labels := by
      have ha : raw1572step0 = (fun i j => raw1572 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1572step0 raw1572; decide +kernel
      have hl : raw1572step0Labels = raw1572Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1572 raw1572Labels permutation32 permutation4
    mixedMoment B raw1572step0 raw1572step0Labels = mixedMoment B raw1572step1 raw1572step1Labels := by
      have ha : raw1572step1 = raw1572step0 := by apply Matrix.ext; unfold raw1572step1 raw1572step0; decide +kernel
      have hl : raw1572step0Labels = labelEmbedding7 ∘ raw1572step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1572step0 raw1572step0Labels raw1572step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4686 node4686Labels := by rfl

theorem canonical1573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1573 raw1573Labels = mixedMoment B node1812 node1812Labels := by
  calc
    mixedMoment B raw1573 raw1573Labels = mixedMoment B raw1573step0 raw1573step0Labels := by
      have ha : raw1573step0 = (fun i j => raw1573 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1573step0 raw1573; decide +kernel
      have hl : raw1573step0Labels = raw1573Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1573 raw1573Labels permutation32 permutation4
    _ = mixedMoment B node1812 node1812Labels := by rfl

theorem canonical1574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1574 raw1574Labels = mixedMoment B node2165 node2165Labels := by
  calc
    mixedMoment B raw1574 raw1574Labels = mixedMoment B raw1574step0 raw1574step0Labels := by
      have ha : raw1574step0 = (fun i j => raw1574 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1574step0 raw1574; decide +kernel
      have hl : raw1574step0Labels = raw1574Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1574 raw1574Labels permutation32 permutation6
    mixedMoment B raw1574step0 raw1574step0Labels = mixedMoment B raw1574step1 raw1574step1Labels := by
      have ha : raw1574step1 = -raw1574step0 := by apply Matrix.ext; change ∀ i j, raw1574step1 i j = -(raw1574step0 i j); unfold raw1574step1 raw1574step0; decide +kernel
      have hl : raw1574step1Labels = raw1574step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1574step1 raw1574step1Labels = mixedMoment B raw1574step2 raw1574step2Labels := by
      have ha : raw1574step2 = raw1574step1 := by apply Matrix.ext; unfold raw1574step2 raw1574step1; decide +kernel
      have hl : raw1574step1Labels = labelEmbedding1 ∘ raw1574step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1574step1 raw1574step1Labels raw1574step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2165 node2165Labels := by rfl

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

theorem canonical1695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1695 raw1695Labels = mixedMoment B node4764 node4764Labels := by
  calc
    mixedMoment B raw1695 raw1695Labels = mixedMoment B raw1695step0 raw1695step0Labels := by
      have ha : raw1695step0 = (fun i j => raw1695 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1695step0 raw1695; decide +kernel
      have hl : raw1695step0Labels = raw1695Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1695 raw1695Labels permutation152 permutation4
    mixedMoment B raw1695step0 raw1695step0Labels = mixedMoment B raw1695step1 raw1695step1Labels := by
      have ha : raw1695step1 = raw1695step0 := by apply Matrix.ext; unfold raw1695step1 raw1695step0; decide +kernel
      have hl : raw1695step0Labels = labelEmbedding7 ∘ raw1695step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1695step0 raw1695step0Labels raw1695step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4764 node4764Labels := by rfl

theorem canonical1696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1696 raw1696Labels = mixedMoment B node1964 node1964Labels := by
  calc
    mixedMoment B raw1696 raw1696Labels = mixedMoment B raw1696step0 raw1696step0Labels := by
      have ha : raw1696step0 = (fun i j => raw1696 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1696step0 raw1696; decide +kernel
      have hl : raw1696step0Labels = raw1696Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1696 raw1696Labels permutation152 permutation4
    _ = mixedMoment B node1964 node1964Labels := by rfl

theorem canonical1697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1697 raw1697Labels = mixedMoment B node2182 node2182Labels := by
  calc
    mixedMoment B raw1697 raw1697Labels = mixedMoment B raw1697step0 raw1697step0Labels := by
      have ha : raw1697step0 = (fun i j => raw1697 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1697step0 raw1697; decide +kernel
      have hl : raw1697step0Labels = raw1697Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1697 raw1697Labels permutation152 permutation6
    mixedMoment B raw1697step0 raw1697step0Labels = mixedMoment B raw1697step1 raw1697step1Labels := by
      have ha : raw1697step1 = -raw1697step0 := by apply Matrix.ext; change ∀ i j, raw1697step1 i j = -(raw1697step0 i j); unfold raw1697step1 raw1697step0; decide +kernel
      have hl : raw1697step1Labels = raw1697step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1697step1 raw1697step1Labels = mixedMoment B raw1697step2 raw1697step2Labels := by
      have ha : raw1697step2 = raw1697step1 := by apply Matrix.ext; unfold raw1697step2 raw1697step1; decide +kernel
      have hl : raw1697step1Labels = labelEmbedding1 ∘ raw1697step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1697step1 raw1697step1Labels raw1697step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2182 node2182Labels := by rfl

theorem canonical1734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1734 raw1734Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw1734 raw1734Labels = mixedMoment B raw1734step0 raw1734step0Labels := by
      have ha : raw1734step0 = (fun i j => raw1734 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1734step0 raw1734; decide +kernel
      have hl : raw1734step0Labels = raw1734Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1734 raw1734Labels permutation152 permutation4
    mixedMoment B raw1734step0 raw1734step0Labels = mixedMoment B raw1734step1 raw1734step1Labels := by
      have ha : raw1734step1 = raw1734step0 := by apply Matrix.ext; unfold raw1734step1 raw1734step0; decide +kernel
      have hl : raw1734step0Labels = labelEmbedding7 ∘ raw1734step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1734step0 raw1734step0Labels raw1734step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical1735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1735 raw1735Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw1735 raw1735Labels = mixedMoment B raw1735step0 raw1735step0Labels := by
      have ha : raw1735step0 = (fun i j => raw1735 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1735step0 raw1735; decide +kernel
      have hl : raw1735step0Labels = raw1735Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1735 raw1735Labels permutation152 permutation4
    _ = mixedMoment B node2020 node2020Labels := by rfl

theorem canonical1736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1736 raw1736Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw1736 raw1736Labels = mixedMoment B raw1736step0 raw1736step0Labels := by
      have ha : raw1736step0 = (fun i j => raw1736 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1736step0 raw1736; decide +kernel
      have hl : raw1736step0Labels = raw1736Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1736 raw1736Labels permutation158 permutation6
    mixedMoment B raw1736step0 raw1736step0Labels = mixedMoment B raw1736step1 raw1736step1Labels := by
      have ha : raw1736step1 = -raw1736step0 := by apply Matrix.ext; change ∀ i j, raw1736step1 i j = -(raw1736step0 i j); unfold raw1736step1 raw1736step0; decide +kernel
      have hl : raw1736step1Labels = raw1736step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1736step1 raw1736step1Labels = mixedMoment B raw1736step2 raw1736step2Labels := by
      have ha : raw1736step2 = raw1736step1 := by apply Matrix.ext; unfold raw1736step2 raw1736step1; decide +kernel
      have hl : raw1736step1Labels = labelEmbedding1 ∘ raw1736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1736step1 raw1736step1Labels raw1736step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

theorem canonical1743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1743 raw1743Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw1743 raw1743Labels = mixedMoment B raw1743step0 raw1743step0Labels := by
      have ha : raw1743step0 = (fun i j => raw1743 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1743step0 raw1743; decide +kernel
      have hl : raw1743step0Labels = raw1743Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1743 raw1743Labels permutation32 permutation4
    mixedMoment B raw1743step0 raw1743step0Labels = mixedMoment B raw1743step1 raw1743step1Labels := by
      have ha : raw1743step1 = raw1743step0 := by apply Matrix.ext; unfold raw1743step1 raw1743step0; decide +kernel
      have hl : raw1743step0Labels = labelEmbedding7 ∘ raw1743step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1743step0 raw1743step0Labels raw1743step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical1744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1744 raw1744Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw1744 raw1744Labels = mixedMoment B raw1744step0 raw1744step0Labels := by
      have ha : raw1744step0 = (fun i j => raw1744 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1744step0 raw1744; decide +kernel
      have hl : raw1744step0Labels = raw1744Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1744 raw1744Labels permutation32 permutation4
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical1745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1745 raw1745Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw1745 raw1745Labels = mixedMoment B raw1745step0 raw1745step0Labels := by
      have ha : raw1745step0 = (fun i j => raw1745 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1745step0 raw1745; decide +kernel
      have hl : raw1745step0Labels = raw1745Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1745 raw1745Labels permutation32 permutation6
    mixedMoment B raw1745step0 raw1745step0Labels = mixedMoment B raw1745step1 raw1745step1Labels := by
      have ha : raw1745step1 = -raw1745step0 := by apply Matrix.ext; change ∀ i j, raw1745step1 i j = -(raw1745step0 i j); unfold raw1745step1 raw1745step0; decide +kernel
      have hl : raw1745step1Labels = raw1745step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1745step1 raw1745step1Labels = mixedMoment B raw1745step2 raw1745step2Labels := by
      have ha : raw1745step2 = raw1745step1 := by apply Matrix.ext; unfold raw1745step2 raw1745step1; decide +kernel
      have hl : raw1745step1Labels = labelEmbedding1 ∘ raw1745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1745step1 raw1745step1Labels raw1745step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

theorem canonical1749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1749 raw1749Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw1749 raw1749Labels = mixedMoment B raw1749step0 raw1749step0Labels := by
      have ha : raw1749step0 = (fun i j => raw1749 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1749step0 raw1749; decide +kernel
      have hl : raw1749step0Labels = raw1749Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1749 raw1749Labels permutation32 permutation4
    mixedMoment B raw1749step0 raw1749step0Labels = mixedMoment B raw1749step1 raw1749step1Labels := by
      have ha : raw1749step1 = raw1749step0 := by apply Matrix.ext; unfold raw1749step1 raw1749step0; decide +kernel
      have hl : raw1749step0Labels = labelEmbedding7 ∘ raw1749step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1749step0 raw1749step0Labels raw1749step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

theorem canonical1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1750 raw1750Labels = mixedMoment B node2029 node2029Labels := by
  calc
    mixedMoment B raw1750 raw1750Labels = mixedMoment B raw1750step0 raw1750step0Labels := by
      have ha : raw1750step0 = (fun i j => raw1750 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1750step0 raw1750; decide +kernel
      have hl : raw1750step0Labels = raw1750Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1750 raw1750Labels permutation32 permutation4
    _ = mixedMoment B node2029 node2029Labels := by rfl

theorem canonical1751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1751 raw1751Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw1751 raw1751Labels = mixedMoment B raw1751step0 raw1751step0Labels := by
      have ha : raw1751step0 = (fun i j => raw1751 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1751step0 raw1751; decide +kernel
      have hl : raw1751step0Labels = raw1751Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1751 raw1751Labels permutation32 permutation6
    mixedMoment B raw1751step0 raw1751step0Labels = mixedMoment B raw1751step1 raw1751step1Labels := by
      have ha : raw1751step1 = -raw1751step0 := by apply Matrix.ext; change ∀ i j, raw1751step1 i j = -(raw1751step0 i j); unfold raw1751step1 raw1751step0; decide +kernel
      have hl : raw1751step1Labels = raw1751step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1751step1 raw1751step1Labels = mixedMoment B raw1751step2 raw1751step2Labels := by
      have ha : raw1751step2 = raw1751step1 := by apply Matrix.ext; unfold raw1751step2 raw1751step1; decide +kernel
      have hl : raw1751step1Labels = labelEmbedding1 ∘ raw1751step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1751step1 raw1751step1Labels raw1751step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2225 node2225Labels := by rfl

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

theorem canonical1803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1803 raw1803Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw1803 raw1803Labels = mixedMoment B raw1803step0 raw1803step0Labels := by
      have ha : raw1803step0 = (fun i j => raw1803 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1803step0 raw1803; decide +kernel
      have hl : raw1803step0Labels = raw1803Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1803 raw1803Labels permutation8 permutation4
    mixedMoment B raw1803step0 raw1803step0Labels = mixedMoment B raw1803step1 raw1803step1Labels := by
      have ha : raw1803step1 = raw1803step0 := by apply Matrix.ext; unfold raw1803step1 raw1803step0; decide +kernel
      have hl : raw1803step0Labels = labelEmbedding7 ∘ raw1803step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1803step0 raw1803step0Labels raw1803step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

theorem canonical1804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1804 raw1804Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw1804 raw1804Labels = mixedMoment B raw1804step0 raw1804step0Labels := by
      have ha : raw1804step0 = (fun i j => raw1804 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1804step0 raw1804; decide +kernel
      have hl : raw1804step0Labels = raw1804Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1804 raw1804Labels permutation8 permutation4
    _ = mixedMoment B node2112 node2112Labels := by rfl

theorem canonical1805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1805 raw1805Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw1805 raw1805Labels = mixedMoment B raw1805step0 raw1805step0Labels := by
      have ha : raw1805step0 = (fun i j => raw1805 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1805step0 raw1805; decide +kernel
      have hl : raw1805step0Labels = raw1805Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1805 raw1805Labels permutation8 permutation6
    mixedMoment B raw1805step0 raw1805step0Labels = mixedMoment B raw1805step1 raw1805step1Labels := by
      have ha : raw1805step1 = -raw1805step0 := by apply Matrix.ext; change ∀ i j, raw1805step1 i j = -(raw1805step0 i j); unfold raw1805step1 raw1805step0; decide +kernel
      have hl : raw1805step1Labels = raw1805step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1805step1 raw1805step1Labels = mixedMoment B raw1805step2 raw1805step2Labels := by
      have ha : raw1805step2 = raw1805step1 := by apply Matrix.ext; unfold raw1805step2 raw1805step1; decide +kernel
      have hl : raw1805step1Labels = labelEmbedding1 ∘ raw1805step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1805step1 raw1805step1Labels raw1805step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2287 node2287Labels := by rfl

theorem canonical1821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1821 raw1821Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw1821 raw1821Labels = mixedMoment B raw1821step0 raw1821step0Labels := by
      have ha : raw1821step0 = (fun i j => raw1821 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1821step0 raw1821; decide +kernel
      have hl : raw1821step0Labels = raw1821Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1821 raw1821Labels permutation8 permutation4
    mixedMoment B raw1821step0 raw1821step0Labels = mixedMoment B raw1821step1 raw1821step1Labels := by
      have ha : raw1821step1 = raw1821step0 := by apply Matrix.ext; unfold raw1821step1 raw1821step0; decide +kernel
      have hl : raw1821step0Labels = labelEmbedding7 ∘ raw1821step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1821step0 raw1821step0Labels raw1821step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical1822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1822 raw1822Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw1822 raw1822Labels = mixedMoment B raw1822step0 raw1822step0Labels := by
      have ha : raw1822step0 = (fun i j => raw1822 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1822step0 raw1822; decide +kernel
      have hl : raw1822step0Labels = raw1822Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1822 raw1822Labels permutation8 permutation4
    _ = mixedMoment B node2247 node2247Labels := by rfl

theorem canonical1823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1823 raw1823Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw1823 raw1823Labels = mixedMoment B raw1823step0 raw1823step0Labels := by
      have ha : raw1823step0 = (fun i j => raw1823 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1823step0 raw1823; decide +kernel
      have hl : raw1823step0Labels = raw1823Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1823 raw1823Labels permutation8 permutation6
    mixedMoment B raw1823step0 raw1823step0Labels = mixedMoment B raw1823step1 raw1823step1Labels := by
      have ha : raw1823step1 = -raw1823step0 := by apply Matrix.ext; change ∀ i j, raw1823step1 i j = -(raw1823step0 i j); unfold raw1823step1 raw1823step0; decide +kernel
      have hl : raw1823step1Labels = raw1823step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1823step1 raw1823step1Labels = mixedMoment B raw1823step2 raw1823step2Labels := by
      have ha : raw1823step2 = raw1823step1 := by apply Matrix.ext; unfold raw1823step2 raw1823step1; decide +kernel
      have hl : raw1823step1Labels = labelEmbedding1 ∘ raw1823step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1823step1 raw1823step1Labels raw1823step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2290 node2290Labels := by rfl

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

theorem canonical2280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2280 raw2280Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw2280 raw2280Labels = mixedMoment B raw2280step0 raw2280step0Labels := by
      have ha : raw2280step0 = (fun i j => raw2280 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2280step0 raw2280; decide +kernel
      have hl : raw2280step0Labels = raw2280Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2280 raw2280Labels permutation32 permutation4
    mixedMoment B raw2280step0 raw2280step0Labels = mixedMoment B raw2280step1 raw2280step1Labels := by
      have ha : raw2280step1 = raw2280step0 := by apply Matrix.ext; unfold raw2280step1 raw2280step0; decide +kernel
      have hl : raw2280step0Labels = labelEmbedding7 ∘ raw2280step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2280step0 raw2280step0Labels raw2280step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical2281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2281 raw2281Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw2281 raw2281Labels = mixedMoment B raw2281step0 raw2281step0Labels := by
      have ha : raw2281step0 = (fun i j => raw2281 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2281step0 raw2281; decide +kernel
      have hl : raw2281step0Labels = raw2281Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2281 raw2281Labels permutation32 permutation4
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical2282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2282 raw2282Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw2282 raw2282Labels = mixedMoment B raw2282step0 raw2282step0Labels := by
      have ha : raw2282step0 = (fun i j => raw2282 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2282step0 raw2282; decide +kernel
      have hl : raw2282step0Labels = raw2282Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2282 raw2282Labels permutation32 permutation6
    mixedMoment B raw2282step0 raw2282step0Labels = mixedMoment B raw2282step1 raw2282step1Labels := by
      have ha : raw2282step1 = -raw2282step0 := by apply Matrix.ext; change ∀ i j, raw2282step1 i j = -(raw2282step0 i j); unfold raw2282step1 raw2282step0; decide +kernel
      have hl : raw2282step1Labels = raw2282step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2282step1 raw2282step1Labels = mixedMoment B raw2282step2 raw2282step2Labels := by
      have ha : raw2282step2 = raw2282step1 := by apply Matrix.ext; unfold raw2282step2 raw2282step1; decide +kernel
      have hl : raw2282step1Labels = labelEmbedding1 ∘ raw2282step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2282step1 raw2282step1Labels raw2282step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical218
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28020 raw28020Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw28020 raw28020Labels = mixedMoment B raw28020step0 raw28020step0Labels := by
      have hz : ∀ j, raw28020 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28020step0 = (fun i j => raw28020 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28020step0 raw28020; decide +kernel
      have hl : raw28020step0Labels = raw28020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28020 raw28020Labels permutation346 hz
    mixedMoment B raw28020step0 raw28020step0Labels = mixedMoment B raw28020step1 raw28020step1Labels := by
      have ha : raw28020step1 = (fun i j => raw28020step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28020step1 raw28020step0; decide +kernel
      have hl : raw28020step1Labels = raw28020step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28020step0 raw28020step0Labels permutation150 permutation2
    mixedMoment B raw28020step1 raw28020step1Labels = mixedMoment B raw28020step2 raw28020step2Labels := by
      have ha : raw28020step2 = -raw28020step1 := by apply Matrix.ext; change ∀ i j, raw28020step2 i j = -(raw28020step1 i j); unfold raw28020step2 raw28020step1; decide +kernel
      have hl : raw28020step2Labels = raw28020step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4811 node4811Labels := by rfl

theorem canonical28021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28021 raw28021Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw28021 raw28021Labels = mixedMoment B raw28021step0 raw28021step0Labels := by
      have ha : raw28021step0 = (fun i j => raw28021 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28021step0 raw28021; decide +kernel
      have hl : raw28021step0Labels = raw28021Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28021 raw28021Labels permutation688 permutation2
    mixedMoment B raw28021step0 raw28021step0Labels = mixedMoment B raw28021step1 raw28021step1Labels := by
      have ha : raw28021step1 = -raw28021step0 := by apply Matrix.ext; change ∀ i j, raw28021step1 i j = -(raw28021step0 i j); unfold raw28021step1 raw28021step0; decide +kernel
      have hl : raw28021step1Labels = raw28021step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4802 node4802Labels := by rfl

theorem canonical28022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28022 raw28022Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw28022 raw28022Labels = mixedMoment B raw28022step0 raw28022step0Labels := by
      have hz : ∀ j, raw28022 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28022step0 = (fun i j => raw28022 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28022step0 raw28022; decide +kernel
      have hl : raw28022step0Labels = raw28022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28022 raw28022Labels permutation346 hz
    mixedMoment B raw28022step0 raw28022step0Labels = mixedMoment B raw28022step1 raw28022step1Labels := by
      have ha : raw28022step1 = (fun i j => raw28022step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28022step1 raw28022step0; decide +kernel
      have hl : raw28022step1Labels = raw28022step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28022step0 raw28022step0Labels permutation149 permutation2
    mixedMoment B raw28022step1 raw28022step1Labels = mixedMoment B raw28022step2 raw28022step2Labels := by
      have ha : raw28022step2 = -raw28022step1 := by apply Matrix.ext; change ∀ i j, raw28022step2 i j = -(raw28022step1 i j); unfold raw28022step2 raw28022step1; decide +kernel
      have hl : raw28022step2Labels = raw28022step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4838 node4838Labels := by rfl

theorem canonical28023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28023 raw28023Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw28023 raw28023Labels = mixedMoment B raw28023step0 raw28023step0Labels := by
      have hz : ∀ j, raw28023 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28023step0 = (fun i j => raw28023 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28023step0 raw28023; decide +kernel
      have hl : raw28023step0Labels = raw28023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28023 raw28023Labels permutation520 hz
    mixedMoment B raw28023step0 raw28023step0Labels = mixedMoment B raw28023step1 raw28023step1Labels := by
      have hz : ∀ j, raw28023step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28023step1 = (fun i j => raw28023step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28023step1 raw28023step0; decide +kernel
      have hl : raw28023step1Labels = raw28023step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28023step0 raw28023step0Labels permutation80 hz
    mixedMoment B raw28023step1 raw28023step1Labels = mixedMoment B raw28023step2 raw28023step2Labels := by
      have ha : raw28023step2 = (fun i j => raw28023step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28023step2 raw28023step1; decide +kernel
      have hl : raw28023step2Labels = raw28023step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28023step1 raw28023step1Labels permutation31 permutation2
    mixedMoment B raw28023step2 raw28023step2Labels = mixedMoment B raw28023step3 raw28023step3Labels := by
      have ha : raw28023step3 = -raw28023step2 := by apply Matrix.ext; change ∀ i j, raw28023step3 i j = -(raw28023step2 i j); unfold raw28023step3 raw28023step2; decide +kernel
      have hl : raw28023step3Labels = raw28023step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4895 node4895Labels := by rfl

theorem canonical28024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28024 raw28024Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw28024 raw28024Labels = mixedMoment B raw28024step0 raw28024step0Labels := by
      have hz : ∀ j, raw28024 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28024step0 = (fun i j => raw28024 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28024step0 raw28024; decide +kernel
      have hl : raw28024step0Labels = raw28024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28024 raw28024Labels permutation346 hz
    mixedMoment B raw28024step0 raw28024step0Labels = mixedMoment B raw28024step1 raw28024step1Labels := by
      have ha : raw28024step1 = (fun i j => raw28024step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28024step1 raw28024step0; decide +kernel
      have hl : raw28024step1Labels = raw28024step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28024step0 raw28024step0Labels permutation151 permutation7
    mixedMoment B raw28024step1 raw28024step1Labels = mixedMoment B raw28024step2 raw28024step2Labels := by
      have ha : raw28024step2 = raw28024step1 := by apply Matrix.ext; unfold raw28024step2 raw28024step1; decide +kernel
      have hl : raw28024step1Labels = labelEmbedding10 ∘ raw28024step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28024step1 raw28024step1Labels raw28024step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

theorem canonical28025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28025 raw28025Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw28025 raw28025Labels = mixedMoment B raw28025step0 raw28025step0Labels := by
      have hz : ∀ j, raw28025 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28025step0 = (fun i j => raw28025 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28025step0 raw28025; decide +kernel
      have hl : raw28025step0Labels = raw28025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28025 raw28025Labels permutation346 hz
    mixedMoment B raw28025step0 raw28025step0Labels = mixedMoment B raw28025step1 raw28025step1Labels := by
      have ha : raw28025step1 = (fun i j => raw28025step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28025step1 raw28025step0; decide +kernel
      have hl : raw28025step1Labels = raw28025step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28025step0 raw28025step0Labels permutation32 permutation3
    mixedMoment B raw28025step1 raw28025step1Labels = mixedMoment B raw28025step2 raw28025step2Labels := by
      have ha : raw28025step2 = raw28025step1 := by apply Matrix.ext; unfold raw28025step2 raw28025step1; decide +kernel
      have hl : raw28025step1Labels = labelEmbedding6 ∘ raw28025step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28025step1 raw28025step1Labels raw28025step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4442 node4442Labels := by rfl

theorem canonical28026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28026 raw28026Labels = mixedMoment B node4792 node4792Labels := by
  calc
    mixedMoment B raw28026 raw28026Labels = mixedMoment B raw28026step0 raw28026step0Labels := by
      have ha : raw28026step0 = (fun i j => raw28026 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28026step0 raw28026; decide +kernel
      have hl : raw28026step0Labels = raw28026Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28026 raw28026Labels permutation676 permutation2
    mixedMoment B raw28026step0 raw28026step0Labels = mixedMoment B raw28026step1 raw28026step1Labels := by
      have ha : raw28026step1 = -raw28026step0 := by apply Matrix.ext; change ∀ i j, raw28026step1 i j = -(raw28026step0 i j); unfold raw28026step1 raw28026step0; decide +kernel
      have hl : raw28026step1Labels = raw28026step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4792 node4792Labels := by rfl

theorem canonical28027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28027 raw28027Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw28027 raw28027Labels = mixedMoment B raw28027step0 raw28027step0Labels := by
      have hz : ∀ j, raw28027 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28027step0 = (fun i j => raw28027 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28027step0 raw28027; decide +kernel
      have hl : raw28027step0Labels = raw28027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28027 raw28027Labels permutation346 hz
    mixedMoment B raw28027step0 raw28027step0Labels = mixedMoment B raw28027step1 raw28027step1Labels := by
      have ha : raw28027step1 = (fun i j => raw28027step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28027step1 raw28027step0; decide +kernel
      have hl : raw28027step1Labels = raw28027step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28027step0 raw28027step0Labels permutation149 permutation2
    mixedMoment B raw28027step1 raw28027step1Labels = mixedMoment B raw28027step2 raw28027step2Labels := by
      have ha : raw28027step2 = -raw28027step1 := by apply Matrix.ext; change ∀ i j, raw28027step2 i j = -(raw28027step1 i j); unfold raw28027step2 raw28027step1; decide +kernel
      have hl : raw28027step2Labels = raw28027step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical28028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28028 raw28028Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw28028 raw28028Labels = mixedMoment B raw28028step0 raw28028step0Labels := by
      have hz : ∀ j, raw28028 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28028step0 = (fun i j => raw28028 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28028step0 raw28028; decide +kernel
      have hl : raw28028step0Labels = raw28028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28028 raw28028Labels permutation520 hz
    mixedMoment B raw28028step0 raw28028step0Labels = mixedMoment B raw28028step1 raw28028step1Labels := by
      have hz : ∀ j, raw28028step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28028step1 = (fun i j => raw28028step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28028step1 raw28028step0; decide +kernel
      have hl : raw28028step1Labels = raw28028step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28028step0 raw28028step0Labels permutation80 hz
    mixedMoment B raw28028step1 raw28028step1Labels = mixedMoment B raw28028step2 raw28028step2Labels := by
      have ha : raw28028step2 = (fun i j => raw28028step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28028step2 raw28028step1; decide +kernel
      have hl : raw28028step2Labels = raw28028step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28028step1 raw28028step1Labels permutation29 permutation2
    mixedMoment B raw28028step2 raw28028step2Labels = mixedMoment B raw28028step3 raw28028step3Labels := by
      have ha : raw28028step3 = -raw28028step2 := by apply Matrix.ext; change ∀ i j, raw28028step3 i j = -(raw28028step2 i j); unfold raw28028step3 raw28028step2; decide +kernel
      have hl : raw28028step3Labels = raw28028step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical28029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28029 raw28029Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw28029 raw28029Labels = mixedMoment B raw28029step0 raw28029step0Labels := by
      have hz : ∀ j, raw28029 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28029step0 = (fun i j => raw28029 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28029step0 raw28029; decide +kernel
      have hl : raw28029step0Labels = raw28029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28029 raw28029Labels permutation346 hz
    mixedMoment B raw28029step0 raw28029step0Labels = mixedMoment B raw28029step1 raw28029step1Labels := by
      have ha : raw28029step1 = (fun i j => raw28029step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28029step1 raw28029step0; decide +kernel
      have hl : raw28029step1Labels = raw28029step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28029step0 raw28029step0Labels permutation149 permutation7
    mixedMoment B raw28029step1 raw28029step1Labels = mixedMoment B raw28029step2 raw28029step2Labels := by
      have ha : raw28029step2 = raw28029step1 := by apply Matrix.ext; unfold raw28029step2 raw28029step1; decide +kernel
      have hl : raw28029step1Labels = labelEmbedding10 ∘ raw28029step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28029step1 raw28029step1Labels raw28029step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

theorem canonical28030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28030 raw28030Labels = mixedMoment B node4331 node4331Labels := by
  calc
    mixedMoment B raw28030 raw28030Labels = mixedMoment B raw28030step0 raw28030step0Labels := by
      have ha : raw28030step0 = (fun i j => raw28030 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28030step0 raw28030; decide +kernel
      have hl : raw28030step0Labels = raw28030Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28030 raw28030Labels permutation158 permutation3
    mixedMoment B raw28030step0 raw28030step0Labels = mixedMoment B raw28030step1 raw28030step1Labels := by
      have ha : raw28030step1 = raw28030step0 := by apply Matrix.ext; unfold raw28030step1 raw28030step0; decide +kernel
      have hl : raw28030step0Labels = labelEmbedding6 ∘ raw28030step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28030step0 raw28030step0Labels raw28030step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4331 node4331Labels := by rfl

theorem canonical28031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28031 raw28031Labels = mixedMoment B node4757 node4757Labels := by
  calc
    mixedMoment B raw28031 raw28031Labels = mixedMoment B raw28031step0 raw28031step0Labels := by
      have ha : raw28031step0 = (fun i j => raw28031 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28031step0 raw28031; decide +kernel
      have hl : raw28031step0Labels = raw28031Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28031 raw28031Labels permutation646 permutation2
    mixedMoment B raw28031step0 raw28031step0Labels = mixedMoment B raw28031step1 raw28031step1Labels := by
      have ha : raw28031step1 = -raw28031step0 := by apply Matrix.ext; change ∀ i j, raw28031step1 i j = -(raw28031step0 i j); unfold raw28031step1 raw28031step0; decide +kernel
      have hl : raw28031step1Labels = raw28031step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4757 node4757Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical219
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical28032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28032 raw28032Labels = mixedMoment B node4764 node4764Labels := by
  calc
    mixedMoment B raw28032 raw28032Labels = mixedMoment B raw28032step0 raw28032step0Labels := by
      have ha : raw28032step0 = (fun i j => raw28032 (permutation644 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28032step0 raw28032; decide +kernel
      have hl : raw28032step0Labels = raw28032Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28032 raw28032Labels permutation644 permutation2
    mixedMoment B raw28032step0 raw28032step0Labels = mixedMoment B raw28032step1 raw28032step1Labels := by
      have ha : raw28032step1 = -raw28032step0 := by apply Matrix.ext; change ∀ i j, raw28032step1 i j = -(raw28032step0 i j); unfold raw28032step1 raw28032step0; decide +kernel
      have hl : raw28032step1Labels = raw28032step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4764 node4764Labels := by rfl

theorem canonical28033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28033 raw28033Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw28033 raw28033Labels = mixedMoment B raw28033step0 raw28033step0Labels := by
      have hz : ∀ j, raw28033 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28033step0 = (fun i j => raw28033 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28033step0 raw28033; decide +kernel
      have hl : raw28033step0Labels = raw28033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28033 raw28033Labels permutation520 hz
    mixedMoment B raw28033step0 raw28033step0Labels = mixedMoment B raw28033step1 raw28033step1Labels := by
      have ha : raw28033step1 = (fun i j => raw28033step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28033step1 raw28033step0; decide +kernel
      have hl : raw28033step1Labels = raw28033step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28033step0 raw28033step0Labels permutation145 permutation2
    mixedMoment B raw28033step1 raw28033step1Labels = mixedMoment B raw28033step2 raw28033step2Labels := by
      have ha : raw28033step2 = -raw28033step1 := by apply Matrix.ext; change ∀ i j, raw28033step2 i j = -(raw28033step1 i j); unfold raw28033step2 raw28033step1; decide +kernel
      have hl : raw28033step2Labels = raw28033step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4807 node4807Labels := by rfl

theorem canonical28034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28034 raw28034Labels = mixedMoment B node5150 node5150Labels := by
  calc
    mixedMoment B raw28034 raw28034Labels = mixedMoment B raw28034step0 raw28034step0Labels := by
      have ha : raw28034step0 = (fun i j => raw28034 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28034step0 raw28034; decide +kernel
      have hl : raw28034step0Labels = raw28034Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28034 raw28034Labels permutation158 permutation3
    mixedMoment B raw28034step0 raw28034step0Labels = mixedMoment B raw28034step1 raw28034step1Labels := by
      have ha : raw28034step1 = raw28034step0 := by apply Matrix.ext; unfold raw28034step1 raw28034step0; decide +kernel
      have hl : raw28034step0Labels = labelEmbedding6 ∘ raw28034step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28034step0 raw28034step0Labels raw28034step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5150 node5150Labels := by rfl

theorem canonical28035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28035 raw28035Labels = mixedMoment B node4353 node4353Labels := by
  calc
    mixedMoment B raw28035 raw28035Labels = mixedMoment B raw28035step0 raw28035step0Labels := by
      have hz : ∀ j, raw28035 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28035step0 = (fun i j => raw28035 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28035step0 raw28035; decide +kernel
      have hl : raw28035step0Labels = raw28035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28035 raw28035Labels permutation346 hz
    mixedMoment B raw28035step0 raw28035step0Labels = mixedMoment B raw28035step1 raw28035step1Labels := by
      have ha : raw28035step1 = (fun i j => raw28035step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28035step1 raw28035step0; decide +kernel
      have hl : raw28035step1Labels = raw28035step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28035step0 raw28035step0Labels permutation34 permutation3
    mixedMoment B raw28035step1 raw28035step1Labels = mixedMoment B raw28035step2 raw28035step2Labels := by
      have ha : raw28035step2 = raw28035step1 := by apply Matrix.ext; unfold raw28035step2 raw28035step1; decide +kernel
      have hl : raw28035step1Labels = labelEmbedding6 ∘ raw28035step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28035step1 raw28035step1Labels raw28035step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4353 node4353Labels := by rfl

theorem canonical28036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28036 raw28036Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw28036 raw28036Labels = mixedMoment B raw28036step0 raw28036step0Labels := by
      have hz : ∀ j, raw28036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28036step0 = (fun i j => raw28036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28036step0 raw28036; decide +kernel
      have hl : raw28036step0Labels = raw28036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28036 raw28036Labels permutation346 hz
    mixedMoment B raw28036step0 raw28036step0Labels = mixedMoment B raw28036step1 raw28036step1Labels := by
      have ha : raw28036step1 = (fun i j => raw28036step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28036step1 raw28036step0; decide +kernel
      have hl : raw28036step1Labels = raw28036step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28036step0 raw28036step0Labels permutation151 permutation2
    mixedMoment B raw28036step1 raw28036step1Labels = mixedMoment B raw28036step2 raw28036step2Labels := by
      have ha : raw28036step2 = -raw28036step1 := by apply Matrix.ext; change ∀ i j, raw28036step2 i j = -(raw28036step1 i j); unfold raw28036step2 raw28036step1; decide +kernel
      have hl : raw28036step2Labels = raw28036step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4777 node4777Labels := by rfl

theorem canonical28037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28037 raw28037Labels = mixedMoment B node4772 node4772Labels := by
  calc
    mixedMoment B raw28037 raw28037Labels = mixedMoment B raw28037step0 raw28037step0Labels := by
      have ha : raw28037step0 = (fun i j => raw28037 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28037step0 raw28037; decide +kernel
      have hl : raw28037step0Labels = raw28037Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28037 raw28037Labels permutation688 permutation2
    mixedMoment B raw28037step0 raw28037step0Labels = mixedMoment B raw28037step1 raw28037step1Labels := by
      have ha : raw28037step1 = -raw28037step0 := by apply Matrix.ext; change ∀ i j, raw28037step1 i j = -(raw28037step0 i j); unfold raw28037step1 raw28037step0; decide +kernel
      have hl : raw28037step1Labels = raw28037step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4772 node4772Labels := by rfl

theorem canonical28038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28038 raw28038Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw28038 raw28038Labels = mixedMoment B raw28038step0 raw28038step0Labels := by
      have hz : ∀ j, raw28038 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28038step0 = (fun i j => raw28038 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28038step0 raw28038; decide +kernel
      have hl : raw28038step0Labels = raw28038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28038 raw28038Labels permutation520 hz
    mixedMoment B raw28038step0 raw28038step0Labels = mixedMoment B raw28038step1 raw28038step1Labels := by
      have hz : ∀ j, raw28038step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28038step1 = (fun i j => raw28038step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28038step1 raw28038step0; decide +kernel
      have hl : raw28038step1Labels = raw28038step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28038step0 raw28038step0Labels permutation80 hz
    mixedMoment B raw28038step1 raw28038step1Labels = mixedMoment B raw28038step2 raw28038step2Labels := by
      have ha : raw28038step2 = (fun i j => raw28038step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28038step2 raw28038step1; decide +kernel
      have hl : raw28038step2Labels = raw28038step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28038step1 raw28038step1Labels permutation31 permutation2
    mixedMoment B raw28038step2 raw28038step2Labels = mixedMoment B raw28038step3 raw28038step3Labels := by
      have ha : raw28038step3 = -raw28038step2 := by apply Matrix.ext; change ∀ i j, raw28038step3 i j = -(raw28038step2 i j); unfold raw28038step3 raw28038step2; decide +kernel
      have hl : raw28038step3Labels = raw28038step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4871 node4871Labels := by rfl

theorem canonical28039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28039 raw28039Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw28039 raw28039Labels = mixedMoment B raw28039step0 raw28039step0Labels := by
      have hz : ∀ j, raw28039 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28039step0 = (fun i j => raw28039 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28039step0 raw28039; decide +kernel
      have hl : raw28039step0Labels = raw28039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28039 raw28039Labels permutation346 hz
    mixedMoment B raw28039step0 raw28039step0Labels = mixedMoment B raw28039step1 raw28039step1Labels := by
      have ha : raw28039step1 = (fun i j => raw28039step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28039step1 raw28039step0; decide +kernel
      have hl : raw28039step1Labels = raw28039step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28039step0 raw28039step0Labels permutation34 permutation3
    mixedMoment B raw28039step1 raw28039step1Labels = mixedMoment B raw28039step2 raw28039step2Labels := by
      have ha : raw28039step2 = raw28039step1 := by apply Matrix.ext; unfold raw28039step2 raw28039step1; decide +kernel
      have hl : raw28039step1Labels = labelEmbedding6 ∘ raw28039step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28039step1 raw28039step1Labels raw28039step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

theorem canonical28040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28040 raw28040Labels = mixedMoment B node4336 node4336Labels := by
  calc
    mixedMoment B raw28040 raw28040Labels = mixedMoment B raw28040step0 raw28040step0Labels := by
      have hz : ∀ j, raw28040 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28040step0 = (fun i j => raw28040 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28040step0 raw28040; decide +kernel
      have hl : raw28040step0Labels = raw28040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28040 raw28040Labels permutation346 hz
    mixedMoment B raw28040step0 raw28040step0Labels = mixedMoment B raw28040step1 raw28040step1Labels := by
      have ha : raw28040step1 = (fun i j => raw28040step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28040step1 raw28040step0; decide +kernel
      have hl : raw28040step1Labels = raw28040step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28040step0 raw28040step0Labels permutation32 permutation3
    mixedMoment B raw28040step1 raw28040step1Labels = mixedMoment B raw28040step2 raw28040step2Labels := by
      have ha : raw28040step2 = raw28040step1 := by apply Matrix.ext; unfold raw28040step2 raw28040step1; decide +kernel
      have hl : raw28040step1Labels = labelEmbedding6 ∘ raw28040step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28040step1 raw28040step1Labels raw28040step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4336 node4336Labels := by rfl

theorem canonical28041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28041 raw28041Labels = mixedMoment B node4670 node4670Labels := by
  calc
    mixedMoment B raw28041 raw28041Labels = mixedMoment B raw28041step0 raw28041step0Labels := by
      have hz : ∀ j, raw28041 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28041step0 = (fun i j => raw28041 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28041step0 raw28041; decide +kernel
      have hl : raw28041step0Labels = raw28041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28041 raw28041Labels permutation346 hz
    mixedMoment B raw28041step0 raw28041step0Labels = mixedMoment B raw28041step1 raw28041step1Labels := by
      have ha : raw28041step1 = (fun i j => raw28041step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28041step1 raw28041step0; decide +kernel
      have hl : raw28041step1Labels = raw28041step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28041step0 raw28041step0Labels permutation151 permutation2
    mixedMoment B raw28041step1 raw28041step1Labels = mixedMoment B raw28041step2 raw28041step2Labels := by
      have ha : raw28041step2 = -raw28041step1 := by apply Matrix.ext; change ∀ i j, raw28041step2 i j = -(raw28041step1 i j); unfold raw28041step2 raw28041step1; decide +kernel
      have hl : raw28041step2Labels = raw28041step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4670 node4670Labels := by rfl

theorem canonical28042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28042 raw28042Labels = mixedMoment B node4664 node4664Labels := by
  calc
    mixedMoment B raw28042 raw28042Labels = mixedMoment B raw28042step0 raw28042step0Labels := by
      have ha : raw28042step0 = (fun i j => raw28042 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28042step0 raw28042; decide +kernel
      have hl : raw28042step0Labels = raw28042Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28042 raw28042Labels permutation688 permutation2
    mixedMoment B raw28042step0 raw28042step0Labels = mixedMoment B raw28042step1 raw28042step1Labels := by
      have ha : raw28042step1 = -raw28042step0 := by apply Matrix.ext; change ∀ i j, raw28042step1 i j = -(raw28042step0 i j); unfold raw28042step1 raw28042step0; decide +kernel
      have hl : raw28042step1Labels = raw28042step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4664 node4664Labels := by rfl

theorem canonical28043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28043 raw28043Labels = mixedMoment B node4686 node4686Labels := by
  calc
    mixedMoment B raw28043 raw28043Labels = mixedMoment B raw28043step0 raw28043step0Labels := by
      have hz : ∀ j, raw28043 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28043step0 = (fun i j => raw28043 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28043step0 raw28043; decide +kernel
      have hl : raw28043step0Labels = raw28043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28043 raw28043Labels permutation346 hz
    mixedMoment B raw28043step0 raw28043step0Labels = mixedMoment B raw28043step1 raw28043step1Labels := by
      have ha : raw28043step1 = (fun i j => raw28043step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28043step1 raw28043step0; decide +kernel
      have hl : raw28043step1Labels = raw28043step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28043step0 raw28043step0Labels permutation149 permutation2
    mixedMoment B raw28043step1 raw28043step1Labels = mixedMoment B raw28043step2 raw28043step2Labels := by
      have ha : raw28043step2 = -raw28043step1 := by apply Matrix.ext; change ∀ i j, raw28043step2 i j = -(raw28043step1 i j); unfold raw28043step2 raw28043step1; decide +kernel
      have hl : raw28043step2Labels = raw28043step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4686 node4686Labels := by rfl

theorem canonical28044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28044 raw28044Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw28044 raw28044Labels = mixedMoment B raw28044step0 raw28044step0Labels := by
      have hz : ∀ j, raw28044 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28044step0 = (fun i j => raw28044 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28044step0 raw28044; decide +kernel
      have hl : raw28044step0Labels = raw28044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28044 raw28044Labels permutation346 hz
    mixedMoment B raw28044step0 raw28044step0Labels = mixedMoment B raw28044step1 raw28044step1Labels := by
      have ha : raw28044step1 = (fun i j => raw28044step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28044step1 raw28044step0; decide +kernel
      have hl : raw28044step1Labels = raw28044step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28044step0 raw28044step0Labels permutation33 permutation3
    mixedMoment B raw28044step1 raw28044step1Labels = mixedMoment B raw28044step2 raw28044step2Labels := by
      have ha : raw28044step2 = raw28044step1 := by apply Matrix.ext; unfold raw28044step2 raw28044step1; decide +kernel
      have hl : raw28044step1Labels = labelEmbedding6 ∘ raw28044step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28044step1 raw28044step1Labels raw28044step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5151 node5151Labels := by rfl

theorem canonical28045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28045 raw28045Labels = mixedMoment B node4333 node4333Labels := by
  calc
    mixedMoment B raw28045 raw28045Labels = mixedMoment B raw28045step0 raw28045step0Labels := by
      have hz : ∀ j, raw28045 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28045step0 = (fun i j => raw28045 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28045step0 raw28045; decide +kernel
      have hl : raw28045step0Labels = raw28045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28045 raw28045Labels permutation346 hz
    mixedMoment B raw28045step0 raw28045step0Labels = mixedMoment B raw28045step1 raw28045step1Labels := by
      have ha : raw28045step1 = (fun i j => raw28045step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28045step1 raw28045step0; decide +kernel
      have hl : raw28045step1Labels = raw28045step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28045step0 raw28045step0Labels permutation151 permutation2
    mixedMoment B raw28045step1 raw28045step1Labels = mixedMoment B raw28045step2 raw28045step2Labels := by
      have ha : raw28045step2 = -raw28045step1 := by apply Matrix.ext; change ∀ i j, raw28045step2 i j = -(raw28045step1 i j); unfold raw28045step2 raw28045step1; decide +kernel
      have hl : raw28045step2Labels = raw28045step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4333 node4333Labels := by rfl

theorem canonical28046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28046 raw28046Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw28046 raw28046Labels = mixedMoment B raw28046step0 raw28046step0Labels := by
      have hz : ∀ j, raw28046 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28046step0 = (fun i j => raw28046 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28046step0 raw28046; decide +kernel
      have hl : raw28046step0Labels = raw28046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28046 raw28046Labels permutation346 hz
    mixedMoment B raw28046step0 raw28046step0Labels = mixedMoment B raw28046step1 raw28046step1Labels := by
      have ha : raw28046step1 = (fun i j => raw28046step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28046step1 raw28046step0; decide +kernel
      have hl : raw28046step1Labels = raw28046step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28046step0 raw28046step0Labels permutation151 permutation2
    mixedMoment B raw28046step1 raw28046step1Labels = mixedMoment B raw28046step2 raw28046step2Labels := by
      have ha : raw28046step2 = -raw28046step1 := by apply Matrix.ext; change ∀ i j, raw28046step2 i j = -(raw28046step1 i j); unfold raw28046step2 raw28046step1; decide +kernel
      have hl : raw28046step2Labels = raw28046step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4335 node4335Labels := by rfl

theorem canonical28047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28047 raw28047Labels = mixedMoment B node4327 node4327Labels := by
  calc
    mixedMoment B raw28047 raw28047Labels = mixedMoment B raw28047step0 raw28047step0Labels := by
      have ha : raw28047step0 = (fun i j => raw28047 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28047step0 raw28047; decide +kernel
      have hl : raw28047step0Labels = raw28047Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28047 raw28047Labels permutation688 permutation2
    mixedMoment B raw28047step0 raw28047step0Labels = mixedMoment B raw28047step1 raw28047step1Labels := by
      have ha : raw28047step1 = -raw28047step0 := by apply Matrix.ext; change ∀ i j, raw28047step1 i j = -(raw28047step0 i j); unfold raw28047step1 raw28047step0; decide +kernel
      have hl : raw28047step1Labels = raw28047step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4327 node4327Labels := by rfl

theorem canonical28048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28048 raw28048Labels = mixedMoment B node4352 node4352Labels := by
  calc
    mixedMoment B raw28048 raw28048Labels = mixedMoment B raw28048step0 raw28048step0Labels := by
      have hz : ∀ j, raw28048 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28048step0 = (fun i j => raw28048 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28048step0 raw28048; decide +kernel
      have hl : raw28048step0Labels = raw28048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28048 raw28048Labels permutation346 hz
    mixedMoment B raw28048step0 raw28048step0Labels = mixedMoment B raw28048step1 raw28048step1Labels := by
      have ha : raw28048step1 = (fun i j => raw28048step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28048step1 raw28048step0; decide +kernel
      have hl : raw28048step1Labels = raw28048step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28048step0 raw28048step0Labels permutation149 permutation2
    mixedMoment B raw28048step1 raw28048step1Labels = mixedMoment B raw28048step2 raw28048step2Labels := by
      have ha : raw28048step2 = -raw28048step1 := by apply Matrix.ext; change ∀ i j, raw28048step2 i j = -(raw28048step1 i j); unfold raw28048step2 raw28048step1; decide +kernel
      have hl : raw28048step2Labels = raw28048step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4352 node4352Labels := by rfl

theorem canonical28049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28049 raw28049Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw28049 raw28049Labels = mixedMoment B raw28049step0 raw28049step0Labels := by
      have hz : ∀ j, raw28049 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28049step0 = (fun i j => raw28049 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28049step0 raw28049; decide +kernel
      have hl : raw28049step0Labels = raw28049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28049 raw28049Labels permutation520 hz
    mixedMoment B raw28049step0 raw28049step0Labels = mixedMoment B raw28049step1 raw28049step1Labels := by
      have hz : ∀ j, raw28049step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28049step1 = (fun i j => raw28049step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28049step1 raw28049step0; decide +kernel
      have hl : raw28049step1Labels = raw28049step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28049step0 raw28049step0Labels permutation80 hz
    mixedMoment B raw28049step1 raw28049step1Labels = mixedMoment B raw28049step2 raw28049step2Labels := by
      have ha : raw28049step2 = (fun i j => raw28049step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28049step2 raw28049step1; decide +kernel
      have hl : raw28049step2Labels = raw28049step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28049step1 raw28049step1Labels permutation31 permutation2
    mixedMoment B raw28049step2 raw28049step2Labels = mixedMoment B raw28049step3 raw28049step3Labels := by
      have ha : raw28049step3 = -raw28049step2 := by apply Matrix.ext; change ∀ i j, raw28049step3 i j = -(raw28049step2 i j); unfold raw28049step3 raw28049step2; decide +kernel
      have hl : raw28049step3Labels = raw28049step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4463 node4463Labels := by rfl

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

theorem singleton4686 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4686 node4686Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1812 node1812Labels + mixedMoment B node2165 node2165Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1572 singletonSmall4686
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4686) = raw1572Labels := by decide +kernel
  rw [hl, canonical1572 B hB] at h
  have hc0 : mixedMoment B raw1572 (Fin.cases (0 : Fin 2) singletonSmall4686) =
      mixedMoment B node1812 node1812Labels := by
    have ha : raw1572 = raw1573 := by apply Matrix.ext; unfold raw1572 raw1573; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4686 = raw1573Labels := by decide +kernel
    rw [ha, hj, canonical1573 B hB]
  have hc1 : mixedMoment B raw1572 (Fin.cases (1 : Fin 2) singletonSmall4686) =
      mixedMoment B node2165 node2165Labels := by
    have ha : raw1572 = raw1574 := by apply Matrix.ext; unfold raw1572 raw1574; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4686 = raw1574Labels := by decide +kernel
    rw [ha, hj, canonical1574 B hB]
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

theorem singleton4764 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4764 node4764Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1964 node1964Labels + mixedMoment B node2182 node2182Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1695 singletonSmall4764
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4764) = raw1695Labels := by decide +kernel
  rw [hl, canonical1695 B hB] at h
  have hc0 : mixedMoment B raw1695 (Fin.cases (0 : Fin 2) singletonSmall4764) =
      mixedMoment B node1964 node1964Labels := by
    have ha : raw1695 = raw1696 := by apply Matrix.ext; unfold raw1695 raw1696; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4764 = raw1696Labels := by decide +kernel
    rw [ha, hj, canonical1696 B hB]
  have hc1 : mixedMoment B raw1695 (Fin.cases (1 : Fin 2) singletonSmall4764) =
      mixedMoment B node2182 node2182Labels := by
    have ha : raw1695 = raw1697 := by apply Matrix.ext; unfold raw1695 raw1697; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4764 = raw1697Labels := by decide +kernel
    rw [ha, hj, canonical1697 B hB]
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

theorem singleton4802 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4802 node4802Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2020 node2020Labels + mixedMoment B node2202 node2202Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1734 singletonSmall4802
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4802) = raw1734Labels := by decide +kernel
  rw [hl, canonical1734 B hB] at h
  have hc0 : mixedMoment B raw1734 (Fin.cases (0 : Fin 2) singletonSmall4802) =
      mixedMoment B node2020 node2020Labels := by
    have ha : raw1734 = raw1735 := by apply Matrix.ext; unfold raw1734 raw1735; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4802 = raw1735Labels := by decide +kernel
    rw [ha, hj, canonical1735 B hB]
  have hc1 : mixedMoment B raw1734 (Fin.cases (1 : Fin 2) singletonSmall4802) =
      mixedMoment B node2202 node2202Labels := by
    have ha : raw1734 = raw1736 := by apply Matrix.ext; unfold raw1734 raw1736; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4802 = raw1736Labels := by decide +kernel
    rw [ha, hj, canonical1736 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4807 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4807 node4807Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2025 node2025Labels + mixedMoment B node2224 node2224Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1743 singletonSmall4807
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4807) = raw1743Labels := by decide +kernel
  rw [hl, canonical1743 B hB] at h
  have hc0 : mixedMoment B raw1743 (Fin.cases (0 : Fin 2) singletonSmall4807) =
      mixedMoment B node2025 node2025Labels := by
    have ha : raw1743 = raw1744 := by apply Matrix.ext; unfold raw1743 raw1744; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4807 = raw1744Labels := by decide +kernel
    rw [ha, hj, canonical1744 B hB]
  have hc1 : mixedMoment B raw1743 (Fin.cases (1 : Fin 2) singletonSmall4807) =
      mixedMoment B node2224 node2224Labels := by
    have ha : raw1743 = raw1745 := by apply Matrix.ext; unfold raw1743 raw1745; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4807 = raw1745Labels := by decide +kernel
    rw [ha, hj, canonical1745 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4811 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4811 node4811Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2029 node2029Labels + mixedMoment B node2225 node2225Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1749 singletonSmall4811
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4811) = raw1749Labels := by decide +kernel
  rw [hl, canonical1749 B hB] at h
  have hc0 : mixedMoment B raw1749 (Fin.cases (0 : Fin 2) singletonSmall4811) =
      mixedMoment B node2029 node2029Labels := by
    have ha : raw1749 = raw1750 := by apply Matrix.ext; unfold raw1749 raw1750; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4811 = raw1750Labels := by decide +kernel
    rw [ha, hj, canonical1750 B hB]
  have hc1 : mixedMoment B raw1749 (Fin.cases (1 : Fin 2) singletonSmall4811) =
      mixedMoment B node2225 node2225Labels := by
    have ha : raw1749 = raw1751 := by apply Matrix.ext; unfold raw1749 raw1751; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4811 = raw1751Labels := by decide +kernel
    rw [ha, hj, canonical1751 B hB]
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

theorem singleton4871 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4871 node4871Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2112 node2112Labels + mixedMoment B node2287 node2287Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1803 singletonSmall4871
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4871) = raw1803Labels := by decide +kernel
  rw [hl, canonical1803 B hB] at h
  have hc0 : mixedMoment B raw1803 (Fin.cases (0 : Fin 2) singletonSmall4871) =
      mixedMoment B node2112 node2112Labels := by
    have ha : raw1803 = raw1804 := by apply Matrix.ext; unfold raw1803 raw1804; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4871 = raw1804Labels := by decide +kernel
    rw [ha, hj, canonical1804 B hB]
  have hc1 : mixedMoment B raw1803 (Fin.cases (1 : Fin 2) singletonSmall4871) =
      mixedMoment B node2287 node2287Labels := by
    have ha : raw1803 = raw1805 := by apply Matrix.ext; unfold raw1803 raw1805; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4871 = raw1805Labels := by decide +kernel
    rw [ha, hj, canonical1805 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4890 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4890 node4890Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2247 node2247Labels + mixedMoment B node2290 node2290Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1821 singletonSmall4890
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4890) = raw1821Labels := by decide +kernel
  rw [hl, canonical1821 B hB] at h
  have hc0 : mixedMoment B raw1821 (Fin.cases (0 : Fin 2) singletonSmall4890) =
      mixedMoment B node2247 node2247Labels := by
    have ha : raw1821 = raw1822 := by apply Matrix.ext; unfold raw1821 raw1822; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4890 = raw1822Labels := by decide +kernel
    rw [ha, hj, canonical1822 B hB]
  have hc1 : mixedMoment B raw1821 (Fin.cases (1 : Fin 2) singletonSmall4890) =
      mixedMoment B node2290 node2290Labels := by
    have ha : raw1821 = raw1823 := by apply Matrix.ext; unfold raw1821 raw1823; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4890 = raw1823Labels := by decide +kernel
    rw [ha, hj, canonical1823 B hB]
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

theorem singleton5271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5271 node5271Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2739 node2739Labels + mixedMoment B node3534 node3534Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2280 singletonSmall5271
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5271) = raw2280Labels := by decide +kernel
  rw [hl, canonical2280 B hB] at h
  have hc0 : mixedMoment B raw2280 (Fin.cases (0 : Fin 2) singletonSmall5271) =
      mixedMoment B node2739 node2739Labels := by
    have ha : raw2280 = raw2281 := by apply Matrix.ext; unfold raw2280 raw2281; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5271 = raw2281Labels := by decide +kernel
    rw [ha, hj, canonical2281 B hB]
  have hc1 : mixedMoment B raw2280 (Fin.cases (1 : Fin 2) singletonSmall5271) =
      mixedMoment B node3534 node3534Labels := by
    have ha : raw2280 = raw2282 := by apply Matrix.ext; unfold raw2280 raw2282; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5271 = raw2282Labels := by decide +kernel
    rw [ha, hj, canonical2282 B hB]
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

theorem sound930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node930 node930Labels = Sparse.eval nodeValue930 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 930) = mixedMoment B node930 node930Labels := rfl
  simpa [nodeValue930, Sparse.eval] using hc.symm

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

theorem sound1046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1046 node1046Labels = Sparse.eval nodeValue1046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1046) = mixedMoment B node1046 node1046Labels := rfl
  simpa [nodeValue1046, Sparse.eval] using hc.symm

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

theorem sound1690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1690 node1690Labels = Sparse.eval nodeValue1690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1690) = mixedMoment B node1690 node1690Labels := rfl
  simpa [nodeValue1690, Sparse.eval] using hc.symm

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

theorem sound1812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1812 node1812Labels = Sparse.eval nodeValue1812 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1812) = mixedMoment B node1812 node1812Labels := rfl
  simpa [nodeValue1812, Sparse.eval] using hc.symm

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

theorem sound1964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1964 node1964Labels = Sparse.eval nodeValue1964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1964) = mixedMoment B node1964 node1964Labels := rfl
  simpa [nodeValue1964, Sparse.eval] using hc.symm

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

theorem sound2020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2020 node2020Labels = Sparse.eval nodeValue2020 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2020) = mixedMoment B node2020 node2020Labels := rfl
  simpa [nodeValue2020, Sparse.eval] using hc.symm

theorem sound2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2025 node2025Labels = Sparse.eval nodeValue2025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2025) = mixedMoment B node2025 node2025Labels := rfl
  simpa [nodeValue2025, Sparse.eval] using hc.symm

theorem sound2029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2029 node2029Labels = Sparse.eval nodeValue2029 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2029) = mixedMoment B node2029 node2029Labels := rfl
  simpa [nodeValue2029, Sparse.eval] using hc.symm

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

theorem sound2112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2112 node2112Labels = Sparse.eval nodeValue2112 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2112) = mixedMoment B node2112 node2112Labels := rfl
  simpa [nodeValue2112, Sparse.eval] using hc.symm

theorem sound2165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2165 node2165Labels = Sparse.eval nodeValue2165 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2165) = mixedMoment B node2165 node2165Labels := rfl
  simpa [nodeValue2165, Sparse.eval] using hc.symm

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

theorem sound2182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2182 node2182Labels = Sparse.eval nodeValue2182 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2182) = mixedMoment B node2182 node2182Labels := rfl
  simpa [nodeValue2182, Sparse.eval] using hc.symm

theorem sound2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2202 node2202Labels = Sparse.eval nodeValue2202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2202) = mixedMoment B node2202 node2202Labels := rfl
  simpa [nodeValue2202, Sparse.eval] using hc.symm

theorem sound2224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2224 node2224Labels = Sparse.eval nodeValue2224 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2224) = mixedMoment B node2224 node2224Labels := rfl
  simpa [nodeValue2224, Sparse.eval] using hc.symm

theorem sound2225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2225 node2225Labels = Sparse.eval nodeValue2225 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2225) = mixedMoment B node2225 node2225Labels := rfl
  simpa [nodeValue2225, Sparse.eval] using hc.symm

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

theorem sound2247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2247 node2247Labels = Sparse.eval nodeValue2247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2247) = mixedMoment B node2247 node2247Labels := rfl
  simpa [nodeValue2247, Sparse.eval] using hc.symm

theorem sound2287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2287 node2287Labels = Sparse.eval nodeValue2287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2287) = mixedMoment B node2287 node2287Labels := rfl
  simpa [nodeValue2287, Sparse.eval] using hc.symm

theorem sound2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2290 node2290Labels = Sparse.eval nodeValue2290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2290) = mixedMoment B node2290 node2290Labels := rfl
  simpa [nodeValue2290, Sparse.eval] using hc.symm

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

theorem sound2739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2739 node2739Labels = Sparse.eval nodeValue2739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2739) = mixedMoment B node2739 node2739Labels := rfl
  simpa [nodeValue2739, Sparse.eval] using hc.symm

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

theorem sound3534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3534 node3534Labels = Sparse.eval nodeValue3534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3534) = mixedMoment B node3534 node3534Labels := rfl
  simpa [nodeValue3534, Sparse.eval] using hc.symm

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

theorem sound4327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4327 node4327Labels = Sparse.eval nodeValue4327 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4327) = mixedMoment B node4327 node4327Labels := rfl
  simpa [nodeValue4327, Sparse.eval] using hc.symm

theorem sound4331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4331 node4331Labels = Sparse.eval nodeValue4331 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4331) = mixedMoment B node4331 node4331Labels := rfl
  simpa [nodeValue4331, Sparse.eval] using hc.symm

theorem sound4333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4333 node4333Labels = Sparse.eval nodeValue4333 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4333) = mixedMoment B node4333 node4333Labels := rfl
  simpa [nodeValue4333, Sparse.eval] using hc.symm

theorem sound4335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4335 node4335Labels = Sparse.eval nodeValue4335 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4335) = mixedMoment B node4335 node4335Labels := rfl
  simpa [nodeValue4335, Sparse.eval] using hc.symm

theorem sound4336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4336 node4336Labels = Sparse.eval nodeValue4336 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4336) = mixedMoment B node4336 node4336Labels := rfl
  simpa [nodeValue4336, Sparse.eval] using hc.symm

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

theorem sound4353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4353 node4353Labels = Sparse.eval nodeValue4353 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4353) = mixedMoment B node4353 node4353Labels := rfl
  simpa [nodeValue4353, Sparse.eval] using hc.symm

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

theorem sound4442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4442 node4442Labels = Sparse.eval nodeValue4442 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4442) = mixedMoment B node4442 node4442Labels := rfl
  simpa [nodeValue4442, Sparse.eval] using hc.symm

theorem sound4463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4463 node4463Labels = Sparse.eval nodeValue4463 (mixedVector B) := by
  have h := singleton4463 B _hB
  rw [sound1046 B _hB _hF, sound1750 B _hB _hF] at h
  norm_num [nodeValue4463, nodeValue1046, nodeValue1750, Sparse.eval] at h ⊢
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

theorem sound4664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4664 node4664Labels = Sparse.eval nodeValue4664 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4664) = mixedMoment B node4664 node4664Labels := rfl
  simpa [nodeValue4664, Sparse.eval] using hc.symm

theorem sound4670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4670 node4670Labels = Sparse.eval nodeValue4670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4670) = mixedMoment B node4670 node4670Labels := rfl
  simpa [nodeValue4670, Sparse.eval] using hc.symm

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

theorem sound4686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4686 node4686Labels = Sparse.eval nodeValue4686 (mixedVector B) := by
  have h := singleton4686 B _hB
  rw [sound1812 B _hB _hF, sound2165 B _hB _hF] at h
  norm_num [nodeValue4686, nodeValue1812, nodeValue2165, Sparse.eval] at h ⊢
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

theorem sound4757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4757 node4757Labels = Sparse.eval nodeValue4757 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4757) = mixedMoment B node4757 node4757Labels := rfl
  simpa [nodeValue4757, Sparse.eval] using hc.symm

theorem sound4764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4764 node4764Labels = Sparse.eval nodeValue4764 (mixedVector B) := by
  have h := singleton4764 B _hB
  rw [sound1964 B _hB _hF, sound2182 B _hB _hF] at h
  norm_num [nodeValue4764, nodeValue1964, nodeValue2182, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4772 node4772Labels = Sparse.eval nodeValue4772 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4772) = mixedMoment B node4772 node4772Labels := rfl
  simpa [nodeValue4772, Sparse.eval] using hc.symm

theorem sound4777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4777 node4777Labels = Sparse.eval nodeValue4777 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4777) = mixedMoment B node4777 node4777Labels := rfl
  simpa [nodeValue4777, Sparse.eval] using hc.symm

theorem sound4792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4792 node4792Labels = Sparse.eval nodeValue4792 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4792) = mixedMoment B node4792 node4792Labels := rfl
  simpa [nodeValue4792, Sparse.eval] using hc.symm

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

theorem sound4802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4802 node4802Labels = Sparse.eval nodeValue4802 (mixedVector B) := by
  have h := singleton4802 B _hB
  rw [sound2020 B _hB _hF, sound2202 B _hB _hF] at h
  norm_num [nodeValue4802, nodeValue2020, nodeValue2202, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4807 node4807Labels = Sparse.eval nodeValue4807 (mixedVector B) := by
  have h := singleton4807 B _hB
  rw [sound2025 B _hB _hF, sound2224 B _hB _hF] at h
  norm_num [nodeValue4807, nodeValue2025, nodeValue2224, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4811 node4811Labels = Sparse.eval nodeValue4811 (mixedVector B) := by
  have h := singleton4811 B _hB
  rw [sound2029 B _hB _hF, sound2225 B _hB _hF] at h
  norm_num [nodeValue4811, nodeValue2029, nodeValue2225, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4871 node4871Labels = Sparse.eval nodeValue4871 (mixedVector B) := by
  have h := singleton4871 B _hB
  rw [sound2112 B _hB _hF, sound2287 B _hB _hF] at h
  norm_num [nodeValue4871, nodeValue2112, nodeValue2287, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4890 node4890Labels = Sparse.eval nodeValue4890 (mixedVector B) := by
  have h := singleton4890 B _hB
  rw [sound2247 B _hB _hF, sound2290 B _hB _hF] at h
  norm_num [nodeValue4890, nodeValue2247, nodeValue2290, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4895 node4895Labels = Sparse.eval nodeValue4895 (mixedVector B) := by
  simpa only [nodeValue4895, Sparse.eval_nil] using zero4895 B _hB _hF

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

theorem sound5150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5150 node5150Labels = Sparse.eval nodeValue5150 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5150) = mixedMoment B node5150 node5150Labels := rfl
  simpa [nodeValue5150, Sparse.eval] using hc.symm

theorem sound5151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5151 node5151Labels = Sparse.eval nodeValue5151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5151) = mixedMoment B node5151 node5151Labels := rfl
  simpa [nodeValue5151, Sparse.eval] using hc.symm

theorem sound5173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5173 node5173Labels = Sparse.eval nodeValue5173 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5173) = mixedMoment B node5173 node5173Labels := rfl
  simpa [nodeValue5173, Sparse.eval] using hc.symm

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

theorem sound5270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5270 node5270Labels = Sparse.eval nodeValue5270 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5270) = mixedMoment B node5270 node5270Labels := rfl
  simpa [nodeValue5270, Sparse.eval] using hc.symm

theorem sound5271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5271 node5271Labels = Sparse.eval nodeValue5271 (mixedVector B) := by
  have h := singleton5271 B _hB
  rw [sound2739 B _hB _hF, sound3534 B _hB _hF] at h
  norm_num [nodeValue5271, nodeValue2739, nodeValue3534, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources61
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1973 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1973 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1973 + difference 0 1) (sourceB1973 + difference 1 0) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA1973 + difference 0 1) (sourceB1973 + difference 1 0) sourceC1973) = raw28020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28020; decide +kernel
    rw [ha]
    exact (canonical28020 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1973 + difference 0 2) (sourceB1973 + difference 2 0) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA1973 + difference 0 2) (sourceB1973 + difference 2 0) sourceC1973) = raw28021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28021; decide +kernel
    rw [ha]
    exact (canonical28021 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1973 + difference 0 3) (sourceB1973 + difference 3 0) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA1973 + difference 0 3) (sourceB1973 + difference 3 0) sourceC1973) = raw28022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28022; decide +kernel
    rw [ha]
    exact (canonical28022 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1973 + difference 0 4) (sourceB1973 + difference 4 0) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1973 + difference 0 4) (sourceB1973 + difference 4 0) sourceC1973) = raw28023 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28023; decide +kernel
    rw [ha]
    exact (canonical28023 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1973 + difference 0 5) (sourceB1973 + difference 5 0) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA1973 + difference 0 5) (sourceB1973 + difference 5 0) sourceC1973) = raw28024 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28024; decide +kernel
    rw [ha]
    exact (canonical28024 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1973 + difference 1 0) (sourceB1973 + difference 0 1) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4442) := by
    have ha : (tripleCharges (sourceA1973 + difference 1 0) (sourceB1973 + difference 0 1) sourceC1973) = raw28025 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28025; decide +kernel
    rw [ha]
    exact (canonical28025 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1973 + difference 1 2) (sourceB1973 + difference 2 1) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4792) := by
    have ha : (tripleCharges (sourceA1973 + difference 1 2) (sourceB1973 + difference 2 1) sourceC1973) = raw28026 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28026; decide +kernel
    rw [ha]
    exact (canonical28026 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1973 + difference 1 3) (sourceB1973 + difference 3 1) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1973 + difference 1 3) (sourceB1973 + difference 3 1) sourceC1973) = raw28027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28027; decide +kernel
    rw [ha]
    exact (canonical28027 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1973 + difference 1 4) (sourceB1973 + difference 4 1) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA1973 + difference 1 4) (sourceB1973 + difference 4 1) sourceC1973) = raw28028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28028; decide +kernel
    rw [ha]
    exact (canonical28028 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1973 + difference 1 5) (sourceB1973 + difference 5 1) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA1973 + difference 1 5) (sourceB1973 + difference 5 1) sourceC1973) = raw28029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28029; decide +kernel
    rw [ha]
    exact (canonical28029 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1973 + difference 2 0) (sourceB1973 + difference 0 2) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4331) := by
    have ha : (tripleCharges (sourceA1973 + difference 2 0) (sourceB1973 + difference 0 2) sourceC1973) = raw28030 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28030; decide +kernel
    rw [ha]
    exact (canonical28030 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1973 + difference 2 1) (sourceB1973 + difference 1 2) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4757) := by
    have ha : (tripleCharges (sourceA1973 + difference 2 1) (sourceB1973 + difference 1 2) sourceC1973) = raw28031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28031; decide +kernel
    rw [ha]
    exact (canonical28031 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1973 + difference 2 3) (sourceB1973 + difference 3 2) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4764) := by
    have ha : (tripleCharges (sourceA1973 + difference 2 3) (sourceB1973 + difference 3 2) sourceC1973) = raw28032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28032; decide +kernel
    rw [ha]
    exact (canonical28032 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1973 + difference 2 4) (sourceB1973 + difference 4 2) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1973 + difference 2 4) (sourceB1973 + difference 4 2) sourceC1973) = raw28033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28033; decide +kernel
    rw [ha]
    exact (canonical28033 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1973 + difference 2 5) (sourceB1973 + difference 5 2) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5150) := by
    have ha : (tripleCharges (sourceA1973 + difference 2 5) (sourceB1973 + difference 5 2) sourceC1973) = raw28034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28034; decide +kernel
    rw [ha]
    exact (canonical28034 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1973 + difference 3 0) (sourceB1973 + difference 0 3) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4353) := by
    have ha : (tripleCharges (sourceA1973 + difference 3 0) (sourceB1973 + difference 0 3) sourceC1973) = raw28035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28035; decide +kernel
    rw [ha]
    exact (canonical28035 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1973 + difference 3 1) (sourceB1973 + difference 1 3) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4777) := by
    have ha : (tripleCharges (sourceA1973 + difference 3 1) (sourceB1973 + difference 1 3) sourceC1973) = raw28036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28036; decide +kernel
    rw [ha]
    exact (canonical28036 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1973 + difference 3 2) (sourceB1973 + difference 2 3) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4772) := by
    have ha : (tripleCharges (sourceA1973 + difference 3 2) (sourceB1973 + difference 2 3) sourceC1973) = raw28037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28037; decide +kernel
    rw [ha]
    exact (canonical28037 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1973 + difference 3 4) (sourceB1973 + difference 4 3) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA1973 + difference 3 4) (sourceB1973 + difference 4 3) sourceC1973) = raw28038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28038; decide +kernel
    rw [ha]
    exact (canonical28038 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1973 + difference 3 5) (sourceB1973 + difference 5 3) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA1973 + difference 3 5) (sourceB1973 + difference 5 3) sourceC1973) = raw28039 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28039; decide +kernel
    rw [ha]
    exact (canonical28039 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1973 + difference 4 0) (sourceB1973 + difference 0 4) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4336) := by
    have ha : (tripleCharges (sourceA1973 + difference 4 0) (sourceB1973 + difference 0 4) sourceC1973) = raw28040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28040; decide +kernel
    rw [ha]
    exact (canonical28040 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1973 + difference 4 1) (sourceB1973 + difference 1 4) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4670) := by
    have ha : (tripleCharges (sourceA1973 + difference 4 1) (sourceB1973 + difference 1 4) sourceC1973) = raw28041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28041; decide +kernel
    rw [ha]
    exact (canonical28041 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1973 + difference 4 2) (sourceB1973 + difference 2 4) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4664) := by
    have ha : (tripleCharges (sourceA1973 + difference 4 2) (sourceB1973 + difference 2 4) sourceC1973) = raw28042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28042; decide +kernel
    rw [ha]
    exact (canonical28042 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1973 + difference 4 3) (sourceB1973 + difference 3 4) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4686) := by
    have ha : (tripleCharges (sourceA1973 + difference 4 3) (sourceB1973 + difference 3 4) sourceC1973) = raw28043 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28043; decide +kernel
    rw [ha]
    exact (canonical28043 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1973 + difference 4 5) (sourceB1973 + difference 5 4) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA1973 + difference 4 5) (sourceB1973 + difference 5 4) sourceC1973) = raw28044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28044; decide +kernel
    rw [ha]
    exact (canonical28044 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1973 + difference 5 0) (sourceB1973 + difference 0 5) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4333) := by
    have ha : (tripleCharges (sourceA1973 + difference 5 0) (sourceB1973 + difference 0 5) sourceC1973) = raw28045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28045; decide +kernel
    rw [ha]
    exact (canonical28045 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1973 + difference 5 1) (sourceB1973 + difference 1 5) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA1973 + difference 5 1) (sourceB1973 + difference 1 5) sourceC1973) = raw28046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28046; decide +kernel
    rw [ha]
    exact (canonical28046 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1973 + difference 5 2) (sourceB1973 + difference 2 5) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4327) := by
    have ha : (tripleCharges (sourceA1973 + difference 5 2) (sourceB1973 + difference 2 5) sourceC1973) = raw28047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28047; decide +kernel
    rw [ha]
    exact (canonical28047 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1973 + difference 5 3) (sourceB1973 + difference 3 5) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4352) := by
    have ha : (tripleCharges (sourceA1973 + difference 5 3) (sourceB1973 + difference 3 5) sourceC1973) = raw28048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28048; decide +kernel
    rw [ha]
    exact (canonical28048 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1973 + difference 5 4) (sourceB1973 + difference 4 5) sourceC1973) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1973 + difference 5 4) (sourceB1973 + difference 4 5) sourceC1973) = raw28049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1973 sourceB1973 sourceC1973 difference raw28049; decide +kernel
    rw [ha]
    exact (canonical28049 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1973 sourceB1973 sourceC1973
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1973, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1673 : Integer.Sparse.reindex keyMap MixedData.row1673 = numericRow1673 := by decide +kernel

theorem numericCheck1673 (x : Master → ℝ) : Integer.Sparse.eval numericRow1673 x =
    (4 : ℝ) * reducedSource1673 x := by
  norm_num [numericRow1673, reducedSource1673, Integer.Sparse.eval, Sparse.eval, nodeValue4327, nodeValue4331, nodeValue4333, nodeValue4335, nodeValue4336, nodeValue4352, nodeValue4353, nodeValue4442, nodeValue4463, nodeValue4664, nodeValue4670, nodeValue4686, nodeValue4757, nodeValue4764, nodeValue4772, nodeValue4777, nodeValue4792, nodeValue4802, nodeValue4807, nodeValue4811, nodeValue4838, nodeValue4871, nodeValue4890, nodeValue4895, nodeValue5150, nodeValue5151, nodeValue5173, nodeValue5270, nodeValue5271]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1673 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1673 (mixedVector B) = 0 := by
  have h4327 : mixedVector B (Sum.inr 4327) = Sparse.eval nodeValue4327 (mixedVector B) := by
    change mixedMoment B node4327 node4327Labels = _
    exact sound4327 B hB hF
  have h4331 : mixedVector B (Sum.inr 4331) = Sparse.eval nodeValue4331 (mixedVector B) := by
    change mixedMoment B node4331 node4331Labels = _
    exact sound4331 B hB hF
  have h4333 : mixedVector B (Sum.inr 4333) = Sparse.eval nodeValue4333 (mixedVector B) := by
    change mixedMoment B node4333 node4333Labels = _
    exact sound4333 B hB hF
  have h4335 : mixedVector B (Sum.inr 4335) = Sparse.eval nodeValue4335 (mixedVector B) := by
    change mixedMoment B node4335 node4335Labels = _
    exact sound4335 B hB hF
  have h4336 : mixedVector B (Sum.inr 4336) = Sparse.eval nodeValue4336 (mixedVector B) := by
    change mixedMoment B node4336 node4336Labels = _
    exact sound4336 B hB hF
  have h4352 : mixedVector B (Sum.inr 4352) = Sparse.eval nodeValue4352 (mixedVector B) := by
    change mixedMoment B node4352 node4352Labels = _
    exact sound4352 B hB hF
  have h4353 : mixedVector B (Sum.inr 4353) = Sparse.eval nodeValue4353 (mixedVector B) := by
    change mixedMoment B node4353 node4353Labels = _
    exact sound4353 B hB hF
  have h4442 : mixedVector B (Sum.inr 4442) = Sparse.eval nodeValue4442 (mixedVector B) := by
    change mixedMoment B node4442 node4442Labels = _
    exact sound4442 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4664 : mixedVector B (Sum.inr 4664) = Sparse.eval nodeValue4664 (mixedVector B) := by
    change mixedMoment B node4664 node4664Labels = _
    exact sound4664 B hB hF
  have h4670 : mixedVector B (Sum.inr 4670) = Sparse.eval nodeValue4670 (mixedVector B) := by
    change mixedMoment B node4670 node4670Labels = _
    exact sound4670 B hB hF
  have h4686 : mixedVector B (Sum.inr 4686) = Sparse.eval nodeValue4686 (mixedVector B) := by
    change mixedMoment B node4686 node4686Labels = _
    exact sound4686 B hB hF
  have h4757 : mixedVector B (Sum.inr 4757) = Sparse.eval nodeValue4757 (mixedVector B) := by
    change mixedMoment B node4757 node4757Labels = _
    exact sound4757 B hB hF
  have h4764 : mixedVector B (Sum.inr 4764) = Sparse.eval nodeValue4764 (mixedVector B) := by
    change mixedMoment B node4764 node4764Labels = _
    exact sound4764 B hB hF
  have h4772 : mixedVector B (Sum.inr 4772) = Sparse.eval nodeValue4772 (mixedVector B) := by
    change mixedMoment B node4772 node4772Labels = _
    exact sound4772 B hB hF
  have h4777 : mixedVector B (Sum.inr 4777) = Sparse.eval nodeValue4777 (mixedVector B) := by
    change mixedMoment B node4777 node4777Labels = _
    exact sound4777 B hB hF
  have h4792 : mixedVector B (Sum.inr 4792) = Sparse.eval nodeValue4792 (mixedVector B) := by
    change mixedMoment B node4792 node4792Labels = _
    exact sound4792 B hB hF
  have h4802 : mixedVector B (Sum.inr 4802) = Sparse.eval nodeValue4802 (mixedVector B) := by
    change mixedMoment B node4802 node4802Labels = _
    exact sound4802 B hB hF
  have h4807 : mixedVector B (Sum.inr 4807) = Sparse.eval nodeValue4807 (mixedVector B) := by
    change mixedMoment B node4807 node4807Labels = _
    exact sound4807 B hB hF
  have h4811 : mixedVector B (Sum.inr 4811) = Sparse.eval nodeValue4811 (mixedVector B) := by
    change mixedMoment B node4811 node4811Labels = _
    exact sound4811 B hB hF
  have h4838 : mixedVector B (Sum.inr 4838) = Sparse.eval nodeValue4838 (mixedVector B) := by
    change mixedMoment B node4838 node4838Labels = _
    exact sound4838 B hB hF
  have h4871 : mixedVector B (Sum.inr 4871) = Sparse.eval nodeValue4871 (mixedVector B) := by
    change mixedMoment B node4871 node4871Labels = _
    exact sound4871 B hB hF
  have h4890 : mixedVector B (Sum.inr 4890) = Sparse.eval nodeValue4890 (mixedVector B) := by
    change mixedMoment B node4890 node4890Labels = _
    exact sound4890 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  have h5150 : mixedVector B (Sum.inr 5150) = Sparse.eval nodeValue5150 (mixedVector B) := by
    change mixedMoment B node5150 node5150Labels = _
    exact sound5150 B hB hF
  have h5151 : mixedVector B (Sum.inr 5151) = Sparse.eval nodeValue5151 (mixedVector B) := by
    change mixedMoment B node5151 node5151Labels = _
    exact sound5151 B hB hF
  have h5173 : mixedVector B (Sum.inr 5173) = Sparse.eval nodeValue5173 (mixedVector B) := by
    change mixedMoment B node5173 node5173Labels = _
    exact sound5173 B hB hF
  have h5270 : mixedVector B (Sum.inr 5270) = Sparse.eval nodeValue5270 (mixedVector B) := by
    change mixedMoment B node5270 node5270Labels = _
    exact sound5270 B hB hF
  have h5271 : mixedVector B (Sum.inr 5271) = Sparse.eval nodeValue5271 (mixedVector B) := by
    change mixedMoment B node5271 node5271Labels = _
    exact sound5271 B hB hF
  simpa only [sourceForm1973, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4327, h4331, h4333, h4335, h4336, h4352, h4353, h4442, h4463, h4664, h4670, h4686, h4757, h4764, h4772, h4777, h4792, h4802, h4807, h4811, h4838, h4871, h4890, h4895, h5150, h5151, h5173, h5270, h5271, reducedSource1673] using sourceEq1973 B hB

theorem rowSound1673_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1673 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1673, numericCheck1673, reducedZero1673 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673_e_oai
