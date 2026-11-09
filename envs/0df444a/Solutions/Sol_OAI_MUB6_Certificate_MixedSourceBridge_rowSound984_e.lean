-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound984_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:13:51.978042+00:00
-- url     : https://prove2.me/submissions/a9ee7f40-5780-44c8-be71-22837565894a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E129
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5433_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5485_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedAlpha
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

theorem rowFourier_alpha_zero {H : CMatrix} (hH : FourierZero H)
    (ρ : Coord ↪ Coord) (σ : Equiv.Perm Coord) :
    rowFourier H ρ (permuteCharge σ alpha) = 0 := by
  rw [permuteCharge, rowFourier_row_permutation]
  let e : Coord ↪ Coord := Equiv.embeddingCongr σ (Equiv.refl Coord) ρ
  let π : Equiv.Perm Coord := Equiv.ofBijective e
    ⟨e.injective, Finite.surjective_of_injective e.injective⟩
  exact hH π

theorem mixedMoment_alpha {n l : ℕ} (B : Fin 7 → Basis) (hB : AllTransitionsFourierZero B)
    (A : Matrix Coord (Fin n) ℤ) (label : Fin n → Fin l) (j : Fin n)
    (σ : Equiv.Perm Coord) (hA : (fun i => A i j) = permuteCharge σ alpha) :
    mixedMoment B A label = 0 := by
  have h (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B A label r ρ τ = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [hA]
    exact rowFourier_alpha_zero (hB r _) ρ σ
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13674 raw13674Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw13674 raw13674Labels = mixedMoment B raw13674step0 raw13674step0Labels := by
      have ha : raw13674step0 = (fun i j => raw13674 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13674step0 raw13674; decide +kernel
      have hl : raw13674step0Labels = raw13674Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13674 raw13674Labels permutation180 permutation2
    _ = mixedMoment B node5408 node5408Labels := by rfl

theorem canonical13675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13675 raw13675Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw13675 raw13675Labels = mixedMoment B raw13675step0 raw13675step0Labels := by
      have ha : raw13675step0 = (fun i j => raw13675 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13675step0 raw13675; decide +kernel
      have hl : raw13675step0Labels = raw13675Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13675 raw13675Labels permutation194 permutation7
    mixedMoment B raw13675step0 raw13675step0Labels = mixedMoment B raw13675step1 raw13675step1Labels := by
      have ha : raw13675step1 = -raw13675step0 := by apply Matrix.ext; change ∀ i j, raw13675step1 i j = -(raw13675step0 i j); unfold raw13675step1 raw13675step0; decide +kernel
      have hl : raw13675step1Labels = raw13675step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13675step1 raw13675step1Labels = mixedMoment B raw13675step2 raw13675step2Labels := by
      have ha : raw13675step2 = raw13675step1 := by apply Matrix.ext; unfold raw13675step2 raw13675step1; decide +kernel
      have hl : raw13675step1Labels = labelEmbedding10 ∘ raw13675step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13675step1 raw13675step1Labels raw13675step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical13676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13676 raw13676Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw13676 raw13676Labels = mixedMoment B raw13676step0 raw13676step0Labels := by
      have ha : raw13676step0 = (fun i j => raw13676 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13676step0 raw13676; decide +kernel
      have hl : raw13676step0Labels = raw13676Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13676 raw13676Labels permutation195 permutation7
    mixedMoment B raw13676step0 raw13676step0Labels = mixedMoment B raw13676step1 raw13676step1Labels := by
      have ha : raw13676step1 = -raw13676step0 := by apply Matrix.ext; change ∀ i j, raw13676step1 i j = -(raw13676step0 i j); unfold raw13676step1 raw13676step0; decide +kernel
      have hl : raw13676step1Labels = raw13676step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13676step1 raw13676step1Labels = mixedMoment B raw13676step2 raw13676step2Labels := by
      have ha : raw13676step2 = raw13676step1 := by apply Matrix.ext; unfold raw13676step2 raw13676step1; decide +kernel
      have hl : raw13676step1Labels = labelEmbedding10 ∘ raw13676step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13676step1 raw13676step1Labels raw13676step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical13677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13677 raw13677Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw13677 raw13677Labels = mixedMoment B raw13677step0 raw13677step0Labels := by
      have hz : ∀ j, raw13677 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13677step0 = (fun i j => raw13677 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13677step0 raw13677; decide +kernel
      have hl : raw13677step0Labels = raw13677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13677 raw13677Labels permutation590 hz
    mixedMoment B raw13677step0 raw13677step0Labels = mixedMoment B raw13677step1 raw13677step1Labels := by
      have ha : raw13677step1 = (fun i j => raw13677step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13677step1 raw13677step0; decide +kernel
      have hl : raw13677step1Labels = raw13677step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13677step0 raw13677step0Labels permutation38 permutation7
    mixedMoment B raw13677step1 raw13677step1Labels = mixedMoment B raw13677step2 raw13677step2Labels := by
      have ha : raw13677step2 = -raw13677step1 := by apply Matrix.ext; change ∀ i j, raw13677step2 i j = -(raw13677step1 i j); unfold raw13677step2 raw13677step1; decide +kernel
      have hl : raw13677step2Labels = raw13677step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13677step2 raw13677step2Labels = mixedMoment B raw13677step3 raw13677step3Labels := by
      have ha : raw13677step3 = raw13677step2 := by apply Matrix.ext; unfold raw13677step3 raw13677step2; decide +kernel
      have hl : raw13677step2Labels = labelEmbedding10 ∘ raw13677step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13677step2 raw13677step2Labels raw13677step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

theorem canonical13684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13684 raw13684Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw13684 raw13684Labels = mixedMoment B raw13684step0 raw13684step0Labels := by
      have ha : raw13684step0 = (fun i j => raw13684 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13684step0 raw13684; decide +kernel
      have hl : raw13684step0Labels = raw13684Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13684 raw13684Labels permutation156 permutation2
    _ = mixedMoment B node5197 node5197Labels := by rfl

theorem canonical13689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13689 raw13689Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw13689 raw13689Labels = mixedMoment B raw13689step0 raw13689step0Labels := by
      have ha : raw13689step0 = (fun i j => raw13689 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13689step0 raw13689; decide +kernel
      have hl : raw13689step0Labels = raw13689Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13689 raw13689Labels permutation157 permutation2
    _ = mixedMoment B node5185 node5185Labels := by rfl

theorem canonical13694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13694 raw13694Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw13694 raw13694Labels = mixedMoment B raw13694step0 raw13694step0Labels := by
      have ha : raw13694step0 = (fun i j => raw13694 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13694step0 raw13694; decide +kernel
      have hl : raw13694step0Labels = raw13694Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13694 raw13694Labels permutation156 permutation2
    _ = mixedMoment B node5185 node5185Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13699 raw13699Labels = mixedMoment B node5187 node5187Labels := by
  calc
    _ = mixedMoment B node5187 node5187Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical149
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19196 raw19196Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw19196 raw19196Labels = mixedMoment B raw19196step0 raw19196step0Labels := by
      have ha : raw19196step0 = (fun i j => raw19196 (permutation313 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19196step0 raw19196; decide +kernel
      have hl : raw19196step0Labels = raw19196Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19196 raw19196Labels permutation313 permutation5
    mixedMoment B raw19196step0 raw19196step0Labels = mixedMoment B raw19196step1 raw19196step1Labels := by
      have ha : raw19196step1 = -raw19196step0 := by apply Matrix.ext; change ∀ i j, raw19196step1 i j = -(raw19196step0 i j); unfold raw19196step1 raw19196step0; decide +kernel
      have hl : raw19196step1Labels = raw19196step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19196step1 raw19196step1Labels = mixedMoment B raw19196step2 raw19196step2Labels := by
      have ha : raw19196step2 = raw19196step1 := by apply Matrix.ext; unfold raw19196step2 raw19196step1; decide +kernel
      have hl : raw19196step1Labels = labelEmbedding8 ∘ raw19196step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19196step1 raw19196step1Labels raw19196step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical19197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19197 raw19197Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw19197 raw19197Labels = mixedMoment B raw19197step0 raw19197step0Labels := by
      have ha : raw19197step0 = (fun i j => raw19197 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19197step0 raw19197; decide +kernel
      have hl : raw19197step0Labels = raw19197Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19197 raw19197Labels permutation194 permutation7
    mixedMoment B raw19197step0 raw19197step0Labels = mixedMoment B raw19197step1 raw19197step1Labels := by
      have ha : raw19197step1 = -raw19197step0 := by apply Matrix.ext; change ∀ i j, raw19197step1 i j = -(raw19197step0 i j); unfold raw19197step1 raw19197step0; decide +kernel
      have hl : raw19197step1Labels = raw19197step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19197step1 raw19197step1Labels = mixedMoment B raw19197step2 raw19197step2Labels := by
      have ha : raw19197step2 = raw19197step1 := by apply Matrix.ext; unfold raw19197step2 raw19197step1; decide +kernel
      have hl : raw19197step1Labels = labelEmbedding10 ∘ raw19197step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19197step1 raw19197step1Labels raw19197step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

theorem canonical19198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19198 raw19198Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw19198 raw19198Labels = mixedMoment B raw19198step0 raw19198step0Labels := by
      have ha : raw19198step0 = (fun i j => raw19198 (permutation317 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19198step0 raw19198; decide +kernel
      have hl : raw19198step0Labels = raw19198Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19198 raw19198Labels permutation317 permutation4
    mixedMoment B raw19198step0 raw19198step0Labels = mixedMoment B raw19198step1 raw19198step1Labels := by
      have ha : raw19198step1 = -raw19198step0 := by apply Matrix.ext; change ∀ i j, raw19198step1 i j = -(raw19198step0 i j); unfold raw19198step1 raw19198step0; decide +kernel
      have hl : raw19198step1Labels = raw19198step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19198step1 raw19198step1Labels = mixedMoment B raw19198step2 raw19198step2Labels := by
      have ha : raw19198step2 = raw19198step1 := by apply Matrix.ext; unfold raw19198step2 raw19198step1; decide +kernel
      have hl : raw19198step1Labels = labelEmbedding7 ∘ raw19198step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19198step1 raw19198step1Labels raw19198step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical19199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19199 raw19199Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw19199 raw19199Labels = mixedMoment B raw19199step0 raw19199step0Labels := by
      have ha : raw19199step0 = (fun i j => raw19199 (permutation328 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19199step0 raw19199; decide +kernel
      have hl : raw19199step0Labels = raw19199Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19199 raw19199Labels permutation328 permutation4
    mixedMoment B raw19199step0 raw19199step0Labels = mixedMoment B raw19199step1 raw19199step1Labels := by
      have ha : raw19199step1 = -raw19199step0 := by apply Matrix.ext; change ∀ i j, raw19199step1 i j = -(raw19199step0 i j); unfold raw19199step1 raw19199step0; decide +kernel
      have hl : raw19199step1Labels = raw19199step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19199step1 raw19199step1Labels = mixedMoment B raw19199step2 raw19199step2Labels := by
      have ha : raw19199step2 = raw19199step1 := by apply Matrix.ext; unfold raw19199step2 raw19199step1; decide +kernel
      have hl : raw19199step1Labels = labelEmbedding7 ∘ raw19199step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19199step1 raw19199step1Labels raw19199step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical150
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19200 raw19200Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw19200 raw19200Labels = mixedMoment B raw19200step0 raw19200step0Labels := by
      have hz : ∀ j, raw19200 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19200step0 = (fun i j => raw19200 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19200step0 raw19200; decide +kernel
      have hl : raw19200step0Labels = raw19200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19200 raw19200Labels permutation590 hz
    mixedMoment B raw19200step0 raw19200step0Labels = mixedMoment B raw19200step1 raw19200step1Labels := by
      have ha : raw19200step1 = (fun i j => raw19200step0 (permutation41 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19200step1 raw19200step0; decide +kernel
      have hl : raw19200step1Labels = raw19200step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19200step0 raw19200step0Labels permutation41 permutation6
    mixedMoment B raw19200step1 raw19200step1Labels = mixedMoment B raw19200step2 raw19200step2Labels := by
      have ha : raw19200step2 = -raw19200step1 := by apply Matrix.ext; change ∀ i j, raw19200step2 i j = -(raw19200step1 i j); unfold raw19200step2 raw19200step1; decide +kernel
      have hl : raw19200step2Labels = raw19200step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19200step2 raw19200step2Labels = mixedMoment B raw19200step3 raw19200step3Labels := by
      have ha : raw19200step3 = raw19200step2 := by apply Matrix.ext; unfold raw19200step3 raw19200step2; decide +kernel
      have hl : raw19200step2Labels = labelEmbedding9 ∘ raw19200step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19200step2 raw19200step2Labels raw19200step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

theorem canonical19201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19201 raw19201Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw19201 raw19201Labels = mixedMoment B raw19201step0 raw19201step0Labels := by
      have ha : raw19201step0 = (fun i j => raw19201 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19201step0 raw19201; decide +kernel
      have hl : raw19201step0Labels = raw19201Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19201 raw19201Labels permutation180 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

theorem canonical19202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19202 raw19202Labels = mixedMoment B node5220 node5220Labels := by
  calc
    mixedMoment B raw19202 raw19202Labels = mixedMoment B raw19202step0 raw19202step0Labels := by
      have ha : raw19202step0 = (fun i j => raw19202 (permutation274 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19202step0 raw19202; decide +kernel
      have hl : raw19202step0Labels = raw19202Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19202 raw19202Labels permutation274 permutation5
    mixedMoment B raw19202step0 raw19202step0Labels = mixedMoment B raw19202step1 raw19202step1Labels := by
      have ha : raw19202step1 = -raw19202step0 := by apply Matrix.ext; change ∀ i j, raw19202step1 i j = -(raw19202step0 i j); unfold raw19202step1 raw19202step0; decide +kernel
      have hl : raw19202step1Labels = raw19202step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19202step1 raw19202step1Labels = mixedMoment B raw19202step2 raw19202step2Labels := by
      have ha : raw19202step2 = raw19202step1 := by apply Matrix.ext; unfold raw19202step2 raw19202step1; decide +kernel
      have hl : raw19202step1Labels = labelEmbedding8 ∘ raw19202step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19202step1 raw19202step1Labels raw19202step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5220 node5220Labels := by rfl

theorem canonical19203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19203 raw19203Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw19203 raw19203Labels = mixedMoment B raw19203step0 raw19203step0Labels := by
      have ha : raw19203step0 = (fun i j => raw19203 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19203step0 raw19203; decide +kernel
      have hl : raw19203step0Labels = raw19203Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19203 raw19203Labels permutation159 permutation2
    _ = mixedMoment B node5445 node5445Labels := by rfl

theorem canonical19204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19204 raw19204Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw19204 raw19204Labels = mixedMoment B raw19204step0 raw19204step0Labels := by
      have ha : raw19204step0 = (fun i j => raw19204 (permutation165 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19204step0 raw19204; decide +kernel
      have hl : raw19204step0Labels = raw19204Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19204 raw19204Labels permutation165 permutation2
    _ = mixedMoment B node5445 node5445Labels := by rfl

theorem canonical19205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19205 raw19205Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw19205 raw19205Labels = mixedMoment B raw19205step0 raw19205step0Labels := by
      have hz : ∀ j, raw19205 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19205step0 = (fun i j => raw19205 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19205step0 raw19205; decide +kernel
      have hl : raw19205step0Labels = raw19205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19205 raw19205Labels permutation590 hz
    _ = mixedMoment B node5448 node5448Labels := by rfl

theorem canonical19206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19206 raw19206Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw19206 raw19206Labels = mixedMoment B raw19206step0 raw19206step0Labels := by
      have ha : raw19206step0 = (fun i j => raw19206 (permutation278 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19206step0 raw19206; decide +kernel
      have hl : raw19206step0Labels = raw19206Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19206 raw19206Labels permutation278 permutation5
    mixedMoment B raw19206step0 raw19206step0Labels = mixedMoment B raw19206step1 raw19206step1Labels := by
      have ha : raw19206step1 = -raw19206step0 := by apply Matrix.ext; change ∀ i j, raw19206step1 i j = -(raw19206step0 i j); unfold raw19206step1 raw19206step0; decide +kernel
      have hl : raw19206step1Labels = raw19206step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19206step1 raw19206step1Labels = mixedMoment B raw19206step2 raw19206step2Labels := by
      have ha : raw19206step2 = raw19206step1 := by apply Matrix.ext; unfold raw19206step2 raw19206step1; decide +kernel
      have hl : raw19206step1Labels = labelEmbedding8 ∘ raw19206step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19206step1 raw19206step1Labels raw19206step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

theorem canonical19207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19207 raw19207Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw19207 raw19207Labels = mixedMoment B raw19207step0 raw19207step0Labels := by
      have ha : raw19207step0 = (fun i j => raw19207 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19207step0 raw19207; decide +kernel
      have hl : raw19207step0Labels = raw19207Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19207 raw19207Labels permutation181 permutation2
    _ = mixedMoment B node5401 node5401Labels := by rfl

theorem canonical19208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19208 raw19208Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw19208 raw19208Labels = mixedMoment B raw19208step0 raw19208step0Labels := by
      have ha : raw19208step0 = (fun i j => raw19208 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19208step0 raw19208; decide +kernel
      have hl : raw19208step0Labels = raw19208Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19208 raw19208Labels permutation195 permutation7
    mixedMoment B raw19208step0 raw19208step0Labels = mixedMoment B raw19208step1 raw19208step1Labels := by
      have ha : raw19208step1 = -raw19208step0 := by apply Matrix.ext; change ∀ i j, raw19208step1 i j = -(raw19208step0 i j); unfold raw19208step1 raw19208step0; decide +kernel
      have hl : raw19208step1Labels = raw19208step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19208step1 raw19208step1Labels = mixedMoment B raw19208step2 raw19208step2Labels := by
      have ha : raw19208step2 = raw19208step1 := by apply Matrix.ext; unfold raw19208step2 raw19208step1; decide +kernel
      have hl : raw19208step1Labels = labelEmbedding10 ∘ raw19208step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19208step1 raw19208step1Labels raw19208step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical19209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19209 raw19209Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw19209 raw19209Labels = mixedMoment B raw19209step0 raw19209step0Labels := by
      have hz : ∀ j, raw19209 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19209step0 = (fun i j => raw19209 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19209step0 raw19209; decide +kernel
      have hl : raw19209step0Labels = raw19209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19209 raw19209Labels permutation590 hz
    mixedMoment B raw19209step0 raw19209step0Labels = mixedMoment B raw19209step1 raw19209step1Labels := by
      have ha : raw19209step1 = (fun i j => raw19209step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19209step1 raw19209step0; decide +kernel
      have hl : raw19209step1Labels = raw19209step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19209step0 raw19209step0Labels permutation39 permutation7
    mixedMoment B raw19209step1 raw19209step1Labels = mixedMoment B raw19209step2 raw19209step2Labels := by
      have ha : raw19209step2 = -raw19209step1 := by apply Matrix.ext; change ∀ i j, raw19209step2 i j = -(raw19209step1 i j); unfold raw19209step2 raw19209step1; decide +kernel
      have hl : raw19209step2Labels = raw19209step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19209step2 raw19209step2Labels = mixedMoment B raw19209step3 raw19209step3Labels := by
      have ha : raw19209step3 = raw19209step2 := by apply Matrix.ext; unfold raw19209step3 raw19209step2; decide +kernel
      have hl : raw19209step2Labels = labelEmbedding10 ∘ raw19209step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19209step2 raw19209step2Labels raw19209step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical19210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19210 raw19210Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw19210 raw19210Labels = mixedMoment B raw19210step0 raw19210step0Labels := by
      have ha : raw19210step0 = (fun i j => raw19210 (permutation272 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19210step0 raw19210; decide +kernel
      have hl : raw19210step0Labels = raw19210Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19210 raw19210Labels permutation272 permutation5
    mixedMoment B raw19210step0 raw19210step0Labels = mixedMoment B raw19210step1 raw19210step1Labels := by
      have ha : raw19210step1 = -raw19210step0 := by apply Matrix.ext; change ∀ i j, raw19210step1 i j = -(raw19210step0 i j); unfold raw19210step1 raw19210step0; decide +kernel
      have hl : raw19210step1Labels = raw19210step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19210step1 raw19210step1Labels = mixedMoment B raw19210step2 raw19210step2Labels := by
      have ha : raw19210step2 = raw19210step1 := by apply Matrix.ext; unfold raw19210step2 raw19210step1; decide +kernel
      have hl : raw19210step1Labels = labelEmbedding8 ∘ raw19210step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19210step1 raw19210step1Labels raw19210step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

theorem canonical19211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19211 raw19211Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw19211 raw19211Labels = mixedMoment B raw19211step0 raw19211step0Labels := by
      have ha : raw19211step0 = (fun i j => raw19211 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19211step0 raw19211; decide +kernel
      have hl : raw19211step0Labels = raw19211Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19211 raw19211Labels permutation180 permutation2
    _ = mixedMoment B node5401 node5401Labels := by rfl

theorem canonical19212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19212 raw19212Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw19212 raw19212Labels = mixedMoment B raw19212step0 raw19212step0Labels := by
      have ha : raw19212step0 = (fun i j => raw19212 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19212step0 raw19212; decide +kernel
      have hl : raw19212step0Labels = raw19212Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19212 raw19212Labels permutation194 permutation7
    mixedMoment B raw19212step0 raw19212step0Labels = mixedMoment B raw19212step1 raw19212step1Labels := by
      have ha : raw19212step1 = -raw19212step0 := by apply Matrix.ext; change ∀ i j, raw19212step1 i j = -(raw19212step0 i j); unfold raw19212step1 raw19212step0; decide +kernel
      have hl : raw19212step1Labels = raw19212step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19212step1 raw19212step1Labels = mixedMoment B raw19212step2 raw19212step2Labels := by
      have ha : raw19212step2 = raw19212step1 := by apply Matrix.ext; unfold raw19212step2 raw19212step1; decide +kernel
      have hl : raw19212step1Labels = labelEmbedding10 ∘ raw19212step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19212step1 raw19212step1Labels raw19212step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical19213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19213 raw19213Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw19213 raw19213Labels = mixedMoment B raw19213step0 raw19213step0Labels := by
      have hz : ∀ j, raw19213 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19213step0 = (fun i j => raw19213 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19213step0 raw19213; decide +kernel
      have hl : raw19213step0Labels = raw19213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19213 raw19213Labels permutation590 hz
    mixedMoment B raw19213step0 raw19213step0Labels = mixedMoment B raw19213step1 raw19213step1Labels := by
      have ha : raw19213step1 = (fun i j => raw19213step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19213step1 raw19213step0; decide +kernel
      have hl : raw19213step1Labels = raw19213step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19213step0 raw19213step0Labels permutation38 permutation7
    mixedMoment B raw19213step1 raw19213step1Labels = mixedMoment B raw19213step2 raw19213step2Labels := by
      have ha : raw19213step2 = -raw19213step1 := by apply Matrix.ext; change ∀ i j, raw19213step2 i j = -(raw19213step1 i j); unfold raw19213step2 raw19213step1; decide +kernel
      have hl : raw19213step2Labels = raw19213step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19213step2 raw19213step2Labels = mixedMoment B raw19213step3 raw19213step3Labels := by
      have ha : raw19213step3 = raw19213step2 := by apply Matrix.ext; unfold raw19213step3 raw19213step2; decide +kernel
      have hl : raw19213step2Labels = labelEmbedding10 ∘ raw19213step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19213step2 raw19213step2Labels raw19213step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical19214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19214 raw19214Labels = mixedMoment B node5219 node5219Labels := by
  calc
    mixedMoment B raw19214 raw19214Labels = mixedMoment B raw19214step0 raw19214step0Labels := by
      have ha : raw19214step0 = (fun i j => raw19214 (permutation273 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19214step0 raw19214; decide +kernel
      have hl : raw19214step0Labels = raw19214Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19214 raw19214Labels permutation273 permutation5
    mixedMoment B raw19214step0 raw19214step0Labels = mixedMoment B raw19214step1 raw19214step1Labels := by
      have ha : raw19214step1 = -raw19214step0 := by apply Matrix.ext; change ∀ i j, raw19214step1 i j = -(raw19214step0 i j); unfold raw19214step1 raw19214step0; decide +kernel
      have hl : raw19214step1Labels = raw19214step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19214step1 raw19214step1Labels = mixedMoment B raw19214step2 raw19214step2Labels := by
      have ha : raw19214step2 = raw19214step1 := by apply Matrix.ext; unfold raw19214step2 raw19214step1; decide +kernel
      have hl : raw19214step1Labels = labelEmbedding8 ∘ raw19214step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19214step1 raw19214step1Labels raw19214step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5219 node5219Labels := by rfl

theorem canonical19215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19215 raw19215Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw19215 raw19215Labels = mixedMoment B raw19215step0 raw19215step0Labels := by
      have ha : raw19215step0 = (fun i j => raw19215 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19215step0 raw19215; decide +kernel
      have hl : raw19215step0Labels = raw19215Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19215 raw19215Labels permutation176 permutation2
    _ = mixedMoment B node5403 node5403Labels := by rfl

theorem canonical19216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19216 raw19216Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw19216 raw19216Labels = mixedMoment B raw19216step0 raw19216step0Labels := by
      have ha : raw19216step0 = (fun i j => raw19216 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19216step0 raw19216; decide +kernel
      have hl : raw19216step0Labels = raw19216Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19216 raw19216Labels permutation682 permutation3
    mixedMoment B raw19216step0 raw19216step0Labels = mixedMoment B raw19216step1 raw19216step1Labels := by
      have ha : raw19216step1 = -raw19216step0 := by apply Matrix.ext; change ∀ i j, raw19216step1 i j = -(raw19216step0 i j); unfold raw19216step1 raw19216step0; decide +kernel
      have hl : raw19216step1Labels = raw19216step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19216step1 raw19216step1Labels = mixedMoment B raw19216step2 raw19216step2Labels := by
      have ha : raw19216step2 = raw19216step1 := by apply Matrix.ext; unfold raw19216step2 raw19216step1; decide +kernel
      have hl : raw19216step1Labels = labelEmbedding6 ∘ raw19216step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19216step1 raw19216step1Labels raw19216step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical19217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19217 raw19217Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw19217 raw19217Labels = mixedMoment B raw19217step0 raw19217step0Labels := by
      have ha : raw19217step0 = (fun i j => raw19217 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19217step0 raw19217; decide +kernel
      have hl : raw19217step0Labels = raw19217Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19217 raw19217Labels permutation658 permutation3
    mixedMoment B raw19217step0 raw19217step0Labels = mixedMoment B raw19217step1 raw19217step1Labels := by
      have ha : raw19217step1 = -raw19217step0 := by apply Matrix.ext; change ∀ i j, raw19217step1 i j = -(raw19217step0 i j); unfold raw19217step1 raw19217step0; decide +kernel
      have hl : raw19217step1Labels = raw19217step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19217step1 raw19217step1Labels = mixedMoment B raw19217step2 raw19217step2Labels := by
      have ha : raw19217step2 = raw19217step1 := by apply Matrix.ext; unfold raw19217step2 raw19217step1; decide +kernel
      have hl : raw19217step1Labels = labelEmbedding6 ∘ raw19217step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19217step1 raw19217step1Labels raw19217step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2475 raw2475Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw2475 raw2475Labels = mixedMoment B raw2475step0 raw2475step0Labels := by
      have ha : raw2475step0 = (fun i j => raw2475 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2475step0 raw2475; decide +kernel
      have hl : raw2475step0Labels = raw2475Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2475 raw2475Labels permutation152 permutation4
    mixedMoment B raw2475step0 raw2475step0Labels = mixedMoment B raw2475step1 raw2475step1Labels := by
      have ha : raw2475step1 = raw2475step0 := by apply Matrix.ext; unfold raw2475step1 raw2475step0; decide +kernel
      have hl : raw2475step0Labels = labelEmbedding7 ∘ raw2475step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2475step0 raw2475step0Labels raw2475step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

theorem canonical2476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2476 raw2476Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw2476 raw2476Labels = mixedMoment B raw2476step0 raw2476step0Labels := by
      have ha : raw2476step0 = (fun i j => raw2476 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2476step0 raw2476; decide +kernel
      have hl : raw2476step0Labels = raw2476Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2476 raw2476Labels permutation152 permutation4
    _ = mixedMoment B node3787 node3787Labels := by rfl

theorem canonical2477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2477 raw2477Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw2477 raw2477Labels = mixedMoment B raw2477step0 raw2477step0Labels := by
      have ha : raw2477step0 = (fun i j => raw2477 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2477step0 raw2477; decide +kernel
      have hl : raw2477step0Labels = raw2477Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2477 raw2477Labels permutation158 permutation6
    mixedMoment B raw2477step0 raw2477step0Labels = mixedMoment B raw2477step1 raw2477step1Labels := by
      have ha : raw2477step1 = -raw2477step0 := by apply Matrix.ext; change ∀ i j, raw2477step1 i j = -(raw2477step0 i j); unfold raw2477step1 raw2477step0; decide +kernel
      have hl : raw2477step1Labels = raw2477step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2477step1 raw2477step1Labels = mixedMoment B raw2477step2 raw2477step2Labels := by
      have ha : raw2477step2 = raw2477step1 := by apply Matrix.ext; unfold raw2477step2 raw2477step1; decide +kernel
      have hl : raw2477step1Labels = labelEmbedding1 ∘ raw2477step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2477step1 raw2477step1Labels raw2477step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

theorem canonical2478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2478 raw2478Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw2478 raw2478Labels = mixedMoment B raw2478step0 raw2478step0Labels := by
      have ha : raw2478step0 = (fun i j => raw2478 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2478step0 raw2478; decide +kernel
      have hl : raw2478step0Labels = raw2478Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2478 raw2478Labels permutation152 permutation4
    mixedMoment B raw2478step0 raw2478step0Labels = mixedMoment B raw2478step1 raw2478step1Labels := by
      have ha : raw2478step1 = raw2478step0 := by apply Matrix.ext; unfold raw2478step1 raw2478step0; decide +kernel
      have hl : raw2478step0Labels = labelEmbedding7 ∘ raw2478step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2478step0 raw2478step0Labels raw2478step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

theorem canonical2479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2479 raw2479Labels = mixedMoment B node3789 node3789Labels := by
  calc
    mixedMoment B raw2479 raw2479Labels = mixedMoment B raw2479step0 raw2479step0Labels := by
      have ha : raw2479step0 = (fun i j => raw2479 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2479step0 raw2479; decide +kernel
      have hl : raw2479step0Labels = raw2479Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2479 raw2479Labels permutation152 permutation4
    _ = mixedMoment B node3789 node3789Labels := by rfl

theorem canonical2480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2480 raw2480Labels = mixedMoment B node3810 node3810Labels := by
  calc
    mixedMoment B raw2480 raw2480Labels = mixedMoment B raw2480step0 raw2480step0Labels := by
      have ha : raw2480step0 = (fun i j => raw2480 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2480step0 raw2480; decide +kernel
      have hl : raw2480step0Labels = raw2480Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2480 raw2480Labels permutation170 permutation6
    mixedMoment B raw2480step0 raw2480step0Labels = mixedMoment B raw2480step1 raw2480step1Labels := by
      have ha : raw2480step1 = -raw2480step0 := by apply Matrix.ext; change ∀ i j, raw2480step1 i j = -(raw2480step0 i j); unfold raw2480step1 raw2480step0; decide +kernel
      have hl : raw2480step1Labels = raw2480step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2480step1 raw2480step1Labels = mixedMoment B raw2480step2 raw2480step2Labels := by
      have ha : raw2480step2 = raw2480step1 := by apply Matrix.ext; unfold raw2480step2 raw2480step1; decide +kernel
      have hl : raw2480step1Labels = labelEmbedding1 ∘ raw2480step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2480step1 raw2480step1Labels raw2480step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3810 node3810Labels := by rfl

theorem canonical2538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2538 raw2538Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw2538 raw2538Labels = mixedMoment B raw2538step0 raw2538step0Labels := by
      have ha : raw2538step0 = (fun i j => raw2538 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2538step0 raw2538; decide +kernel
      have hl : raw2538step0Labels = raw2538Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2538 raw2538Labels permutation32 permutation4
    mixedMoment B raw2538step0 raw2538step0Labels = mixedMoment B raw2538step1 raw2538step1Labels := by
      have ha : raw2538step1 = raw2538step0 := by apply Matrix.ext; unfold raw2538step1 raw2538step0; decide +kernel
      have hl : raw2538step0Labels = labelEmbedding7 ∘ raw2538step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2538step0 raw2538step0Labels raw2538step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

theorem canonical2539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2539 raw2539Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw2539 raw2539Labels = mixedMoment B raw2539step0 raw2539step0Labels := by
      have ha : raw2539step0 = (fun i j => raw2539 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2539step0 raw2539; decide +kernel
      have hl : raw2539step0Labels = raw2539Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2539 raw2539Labels permutation32 permutation4
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical2540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2540 raw2540Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw2540 raw2540Labels = mixedMoment B raw2540step0 raw2540step0Labels := by
      have ha : raw2540step0 = (fun i j => raw2540 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2540step0 raw2540; decide +kernel
      have hl : raw2540step0Labels = raw2540Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2540 raw2540Labels permutation38 permutation6
    mixedMoment B raw2540step0 raw2540step0Labels = mixedMoment B raw2540step1 raw2540step1Labels := by
      have ha : raw2540step1 = -raw2540step0 := by apply Matrix.ext; change ∀ i j, raw2540step1 i j = -(raw2540step0 i j); unfold raw2540step1 raw2540step0; decide +kernel
      have hl : raw2540step1Labels = raw2540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2540step1 raw2540step1Labels = mixedMoment B raw2540step2 raw2540step2Labels := by
      have ha : raw2540step2 = raw2540step1 := by apply Matrix.ext; unfold raw2540step2 raw2540step1; decide +kernel
      have hl : raw2540step1Labels = labelEmbedding1 ∘ raw2540step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2540step1 raw2540step1Labels raw2540step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

theorem canonical2550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2550 raw2550Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw2550 raw2550Labels = mixedMoment B raw2550step0 raw2550step0Labels := by
      have ha : raw2550step0 = (fun i j => raw2550 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2550step0 raw2550; decide +kernel
      have hl : raw2550step0Labels = raw2550Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2550 raw2550Labels permutation32 permutation4
    mixedMoment B raw2550step0 raw2550step0Labels = mixedMoment B raw2550step1 raw2550step1Labels := by
      have ha : raw2550step1 = raw2550step0 := by apply Matrix.ext; unfold raw2550step1 raw2550step0; decide +kernel
      have hl : raw2550step0Labels = labelEmbedding7 ∘ raw2550step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2550step0 raw2550step0Labels raw2550step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

theorem canonical2551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2551 raw2551Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw2551 raw2551Labels = mixedMoment B raw2551step0 raw2551step0Labels := by
      have ha : raw2551step0 = (fun i j => raw2551 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2551step0 raw2551; decide +kernel
      have hl : raw2551step0Labels = raw2551Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2551 raw2551Labels permutation32 permutation4
    _ = mixedMoment B node3885 node3885Labels := by rfl

theorem canonical2552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2552 raw2552Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw2552 raw2552Labels = mixedMoment B raw2552step0 raw2552step0Labels := by
      have ha : raw2552step0 = (fun i j => raw2552 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2552step0 raw2552; decide +kernel
      have hl : raw2552step0Labels = raw2552Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2552 raw2552Labels permutation38 permutation6
    mixedMoment B raw2552step0 raw2552step0Labels = mixedMoment B raw2552step1 raw2552step1Labels := by
      have ha : raw2552step1 = -raw2552step0 := by apply Matrix.ext; change ∀ i j, raw2552step1 i j = -(raw2552step0 i j); unfold raw2552step1 raw2552step0; decide +kernel
      have hl : raw2552step1Labels = raw2552step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2552step1 raw2552step1Labels = mixedMoment B raw2552step2 raw2552step2Labels := by
      have ha : raw2552step2 = raw2552step1 := by apply Matrix.ext; unfold raw2552step2 raw2552step1; decide +kernel
      have hl : raw2552step1Labels = labelEmbedding1 ∘ raw2552step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2552step1 raw2552step1Labels raw2552step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3885 node3885Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2598 raw2598Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw2598 raw2598Labels = mixedMoment B raw2598step0 raw2598step0Labels := by
      have ha : raw2598step0 = (fun i j => raw2598 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2598step0 raw2598; decide +kernel
      have hl : raw2598step0Labels = raw2598Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2598 raw2598Labels permutation152 permutation4
    mixedMoment B raw2598step0 raw2598step0Labels = mixedMoment B raw2598step1 raw2598step1Labels := by
      have ha : raw2598step1 = raw2598step0 := by apply Matrix.ext; unfold raw2598step1 raw2598step0; decide +kernel
      have hl : raw2598step0Labels = labelEmbedding7 ∘ raw2598step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2598step0 raw2598step0Labels raw2598step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

theorem canonical2599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2599 raw2599Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw2599 raw2599Labels = mixedMoment B raw2599step0 raw2599step0Labels := by
      have ha : raw2599step0 = (fun i j => raw2599 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2599step0 raw2599; decide +kernel
      have hl : raw2599step0Labels = raw2599Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2599 raw2599Labels permutation152 permutation4
    _ = mixedMoment B node3974 node3974Labels := by rfl

theorem canonical2600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2600 raw2600Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw2600 raw2600Labels = mixedMoment B raw2600step0 raw2600step0Labels := by
      have ha : raw2600step0 = (fun i j => raw2600 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2600step0 raw2600; decide +kernel
      have hl : raw2600step0Labels = raw2600Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2600 raw2600Labels permutation688 permutation6
    mixedMoment B raw2600step0 raw2600step0Labels = mixedMoment B raw2600step1 raw2600step1Labels := by
      have ha : raw2600step1 = raw2600step0 := by apply Matrix.ext; unfold raw2600step1 raw2600step0; decide +kernel
      have hl : raw2600step0Labels = labelEmbedding1 ∘ raw2600step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2600step0 raw2600step0Labels raw2600step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5401 node5401Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3787 node3787Labels + mixedMoment B node3804 node3804Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2475 singletonSmall5401
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5401) = raw2475Labels := by decide +kernel
  rw [hl, canonical2475 B hB] at h
  have hc0 : mixedMoment B raw2475 (Fin.cases (0 : Fin 2) singletonSmall5401) =
      mixedMoment B node3787 node3787Labels := by
    have ha : raw2475 = raw2476 := by apply Matrix.ext; unfold raw2475 raw2476; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5401 = raw2476Labels := by decide +kernel
    rw [ha, hj, canonical2476 B hB]
  have hc1 : mixedMoment B raw2475 (Fin.cases (1 : Fin 2) singletonSmall5401) =
      mixedMoment B node3804 node3804Labels := by
    have ha : raw2475 = raw2477 := by apply Matrix.ext; unfold raw2475 raw2477; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5401 = raw2477Labels := by decide +kernel
    rw [ha, hj, canonical2477 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5403 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5403 node5403Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3789 node3789Labels + mixedMoment B node3810 node3810Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2478 singletonSmall5403
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5403) = raw2478Labels := by decide +kernel
  rw [hl, canonical2478 B hB] at h
  have hc0 : mixedMoment B raw2478 (Fin.cases (0 : Fin 2) singletonSmall5403) =
      mixedMoment B node3789 node3789Labels := by
    have ha : raw2478 = raw2479 := by apply Matrix.ext; unfold raw2478 raw2479; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5403 = raw2479Labels := by decide +kernel
    rw [ha, hj, canonical2479 B hB]
  have hc1 : mixedMoment B raw2478 (Fin.cases (1 : Fin 2) singletonSmall5403) =
      mixedMoment B node3810 node3810Labels := by
    have ha : raw2478 = raw2480 := by apply Matrix.ext; unfold raw2478 raw2480; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5403 = raw2480Labels := by decide +kernel
    rw [ha, hj, canonical2480 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5438 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5438 node5438Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3857 node3857Labels + mixedMoment B node3876 node3876Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2538 singletonSmall5438
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5438) = raw2538Labels := by decide +kernel
  rw [hl, canonical2538 B hB] at h
  have hc0 : mixedMoment B raw2538 (Fin.cases (0 : Fin 2) singletonSmall5438) =
      mixedMoment B node3857 node3857Labels := by
    have ha : raw2538 = raw2539 := by apply Matrix.ext; unfold raw2538 raw2539; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5438 = raw2539Labels := by decide +kernel
    rw [ha, hj, canonical2539 B hB]
  have hc1 : mixedMoment B raw2538 (Fin.cases (1 : Fin 2) singletonSmall5438) =
      mixedMoment B node3876 node3876Labels := by
    have ha : raw2538 = raw2540 := by apply Matrix.ext; unfold raw2538 raw2540; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5438 = raw2540Labels := by decide +kernel
    rw [ha, hj, canonical2540 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5448 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5448 node5448Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3885 node3885Labels + mixedMoment B node3885 node3885Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2550 singletonSmall5448
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5448) = raw2550Labels := by decide +kernel
  rw [hl, canonical2550 B hB] at h
  have hc0 : mixedMoment B raw2550 (Fin.cases (0 : Fin 2) singletonSmall5448) =
      mixedMoment B node3885 node3885Labels := by
    have ha : raw2550 = raw2551 := by apply Matrix.ext; unfold raw2550 raw2551; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5448 = raw2551Labels := by decide +kernel
    rw [ha, hj, canonical2551 B hB]
  have hc1 : mixedMoment B raw2550 (Fin.cases (1 : Fin 2) singletonSmall5448) =
      mixedMoment B node3885 node3885Labels := by
    have ha : raw2550 = raw2552 := by apply Matrix.ext; unfold raw2550 raw2552; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5448 = raw2552Labels := by decide +kernel
    rw [ha, hj, canonical2552 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5478 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5478 node5478Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3974 node3974Labels + mixedMoment B node3974 node3974Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2598 singletonSmall5478
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5478) = raw2598Labels := by decide +kernel
  rw [hl, canonical2598 B hB] at h
  have hc0 : mixedMoment B raw2598 (Fin.cases (0 : Fin 2) singletonSmall5478) =
      mixedMoment B node3974 node3974Labels := by
    have ha : raw2598 = raw2599 := by apply Matrix.ext; unfold raw2598 raw2599; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5478 = raw2599Labels := by decide +kernel
    rw [ha, hj, canonical2599 B hB]
  have hc1 : mixedMoment B raw2598 (Fin.cases (1 : Fin 2) singletonSmall5478) =
      mixedMoment B node3974 node3974Labels := by
    have ha : raw2598 = raw2600 := by apply Matrix.ext; unfold raw2598 raw2600; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5478 = raw2600Labels := by decide +kernel
    rw [ha, hj, canonical2600 B hB]
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

theorem zero5481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node5481 node5481Labels = 0 := by
  exact mixedMoment_alpha B hF node5481 node5481Labels 2 permutation158
    (by decide +kernel)

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

theorem sound3532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3532 node3532Labels = Sparse.eval nodeValue3532 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3532) = mixedMoment B node3532 node3532Labels := rfl
  simpa [nodeValue3532, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3787 node3787Labels = Sparse.eval nodeValue3787 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3787) = mixedMoment B node3787 node3787Labels := rfl
  simpa [nodeValue3787, Sparse.eval] using hc.symm

theorem sound3789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3789 node3789Labels = Sparse.eval nodeValue3789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3789) = mixedMoment B node3789 node3789Labels := rfl
  simpa [nodeValue3789, Sparse.eval] using hc.symm

theorem sound3804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3804 node3804Labels = Sparse.eval nodeValue3804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3804) = mixedMoment B node3804 node3804Labels := rfl
  simpa [nodeValue3804, Sparse.eval] using hc.symm

theorem sound3810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3810 node3810Labels = Sparse.eval nodeValue3810 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3810) = mixedMoment B node3810 node3810Labels := rfl
  simpa [nodeValue3810, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3857 node3857Labels = Sparse.eval nodeValue3857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3857) = mixedMoment B node3857 node3857Labels := rfl
  simpa [nodeValue3857, Sparse.eval] using hc.symm

theorem sound3876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3876 node3876Labels = Sparse.eval nodeValue3876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3876) = mixedMoment B node3876 node3876Labels := rfl
  simpa [nodeValue3876, Sparse.eval] using hc.symm

theorem sound3885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3885 node3885Labels = Sparse.eval nodeValue3885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3885) = mixedMoment B node3885 node3885Labels := rfl
  simpa [nodeValue3885, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3974 node3974Labels = Sparse.eval nodeValue3974 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3974) = mixedMoment B node3974 node3974Labels := rfl
  simpa [nodeValue3974, Sparse.eval] using hc.symm

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

theorem sound5185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5185 node5185Labels = Sparse.eval nodeValue5185 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5185) = mixedMoment B node5185 node5185Labels := rfl
  simpa [nodeValue5185, Sparse.eval] using hc.symm

theorem sound5187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5187 node5187Labels = Sparse.eval nodeValue5187 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5187) = mixedMoment B node5187 node5187Labels := rfl
  simpa [nodeValue5187, Sparse.eval] using hc.symm

theorem sound5197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5197 node5197Labels = Sparse.eval nodeValue5197 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5197) = mixedMoment B node5197 node5197Labels := rfl
  simpa [nodeValue5197, Sparse.eval] using hc.symm

theorem sound5219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5219 node5219Labels = Sparse.eval nodeValue5219 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5219) = mixedMoment B node5219 node5219Labels := rfl
  simpa [nodeValue5219, Sparse.eval] using hc.symm

theorem sound5220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5220 node5220Labels = Sparse.eval nodeValue5220 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5220) = mixedMoment B node5220 node5220Labels := rfl
  simpa [nodeValue5220, Sparse.eval] using hc.symm

theorem sound5226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5226 node5226Labels = Sparse.eval nodeValue5226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5226) = mixedMoment B node5226 node5226Labels := rfl
  simpa [nodeValue5226, Sparse.eval] using hc.symm

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

theorem sound5281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5281 node5281Labels = Sparse.eval nodeValue5281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5281) = mixedMoment B node5281 node5281Labels := rfl
  simpa [nodeValue5281, Sparse.eval] using hc.symm

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

theorem zero5408 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5408 node5408Labels = 0 := by
  exact mixedMoment_order_one B hB node5408 node5408Labels 1
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

theorem sound5401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5401 node5401Labels = Sparse.eval nodeValue5401 (mixedVector B) := by
  have h := singleton5401 B _hB
  rw [sound3787 B _hB _hF, sound3804 B _hB _hF] at h
  norm_num [nodeValue5401, nodeValue3787, nodeValue3804, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5403 node5403Labels = Sparse.eval nodeValue5403 (mixedVector B) := by
  have h := singleton5403 B _hB
  rw [sound3789 B _hB _hF, sound3810 B _hB _hF] at h
  norm_num [nodeValue5403, nodeValue3789, nodeValue3810, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5408 node5408Labels = Sparse.eval nodeValue5408 (mixedVector B) := by
  simpa only [nodeValue5408, Sparse.eval_nil] using zero5408 B _hB _hF

theorem sound5425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5425 node5425Labels = Sparse.eval nodeValue5425 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5425) = mixedMoment B node5425 node5425Labels := rfl
  simpa [nodeValue5425, Sparse.eval] using hc.symm

theorem sound5430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5430 node5430Labels = Sparse.eval nodeValue5430 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5430) = mixedMoment B node5430 node5430Labels := rfl
  simpa [nodeValue5430, Sparse.eval] using hc.symm

theorem sound5438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5438 node5438Labels = Sparse.eval nodeValue5438 (mixedVector B) := by
  have h := singleton5438 B _hB
  rw [sound3857 B _hB _hF, sound3876 B _hB _hF] at h
  norm_num [nodeValue5438, nodeValue3857, nodeValue3876, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5445 node5445Labels = Sparse.eval nodeValue5445 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5445) = mixedMoment B node5445 node5445Labels := rfl
  simpa [nodeValue5445, Sparse.eval] using hc.symm

theorem sound5448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5448 node5448Labels = Sparse.eval nodeValue5448 (mixedVector B) := by
  have h := singleton5448 B _hB
  rw [sound3885 B _hB _hF] at h
  norm_num [nodeValue5448, nodeValue3885, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5478 node5478Labels = Sparse.eval nodeValue5478 (mixedVector B) := by
  have h := singleton5478 B _hB
  rw [sound3974 B _hB _hF] at h
  norm_num [nodeValue5478, nodeValue3974, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5481 node5481Labels = Sparse.eval nodeValue5481 (mixedVector B) := by
  simpa only [nodeValue5481, Sparse.eval_nil] using zero5481 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources35
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1132 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1132 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1132 + difference 0 1) (sourceB1132 + difference 1 0) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA1132 + difference 0 1) (sourceB1132 + difference 1 0) sourceC1132) = raw19196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19196; decide +kernel
    rw [ha]
    exact (canonical19196 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1132 + difference 0 2) (sourceB1132 + difference 2 0) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA1132 + difference 0 2) (sourceB1132 + difference 2 0) sourceC1132) = raw19197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19197; decide +kernel
    rw [ha]
    exact (canonical19197 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1132 + difference 0 3) (sourceB1132 + difference 3 0) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1132 + difference 0 3) (sourceB1132 + difference 3 0) sourceC1132) = raw19198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19198; decide +kernel
    rw [ha]
    exact (canonical19198 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1132 + difference 0 4) (sourceB1132 + difference 4 0) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA1132 + difference 0 4) (sourceB1132 + difference 4 0) sourceC1132) = raw19199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19199; decide +kernel
    rw [ha]
    exact (canonical19199 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1132 + difference 0 5) (sourceB1132 + difference 5 0) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA1132 + difference 0 5) (sourceB1132 + difference 5 0) sourceC1132) = raw19200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19200; decide +kernel
    rw [ha]
    exact (canonical19200 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1132 + difference 1 0) (sourceB1132 + difference 0 1) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA1132 + difference 1 0) (sourceB1132 + difference 0 1) sourceC1132) = raw19201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19201; decide +kernel
    rw [ha]
    exact (canonical19201 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1132 + difference 1 2) (sourceB1132 + difference 2 1) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5408) := by
    have ha : (tripleCharges (sourceA1132 + difference 1 2) (sourceB1132 + difference 2 1) sourceC1132) = raw13674 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw13674; decide +kernel
    rw [ha]
    exact (canonical13674 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1132 + difference 1 3) (sourceB1132 + difference 3 1) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1132 + difference 1 3) (sourceB1132 + difference 3 1) sourceC1132) = raw13675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw13675; decide +kernel
    rw [ha]
    exact (canonical13675 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1132 + difference 1 4) (sourceB1132 + difference 4 1) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1132 + difference 1 4) (sourceB1132 + difference 4 1) sourceC1132) = raw13676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw13676; decide +kernel
    rw [ha]
    exact (canonical13676 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1132 + difference 1 5) (sourceB1132 + difference 5 1) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1132 + difference 1 5) (sourceB1132 + difference 5 1) sourceC1132) = raw13677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw13677; decide +kernel
    rw [ha]
    exact (canonical13677 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1132 + difference 2 0) (sourceB1132 + difference 0 2) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5197) := by
    have ha : (tripleCharges (sourceA1132 + difference 2 0) (sourceB1132 + difference 0 2) sourceC1132) = raw13684 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw13684; decide +kernel
    rw [ha]
    exact (canonical13684 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1132 + difference 2 1) (sourceB1132 + difference 1 2) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5220) := by
    have ha : (tripleCharges (sourceA1132 + difference 2 1) (sourceB1132 + difference 1 2) sourceC1132) = raw19202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19202; decide +kernel
    rw [ha]
    exact (canonical19202 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1132 + difference 2 3) (sourceB1132 + difference 3 2) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1132 + difference 2 3) (sourceB1132 + difference 3 2) sourceC1132) = raw19203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19203; decide +kernel
    rw [ha]
    exact (canonical19203 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1132 + difference 2 4) (sourceB1132 + difference 4 2) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1132 + difference 2 4) (sourceB1132 + difference 4 2) sourceC1132) = raw19204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19204; decide +kernel
    rw [ha]
    exact (canonical19204 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1132 + difference 2 5) (sourceB1132 + difference 5 2) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1132 + difference 2 5) (sourceB1132 + difference 5 2) sourceC1132) = raw19205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19205; decide +kernel
    rw [ha]
    exact (canonical19205 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1132 + difference 3 0) (sourceB1132 + difference 0 3) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA1132 + difference 3 0) (sourceB1132 + difference 0 3) sourceC1132) = raw13689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw13689; decide +kernel
    rw [ha]
    exact (canonical13689 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1132 + difference 3 1) (sourceB1132 + difference 1 3) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA1132 + difference 3 1) (sourceB1132 + difference 1 3) sourceC1132) = raw19206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19206; decide +kernel
    rw [ha]
    exact (canonical19206 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1132 + difference 3 2) (sourceB1132 + difference 2 3) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1132 + difference 3 2) (sourceB1132 + difference 2 3) sourceC1132) = raw19207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19207; decide +kernel
    rw [ha]
    exact (canonical19207 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1132 + difference 3 4) (sourceB1132 + difference 4 3) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1132 + difference 3 4) (sourceB1132 + difference 4 3) sourceC1132) = raw19208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19208; decide +kernel
    rw [ha]
    exact (canonical19208 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1132 + difference 3 5) (sourceB1132 + difference 5 3) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1132 + difference 3 5) (sourceB1132 + difference 5 3) sourceC1132) = raw19209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19209; decide +kernel
    rw [ha]
    exact (canonical19209 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1132 + difference 4 0) (sourceB1132 + difference 0 4) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA1132 + difference 4 0) (sourceB1132 + difference 0 4) sourceC1132) = raw13694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw13694; decide +kernel
    rw [ha]
    exact (canonical13694 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1132 + difference 4 1) (sourceB1132 + difference 1 4) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA1132 + difference 4 1) (sourceB1132 + difference 1 4) sourceC1132) = raw19210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19210; decide +kernel
    rw [ha]
    exact (canonical19210 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1132 + difference 4 2) (sourceB1132 + difference 2 4) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA1132 + difference 4 2) (sourceB1132 + difference 2 4) sourceC1132) = raw19211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19211; decide +kernel
    rw [ha]
    exact (canonical19211 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1132 + difference 4 3) (sourceB1132 + difference 3 4) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA1132 + difference 4 3) (sourceB1132 + difference 3 4) sourceC1132) = raw19212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19212; decide +kernel
    rw [ha]
    exact (canonical19212 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1132 + difference 4 5) (sourceB1132 + difference 5 4) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA1132 + difference 4 5) (sourceB1132 + difference 5 4) sourceC1132) = raw19213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19213; decide +kernel
    rw [ha]
    exact (canonical19213 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1132 + difference 5 0) (sourceB1132 + difference 0 5) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5187) := by
    have ha : (tripleCharges (sourceA1132 + difference 5 0) (sourceB1132 + difference 0 5) sourceC1132) = raw13699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw13699; decide +kernel
    rw [ha]
    exact (canonical13699 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1132 + difference 5 1) (sourceB1132 + difference 1 5) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5219) := by
    have ha : (tripleCharges (sourceA1132 + difference 5 1) (sourceB1132 + difference 1 5) sourceC1132) = raw19214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19214; decide +kernel
    rw [ha]
    exact (canonical19214 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1132 + difference 5 2) (sourceB1132 + difference 2 5) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA1132 + difference 5 2) (sourceB1132 + difference 2 5) sourceC1132) = raw19215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19215; decide +kernel
    rw [ha]
    exact (canonical19215 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1132 + difference 5 3) (sourceB1132 + difference 3 5) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1132 + difference 5 3) (sourceB1132 + difference 3 5) sourceC1132) = raw19216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19216; decide +kernel
    rw [ha]
    exact (canonical19216 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1132 + difference 5 4) (sourceB1132 + difference 4 5) sourceC1132) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA1132 + difference 5 4) (sourceB1132 + difference 4 5) sourceC1132) = raw19217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1132 sourceB1132 sourceC1132 difference raw19217; decide +kernel
    rw [ha]
    exact (canonical19217 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1132 sourceB1132 sourceC1132
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1132, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck984 : Integer.Sparse.reindex keyMap MixedData.row984 = numericRow984 := by decide +kernel

theorem numericCheck984 (x : Master → ℝ) : Integer.Sparse.eval numericRow984 x =
    (17280 : ℝ) * reducedSource984 x := by
  norm_num [numericRow984, reducedSource984, Integer.Sparse.eval, Sparse.eval, nodeValue5185, nodeValue5187, nodeValue5197, nodeValue5219, nodeValue5220, nodeValue5226, nodeValue5257, nodeValue5281, nodeValue5401, nodeValue5403, nodeValue5408, nodeValue5425, nodeValue5430, nodeValue5433, nodeValue5438, nodeValue5440, nodeValue5445, nodeValue5448, nodeValue5478, nodeValue5481, nodeValue5485]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero984 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource984 (mixedVector B) = 0 := by
  have h5185 : mixedVector B (Sum.inr 5185) = Sparse.eval nodeValue5185 (mixedVector B) := by
    change mixedMoment B node5185 node5185Labels = _
    exact sound5185 B hB hF
  have h5187 : mixedVector B (Sum.inr 5187) = Sparse.eval nodeValue5187 (mixedVector B) := by
    change mixedMoment B node5187 node5187Labels = _
    exact sound5187 B hB hF
  have h5197 : mixedVector B (Sum.inr 5197) = Sparse.eval nodeValue5197 (mixedVector B) := by
    change mixedMoment B node5197 node5197Labels = _
    exact sound5197 B hB hF
  have h5219 : mixedVector B (Sum.inr 5219) = Sparse.eval nodeValue5219 (mixedVector B) := by
    change mixedMoment B node5219 node5219Labels = _
    exact sound5219 B hB hF
  have h5220 : mixedVector B (Sum.inr 5220) = Sparse.eval nodeValue5220 (mixedVector B) := by
    change mixedMoment B node5220 node5220Labels = _
    exact sound5220 B hB hF
  have h5226 : mixedVector B (Sum.inr 5226) = Sparse.eval nodeValue5226 (mixedVector B) := by
    change mixedMoment B node5226 node5226Labels = _
    exact sound5226 B hB hF
  have h5257 : mixedVector B (Sum.inr 5257) = Sparse.eval nodeValue5257 (mixedVector B) := by
    change mixedMoment B node5257 node5257Labels = _
    exact sound5257 B hB hF
  have h5281 : mixedVector B (Sum.inr 5281) = Sparse.eval nodeValue5281 (mixedVector B) := by
    change mixedMoment B node5281 node5281Labels = _
    exact sound5281 B hB hF
  have h5401 : mixedVector B (Sum.inr 5401) = Sparse.eval nodeValue5401 (mixedVector B) := by
    change mixedMoment B node5401 node5401Labels = _
    exact sound5401 B hB hF
  have h5403 : mixedVector B (Sum.inr 5403) = Sparse.eval nodeValue5403 (mixedVector B) := by
    change mixedMoment B node5403 node5403Labels = _
    exact sound5403 B hB hF
  have h5408 : mixedVector B (Sum.inr 5408) = Sparse.eval nodeValue5408 (mixedVector B) := by
    change mixedMoment B node5408 node5408Labels = _
    exact sound5408 B hB hF
  have h5425 : mixedVector B (Sum.inr 5425) = Sparse.eval nodeValue5425 (mixedVector B) := by
    change mixedMoment B node5425 node5425Labels = _
    exact sound5425 B hB hF
  have h5430 : mixedVector B (Sum.inr 5430) = Sparse.eval nodeValue5430 (mixedVector B) := by
    change mixedMoment B node5430 node5430Labels = _
    exact sound5430 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433_e B hB hF
  have h5438 : mixedVector B (Sum.inr 5438) = Sparse.eval nodeValue5438 (mixedVector B) := by
    change mixedMoment B node5438 node5438Labels = _
    exact sound5438 B hB hF
  have h5440 : mixedVector B (Sum.inr 5440) = Sparse.eval nodeValue5440 (mixedVector B) := by
    change mixedMoment B node5440 node5440Labels = _
    exact sound5440 B hB hF
  have h5445 : mixedVector B (Sum.inr 5445) = Sparse.eval nodeValue5445 (mixedVector B) := by
    change mixedMoment B node5445 node5445Labels = _
    exact sound5445 B hB hF
  have h5448 : mixedVector B (Sum.inr 5448) = Sparse.eval nodeValue5448 (mixedVector B) := by
    change mixedMoment B node5448 node5448Labels = _
    exact sound5448 B hB hF
  have h5478 : mixedVector B (Sum.inr 5478) = Sparse.eval nodeValue5478 (mixedVector B) := by
    change mixedMoment B node5478 node5478Labels = _
    exact sound5478 B hB hF
  have h5481 : mixedVector B (Sum.inr 5481) = Sparse.eval nodeValue5481 (mixedVector B) := by
    change mixedMoment B node5481 node5481Labels = _
    exact sound5481 B hB hF
  have h5485 : mixedVector B (Sum.inr 5485) = Sparse.eval nodeValue5485 (mixedVector B) := by
    change mixedMoment B node5485 node5485Labels = _
    exact sound5485_e B hB hF
  simpa only [sourceForm1132, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5185, h5187, h5197, h5219, h5220, h5226, h5257, h5281, h5401, h5403, h5408, h5425, h5430, h5433, h5438, h5440, h5445, h5448, h5478, h5481, h5485, reducedSource984] using sourceEq1132 B hB

theorem rowSound984_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row984 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck984, numericCheck984, reducedZero984 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound984_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound984_e_oai
