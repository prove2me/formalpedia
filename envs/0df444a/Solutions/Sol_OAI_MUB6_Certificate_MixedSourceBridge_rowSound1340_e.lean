-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T20:44:00.344884+00:00
-- url     : https://prove2.me/submissions/339d14b3-286d-4b18-bd1e-6dda52b11a0b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E190
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E099
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E118
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical176
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22611 raw22611Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw22611 raw22611Labels = mixedMoment B raw22611step0 raw22611step0Labels := by
      have hz : ∀ j, raw22611 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22611step0 = (fun i j => raw22611 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22611step0 raw22611; decide +kernel
      have hl : raw22611step0Labels = raw22611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22611 raw22611Labels permutation434 hz
    mixedMoment B raw22611step0 raw22611step0Labels = mixedMoment B raw22611step1 raw22611step1Labels := by
      have hz : ∀ j, raw22611step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22611step1 = (fun i j => raw22611step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22611step1 raw22611step0; decide +kernel
      have hl : raw22611step1Labels = raw22611step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22611step0 raw22611step0Labels permutation80 hz
    mixedMoment B raw22611step1 raw22611step1Labels = mixedMoment B raw22611step2 raw22611step2Labels := by
      have ha : raw22611step2 = (fun i j => raw22611step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22611step2 raw22611step1; decide +kernel
      have hl : raw22611step2Labels = raw22611step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22611step1 raw22611step1Labels permutation8 permutation6
    mixedMoment B raw22611step2 raw22611step2Labels = mixedMoment B raw22611step3 raw22611step3Labels := by
      have ha : raw22611step3 = raw22611step2 := by apply Matrix.ext; unfold raw22611step3 raw22611step2; decide +kernel
      have hl : raw22611step2Labels = labelEmbedding9 ∘ raw22611step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22611step2 raw22611step2Labels raw22611step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

theorem canonical22623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22623 raw22623Labels = mixedMoment B node4511 node4511Labels := by
  calc
    mixedMoment B raw22623 raw22623Labels = mixedMoment B raw22623step0 raw22623step0Labels := by
      have hz : ∀ j, raw22623 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22623step0 = (fun i j => raw22623 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22623step0 raw22623; decide +kernel
      have hl : raw22623step0Labels = raw22623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22623 raw22623Labels permutation434 hz
    mixedMoment B raw22623step0 raw22623step0Labels = mixedMoment B raw22623step1 raw22623step1Labels := by
      have hz : ∀ j, raw22623step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22623step1 = (fun i j => raw22623step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22623step1 raw22623step0; decide +kernel
      have hl : raw22623step1Labels = raw22623step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22623step0 raw22623step0Labels permutation80 hz
    mixedMoment B raw22623step1 raw22623step1Labels = mixedMoment B raw22623step2 raw22623step2Labels := by
      have hz : ∀ j, raw22623step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22623step2 = (fun i j => raw22623step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22623step2 raw22623step1; decide +kernel
      have hl : raw22623step2Labels = raw22623step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22623step1 raw22623step1Labels permutation14 hz
    mixedMoment B raw22623step2 raw22623step2Labels = mixedMoment B raw22623step3 raw22623step3Labels := by
      have ha : raw22623step3 = (fun i j => raw22623step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22623step3 raw22623step2; decide +kernel
      have hl : raw22623step3Labels = raw22623step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22623step2 raw22623step2Labels permutation3 permutation6
    mixedMoment B raw22623step3 raw22623step3Labels = mixedMoment B raw22623step4 raw22623step4Labels := by
      have ha : raw22623step4 = raw22623step3 := by apply Matrix.ext; unfold raw22623step4 raw22623step3; decide +kernel
      have hl : raw22623step3Labels = labelEmbedding9 ∘ raw22623step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22623step3 raw22623step3Labels raw22623step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4511 node4511Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical177
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22775 raw22775Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw22775 raw22775Labels = mixedMoment B raw22775step0 raw22775step0Labels := by
      have hz : ∀ j, raw22775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22775step0 = (fun i j => raw22775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22775step0 raw22775; decide +kernel
      have hl : raw22775step0Labels = raw22775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22775 raw22775Labels permutation346 hz
    mixedMoment B raw22775step0 raw22775step0Labels = mixedMoment B raw22775step1 raw22775step1Labels := by
      have ha : raw22775step1 = (fun i j => raw22775step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22775step1 raw22775step0; decide +kernel
      have hl : raw22775step1Labels = raw22775step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22775step0 raw22775step0Labels permutation39 permutation6
    mixedMoment B raw22775step1 raw22775step1Labels = mixedMoment B raw22775step2 raw22775step2Labels := by
      have ha : raw22775step2 = raw22775step1 := by apply Matrix.ext; unfold raw22775step2 raw22775step1; decide +kernel
      have hl : raw22775step1Labels = labelEmbedding9 ∘ raw22775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22775step1 raw22775step1Labels raw22775step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical180
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23077 raw23077Labels = mixedMoment B node4278 node4278Labels := by
  calc
    mixedMoment B raw23077 raw23077Labels = mixedMoment B raw23077step0 raw23077step0Labels := by
      have hz : ∀ j, raw23077 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23077step0 = (fun i j => raw23077 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23077step0 raw23077; decide +kernel
      have hl : raw23077step0Labels = raw23077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23077 raw23077Labels permutation434 hz
    mixedMoment B raw23077step0 raw23077step0Labels = mixedMoment B raw23077step1 raw23077step1Labels := by
      have hz : ∀ j, raw23077step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23077step1 = (fun i j => raw23077step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23077step1 raw23077step0; decide +kernel
      have hl : raw23077step1Labels = raw23077step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23077step0 raw23077step0Labels permutation80 hz
    mixedMoment B raw23077step1 raw23077step1Labels = mixedMoment B raw23077step2 raw23077step2Labels := by
      have ha : raw23077step2 = (fun i j => raw23077step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23077step2 raw23077step1; decide +kernel
      have hl : raw23077step2Labels = raw23077step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23077step1 raw23077step1Labels permutation12 permutation4
    mixedMoment B raw23077step2 raw23077step2Labels = mixedMoment B raw23077step3 raw23077step3Labels := by
      have ha : raw23077step3 = -raw23077step2 := by apply Matrix.ext; change ∀ i j, raw23077step3 i j = -(raw23077step2 i j); unfold raw23077step3 raw23077step2; decide +kernel
      have hl : raw23077step3Labels = raw23077step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23077step3 raw23077step3Labels = mixedMoment B raw23077step4 raw23077step4Labels := by
      have ha : raw23077step4 = raw23077step3 := by apply Matrix.ext; unfold raw23077step4 raw23077step3; decide +kernel
      have hl : raw23077step3Labels = labelEmbedding7 ∘ raw23077step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23077step3 raw23077step3Labels raw23077step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4278 node4278Labels := by rfl

theorem canonical23082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23082 raw23082Labels = mixedMoment B node4255 node4255Labels := by
  calc
    mixedMoment B raw23082 raw23082Labels = mixedMoment B raw23082step0 raw23082step0Labels := by
      have hz : ∀ j, raw23082 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23082step0 = (fun i j => raw23082 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23082step0 raw23082; decide +kernel
      have hl : raw23082step0Labels = raw23082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23082 raw23082Labels permutation434 hz
    mixedMoment B raw23082step0 raw23082step0Labels = mixedMoment B raw23082step1 raw23082step1Labels := by
      have ha : raw23082step1 = (fun i j => raw23082step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23082step1 raw23082step0; decide +kernel
      have hl : raw23082step1Labels = raw23082step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23082step0 raw23082step0Labels permutation33 permutation6
    mixedMoment B raw23082step1 raw23082step1Labels = mixedMoment B raw23082step2 raw23082step2Labels := by
      have ha : raw23082step2 = raw23082step1 := by apply Matrix.ext; unfold raw23082step2 raw23082step1; decide +kernel
      have hl : raw23082step1Labels = labelEmbedding9 ∘ raw23082step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23082step1 raw23082step1Labels raw23082step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4255 node4255Labels := by rfl

theorem canonical23087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23087 raw23087Labels = mixedMoment B node4255 node4255Labels := by
  calc
    mixedMoment B raw23087 raw23087Labels = mixedMoment B raw23087step0 raw23087step0Labels := by
      have hz : ∀ j, raw23087 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23087step0 = (fun i j => raw23087 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23087step0 raw23087; decide +kernel
      have hl : raw23087step0Labels = raw23087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23087 raw23087Labels permutation346 hz
    mixedMoment B raw23087step0 raw23087step0Labels = mixedMoment B raw23087step1 raw23087step1Labels := by
      have ha : raw23087step1 = (fun i j => raw23087step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23087step1 raw23087step0; decide +kernel
      have hl : raw23087step1Labels = raw23087step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23087step0 raw23087step0Labels permutation33 permutation6
    mixedMoment B raw23087step1 raw23087step1Labels = mixedMoment B raw23087step2 raw23087step2Labels := by
      have ha : raw23087step2 = raw23087step1 := by apply Matrix.ext; unfold raw23087step2 raw23087step1; decide +kernel
      have hl : raw23087step1Labels = labelEmbedding9 ∘ raw23087step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23087step1 raw23087step1Labels raw23087step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4255 node4255Labels := by rfl

theorem canonical23092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23092 raw23092Labels = mixedMoment B node4272 node4272Labels := by
  calc
    mixedMoment B raw23092 raw23092Labels = mixedMoment B raw23092step0 raw23092step0Labels := by
      have hz : ∀ j, raw23092 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23092step0 = (fun i j => raw23092 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23092step0 raw23092; decide +kernel
      have hl : raw23092step0Labels = raw23092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23092 raw23092Labels permutation434 hz
    mixedMoment B raw23092step0 raw23092step0Labels = mixedMoment B raw23092step1 raw23092step1Labels := by
      have hz : ∀ j, raw23092step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23092step1 = (fun i j => raw23092step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23092step1 raw23092step0; decide +kernel
      have hl : raw23092step1Labels = raw23092step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23092step0 raw23092step0Labels permutation80 hz
    mixedMoment B raw23092step1 raw23092step1Labels = mixedMoment B raw23092step2 raw23092step2Labels := by
      have ha : raw23092step2 = (fun i j => raw23092step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23092step2 raw23092step1; decide +kernel
      have hl : raw23092step2Labels = raw23092step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23092step1 raw23092step1Labels permutation9 permutation6
    mixedMoment B raw23092step2 raw23092step2Labels = mixedMoment B raw23092step3 raw23092step3Labels := by
      have ha : raw23092step3 = raw23092step2 := by apply Matrix.ext; unfold raw23092step3 raw23092step2; decide +kernel
      have hl : raw23092step2Labels = labelEmbedding9 ∘ raw23092step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23092step2 raw23092step2Labels raw23092step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4272 node4272Labels := by rfl

theorem canonical23098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23098 raw23098Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw23098 raw23098Labels = mixedMoment B raw23098step0 raw23098step0Labels := by
      have hz : ∀ j, raw23098 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23098step0 = (fun i j => raw23098 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23098step0 raw23098; decide +kernel
      have hl : raw23098step0Labels = raw23098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23098 raw23098Labels permutation434 hz
    mixedMoment B raw23098step0 raw23098step0Labels = mixedMoment B raw23098step1 raw23098step1Labels := by
      have ha : raw23098step1 = (fun i j => raw23098step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23098step1 raw23098step0; decide +kernel
      have hl : raw23098step1Labels = raw23098step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23098step0 raw23098step0Labels permutation39 permutation6
    mixedMoment B raw23098step1 raw23098step1Labels = mixedMoment B raw23098step2 raw23098step2Labels := by
      have ha : raw23098step2 = raw23098step1 := by apply Matrix.ext; unfold raw23098step2 raw23098step1; decide +kernel
      have hl : raw23098step1Labels = labelEmbedding9 ∘ raw23098step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23098step1 raw23098step1Labels raw23098step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical181
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23260 raw23260Labels = mixedMoment B node4279 node4279Labels := by
  calc
    mixedMoment B raw23260 raw23260Labels = mixedMoment B raw23260step0 raw23260step0Labels := by
      have hz : ∀ j, raw23260 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23260step0 = (fun i j => raw23260 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23260step0 raw23260; decide +kernel
      have hl : raw23260step0Labels = raw23260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23260 raw23260Labels permutation434 hz
    mixedMoment B raw23260step0 raw23260step0Labels = mixedMoment B raw23260step1 raw23260step1Labels := by
      have hz : ∀ j, raw23260step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23260step1 = (fun i j => raw23260step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23260step1 raw23260step0; decide +kernel
      have hl : raw23260step1Labels = raw23260step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23260step0 raw23260step0Labels permutation80 hz
    mixedMoment B raw23260step1 raw23260step1Labels = mixedMoment B raw23260step2 raw23260step2Labels := by
      have ha : raw23260step2 = (fun i j => raw23260step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23260step2 raw23260step1; decide +kernel
      have hl : raw23260step2Labels = raw23260step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23260step1 raw23260step1Labels permutation8 permutation6
    mixedMoment B raw23260step2 raw23260step2Labels = mixedMoment B raw23260step3 raw23260step3Labels := by
      have ha : raw23260step3 = raw23260step2 := by apply Matrix.ext; unfold raw23260step3 raw23260step2; decide +kernel
      have hl : raw23260step2Labels = labelEmbedding9 ∘ raw23260step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23260step2 raw23260step2Labels raw23260step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4279 node4279Labels := by rfl

theorem canonical23264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23264 raw23264Labels = mixedMoment B node4256 node4256Labels := by
  calc
    mixedMoment B raw23264 raw23264Labels = mixedMoment B raw23264step0 raw23264step0Labels := by
      have hz : ∀ j, raw23264 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23264step0 = (fun i j => raw23264 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23264step0 raw23264; decide +kernel
      have hl : raw23264step0Labels = raw23264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23264 raw23264Labels permutation434 hz
    mixedMoment B raw23264step0 raw23264step0Labels = mixedMoment B raw23264step1 raw23264step1Labels := by
      have ha : raw23264step1 = (fun i j => raw23264step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23264step1 raw23264step0; decide +kernel
      have hl : raw23264step1Labels = raw23264step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23264step0 raw23264step0Labels permutation32 permutation6
    mixedMoment B raw23264step1 raw23264step1Labels = mixedMoment B raw23264step2 raw23264step2Labels := by
      have ha : raw23264step2 = raw23264step1 := by apply Matrix.ext; unfold raw23264step2 raw23264step1; decide +kernel
      have hl : raw23264step1Labels = labelEmbedding9 ∘ raw23264step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23264step1 raw23264step1Labels raw23264step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4256 node4256Labels := by rfl

theorem canonical23267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23267 raw23267Labels = mixedMoment B node4256 node4256Labels := by
  calc
    mixedMoment B raw23267 raw23267Labels = mixedMoment B raw23267step0 raw23267step0Labels := by
      have hz : ∀ j, raw23267 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23267step0 = (fun i j => raw23267 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23267step0 raw23267; decide +kernel
      have hl : raw23267step0Labels = raw23267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23267 raw23267Labels permutation346 hz
    mixedMoment B raw23267step0 raw23267step0Labels = mixedMoment B raw23267step1 raw23267step1Labels := by
      have ha : raw23267step1 = (fun i j => raw23267step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23267step1 raw23267step0; decide +kernel
      have hl : raw23267step1Labels = raw23267step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23267step0 raw23267step0Labels permutation32 permutation6
    mixedMoment B raw23267step1 raw23267step1Labels = mixedMoment B raw23267step2 raw23267step2Labels := by
      have ha : raw23267step2 = raw23267step1 := by apply Matrix.ext; unfold raw23267step2 raw23267step1; decide +kernel
      have hl : raw23267step1Labels = labelEmbedding9 ∘ raw23267step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23267step1 raw23267step1Labels raw23267step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4256 node4256Labels := by rfl

theorem canonical23270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23270 raw23270Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw23270 raw23270Labels = mixedMoment B raw23270step0 raw23270step0Labels := by
      have hz : ∀ j, raw23270 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23270step0 = (fun i j => raw23270 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23270step0 raw23270; decide +kernel
      have hl : raw23270step0Labels = raw23270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23270 raw23270Labels permutation434 hz
    mixedMoment B raw23270step0 raw23270step0Labels = mixedMoment B raw23270step1 raw23270step1Labels := by
      have hz : ∀ j, raw23270step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23270step1 = (fun i j => raw23270step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23270step1 raw23270step0; decide +kernel
      have hl : raw23270step1Labels = raw23270step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23270step0 raw23270step0Labels permutation80 hz
    mixedMoment B raw23270step1 raw23270step1Labels = mixedMoment B raw23270step2 raw23270step2Labels := by
      have ha : raw23270step2 = (fun i j => raw23270step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23270step2 raw23270step1; decide +kernel
      have hl : raw23270step2Labels = raw23270step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23270step1 raw23270step1Labels permutation9 permutation6
    mixedMoment B raw23270step2 raw23270step2Labels = mixedMoment B raw23270step3 raw23270step3Labels := by
      have ha : raw23270step3 = raw23270step2 := by apply Matrix.ext; unfold raw23270step3 raw23270step2; decide +kernel
      have hl : raw23270step2Labels = labelEmbedding9 ∘ raw23270step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23270step2 raw23270step2Labels raw23270step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

theorem canonical23271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23271 raw23271Labels = mixedMoment B node4273 node4273Labels := by
  calc
    mixedMoment B raw23271 raw23271Labels = mixedMoment B raw23271step0 raw23271step0Labels := by
      have hz : ∀ j, raw23271 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23271step0 = (fun i j => raw23271 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23271step0 raw23271; decide +kernel
      have hl : raw23271step0Labels = raw23271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23271 raw23271Labels permutation434 hz
    mixedMoment B raw23271step0 raw23271step0Labels = mixedMoment B raw23271step1 raw23271step1Labels := by
      have hz : ∀ j, raw23271step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23271step1 = (fun i j => raw23271step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23271step1 raw23271step0; decide +kernel
      have hl : raw23271step1Labels = raw23271step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23271step0 raw23271step0Labels permutation80 hz
    mixedMoment B raw23271step1 raw23271step1Labels = mixedMoment B raw23271step2 raw23271step2Labels := by
      have ha : raw23271step2 = (fun i j => raw23271step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23271step2 raw23271step1; decide +kernel
      have hl : raw23271step2Labels = raw23271step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23271step1 raw23271step1Labels permutation8 permutation6
    mixedMoment B raw23271step2 raw23271step2Labels = mixedMoment B raw23271step3 raw23271step3Labels := by
      have ha : raw23271step3 = raw23271step2 := by apply Matrix.ext; unfold raw23271step3 raw23271step2; decide +kernel
      have hl : raw23271step2Labels = labelEmbedding9 ∘ raw23271step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23271step2 raw23271step2Labels raw23271step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4273 node4273Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical183
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23477 raw23477Labels = mixedMoment B node4284 node4284Labels := by
  calc
    mixedMoment B raw23477 raw23477Labels = mixedMoment B raw23477step0 raw23477step0Labels := by
      have hz : ∀ j, raw23477 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23477step0 = (fun i j => raw23477 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23477step0 raw23477; decide +kernel
      have hl : raw23477step0Labels = raw23477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23477 raw23477Labels permutation434 hz
    mixedMoment B raw23477step0 raw23477step0Labels = mixedMoment B raw23477step1 raw23477step1Labels := by
      have hz : ∀ j, raw23477step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23477step1 = (fun i j => raw23477step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23477step1 raw23477step0; decide +kernel
      have hl : raw23477step1Labels = raw23477step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23477step0 raw23477step0Labels permutation80 hz
    mixedMoment B raw23477step1 raw23477step1Labels = mixedMoment B raw23477step2 raw23477step2Labels := by
      have hz : ∀ j, raw23477step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23477step2 = (fun i j => raw23477step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23477step2 raw23477step1; decide +kernel
      have hl : raw23477step2Labels = raw23477step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23477step1 raw23477step1Labels permutation14 hz
    mixedMoment B raw23477step2 raw23477step2Labels = mixedMoment B raw23477step3 raw23477step3Labels := by
      have ha : raw23477step3 = (fun i j => raw23477step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23477step3 raw23477step2; decide +kernel
      have hl : raw23477step3Labels = raw23477step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23477step2 raw23477step2Labels permutation3 permutation4
    mixedMoment B raw23477step3 raw23477step3Labels = mixedMoment B raw23477step4 raw23477step4Labels := by
      have ha : raw23477step4 = -raw23477step3 := by apply Matrix.ext; change ∀ i j, raw23477step4 i j = -(raw23477step3 i j); unfold raw23477step4 raw23477step3; decide +kernel
      have hl : raw23477step4Labels = raw23477step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23477step4 raw23477step4Labels = mixedMoment B raw23477step5 raw23477step5Labels := by
      have ha : raw23477step5 = raw23477step4 := by apply Matrix.ext; unfold raw23477step5 raw23477step4; decide +kernel
      have hl : raw23477step4Labels = labelEmbedding7 ∘ raw23477step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23477step4 raw23477step4Labels raw23477step5Labels labelEmbedding7 hl
    _ = mixedMoment B node4284 node4284Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical184
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23563 raw23563Labels = mixedMoment B node4273 node4273Labels := by
  calc
    mixedMoment B raw23563 raw23563Labels = mixedMoment B raw23563step0 raw23563step0Labels := by
      have hz : ∀ j, raw23563 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23563step0 = (fun i j => raw23563 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23563step0 raw23563; decide +kernel
      have hl : raw23563step0Labels = raw23563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23563 raw23563Labels permutation434 hz
    mixedMoment B raw23563step0 raw23563step0Labels = mixedMoment B raw23563step1 raw23563step1Labels := by
      have hz : ∀ j, raw23563step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23563step1 = (fun i j => raw23563step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23563step1 raw23563step0; decide +kernel
      have hl : raw23563step1Labels = raw23563step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23563step0 raw23563step0Labels permutation56 hz
    mixedMoment B raw23563step1 raw23563step1Labels = mixedMoment B raw23563step2 raw23563step2Labels := by
      have ha : raw23563step2 = (fun i j => raw23563step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23563step2 raw23563step1; decide +kernel
      have hl : raw23563step2Labels = raw23563step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23563step1 raw23563step1Labels permutation9 permutation6
    mixedMoment B raw23563step2 raw23563step2Labels = mixedMoment B raw23563step3 raw23563step3Labels := by
      have ha : raw23563step3 = raw23563step2 := by apply Matrix.ext; unfold raw23563step3 raw23563step2; decide +kernel
      have hl : raw23563step2Labels = labelEmbedding9 ∘ raw23563step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23563step2 raw23563step2Labels raw23563step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4273 node4273Labels := by rfl

theorem canonical23565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23565 raw23565Labels = mixedMoment B node4273 node4273Labels := by
  calc
    mixedMoment B raw23565 raw23565Labels = mixedMoment B raw23565step0 raw23565step0Labels := by
      have hz : ∀ j, raw23565 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23565step0 = (fun i j => raw23565 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23565step0 raw23565; decide +kernel
      have hl : raw23565step0Labels = raw23565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23565 raw23565Labels permutation346 hz
    mixedMoment B raw23565step0 raw23565step0Labels = mixedMoment B raw23565step1 raw23565step1Labels := by
      have hz : ∀ j, raw23565step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23565step1 = (fun i j => raw23565step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23565step1 raw23565step0; decide +kernel
      have hl : raw23565step1Labels = raw23565step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23565step0 raw23565step0Labels permutation56 hz
    mixedMoment B raw23565step1 raw23565step1Labels = mixedMoment B raw23565step2 raw23565step2Labels := by
      have ha : raw23565step2 = (fun i j => raw23565step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23565step2 raw23565step1; decide +kernel
      have hl : raw23565step2Labels = raw23565step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23565step1 raw23565step1Labels permutation9 permutation6
    mixedMoment B raw23565step2 raw23565step2Labels = mixedMoment B raw23565step3 raw23565step3Labels := by
      have ha : raw23565step3 = raw23565step2 := by apply Matrix.ext; unfold raw23565step3 raw23565step2; decide +kernel
      have hl : raw23565step2Labels = labelEmbedding9 ∘ raw23565step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23565step2 raw23565step2Labels raw23565step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4273 node4273Labels := by rfl

theorem canonical23568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23568 raw23568Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw23568 raw23568Labels = mixedMoment B raw23568step0 raw23568step0Labels := by
      have hz : ∀ j, raw23568 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23568step0 = (fun i j => raw23568 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23568step0 raw23568; decide +kernel
      have hl : raw23568step0Labels = raw23568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23568 raw23568Labels permutation434 hz
    mixedMoment B raw23568step0 raw23568step0Labels = mixedMoment B raw23568step1 raw23568step1Labels := by
      have hz : ∀ j, raw23568step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23568step1 = (fun i j => raw23568step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23568step1 raw23568step0; decide +kernel
      have hl : raw23568step1Labels = raw23568step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23568step0 raw23568step0Labels permutation80 hz
    mixedMoment B raw23568step1 raw23568step1Labels = mixedMoment B raw23568step2 raw23568step2Labels := by
      have hz : ∀ j, raw23568step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23568step2 = (fun i j => raw23568step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23568step2 raw23568step1; decide +kernel
      have hl : raw23568step2Labels = raw23568step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23568step1 raw23568step1Labels permutation14 hz
    mixedMoment B raw23568step2 raw23568step2Labels = mixedMoment B raw23568step3 raw23568step3Labels := by
      have hz : ∀ i, raw23568step2 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw23568step3 = (fun i j => raw23568step2 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw23568step3 raw23568step2; decide +kernel
      have hl : raw23568step3Labels = (fun j => raw23568step2Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23568step2 raw23568step2Labels permutation2 hz
    mixedMoment B raw23568step3 raw23568step3Labels = mixedMoment B raw23568step4 raw23568step4Labels := by
      have ha : raw23568step4 = -raw23568step3 := by apply Matrix.ext; change ∀ i j, raw23568step4 i j = -(raw23568step3 i j); unfold raw23568step4 raw23568step3; decide +kernel
      have hl : raw23568step4Labels = raw23568step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23568step4 raw23568step4Labels = mixedMoment B raw23568step5 raw23568step5Labels := by
      have ha : raw23568step5 = raw23568step4 := by apply Matrix.ext; unfold raw23568step5 raw23568step4; decide +kernel
      have hl : raw23568step4Labels = labelEmbedding3 ∘ raw23568step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23568step4 raw23568step4Labels raw23568step5Labels labelEmbedding3 hl
    _ = mixedMoment B node4071 node4071Labels := by rfl

theorem canonical23646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23646 raw23646Labels = mixedMoment B node4214 node4214Labels := by
  calc
    mixedMoment B raw23646 raw23646Labels = mixedMoment B raw23646step0 raw23646step0Labels := by
      have hz : ∀ j, raw23646 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23646step0 = (fun i j => raw23646 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23646step0 raw23646; decide +kernel
      have hl : raw23646step0Labels = raw23646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23646 raw23646Labels permutation346 hz
    mixedMoment B raw23646step0 raw23646step0Labels = mixedMoment B raw23646step1 raw23646step1Labels := by
      have ha : raw23646step1 = (fun i j => raw23646step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23646step1 raw23646step0; decide +kernel
      have hl : raw23646step1Labels = raw23646step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23646step0 raw23646step0Labels permutation38 permutation4
    mixedMoment B raw23646step1 raw23646step1Labels = mixedMoment B raw23646step2 raw23646step2Labels := by
      have ha : raw23646step2 = -raw23646step1 := by apply Matrix.ext; change ∀ i j, raw23646step2 i j = -(raw23646step1 i j); unfold raw23646step2 raw23646step1; decide +kernel
      have hl : raw23646step2Labels = raw23646step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23646step2 raw23646step2Labels = mixedMoment B raw23646step3 raw23646step3Labels := by
      have ha : raw23646step3 = raw23646step2 := by apply Matrix.ext; unfold raw23646step3 raw23646step2; decide +kernel
      have hl : raw23646step2Labels = labelEmbedding7 ∘ raw23646step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23646step2 raw23646step2Labels raw23646step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4214 node4214Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical185
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23765 raw23765Labels = mixedMoment B node4132 node4132Labels := by
  calc
    mixedMoment B raw23765 raw23765Labels = mixedMoment B raw23765step0 raw23765step0Labels := by
      have hz : ∀ j, raw23765 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23765step0 = (fun i j => raw23765 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23765step0 raw23765; decide +kernel
      have hl : raw23765step0Labels = raw23765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23765 raw23765Labels permutation434 hz
    mixedMoment B raw23765step0 raw23765step0Labels = mixedMoment B raw23765step1 raw23765step1Labels := by
      have hz : ∀ j, raw23765step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23765step1 = (fun i j => raw23765step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23765step1 raw23765step0; decide +kernel
      have hl : raw23765step1Labels = raw23765step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23765step0 raw23765step0Labels permutation80 hz
    mixedMoment B raw23765step1 raw23765step1Labels = mixedMoment B raw23765step2 raw23765step2Labels := by
      have ha : raw23765step2 = (fun i j => raw23765step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23765step2 raw23765step1; decide +kernel
      have hl : raw23765step2Labels = raw23765step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23765step1 raw23765step1Labels permutation12 permutation4
    mixedMoment B raw23765step2 raw23765step2Labels = mixedMoment B raw23765step3 raw23765step3Labels := by
      have ha : raw23765step3 = -raw23765step2 := by apply Matrix.ext; change ∀ i j, raw23765step3 i j = -(raw23765step2 i j); unfold raw23765step3 raw23765step2; decide +kernel
      have hl : raw23765step3Labels = raw23765step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23765step3 raw23765step3Labels = mixedMoment B raw23765step4 raw23765step4Labels := by
      have ha : raw23765step4 = raw23765step3 := by apply Matrix.ext; unfold raw23765step4 raw23765step3; decide +kernel
      have hl : raw23765step3Labels = labelEmbedding7 ∘ raw23765step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23765step3 raw23765step3Labels raw23765step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4132 node4132Labels := by rfl

theorem canonical23766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23766 raw23766Labels = mixedMoment B node4223 node4223Labels := by
  calc
    mixedMoment B raw23766 raw23766Labels = mixedMoment B raw23766step0 raw23766step0Labels := by
      have hz : ∀ j, raw23766 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23766step0 = (fun i j => raw23766 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23766step0 raw23766; decide +kernel
      have hl : raw23766step0Labels = raw23766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23766 raw23766Labels permutation434 hz
    mixedMoment B raw23766step0 raw23766step0Labels = mixedMoment B raw23766step1 raw23766step1Labels := by
      have ha : raw23766step1 = (fun i j => raw23766step0 (permutation42 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23766step1 raw23766step0; decide +kernel
      have hl : raw23766step1Labels = raw23766step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23766step0 raw23766step0Labels permutation42 permutation4
    mixedMoment B raw23766step1 raw23766step1Labels = mixedMoment B raw23766step2 raw23766step2Labels := by
      have ha : raw23766step2 = -raw23766step1 := by apply Matrix.ext; change ∀ i j, raw23766step2 i j = -(raw23766step1 i j); unfold raw23766step2 raw23766step1; decide +kernel
      have hl : raw23766step2Labels = raw23766step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23766step2 raw23766step2Labels = mixedMoment B raw23766step3 raw23766step3Labels := by
      have ha : raw23766step3 = raw23766step2 := by apply Matrix.ext; unfold raw23766step3 raw23766step2; decide +kernel
      have hl : raw23766step2Labels = labelEmbedding7 ∘ raw23766step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23766step2 raw23766step2Labels raw23766step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4223 node4223Labels := by rfl

theorem canonical23767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23767 raw23767Labels = mixedMoment B node4223 node4223Labels := by
  calc
    mixedMoment B raw23767 raw23767Labels = mixedMoment B raw23767step0 raw23767step0Labels := by
      have hz : ∀ j, raw23767 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23767step0 = (fun i j => raw23767 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23767step0 raw23767; decide +kernel
      have hl : raw23767step0Labels = raw23767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23767 raw23767Labels permutation346 hz
    mixedMoment B raw23767step0 raw23767step0Labels = mixedMoment B raw23767step1 raw23767step1Labels := by
      have ha : raw23767step1 = (fun i j => raw23767step0 (permutation42 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23767step1 raw23767step0; decide +kernel
      have hl : raw23767step1Labels = raw23767step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23767step0 raw23767step0Labels permutation42 permutation4
    mixedMoment B raw23767step1 raw23767step1Labels = mixedMoment B raw23767step2 raw23767step2Labels := by
      have ha : raw23767step2 = -raw23767step1 := by apply Matrix.ext; change ∀ i j, raw23767step2 i j = -(raw23767step1 i j); unfold raw23767step2 raw23767step1; decide +kernel
      have hl : raw23767step2Labels = raw23767step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23767step2 raw23767step2Labels = mixedMoment B raw23767step3 raw23767step3Labels := by
      have ha : raw23767step3 = raw23767step2 := by apply Matrix.ext; unfold raw23767step3 raw23767step2; decide +kernel
      have hl : raw23767step2Labels = labelEmbedding7 ∘ raw23767step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23767step2 raw23767step2Labels raw23767step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4223 node4223Labels := by rfl

theorem canonical23768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23768 raw23768Labels = mixedMoment B node4115 node4115Labels := by
  calc
    mixedMoment B raw23768 raw23768Labels = mixedMoment B raw23768step0 raw23768step0Labels := by
      have hz : ∀ j, raw23768 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23768step0 = (fun i j => raw23768 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23768step0 raw23768; decide +kernel
      have hl : raw23768step0Labels = raw23768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23768 raw23768Labels permutation434 hz
    mixedMoment B raw23768step0 raw23768step0Labels = mixedMoment B raw23768step1 raw23768step1Labels := by
      have ha : raw23768step1 = (fun i j => raw23768step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23768step1 raw23768step0; decide +kernel
      have hl : raw23768step1Labels = raw23768step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23768step0 raw23768step0Labels permutation33 permutation4
    mixedMoment B raw23768step1 raw23768step1Labels = mixedMoment B raw23768step2 raw23768step2Labels := by
      have ha : raw23768step2 = -raw23768step1 := by apply Matrix.ext; change ∀ i j, raw23768step2 i j = -(raw23768step1 i j); unfold raw23768step2 raw23768step1; decide +kernel
      have hl : raw23768step2Labels = raw23768step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23768step2 raw23768step2Labels = mixedMoment B raw23768step3 raw23768step3Labels := by
      have ha : raw23768step3 = raw23768step2 := by apply Matrix.ext; unfold raw23768step3 raw23768step2; decide +kernel
      have hl : raw23768step2Labels = labelEmbedding7 ∘ raw23768step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23768step2 raw23768step2Labels raw23768step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4115 node4115Labels := by rfl

theorem canonical23769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23769 raw23769Labels = mixedMoment B node4207 node4207Labels := by
  calc
    mixedMoment B raw23769 raw23769Labels = mixedMoment B raw23769step0 raw23769step0Labels := by
      have ha : raw23769step0 = (fun i j => raw23769 (permutation201 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23769step0 raw23769; decide +kernel
      have hl : raw23769step0Labels = raw23769Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23769 raw23769Labels permutation201 permutation4
    mixedMoment B raw23769step0 raw23769step0Labels = mixedMoment B raw23769step1 raw23769step1Labels := by
      have ha : raw23769step1 = -raw23769step0 := by apply Matrix.ext; change ∀ i j, raw23769step1 i j = -(raw23769step0 i j); unfold raw23769step1 raw23769step0; decide +kernel
      have hl : raw23769step1Labels = raw23769step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23769step1 raw23769step1Labels = mixedMoment B raw23769step2 raw23769step2Labels := by
      have ha : raw23769step2 = raw23769step1 := by apply Matrix.ext; unfold raw23769step2 raw23769step1; decide +kernel
      have hl : raw23769step1Labels = labelEmbedding7 ∘ raw23769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23769step1 raw23769step1Labels raw23769step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4207 node4207Labels := by rfl

theorem canonical23770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23770 raw23770Labels = mixedMoment B node4115 node4115Labels := by
  calc
    mixedMoment B raw23770 raw23770Labels = mixedMoment B raw23770step0 raw23770step0Labels := by
      have hz : ∀ j, raw23770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23770step0 = (fun i j => raw23770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23770step0 raw23770; decide +kernel
      have hl : raw23770step0Labels = raw23770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23770 raw23770Labels permutation346 hz
    mixedMoment B raw23770step0 raw23770step0Labels = mixedMoment B raw23770step1 raw23770step1Labels := by
      have ha : raw23770step1 = (fun i j => raw23770step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23770step1 raw23770step0; decide +kernel
      have hl : raw23770step1Labels = raw23770step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23770step0 raw23770step0Labels permutation33 permutation4
    mixedMoment B raw23770step1 raw23770step1Labels = mixedMoment B raw23770step2 raw23770step2Labels := by
      have ha : raw23770step2 = -raw23770step1 := by apply Matrix.ext; change ∀ i j, raw23770step2 i j = -(raw23770step1 i j); unfold raw23770step2 raw23770step1; decide +kernel
      have hl : raw23770step2Labels = raw23770step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23770step2 raw23770step2Labels = mixedMoment B raw23770step3 raw23770step3Labels := by
      have ha : raw23770step3 = raw23770step2 := by apply Matrix.ext; unfold raw23770step3 raw23770step2; decide +kernel
      have hl : raw23770step2Labels = labelEmbedding7 ∘ raw23770step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23770step2 raw23770step2Labels raw23770step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4115 node4115Labels := by rfl

theorem canonical23771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23771 raw23771Labels = mixedMoment B node4207 node4207Labels := by
  calc
    mixedMoment B raw23771 raw23771Labels = mixedMoment B raw23771step0 raw23771step0Labels := by
      have ha : raw23771step0 = (fun i j => raw23771 (permutation177 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23771step0 raw23771; decide +kernel
      have hl : raw23771step0Labels = raw23771Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23771 raw23771Labels permutation177 permutation4
    mixedMoment B raw23771step0 raw23771step0Labels = mixedMoment B raw23771step1 raw23771step1Labels := by
      have ha : raw23771step1 = -raw23771step0 := by apply Matrix.ext; change ∀ i j, raw23771step1 i j = -(raw23771step0 i j); unfold raw23771step1 raw23771step0; decide +kernel
      have hl : raw23771step1Labels = raw23771step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23771step1 raw23771step1Labels = mixedMoment B raw23771step2 raw23771step2Labels := by
      have ha : raw23771step2 = raw23771step1 := by apply Matrix.ext; unfold raw23771step2 raw23771step1; decide +kernel
      have hl : raw23771step1Labels = labelEmbedding7 ∘ raw23771step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23771step1 raw23771step1Labels raw23771step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4207 node4207Labels := by rfl

theorem canonical23772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23772 raw23772Labels = mixedMoment B node4121 node4121Labels := by
  calc
    mixedMoment B raw23772 raw23772Labels = mixedMoment B raw23772step0 raw23772step0Labels := by
      have hz : ∀ j, raw23772 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23772step0 = (fun i j => raw23772 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23772step0 raw23772; decide +kernel
      have hl : raw23772step0Labels = raw23772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23772 raw23772Labels permutation434 hz
    mixedMoment B raw23772step0 raw23772step0Labels = mixedMoment B raw23772step1 raw23772step1Labels := by
      have hz : ∀ j, raw23772step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23772step1 = (fun i j => raw23772step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23772step1 raw23772step0; decide +kernel
      have hl : raw23772step1Labels = raw23772step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23772step0 raw23772step0Labels permutation80 hz
    mixedMoment B raw23772step1 raw23772step1Labels = mixedMoment B raw23772step2 raw23772step2Labels := by
      have ha : raw23772step2 = (fun i j => raw23772step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23772step2 raw23772step1; decide +kernel
      have hl : raw23772step2Labels = raw23772step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23772step1 raw23772step1Labels permutation9 permutation4
    mixedMoment B raw23772step2 raw23772step2Labels = mixedMoment B raw23772step3 raw23772step3Labels := by
      have ha : raw23772step3 = -raw23772step2 := by apply Matrix.ext; change ∀ i j, raw23772step3 i j = -(raw23772step2 i j); unfold raw23772step3 raw23772step2; decide +kernel
      have hl : raw23772step3Labels = raw23772step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23772step3 raw23772step3Labels = mixedMoment B raw23772step4 raw23772step4Labels := by
      have ha : raw23772step4 = raw23772step3 := by apply Matrix.ext; unfold raw23772step4 raw23772step3; decide +kernel
      have hl : raw23772step3Labels = labelEmbedding7 ∘ raw23772step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23772step3 raw23772step3Labels raw23772step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4121 node4121Labels := by rfl

theorem canonical23773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23773 raw23773Labels = mixedMoment B node4212 node4212Labels := by
  calc
    mixedMoment B raw23773 raw23773Labels = mixedMoment B raw23773step0 raw23773step0Labels := by
      have hz : ∀ j, raw23773 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23773step0 = (fun i j => raw23773 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23773step0 raw23773; decide +kernel
      have hl : raw23773step0Labels = raw23773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23773 raw23773Labels permutation434 hz
    mixedMoment B raw23773step0 raw23773step0Labels = mixedMoment B raw23773step1 raw23773step1Labels := by
      have ha : raw23773step1 = (fun i j => raw23773step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23773step1 raw23773step0; decide +kernel
      have hl : raw23773step1Labels = raw23773step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23773step0 raw23773step0Labels permutation39 permutation4
    mixedMoment B raw23773step1 raw23773step1Labels = mixedMoment B raw23773step2 raw23773step2Labels := by
      have ha : raw23773step2 = -raw23773step1 := by apply Matrix.ext; change ∀ i j, raw23773step2 i j = -(raw23773step1 i j); unfold raw23773step2 raw23773step1; decide +kernel
      have hl : raw23773step2Labels = raw23773step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23773step2 raw23773step2Labels = mixedMoment B raw23773step3 raw23773step3Labels := by
      have ha : raw23773step3 = raw23773step2 := by apply Matrix.ext; unfold raw23773step3 raw23773step2; decide +kernel
      have hl : raw23773step2Labels = labelEmbedding7 ∘ raw23773step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23773step2 raw23773step2Labels raw23773step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4212 node4212Labels := by rfl

theorem canonical23774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23774 raw23774Labels = mixedMoment B node4212 node4212Labels := by
  calc
    mixedMoment B raw23774 raw23774Labels = mixedMoment B raw23774step0 raw23774step0Labels := by
      have hz : ∀ j, raw23774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23774step0 = (fun i j => raw23774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23774step0 raw23774; decide +kernel
      have hl : raw23774step0Labels = raw23774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23774 raw23774Labels permutation346 hz
    mixedMoment B raw23774step0 raw23774step0Labels = mixedMoment B raw23774step1 raw23774step1Labels := by
      have ha : raw23774step1 = (fun i j => raw23774step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23774step1 raw23774step0; decide +kernel
      have hl : raw23774step1Labels = raw23774step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23774step0 raw23774step0Labels permutation39 permutation4
    mixedMoment B raw23774step1 raw23774step1Labels = mixedMoment B raw23774step2 raw23774step2Labels := by
      have ha : raw23774step2 = -raw23774step1 := by apply Matrix.ext; change ∀ i j, raw23774step2 i j = -(raw23774step1 i j); unfold raw23774step2 raw23774step1; decide +kernel
      have hl : raw23774step2Labels = raw23774step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23774step2 raw23774step2Labels = mixedMoment B raw23774step3 raw23774step3Labels := by
      have ha : raw23774step3 = raw23774step2 := by apply Matrix.ext; unfold raw23774step3 raw23774step2; decide +kernel
      have hl : raw23774step2Labels = labelEmbedding7 ∘ raw23774step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23774step2 raw23774step2Labels raw23774step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4212 node4212Labels := by rfl

theorem canonical23775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23775 raw23775Labels = mixedMoment B node4123 node4123Labels := by
  calc
    mixedMoment B raw23775 raw23775Labels = mixedMoment B raw23775step0 raw23775step0Labels := by
      have hz : ∀ j, raw23775 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23775step0 = (fun i j => raw23775 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23775step0 raw23775; decide +kernel
      have hl : raw23775step0Labels = raw23775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23775 raw23775Labels permutation434 hz
    mixedMoment B raw23775step0 raw23775step0Labels = mixedMoment B raw23775step1 raw23775step1Labels := by
      have hz : ∀ j, raw23775step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23775step1 = (fun i j => raw23775step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23775step1 raw23775step0; decide +kernel
      have hl : raw23775step1Labels = raw23775step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23775step0 raw23775step0Labels permutation80 hz
    mixedMoment B raw23775step1 raw23775step1Labels = mixedMoment B raw23775step2 raw23775step2Labels := by
      have ha : raw23775step2 = (fun i j => raw23775step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23775step2 raw23775step1; decide +kernel
      have hl : raw23775step2Labels = raw23775step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23775step1 raw23775step1Labels permutation8 permutation4
    mixedMoment B raw23775step2 raw23775step2Labels = mixedMoment B raw23775step3 raw23775step3Labels := by
      have ha : raw23775step3 = -raw23775step2 := by apply Matrix.ext; change ∀ i j, raw23775step3 i j = -(raw23775step2 i j); unfold raw23775step3 raw23775step2; decide +kernel
      have hl : raw23775step3Labels = raw23775step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23775step3 raw23775step3Labels = mixedMoment B raw23775step4 raw23775step4Labels := by
      have ha : raw23775step4 = raw23775step3 := by apply Matrix.ext; unfold raw23775step4 raw23775step3; decide +kernel
      have hl : raw23775step3Labels = labelEmbedding7 ∘ raw23775step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23775step3 raw23775step3Labels raw23775step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4123 node4123Labels := by rfl

theorem canonical23776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23776 raw23776Labels = mixedMoment B node4214 node4214Labels := by
  calc
    mixedMoment B raw23776 raw23776Labels = mixedMoment B raw23776step0 raw23776step0Labels := by
      have hz : ∀ j, raw23776 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23776step0 = (fun i j => raw23776 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23776step0 raw23776; decide +kernel
      have hl : raw23776step0Labels = raw23776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23776 raw23776Labels permutation434 hz
    mixedMoment B raw23776step0 raw23776step0Labels = mixedMoment B raw23776step1 raw23776step1Labels := by
      have ha : raw23776step1 = (fun i j => raw23776step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23776step1 raw23776step0; decide +kernel
      have hl : raw23776step1Labels = raw23776step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23776step0 raw23776step0Labels permutation38 permutation4
    mixedMoment B raw23776step1 raw23776step1Labels = mixedMoment B raw23776step2 raw23776step2Labels := by
      have ha : raw23776step2 = -raw23776step1 := by apply Matrix.ext; change ∀ i j, raw23776step2 i j = -(raw23776step1 i j); unfold raw23776step2 raw23776step1; decide +kernel
      have hl : raw23776step2Labels = raw23776step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23776step2 raw23776step2Labels = mixedMoment B raw23776step3 raw23776step3Labels := by
      have ha : raw23776step3 = raw23776step2 := by apply Matrix.ext; unfold raw23776step3 raw23776step2; decide +kernel
      have hl : raw23776step2Labels = labelEmbedding7 ∘ raw23776step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23776step2 raw23776step2Labels raw23776step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4214 node4214Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw717 raw717Labels = mixedMoment B node4115 node4115Labels := by
  calc
    mixedMoment B raw717 raw717Labels = mixedMoment B raw717step0 raw717step0Labels := by
      have ha : raw717step0 = (fun i j => raw717 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw717step0 raw717; decide +kernel
      have hl : raw717step0Labels = raw717Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw717 raw717Labels permutation32 permutation4
    mixedMoment B raw717step0 raw717step0Labels = mixedMoment B raw717step1 raw717step1Labels := by
      have ha : raw717step1 = raw717step0 := by apply Matrix.ext; unfold raw717step1 raw717step0; decide +kernel
      have hl : raw717step0Labels = labelEmbedding7 ∘ raw717step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw717step0 raw717step0Labels raw717step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4115 node4115Labels := by rfl

theorem canonical718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw718 raw718Labels = mixedMoment B node552 node552Labels := by
  calc
    mixedMoment B raw718 raw718Labels = mixedMoment B raw718step0 raw718step0Labels := by
      have ha : raw718step0 = (fun i j => raw718 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw718step0 raw718; decide +kernel
      have hl : raw718step0Labels = raw718Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw718 raw718Labels permutation32 permutation4
    _ = mixedMoment B node552 node552Labels := by rfl

theorem canonical719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw719 raw719Labels = mixedMoment B node660 node660Labels := by
  calc
    mixedMoment B raw719 raw719Labels = mixedMoment B raw719step0 raw719step0Labels := by
      have ha : raw719step0 = (fun i j => raw719 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw719step0 raw719; decide +kernel
      have hl : raw719step0Labels = raw719Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw719 raw719Labels permutation32 permutation6
    mixedMoment B raw719step0 raw719step0Labels = mixedMoment B raw719step1 raw719step1Labels := by
      have ha : raw719step1 = -raw719step0 := by apply Matrix.ext; change ∀ i j, raw719step1 i j = -(raw719step0 i j); unfold raw719step1 raw719step0; decide +kernel
      have hl : raw719step1Labels = raw719step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw719step1 raw719step1Labels = mixedMoment B raw719step2 raw719step2Labels := by
      have ha : raw719step2 = raw719step1 := by apply Matrix.ext; unfold raw719step2 raw719step1; decide +kernel
      have hl : raw719step1Labels = labelEmbedding1 ∘ raw719step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw719step1 raw719step1Labels raw719step2Labels labelEmbedding1 hl
    _ = mixedMoment B node660 node660Labels := by rfl

theorem canonical726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw726 raw726Labels = mixedMoment B node4121 node4121Labels := by
  calc
    mixedMoment B raw726 raw726Labels = mixedMoment B raw726step0 raw726step0Labels := by
      have ha : raw726step0 = (fun i j => raw726 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw726step0 raw726; decide +kernel
      have hl : raw726step0Labels = raw726Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw726 raw726Labels permutation8 permutation4
    mixedMoment B raw726step0 raw726step0Labels = mixedMoment B raw726step1 raw726step1Labels := by
      have ha : raw726step1 = raw726step0 := by apply Matrix.ext; unfold raw726step1 raw726step0; decide +kernel
      have hl : raw726step0Labels = labelEmbedding7 ∘ raw726step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw726step0 raw726step0Labels raw726step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4121 node4121Labels := by rfl

theorem canonical727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw727 raw727Labels = mixedMoment B node555 node555Labels := by
  calc
    mixedMoment B raw727 raw727Labels = mixedMoment B raw727step0 raw727step0Labels := by
      have ha : raw727step0 = (fun i j => raw727 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw727step0 raw727; decide +kernel
      have hl : raw727step0Labels = raw727Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw727 raw727Labels permutation8 permutation4
    _ = mixedMoment B node555 node555Labels := by rfl

theorem canonical728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw728 raw728Labels = mixedMoment B node671 node671Labels := by
  calc
    mixedMoment B raw728 raw728Labels = mixedMoment B raw728step0 raw728step0Labels := by
      have ha : raw728step0 = (fun i j => raw728 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw728step0 raw728; decide +kernel
      have hl : raw728step0Labels = raw728Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw728 raw728Labels permutation8 permutation6
    mixedMoment B raw728step0 raw728step0Labels = mixedMoment B raw728step1 raw728step1Labels := by
      have ha : raw728step1 = -raw728step0 := by apply Matrix.ext; change ∀ i j, raw728step1 i j = -(raw728step0 i j); unfold raw728step1 raw728step0; decide +kernel
      have hl : raw728step1Labels = raw728step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw728step1 raw728step1Labels = mixedMoment B raw728step2 raw728step2Labels := by
      have ha : raw728step2 = raw728step1 := by apply Matrix.ext; unfold raw728step2 raw728step1; decide +kernel
      have hl : raw728step1Labels = labelEmbedding1 ∘ raw728step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw728step1 raw728step1Labels raw728step2Labels labelEmbedding1 hl
    _ = mixedMoment B node671 node671Labels := by rfl

theorem canonical741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw741 raw741Labels = mixedMoment B node4132 node4132Labels := by
  calc
    mixedMoment B raw741 raw741Labels = mixedMoment B raw741step0 raw741step0Labels := by
      have ha : raw741step0 = (fun i j => raw741 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw741step0 raw741; decide +kernel
      have hl : raw741step0Labels = raw741Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw741 raw741Labels permutation8 permutation4
    mixedMoment B raw741step0 raw741step0Labels = mixedMoment B raw741step1 raw741step1Labels := by
      have ha : raw741step1 = raw741step0 := by apply Matrix.ext; unfold raw741step1 raw741step0; decide +kernel
      have hl : raw741step0Labels = labelEmbedding7 ∘ raw741step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw741step0 raw741step0Labels raw741step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4132 node4132Labels := by rfl

theorem canonical742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw742 raw742Labels = mixedMoment B node562 node562Labels := by
  calc
    mixedMoment B raw742 raw742Labels = mixedMoment B raw742step0 raw742step0Labels := by
      have ha : raw742step0 = (fun i j => raw742 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw742step0 raw742; decide +kernel
      have hl : raw742step0Labels = raw742Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw742 raw742Labels permutation8 permutation4
    _ = mixedMoment B node562 node562Labels := by rfl

theorem canonical743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw743 raw743Labels = mixedMoment B node679 node679Labels := by
  calc
    mixedMoment B raw743 raw743Labels = mixedMoment B raw743step0 raw743step0Labels := by
      have ha : raw743step0 = (fun i j => raw743 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw743step0 raw743; decide +kernel
      have hl : raw743step0Labels = raw743Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw743 raw743Labels permutation10 permutation6
    mixedMoment B raw743step0 raw743step0Labels = mixedMoment B raw743step1 raw743step1Labels := by
      have ha : raw743step1 = -raw743step0 := by apply Matrix.ext; change ∀ i j, raw743step1 i j = -(raw743step0 i j); unfold raw743step1 raw743step0; decide +kernel
      have hl : raw743step1Labels = raw743step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw743step1 raw743step1Labels = mixedMoment B raw743step2 raw743step2Labels := by
      have ha : raw743step2 = raw743step1 := by apply Matrix.ext; unfold raw743step2 raw743step1; decide +kernel
      have hl : raw743step1Labels = labelEmbedding1 ∘ raw743step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw743step1 raw743step1Labels raw743step2Labels labelEmbedding1 hl
    _ = mixedMoment B node679 node679Labels := by rfl

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

theorem canonical885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw885 raw885Labels = mixedMoment B node4207 node4207Labels := by
  calc
    mixedMoment B raw885 raw885Labels = mixedMoment B raw885step0 raw885step0Labels := by
      have ha : raw885step0 = (fun i j => raw885 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw885step0 raw885; decide +kernel
      have hl : raw885step0Labels = raw885Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw885 raw885Labels permutation152 permutation4
    mixedMoment B raw885step0 raw885step0Labels = mixedMoment B raw885step1 raw885step1Labels := by
      have ha : raw885step1 = raw885step0 := by apply Matrix.ext; unfold raw885step1 raw885step0; decide +kernel
      have hl : raw885step0Labels = labelEmbedding7 ∘ raw885step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw885step0 raw885step0Labels raw885step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4207 node4207Labels := by rfl

theorem canonical886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw886 raw886Labels = mixedMoment B node710 node710Labels := by
  calc
    mixedMoment B raw886 raw886Labels = mixedMoment B raw886step0 raw886step0Labels := by
      have ha : raw886step0 = (fun i j => raw886 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw886step0 raw886; decide +kernel
      have hl : raw886step0Labels = raw886Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw886 raw886Labels permutation152 permutation4
    _ = mixedMoment B node710 node710Labels := by rfl

theorem canonical887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw887 raw887Labels = mixedMoment B node746 node746Labels := by
  calc
    mixedMoment B raw887 raw887Labels = mixedMoment B raw887step0 raw887step0Labels := by
      have ha : raw887step0 = (fun i j => raw887 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw887step0 raw887; decide +kernel
      have hl : raw887step0Labels = raw887Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw887 raw887Labels permutation152 permutation6
    mixedMoment B raw887step0 raw887step0Labels = mixedMoment B raw887step1 raw887step1Labels := by
      have ha : raw887step1 = -raw887step0 := by apply Matrix.ext; change ∀ i j, raw887step1 i j = -(raw887step0 i j); unfold raw887step1 raw887step0; decide +kernel
      have hl : raw887step1Labels = raw887step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw887step1 raw887step1Labels = mixedMoment B raw887step2 raw887step2Labels := by
      have ha : raw887step2 = raw887step1 := by apply Matrix.ext; unfold raw887step2 raw887step1; decide +kernel
      have hl : raw887step1Labels = labelEmbedding1 ∘ raw887step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw887step1 raw887step1Labels raw887step2Labels labelEmbedding1 hl
    _ = mixedMoment B node746 node746Labels := by rfl

theorem canonical894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw894 raw894Labels = mixedMoment B node4212 node4212Labels := by
  calc
    mixedMoment B raw894 raw894Labels = mixedMoment B raw894step0 raw894step0Labels := by
      have ha : raw894step0 = (fun i j => raw894 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw894step0 raw894; decide +kernel
      have hl : raw894step0Labels = raw894Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw894 raw894Labels permutation32 permutation4
    mixedMoment B raw894step0 raw894step0Labels = mixedMoment B raw894step1 raw894step1Labels := by
      have ha : raw894step1 = raw894step0 := by apply Matrix.ext; unfold raw894step1 raw894step0; decide +kernel
      have hl : raw894step0Labels = labelEmbedding7 ∘ raw894step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw894step0 raw894step0Labels raw894step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4212 node4212Labels := by rfl

theorem canonical895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw895 raw895Labels = mixedMoment B node715 node715Labels := by
  calc
    mixedMoment B raw895 raw895Labels = mixedMoment B raw895step0 raw895step0Labels := by
      have ha : raw895step0 = (fun i j => raw895 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw895step0 raw895; decide +kernel
      have hl : raw895step0Labels = raw895Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw895 raw895Labels permutation32 permutation4
    _ = mixedMoment B node715 node715Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw896 raw896Labels = mixedMoment B node753 node753Labels := by
  calc
    mixedMoment B raw896 raw896Labels = mixedMoment B raw896step0 raw896step0Labels := by
      have ha : raw896step0 = (fun i j => raw896 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw896step0 raw896; decide +kernel
      have hl : raw896step0Labels = raw896Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw896 raw896Labels permutation32 permutation6
    mixedMoment B raw896step0 raw896step0Labels = mixedMoment B raw896step1 raw896step1Labels := by
      have ha : raw896step1 = -raw896step0 := by apply Matrix.ext; change ∀ i j, raw896step1 i j = -(raw896step0 i j); unfold raw896step1 raw896step0; decide +kernel
      have hl : raw896step1Labels = raw896step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw896step1 raw896step1Labels = mixedMoment B raw896step2 raw896step2Labels := by
      have ha : raw896step2 = raw896step1 := by apply Matrix.ext; unfold raw896step2 raw896step1; decide +kernel
      have hl : raw896step1Labels = labelEmbedding1 ∘ raw896step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw896step1 raw896step1Labels raw896step2Labels labelEmbedding1 hl
    _ = mixedMoment B node753 node753Labels := by rfl

theorem canonical909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw909 raw909Labels = mixedMoment B node4223 node4223Labels := by
  calc
    mixedMoment B raw909 raw909Labels = mixedMoment B raw909step0 raw909step0Labels := by
      have ha : raw909step0 = (fun i j => raw909 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw909step0 raw909; decide +kernel
      have hl : raw909step0Labels = raw909Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw909 raw909Labels permutation32 permutation4
    mixedMoment B raw909step0 raw909step0Labels = mixedMoment B raw909step1 raw909step1Labels := by
      have ha : raw909step1 = raw909step0 := by apply Matrix.ext; unfold raw909step1 raw909step0; decide +kernel
      have hl : raw909step0Labels = labelEmbedding7 ∘ raw909step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw909step0 raw909step0Labels raw909step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4223 node4223Labels := by rfl

theorem canonical910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw910 raw910Labels = mixedMoment B node724 node724Labels := by
  calc
    mixedMoment B raw910 raw910Labels = mixedMoment B raw910step0 raw910step0Labels := by
      have ha : raw910step0 = (fun i j => raw910 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw910step0 raw910; decide +kernel
      have hl : raw910step0Labels = raw910Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw910 raw910Labels permutation32 permutation4
    _ = mixedMoment B node724 node724Labels := by rfl

theorem canonical911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw911 raw911Labels = mixedMoment B node758 node758Labels := by
  calc
    mixedMoment B raw911 raw911Labels = mixedMoment B raw911step0 raw911step0Labels := by
      have ha : raw911step0 = (fun i j => raw911 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw911step0 raw911; decide +kernel
      have hl : raw911step0Labels = raw911Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw911 raw911Labels permutation34 permutation6
    mixedMoment B raw911step0 raw911step0Labels = mixedMoment B raw911step1 raw911step1Labels := by
      have ha : raw911step1 = -raw911step0 := by apply Matrix.ext; change ∀ i j, raw911step1 i j = -(raw911step0 i j); unfold raw911step1 raw911step0; decide +kernel
      have hl : raw911step1Labels = raw911step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw911step1 raw911step1Labels = mixedMoment B raw911step2 raw911step2Labels := by
      have ha : raw911step2 = raw911step1 := by apply Matrix.ext; unfold raw911step2 raw911step1; decide +kernel
      have hl : raw911step1Labels = labelEmbedding1 ∘ raw911step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw911step1 raw911step1Labels raw911step2Labels labelEmbedding1 hl
    _ = mixedMoment B node758 node758Labels := by rfl

theorem canonical981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw981 raw981Labels = mixedMoment B node4255 node4255Labels := by
  calc
    mixedMoment B raw981 raw981Labels = mixedMoment B raw981step0 raw981step0Labels := by
      have ha : raw981step0 = (fun i j => raw981 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw981step0 raw981; decide +kernel
      have hl : raw981step0Labels = raw981Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw981 raw981Labels permutation32 permutation4
    mixedMoment B raw981step0 raw981step0Labels = mixedMoment B raw981step1 raw981step1Labels := by
      have ha : raw981step1 = raw981step0 := by apply Matrix.ext; unfold raw981step1 raw981step0; decide +kernel
      have hl : raw981step0Labels = labelEmbedding7 ∘ raw981step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw981step0 raw981step0Labels raw981step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4255 node4255Labels := by rfl

theorem canonical982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw982 raw982Labels = mixedMoment B node789 node789Labels := by
  calc
    mixedMoment B raw982 raw982Labels = mixedMoment B raw982step0 raw982step0Labels := by
      have ha : raw982step0 = (fun i j => raw982 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw982step0 raw982; decide +kernel
      have hl : raw982step0Labels = raw982Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw982 raw982Labels permutation32 permutation4
    _ = mixedMoment B node789 node789Labels := by rfl

theorem canonical983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw983 raw983Labels = mixedMoment B node823 node823Labels := by
  calc
    mixedMoment B raw983 raw983Labels = mixedMoment B raw983step0 raw983step0Labels := by
      have ha : raw983step0 = (fun i j => raw983 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw983step0 raw983; decide +kernel
      have hl : raw983step0Labels = raw983Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw983 raw983Labels permutation44 permutation6
    mixedMoment B raw983step0 raw983step0Labels = mixedMoment B raw983step1 raw983step1Labels := by
      have ha : raw983step1 = -raw983step0 := by apply Matrix.ext; change ∀ i j, raw983step1 i j = -(raw983step0 i j); unfold raw983step1 raw983step0; decide +kernel
      have hl : raw983step1Labels = raw983step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw983step1 raw983step1Labels = mixedMoment B raw983step2 raw983step2Labels := by
      have ha : raw983step2 = raw983step1 := by apply Matrix.ext; unfold raw983step2 raw983step1; decide +kernel
      have hl : raw983step1Labels = labelEmbedding1 ∘ raw983step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw983step1 raw983step1Labels raw983step2Labels labelEmbedding1 hl
    _ = mixedMoment B node823 node823Labels := by rfl

theorem canonical984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw984 raw984Labels = mixedMoment B node4256 node4256Labels := by
  calc
    mixedMoment B raw984 raw984Labels = mixedMoment B raw984step0 raw984step0Labels := by
      have ha : raw984step0 = (fun i j => raw984 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw984step0 raw984; decide +kernel
      have hl : raw984step0Labels = raw984Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw984 raw984Labels permutation32 permutation4
    mixedMoment B raw984step0 raw984step0Labels = mixedMoment B raw984step1 raw984step1Labels := by
      have ha : raw984step1 = raw984step0 := by apply Matrix.ext; unfold raw984step1 raw984step0; decide +kernel
      have hl : raw984step0Labels = labelEmbedding7 ∘ raw984step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw984step0 raw984step0Labels raw984step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4256 node4256Labels := by rfl

theorem canonical985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw985 raw985Labels = mixedMoment B node790 node790Labels := by
  calc
    mixedMoment B raw985 raw985Labels = mixedMoment B raw985step0 raw985step0Labels := by
      have ha : raw985step0 = (fun i j => raw985 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw985step0 raw985; decide +kernel
      have hl : raw985step0Labels = raw985Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw985 raw985Labels permutation32 permutation4
    _ = mixedMoment B node790 node790Labels := by rfl

theorem canonical986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw986 raw986Labels = mixedMoment B node848 node848Labels := by
  calc
    mixedMoment B raw986 raw986Labels = mixedMoment B raw986step0 raw986step0Labels := by
      have ha : raw986step0 = (fun i j => raw986 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw986step0 raw986; decide +kernel
      have hl : raw986step0Labels = raw986Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw986 raw986Labels permutation32 permutation6
    mixedMoment B raw986step0 raw986step0Labels = mixedMoment B raw986step1 raw986step1Labels := by
      have ha : raw986step1 = -raw986step0 := by apply Matrix.ext; change ∀ i j, raw986step1 i j = -(raw986step0 i j); unfold raw986step1 raw986step0; decide +kernel
      have hl : raw986step1Labels = raw986step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw986step1 raw986step1Labels = mixedMoment B raw986step2 raw986step2Labels := by
      have ha : raw986step2 = raw986step1 := by apply Matrix.ext; unfold raw986step2 raw986step1; decide +kernel
      have hl : raw986step1Labels = labelEmbedding1 ∘ raw986step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw986step1 raw986step1Labels raw986step2Labels labelEmbedding1 hl
    _ = mixedMoment B node848 node848Labels := by rfl

theorem canonical999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw999 raw999Labels = mixedMoment B node4272 node4272Labels := by
  calc
    mixedMoment B raw999 raw999Labels = mixedMoment B raw999step0 raw999step0Labels := by
      have ha : raw999step0 = (fun i j => raw999 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw999step0 raw999; decide +kernel
      have hl : raw999step0Labels = raw999Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw999 raw999Labels permutation8 permutation4
    mixedMoment B raw999step0 raw999step0Labels = mixedMoment B raw999step1 raw999step1Labels := by
      have ha : raw999step1 = raw999step0 := by apply Matrix.ext; unfold raw999step1 raw999step0; decide +kernel
      have hl : raw999step0Labels = labelEmbedding7 ∘ raw999step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw999step0 raw999step0Labels raw999step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4272 node4272Labels := by rfl

theorem canonical1000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1000 raw1000Labels = mixedMoment B node815 node815Labels := by
  calc
    mixedMoment B raw1000 raw1000Labels = mixedMoment B raw1000step0 raw1000step0Labels := by
      have ha : raw1000step0 = (fun i j => raw1000 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1000step0 raw1000; decide +kernel
      have hl : raw1000step0Labels = raw1000Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1000 raw1000Labels permutation8 permutation4
    _ = mixedMoment B node815 node815Labels := by rfl

theorem canonical1001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1001 raw1001Labels = mixedMoment B node826 node826Labels := by
  calc
    mixedMoment B raw1001 raw1001Labels = mixedMoment B raw1001step0 raw1001step0Labels := by
      have ha : raw1001step0 = (fun i j => raw1001 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1001step0 raw1001; decide +kernel
      have hl : raw1001step0Labels = raw1001Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1001 raw1001Labels permutation10 permutation6
    mixedMoment B raw1001step0 raw1001step0Labels = mixedMoment B raw1001step1 raw1001step1Labels := by
      have ha : raw1001step1 = -raw1001step0 := by apply Matrix.ext; change ∀ i j, raw1001step1 i j = -(raw1001step0 i j); unfold raw1001step1 raw1001step0; decide +kernel
      have hl : raw1001step1Labels = raw1001step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1001step1 raw1001step1Labels = mixedMoment B raw1001step2 raw1001step2Labels := by
      have ha : raw1001step2 = raw1001step1 := by apply Matrix.ext; unfold raw1001step2 raw1001step1; decide +kernel
      have hl : raw1001step1Labels = labelEmbedding1 ∘ raw1001step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1001step1 raw1001step1Labels raw1001step2Labels labelEmbedding1 hl
    _ = mixedMoment B node826 node826Labels := by rfl

theorem canonical1008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1008 raw1008Labels = mixedMoment B node4278 node4278Labels := by
  calc
    mixedMoment B raw1008 raw1008Labels = mixedMoment B raw1008step0 raw1008step0Labels := by
      have ha : raw1008step0 = (fun i j => raw1008 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1008step0 raw1008; decide +kernel
      have hl : raw1008step0Labels = raw1008Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1008 raw1008Labels permutation8 permutation4
    mixedMoment B raw1008step0 raw1008step0Labels = mixedMoment B raw1008step1 raw1008step1Labels := by
      have ha : raw1008step1 = raw1008step0 := by apply Matrix.ext; unfold raw1008step1 raw1008step0; decide +kernel
      have hl : raw1008step0Labels = labelEmbedding7 ∘ raw1008step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1008step0 raw1008step0Labels raw1008step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4278 node4278Labels := by rfl

theorem canonical1009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1009 raw1009Labels = mixedMoment B node830 node830Labels := by
  calc
    mixedMoment B raw1009 raw1009Labels = mixedMoment B raw1009step0 raw1009step0Labels := by
      have ha : raw1009step0 = (fun i j => raw1009 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1009step0 raw1009; decide +kernel
      have hl : raw1009step0Labels = raw1009Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1009 raw1009Labels permutation8 permutation4
    _ = mixedMoment B node830 node830Labels := by rfl

theorem canonical1010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1010 raw1010Labels = mixedMoment B node830 node830Labels := by
  calc
    mixedMoment B raw1010 raw1010Labels = mixedMoment B raw1010step0 raw1010step0Labels := by
      have ha : raw1010step0 = (fun i j => raw1010 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1010step0 raw1010; decide +kernel
      have hl : raw1010step0Labels = raw1010Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1010 raw1010Labels permutation10 permutation6
    mixedMoment B raw1010step0 raw1010step0Labels = mixedMoment B raw1010step1 raw1010step1Labels := by
      have ha : raw1010step1 = -raw1010step0 := by apply Matrix.ext; change ∀ i j, raw1010step1 i j = -(raw1010step0 i j); unfold raw1010step1 raw1010step0; decide +kernel
      have hl : raw1010step1Labels = raw1010step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1010step1 raw1010step1Labels = mixedMoment B raw1010step2 raw1010step2Labels := by
      have ha : raw1010step2 = raw1010step1 := by apply Matrix.ext; unfold raw1010step2 raw1010step1; decide +kernel
      have hl : raw1010step1Labels = labelEmbedding1 ∘ raw1010step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1010step1 raw1010step1Labels raw1010step2Labels labelEmbedding1 hl
    _ = mixedMoment B node830 node830Labels := by rfl

theorem canonical1011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1011 raw1011Labels = mixedMoment B node4279 node4279Labels := by
  calc
    mixedMoment B raw1011 raw1011Labels = mixedMoment B raw1011step0 raw1011step0Labels := by
      have ha : raw1011step0 = (fun i j => raw1011 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1011step0 raw1011; decide +kernel
      have hl : raw1011step0Labels = raw1011Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1011 raw1011Labels permutation8 permutation4
    mixedMoment B raw1011step0 raw1011step0Labels = mixedMoment B raw1011step1 raw1011step1Labels := by
      have ha : raw1011step1 = raw1011step0 := by apply Matrix.ext; unfold raw1011step1 raw1011step0; decide +kernel
      have hl : raw1011step0Labels = labelEmbedding7 ∘ raw1011step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1011step0 raw1011step0Labels raw1011step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4279 node4279Labels := by rfl

theorem canonical1012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1012 raw1012Labels = mixedMoment B node831 node831Labels := by
  calc
    mixedMoment B raw1012 raw1012Labels = mixedMoment B raw1012step0 raw1012step0Labels := by
      have ha : raw1012step0 = (fun i j => raw1012 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1012step0 raw1012; decide +kernel
      have hl : raw1012step0Labels = raw1012Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1012 raw1012Labels permutation8 permutation4
    _ = mixedMoment B node831 node831Labels := by rfl

theorem canonical1013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1013 raw1013Labels = mixedMoment B node858 node858Labels := by
  calc
    mixedMoment B raw1013 raw1013Labels = mixedMoment B raw1013step0 raw1013step0Labels := by
      have ha : raw1013step0 = (fun i j => raw1013 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1013step0 raw1013; decide +kernel
      have hl : raw1013step0Labels = raw1013Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1013 raw1013Labels permutation11 permutation6
    mixedMoment B raw1013step0 raw1013step0Labels = mixedMoment B raw1013step1 raw1013step1Labels := by
      have ha : raw1013step1 = -raw1013step0 := by apply Matrix.ext; change ∀ i j, raw1013step1 i j = -(raw1013step0 i j); unfold raw1013step1 raw1013step0; decide +kernel
      have hl : raw1013step1Labels = raw1013step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1013step1 raw1013step1Labels = mixedMoment B raw1013step2 raw1013step2Labels := by
      have ha : raw1013step2 = raw1013step1 := by apply Matrix.ext; unfold raw1013step2 raw1013step1; decide +kernel
      have hl : raw1013step1Labels = labelEmbedding1 ∘ raw1013step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1013step1 raw1013step1Labels raw1013step2Labels labelEmbedding1 hl
    _ = mixedMoment B node858 node858Labels := by rfl

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

theorem canonical1218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1218 raw1218Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw1218 raw1218Labels = mixedMoment B raw1218step0 raw1218step0Labels := by
      have ha : raw1218step0 = (fun i j => raw1218 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1218step0 raw1218; decide +kernel
      have hl : raw1218step0Labels = raw1218Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1218 raw1218Labels permutation32 permutation4
    mixedMoment B raw1218step0 raw1218step0Labels = mixedMoment B raw1218step1 raw1218step1Labels := by
      have ha : raw1218step1 = raw1218step0 := by apply Matrix.ext; unfold raw1218step1 raw1218step0; decide +kernel
      have hl : raw1218step0Labels = labelEmbedding7 ∘ raw1218step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1218step0 raw1218step0Labels raw1218step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

theorem canonical1219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1219 raw1219Labels = mixedMoment B node985 node985Labels := by
  calc
    mixedMoment B raw1219 raw1219Labels = mixedMoment B raw1219step0 raw1219step0Labels := by
      have ha : raw1219step0 = (fun i j => raw1219 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1219step0 raw1219; decide +kernel
      have hl : raw1219step0Labels = raw1219Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1219 raw1219Labels permutation32 permutation4
    _ = mixedMoment B node985 node985Labels := by rfl

theorem canonical1220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1220 raw1220Labels = mixedMoment B node1618 node1618Labels := by
  calc
    mixedMoment B raw1220 raw1220Labels = mixedMoment B raw1220step0 raw1220step0Labels := by
      have ha : raw1220step0 = (fun i j => raw1220 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1220step0 raw1220; decide +kernel
      have hl : raw1220step0Labels = raw1220Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1220 raw1220Labels permutation32 permutation6
    mixedMoment B raw1220step0 raw1220step0Labels = mixedMoment B raw1220step1 raw1220step1Labels := by
      have ha : raw1220step1 = -raw1220step0 := by apply Matrix.ext; change ∀ i j, raw1220step1 i j = -(raw1220step0 i j); unfold raw1220step1 raw1220step0; decide +kernel
      have hl : raw1220step1Labels = raw1220step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1220step1 raw1220step1Labels = mixedMoment B raw1220step2 raw1220step2Labels := by
      have ha : raw1220step2 = raw1220step1 := by apply Matrix.ext; unfold raw1220step2 raw1220step1; decide +kernel
      have hl : raw1220step1Labels = labelEmbedding1 ∘ raw1220step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1220step1 raw1220step1Labels raw1220step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1618 node1618Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4115 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4115 node4115Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node552 node552Labels + mixedMoment B node660 node660Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw717 singletonSmall4115
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4115) = raw717Labels := by decide +kernel
  rw [hl, canonical717 B hB] at h
  have hc0 : mixedMoment B raw717 (Fin.cases (0 : Fin 2) singletonSmall4115) =
      mixedMoment B node552 node552Labels := by
    have ha : raw717 = raw718 := by apply Matrix.ext; unfold raw717 raw718; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4115 = raw718Labels := by decide +kernel
    rw [ha, hj, canonical718 B hB]
  have hc1 : mixedMoment B raw717 (Fin.cases (1 : Fin 2) singletonSmall4115) =
      mixedMoment B node660 node660Labels := by
    have ha : raw717 = raw719 := by apply Matrix.ext; unfold raw717 raw719; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4115 = raw719Labels := by decide +kernel
    rw [ha, hj, canonical719 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4121 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4121 node4121Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node555 node555Labels + mixedMoment B node671 node671Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw726 singletonSmall4121
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4121) = raw726Labels := by decide +kernel
  rw [hl, canonical726 B hB] at h
  have hc0 : mixedMoment B raw726 (Fin.cases (0 : Fin 2) singletonSmall4121) =
      mixedMoment B node555 node555Labels := by
    have ha : raw726 = raw727 := by apply Matrix.ext; unfold raw726 raw727; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4121 = raw727Labels := by decide +kernel
    rw [ha, hj, canonical727 B hB]
  have hc1 : mixedMoment B raw726 (Fin.cases (1 : Fin 2) singletonSmall4121) =
      mixedMoment B node671 node671Labels := by
    have ha : raw726 = raw728 := by apply Matrix.ext; unfold raw726 raw728; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4121 = raw728Labels := by decide +kernel
    rw [ha, hj, canonical728 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4132 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4132 node4132Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node562 node562Labels + mixedMoment B node679 node679Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw741 singletonSmall4132
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4132) = raw741Labels := by decide +kernel
  rw [hl, canonical741 B hB] at h
  have hc0 : mixedMoment B raw741 (Fin.cases (0 : Fin 2) singletonSmall4132) =
      mixedMoment B node562 node562Labels := by
    have ha : raw741 = raw742 := by apply Matrix.ext; unfold raw741 raw742; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4132 = raw742Labels := by decide +kernel
    rw [ha, hj, canonical742 B hB]
  have hc1 : mixedMoment B raw741 (Fin.cases (1 : Fin 2) singletonSmall4132) =
      mixedMoment B node679 node679Labels := by
    have ha : raw741 = raw743 := by apply Matrix.ext; unfold raw741 raw743; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4132 = raw743Labels := by decide +kernel
    rw [ha, hj, canonical743 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4207 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4207 node4207Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node710 node710Labels + mixedMoment B node746 node746Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw885 singletonSmall4207
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4207) = raw885Labels := by decide +kernel
  rw [hl, canonical885 B hB] at h
  have hc0 : mixedMoment B raw885 (Fin.cases (0 : Fin 2) singletonSmall4207) =
      mixedMoment B node710 node710Labels := by
    have ha : raw885 = raw886 := by apply Matrix.ext; unfold raw885 raw886; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4207 = raw886Labels := by decide +kernel
    rw [ha, hj, canonical886 B hB]
  have hc1 : mixedMoment B raw885 (Fin.cases (1 : Fin 2) singletonSmall4207) =
      mixedMoment B node746 node746Labels := by
    have ha : raw885 = raw887 := by apply Matrix.ext; unfold raw885 raw887; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4207 = raw887Labels := by decide +kernel
    rw [ha, hj, canonical887 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4212 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4212 node4212Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node715 node715Labels + mixedMoment B node753 node753Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw894 singletonSmall4212
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4212) = raw894Labels := by decide +kernel
  rw [hl, canonical894 B hB] at h
  have hc0 : mixedMoment B raw894 (Fin.cases (0 : Fin 2) singletonSmall4212) =
      mixedMoment B node715 node715Labels := by
    have ha : raw894 = raw895 := by apply Matrix.ext; unfold raw894 raw895; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4212 = raw895Labels := by decide +kernel
    rw [ha, hj, canonical895 B hB]
  have hc1 : mixedMoment B raw894 (Fin.cases (1 : Fin 2) singletonSmall4212) =
      mixedMoment B node753 node753Labels := by
    have ha : raw894 = raw896 := by apply Matrix.ext; unfold raw894 raw896; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4212 = raw896Labels := by decide +kernel
    rw [ha, hj, canonical896 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4223 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4223 node4223Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node724 node724Labels + mixedMoment B node758 node758Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw909 singletonSmall4223
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4223) = raw909Labels := by decide +kernel
  rw [hl, canonical909 B hB] at h
  have hc0 : mixedMoment B raw909 (Fin.cases (0 : Fin 2) singletonSmall4223) =
      mixedMoment B node724 node724Labels := by
    have ha : raw909 = raw910 := by apply Matrix.ext; unfold raw909 raw910; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4223 = raw910Labels := by decide +kernel
    rw [ha, hj, canonical910 B hB]
  have hc1 : mixedMoment B raw909 (Fin.cases (1 : Fin 2) singletonSmall4223) =
      mixedMoment B node758 node758Labels := by
    have ha : raw909 = raw911 := by apply Matrix.ext; unfold raw909 raw911; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4223 = raw911Labels := by decide +kernel
    rw [ha, hj, canonical911 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4255 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4255 node4255Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node789 node789Labels + mixedMoment B node823 node823Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw981 singletonSmall4255
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4255) = raw981Labels := by decide +kernel
  rw [hl, canonical981 B hB] at h
  have hc0 : mixedMoment B raw981 (Fin.cases (0 : Fin 2) singletonSmall4255) =
      mixedMoment B node789 node789Labels := by
    have ha : raw981 = raw982 := by apply Matrix.ext; unfold raw981 raw982; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4255 = raw982Labels := by decide +kernel
    rw [ha, hj, canonical982 B hB]
  have hc1 : mixedMoment B raw981 (Fin.cases (1 : Fin 2) singletonSmall4255) =
      mixedMoment B node823 node823Labels := by
    have ha : raw981 = raw983 := by apply Matrix.ext; unfold raw981 raw983; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4255 = raw983Labels := by decide +kernel
    rw [ha, hj, canonical983 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4256 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4256 node4256Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node790 node790Labels + mixedMoment B node848 node848Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw984 singletonSmall4256
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4256) = raw984Labels := by decide +kernel
  rw [hl, canonical984 B hB] at h
  have hc0 : mixedMoment B raw984 (Fin.cases (0 : Fin 2) singletonSmall4256) =
      mixedMoment B node790 node790Labels := by
    have ha : raw984 = raw985 := by apply Matrix.ext; unfold raw984 raw985; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4256 = raw985Labels := by decide +kernel
    rw [ha, hj, canonical985 B hB]
  have hc1 : mixedMoment B raw984 (Fin.cases (1 : Fin 2) singletonSmall4256) =
      mixedMoment B node848 node848Labels := by
    have ha : raw984 = raw986 := by apply Matrix.ext; unfold raw984 raw986; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4256 = raw986Labels := by decide +kernel
    rw [ha, hj, canonical986 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4272 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4272 node4272Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node815 node815Labels + mixedMoment B node826 node826Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw999 singletonSmall4272
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4272) = raw999Labels := by decide +kernel
  rw [hl, canonical999 B hB] at h
  have hc0 : mixedMoment B raw999 (Fin.cases (0 : Fin 2) singletonSmall4272) =
      mixedMoment B node815 node815Labels := by
    have ha : raw999 = raw1000 := by apply Matrix.ext; unfold raw999 raw1000; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4272 = raw1000Labels := by decide +kernel
    rw [ha, hj, canonical1000 B hB]
  have hc1 : mixedMoment B raw999 (Fin.cases (1 : Fin 2) singletonSmall4272) =
      mixedMoment B node826 node826Labels := by
    have ha : raw999 = raw1001 := by apply Matrix.ext; unfold raw999 raw1001; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4272 = raw1001Labels := by decide +kernel
    rw [ha, hj, canonical1001 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4278 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4278 node4278Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node830 node830Labels + mixedMoment B node830 node830Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1008 singletonSmall4278
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4278) = raw1008Labels := by decide +kernel
  rw [hl, canonical1008 B hB] at h
  have hc0 : mixedMoment B raw1008 (Fin.cases (0 : Fin 2) singletonSmall4278) =
      mixedMoment B node830 node830Labels := by
    have ha : raw1008 = raw1009 := by apply Matrix.ext; unfold raw1008 raw1009; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4278 = raw1009Labels := by decide +kernel
    rw [ha, hj, canonical1009 B hB]
  have hc1 : mixedMoment B raw1008 (Fin.cases (1 : Fin 2) singletonSmall4278) =
      mixedMoment B node830 node830Labels := by
    have ha : raw1008 = raw1010 := by apply Matrix.ext; unfold raw1008 raw1010; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4278 = raw1010Labels := by decide +kernel
    rw [ha, hj, canonical1010 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4279 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4279 node4279Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node831 node831Labels + mixedMoment B node858 node858Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1011 singletonSmall4279
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4279) = raw1011Labels := by decide +kernel
  rw [hl, canonical1011 B hB] at h
  have hc0 : mixedMoment B raw1011 (Fin.cases (0 : Fin 2) singletonSmall4279) =
      mixedMoment B node831 node831Labels := by
    have ha : raw1011 = raw1012 := by apply Matrix.ext; unfold raw1011 raw1012; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4279 = raw1012Labels := by decide +kernel
    rw [ha, hj, canonical1012 B hB]
  have hc1 : mixedMoment B raw1011 (Fin.cases (1 : Fin 2) singletonSmall4279) =
      mixedMoment B node858 node858Labels := by
    have ha : raw1011 = raw1013 := by apply Matrix.ext; unfold raw1011 raw1013; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4279 = raw1013Labels := by decide +kernel
    rw [ha, hj, canonical1013 B hB]
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

theorem singleton4404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4404 node4404Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node985 node985Labels + mixedMoment B node1618 node1618Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1218 singletonSmall4404
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4404) = raw1218Labels := by decide +kernel
  rw [hl, canonical1218 B hB] at h
  have hc0 : mixedMoment B raw1218 (Fin.cases (0 : Fin 2) singletonSmall4404) =
      mixedMoment B node985 node985Labels := by
    have ha : raw1218 = raw1219 := by apply Matrix.ext; unfold raw1218 raw1219; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4404 = raw1219Labels := by decide +kernel
    rw [ha, hj, canonical1219 B hB]
  have hc1 : mixedMoment B raw1218 (Fin.cases (1 : Fin 2) singletonSmall4404) =
      mixedMoment B node1618 node1618Labels := by
    have ha : raw1218 = raw1220 := by apply Matrix.ext; unfold raw1218 raw1220; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4404 = raw1220Labels := by decide +kernel
    rw [ha, hj, canonical1220 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node660 node660Labels = Sparse.eval nodeValue660 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 660) = mixedMoment B node660 node660Labels := rfl
  simpa [nodeValue660, Sparse.eval] using hc.symm

theorem sound671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node671 node671Labels = Sparse.eval nodeValue671 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 671) = mixedMoment B node671 node671Labels := rfl
  simpa [nodeValue671, Sparse.eval] using hc.symm

theorem sound679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node679 node679Labels = Sparse.eval nodeValue679 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 679) = mixedMoment B node679 node679Labels := rfl
  simpa [nodeValue679, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node710 node710Labels = Sparse.eval nodeValue710 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 710) = mixedMoment B node710 node710Labels := rfl
  simpa [nodeValue710, Sparse.eval] using hc.symm

theorem sound715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node715 node715Labels = Sparse.eval nodeValue715 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 715) = mixedMoment B node715 node715Labels := rfl
  simpa [nodeValue715, Sparse.eval] using hc.symm

theorem sound724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node724 node724Labels = Sparse.eval nodeValue724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 724) = mixedMoment B node724 node724Labels := rfl
  simpa [nodeValue724, Sparse.eval] using hc.symm

theorem sound746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node746 node746Labels = Sparse.eval nodeValue746 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 746) = mixedMoment B node746 node746Labels := rfl
  simpa [nodeValue746, Sparse.eval] using hc.symm

theorem sound753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node753 node753Labels = Sparse.eval nodeValue753 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 753) = mixedMoment B node753 node753Labels := rfl
  simpa [nodeValue753, Sparse.eval] using hc.symm

theorem sound758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node758 node758Labels = Sparse.eval nodeValue758 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 758) = mixedMoment B node758 node758Labels := rfl
  simpa [nodeValue758, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node789 node789Labels = Sparse.eval nodeValue789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 789) = mixedMoment B node789 node789Labels := rfl
  simpa [nodeValue789, Sparse.eval] using hc.symm

theorem sound790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node790 node790Labels = Sparse.eval nodeValue790 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 790) = mixedMoment B node790 node790Labels := rfl
  simpa [nodeValue790, Sparse.eval] using hc.symm

theorem sound815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node815 node815Labels = Sparse.eval nodeValue815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 815) = mixedMoment B node815 node815Labels := rfl
  simpa [nodeValue815, Sparse.eval] using hc.symm

theorem sound823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node823 node823Labels = Sparse.eval nodeValue823 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 823) = mixedMoment B node823 node823Labels := rfl
  simpa [nodeValue823, Sparse.eval] using hc.symm

theorem sound826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node826 node826Labels = Sparse.eval nodeValue826 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 826) = mixedMoment B node826 node826Labels := rfl
  simpa [nodeValue826, Sparse.eval] using hc.symm

theorem sound830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node830 node830Labels = Sparse.eval nodeValue830 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 830) = mixedMoment B node830 node830Labels := rfl
  simpa [nodeValue830, Sparse.eval] using hc.symm

theorem sound831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node831 node831Labels = Sparse.eval nodeValue831 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 831) = mixedMoment B node831 node831Labels := rfl
  simpa [nodeValue831, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node848 node848Labels = Sparse.eval nodeValue848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 848) = mixedMoment B node848 node848Labels := rfl
  simpa [nodeValue848, Sparse.eval] using hc.symm

theorem sound858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node858 node858Labels = Sparse.eval nodeValue858 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 858) = mixedMoment B node858 node858Labels := rfl
  simpa [nodeValue858, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node985 node985Labels = Sparse.eval nodeValue985 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 985) = mixedMoment B node985 node985Labels := rfl
  simpa [nodeValue985, Sparse.eval] using hc.symm

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

theorem sound1050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1050 node1050Labels = Sparse.eval nodeValue1050 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1050) = mixedMoment B node1050 node1050Labels := rfl
  simpa [nodeValue1050, Sparse.eval] using hc.symm

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

theorem sound1618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1618 node1618Labels = Sparse.eval nodeValue1618 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1618) = mixedMoment B node1618 node1618Labels := rfl
  simpa [nodeValue1618, Sparse.eval] using hc.symm

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

theorem sound1751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1751 node1751Labels = Sparse.eval nodeValue1751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1751) = mixedMoment B node1751 node1751Labels := rfl
  simpa [nodeValue1751, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node552 node552Labels = Sparse.eval nodeValue552 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 552) = mixedMoment B node552 node552Labels := rfl
  simpa [nodeValue552, Sparse.eval] using hc.symm

theorem sound555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node555 node555Labels = Sparse.eval nodeValue555 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 555) = mixedMoment B node555 node555Labels := rfl
  simpa [nodeValue555, Sparse.eval] using hc.symm

theorem sound562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node562 node562Labels = Sparse.eval nodeValue562 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 562) = mixedMoment B node562 node562Labels := rfl
  simpa [nodeValue562, Sparse.eval] using hc.symm

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

theorem sound4071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4071 node4071Labels = Sparse.eval nodeValue4071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4071) = mixedMoment B node4071 node4071Labels := rfl
  simpa [nodeValue4071, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4123 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4123 node4123Labels = 0 := by
  exact mixedMoment_order_one B hB node4123 node4123Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4115 node4115Labels = Sparse.eval nodeValue4115 (mixedVector B) := by
  have h := singleton4115 B _hB
  rw [sound552 B _hB _hF, sound660 B _hB _hF] at h
  norm_num [nodeValue4115, nodeValue552, nodeValue660, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4121 node4121Labels = Sparse.eval nodeValue4121 (mixedVector B) := by
  have h := singleton4121 B _hB
  rw [sound555 B _hB _hF, sound671 B _hB _hF] at h
  norm_num [nodeValue4121, nodeValue555, nodeValue671, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4123 node4123Labels = Sparse.eval nodeValue4123 (mixedVector B) := by
  simpa only [nodeValue4123, Sparse.eval_nil] using zero4123 B _hB _hF

theorem sound4132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4132 node4132Labels = Sparse.eval nodeValue4132 (mixedVector B) := by
  have h := singleton4132 B _hB
  rw [sound562 B _hB _hF, sound679 B _hB _hF] at h
  norm_num [nodeValue4132, nodeValue562, nodeValue679, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4214 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4214 node4214Labels = 0 := by
  exact mixedMoment_order_one B hB node4214 node4214Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4207 node4207Labels = Sparse.eval nodeValue4207 (mixedVector B) := by
  have h := singleton4207 B _hB
  rw [sound710 B _hB _hF, sound746 B _hB _hF] at h
  norm_num [nodeValue4207, nodeValue710, nodeValue746, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4212 node4212Labels = Sparse.eval nodeValue4212 (mixedVector B) := by
  have h := singleton4212 B _hB
  rw [sound715 B _hB _hF, sound753 B _hB _hF] at h
  norm_num [nodeValue4212, nodeValue715, nodeValue753, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4214 node4214Labels = Sparse.eval nodeValue4214 (mixedVector B) := by
  simpa only [nodeValue4214, Sparse.eval_nil] using zero4214 B _hB _hF

theorem sound4223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4223 node4223Labels = Sparse.eval nodeValue4223 (mixedVector B) := by
  have h := singleton4223 B _hB
  rw [sound724 B _hB _hF, sound758 B _hB _hF] at h
  norm_num [nodeValue4223, nodeValue724, nodeValue758, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4273 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4273 node4273Labels = 0 := by
  exact mixedMoment_order_one B hB node4273 node4273Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4284 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4284 node4284Labels = 0 := by
  exact mixedMoment_order_one B hB node4284 node4284Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4255 node4255Labels = Sparse.eval nodeValue4255 (mixedVector B) := by
  have h := singleton4255 B _hB
  rw [sound789 B _hB _hF, sound823 B _hB _hF] at h
  norm_num [nodeValue4255, nodeValue789, nodeValue823, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4256 node4256Labels = Sparse.eval nodeValue4256 (mixedVector B) := by
  have h := singleton4256 B _hB
  rw [sound790 B _hB _hF, sound848 B _hB _hF] at h
  norm_num [nodeValue4256, nodeValue790, nodeValue848, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4272 node4272Labels = Sparse.eval nodeValue4272 (mixedVector B) := by
  have h := singleton4272 B _hB
  rw [sound815 B _hB _hF, sound826 B _hB _hF] at h
  norm_num [nodeValue4272, nodeValue815, nodeValue826, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4273 node4273Labels = Sparse.eval nodeValue4273 (mixedVector B) := by
  simpa only [nodeValue4273, Sparse.eval_nil] using zero4273 B _hB _hF

theorem sound4278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4278 node4278Labels = Sparse.eval nodeValue4278 (mixedVector B) := by
  have h := singleton4278 B _hB
  rw [sound830 B _hB _hF] at h
  norm_num [nodeValue4278, nodeValue830, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4279 node4279Labels = Sparse.eval nodeValue4279 (mixedVector B) := by
  have h := singleton4279 B _hB
  rw [sound831 B _hB _hF, sound858 B _hB _hF] at h
  norm_num [nodeValue4279, nodeValue831, nodeValue858, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4284 node4284Labels = Sparse.eval nodeValue4284 (mixedVector B) := by
  simpa only [nodeValue4284, Sparse.eval_nil] using zero4284 B _hB _hF

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

theorem sound4404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4404 node4404Labels = Sparse.eval nodeValue4404 (mixedVector B) := by
  have h := singleton4404 B _hB
  rw [sound985 B _hB _hF, sound1618 B _hB _hF] at h
  norm_num [nodeValue4404, nodeValue985, nodeValue1618, Sparse.eval] at h ⊢
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

theorem sound4466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4466 node4466Labels = Sparse.eval nodeValue4466 (mixedVector B) := by
  have h := singleton4466 B _hB
  rw [sound1049 B _hB _hF, sound1738 B _hB _hF] at h
  norm_num [nodeValue4466, nodeValue1049, nodeValue1738, Sparse.eval] at h ⊢
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

theorem sound4511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4511 node4511Labels = Sparse.eval nodeValue4511 (mixedVector B) := by
  simpa only [nodeValue4511, Sparse.eval_nil] using zero4511 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources49
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1574 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1574 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1574 + difference 0 1) (sourceB1574 + difference 1 0) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1574 + difference 0 1) (sourceB1574 + difference 1 0) sourceC1574) = raw22623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw22623; decide +kernel
    rw [ha]
    exact (canonical22623 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1574 + difference 0 2) (sourceB1574 + difference 2 0) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1574 + difference 0 2) (sourceB1574 + difference 2 0) sourceC1574) = raw23098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23098; decide +kernel
    rw [ha]
    exact (canonical23098 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1574 + difference 0 3) (sourceB1574 + difference 3 0) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1574 + difference 0 3) (sourceB1574 + difference 3 0) sourceC1574) = raw22775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw22775; decide +kernel
    rw [ha]
    exact (canonical22775 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1574 + difference 0 4) (sourceB1574 + difference 4 0) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1574 + difference 0 4) (sourceB1574 + difference 4 0) sourceC1574) = raw22611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw22611; decide +kernel
    rw [ha]
    exact (canonical22611 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1574 + difference 0 5) (sourceB1574 + difference 5 0) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1574 + difference 0 5) (sourceB1574 + difference 5 0) sourceC1574) = raw23270 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23270; decide +kernel
    rw [ha]
    exact (canonical23270 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1574 + difference 1 0) (sourceB1574 + difference 0 1) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4132) := by
    have ha : (tripleCharges (sourceA1574 + difference 1 0) (sourceB1574 + difference 0 1) sourceC1574) = raw23765 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23765; decide +kernel
    rw [ha]
    exact (canonical23765 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1574 + difference 1 2) (sourceB1574 + difference 2 1) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4223) := by
    have ha : (tripleCharges (sourceA1574 + difference 1 2) (sourceB1574 + difference 2 1) sourceC1574) = raw23766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23766; decide +kernel
    rw [ha]
    exact (canonical23766 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1574 + difference 1 3) (sourceB1574 + difference 3 1) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4223) := by
    have ha : (tripleCharges (sourceA1574 + difference 1 3) (sourceB1574 + difference 3 1) sourceC1574) = raw23767 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23767; decide +kernel
    rw [ha]
    exact (canonical23767 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1574 + difference 1 4) (sourceB1574 + difference 4 1) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4279) := by
    have ha : (tripleCharges (sourceA1574 + difference 1 4) (sourceB1574 + difference 4 1) sourceC1574) = raw23260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23260; decide +kernel
    rw [ha]
    exact (canonical23260 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1574 + difference 1 5) (sourceB1574 + difference 5 1) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4278) := by
    have ha : (tripleCharges (sourceA1574 + difference 1 5) (sourceB1574 + difference 5 1) sourceC1574) = raw23077 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23077; decide +kernel
    rw [ha]
    exact (canonical23077 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1574 + difference 2 0) (sourceB1574 + difference 0 2) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4115) := by
    have ha : (tripleCharges (sourceA1574 + difference 2 0) (sourceB1574 + difference 0 2) sourceC1574) = raw23768 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23768; decide +kernel
    rw [ha]
    exact (canonical23768 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1574 + difference 2 1) (sourceB1574 + difference 1 2) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4273) := by
    have ha : (tripleCharges (sourceA1574 + difference 2 1) (sourceB1574 + difference 1 2) sourceC1574) = raw23563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23563; decide +kernel
    rw [ha]
    exact (canonical23563 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1574 + difference 2 3) (sourceB1574 + difference 3 2) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4207) := by
    have ha : (tripleCharges (sourceA1574 + difference 2 3) (sourceB1574 + difference 3 2) sourceC1574) = raw23769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23769; decide +kernel
    rw [ha]
    exact (canonical23769 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1574 + difference 2 4) (sourceB1574 + difference 4 2) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4256) := by
    have ha : (tripleCharges (sourceA1574 + difference 2 4) (sourceB1574 + difference 4 2) sourceC1574) = raw23264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23264; decide +kernel
    rw [ha]
    exact (canonical23264 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1574 + difference 2 5) (sourceB1574 + difference 5 2) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4255) := by
    have ha : (tripleCharges (sourceA1574 + difference 2 5) (sourceB1574 + difference 5 2) sourceC1574) = raw23082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23082; decide +kernel
    rw [ha]
    exact (canonical23082 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1574 + difference 3 0) (sourceB1574 + difference 0 3) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4115) := by
    have ha : (tripleCharges (sourceA1574 + difference 3 0) (sourceB1574 + difference 0 3) sourceC1574) = raw23770 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23770; decide +kernel
    rw [ha]
    exact (canonical23770 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1574 + difference 3 1) (sourceB1574 + difference 1 3) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4273) := by
    have ha : (tripleCharges (sourceA1574 + difference 3 1) (sourceB1574 + difference 1 3) sourceC1574) = raw23565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23565; decide +kernel
    rw [ha]
    exact (canonical23565 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1574 + difference 3 2) (sourceB1574 + difference 2 3) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4207) := by
    have ha : (tripleCharges (sourceA1574 + difference 3 2) (sourceB1574 + difference 2 3) sourceC1574) = raw23771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23771; decide +kernel
    rw [ha]
    exact (canonical23771 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1574 + difference 3 4) (sourceB1574 + difference 4 3) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4256) := by
    have ha : (tripleCharges (sourceA1574 + difference 3 4) (sourceB1574 + difference 4 3) sourceC1574) = raw23267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23267; decide +kernel
    rw [ha]
    exact (canonical23267 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1574 + difference 3 5) (sourceB1574 + difference 5 3) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4255) := by
    have ha : (tripleCharges (sourceA1574 + difference 3 5) (sourceB1574 + difference 5 3) sourceC1574) = raw23087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23087; decide +kernel
    rw [ha]
    exact (canonical23087 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1574 + difference 4 0) (sourceB1574 + difference 0 4) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4121) := by
    have ha : (tripleCharges (sourceA1574 + difference 4 0) (sourceB1574 + difference 0 4) sourceC1574) = raw23772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23772; decide +kernel
    rw [ha]
    exact (canonical23772 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1574 + difference 4 1) (sourceB1574 + difference 1 4) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4284) := by
    have ha : (tripleCharges (sourceA1574 + difference 4 1) (sourceB1574 + difference 1 4) sourceC1574) = raw23477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23477; decide +kernel
    rw [ha]
    exact (canonical23477 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1574 + difference 4 2) (sourceB1574 + difference 2 4) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4212) := by
    have ha : (tripleCharges (sourceA1574 + difference 4 2) (sourceB1574 + difference 2 4) sourceC1574) = raw23773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23773; decide +kernel
    rw [ha]
    exact (canonical23773 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1574 + difference 4 3) (sourceB1574 + difference 3 4) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4212) := by
    have ha : (tripleCharges (sourceA1574 + difference 4 3) (sourceB1574 + difference 3 4) sourceC1574) = raw23774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23774; decide +kernel
    rw [ha]
    exact (canonical23774 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1574 + difference 4 5) (sourceB1574 + difference 5 4) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4272) := by
    have ha : (tripleCharges (sourceA1574 + difference 4 5) (sourceB1574 + difference 5 4) sourceC1574) = raw23092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23092; decide +kernel
    rw [ha]
    exact (canonical23092 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1574 + difference 5 0) (sourceB1574 + difference 0 5) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4123) := by
    have ha : (tripleCharges (sourceA1574 + difference 5 0) (sourceB1574 + difference 0 5) sourceC1574) = raw23775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23775; decide +kernel
    rw [ha]
    exact (canonical23775 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1574 + difference 5 1) (sourceB1574 + difference 1 5) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (tripleCharges (sourceA1574 + difference 5 1) (sourceB1574 + difference 1 5) sourceC1574) = raw23568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23568; decide +kernel
    rw [ha]
    exact (canonical23568 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1574 + difference 5 2) (sourceB1574 + difference 2 5) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4214) := by
    have ha : (tripleCharges (sourceA1574 + difference 5 2) (sourceB1574 + difference 2 5) sourceC1574) = raw23776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23776; decide +kernel
    rw [ha]
    exact (canonical23776 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1574 + difference 5 3) (sourceB1574 + difference 3 5) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4214) := by
    have ha : (tripleCharges (sourceA1574 + difference 5 3) (sourceB1574 + difference 3 5) sourceC1574) = raw23646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23646; decide +kernel
    rw [ha]
    exact (canonical23646 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1574 + difference 5 4) (sourceB1574 + difference 4 5) sourceC1574) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4273) := by
    have ha : (tripleCharges (sourceA1574 + difference 5 4) (sourceB1574 + difference 4 5) sourceC1574) = raw23271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1574 sourceB1574 sourceC1574 difference raw23271; decide +kernel
    rw [ha]
    exact (canonical23271 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1574 sourceB1574 sourceC1574
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1574, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1340 : Integer.Sparse.reindex keyMap MixedData.row1340 = numericRow1340 := by decide +kernel

theorem numericCheck1340 (x : Master → ℝ) : Integer.Sparse.eval numericRow1340 x =
    (4 : ℝ) * reducedSource1340 x := by
  norm_num [numericRow1340, reducedSource1340, Integer.Sparse.eval, Sparse.eval, nodeValue4071, nodeValue4115, nodeValue4121, nodeValue4123, nodeValue4132, nodeValue4207, nodeValue4212, nodeValue4214, nodeValue4223, nodeValue4255, nodeValue4256, nodeValue4272, nodeValue4273, nodeValue4278, nodeValue4279, nodeValue4284, nodeValue4404, nodeValue4466, nodeValue4467, nodeValue4511] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1340 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1340 (mixedVector B) = 0 := by
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  have h4115 : mixedVector B (Sum.inr 4115) = Sparse.eval nodeValue4115 (mixedVector B) := by
    change mixedMoment B node4115 node4115Labels = _
    exact sound4115 B hB hF
  have h4121 : mixedVector B (Sum.inr 4121) = Sparse.eval nodeValue4121 (mixedVector B) := by
    change mixedMoment B node4121 node4121Labels = _
    exact sound4121 B hB hF
  have h4123 : mixedVector B (Sum.inr 4123) = Sparse.eval nodeValue4123 (mixedVector B) := by
    change mixedMoment B node4123 node4123Labels = _
    exact sound4123 B hB hF
  have h4132 : mixedVector B (Sum.inr 4132) = Sparse.eval nodeValue4132 (mixedVector B) := by
    change mixedMoment B node4132 node4132Labels = _
    exact sound4132 B hB hF
  have h4207 : mixedVector B (Sum.inr 4207) = Sparse.eval nodeValue4207 (mixedVector B) := by
    change mixedMoment B node4207 node4207Labels = _
    exact sound4207 B hB hF
  have h4212 : mixedVector B (Sum.inr 4212) = Sparse.eval nodeValue4212 (mixedVector B) := by
    change mixedMoment B node4212 node4212Labels = _
    exact sound4212 B hB hF
  have h4214 : mixedVector B (Sum.inr 4214) = Sparse.eval nodeValue4214 (mixedVector B) := by
    change mixedMoment B node4214 node4214Labels = _
    exact sound4214 B hB hF
  have h4223 : mixedVector B (Sum.inr 4223) = Sparse.eval nodeValue4223 (mixedVector B) := by
    change mixedMoment B node4223 node4223Labels = _
    exact sound4223 B hB hF
  have h4255 : mixedVector B (Sum.inr 4255) = Sparse.eval nodeValue4255 (mixedVector B) := by
    change mixedMoment B node4255 node4255Labels = _
    exact sound4255 B hB hF
  have h4256 : mixedVector B (Sum.inr 4256) = Sparse.eval nodeValue4256 (mixedVector B) := by
    change mixedMoment B node4256 node4256Labels = _
    exact sound4256 B hB hF
  have h4272 : mixedVector B (Sum.inr 4272) = Sparse.eval nodeValue4272 (mixedVector B) := by
    change mixedMoment B node4272 node4272Labels = _
    exact sound4272 B hB hF
  have h4273 : mixedVector B (Sum.inr 4273) = Sparse.eval nodeValue4273 (mixedVector B) := by
    change mixedMoment B node4273 node4273Labels = _
    exact sound4273 B hB hF
  have h4278 : mixedVector B (Sum.inr 4278) = Sparse.eval nodeValue4278 (mixedVector B) := by
    change mixedMoment B node4278 node4278Labels = _
    exact sound4278 B hB hF
  have h4279 : mixedVector B (Sum.inr 4279) = Sparse.eval nodeValue4279 (mixedVector B) := by
    change mixedMoment B node4279 node4279Labels = _
    exact sound4279 B hB hF
  have h4284 : mixedVector B (Sum.inr 4284) = Sparse.eval nodeValue4284 (mixedVector B) := by
    change mixedMoment B node4284 node4284Labels = _
    exact sound4284 B hB hF
  have h4404 : mixedVector B (Sum.inr 4404) = Sparse.eval nodeValue4404 (mixedVector B) := by
    change mixedMoment B node4404 node4404Labels = _
    exact sound4404 B hB hF
  have h4466 : mixedVector B (Sum.inr 4466) = Sparse.eval nodeValue4466 (mixedVector B) := by
    change mixedMoment B node4466 node4466Labels = _
    exact sound4466 B hB hF
  have h4467 : mixedVector B (Sum.inr 4467) = Sparse.eval nodeValue4467 (mixedVector B) := by
    change mixedMoment B node4467 node4467Labels = _
    exact sound4467 B hB hF
  have h4511 : mixedVector B (Sum.inr 4511) = Sparse.eval nodeValue4511 (mixedVector B) := by
    change mixedMoment B node4511 node4511Labels = _
    exact sound4511 B hB hF
  simpa only [sourceForm1574, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4071, h4115, h4121, h4123, h4132, h4207, h4212, h4214, h4223, h4255, h4256, h4272, h4273, h4278, h4279, h4284, h4404, h4466, h4467, h4511, reducedSource1340] using sourceEq1574 B hB

theorem rowSound1340_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1340 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1340, numericCheck1340, reducedZero1340 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340_e_oai
