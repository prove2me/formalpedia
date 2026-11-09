-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound957_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:04:44.503393+00:00
-- url     : https://prove2.me/submissions/6c9b1b84-6110-4abe-96df-f9981c28b798

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E195
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E129
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5433_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5439_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound5450_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical143
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18404 raw18404Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw18404 raw18404Labels = mixedMoment B raw18404step0 raw18404step0Labels := by
      have hz : ∀ j, raw18404 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18404step0 = (fun i j => raw18404 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18404step0 raw18404; decide +kernel
      have hl : raw18404step0Labels = raw18404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18404 raw18404Labels permutation346 hz
    mixedMoment B raw18404step0 raw18404step0Labels = mixedMoment B raw18404step1 raw18404step1Labels := by
      have ha : raw18404step1 = (fun i j => raw18404step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18404step1 raw18404step0; decide +kernel
      have hl : raw18404step1Labels = raw18404step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18404step0 raw18404step0Labels permutation36 permutation7
    mixedMoment B raw18404step1 raw18404step1Labels = mixedMoment B raw18404step2 raw18404step2Labels := by
      have ha : raw18404step2 = raw18404step1 := by apply Matrix.ext; unfold raw18404step2 raw18404step1; decide +kernel
      have hl : raw18404step1Labels = labelEmbedding10 ∘ raw18404step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18404step1 raw18404step1Labels raw18404step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5486 node5486Labels := by rfl

theorem canonical18408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18408 raw18408Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw18408 raw18408Labels = mixedMoment B raw18408step0 raw18408step0Labels := by
      have ha : raw18408step0 = (fun i j => raw18408 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18408step0 raw18408; decide +kernel
      have hl : raw18408step0Labels = raw18408Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18408 raw18408Labels permutation212 permutation4
    mixedMoment B raw18408step0 raw18408step0Labels = mixedMoment B raw18408step1 raw18408step1Labels := by
      have ha : raw18408step1 = -raw18408step0 := by apply Matrix.ext; change ∀ i j, raw18408step1 i j = -(raw18408step0 i j); unfold raw18408step1 raw18408step0; decide +kernel
      have hl : raw18408step1Labels = raw18408step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18408step1 raw18408step1Labels = mixedMoment B raw18408step2 raw18408step2Labels := by
      have ha : raw18408step2 = raw18408step1 := by apply Matrix.ext; unfold raw18408step2 raw18408step1; decide +kernel
      have hl : raw18408step1Labels = labelEmbedding7 ∘ raw18408step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18408step1 raw18408step1Labels raw18408step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical18410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18410 raw18410Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw18410 raw18410Labels = mixedMoment B raw18410step0 raw18410step0Labels := by
      have ha : raw18410step0 = (fun i j => raw18410 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18410step0 raw18410; decide +kernel
      have hl : raw18410step0Labels = raw18410Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18410 raw18410Labels permutation212 permutation4
    mixedMoment B raw18410step0 raw18410step0Labels = mixedMoment B raw18410step1 raw18410step1Labels := by
      have ha : raw18410step1 = -raw18410step0 := by apply Matrix.ext; change ∀ i j, raw18410step1 i j = -(raw18410step0 i j); unfold raw18410step1 raw18410step0; decide +kernel
      have hl : raw18410step1Labels = raw18410step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18410step1 raw18410step1Labels = mixedMoment B raw18410step2 raw18410step2Labels := by
      have ha : raw18410step2 = raw18410step1 := by apply Matrix.ext; unfold raw18410step2 raw18410step1; decide +kernel
      have hl : raw18410step1Labels = labelEmbedding7 ∘ raw18410step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18410step1 raw18410step1Labels raw18410step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

theorem canonical18411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18411 raw18411Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw18411 raw18411Labels = mixedMoment B raw18411step0 raw18411step0Labels := by
      have ha : raw18411step0 = (fun i j => raw18411 (permutation234 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18411step0 raw18411; decide +kernel
      have hl : raw18411step0Labels = raw18411Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18411 raw18411Labels permutation234 permutation4
    mixedMoment B raw18411step0 raw18411step0Labels = mixedMoment B raw18411step1 raw18411step1Labels := by
      have ha : raw18411step1 = -raw18411step0 := by apply Matrix.ext; change ∀ i j, raw18411step1 i j = -(raw18411step0 i j); unfold raw18411step1 raw18411step0; decide +kernel
      have hl : raw18411step1Labels = raw18411step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18411step1 raw18411step1Labels = mixedMoment B raw18411step2 raw18411step2Labels := by
      have ha : raw18411step2 = raw18411step1 := by apply Matrix.ext; unfold raw18411step2 raw18411step1; decide +kernel
      have hl : raw18411step1Labels = labelEmbedding7 ∘ raw18411step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18411step1 raw18411step1Labels raw18411step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

theorem canonical18412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18412 raw18412Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw18412 raw18412Labels = mixedMoment B raw18412step0 raw18412step0Labels := by
      have ha : raw18412step0 = (fun i j => raw18412 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18412step0 raw18412; decide +kernel
      have hl : raw18412step0Labels = raw18412Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18412 raw18412Labels permutation152 permutation6
    mixedMoment B raw18412step0 raw18412step0Labels = mixedMoment B raw18412step1 raw18412step1Labels := by
      have ha : raw18412step1 = raw18412step0 := by apply Matrix.ext; unfold raw18412step1 raw18412step0; decide +kernel
      have hl : raw18412step0Labels = labelEmbedding9 ∘ raw18412step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18412step0 raw18412step0Labels raw18412step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

theorem canonical18420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18420 raw18420Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw18420 raw18420Labels = mixedMoment B raw18420step0 raw18420step0Labels := by
      have hz : ∀ j, raw18420 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18420step0 = (fun i j => raw18420 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18420step0 raw18420; decide +kernel
      have hl : raw18420step0Labels = raw18420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18420 raw18420Labels permutation346 hz
    mixedMoment B raw18420step0 raw18420step0Labels = mixedMoment B raw18420step1 raw18420step1Labels := by
      have ha : raw18420step1 = (fun i j => raw18420step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18420step1 raw18420step0; decide +kernel
      have hl : raw18420step1Labels = raw18420step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18420step0 raw18420step0Labels permutation34 permutation6
    mixedMoment B raw18420step1 raw18420step1Labels = mixedMoment B raw18420step2 raw18420step2Labels := by
      have ha : raw18420step2 = raw18420step1 := by apply Matrix.ext; unfold raw18420step2 raw18420step1; decide +kernel
      have hl : raw18420step1Labels = labelEmbedding9 ∘ raw18420step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18420step1 raw18420step1Labels raw18420step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

theorem canonical18425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18425 raw18425Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw18425 raw18425Labels = mixedMoment B raw18425step0 raw18425step0Labels := by
      have hz : ∀ j, raw18425 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18425step0 = (fun i j => raw18425 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18425step0 raw18425; decide +kernel
      have hl : raw18425step0Labels = raw18425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18425 raw18425Labels permutation346 hz
    mixedMoment B raw18425step0 raw18425step0Labels = mixedMoment B raw18425step1 raw18425step1Labels := by
      have ha : raw18425step1 = (fun i j => raw18425step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18425step1 raw18425step0; decide +kernel
      have hl : raw18425step1Labels = raw18425step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18425step0 raw18425step0Labels permutation32 permutation6
    mixedMoment B raw18425step1 raw18425step1Labels = mixedMoment B raw18425step2 raw18425step2Labels := by
      have ha : raw18425step2 = raw18425step1 := by apply Matrix.ext; unfold raw18425step2 raw18425step1; decide +kernel
      have hl : raw18425step1Labels = labelEmbedding9 ∘ raw18425step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18425step1 raw18425step1Labels raw18425step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

theorem canonical18430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18430 raw18430Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18430 raw18430Labels = mixedMoment B raw18430step0 raw18430step0Labels := by
      have hz : ∀ j, raw18430 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18430step0 = (fun i j => raw18430 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18430step0 raw18430; decide +kernel
      have hl : raw18430step0Labels = raw18430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18430 raw18430Labels permutation346 hz
    mixedMoment B raw18430step0 raw18430step0Labels = mixedMoment B raw18430step1 raw18430step1Labels := by
      have ha : raw18430step1 = (fun i j => raw18430step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18430step1 raw18430step0; decide +kernel
      have hl : raw18430step1Labels = raw18430step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18430step0 raw18430step0Labels permutation32 permutation6
    mixedMoment B raw18430step1 raw18430step1Labels = mixedMoment B raw18430step2 raw18430step2Labels := by
      have ha : raw18430step2 = raw18430step1 := by apply Matrix.ext; unfold raw18430step2 raw18430step1; decide +kernel
      have hl : raw18430step1Labels = labelEmbedding9 ∘ raw18430step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18430step1 raw18430step1Labels raw18430step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical144
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18507 raw18507Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw18507 raw18507Labels = mixedMoment B raw18507step0 raw18507step0Labels := by
      have ha : raw18507step0 = (fun i j => raw18507 (permutation283 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18507step0 raw18507; decide +kernel
      have hl : raw18507step0Labels = raw18507Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18507 raw18507Labels permutation283 permutation2
    mixedMoment B raw18507step0 raw18507step0Labels = mixedMoment B raw18507step1 raw18507step1Labels := by
      have ha : raw18507step1 = -raw18507step0 := by apply Matrix.ext; change ∀ i j, raw18507step1 i j = -(raw18507step0 i j); unfold raw18507step1 raw18507step0; decide +kernel
      have hl : raw18507step1Labels = raw18507step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5472 node5472Labels := by rfl

theorem canonical18508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18508 raw18508Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw18508 raw18508Labels = mixedMoment B raw18508step0 raw18508step0Labels := by
      have hz : ∀ j, raw18508 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18508step0 = (fun i j => raw18508 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18508step0 raw18508; decide +kernel
      have hl : raw18508step0Labels = raw18508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18508 raw18508Labels permutation346 hz
    mixedMoment B raw18508step0 raw18508step0Labels = mixedMoment B raw18508step1 raw18508step1Labels := by
      have ha : raw18508step1 = (fun i j => raw18508step0 (permutation61 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18508step1 raw18508step0; decide +kernel
      have hl : raw18508step1Labels = raw18508step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18508step0 raw18508step0Labels permutation61 permutation2
    mixedMoment B raw18508step1 raw18508step1Labels = mixedMoment B raw18508step2 raw18508step2Labels := by
      have ha : raw18508step2 = -raw18508step1 := by apply Matrix.ext; change ∀ i j, raw18508step2 i j = -(raw18508step1 i j); unfold raw18508step2 raw18508step1; decide +kernel
      have hl : raw18508step2Labels = raw18508step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical18509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18509 raw18509Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw18509 raw18509Labels = mixedMoment B raw18509step0 raw18509step0Labels := by
      have hz : ∀ j, raw18509 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18509step0 = (fun i j => raw18509 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18509step0 raw18509; decide +kernel
      have hl : raw18509step0Labels = raw18509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18509 raw18509Labels permutation346 hz
    mixedMoment B raw18509step0 raw18509step0Labels = mixedMoment B raw18509step1 raw18509step1Labels := by
      have ha : raw18509step1 = (fun i j => raw18509step0 (permutation60 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18509step1 raw18509step0; decide +kernel
      have hl : raw18509step1Labels = raw18509step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18509step0 raw18509step0Labels permutation60 permutation2
    mixedMoment B raw18509step1 raw18509step1Labels = mixedMoment B raw18509step2 raw18509step2Labels := by
      have ha : raw18509step2 = -raw18509step1 := by apply Matrix.ext; change ∀ i j, raw18509step2 i j = -(raw18509step1 i j); unfold raw18509step2 raw18509step1; decide +kernel
      have hl : raw18509step2Labels = raw18509step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical18510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18510 raw18510Labels = mixedMoment B node5474 node5474Labels := by
  calc
    mixedMoment B raw18510 raw18510Labels = mixedMoment B raw18510step0 raw18510step0Labels := by
      have hz : ∀ j, raw18510 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18510step0 = (fun i j => raw18510 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18510step0 raw18510; decide +kernel
      have hl : raw18510step0Labels = raw18510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18510 raw18510Labels permutation346 hz
    mixedMoment B raw18510step0 raw18510step0Labels = mixedMoment B raw18510step1 raw18510step1Labels := by
      have ha : raw18510step1 = (fun i j => raw18510step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18510step1 raw18510step0; decide +kernel
      have hl : raw18510step1Labels = raw18510step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18510step0 raw18510step0Labels permutation56 permutation2
    mixedMoment B raw18510step1 raw18510step1Labels = mixedMoment B raw18510step2 raw18510step2Labels := by
      have ha : raw18510step2 = -raw18510step1 := by apply Matrix.ext; change ∀ i j, raw18510step2 i j = -(raw18510step1 i j); unfold raw18510step2 raw18510step1; decide +kernel
      have hl : raw18510step2Labels = raw18510step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5474 node5474Labels := by rfl

theorem canonical18511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18511 raw18511Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw18511 raw18511Labels = mixedMoment B raw18511step0 raw18511step0Labels := by
      have hz : ∀ j, raw18511 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18511step0 = (fun i j => raw18511 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18511step0 raw18511; decide +kernel
      have hl : raw18511step0Labels = raw18511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18511 raw18511Labels permutation346 hz
    mixedMoment B raw18511step0 raw18511step0Labels = mixedMoment B raw18511step1 raw18511step1Labels := by
      have ha : raw18511step1 = (fun i j => raw18511step0 (permutation77 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18511step1 raw18511step0; decide +kernel
      have hl : raw18511step1Labels = raw18511step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18511step0 raw18511step0Labels permutation77 permutation3
    mixedMoment B raw18511step1 raw18511step1Labels = mixedMoment B raw18511step2 raw18511step2Labels := by
      have ha : raw18511step2 = -raw18511step1 := by apply Matrix.ext; change ∀ i j, raw18511step2 i j = -(raw18511step1 i j); unfold raw18511step2 raw18511step1; decide +kernel
      have hl : raw18511step2Labels = raw18511step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18511step2 raw18511step2Labels = mixedMoment B raw18511step3 raw18511step3Labels := by
      have ha : raw18511step3 = raw18511step2 := by apply Matrix.ext; unfold raw18511step3 raw18511step2; decide +kernel
      have hl : raw18511step2Labels = labelEmbedding6 ∘ raw18511step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18511step2 raw18511step2Labels raw18511step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

theorem canonical18512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18512 raw18512Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw18512 raw18512Labels = mixedMoment B raw18512step0 raw18512step0Labels := by
      have ha : raw18512step0 = (fun i j => raw18512 (permutation336 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18512step0 raw18512; decide +kernel
      have hl : raw18512step0Labels = raw18512Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18512 raw18512Labels permutation336 permutation3
    mixedMoment B raw18512step0 raw18512step0Labels = mixedMoment B raw18512step1 raw18512step1Labels := by
      have ha : raw18512step1 = -raw18512step0 := by apply Matrix.ext; change ∀ i j, raw18512step1 i j = -(raw18512step0 i j); unfold raw18512step1 raw18512step0; decide +kernel
      have hl : raw18512step1Labels = raw18512step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18512step1 raw18512step1Labels = mixedMoment B raw18512step2 raw18512step2Labels := by
      have ha : raw18512step2 = raw18512step1 := by apply Matrix.ext; unfold raw18512step2 raw18512step1; decide +kernel
      have hl : raw18512step1Labels = labelEmbedding6 ∘ raw18512step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18512step1 raw18512step1Labels raw18512step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical18513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18513 raw18513Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw18513 raw18513Labels = mixedMoment B raw18513step0 raw18513step0Labels := by
      have hz : ∀ j, raw18513 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18513step0 = (fun i j => raw18513 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18513step0 raw18513; decide +kernel
      have hl : raw18513step0Labels = raw18513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18513 raw18513Labels permutation346 hz
    mixedMoment B raw18513step0 raw18513step0Labels = mixedMoment B raw18513step1 raw18513step1Labels := by
      have ha : raw18513step1 = (fun i j => raw18513step0 (permutation75 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18513step1 raw18513step0; decide +kernel
      have hl : raw18513step1Labels = raw18513step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18513step0 raw18513step0Labels permutation75 permutation3
    mixedMoment B raw18513step1 raw18513step1Labels = mixedMoment B raw18513step2 raw18513step2Labels := by
      have ha : raw18513step2 = -raw18513step1 := by apply Matrix.ext; change ∀ i j, raw18513step2 i j = -(raw18513step1 i j); unfold raw18513step2 raw18513step1; decide +kernel
      have hl : raw18513step2Labels = raw18513step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18513step2 raw18513step2Labels = mixedMoment B raw18513step3 raw18513step3Labels := by
      have ha : raw18513step3 = raw18513step2 := by apply Matrix.ext; unfold raw18513step3 raw18513step2; decide +kernel
      have hl : raw18513step2Labels = labelEmbedding6 ∘ raw18513step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18513step2 raw18513step2Labels raw18513step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

theorem canonical18514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18514 raw18514Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw18514 raw18514Labels = mixedMoment B raw18514step0 raw18514step0Labels := by
      have hz : ∀ j, raw18514 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18514step0 = (fun i j => raw18514 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18514step0 raw18514; decide +kernel
      have hl : raw18514step0Labels = raw18514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18514 raw18514Labels permutation346 hz
    mixedMoment B raw18514step0 raw18514step0Labels = mixedMoment B raw18514step1 raw18514step1Labels := by
      have ha : raw18514step1 = (fun i j => raw18514step0 (permutation74 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18514step1 raw18514step0; decide +kernel
      have hl : raw18514step1Labels = raw18514step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18514step0 raw18514step0Labels permutation74 permutation3
    mixedMoment B raw18514step1 raw18514step1Labels = mixedMoment B raw18514step2 raw18514step2Labels := by
      have ha : raw18514step2 = -raw18514step1 := by apply Matrix.ext; change ∀ i j, raw18514step2 i j = -(raw18514step1 i j); unfold raw18514step2 raw18514step1; decide +kernel
      have hl : raw18514step2Labels = raw18514step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18514step2 raw18514step2Labels = mixedMoment B raw18514step3 raw18514step3Labels := by
      have ha : raw18514step3 = raw18514step2 := by apply Matrix.ext; unfold raw18514step3 raw18514step2; decide +kernel
      have hl : raw18514step2Labels = labelEmbedding6 ∘ raw18514step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18514step2 raw18514step2Labels raw18514step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

theorem canonical18515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18515 raw18515Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw18515 raw18515Labels = mixedMoment B raw18515step0 raw18515step0Labels := by
      have hz : ∀ j, raw18515 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18515step0 = (fun i j => raw18515 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18515step0 raw18515; decide +kernel
      have hl : raw18515step0Labels = raw18515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18515 raw18515Labels permutation346 hz
    mixedMoment B raw18515step0 raw18515step0Labels = mixedMoment B raw18515step1 raw18515step1Labels := by
      have ha : raw18515step1 = (fun i j => raw18515step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18515step1 raw18515step0; decide +kernel
      have hl : raw18515step1Labels = raw18515step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18515step0 raw18515step0Labels permutation56 permutation3
    mixedMoment B raw18515step1 raw18515step1Labels = mixedMoment B raw18515step2 raw18515step2Labels := by
      have ha : raw18515step2 = -raw18515step1 := by apply Matrix.ext; change ∀ i j, raw18515step2 i j = -(raw18515step1 i j); unfold raw18515step2 raw18515step1; decide +kernel
      have hl : raw18515step2Labels = raw18515step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18515step2 raw18515step2Labels = mixedMoment B raw18515step3 raw18515step3Labels := by
      have ha : raw18515step3 = raw18515step2 := by apply Matrix.ext; unfold raw18515step3 raw18515step2; decide +kernel
      have hl : raw18515step2Labels = labelEmbedding6 ∘ raw18515step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18515step2 raw18515step2Labels raw18515step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

theorem canonical18516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18516 raw18516Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18516 raw18516Labels = mixedMoment B raw18516step0 raw18516step0Labels := by
      have ha : raw18516step0 = (fun i j => raw18516 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18516step0 raw18516; decide +kernel
      have hl : raw18516step0Labels = raw18516Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18516 raw18516Labels permutation152 permutation6
    mixedMoment B raw18516step0 raw18516step0Labels = mixedMoment B raw18516step1 raw18516step1Labels := by
      have ha : raw18516step1 = raw18516step0 := by apply Matrix.ext; unfold raw18516step1 raw18516step0; decide +kernel
      have hl : raw18516step0Labels = labelEmbedding9 ∘ raw18516step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18516step0 raw18516step0Labels raw18516step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

theorem canonical18517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18517 raw18517Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw18517 raw18517Labels = mixedMoment B raw18517step0 raw18517step0Labels := by
      have hz : ∀ j, raw18517 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18517step0 = (fun i j => raw18517 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18517step0 raw18517; decide +kernel
      have hl : raw18517step0Labels = raw18517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18517 raw18517Labels permutation346 hz
    mixedMoment B raw18517step0 raw18517step0Labels = mixedMoment B raw18517step1 raw18517step1Labels := by
      have ha : raw18517step1 = (fun i j => raw18517step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18517step1 raw18517step0; decide +kernel
      have hl : raw18517step1Labels = raw18517step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18517step0 raw18517step0Labels permutation44 permutation4
    mixedMoment B raw18517step1 raw18517step1Labels = mixedMoment B raw18517step2 raw18517step2Labels := by
      have ha : raw18517step2 = -raw18517step1 := by apply Matrix.ext; change ∀ i j, raw18517step2 i j = -(raw18517step1 i j); unfold raw18517step2 raw18517step1; decide +kernel
      have hl : raw18517step2Labels = raw18517step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18517step2 raw18517step2Labels = mixedMoment B raw18517step3 raw18517step3Labels := by
      have ha : raw18517step3 = raw18517step2 := by apply Matrix.ext; unfold raw18517step3 raw18517step2; decide +kernel
      have hl : raw18517step2Labels = labelEmbedding7 ∘ raw18517step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18517step2 raw18517step2Labels raw18517step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical18518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18518 raw18518Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw18518 raw18518Labels = mixedMoment B raw18518step0 raw18518step0Labels := by
      have ha : raw18518step0 = (fun i j => raw18518 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18518step0 raw18518; decide +kernel
      have hl : raw18518step0Labels = raw18518Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18518 raw18518Labels permutation188 permutation4
    mixedMoment B raw18518step0 raw18518step0Labels = mixedMoment B raw18518step1 raw18518step1Labels := by
      have ha : raw18518step1 = -raw18518step0 := by apply Matrix.ext; change ∀ i j, raw18518step1 i j = -(raw18518step0 i j); unfold raw18518step1 raw18518step0; decide +kernel
      have hl : raw18518step1Labels = raw18518step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18518step1 raw18518step1Labels = mixedMoment B raw18518step2 raw18518step2Labels := by
      have ha : raw18518step2 = raw18518step1 := by apply Matrix.ext; unfold raw18518step2 raw18518step1; decide +kernel
      have hl : raw18518step1Labels = labelEmbedding7 ∘ raw18518step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18518step1 raw18518step1Labels raw18518step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical18519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18519 raw18519Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw18519 raw18519Labels = mixedMoment B raw18519step0 raw18519step0Labels := by
      have hz : ∀ j, raw18519 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18519step0 = (fun i j => raw18519 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18519step0 raw18519; decide +kernel
      have hl : raw18519step0Labels = raw18519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18519 raw18519Labels permutation346 hz
    mixedMoment B raw18519step0 raw18519step0Labels = mixedMoment B raw18519step1 raw18519step1Labels := by
      have ha : raw18519step1 = (fun i j => raw18519step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18519step1 raw18519step0; decide +kernel
      have hl : raw18519step1Labels = raw18519step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18519step0 raw18519step0Labels permutation44 permutation4
    mixedMoment B raw18519step1 raw18519step1Labels = mixedMoment B raw18519step2 raw18519step2Labels := by
      have ha : raw18519step2 = -raw18519step1 := by apply Matrix.ext; change ∀ i j, raw18519step2 i j = -(raw18519step1 i j); unfold raw18519step2 raw18519step1; decide +kernel
      have hl : raw18519step2Labels = raw18519step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18519step2 raw18519step2Labels = mixedMoment B raw18519step3 raw18519step3Labels := by
      have ha : raw18519step3 = raw18519step2 := by apply Matrix.ext; unfold raw18519step3 raw18519step2; decide +kernel
      have hl : raw18519step2Labels = labelEmbedding7 ∘ raw18519step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18519step2 raw18519step2Labels raw18519step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

theorem canonical18520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18520 raw18520Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18520 raw18520Labels = mixedMoment B raw18520step0 raw18520step0Labels := by
      have hz : ∀ j, raw18520 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18520step0 = (fun i j => raw18520 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18520step0 raw18520; decide +kernel
      have hl : raw18520step0Labels = raw18520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18520 raw18520Labels permutation346 hz
    mixedMoment B raw18520step0 raw18520step0Labels = mixedMoment B raw18520step1 raw18520step1Labels := by
      have ha : raw18520step1 = (fun i j => raw18520step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18520step1 raw18520step0; decide +kernel
      have hl : raw18520step1Labels = raw18520step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18520step0 raw18520step0Labels permutation35 permutation6
    mixedMoment B raw18520step1 raw18520step1Labels = mixedMoment B raw18520step2 raw18520step2Labels := by
      have ha : raw18520step2 = raw18520step1 := by apply Matrix.ext; unfold raw18520step2 raw18520step1; decide +kernel
      have hl : raw18520step1Labels = labelEmbedding9 ∘ raw18520step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18520step1 raw18520step1Labels raw18520step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical18521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18521 raw18521Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw18521 raw18521Labels = mixedMoment B raw18521step0 raw18521step0Labels := by
      have hz : ∀ j, raw18521 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18521step0 = (fun i j => raw18521 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18521step0 raw18521; decide +kernel
      have hl : raw18521step0Labels = raw18521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18521 raw18521Labels permutation346 hz
    mixedMoment B raw18521step0 raw18521step0Labels = mixedMoment B raw18521step1 raw18521step1Labels := by
      have ha : raw18521step1 = (fun i j => raw18521step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18521step1 raw18521step0; decide +kernel
      have hl : raw18521step1Labels = raw18521step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18521step0 raw18521step0Labels permutation38 permutation4
    mixedMoment B raw18521step1 raw18521step1Labels = mixedMoment B raw18521step2 raw18521step2Labels := by
      have ha : raw18521step2 = -raw18521step1 := by apply Matrix.ext; change ∀ i j, raw18521step2 i j = -(raw18521step1 i j); unfold raw18521step2 raw18521step1; decide +kernel
      have hl : raw18521step2Labels = raw18521step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18521step2 raw18521step2Labels = mixedMoment B raw18521step3 raw18521step3Labels := by
      have ha : raw18521step3 = raw18521step2 := by apply Matrix.ext; unfold raw18521step3 raw18521step2; decide +kernel
      have hl : raw18521step2Labels = labelEmbedding7 ∘ raw18521step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18521step2 raw18521step2Labels raw18521step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical18522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18522 raw18522Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw18522 raw18522Labels = mixedMoment B raw18522step0 raw18522step0Labels := by
      have ha : raw18522step0 = (fun i j => raw18522 (permutation182 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18522step0 raw18522; decide +kernel
      have hl : raw18522step0Labels = raw18522Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18522 raw18522Labels permutation182 permutation4
    mixedMoment B raw18522step0 raw18522step0Labels = mixedMoment B raw18522step1 raw18522step1Labels := by
      have ha : raw18522step1 = -raw18522step0 := by apply Matrix.ext; change ∀ i j, raw18522step1 i j = -(raw18522step0 i j); unfold raw18522step1 raw18522step0; decide +kernel
      have hl : raw18522step1Labels = raw18522step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18522step1 raw18522step1Labels = mixedMoment B raw18522step2 raw18522step2Labels := by
      have ha : raw18522step2 = raw18522step1 := by apply Matrix.ext; unfold raw18522step2 raw18522step1; decide +kernel
      have hl : raw18522step1Labels = labelEmbedding7 ∘ raw18522step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18522step1 raw18522step1Labels raw18522step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical18523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18523 raw18523Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw18523 raw18523Labels = mixedMoment B raw18523step0 raw18523step0Labels := by
      have hz : ∀ j, raw18523 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18523step0 = (fun i j => raw18523 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18523step0 raw18523; decide +kernel
      have hl : raw18523step0Labels = raw18523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18523 raw18523Labels permutation346 hz
    mixedMoment B raw18523step0 raw18523step0Labels = mixedMoment B raw18523step1 raw18523step1Labels := by
      have ha : raw18523step1 = (fun i j => raw18523step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18523step1 raw18523step0; decide +kernel
      have hl : raw18523step1Labels = raw18523step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18523step0 raw18523step0Labels permutation38 permutation4
    mixedMoment B raw18523step1 raw18523step1Labels = mixedMoment B raw18523step2 raw18523step2Labels := by
      have ha : raw18523step2 = -raw18523step1 := by apply Matrix.ext; change ∀ i j, raw18523step2 i j = -(raw18523step1 i j); unfold raw18523step2 raw18523step1; decide +kernel
      have hl : raw18523step2Labels = raw18523step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18523step2 raw18523step2Labels = mixedMoment B raw18523step3 raw18523step3Labels := by
      have ha : raw18523step3 = raw18523step2 := by apply Matrix.ext; unfold raw18523step3 raw18523step2; decide +kernel
      have hl : raw18523step2Labels = labelEmbedding7 ∘ raw18523step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18523step2 raw18523step2Labels raw18523step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

theorem canonical18524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18524 raw18524Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18524 raw18524Labels = mixedMoment B raw18524step0 raw18524step0Labels := by
      have hz : ∀ j, raw18524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18524step0 = (fun i j => raw18524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18524step0 raw18524; decide +kernel
      have hl : raw18524step0Labels = raw18524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18524 raw18524Labels permutation346 hz
    mixedMoment B raw18524step0 raw18524step0Labels = mixedMoment B raw18524step1 raw18524step1Labels := by
      have ha : raw18524step1 = (fun i j => raw18524step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18524step1 raw18524step0; decide +kernel
      have hl : raw18524step1Labels = raw18524step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18524step0 raw18524step0Labels permutation33 permutation6
    mixedMoment B raw18524step1 raw18524step1Labels = mixedMoment B raw18524step2 raw18524step2Labels := by
      have ha : raw18524step2 = raw18524step1 := by apply Matrix.ext; unfold raw18524step2 raw18524step1; decide +kernel
      have hl : raw18524step1Labels = labelEmbedding9 ∘ raw18524step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18524step1 raw18524step1Labels raw18524step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

theorem canonical18525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18525 raw18525Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw18525 raw18525Labels = mixedMoment B raw18525step0 raw18525step0Labels := by
      have hz : ∀ j, raw18525 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18525step0 = (fun i j => raw18525 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18525step0 raw18525; decide +kernel
      have hl : raw18525step0Labels = raw18525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18525 raw18525Labels permutation346 hz
    mixedMoment B raw18525step0 raw18525step0Labels = mixedMoment B raw18525step1 raw18525step1Labels := by
      have ha : raw18525step1 = (fun i j => raw18525step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18525step1 raw18525step0; decide +kernel
      have hl : raw18525step1Labels = raw18525step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18525step0 raw18525step0Labels permutation40 permutation4
    mixedMoment B raw18525step1 raw18525step1Labels = mixedMoment B raw18525step2 raw18525step2Labels := by
      have ha : raw18525step2 = -raw18525step1 := by apply Matrix.ext; change ∀ i j, raw18525step2 i j = -(raw18525step1 i j); unfold raw18525step2 raw18525step1; decide +kernel
      have hl : raw18525step2Labels = raw18525step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18525step2 raw18525step2Labels = mixedMoment B raw18525step3 raw18525step3Labels := by
      have ha : raw18525step3 = raw18525step2 := by apply Matrix.ext; unfold raw18525step3 raw18525step2; decide +kernel
      have hl : raw18525step2Labels = labelEmbedding7 ∘ raw18525step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18525step2 raw18525step2Labels raw18525step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

theorem canonical18526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18526 raw18526Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw18526 raw18526Labels = mixedMoment B raw18526step0 raw18526step0Labels := by
      have ha : raw18526step0 = (fun i j => raw18526 (permutation184 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18526step0 raw18526; decide +kernel
      have hl : raw18526step0Labels = raw18526Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18526 raw18526Labels permutation184 permutation4
    mixedMoment B raw18526step0 raw18526step0Labels = mixedMoment B raw18526step1 raw18526step1Labels := by
      have ha : raw18526step1 = -raw18526step0 := by apply Matrix.ext; change ∀ i j, raw18526step1 i j = -(raw18526step0 i j); unfold raw18526step1 raw18526step0; decide +kernel
      have hl : raw18526step1Labels = raw18526step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18526step1 raw18526step1Labels = mixedMoment B raw18526step2 raw18526step2Labels := by
      have ha : raw18526step2 = raw18526step1 := by apply Matrix.ext; unfold raw18526step2 raw18526step1; decide +kernel
      have hl : raw18526step1Labels = labelEmbedding7 ∘ raw18526step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18526step1 raw18526step1Labels raw18526step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

theorem canonical18527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18527 raw18527Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw18527 raw18527Labels = mixedMoment B raw18527step0 raw18527step0Labels := by
      have hz : ∀ j, raw18527 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18527step0 = (fun i j => raw18527 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18527step0 raw18527; decide +kernel
      have hl : raw18527step0Labels = raw18527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18527 raw18527Labels permutation346 hz
    mixedMoment B raw18527step0 raw18527step0Labels = mixedMoment B raw18527step1 raw18527step1Labels := by
      have ha : raw18527step1 = (fun i j => raw18527step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18527step1 raw18527step0; decide +kernel
      have hl : raw18527step1Labels = raw18527step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18527step0 raw18527step0Labels permutation40 permutation4
    mixedMoment B raw18527step1 raw18527step1Labels = mixedMoment B raw18527step2 raw18527step2Labels := by
      have ha : raw18527step2 = -raw18527step1 := by apply Matrix.ext; change ∀ i j, raw18527step2 i j = -(raw18527step1 i j); unfold raw18527step2 raw18527step1; decide +kernel
      have hl : raw18527step2Labels = raw18527step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18527step2 raw18527step2Labels = mixedMoment B raw18527step3 raw18527step3Labels := by
      have ha : raw18527step3 = raw18527step2 := by apply Matrix.ext; unfold raw18527step3 raw18527step2; decide +kernel
      have hl : raw18527step2Labels = labelEmbedding7 ∘ raw18527step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18527step2 raw18527step2Labels raw18527step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

theorem canonical18528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18528 raw18528Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw18528 raw18528Labels = mixedMoment B raw18528step0 raw18528step0Labels := by
      have hz : ∀ j, raw18528 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18528step0 = (fun i j => raw18528 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18528step0 raw18528; decide +kernel
      have hl : raw18528step0Labels = raw18528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18528 raw18528Labels permutation346 hz
    mixedMoment B raw18528step0 raw18528step0Labels = mixedMoment B raw18528step1 raw18528step1Labels := by
      have ha : raw18528step1 = (fun i j => raw18528step0 (permutation46 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18528step1 raw18528step0; decide +kernel
      have hl : raw18528step1Labels = raw18528step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18528step0 raw18528step0Labels permutation46 permutation4
    mixedMoment B raw18528step1 raw18528step1Labels = mixedMoment B raw18528step2 raw18528step2Labels := by
      have ha : raw18528step2 = -raw18528step1 := by apply Matrix.ext; change ∀ i j, raw18528step2 i j = -(raw18528step1 i j); unfold raw18528step2 raw18528step1; decide +kernel
      have hl : raw18528step2Labels = raw18528step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18528step2 raw18528step2Labels = mixedMoment B raw18528step3 raw18528step3Labels := by
      have ha : raw18528step3 = raw18528step2 := by apply Matrix.ext; unfold raw18528step3 raw18528step2; decide +kernel
      have hl : raw18528step2Labels = labelEmbedding7 ∘ raw18528step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18528step2 raw18528step2Labels raw18528step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

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

theorem canonical2292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2292 raw2292Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw2292 raw2292Labels = mixedMoment B raw2292step0 raw2292step0Labels := by
      have ha : raw2292step0 = (fun i j => raw2292 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2292step0 raw2292; decide +kernel
      have hl : raw2292step0Labels = raw2292Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2292 raw2292Labels permutation32 permutation4
    mixedMoment B raw2292step0 raw2292step0Labels = mixedMoment B raw2292step1 raw2292step1Labels := by
      have ha : raw2292step1 = raw2292step0 := by apply Matrix.ext; unfold raw2292step1 raw2292step0; decide +kernel
      have hl : raw2292step0Labels = labelEmbedding7 ∘ raw2292step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2292step0 raw2292step0Labels raw2292step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

theorem canonical2293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2293 raw2293Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw2293 raw2293Labels = mixedMoment B raw2293step0 raw2293step0Labels := by
      have ha : raw2293step0 = (fun i j => raw2293 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2293step0 raw2293; decide +kernel
      have hl : raw2293step0Labels = raw2293Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2293 raw2293Labels permutation32 permutation4
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2294 raw2294Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw2294 raw2294Labels = mixedMoment B raw2294step0 raw2294step0Labels := by
      have ha : raw2294step0 = (fun i j => raw2294 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2294step0 raw2294; decide +kernel
      have hl : raw2294step0Labels = raw2294Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2294 raw2294Labels permutation38 permutation6
    mixedMoment B raw2294step0 raw2294step0Labels = mixedMoment B raw2294step1 raw2294step1Labels := by
      have ha : raw2294step1 = -raw2294step0 := by apply Matrix.ext; change ∀ i j, raw2294step1 i j = -(raw2294step0 i j); unfold raw2294step1 raw2294step0; decide +kernel
      have hl : raw2294step1Labels = raw2294step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2294step1 raw2294step1Labels = mixedMoment B raw2294step2 raw2294step2Labels := by
      have ha : raw2294step2 = raw2294step1 := by apply Matrix.ext; unfold raw2294step2 raw2294step1; decide +kernel
      have hl : raw2294step1Labels = labelEmbedding1 ∘ raw2294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2294step1 raw2294step1Labels raw2294step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2310 raw2310Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw2310 raw2310Labels = mixedMoment B raw2310step0 raw2310step0Labels := by
      have ha : raw2310step0 = (fun i j => raw2310 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2310step0 raw2310; decide +kernel
      have hl : raw2310step0Labels = raw2310Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2310 raw2310Labels permutation32 permutation5
    mixedMoment B raw2310step0 raw2310step0Labels = mixedMoment B raw2310step1 raw2310step1Labels := by
      have ha : raw2310step1 = raw2310step0 := by apply Matrix.ext; unfold raw2310step1 raw2310step0; decide +kernel
      have hl : raw2310step0Labels = labelEmbedding8 ∘ raw2310step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2310step0 raw2310step0Labels raw2310step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

theorem canonical2311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2311 raw2311Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw2311 raw2311Labels = mixedMoment B raw2311step0 raw2311step0Labels := by
      have ha : raw2311step0 = (fun i j => raw2311 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2311step0 raw2311; decide +kernel
      have hl : raw2311step0Labels = raw2311Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2311 raw2311Labels permutation32 permutation4
    _ = mixedMoment B node3053 node3053Labels := by rfl

theorem canonical2312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2312 raw2312Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw2312 raw2312Labels = mixedMoment B raw2312step0 raw2312step0Labels := by
      have ha : raw2312step0 = (fun i j => raw2312 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2312step0 raw2312; decide +kernel
      have hl : raw2312step0Labels = raw2312Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2312 raw2312Labels permutation41 permutation3
    mixedMoment B raw2312step0 raw2312step0Labels = mixedMoment B raw2312step1 raw2312step1Labels := by
      have ha : raw2312step1 = -raw2312step0 := by apply Matrix.ext; change ∀ i j, raw2312step1 i j = -(raw2312step0 i j); unfold raw2312step1 raw2312step0; decide +kernel
      have hl : raw2312step1Labels = raw2312step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2312step1 raw2312step1Labels = mixedMoment B raw2312step2 raw2312step2Labels := by
      have ha : raw2312step2 = raw2312step1 := by apply Matrix.ext; unfold raw2312step2 raw2312step1; decide +kernel
      have hl : raw2312step1Labels = labelEmbedding1 ∘ raw2312step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2312step1 raw2312step1Labels raw2312step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3619 node3619Labels := by rfl

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

theorem canonical2520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2520 raw2520Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw2520 raw2520Labels = mixedMoment B raw2520step0 raw2520step0Labels := by
      have ha : raw2520step0 = (fun i j => raw2520 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2520step0 raw2520; decide +kernel
      have hl : raw2520step0Labels = raw2520Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2520 raw2520Labels permutation152 permutation4
    mixedMoment B raw2520step0 raw2520step0Labels = mixedMoment B raw2520step1 raw2520step1Labels := by
      have ha : raw2520step1 = raw2520step0 := by apply Matrix.ext; unfold raw2520step1 raw2520step0; decide +kernel
      have hl : raw2520step0Labels = labelEmbedding7 ∘ raw2520step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2520step0 raw2520step0Labels raw2520step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

theorem canonical2521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2521 raw2521Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw2521 raw2521Labels = mixedMoment B raw2521step0 raw2521step0Labels := by
      have ha : raw2521step0 = (fun i j => raw2521 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2521step0 raw2521; decide +kernel
      have hl : raw2521step0Labels = raw2521Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2521 raw2521Labels permutation152 permutation4
    _ = mixedMoment B node3849 node3849Labels := by rfl

theorem canonical2522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2522 raw2522Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw2522 raw2522Labels = mixedMoment B raw2522step0 raw2522step0Labels := by
      have ha : raw2522step0 = (fun i j => raw2522 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2522step0 raw2522; decide +kernel
      have hl : raw2522step0Labels = raw2522Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2522 raw2522Labels permutation200 permutation6
    mixedMoment B raw2522step0 raw2522step0Labels = mixedMoment B raw2522step1 raw2522step1Labels := by
      have ha : raw2522step1 = -raw2522step0 := by apply Matrix.ext; change ∀ i j, raw2522step1 i j = -(raw2522step0 i j); unfold raw2522step1 raw2522step0; decide +kernel
      have hl : raw2522step1Labels = raw2522step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2522step1 raw2522step1Labels = mixedMoment B raw2522step2 raw2522step2Labels := by
      have ha : raw2522step2 = raw2522step1 := by apply Matrix.ext; unfold raw2522step2 raw2522step1; decide +kernel
      have hl : raw2522step1Labels = labelEmbedding1 ∘ raw2522step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2522step1 raw2522step1Labels raw2522step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

theorem canonical2547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2547 raw2547Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw2547 raw2547Labels = mixedMoment B raw2547step0 raw2547step0Labels := by
      have ha : raw2547step0 = (fun i j => raw2547 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2547step0 raw2547; decide +kernel
      have hl : raw2547step0Labels = raw2547Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2547 raw2547Labels permutation152 permutation5
    mixedMoment B raw2547step0 raw2547step0Labels = mixedMoment B raw2547step1 raw2547step1Labels := by
      have ha : raw2547step1 = raw2547step0 := by apply Matrix.ext; unfold raw2547step1 raw2547step0; decide +kernel
      have hl : raw2547step0Labels = labelEmbedding8 ∘ raw2547step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2547step0 raw2547step0Labels raw2547step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

theorem canonical2548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2548 raw2548Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw2548 raw2548Labels = mixedMoment B raw2548step0 raw2548step0Labels := by
      have ha : raw2548step0 = (fun i j => raw2548 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2548step0 raw2548; decide +kernel
      have hl : raw2548step0Labels = raw2548Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2548 raw2548Labels permutation152 permutation4
    _ = mixedMoment B node4025 node4025Labels := by rfl

theorem canonical2549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2549 raw2549Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw2549 raw2549Labels = mixedMoment B raw2549step0 raw2549step0Labels := by
      have ha : raw2549step0 = (fun i j => raw2549 (permutation216 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2549step0 raw2549; decide +kernel
      have hl : raw2549step0Labels = raw2549Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2549 raw2549Labels permutation216 permutation3
    mixedMoment B raw2549step0 raw2549step0Labels = mixedMoment B raw2549step1 raw2549step1Labels := by
      have ha : raw2549step1 = -raw2549step0 := by apply Matrix.ext; change ∀ i j, raw2549step1 i j = -(raw2549step0 i j); unfold raw2549step1 raw2549step0; decide +kernel
      have hl : raw2549step1Labels = raw2549step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2549step1 raw2549step1Labels = mixedMoment B raw2549step2 raw2549step2Labels := by
      have ha : raw2549step2 = raw2549step1 := by apply Matrix.ext; unfold raw2549step2 raw2549step1; decide +kernel
      have hl : raw2549step1Labels = labelEmbedding1 ∘ raw2549step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2549step1 raw2549step1Labels raw2549step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3909 node3909Labels := by rfl

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

theorem canonical2586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2586 raw2586Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw2586 raw2586Labels = mixedMoment B raw2586step0 raw2586step0Labels := by
      have ha : raw2586step0 = (fun i j => raw2586 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2586step0 raw2586; decide +kernel
      have hl : raw2586step0Labels = raw2586Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2586 raw2586Labels permutation152 permutation4
    mixedMoment B raw2586step0 raw2586step0Labels = mixedMoment B raw2586step1 raw2586step1Labels := by
      have ha : raw2586step1 = raw2586step0 := by apply Matrix.ext; unfold raw2586step1 raw2586step0; decide +kernel
      have hl : raw2586step0Labels = labelEmbedding7 ∘ raw2586step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2586step0 raw2586step0Labels raw2586step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5472 node5472Labels := by rfl

theorem canonical2587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2587 raw2587Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw2587 raw2587Labels = mixedMoment B raw2587step0 raw2587step0Labels := by
      have ha : raw2587step0 = (fun i j => raw2587 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2587step0 raw2587; decide +kernel
      have hl : raw2587step0Labels = raw2587Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2587 raw2587Labels permutation152 permutation4
    _ = mixedMoment B node3957 node3957Labels := by rfl

theorem canonical2588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2588 raw2588Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw2588 raw2588Labels = mixedMoment B raw2588step0 raw2588step0Labels := by
      have ha : raw2588step0 = (fun i j => raw2588 (permutation271 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2588step0 raw2588; decide +kernel
      have hl : raw2588step0Labels = raw2588Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2588 raw2588Labels permutation271 permutation6
    mixedMoment B raw2588step0 raw2588step0Labels = mixedMoment B raw2588step1 raw2588step1Labels := by
      have ha : raw2588step1 = -raw2588step0 := by apply Matrix.ext; change ∀ i j, raw2588step1 i j = -(raw2588step0 i j); unfold raw2588step1 raw2588step0; decide +kernel
      have hl : raw2588step1Labels = raw2588step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2588step1 raw2588step1Labels = mixedMoment B raw2588step2 raw2588step2Labels := by
      have ha : raw2588step2 = raw2588step1 := by apply Matrix.ext; unfold raw2588step2 raw2588step1; decide +kernel
      have hl : raw2588step1Labels = labelEmbedding1 ∘ raw2588step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2588step1 raw2588step1Labels raw2588step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3957 node3957Labels := by rfl

theorem canonical2589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2589 raw2589Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw2589 raw2589Labels = mixedMoment B raw2589step0 raw2589step0Labels := by
      have ha : raw2589step0 = (fun i j => raw2589 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2589step0 raw2589; decide +kernel
      have hl : raw2589step0Labels = raw2589Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2589 raw2589Labels permutation32 permutation4
    mixedMoment B raw2589step0 raw2589step0Labels = mixedMoment B raw2589step1 raw2589step1Labels := by
      have ha : raw2589step1 = raw2589step0 := by apply Matrix.ext; unfold raw2589step1 raw2589step0; decide +kernel
      have hl : raw2589step0Labels = labelEmbedding7 ∘ raw2589step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2589step0 raw2589step0Labels raw2589step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical2590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2590 raw2590Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw2590 raw2590Labels = mixedMoment B raw2590step0 raw2590step0Labels := by
      have ha : raw2590step0 = (fun i j => raw2590 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2590step0 raw2590; decide +kernel
      have hl : raw2590step0Labels = raw2590Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2590 raw2590Labels permutation32 permutation4
    _ = mixedMoment B node3958 node3958Labels := by rfl

theorem canonical2591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2591 raw2591Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw2591 raw2591Labels = mixedMoment B raw2591step0 raw2591step0Labels := by
      have ha : raw2591step0 = (fun i j => raw2591 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2591step0 raw2591; decide +kernel
      have hl : raw2591step0Labels = raw2591Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2591 raw2591Labels permutation56 permutation6
    mixedMoment B raw2591step0 raw2591step0Labels = mixedMoment B raw2591step1 raw2591step1Labels := by
      have ha : raw2591step1 = -raw2591step0 := by apply Matrix.ext; change ∀ i j, raw2591step1 i j = -(raw2591step0 i j); unfold raw2591step1 raw2591step0; decide +kernel
      have hl : raw2591step1Labels = raw2591step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2591step1 raw2591step1Labels = mixedMoment B raw2591step2 raw2591step2Labels := by
      have ha : raw2591step2 = raw2591step1 := by apply Matrix.ext; unfold raw2591step2 raw2591step1; decide +kernel
      have hl : raw2591step1Labels = labelEmbedding1 ∘ raw2591step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2591step1 raw2591step1Labels raw2591step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

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

theorem singleton5290 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5290 node5290Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2764 node2764Labels + mixedMoment B node3581 node3581Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2292 singletonSmall5290
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5290) = raw2292Labels := by decide +kernel
  rw [hl, canonical2292 B hB] at h
  have hc0 : mixedMoment B raw2292 (Fin.cases (0 : Fin 2) singletonSmall5290) =
      mixedMoment B node2764 node2764Labels := by
    have ha : raw2292 = raw2293 := by apply Matrix.ext; unfold raw2292 raw2293; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5290 = raw2293Labels := by decide +kernel
    rw [ha, hj, canonical2293 B hB]
  have hc1 : mixedMoment B raw2292 (Fin.cases (1 : Fin 2) singletonSmall5290) =
      mixedMoment B node3581 node3581Labels := by
    have ha : raw2292 = raw2294 := by apply Matrix.ext; unfold raw2292 raw2294; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5290 = raw2294Labels := by decide +kernel
    rw [ha, hj, canonical2294 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5301 node5301Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3053 node3053Labels + mixedMoment B node3619 node3619Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2310 singletonSmall5301
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5301) = raw2310Labels := by decide +kernel
  rw [hl, canonical2310 B hB] at h
  have hc0 : mixedMoment B raw2310 (Fin.cases (0 : Fin 2) singletonSmall5301) =
      mixedMoment B node3053 node3053Labels := by
    have ha : raw2310 = raw2311 := by apply Matrix.ext; unfold raw2310 raw2311; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5301 = raw2311Labels := by decide +kernel
    rw [ha, hj, canonical2311 B hB]
  have hc1 : mixedMoment B raw2310 (Fin.cases (1 : Fin 2) singletonSmall5301) =
      mixedMoment B node3619 node3619Labels := by
    have ha : raw2310 = raw2312 := by apply Matrix.ext; unfold raw2310 raw2312; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5301 = raw2312Labels := by decide +kernel
    rw [ha, hj, canonical2312 B hB]
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

theorem singleton5431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5431 node5431Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3849 node3849Labels + mixedMoment B node3875 node3875Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2520 singletonSmall5431
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5431) = raw2520Labels := by decide +kernel
  rw [hl, canonical2520 B hB] at h
  have hc0 : mixedMoment B raw2520 (Fin.cases (0 : Fin 2) singletonSmall5431) =
      mixedMoment B node3849 node3849Labels := by
    have ha : raw2520 = raw2521 := by apply Matrix.ext; unfold raw2520 raw2521; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5431 = raw2521Labels := by decide +kernel
    rw [ha, hj, canonical2521 B hB]
  have hc1 : mixedMoment B raw2520 (Fin.cases (1 : Fin 2) singletonSmall5431) =
      mixedMoment B node3875 node3875Labels := by
    have ha : raw2520 = raw2522 := by apply Matrix.ext; unfold raw2520 raw2522; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5431 = raw2522Labels := by decide +kernel
    rw [ha, hj, canonical2522 B hB]
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

theorem singleton5447 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5447 node5447Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node4025 node4025Labels + mixedMoment B node3909 node3909Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2547 singletonSmall5447
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5447) = raw2547Labels := by decide +kernel
  rw [hl, canonical2547 B hB] at h
  have hc0 : mixedMoment B raw2547 (Fin.cases (0 : Fin 2) singletonSmall5447) =
      mixedMoment B node4025 node4025Labels := by
    have ha : raw2547 = raw2548 := by apply Matrix.ext; unfold raw2547 raw2548; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5447 = raw2548Labels := by decide +kernel
    rw [ha, hj, canonical2548 B hB]
  have hc1 : mixedMoment B raw2547 (Fin.cases (1 : Fin 2) singletonSmall5447) =
      mixedMoment B node3909 node3909Labels := by
    have ha : raw2547 = raw2549 := by apply Matrix.ext; unfold raw2547 raw2549; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5447 = raw2549Labels := by decide +kernel
    rw [ha, hj, canonical2549 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton5472 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5472 node5472Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3957 node3957Labels + mixedMoment B node3957 node3957Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2586 singletonSmall5472
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5472) = raw2586Labels := by decide +kernel
  rw [hl, canonical2586 B hB] at h
  have hc0 : mixedMoment B raw2586 (Fin.cases (0 : Fin 2) singletonSmall5472) =
      mixedMoment B node3957 node3957Labels := by
    have ha : raw2586 = raw2587 := by apply Matrix.ext; unfold raw2586 raw2587; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5472 = raw2587Labels := by decide +kernel
    rw [ha, hj, canonical2587 B hB]
  have hc1 : mixedMoment B raw2586 (Fin.cases (1 : Fin 2) singletonSmall5472) =
      mixedMoment B node3957 node3957Labels := by
    have ha : raw2586 = raw2588 := by apply Matrix.ext; unfold raw2586 raw2588; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5472 = raw2588Labels := by decide +kernel
    rw [ha, hj, canonical2588 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5473 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5473 node5473Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3958 node3958Labels + mixedMoment B node3961 node3961Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2589 singletonSmall5473
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5473) = raw2589Labels := by decide +kernel
  rw [hl, canonical2589 B hB] at h
  have hc0 : mixedMoment B raw2589 (Fin.cases (0 : Fin 2) singletonSmall5473) =
      mixedMoment B node3958 node3958Labels := by
    have ha : raw2589 = raw2590 := by apply Matrix.ext; unfold raw2589 raw2590; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5473 = raw2590Labels := by decide +kernel
    rw [ha, hj, canonical2590 B hB]
  have hc1 : mixedMoment B raw2589 (Fin.cases (1 : Fin 2) singletonSmall5473) =
      mixedMoment B node3961 node3961Labels := by
    have ha : raw2589 = raw2591 := by apply Matrix.ext; unfold raw2589 raw2591; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5473 = raw2591Labels := by decide +kernel
    rw [ha, hj, canonical2591 B hB]
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

theorem zero5474 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5474 node5474Labels = 0 := by
  exact mixedMoment_order_one B hB node5474 node5474Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5486 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5486 node5486Labels = 0 := by
  exact mixedMoment_order_one B hB node5486 node5486Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2764 node2764Labels = Sparse.eval nodeValue2764 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2764) = mixedMoment B node2764 node2764Labels := rfl
  simpa [nodeValue2764, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3053 node3053Labels = Sparse.eval nodeValue3053 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3053) = mixedMoment B node3053 node3053Labels := rfl
  simpa [nodeValue3053, Sparse.eval] using hc.symm

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

theorem sound3581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3581 node3581Labels = Sparse.eval nodeValue3581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3581) = mixedMoment B node3581 node3581Labels := rfl
  simpa [nodeValue3581, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3619 node3619Labels = Sparse.eval nodeValue3619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3619) = mixedMoment B node3619 node3619Labels := rfl
  simpa [nodeValue3619, Sparse.eval] using hc.symm

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

theorem sound3849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3849 node3849Labels = Sparse.eval nodeValue3849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3849) = mixedMoment B node3849 node3849Labels := rfl
  simpa [nodeValue3849, Sparse.eval] using hc.symm

theorem sound3875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3875 node3875Labels = Sparse.eval nodeValue3875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3875) = mixedMoment B node3875 node3875Labels := rfl
  simpa [nodeValue3875, Sparse.eval] using hc.symm

theorem sound3885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3885 node3885Labels = Sparse.eval nodeValue3885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3885) = mixedMoment B node3885 node3885Labels := rfl
  simpa [nodeValue3885, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3909 node3909Labels = Sparse.eval nodeValue3909 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3909) = mixedMoment B node3909 node3909Labels := rfl
  simpa [nodeValue3909, Sparse.eval] using hc.symm

theorem sound3957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3957 node3957Labels = Sparse.eval nodeValue3957 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3957) = mixedMoment B node3957 node3957Labels := rfl
  simpa [nodeValue3957, Sparse.eval] using hc.symm

theorem sound3958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3958 node3958Labels = Sparse.eval nodeValue3958 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3958) = mixedMoment B node3958 node3958Labels := rfl
  simpa [nodeValue3958, Sparse.eval] using hc.symm

theorem sound3961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3961 node3961Labels = Sparse.eval nodeValue3961 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3961) = mixedMoment B node3961 node3961Labels := rfl
  simpa [nodeValue3961, Sparse.eval] using hc.symm

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

theorem sound4025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4025 node4025Labels = Sparse.eval nodeValue4025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4025) = mixedMoment B node4025 node4025Labels := rfl
  simpa [nodeValue4025, Sparse.eval] using hc.symm

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

theorem sound5265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5265 node5265Labels = Sparse.eval nodeValue5265 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5265) = mixedMoment B node5265 node5265Labels := rfl
  simpa [nodeValue5265, Sparse.eval] using hc.symm

theorem sound5266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5266 node5266Labels = Sparse.eval nodeValue5266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5266) = mixedMoment B node5266 node5266Labels := rfl
  simpa [nodeValue5266, Sparse.eval] using hc.symm

theorem sound5270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5270 node5270Labels = Sparse.eval nodeValue5270 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5270) = mixedMoment B node5270 node5270Labels := rfl
  simpa [nodeValue5270, Sparse.eval] using hc.symm

theorem sound5281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5281 node5281Labels = Sparse.eval nodeValue5281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5281) = mixedMoment B node5281 node5281Labels := rfl
  simpa [nodeValue5281, Sparse.eval] using hc.symm

theorem sound5282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5282 node5282Labels = Sparse.eval nodeValue5282 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5282) = mixedMoment B node5282 node5282Labels := rfl
  simpa [nodeValue5282, Sparse.eval] using hc.symm

theorem sound5290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5290 node5290Labels = Sparse.eval nodeValue5290 (mixedVector B) := by
  have h := singleton5290 B _hB
  rw [sound2764 B _hB _hF, sound3581 B _hB _hF] at h
  norm_num [nodeValue5290, nodeValue2764, nodeValue3581, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5301 node5301Labels = Sparse.eval nodeValue5301 (mixedVector B) := by
  have h := singleton5301 B _hB
  rw [sound3053 B _hB _hF, sound3619 B _hB _hF] at h
  norm_num [nodeValue5301, nodeValue3053, nodeValue3619, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5429 node5429Labels = Sparse.eval nodeValue5429 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5429) = mixedMoment B node5429 node5429Labels := rfl
  simpa [nodeValue5429, Sparse.eval] using hc.symm

theorem sound5431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5431 node5431Labels = Sparse.eval nodeValue5431 (mixedVector B) := by
  have h := singleton5431 B _hB
  rw [sound3849 B _hB _hF, sound3875 B _hB _hF] at h
  norm_num [nodeValue5431, nodeValue3849, nodeValue3875, Sparse.eval] at h ⊢
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

theorem sound5446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5446 node5446Labels = Sparse.eval nodeValue5446 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5446) = mixedMoment B node5446 node5446Labels := rfl
  simpa [nodeValue5446, Sparse.eval] using hc.symm

theorem sound5447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5447 node5447Labels = Sparse.eval nodeValue5447 (mixedVector B) := by
  have h := singleton5447 B _hB
  rw [sound3909 B _hB _hF, sound4025 B _hB _hF] at h
  norm_num [nodeValue5447, nodeValue3909, nodeValue4025, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5448 node5448Labels = Sparse.eval nodeValue5448 (mixedVector B) := by
  have h := singleton5448 B _hB
  rw [sound3885 B _hB _hF] at h
  norm_num [nodeValue5448, nodeValue3885, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5472 node5472Labels = Sparse.eval nodeValue5472 (mixedVector B) := by
  have h := singleton5472 B _hB
  rw [sound3957 B _hB _hF] at h
  norm_num [nodeValue5472, nodeValue3957, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5473 node5473Labels = Sparse.eval nodeValue5473 (mixedVector B) := by
  have h := singleton5473 B _hB
  rw [sound3958 B _hB _hF, sound3961 B _hB _hF] at h
  norm_num [nodeValue5473, nodeValue3958, nodeValue3961, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5474 node5474Labels = Sparse.eval nodeValue5474 (mixedVector B) := by
  simpa only [nodeValue5474, Sparse.eval_nil] using zero5474 B _hB _hF

theorem sound5486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5486 node5486Labels = Sparse.eval nodeValue5486 (mixedVector B) := by
  simpa only [nodeValue5486, Sparse.eval_nil] using zero5486 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources34
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1104 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1104 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1104 + difference 0 1) (sourceB1104 + difference 1 0) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA1104 + difference 0 1) (sourceB1104 + difference 1 0) sourceC1104) = raw18404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18404; decide +kernel
    rw [ha]
    exact (canonical18404 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1104 + difference 0 2) (sourceB1104 + difference 2 0) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA1104 + difference 0 2) (sourceB1104 + difference 2 0) sourceC1104) = raw18507 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18507; decide +kernel
    rw [ha]
    exact (canonical18507 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1104 + difference 0 3) (sourceB1104 + difference 3 0) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1104 + difference 0 3) (sourceB1104 + difference 3 0) sourceC1104) = raw18508 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18508; decide +kernel
    rw [ha]
    exact (canonical18508 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1104 + difference 0 4) (sourceB1104 + difference 4 0) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA1104 + difference 0 4) (sourceB1104 + difference 4 0) sourceC1104) = raw18509 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18509; decide +kernel
    rw [ha]
    exact (canonical18509 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1104 + difference 0 5) (sourceB1104 + difference 5 0) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5474) := by
    have ha : (tripleCharges (sourceA1104 + difference 0 5) (sourceB1104 + difference 5 0) sourceC1104) = raw18510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18510; decide +kernel
    rw [ha]
    exact (canonical18510 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1104 + difference 1 0) (sourceB1104 + difference 0 1) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA1104 + difference 1 0) (sourceB1104 + difference 0 1) sourceC1104) = raw18511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18511; decide +kernel
    rw [ha]
    exact (canonical18511 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1104 + difference 1 2) (sourceB1104 + difference 2 1) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA1104 + difference 1 2) (sourceB1104 + difference 2 1) sourceC1104) = raw18512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18512; decide +kernel
    rw [ha]
    exact (canonical18512 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1104 + difference 1 3) (sourceB1104 + difference 3 1) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA1104 + difference 1 3) (sourceB1104 + difference 3 1) sourceC1104) = raw18513 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18513; decide +kernel
    rw [ha]
    exact (canonical18513 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1104 + difference 1 4) (sourceB1104 + difference 4 1) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA1104 + difference 1 4) (sourceB1104 + difference 4 1) sourceC1104) = raw18514 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18514; decide +kernel
    rw [ha]
    exact (canonical18514 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1104 + difference 1 5) (sourceB1104 + difference 5 1) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA1104 + difference 1 5) (sourceB1104 + difference 5 1) sourceC1104) = raw18515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18515; decide +kernel
    rw [ha]
    exact (canonical18515 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1104 + difference 2 0) (sourceB1104 + difference 0 2) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA1104 + difference 2 0) (sourceB1104 + difference 0 2) sourceC1104) = raw18408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18408; decide +kernel
    rw [ha]
    exact (canonical18408 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1104 + difference 2 1) (sourceB1104 + difference 1 2) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA1104 + difference 2 1) (sourceB1104 + difference 1 2) sourceC1104) = raw18516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18516; decide +kernel
    rw [ha]
    exact (canonical18516 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1104 + difference 2 3) (sourceB1104 + difference 3 2) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1104 + difference 2 3) (sourceB1104 + difference 3 2) sourceC1104) = raw18410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18410; decide +kernel
    rw [ha]
    exact (canonical18410 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1104 + difference 2 4) (sourceB1104 + difference 4 2) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA1104 + difference 2 4) (sourceB1104 + difference 4 2) sourceC1104) = raw18411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18411; decide +kernel
    rw [ha]
    exact (canonical18411 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1104 + difference 2 5) (sourceB1104 + difference 5 2) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA1104 + difference 2 5) (sourceB1104 + difference 5 2) sourceC1104) = raw18412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18412; decide +kernel
    rw [ha]
    exact (canonical18412 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1104 + difference 3 0) (sourceB1104 + difference 0 3) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA1104 + difference 3 0) (sourceB1104 + difference 0 3) sourceC1104) = raw18517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18517; decide +kernel
    rw [ha]
    exact (canonical18517 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1104 + difference 3 1) (sourceB1104 + difference 1 3) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1104 + difference 3 1) (sourceB1104 + difference 1 3) sourceC1104) = raw18420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18420; decide +kernel
    rw [ha]
    exact (canonical18420 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1104 + difference 3 2) (sourceB1104 + difference 2 3) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1104 + difference 3 2) (sourceB1104 + difference 2 3) sourceC1104) = raw18518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18518; decide +kernel
    rw [ha]
    exact (canonical18518 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1104 + difference 3 4) (sourceB1104 + difference 4 3) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1104 + difference 3 4) (sourceB1104 + difference 4 3) sourceC1104) = raw18519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18519; decide +kernel
    rw [ha]
    exact (canonical18519 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1104 + difference 3 5) (sourceB1104 + difference 5 3) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1104 + difference 3 5) (sourceB1104 + difference 5 3) sourceC1104) = raw18520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18520; decide +kernel
    rw [ha]
    exact (canonical18520 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1104 + difference 4 0) (sourceB1104 + difference 0 4) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA1104 + difference 4 0) (sourceB1104 + difference 0 4) sourceC1104) = raw18521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18521; decide +kernel
    rw [ha]
    exact (canonical18521 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1104 + difference 4 1) (sourceB1104 + difference 1 4) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA1104 + difference 4 1) (sourceB1104 + difference 1 4) sourceC1104) = raw18425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18425; decide +kernel
    rw [ha]
    exact (canonical18425 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1104 + difference 4 2) (sourceB1104 + difference 2 4) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA1104 + difference 4 2) (sourceB1104 + difference 2 4) sourceC1104) = raw18522 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18522; decide +kernel
    rw [ha]
    exact (canonical18522 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1104 + difference 4 3) (sourceB1104 + difference 3 4) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA1104 + difference 4 3) (sourceB1104 + difference 3 4) sourceC1104) = raw18523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18523; decide +kernel
    rw [ha]
    exact (canonical18523 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1104 + difference 4 5) (sourceB1104 + difference 5 4) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA1104 + difference 4 5) (sourceB1104 + difference 5 4) sourceC1104) = raw18524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18524; decide +kernel
    rw [ha]
    exact (canonical18524 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1104 + difference 5 0) (sourceB1104 + difference 0 5) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA1104 + difference 5 0) (sourceB1104 + difference 0 5) sourceC1104) = raw18525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18525; decide +kernel
    rw [ha]
    exact (canonical18525 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1104 + difference 5 1) (sourceB1104 + difference 1 5) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA1104 + difference 5 1) (sourceB1104 + difference 1 5) sourceC1104) = raw18430 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18430; decide +kernel
    rw [ha]
    exact (canonical18430 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1104 + difference 5 2) (sourceB1104 + difference 2 5) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA1104 + difference 5 2) (sourceB1104 + difference 2 5) sourceC1104) = raw18526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18526; decide +kernel
    rw [ha]
    exact (canonical18526 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1104 + difference 5 3) (sourceB1104 + difference 3 5) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1104 + difference 5 3) (sourceB1104 + difference 3 5) sourceC1104) = raw18527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18527; decide +kernel
    rw [ha]
    exact (canonical18527 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1104 + difference 5 4) (sourceB1104 + difference 4 5) sourceC1104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA1104 + difference 5 4) (sourceB1104 + difference 4 5) sourceC1104) = raw18528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1104 sourceB1104 sourceC1104 difference raw18528; decide +kernel
    rw [ha]
    exact (canonical18528 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1104 sourceB1104 sourceC1104
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1104, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck957 : Integer.Sparse.reindex keyMap MixedData.row957 = numericRow957 := by decide +kernel

theorem numericCheck957 (x : Master → ℝ) : Integer.Sparse.eval numericRow957 x =
    (8640 : ℝ) * reducedSource957 x := by
  norm_num [numericRow957, reducedSource957, Integer.Sparse.eval, Sparse.eval, nodeValue5265, nodeValue5266, nodeValue5270, nodeValue5281, nodeValue5282, nodeValue5290, nodeValue5301, nodeValue5429, nodeValue5431, nodeValue5433, nodeValue5439, nodeValue5440, nodeValue5445, nodeValue5446, nodeValue5447, nodeValue5448, nodeValue5450, nodeValue5472, nodeValue5473, nodeValue5474, nodeValue5486] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero957 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource957 (mixedVector B) = 0 := by
  have h5265 : mixedVector B (Sum.inr 5265) = Sparse.eval nodeValue5265 (mixedVector B) := by
    change mixedMoment B node5265 node5265Labels = _
    exact sound5265 B hB hF
  have h5266 : mixedVector B (Sum.inr 5266) = Sparse.eval nodeValue5266 (mixedVector B) := by
    change mixedMoment B node5266 node5266Labels = _
    exact sound5266 B hB hF
  have h5270 : mixedVector B (Sum.inr 5270) = Sparse.eval nodeValue5270 (mixedVector B) := by
    change mixedMoment B node5270 node5270Labels = _
    exact sound5270 B hB hF
  have h5281 : mixedVector B (Sum.inr 5281) = Sparse.eval nodeValue5281 (mixedVector B) := by
    change mixedMoment B node5281 node5281Labels = _
    exact sound5281 B hB hF
  have h5282 : mixedVector B (Sum.inr 5282) = Sparse.eval nodeValue5282 (mixedVector B) := by
    change mixedMoment B node5282 node5282Labels = _
    exact sound5282 B hB hF
  have h5290 : mixedVector B (Sum.inr 5290) = Sparse.eval nodeValue5290 (mixedVector B) := by
    change mixedMoment B node5290 node5290Labels = _
    exact sound5290 B hB hF
  have h5301 : mixedVector B (Sum.inr 5301) = Sparse.eval nodeValue5301 (mixedVector B) := by
    change mixedMoment B node5301 node5301Labels = _
    exact sound5301 B hB hF
  have h5429 : mixedVector B (Sum.inr 5429) = Sparse.eval nodeValue5429 (mixedVector B) := by
    change mixedMoment B node5429 node5429Labels = _
    exact sound5429 B hB hF
  have h5431 : mixedVector B (Sum.inr 5431) = Sparse.eval nodeValue5431 (mixedVector B) := by
    change mixedMoment B node5431 node5431Labels = _
    exact sound5431 B hB hF
  have h5433 : mixedVector B (Sum.inr 5433) = Sparse.eval nodeValue5433 (mixedVector B) := by
    change mixedMoment B node5433 node5433Labels = _
    exact sound5433_e B hB hF
  have h5439 : mixedVector B (Sum.inr 5439) = Sparse.eval nodeValue5439 (mixedVector B) := by
    change mixedMoment B node5439 node5439Labels = _
    exact sound5439_e B hB hF
  have h5440 : mixedVector B (Sum.inr 5440) = Sparse.eval nodeValue5440 (mixedVector B) := by
    change mixedMoment B node5440 node5440Labels = _
    exact sound5440 B hB hF
  have h5445 : mixedVector B (Sum.inr 5445) = Sparse.eval nodeValue5445 (mixedVector B) := by
    change mixedMoment B node5445 node5445Labels = _
    exact sound5445 B hB hF
  have h5446 : mixedVector B (Sum.inr 5446) = Sparse.eval nodeValue5446 (mixedVector B) := by
    change mixedMoment B node5446 node5446Labels = _
    exact sound5446 B hB hF
  have h5447 : mixedVector B (Sum.inr 5447) = Sparse.eval nodeValue5447 (mixedVector B) := by
    change mixedMoment B node5447 node5447Labels = _
    exact sound5447 B hB hF
  have h5448 : mixedVector B (Sum.inr 5448) = Sparse.eval nodeValue5448 (mixedVector B) := by
    change mixedMoment B node5448 node5448Labels = _
    exact sound5448 B hB hF
  have h5450 : mixedVector B (Sum.inr 5450) = Sparse.eval nodeValue5450 (mixedVector B) := by
    change mixedMoment B node5450 node5450Labels = _
    exact sound5450_e B hB hF
  have h5472 : mixedVector B (Sum.inr 5472) = Sparse.eval nodeValue5472 (mixedVector B) := by
    change mixedMoment B node5472 node5472Labels = _
    exact sound5472 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  have h5474 : mixedVector B (Sum.inr 5474) = Sparse.eval nodeValue5474 (mixedVector B) := by
    change mixedMoment B node5474 node5474Labels = _
    exact sound5474 B hB hF
  have h5486 : mixedVector B (Sum.inr 5486) = Sparse.eval nodeValue5486 (mixedVector B) := by
    change mixedMoment B node5486 node5486Labels = _
    exact sound5486 B hB hF
  simpa only [sourceForm1104, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h5265, h5266, h5270, h5281, h5282, h5290, h5301, h5429, h5431, h5433, h5439, h5440, h5445, h5446, h5447, h5448, h5450, h5472, h5473, h5474, h5486, reducedSource957] using sourceEq1104 B hB

theorem rowSound957_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row957 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck957, numericCheck957, reducedZero957 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound957_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound957_e_oai
