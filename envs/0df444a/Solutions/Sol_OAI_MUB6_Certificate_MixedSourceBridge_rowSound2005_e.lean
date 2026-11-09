-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:44:08.934087+00:00
-- url     : https://prove2.me/submissions/3da70f7f-51e0-4b94-9f29-5c00d9840452

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E190
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

theorem canonical1554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1554 raw1554Labels = mixedMoment B node4676 node4676Labels := by
  calc
    mixedMoment B raw1554 raw1554Labels = mixedMoment B raw1554step0 raw1554step0Labels := by
      have ha : raw1554step0 = (fun i j => raw1554 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1554step0 raw1554; decide +kernel
      have hl : raw1554step0Labels = raw1554Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1554 raw1554Labels permutation152 permutation4
    mixedMoment B raw1554step0 raw1554step0Labels = mixedMoment B raw1554step1 raw1554step1Labels := by
      have ha : raw1554step1 = raw1554step0 := by apply Matrix.ext; unfold raw1554step1 raw1554step0; decide +kernel
      have hl : raw1554step0Labels = labelEmbedding7 ∘ raw1554step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1554step0 raw1554step0Labels raw1554step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4676 node4676Labels := by rfl

theorem canonical1555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1555 raw1555Labels = mixedMoment B node1802 node1802Labels := by
  calc
    mixedMoment B raw1555 raw1555Labels = mixedMoment B raw1555step0 raw1555step0Labels := by
      have ha : raw1555step0 = (fun i j => raw1555 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1555step0 raw1555; decide +kernel
      have hl : raw1555step0Labels = raw1555Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1555 raw1555Labels permutation152 permutation4
    _ = mixedMoment B node1802 node1802Labels := by rfl

theorem canonical1556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1556 raw1556Labels = mixedMoment B node2141 node2141Labels := by
  calc
    mixedMoment B raw1556 raw1556Labels = mixedMoment B raw1556step0 raw1556step0Labels := by
      have ha : raw1556step0 = (fun i j => raw1556 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1556step0 raw1556; decide +kernel
      have hl : raw1556step0Labels = raw1556Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1556 raw1556Labels permutation152 permutation6
    mixedMoment B raw1556step0 raw1556step0Labels = mixedMoment B raw1556step1 raw1556step1Labels := by
      have ha : raw1556step1 = -raw1556step0 := by apply Matrix.ext; change ∀ i j, raw1556step1 i j = -(raw1556step0 i j); unfold raw1556step1 raw1556step0; decide +kernel
      have hl : raw1556step1Labels = raw1556step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1556step1 raw1556step1Labels = mixedMoment B raw1556step2 raw1556step2Labels := by
      have ha : raw1556step2 = raw1556step1 := by apply Matrix.ext; unfold raw1556step2 raw1556step1; decide +kernel
      have hl : raw1556step1Labels = labelEmbedding1 ∘ raw1556step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1556step1 raw1556step1Labels raw1556step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2141 node2141Labels := by rfl

theorem canonical1563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1563 raw1563Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw1563 raw1563Labels = mixedMoment B raw1563step0 raw1563step0Labels := by
      have ha : raw1563step0 = (fun i j => raw1563 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1563step0 raw1563; decide +kernel
      have hl : raw1563step0Labels = raw1563Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1563 raw1563Labels permutation32 permutation4
    mixedMoment B raw1563step0 raw1563step0Labels = mixedMoment B raw1563step1 raw1563step1Labels := by
      have ha : raw1563step1 = raw1563step0 := by apply Matrix.ext; unfold raw1563step1 raw1563step0; decide +kernel
      have hl : raw1563step0Labels = labelEmbedding7 ∘ raw1563step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1563step0 raw1563step0Labels raw1563step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4681 node4681Labels := by rfl

theorem canonical1564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1564 raw1564Labels = mixedMoment B node1807 node1807Labels := by
  calc
    mixedMoment B raw1564 raw1564Labels = mixedMoment B raw1564step0 raw1564step0Labels := by
      have ha : raw1564step0 = (fun i j => raw1564 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1564step0 raw1564; decide +kernel
      have hl : raw1564step0Labels = raw1564Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1564 raw1564Labels permutation32 permutation4
    _ = mixedMoment B node1807 node1807Labels := by rfl

theorem canonical1565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1565 raw1565Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw1565 raw1565Labels = mixedMoment B raw1565step0 raw1565step0Labels := by
      have ha : raw1565step0 = (fun i j => raw1565 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1565step0 raw1565; decide +kernel
      have hl : raw1565step0Labels = raw1565Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1565 raw1565Labels permutation32 permutation6
    mixedMoment B raw1565step0 raw1565step0Labels = mixedMoment B raw1565step1 raw1565step1Labels := by
      have ha : raw1565step1 = -raw1565step0 := by apply Matrix.ext; change ∀ i j, raw1565step1 i j = -(raw1565step0 i j); unfold raw1565step1 raw1565step0; decide +kernel
      have hl : raw1565step1Labels = raw1565step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1565step1 raw1565step1Labels = mixedMoment B raw1565step2 raw1565step2Labels := by
      have ha : raw1565step2 = raw1565step1 := by apply Matrix.ext; unfold raw1565step2 raw1565step1; decide +kernel
      have hl : raw1565step1Labels = labelEmbedding1 ∘ raw1565step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1565step1 raw1565step1Labels raw1565step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2151 node2151Labels := by rfl

theorem canonical1566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1566 raw1566Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw1566 raw1566Labels = mixedMoment B raw1566step0 raw1566step0Labels := by
      have ha : raw1566step0 = (fun i j => raw1566 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1566step0 raw1566; decide +kernel
      have hl : raw1566step0Labels = raw1566Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1566 raw1566Labels permutation32 permutation4
    mixedMoment B raw1566step0 raw1566step0Labels = mixedMoment B raw1566step1 raw1566step1Labels := by
      have ha : raw1566step1 = raw1566step0 := by apply Matrix.ext; unfold raw1566step1 raw1566step0; decide +kernel
      have hl : raw1566step0Labels = labelEmbedding7 ∘ raw1566step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1566step0 raw1566step0Labels raw1566step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4684 node4684Labels := by rfl

theorem canonical1567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1567 raw1567Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw1567 raw1567Labels = mixedMoment B raw1567step0 raw1567step0Labels := by
      have ha : raw1567step0 = (fun i j => raw1567 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1567step0 raw1567; decide +kernel
      have hl : raw1567step0Labels = raw1567Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1567 raw1567Labels permutation32 permutation4
    _ = mixedMoment B node1810 node1810Labels := by rfl

theorem canonical1568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1568 raw1568Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw1568 raw1568Labels = mixedMoment B raw1568step0 raw1568step0Labels := by
      have ha : raw1568step0 = (fun i j => raw1568 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1568step0 raw1568; decide +kernel
      have hl : raw1568step0Labels = raw1568Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1568 raw1568Labels permutation32 permutation6
    mixedMoment B raw1568step0 raw1568step0Labels = mixedMoment B raw1568step1 raw1568step1Labels := by
      have ha : raw1568step1 = -raw1568step0 := by apply Matrix.ext; change ∀ i j, raw1568step1 i j = -(raw1568step0 i j); unfold raw1568step1 raw1568step0; decide +kernel
      have hl : raw1568step1Labels = raw1568step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1568step1 raw1568step1Labels = mixedMoment B raw1568step2 raw1568step2Labels := by
      have ha : raw1568step2 = raw1568step1 := by apply Matrix.ext; unfold raw1568step2 raw1568step1; decide +kernel
      have hl : raw1568step1Labels = labelEmbedding1 ∘ raw1568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1568step1 raw1568step1Labels raw1568step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2152 node2152Labels := by rfl

theorem canonical1575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1575 raw1575Labels = mixedMoment B node4688 node4688Labels := by
  calc
    mixedMoment B raw1575 raw1575Labels = mixedMoment B raw1575step0 raw1575step0Labels := by
      have ha : raw1575step0 = (fun i j => raw1575 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1575step0 raw1575; decide +kernel
      have hl : raw1575step0Labels = raw1575Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1575 raw1575Labels permutation32 permutation4
    mixedMoment B raw1575step0 raw1575step0Labels = mixedMoment B raw1575step1 raw1575step1Labels := by
      have ha : raw1575step1 = raw1575step0 := by apply Matrix.ext; unfold raw1575step1 raw1575step0; decide +kernel
      have hl : raw1575step0Labels = labelEmbedding7 ∘ raw1575step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1575step0 raw1575step0Labels raw1575step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4688 node4688Labels := by rfl

theorem canonical1576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1576 raw1576Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw1576 raw1576Labels = mixedMoment B raw1576step0 raw1576step0Labels := by
      have ha : raw1576step0 = (fun i j => raw1576 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1576step0 raw1576; decide +kernel
      have hl : raw1576step0Labels = raw1576Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1576 raw1576Labels permutation32 permutation4
    _ = mixedMoment B node1814 node1814Labels := by rfl

theorem canonical1577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1577 raw1577Labels = mixedMoment B node2157 node2157Labels := by
  calc
    mixedMoment B raw1577 raw1577Labels = mixedMoment B raw1577step0 raw1577step0Labels := by
      have ha : raw1577step0 = (fun i j => raw1577 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1577step0 raw1577; decide +kernel
      have hl : raw1577step0Labels = raw1577Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1577 raw1577Labels permutation34 permutation6
    mixedMoment B raw1577step0 raw1577step0Labels = mixedMoment B raw1577step1 raw1577step1Labels := by
      have ha : raw1577step1 = -raw1577step0 := by apply Matrix.ext; change ∀ i j, raw1577step1 i j = -(raw1577step0 i j); unfold raw1577step1 raw1577step0; decide +kernel
      have hl : raw1577step1Labels = raw1577step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1577step1 raw1577step1Labels = mixedMoment B raw1577step2 raw1577step2Labels := by
      have ha : raw1577step2 = raw1577step1 := by apply Matrix.ext; unfold raw1577step2 raw1577step1; decide +kernel
      have hl : raw1577step1Labels = labelEmbedding1 ∘ raw1577step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1577step1 raw1577step1Labels raw1577step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2157 node2157Labels := by rfl

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

theorem canonical1689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1689 raw1689Labels = mixedMoment B node4760 node4760Labels := by
  calc
    mixedMoment B raw1689 raw1689Labels = mixedMoment B raw1689step0 raw1689step0Labels := by
      have ha : raw1689step0 = (fun i j => raw1689 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1689step0 raw1689; decide +kernel
      have hl : raw1689step0Labels = raw1689Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1689 raw1689Labels permutation152 permutation4
    mixedMoment B raw1689step0 raw1689step0Labels = mixedMoment B raw1689step1 raw1689step1Labels := by
      have ha : raw1689step1 = raw1689step0 := by apply Matrix.ext; unfold raw1689step1 raw1689step0; decide +kernel
      have hl : raw1689step0Labels = labelEmbedding7 ∘ raw1689step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1689step0 raw1689step0Labels raw1689step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4760 node4760Labels := by rfl

theorem canonical1690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1690 raw1690Labels = mixedMoment B node1960 node1960Labels := by
  calc
    mixedMoment B raw1690 raw1690Labels = mixedMoment B raw1690step0 raw1690step0Labels := by
      have ha : raw1690step0 = (fun i j => raw1690 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1690step0 raw1690; decide +kernel
      have hl : raw1690step0Labels = raw1690Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1690 raw1690Labels permutation152 permutation4
    _ = mixedMoment B node1960 node1960Labels := by rfl

theorem canonical1691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1691 raw1691Labels = mixedMoment B node2173 node2173Labels := by
  calc
    mixedMoment B raw1691 raw1691Labels = mixedMoment B raw1691step0 raw1691step0Labels := by
      have ha : raw1691step0 = (fun i j => raw1691 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1691step0 raw1691; decide +kernel
      have hl : raw1691step0Labels = raw1691Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1691 raw1691Labels permutation152 permutation6
    mixedMoment B raw1691step0 raw1691step0Labels = mixedMoment B raw1691step1 raw1691step1Labels := by
      have ha : raw1691step1 = -raw1691step0 := by apply Matrix.ext; change ∀ i j, raw1691step1 i j = -(raw1691step0 i j); unfold raw1691step1 raw1691step0; decide +kernel
      have hl : raw1691step1Labels = raw1691step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1691step1 raw1691step1Labels = mixedMoment B raw1691step2 raw1691step2Labels := by
      have ha : raw1691step2 = raw1691step1 := by apply Matrix.ext; unfold raw1691step2 raw1691step1; decide +kernel
      have hl : raw1691step1Labels = labelEmbedding1 ∘ raw1691step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1691step1 raw1691step1Labels raw1691step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2173 node2173Labels := by rfl

theorem canonical1692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1692 raw1692Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw1692 raw1692Labels = mixedMoment B raw1692step0 raw1692step0Labels := by
      have ha : raw1692step0 = (fun i j => raw1692 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1692step0 raw1692; decide +kernel
      have hl : raw1692step0Labels = raw1692Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1692 raw1692Labels permutation152 permutation4
    mixedMoment B raw1692step0 raw1692step0Labels = mixedMoment B raw1692step1 raw1692step1Labels := by
      have ha : raw1692step1 = raw1692step0 := by apply Matrix.ext; unfold raw1692step1 raw1692step0; decide +kernel
      have hl : raw1692step0Labels = labelEmbedding7 ∘ raw1692step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1692step0 raw1692step0Labels raw1692step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4763 node4763Labels := by rfl

theorem canonical1693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1693 raw1693Labels = mixedMoment B node1963 node1963Labels := by
  calc
    mixedMoment B raw1693 raw1693Labels = mixedMoment B raw1693step0 raw1693step0Labels := by
      have ha : raw1693step0 = (fun i j => raw1693 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1693step0 raw1693; decide +kernel
      have hl : raw1693step0Labels = raw1693Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1693 raw1693Labels permutation152 permutation4
    _ = mixedMoment B node1963 node1963Labels := by rfl

theorem canonical1694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1694 raw1694Labels = mixedMoment B node2174 node2174Labels := by
  calc
    mixedMoment B raw1694 raw1694Labels = mixedMoment B raw1694step0 raw1694step0Labels := by
      have ha : raw1694step0 = (fun i j => raw1694 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1694step0 raw1694; decide +kernel
      have hl : raw1694step0Labels = raw1694Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1694 raw1694Labels permutation152 permutation6
    mixedMoment B raw1694step0 raw1694step0Labels = mixedMoment B raw1694step1 raw1694step1Labels := by
      have ha : raw1694step1 = -raw1694step0 := by apply Matrix.ext; change ∀ i j, raw1694step1 i j = -(raw1694step0 i j); unfold raw1694step1 raw1694step0; decide +kernel
      have hl : raw1694step1Labels = raw1694step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1694step1 raw1694step1Labels = mixedMoment B raw1694step2 raw1694step2Labels := by
      have ha : raw1694step2 = raw1694step1 := by apply Matrix.ext; unfold raw1694step2 raw1694step1; decide +kernel
      have hl : raw1694step1Labels = labelEmbedding1 ∘ raw1694step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1694step1 raw1694step1Labels raw1694step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2174 node2174Labels := by rfl

theorem canonical1698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1698 raw1698Labels = mixedMoment B node4766 node4766Labels := by
  calc
    mixedMoment B raw1698 raw1698Labels = mixedMoment B raw1698step0 raw1698step0Labels := by
      have ha : raw1698step0 = (fun i j => raw1698 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1698step0 raw1698; decide +kernel
      have hl : raw1698step0Labels = raw1698Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1698 raw1698Labels permutation152 permutation4
    mixedMoment B raw1698step0 raw1698step0Labels = mixedMoment B raw1698step1 raw1698step1Labels := by
      have ha : raw1698step1 = raw1698step0 := by apply Matrix.ext; unfold raw1698step1 raw1698step0; decide +kernel
      have hl : raw1698step0Labels = labelEmbedding7 ∘ raw1698step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1698step0 raw1698step0Labels raw1698step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4766 node4766Labels := by rfl

theorem canonical1699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1699 raw1699Labels = mixedMoment B node1966 node1966Labels := by
  calc
    mixedMoment B raw1699 raw1699Labels = mixedMoment B raw1699step0 raw1699step0Labels := by
      have ha : raw1699step0 = (fun i j => raw1699 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1699step0 raw1699; decide +kernel
      have hl : raw1699step0Labels = raw1699Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1699 raw1699Labels permutation152 permutation4
    _ = mixedMoment B node1966 node1966Labels := by rfl

theorem canonical1700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1700 raw1700Labels = mixedMoment B node2177 node2177Labels := by
  calc
    mixedMoment B raw1700 raw1700Labels = mixedMoment B raw1700step0 raw1700step0Labels := by
      have ha : raw1700step0 = (fun i j => raw1700 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1700step0 raw1700; decide +kernel
      have hl : raw1700step0Labels = raw1700Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1700 raw1700Labels permutation154 permutation6
    mixedMoment B raw1700step0 raw1700step0Labels = mixedMoment B raw1700step1 raw1700step1Labels := by
      have ha : raw1700step1 = -raw1700step0 := by apply Matrix.ext; change ∀ i j, raw1700step1 i j = -(raw1700step0 i j); unfold raw1700step1 raw1700step0; decide +kernel
      have hl : raw1700step1Labels = raw1700step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1700step1 raw1700step1Labels = mixedMoment B raw1700step2 raw1700step2Labels := by
      have ha : raw1700step2 = raw1700step1 := by apply Matrix.ext; unfold raw1700step2 raw1700step1; decide +kernel
      have hl : raw1700step1Labels = labelEmbedding1 ∘ raw1700step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1700step1 raw1700step1Labels raw1700step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2177 node2177Labels := by rfl

theorem canonical1731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1731 raw1731Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw1731 raw1731Labels = mixedMoment B raw1731step0 raw1731step0Labels := by
      have ha : raw1731step0 = (fun i j => raw1731 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1731step0 raw1731; decide +kernel
      have hl : raw1731step0Labels = raw1731Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1731 raw1731Labels permutation152 permutation4
    mixedMoment B raw1731step0 raw1731step0Labels = mixedMoment B raw1731step1 raw1731step1Labels := by
      have ha : raw1731step1 = raw1731step0 := by apply Matrix.ext; unfold raw1731step1 raw1731step0; decide +kernel
      have hl : raw1731step0Labels = labelEmbedding7 ∘ raw1731step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1731step0 raw1731step0Labels raw1731step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

theorem canonical1732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1732 raw1732Labels = mixedMoment B node2019 node2019Labels := by
  calc
    mixedMoment B raw1732 raw1732Labels = mixedMoment B raw1732step0 raw1732step0Labels := by
      have ha : raw1732step0 = (fun i j => raw1732 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1732step0 raw1732; decide +kernel
      have hl : raw1732step0Labels = raw1732Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1732 raw1732Labels permutation152 permutation4
    _ = mixedMoment B node2019 node2019Labels := by rfl

theorem canonical1733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1733 raw1733Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw1733 raw1733Labels = mixedMoment B raw1733step0 raw1733step0Labels := by
      have ha : raw1733step0 = (fun i j => raw1733 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1733step0 raw1733; decide +kernel
      have hl : raw1733step0Labels = raw1733Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1733 raw1733Labels permutation160 permutation6
    mixedMoment B raw1733step0 raw1733step0Labels = mixedMoment B raw1733step1 raw1733step1Labels := by
      have ha : raw1733step1 = -raw1733step0 := by apply Matrix.ext; change ∀ i j, raw1733step1 i j = -(raw1733step0 i j); unfold raw1733step1 raw1733step0; decide +kernel
      have hl : raw1733step1Labels = raw1733step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1733step1 raw1733step1Labels = mixedMoment B raw1733step2 raw1733step2Labels := by
      have ha : raw1733step2 = raw1733step1 := by apply Matrix.ext; unfold raw1733step2 raw1733step1; decide +kernel
      have hl : raw1733step1Labels = labelEmbedding1 ∘ raw1733step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1733step1 raw1733step1Labels raw1733step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2190 node2190Labels := by rfl

theorem canonical1737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1737 raw1737Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw1737 raw1737Labels = mixedMoment B raw1737step0 raw1737step0Labels := by
      have ha : raw1737step0 = (fun i j => raw1737 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1737step0 raw1737; decide +kernel
      have hl : raw1737step0Labels = raw1737Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1737 raw1737Labels permutation32 permutation4
    mixedMoment B raw1737step0 raw1737step0Labels = mixedMoment B raw1737step1 raw1737step1Labels := by
      have ha : raw1737step1 = raw1737step0 := by apply Matrix.ext; unfold raw1737step1 raw1737step0; decide +kernel
      have hl : raw1737step0Labels = labelEmbedding7 ∘ raw1737step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1737step0 raw1737step0Labels raw1737step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical1738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1738 raw1738Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw1738 raw1738Labels = mixedMoment B raw1738step0 raw1738step0Labels := by
      have ha : raw1738step0 = (fun i j => raw1738 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1738step0 raw1738; decide +kernel
      have hl : raw1738step0Labels = raw1738Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1738 raw1738Labels permutation32 permutation4
    _ = mixedMoment B node2022 node2022Labels := by rfl

theorem canonical1739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1739 raw1739Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw1739 raw1739Labels = mixedMoment B raw1739step0 raw1739step0Labels := by
      have ha : raw1739step0 = (fun i j => raw1739 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1739step0 raw1739; decide +kernel
      have hl : raw1739step0Labels = raw1739Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1739 raw1739Labels permutation34 permutation6
    mixedMoment B raw1739step0 raw1739step0Labels = mixedMoment B raw1739step1 raw1739step1Labels := by
      have ha : raw1739step1 = -raw1739step0 := by apply Matrix.ext; change ∀ i j, raw1739step1 i j = -(raw1739step0 i j); unfold raw1739step1 raw1739step0; decide +kernel
      have hl : raw1739step1Labels = raw1739step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1739step1 raw1739step1Labels = mixedMoment B raw1739step2 raw1739step2Labels := by
      have ha : raw1739step2 = raw1739step1 := by apply Matrix.ext; unfold raw1739step2 raw1739step1; decide +kernel
      have hl : raw1739step1Labels = labelEmbedding1 ∘ raw1739step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1739step1 raw1739step1Labels raw1739step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

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

theorem canonical1761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1761 raw1761Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw1761 raw1761Labels = mixedMoment B raw1761step0 raw1761step0Labels := by
      have ha : raw1761step0 = (fun i j => raw1761 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1761step0 raw1761; decide +kernel
      have hl : raw1761step0Labels = raw1761Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1761 raw1761Labels permutation152 permutation4
    mixedMoment B raw1761step0 raw1761step0Labels = mixedMoment B raw1761step1 raw1761step1Labels := by
      have ha : raw1761step1 = raw1761step0 := by apply Matrix.ext; unfold raw1761step1 raw1761step0; decide +kernel
      have hl : raw1761step0Labels = labelEmbedding7 ∘ raw1761step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1761step0 raw1761step0Labels raw1761step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

theorem canonical1762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1762 raw1762Labels = mixedMoment B node2051 node2051Labels := by
  calc
    mixedMoment B raw1762 raw1762Labels = mixedMoment B raw1762step0 raw1762step0Labels := by
      have ha : raw1762step0 = (fun i j => raw1762 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1762step0 raw1762; decide +kernel
      have hl : raw1762step0Labels = raw1762Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1762 raw1762Labels permutation152 permutation4
    _ = mixedMoment B node2051 node2051Labels := by rfl

theorem canonical1763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1763 raw1763Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw1763 raw1763Labels = mixedMoment B raw1763step0 raw1763step0Labels := by
      have ha : raw1763step0 = (fun i j => raw1763 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1763step0 raw1763; decide +kernel
      have hl : raw1763step0Labels = raw1763Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1763 raw1763Labels permutation152 permutation6
    mixedMoment B raw1763step0 raw1763step0Labels = mixedMoment B raw1763step1 raw1763step1Labels := by
      have ha : raw1763step1 = -raw1763step0 := by apply Matrix.ext; change ∀ i j, raw1763step1 i j = -(raw1763step0 i j); unfold raw1763step1 raw1763step0; decide +kernel
      have hl : raw1763step1Labels = raw1763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1763step1 raw1763step1Labels = mixedMoment B raw1763step2 raw1763step2Labels := by
      have ha : raw1763step2 = raw1763step1 := by apply Matrix.ext; unfold raw1763step2 raw1763step1; decide +kernel
      have hl : raw1763step1Labels = labelEmbedding1 ∘ raw1763step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1763step1 raw1763step1Labels raw1763step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2191 node2191Labels := by rfl

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

theorem canonical1770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1770 raw1770Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw1770 raw1770Labels = mixedMoment B raw1770step0 raw1770step0Labels := by
      have ha : raw1770step0 = (fun i j => raw1770 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1770step0 raw1770; decide +kernel
      have hl : raw1770step0Labels = raw1770Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1770 raw1770Labels permutation32 permutation4
    mixedMoment B raw1770step0 raw1770step0Labels = mixedMoment B raw1770step1 raw1770step1Labels := by
      have ha : raw1770step1 = raw1770step0 := by apply Matrix.ext; unfold raw1770step1 raw1770step0; decide +kernel
      have hl : raw1770step0Labels = labelEmbedding7 ∘ raw1770step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1770step0 raw1770step0Labels raw1770step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

theorem canonical1771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1771 raw1771Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw1771 raw1771Labels = mixedMoment B raw1771step0 raw1771step0Labels := by
      have ha : raw1771step0 = (fun i j => raw1771 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1771step0 raw1771; decide +kernel
      have hl : raw1771step0Labels = raw1771Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1771 raw1771Labels permutation32 permutation4
    _ = mixedMoment B node2058 node2058Labels := by rfl

theorem canonical1772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1772 raw1772Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw1772 raw1772Labels = mixedMoment B raw1772step0 raw1772step0Labels := by
      have ha : raw1772step0 = (fun i j => raw1772 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1772step0 raw1772; decide +kernel
      have hl : raw1772step0Labels = raw1772Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1772 raw1772Labels permutation36 permutation6
    mixedMoment B raw1772step0 raw1772step0Labels = mixedMoment B raw1772step1 raw1772step1Labels := by
      have ha : raw1772step1 = -raw1772step0 := by apply Matrix.ext; change ∀ i j, raw1772step1 i j = -(raw1772step0 i j); unfold raw1772step1 raw1772step0; decide +kernel
      have hl : raw1772step1Labels = raw1772step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1772step1 raw1772step1Labels = mixedMoment B raw1772step2 raw1772step2Labels := by
      have ha : raw1772step2 = raw1772step1 := by apply Matrix.ext; unfold raw1772step2 raw1772step1; decide +kernel
      have hl : raw1772step1Labels = labelEmbedding1 ∘ raw1772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1772step1 raw1772step1Labels raw1772step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

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

theorem canonical2250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2250 raw2250Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw2250 raw2250Labels = mixedMoment B raw2250step0 raw2250step0Labels := by
      have ha : raw2250step0 = (fun i j => raw2250 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2250step0 raw2250; decide +kernel
      have hl : raw2250step0Labels = raw2250Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2250 raw2250Labels permutation32 permutation4
    mixedMoment B raw2250step0 raw2250step0Labels = mixedMoment B raw2250step1 raw2250step1Labels := by
      have ha : raw2250step1 = raw2250step0 := by apply Matrix.ext; unfold raw2250step1 raw2250step0; decide +kernel
      have hl : raw2250step0Labels = labelEmbedding7 ∘ raw2250step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2250step0 raw2250step0Labels raw2250step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

theorem canonical2251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2251 raw2251Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw2251 raw2251Labels = mixedMoment B raw2251step0 raw2251step0Labels := by
      have ha : raw2251step0 = (fun i j => raw2251 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2251step0 raw2251; decide +kernel
      have hl : raw2251step0Labels = raw2251Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2251 raw2251Labels permutation32 permutation4
    _ = mixedMoment B node2672 node2672Labels := by rfl

theorem canonical2252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2252 raw2252Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw2252 raw2252Labels = mixedMoment B raw2252step0 raw2252step0Labels := by
      have ha : raw2252step0 = (fun i j => raw2252 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2252step0 raw2252; decide +kernel
      have hl : raw2252step0Labels = raw2252Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2252 raw2252Labels permutation32 permutation6
    mixedMoment B raw2252step0 raw2252step0Labels = mixedMoment B raw2252step1 raw2252step1Labels := by
      have ha : raw2252step1 = -raw2252step0 := by apply Matrix.ext; change ∀ i j, raw2252step1 i j = -(raw2252step0 i j); unfold raw2252step1 raw2252step0; decide +kernel
      have hl : raw2252step1Labels = raw2252step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2252step1 raw2252step1Labels = mixedMoment B raw2252step2 raw2252step2Labels := by
      have ha : raw2252step2 = raw2252step1 := by apply Matrix.ext; unfold raw2252step2 raw2252step1; decide +kernel
      have hl : raw2252step1Labels = labelEmbedding1 ∘ raw2252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2252step1 raw2252step1Labels raw2252step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3391 node3391Labels := by rfl

theorem canonical2259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2259 raw2259Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw2259 raw2259Labels = mixedMoment B raw2259step0 raw2259step0Labels := by
      have ha : raw2259step0 = (fun i j => raw2259 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2259step0 raw2259; decide +kernel
      have hl : raw2259step0Labels = raw2259Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2259 raw2259Labels permutation152 permutation4
    mixedMoment B raw2259step0 raw2259step0Labels = mixedMoment B raw2259step1 raw2259step1Labels := by
      have ha : raw2259step1 = raw2259step0 := by apply Matrix.ext; unfold raw2259step1 raw2259step0; decide +kernel
      have hl : raw2259step0Labels = labelEmbedding7 ∘ raw2259step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2259step0 raw2259step0Labels raw2259step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

theorem canonical2260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2260 raw2260Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw2260 raw2260Labels = mixedMoment B raw2260step0 raw2260step0Labels := by
      have ha : raw2260step0 = (fun i j => raw2260 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2260step0 raw2260; decide +kernel
      have hl : raw2260step0Labels = raw2260Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2260 raw2260Labels permutation152 permutation4
    _ = mixedMoment B node2694 node2694Labels := by rfl

theorem canonical2261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2261 raw2261Labels = mixedMoment B node3493 node3493Labels := by
  calc
    mixedMoment B raw2261 raw2261Labels = mixedMoment B raw2261step0 raw2261step0Labels := by
      have ha : raw2261step0 = (fun i j => raw2261 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2261step0 raw2261; decide +kernel
      have hl : raw2261step0Labels = raw2261Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2261 raw2261Labels permutation152 permutation6
    mixedMoment B raw2261step0 raw2261step0Labels = mixedMoment B raw2261step1 raw2261step1Labels := by
      have ha : raw2261step1 = -raw2261step0 := by apply Matrix.ext; change ∀ i j, raw2261step1 i j = -(raw2261step0 i j); unfold raw2261step1 raw2261step0; decide +kernel
      have hl : raw2261step1Labels = raw2261step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2261step1 raw2261step1Labels = mixedMoment B raw2261step2 raw2261step2Labels := by
      have ha : raw2261step2 = raw2261step1 := by apply Matrix.ext; unfold raw2261step2 raw2261step1; decide +kernel
      have hl : raw2261step1Labels = labelEmbedding1 ∘ raw2261step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2261step1 raw2261step1Labels raw2261step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3493 node3493Labels := by rfl

theorem canonical2271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2271 raw2271Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw2271 raw2271Labels = mixedMoment B raw2271step0 raw2271step0Labels := by
      have ha : raw2271step0 = (fun i j => raw2271 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2271step0 raw2271; decide +kernel
      have hl : raw2271step0Labels = raw2271Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2271 raw2271Labels permutation32 permutation4
    mixedMoment B raw2271step0 raw2271step0Labels = mixedMoment B raw2271step1 raw2271step1Labels := by
      have ha : raw2271step1 = raw2271step0 := by apply Matrix.ext; unfold raw2271step1 raw2271step0; decide +kernel
      have hl : raw2271step0Labels = labelEmbedding7 ∘ raw2271step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2271step0 raw2271step0Labels raw2271step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical2272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2272 raw2272Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw2272 raw2272Labels = mixedMoment B raw2272step0 raw2272step0Labels := by
      have ha : raw2272step0 = (fun i j => raw2272 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2272step0 raw2272; decide +kernel
      have hl : raw2272step0Labels = raw2272Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2272 raw2272Labels permutation32 permutation4
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical2273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2273 raw2273Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw2273 raw2273Labels = mixedMoment B raw2273step0 raw2273step0Labels := by
      have ha : raw2273step0 = (fun i j => raw2273 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2273step0 raw2273; decide +kernel
      have hl : raw2273step0Labels = raw2273Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2273 raw2273Labels permutation34 permutation6
    mixedMoment B raw2273step0 raw2273step0Labels = mixedMoment B raw2273step1 raw2273step1Labels := by
      have ha : raw2273step1 = -raw2273step0 := by apply Matrix.ext; change ∀ i j, raw2273step1 i j = -(raw2273step0 i j); unfold raw2273step1 raw2273step0; decide +kernel
      have hl : raw2273step1Labels = raw2273step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2273step1 raw2273step1Labels = mixedMoment B raw2273step2 raw2273step2Labels := by
      have ha : raw2273step2 = raw2273step1 := by apply Matrix.ext; unfold raw2273step2 raw2273step1; decide +kernel
      have hl : raw2273step1Labels = labelEmbedding1 ∘ raw2273step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2273step1 raw2273step1Labels raw2273step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical2274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2274 raw2274Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw2274 raw2274Labels = mixedMoment B raw2274step0 raw2274step0Labels := by
      have ha : raw2274step0 = (fun i j => raw2274 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2274step0 raw2274; decide +kernel
      have hl : raw2274step0Labels = raw2274Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2274 raw2274Labels permutation32 permutation4
    mixedMoment B raw2274step0 raw2274step0Labels = mixedMoment B raw2274step1 raw2274step1Labels := by
      have ha : raw2274step1 = raw2274step0 := by apply Matrix.ext; unfold raw2274step1 raw2274step0; decide +kernel
      have hl : raw2274step0Labels = labelEmbedding7 ∘ raw2274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2274step0 raw2274step0Labels raw2274step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical2275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2275 raw2275Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw2275 raw2275Labels = mixedMoment B raw2275step0 raw2275step0Labels := by
      have ha : raw2275step0 = (fun i j => raw2275 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2275step0 raw2275; decide +kernel
      have hl : raw2275step0Labels = raw2275Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2275 raw2275Labels permutation32 permutation4
    _ = mixedMoment B node2723 node2723Labels := by rfl

theorem canonical2276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2276 raw2276Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw2276 raw2276Labels = mixedMoment B raw2276step0 raw2276step0Labels := by
      have ha : raw2276step0 = (fun i j => raw2276 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2276step0 raw2276; decide +kernel
      have hl : raw2276step0Labels = raw2276Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2276 raw2276Labels permutation32 permutation6
    mixedMoment B raw2276step0 raw2276step0Labels = mixedMoment B raw2276step1 raw2276step1Labels := by
      have ha : raw2276step1 = -raw2276step0 := by apply Matrix.ext; change ∀ i j, raw2276step1 i j = -(raw2276step0 i j); unfold raw2276step1 raw2276step0; decide +kernel
      have hl : raw2276step1Labels = raw2276step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2276step1 raw2276step1Labels = mixedMoment B raw2276step2 raw2276step2Labels := by
      have ha : raw2276step2 = raw2276step1 := by apply Matrix.ext; unfold raw2276step2 raw2276step1; decide +kernel
      have hl : raw2276step1Labels = labelEmbedding1 ∘ raw2276step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2276step1 raw2276step1Labels raw2276step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

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

theorem canonical25896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25896 raw25896Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw25896 raw25896Labels = mixedMoment B raw25896step0 raw25896step0Labels := by
      have ha : raw25896step0 = (fun i j => raw25896 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25896step0 raw25896; decide +kernel
      have hl : raw25896step0Labels = raw25896Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25896 raw25896Labels permutation154 permutation2
    _ = mixedMoment B node4341 node4341Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical267
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34292 raw34292Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw34292 raw34292Labels = mixedMoment B raw34292step0 raw34292step0Labels := by
      have hz : ∀ j, raw34292 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34292step0 = (fun i j => raw34292 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34292step0 raw34292; decide +kernel
      have hl : raw34292step0Labels = raw34292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34292 raw34292Labels permutation346 hz
    mixedMoment B raw34292step0 raw34292step0Labels = mixedMoment B raw34292step1 raw34292step1Labels := by
      have ha : raw34292step1 = (fun i j => raw34292step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34292step1 raw34292step0; decide +kernel
      have hl : raw34292step1Labels = raw34292step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34292step0 raw34292step0Labels permutation34 permutation7
    mixedMoment B raw34292step1 raw34292step1Labels = mixedMoment B raw34292step2 raw34292step2Labels := by
      have ha : raw34292step2 = -raw34292step1 := by apply Matrix.ext; change ∀ i j, raw34292step2 i j = -(raw34292step1 i j); unfold raw34292step2 raw34292step1; decide +kernel
      have hl : raw34292step2Labels = raw34292step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34292step2 raw34292step2Labels = mixedMoment B raw34292step3 raw34292step3Labels := by
      have ha : raw34292step3 = raw34292step2 := by apply Matrix.ext; unfold raw34292step3 raw34292step2; decide +kernel
      have hl : raw34292step2Labels = labelEmbedding10 ∘ raw34292step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34292step2 raw34292step2Labels raw34292step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

theorem canonical34293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34293 raw34293Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw34293 raw34293Labels = mixedMoment B raw34293step0 raw34293step0Labels := by
      have ha : raw34293step0 = (fun i j => raw34293 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34293step0 raw34293; decide +kernel
      have hl : raw34293step0Labels = raw34293Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34293 raw34293Labels permutation154 permutation7
    mixedMoment B raw34293step0 raw34293step0Labels = mixedMoment B raw34293step1 raw34293step1Labels := by
      have ha : raw34293step1 = -raw34293step0 := by apply Matrix.ext; change ∀ i j, raw34293step1 i j = -(raw34293step0 i j); unfold raw34293step1 raw34293step0; decide +kernel
      have hl : raw34293step1Labels = raw34293step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34293step1 raw34293step1Labels = mixedMoment B raw34293step2 raw34293step2Labels := by
      have ha : raw34293step2 = raw34293step1 := by apply Matrix.ext; unfold raw34293step2 raw34293step1; decide +kernel
      have hl : raw34293step1Labels = labelEmbedding10 ∘ raw34293step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34293step1 raw34293step1Labels raw34293step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

theorem canonical34294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34294 raw34294Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw34294 raw34294Labels = mixedMoment B raw34294step0 raw34294step0Labels := by
      have hz : ∀ j, raw34294 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34294step0 = (fun i j => raw34294 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34294step0 raw34294; decide +kernel
      have hl : raw34294step0Labels = raw34294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34294 raw34294Labels permutation346 hz
    mixedMoment B raw34294step0 raw34294step0Labels = mixedMoment B raw34294step1 raw34294step1Labels := by
      have ha : raw34294step1 = (fun i j => raw34294step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34294step1 raw34294step0; decide +kernel
      have hl : raw34294step1Labels = raw34294step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34294step0 raw34294step0Labels permutation34 permutation7
    mixedMoment B raw34294step1 raw34294step1Labels = mixedMoment B raw34294step2 raw34294step2Labels := by
      have ha : raw34294step2 = -raw34294step1 := by apply Matrix.ext; change ∀ i j, raw34294step2 i j = -(raw34294step1 i j); unfold raw34294step2 raw34294step1; decide +kernel
      have hl : raw34294step2Labels = raw34294step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34294step2 raw34294step2Labels = mixedMoment B raw34294step3 raw34294step3Labels := by
      have ha : raw34294step3 = raw34294step2 := by apply Matrix.ext; unfold raw34294step3 raw34294step2; decide +kernel
      have hl : raw34294step2Labels = labelEmbedding10 ∘ raw34294step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34294step2 raw34294step2Labels raw34294step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

theorem canonical34295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34295 raw34295Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw34295 raw34295Labels = mixedMoment B raw34295step0 raw34295step0Labels := by
      have hz : ∀ j, raw34295 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34295step0 = (fun i j => raw34295 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34295step0 raw34295; decide +kernel
      have hl : raw34295step0Labels = raw34295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34295 raw34295Labels permutation520 hz
    mixedMoment B raw34295step0 raw34295step0Labels = mixedMoment B raw34295step1 raw34295step1Labels := by
      have hz : ∀ j, raw34295step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34295step1 = (fun i j => raw34295step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34295step1 raw34295step0; decide +kernel
      have hl : raw34295step1Labels = raw34295step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34295step0 raw34295step0Labels permutation80 hz
    mixedMoment B raw34295step1 raw34295step1Labels = mixedMoment B raw34295step2 raw34295step2Labels := by
      have ha : raw34295step2 = (fun i j => raw34295step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34295step2 raw34295step1; decide +kernel
      have hl : raw34295step2Labels = raw34295step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34295step1 raw34295step1Labels permutation8 permutation7
    mixedMoment B raw34295step2 raw34295step2Labels = mixedMoment B raw34295step3 raw34295step3Labels := by
      have ha : raw34295step3 = -raw34295step2 := by apply Matrix.ext; change ∀ i j, raw34295step3 i j = -(raw34295step2 i j); unfold raw34295step3 raw34295step2; decide +kernel
      have hl : raw34295step3Labels = raw34295step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34295step3 raw34295step3Labels = mixedMoment B raw34295step4 raw34295step4Labels := by
      have ha : raw34295step4 = raw34295step3 := by apply Matrix.ext; unfold raw34295step4 raw34295step3; decide +kernel
      have hl : raw34295step3Labels = labelEmbedding10 ∘ raw34295step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34295step3 raw34295step3Labels raw34295step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

theorem canonical34296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34296 raw34296Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw34296 raw34296Labels = mixedMoment B raw34296step0 raw34296step0Labels := by
      have hz : ∀ j, raw34296 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34296step0 = (fun i j => raw34296 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34296step0 raw34296; decide +kernel
      have hl : raw34296step0Labels = raw34296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34296 raw34296Labels permutation346 hz
    mixedMoment B raw34296step0 raw34296step0Labels = mixedMoment B raw34296step1 raw34296step1Labels := by
      have ha : raw34296step1 = (fun i j => raw34296step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34296step1 raw34296step0; decide +kernel
      have hl : raw34296step1Labels = raw34296step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34296step0 raw34296step0Labels permutation34 permutation7
    mixedMoment B raw34296step1 raw34296step1Labels = mixedMoment B raw34296step2 raw34296step2Labels := by
      have ha : raw34296step2 = -raw34296step1 := by apply Matrix.ext; change ∀ i j, raw34296step2 i j = -(raw34296step1 i j); unfold raw34296step2 raw34296step1; decide +kernel
      have hl : raw34296step2Labels = raw34296step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34296step2 raw34296step2Labels = mixedMoment B raw34296step3 raw34296step3Labels := by
      have ha : raw34296step3 = raw34296step2 := by apply Matrix.ext; unfold raw34296step3 raw34296step2; decide +kernel
      have hl : raw34296step2Labels = labelEmbedding10 ∘ raw34296step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34296step2 raw34296step2Labels raw34296step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

theorem canonical34297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34297 raw34297Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw34297 raw34297Labels = mixedMoment B raw34297step0 raw34297step0Labels := by
      have hz : ∀ j, raw34297 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34297step0 = (fun i j => raw34297 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34297step0 raw34297; decide +kernel
      have hl : raw34297step0Labels = raw34297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34297 raw34297Labels permutation346 hz
    mixedMoment B raw34297step0 raw34297step0Labels = mixedMoment B raw34297step1 raw34297step1Labels := by
      have hz : ∀ j, raw34297step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw34297step1 = (fun i j => raw34297step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw34297step1 raw34297step0; decide +kernel
      have hl : raw34297step1Labels = raw34297step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34297step0 raw34297step0Labels permutation56 hz
    mixedMoment B raw34297step1 raw34297step1Labels = mixedMoment B raw34297step2 raw34297step2Labels := by
      have ha : raw34297step2 = (fun i j => raw34297step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34297step2 raw34297step1; decide +kernel
      have hl : raw34297step2Labels = raw34297step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34297step1 raw34297step1Labels permutation10 permutation2
    _ = mixedMoment B node4498 node4498Labels := by rfl

theorem canonical34298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34298 raw34298Labels = mixedMoment B node4676 node4676Labels := by
  calc
    mixedMoment B raw34298 raw34298Labels = mixedMoment B raw34298step0 raw34298step0Labels := by
      have ha : raw34298step0 = (fun i j => raw34298 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34298step0 raw34298; decide +kernel
      have hl : raw34298step0Labels = raw34298Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34298 raw34298Labels permutation154 permutation2
    _ = mixedMoment B node4676 node4676Labels := by rfl

theorem canonical34299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34299 raw34299Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw34299 raw34299Labels = mixedMoment B raw34299step0 raw34299step0Labels := by
      have ha : raw34299step0 = (fun i j => raw34299 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34299step0 raw34299; decide +kernel
      have hl : raw34299step0Labels = raw34299Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34299 raw34299Labels permutation158 permutation2
    _ = mixedMoment B node4801 node4801Labels := by rfl

theorem canonical34300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34300 raw34300Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw34300 raw34300Labels = mixedMoment B raw34300step0 raw34300step0Labels := by
      have hz : ∀ j, raw34300 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34300step0 = (fun i j => raw34300 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34300step0 raw34300; decide +kernel
      have hl : raw34300step0Labels = raw34300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34300 raw34300Labels permutation520 hz
    _ = mixedMoment B node4834 node4834Labels := by rfl

theorem canonical34301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34301 raw34301Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw34301 raw34301Labels = mixedMoment B raw34301step0 raw34301step0Labels := by
      have ha : raw34301step0 = (fun i j => raw34301 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34301step0 raw34301; decide +kernel
      have hl : raw34301step0Labels = raw34301Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34301 raw34301Labels permutation154 permutation2
    _ = mixedMoment B node4831 node4831Labels := by rfl

theorem canonical34302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34302 raw34302Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw34302 raw34302Labels = mixedMoment B raw34302step0 raw34302step0Labels := by
      have hz : ∀ j, raw34302 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34302step0 = (fun i j => raw34302 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34302step0 raw34302; decide +kernel
      have hl : raw34302step0Labels = raw34302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34302 raw34302Labels permutation346 hz
    mixedMoment B raw34302step0 raw34302step0Labels = mixedMoment B raw34302step1 raw34302step1Labels := by
      have ha : raw34302step1 = (fun i j => raw34302step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34302step1 raw34302step0; decide +kernel
      have hl : raw34302step1Labels = raw34302step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34302step0 raw34302step0Labels permutation34 permutation2
    _ = mixedMoment B node4684 node4684Labels := by rfl

theorem canonical34303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34303 raw34303Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw34303 raw34303Labels = mixedMoment B raw34303step0 raw34303step0Labels := by
      have ha : raw34303step0 = (fun i j => raw34303 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34303step0 raw34303; decide +kernel
      have hl : raw34303step0Labels = raw34303Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34303 raw34303Labels permutation154 permutation2
    _ = mixedMoment B node4763 node4763Labels := by rfl

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

theorem canonical34304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34304 raw34304Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw34304 raw34304Labels = mixedMoment B raw34304step0 raw34304step0Labels := by
      have hz : ∀ j, raw34304 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34304step0 = (fun i j => raw34304 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34304step0 raw34304; decide +kernel
      have hl : raw34304step0Labels = raw34304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34304 raw34304Labels permutation520 hz
    mixedMoment B raw34304step0 raw34304step0Labels = mixedMoment B raw34304step1 raw34304step1Labels := by
      have hz : ∀ j, raw34304step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34304step1 = (fun i j => raw34304step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34304step1 raw34304step0; decide +kernel
      have hl : raw34304step1Labels = raw34304step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34304step0 raw34304step0Labels permutation80 hz
    _ = mixedMoment B node4846 node4846Labels := by rfl

theorem canonical34305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34305 raw34305Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw34305 raw34305Labels = mixedMoment B raw34305step0 raw34305step0Labels := by
      have hz : ∀ j, raw34305 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34305step0 = (fun i j => raw34305 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34305step0 raw34305; decide +kernel
      have hl : raw34305step0Labels = raw34305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34305 raw34305Labels permutation346 hz
    mixedMoment B raw34305step0 raw34305step0Labels = mixedMoment B raw34305step1 raw34305step1Labels := by
      have ha : raw34305step1 = (fun i j => raw34305step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34305step1 raw34305step0; decide +kernel
      have hl : raw34305step1Labels = raw34305step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34305step0 raw34305step0Labels permutation35 permutation2
    _ = mixedMoment B node4835 node4835Labels := by rfl

theorem canonical34306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34306 raw34306Labels = mixedMoment B node4688 node4688Labels := by
  calc
    mixedMoment B raw34306 raw34306Labels = mixedMoment B raw34306step0 raw34306step0Labels := by
      have hz : ∀ j, raw34306 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34306step0 = (fun i j => raw34306 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34306step0 raw34306; decide +kernel
      have hl : raw34306step0Labels = raw34306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34306 raw34306Labels permutation346 hz
    _ = mixedMoment B node4688 node4688Labels := by rfl

theorem canonical34307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34307 raw34307Labels = mixedMoment B node4766 node4766Labels := by
  calc
    _ = mixedMoment B node4766 node4766Labels := by rfl

theorem canonical34308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34308 raw34308Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw34308 raw34308Labels = mixedMoment B raw34308step0 raw34308step0Labels := by
      have hz : ∀ j, raw34308 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34308step0 = (fun i j => raw34308 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34308step0 raw34308; decide +kernel
      have hl : raw34308step0Labels = raw34308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34308 raw34308Labels permutation346 hz
    _ = mixedMoment B node4810 node4810Labels := by rfl

theorem canonical34309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34309 raw34309Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw34309 raw34309Labels = mixedMoment B raw34309step0 raw34309step0Labels := by
      have hz : ∀ j, raw34309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34309step0 = (fun i j => raw34309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34309step0 raw34309; decide +kernel
      have hl : raw34309step0Labels = raw34309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34309 raw34309Labels permutation346 hz
    mixedMoment B raw34309step0 raw34309step0Labels = mixedMoment B raw34309step1 raw34309step1Labels := by
      have ha : raw34309step1 = (fun i j => raw34309step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34309step1 raw34309step0; decide +kernel
      have hl : raw34309step1Labels = raw34309step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34309step0 raw34309step0Labels permutation33 permutation2
    _ = mixedMoment B node4839 node4839Labels := by rfl

theorem canonical34310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34310 raw34310Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw34310 raw34310Labels = mixedMoment B raw34310step0 raw34310step0Labels := by
      have hz : ∀ j, raw34310 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34310step0 = (fun i j => raw34310 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34310step0 raw34310; decide +kernel
      have hl : raw34310step0Labels = raw34310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34310 raw34310Labels permutation346 hz
    mixedMoment B raw34310step0 raw34310step0Labels = mixedMoment B raw34310step1 raw34310step1Labels := by
      have ha : raw34310step1 = (fun i j => raw34310step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34310step1 raw34310step0; decide +kernel
      have hl : raw34310step1Labels = raw34310step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34310step0 raw34310step0Labels permutation34 permutation2
    _ = mixedMoment B node4681 node4681Labels := by rfl

theorem canonical34311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34311 raw34311Labels = mixedMoment B node4760 node4760Labels := by
  calc
    mixedMoment B raw34311 raw34311Labels = mixedMoment B raw34311step0 raw34311step0Labels := by
      have ha : raw34311step0 = (fun i j => raw34311 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34311step0 raw34311; decide +kernel
      have hl : raw34311step0Labels = raw34311Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34311 raw34311Labels permutation154 permutation2
    _ = mixedMoment B node4760 node4760Labels := by rfl

theorem canonical34312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34312 raw34312Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw34312 raw34312Labels = mixedMoment B raw34312step0 raw34312step0Labels := by
      have hz : ∀ j, raw34312 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34312step0 = (fun i j => raw34312 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34312step0 raw34312; decide +kernel
      have hl : raw34312step0Labels = raw34312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34312 raw34312Labels permutation346 hz
    _ = mixedMoment B node4804 node4804Labels := by rfl

theorem canonical34313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34313 raw34313Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw34313 raw34313Labels = mixedMoment B raw34313step0 raw34313step0Labels := by
      have hz : ∀ j, raw34313 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34313step0 = (fun i j => raw34313 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34313step0 raw34313; decide +kernel
      have hl : raw34313step0Labels = raw34313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34313 raw34313Labels permutation520 hz
    mixedMoment B raw34313step0 raw34313step0Labels = mixedMoment B raw34313step1 raw34313step1Labels := by
      have hz : ∀ j, raw34313step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34313step1 = (fun i j => raw34313step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34313step1 raw34313step0; decide +kernel
      have hl : raw34313step1Labels = raw34313step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34313step0 raw34313step0Labels permutation80 hz
    _ = mixedMoment B node4841 node4841Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4676 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4676 node4676Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1802 node1802Labels + mixedMoment B node2141 node2141Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1554 singletonSmall4676
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4676) = raw1554Labels := by decide +kernel
  rw [hl, canonical1554 B hB] at h
  have hc0 : mixedMoment B raw1554 (Fin.cases (0 : Fin 2) singletonSmall4676) =
      mixedMoment B node1802 node1802Labels := by
    have ha : raw1554 = raw1555 := by apply Matrix.ext; unfold raw1554 raw1555; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4676 = raw1555Labels := by decide +kernel
    rw [ha, hj, canonical1555 B hB]
  have hc1 : mixedMoment B raw1554 (Fin.cases (1 : Fin 2) singletonSmall4676) =
      mixedMoment B node2141 node2141Labels := by
    have ha : raw1554 = raw1556 := by apply Matrix.ext; unfold raw1554 raw1556; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4676 = raw1556Labels := by decide +kernel
    rw [ha, hj, canonical1556 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4681 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4681 node4681Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1807 node1807Labels + mixedMoment B node2151 node2151Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1563 singletonSmall4681
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4681) = raw1563Labels := by decide +kernel
  rw [hl, canonical1563 B hB] at h
  have hc0 : mixedMoment B raw1563 (Fin.cases (0 : Fin 2) singletonSmall4681) =
      mixedMoment B node1807 node1807Labels := by
    have ha : raw1563 = raw1564 := by apply Matrix.ext; unfold raw1563 raw1564; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4681 = raw1564Labels := by decide +kernel
    rw [ha, hj, canonical1564 B hB]
  have hc1 : mixedMoment B raw1563 (Fin.cases (1 : Fin 2) singletonSmall4681) =
      mixedMoment B node2151 node2151Labels := by
    have ha : raw1563 = raw1565 := by apply Matrix.ext; unfold raw1563 raw1565; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4681 = raw1565Labels := by decide +kernel
    rw [ha, hj, canonical1565 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4684 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4684 node4684Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1810 node1810Labels + mixedMoment B node2152 node2152Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1566 singletonSmall4684
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4684) = raw1566Labels := by decide +kernel
  rw [hl, canonical1566 B hB] at h
  have hc0 : mixedMoment B raw1566 (Fin.cases (0 : Fin 2) singletonSmall4684) =
      mixedMoment B node1810 node1810Labels := by
    have ha : raw1566 = raw1567 := by apply Matrix.ext; unfold raw1566 raw1567; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4684 = raw1567Labels := by decide +kernel
    rw [ha, hj, canonical1567 B hB]
  have hc1 : mixedMoment B raw1566 (Fin.cases (1 : Fin 2) singletonSmall4684) =
      mixedMoment B node2152 node2152Labels := by
    have ha : raw1566 = raw1568 := by apply Matrix.ext; unfold raw1566 raw1568; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4684 = raw1568Labels := by decide +kernel
    rw [ha, hj, canonical1568 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4688 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4688 node4688Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1814 node1814Labels + mixedMoment B node2157 node2157Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1575 singletonSmall4688
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4688) = raw1575Labels := by decide +kernel
  rw [hl, canonical1575 B hB] at h
  have hc0 : mixedMoment B raw1575 (Fin.cases (0 : Fin 2) singletonSmall4688) =
      mixedMoment B node1814 node1814Labels := by
    have ha : raw1575 = raw1576 := by apply Matrix.ext; unfold raw1575 raw1576; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4688 = raw1576Labels := by decide +kernel
    rw [ha, hj, canonical1576 B hB]
  have hc1 : mixedMoment B raw1575 (Fin.cases (1 : Fin 2) singletonSmall4688) =
      mixedMoment B node2157 node2157Labels := by
    have ha : raw1575 = raw1577 := by apply Matrix.ext; unfold raw1575 raw1577; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4688 = raw1577Labels := by decide +kernel
    rw [ha, hj, canonical1577 B hB]
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

theorem singleton4760 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4760 node4760Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1960 node1960Labels + mixedMoment B node2173 node2173Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1689 singletonSmall4760
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4760) = raw1689Labels := by decide +kernel
  rw [hl, canonical1689 B hB] at h
  have hc0 : mixedMoment B raw1689 (Fin.cases (0 : Fin 2) singletonSmall4760) =
      mixedMoment B node1960 node1960Labels := by
    have ha : raw1689 = raw1690 := by apply Matrix.ext; unfold raw1689 raw1690; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4760 = raw1690Labels := by decide +kernel
    rw [ha, hj, canonical1690 B hB]
  have hc1 : mixedMoment B raw1689 (Fin.cases (1 : Fin 2) singletonSmall4760) =
      mixedMoment B node2173 node2173Labels := by
    have ha : raw1689 = raw1691 := by apply Matrix.ext; unfold raw1689 raw1691; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4760 = raw1691Labels := by decide +kernel
    rw [ha, hj, canonical1691 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4763 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4763 node4763Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1963 node1963Labels + mixedMoment B node2174 node2174Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1692 singletonSmall4763
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4763) = raw1692Labels := by decide +kernel
  rw [hl, canonical1692 B hB] at h
  have hc0 : mixedMoment B raw1692 (Fin.cases (0 : Fin 2) singletonSmall4763) =
      mixedMoment B node1963 node1963Labels := by
    have ha : raw1692 = raw1693 := by apply Matrix.ext; unfold raw1692 raw1693; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4763 = raw1693Labels := by decide +kernel
    rw [ha, hj, canonical1693 B hB]
  have hc1 : mixedMoment B raw1692 (Fin.cases (1 : Fin 2) singletonSmall4763) =
      mixedMoment B node2174 node2174Labels := by
    have ha : raw1692 = raw1694 := by apply Matrix.ext; unfold raw1692 raw1694; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4763 = raw1694Labels := by decide +kernel
    rw [ha, hj, canonical1694 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4766 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4766 node4766Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1966 node1966Labels + mixedMoment B node2177 node2177Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1698 singletonSmall4766
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4766) = raw1698Labels := by decide +kernel
  rw [hl, canonical1698 B hB] at h
  have hc0 : mixedMoment B raw1698 (Fin.cases (0 : Fin 2) singletonSmall4766) =
      mixedMoment B node1966 node1966Labels := by
    have ha : raw1698 = raw1699 := by apply Matrix.ext; unfold raw1698 raw1699; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4766 = raw1699Labels := by decide +kernel
    rw [ha, hj, canonical1699 B hB]
  have hc1 : mixedMoment B raw1698 (Fin.cases (1 : Fin 2) singletonSmall4766) =
      mixedMoment B node2177 node2177Labels := by
    have ha : raw1698 = raw1700 := by apply Matrix.ext; unfold raw1698 raw1700; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4766 = raw1700Labels := by decide +kernel
    rw [ha, hj, canonical1700 B hB]
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

theorem singleton4801 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4801 node4801Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2019 node2019Labels + mixedMoment B node2190 node2190Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1731 singletonSmall4801
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4801) = raw1731Labels := by decide +kernel
  rw [hl, canonical1731 B hB] at h
  have hc0 : mixedMoment B raw1731 (Fin.cases (0 : Fin 2) singletonSmall4801) =
      mixedMoment B node2019 node2019Labels := by
    have ha : raw1731 = raw1732 := by apply Matrix.ext; unfold raw1731 raw1732; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4801 = raw1732Labels := by decide +kernel
    rw [ha, hj, canonical1732 B hB]
  have hc1 : mixedMoment B raw1731 (Fin.cases (1 : Fin 2) singletonSmall4801) =
      mixedMoment B node2190 node2190Labels := by
    have ha : raw1731 = raw1733 := by apply Matrix.ext; unfold raw1731 raw1733; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4801 = raw1733Labels := by decide +kernel
    rw [ha, hj, canonical1733 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4804 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4804 node4804Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2022 node2022Labels + mixedMoment B node2203 node2203Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1737 singletonSmall4804
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4804) = raw1737Labels := by decide +kernel
  rw [hl, canonical1737 B hB] at h
  have hc0 : mixedMoment B raw1737 (Fin.cases (0 : Fin 2) singletonSmall4804) =
      mixedMoment B node2022 node2022Labels := by
    have ha : raw1737 = raw1738 := by apply Matrix.ext; unfold raw1737 raw1738; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4804 = raw1738Labels := by decide +kernel
    rw [ha, hj, canonical1738 B hB]
  have hc1 : mixedMoment B raw1737 (Fin.cases (1 : Fin 2) singletonSmall4804) =
      mixedMoment B node2203 node2203Labels := by
    have ha : raw1737 = raw1739 := by apply Matrix.ext; unfold raw1737 raw1739; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4804 = raw1739Labels := by decide +kernel
    rw [ha, hj, canonical1739 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4831 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4831 node4831Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2051 node2051Labels + mixedMoment B node2191 node2191Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1761 singletonSmall4831
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4831) = raw1761Labels := by decide +kernel
  rw [hl, canonical1761 B hB] at h
  have hc0 : mixedMoment B raw1761 (Fin.cases (0 : Fin 2) singletonSmall4831) =
      mixedMoment B node2051 node2051Labels := by
    have ha : raw1761 = raw1762 := by apply Matrix.ext; unfold raw1761 raw1762; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4831 = raw1762Labels := by decide +kernel
    rw [ha, hj, canonical1762 B hB]
  have hc1 : mixedMoment B raw1761 (Fin.cases (1 : Fin 2) singletonSmall4831) =
      mixedMoment B node2191 node2191Labels := by
    have ha : raw1761 = raw1763 := by apply Matrix.ext; unfold raw1761 raw1763; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4831 = raw1763Labels := by decide +kernel
    rw [ha, hj, canonical1763 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem singleton4839 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4839 node4839Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2058 node2058Labels + mixedMoment B node2216 node2216Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1770 singletonSmall4839
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4839) = raw1770Labels := by decide +kernel
  rw [hl, canonical1770 B hB] at h
  have hc0 : mixedMoment B raw1770 (Fin.cases (0 : Fin 2) singletonSmall4839) =
      mixedMoment B node2058 node2058Labels := by
    have ha : raw1770 = raw1771 := by apply Matrix.ext; unfold raw1770 raw1771; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4839 = raw1771Labels := by decide +kernel
    rw [ha, hj, canonical1771 B hB]
  have hc1 : mixedMoment B raw1770 (Fin.cases (1 : Fin 2) singletonSmall4839) =
      mixedMoment B node2216 node2216Labels := by
    have ha : raw1770 = raw1772 := by apply Matrix.ext; unfold raw1770 raw1772; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4839 = raw1772Labels := by decide +kernel
    rw [ha, hj, canonical1772 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5228 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5228 node5228Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2672 node2672Labels + mixedMoment B node3391 node3391Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2250 singletonSmall5228
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5228) = raw2250Labels := by decide +kernel
  rw [hl, canonical2250 B hB] at h
  have hc0 : mixedMoment B raw2250 (Fin.cases (0 : Fin 2) singletonSmall5228) =
      mixedMoment B node2672 node2672Labels := by
    have ha : raw2250 = raw2251 := by apply Matrix.ext; unfold raw2250 raw2251; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5228 = raw2251Labels := by decide +kernel
    rw [ha, hj, canonical2251 B hB]
  have hc1 : mixedMoment B raw2250 (Fin.cases (1 : Fin 2) singletonSmall5228) =
      mixedMoment B node3391 node3391Labels := by
    have ha : raw2250 = raw2252 := by apply Matrix.ext; unfold raw2250 raw2252; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5228 = raw2252Labels := by decide +kernel
    rw [ha, hj, canonical2252 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5241 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5241 node5241Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2694 node2694Labels + mixedMoment B node3493 node3493Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2259 singletonSmall5241
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5241) = raw2259Labels := by decide +kernel
  rw [hl, canonical2259 B hB] at h
  have hc0 : mixedMoment B raw2259 (Fin.cases (0 : Fin 2) singletonSmall5241) =
      mixedMoment B node2694 node2694Labels := by
    have ha : raw2259 = raw2260 := by apply Matrix.ext; unfold raw2259 raw2260; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5241 = raw2260Labels := by decide +kernel
    rw [ha, hj, canonical2260 B hB]
  have hc1 : mixedMoment B raw2259 (Fin.cases (1 : Fin 2) singletonSmall5241) =
      mixedMoment B node3493 node3493Labels := by
    have ha : raw2259 = raw2261 := by apply Matrix.ext; unfold raw2259 raw2261; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5241 = raw2261Labels := by decide +kernel
    rw [ha, hj, canonical2261 B hB]
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

theorem singleton5258 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5258 node5258Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2722 node2722Labels + mixedMoment B node3533 node3533Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2271 singletonSmall5258
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5258) = raw2271Labels := by decide +kernel
  rw [hl, canonical2271 B hB] at h
  have hc0 : mixedMoment B raw2271 (Fin.cases (0 : Fin 2) singletonSmall5258) =
      mixedMoment B node2722 node2722Labels := by
    have ha : raw2271 = raw2272 := by apply Matrix.ext; unfold raw2271 raw2272; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5258 = raw2272Labels := by decide +kernel
    rw [ha, hj, canonical2272 B hB]
  have hc1 : mixedMoment B raw2271 (Fin.cases (1 : Fin 2) singletonSmall5258) =
      mixedMoment B node3533 node3533Labels := by
    have ha : raw2271 = raw2273 := by apply Matrix.ext; unfold raw2271 raw2273; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5258 = raw2273Labels := by decide +kernel
    rw [ha, hj, canonical2273 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5259 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5259 node5259Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2723 node2723Labels + mixedMoment B node3544 node3544Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2274 singletonSmall5259
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5259) = raw2274Labels := by decide +kernel
  rw [hl, canonical2274 B hB] at h
  have hc0 : mixedMoment B raw2274 (Fin.cases (0 : Fin 2) singletonSmall5259) =
      mixedMoment B node2723 node2723Labels := by
    have ha : raw2274 = raw2275 := by apply Matrix.ext; unfold raw2274 raw2275; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5259 = raw2275Labels := by decide +kernel
    rw [ha, hj, canonical2275 B hB]
  have hc1 : mixedMoment B raw2274 (Fin.cases (1 : Fin 2) singletonSmall5259) =
      mixedMoment B node3544 node3544Labels := by
    have ha : raw2274 = raw2276 := by apply Matrix.ext; unfold raw2274 raw2276; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5259 = raw2276Labels := by decide +kernel
    rw [ha, hj, canonical2276 B hB]
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

theorem sound1802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1802 node1802Labels = Sparse.eval nodeValue1802 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1802) = mixedMoment B node1802 node1802Labels := rfl
  simpa [nodeValue1802, Sparse.eval] using hc.symm

theorem sound1807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1807 node1807Labels = Sparse.eval nodeValue1807 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1807) = mixedMoment B node1807 node1807Labels := rfl
  simpa [nodeValue1807, Sparse.eval] using hc.symm

theorem sound1810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1810 node1810Labels = Sparse.eval nodeValue1810 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1810) = mixedMoment B node1810 node1810Labels := rfl
  simpa [nodeValue1810, Sparse.eval] using hc.symm

theorem sound1814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1814 node1814Labels = Sparse.eval nodeValue1814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1814) = mixedMoment B node1814 node1814Labels := rfl
  simpa [nodeValue1814, Sparse.eval] using hc.symm

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

theorem sound1960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1960 node1960Labels = Sparse.eval nodeValue1960 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1960) = mixedMoment B node1960 node1960Labels := rfl
  simpa [nodeValue1960, Sparse.eval] using hc.symm

theorem sound1963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1963 node1963Labels = Sparse.eval nodeValue1963 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1963) = mixedMoment B node1963 node1963Labels := rfl
  simpa [nodeValue1963, Sparse.eval] using hc.symm

theorem sound1966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1966 node1966Labels = Sparse.eval nodeValue1966 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1966) = mixedMoment B node1966 node1966Labels := rfl
  simpa [nodeValue1966, Sparse.eval] using hc.symm

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

theorem sound2019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2019 node2019Labels = Sparse.eval nodeValue2019 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2019) = mixedMoment B node2019 node2019Labels := rfl
  simpa [nodeValue2019, Sparse.eval] using hc.symm

theorem sound2022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2022 node2022Labels = Sparse.eval nodeValue2022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2022) = mixedMoment B node2022 node2022Labels := rfl
  simpa [nodeValue2022, Sparse.eval] using hc.symm

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

theorem sound2051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2051 node2051Labels = Sparse.eval nodeValue2051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2051) = mixedMoment B node2051 node2051Labels := rfl
  simpa [nodeValue2051, Sparse.eval] using hc.symm

theorem sound2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2054 node2054Labels = Sparse.eval nodeValue2054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2054) = mixedMoment B node2054 node2054Labels := rfl
  simpa [nodeValue2054, Sparse.eval] using hc.symm

theorem sound2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2058 node2058Labels = Sparse.eval nodeValue2058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2058) = mixedMoment B node2058 node2058Labels := rfl
  simpa [nodeValue2058, Sparse.eval] using hc.symm

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

theorem sound2141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2141 node2141Labels = Sparse.eval nodeValue2141 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2141) = mixedMoment B node2141 node2141Labels := rfl
  simpa [nodeValue2141, Sparse.eval] using hc.symm

theorem sound2151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2151 node2151Labels = Sparse.eval nodeValue2151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2151) = mixedMoment B node2151 node2151Labels := rfl
  simpa [nodeValue2151, Sparse.eval] using hc.symm

theorem sound2152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2152 node2152Labels = Sparse.eval nodeValue2152 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2152) = mixedMoment B node2152 node2152Labels := rfl
  simpa [nodeValue2152, Sparse.eval] using hc.symm

theorem sound2157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2157 node2157Labels = Sparse.eval nodeValue2157 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2157) = mixedMoment B node2157 node2157Labels := rfl
  simpa [nodeValue2157, Sparse.eval] using hc.symm

theorem sound2173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2173 node2173Labels = Sparse.eval nodeValue2173 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2173) = mixedMoment B node2173 node2173Labels := rfl
  simpa [nodeValue2173, Sparse.eval] using hc.symm

theorem sound2174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2174 node2174Labels = Sparse.eval nodeValue2174 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2174) = mixedMoment B node2174 node2174Labels := rfl
  simpa [nodeValue2174, Sparse.eval] using hc.symm

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

theorem sound2177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2177 node2177Labels = Sparse.eval nodeValue2177 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2177) = mixedMoment B node2177 node2177Labels := rfl
  simpa [nodeValue2177, Sparse.eval] using hc.symm

theorem sound2190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2190 node2190Labels = Sparse.eval nodeValue2190 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2190) = mixedMoment B node2190 node2190Labels := rfl
  simpa [nodeValue2190, Sparse.eval] using hc.symm

theorem sound2191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2191 node2191Labels = Sparse.eval nodeValue2191 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2191) = mixedMoment B node2191 node2191Labels := rfl
  simpa [nodeValue2191, Sparse.eval] using hc.symm

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

theorem sound2206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2206 node2206Labels = Sparse.eval nodeValue2206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2206) = mixedMoment B node2206 node2206Labels := rfl
  simpa [nodeValue2206, Sparse.eval] using hc.symm

theorem sound2215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2215 node2215Labels = Sparse.eval nodeValue2215 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2215) = mixedMoment B node2215 node2215Labels := rfl
  simpa [nodeValue2215, Sparse.eval] using hc.symm

theorem sound2216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2216 node2216Labels = Sparse.eval nodeValue2216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2216) = mixedMoment B node2216 node2216Labels := rfl
  simpa [nodeValue2216, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2672 node2672Labels = Sparse.eval nodeValue2672 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2672) = mixedMoment B node2672 node2672Labels := rfl
  simpa [nodeValue2672, Sparse.eval] using hc.symm

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

theorem sound2694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2694 node2694Labels = Sparse.eval nodeValue2694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2694) = mixedMoment B node2694 node2694Labels := rfl
  simpa [nodeValue2694, Sparse.eval] using hc.symm

theorem sound2722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2722 node2722Labels = Sparse.eval nodeValue2722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2722) = mixedMoment B node2722 node2722Labels := rfl
  simpa [nodeValue2722, Sparse.eval] using hc.symm

theorem sound2723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2723 node2723Labels = Sparse.eval nodeValue2723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2723) = mixedMoment B node2723 node2723Labels := rfl
  simpa [nodeValue2723, Sparse.eval] using hc.symm

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

theorem sound3391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3391 node3391Labels = Sparse.eval nodeValue3391 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3391) = mixedMoment B node3391 node3391Labels := rfl
  simpa [nodeValue3391, Sparse.eval] using hc.symm

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

theorem sound3493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3493 node3493Labels = Sparse.eval nodeValue3493 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3493) = mixedMoment B node3493 node3493Labels := rfl
  simpa [nodeValue3493, Sparse.eval] using hc.symm

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

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

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

theorem sound4498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4498 node4498Labels = Sparse.eval nodeValue4498 (mixedVector B) := by
  simpa only [nodeValue4498, Sparse.eval_nil] using zero4498 B _hB _hF

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

theorem sound4676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4676 node4676Labels = Sparse.eval nodeValue4676 (mixedVector B) := by
  have h := singleton4676 B _hB
  rw [sound1802 B _hB _hF, sound2141 B _hB _hF] at h
  norm_num [nodeValue4676, nodeValue1802, nodeValue2141, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4681 node4681Labels = Sparse.eval nodeValue4681 (mixedVector B) := by
  have h := singleton4681 B _hB
  rw [sound1807 B _hB _hF, sound2151 B _hB _hF] at h
  norm_num [nodeValue4681, nodeValue1807, nodeValue2151, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4684 node4684Labels = Sparse.eval nodeValue4684 (mixedVector B) := by
  have h := singleton4684 B _hB
  rw [sound1810 B _hB _hF, sound2152 B _hB _hF] at h
  norm_num [nodeValue4684, nodeValue1810, nodeValue2152, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4688 node4688Labels = Sparse.eval nodeValue4688 (mixedVector B) := by
  have h := singleton4688 B _hB
  rw [sound1814 B _hB _hF, sound2157 B _hB _hF] at h
  norm_num [nodeValue4688, nodeValue1814, nodeValue2157, Sparse.eval] at h ⊢
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

theorem sound4760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4760 node4760Labels = Sparse.eval nodeValue4760 (mixedVector B) := by
  have h := singleton4760 B _hB
  rw [sound1960 B _hB _hF, sound2173 B _hB _hF] at h
  norm_num [nodeValue4760, nodeValue1960, nodeValue2173, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4763 node4763Labels = Sparse.eval nodeValue4763 (mixedVector B) := by
  have h := singleton4763 B _hB
  rw [sound1963 B _hB _hF, sound2174 B _hB _hF] at h
  norm_num [nodeValue4763, nodeValue1963, nodeValue2174, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4766 node4766Labels = Sparse.eval nodeValue4766 (mixedVector B) := by
  have h := singleton4766 B _hB
  rw [sound1966 B _hB _hF, sound2177 B _hB _hF] at h
  norm_num [nodeValue4766, nodeValue1966, nodeValue2177, Sparse.eval] at h ⊢
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

theorem zero4841 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4841 node4841Labels = 0 := by
  exact mixedMoment_order_one B hB node4841 node4841Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4801 node4801Labels = Sparse.eval nodeValue4801 (mixedVector B) := by
  have h := singleton4801 B _hB
  rw [sound2019 B _hB _hF, sound2190 B _hB _hF] at h
  norm_num [nodeValue4801, nodeValue2019, nodeValue2190, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4804 node4804Labels = Sparse.eval nodeValue4804 (mixedVector B) := by
  have h := singleton4804 B _hB
  rw [sound2022 B _hB _hF, sound2203 B _hB _hF] at h
  norm_num [nodeValue4804, nodeValue2022, nodeValue2203, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4810 node4810Labels = Sparse.eval nodeValue4810 (mixedVector B) := by
  have h := singleton4810 B _hB
  rw [sound2028 B _hB _hF, sound2215 B _hB _hF] at h
  norm_num [nodeValue4810, nodeValue2028, nodeValue2215, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4831 node4831Labels = Sparse.eval nodeValue4831 (mixedVector B) := by
  have h := singleton4831 B _hB
  rw [sound2051 B _hB _hF, sound2191 B _hB _hF] at h
  norm_num [nodeValue4831, nodeValue2051, nodeValue2191, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4834 node4834Labels = Sparse.eval nodeValue4834 (mixedVector B) := by
  simpa only [nodeValue4834, Sparse.eval_nil] using zero4834 B _hB _hF

theorem sound4835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4835 node4835Labels = Sparse.eval nodeValue4835 (mixedVector B) := by
  have h := singleton4835 B _hB
  rw [sound2054 B _hB _hF, sound2206 B _hB _hF] at h
  norm_num [nodeValue4835, nodeValue2054, nodeValue2206, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4839 node4839Labels = Sparse.eval nodeValue4839 (mixedVector B) := by
  have h := singleton4839 B _hB
  rw [sound2058 B _hB _hF, sound2216 B _hB _hF] at h
  norm_num [nodeValue4839, nodeValue2058, nodeValue2216, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4841 node4841Labels = Sparse.eval nodeValue4841 (mixedVector B) := by
  simpa only [nodeValue4841, Sparse.eval_nil] using zero4841 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5228 node5228Labels = Sparse.eval nodeValue5228 (mixedVector B) := by
  have h := singleton5228 B _hB
  rw [sound2672 B _hB _hF, sound3391 B _hB _hF] at h
  norm_num [nodeValue5228, nodeValue2672, nodeValue3391, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5241 node5241Labels = Sparse.eval nodeValue5241 (mixedVector B) := by
  have h := singleton5241 B _hB
  rw [sound2694 B _hB _hF, sound3493 B _hB _hF] at h
  norm_num [nodeValue5241, nodeValue2694, nodeValue3493, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5274 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5274 node5274Labels = 0 := by
  exact mixedMoment_order_one B hB node5274 node5274Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5258 node5258Labels = Sparse.eval nodeValue5258 (mixedVector B) := by
  have h := singleton5258 B _hB
  rw [sound2722 B _hB _hF, sound3533 B _hB _hF] at h
  norm_num [nodeValue5258, nodeValue2722, nodeValue3533, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5259 node5259Labels = Sparse.eval nodeValue5259 (mixedVector B) := by
  have h := singleton5259 B _hB
  rw [sound2723 B _hB _hF, sound3544 B _hB _hF] at h
  norm_num [nodeValue5259, nodeValue2723, nodeValue3544, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5274 node5274Labels = Sparse.eval nodeValue5274 (mixedVector B) := by
  simpa only [nodeValue5274, Sparse.eval_nil] using zero5274 B _hB _hF

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

theorem sourceEq2488 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2488 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2488 + difference 0 1) (sourceB2488 + difference 1 0) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2488 + difference 0 1) (sourceB2488 + difference 1 0) sourceC2488) = raw34292 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34292; decide +kernel
    rw [ha]
    exact (canonical34292 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2488 + difference 0 2) (sourceB2488 + difference 2 0) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA2488 + difference 0 2) (sourceB2488 + difference 2 0) sourceC2488) = raw34293 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34293; decide +kernel
    rw [ha]
    exact (canonical34293 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2488 + difference 0 3) (sourceB2488 + difference 3 0) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2488 + difference 0 3) (sourceB2488 + difference 3 0) sourceC2488) = raw34294 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34294; decide +kernel
    rw [ha]
    exact (canonical34294 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2488 + difference 0 4) (sourceB2488 + difference 4 0) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2488 + difference 0 4) (sourceB2488 + difference 4 0) sourceC2488) = raw34295 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34295; decide +kernel
    rw [ha]
    exact (canonical34295 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2488 + difference 0 5) (sourceB2488 + difference 5 0) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2488 + difference 0 5) (sourceB2488 + difference 5 0) sourceC2488) = raw34296 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34296; decide +kernel
    rw [ha]
    exact (canonical34296 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2488 + difference 1 0) (sourceB2488 + difference 0 1) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA2488 + difference 1 0) (sourceB2488 + difference 0 1) sourceC2488) = raw34297 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34297; decide +kernel
    rw [ha]
    exact (canonical34297 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2488 + difference 1 2) (sourceB2488 + difference 2 1) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2488 + difference 1 2) (sourceB2488 + difference 2 1) sourceC2488) = raw25886 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw25886; decide +kernel
    rw [ha]
    exact (canonical25886 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2488 + difference 1 3) (sourceB2488 + difference 3 1) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA2488 + difference 1 3) (sourceB2488 + difference 3 1) sourceC2488) = raw25887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw25887; decide +kernel
    rw [ha]
    exact (canonical25887 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2488 + difference 1 4) (sourceB2488 + difference 4 1) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA2488 + difference 1 4) (sourceB2488 + difference 4 1) sourceC2488) = raw25888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw25888; decide +kernel
    rw [ha]
    exact (canonical25888 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2488 + difference 1 5) (sourceB2488 + difference 5 1) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA2488 + difference 1 5) (sourceB2488 + difference 5 1) sourceC2488) = raw25889 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw25889; decide +kernel
    rw [ha]
    exact (canonical25889 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2488 + difference 2 0) (sourceB2488 + difference 0 2) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4341) := by
    have ha : (tripleCharges (sourceA2488 + difference 2 0) (sourceB2488 + difference 0 2) sourceC2488) = raw25896 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw25896; decide +kernel
    rw [ha]
    exact (canonical25896 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2488 + difference 2 1) (sourceB2488 + difference 1 2) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4676) := by
    have ha : (tripleCharges (sourceA2488 + difference 2 1) (sourceB2488 + difference 1 2) sourceC2488) = raw34298 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34298; decide +kernel
    rw [ha]
    exact (canonical34298 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2488 + difference 2 3) (sourceB2488 + difference 3 2) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2488 + difference 2 3) (sourceB2488 + difference 3 2) sourceC2488) = raw34299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34299; decide +kernel
    rw [ha]
    exact (canonical34299 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2488 + difference 2 4) (sourceB2488 + difference 4 2) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2488 + difference 2 4) (sourceB2488 + difference 4 2) sourceC2488) = raw34300 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34300; decide +kernel
    rw [ha]
    exact (canonical34300 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2488 + difference 2 5) (sourceB2488 + difference 5 2) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA2488 + difference 2 5) (sourceB2488 + difference 5 2) sourceC2488) = raw34301 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34301; decide +kernel
    rw [ha]
    exact (canonical34301 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2488 + difference 3 0) (sourceB2488 + difference 0 3) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA2488 + difference 3 0) (sourceB2488 + difference 0 3) sourceC2488) = raw25901 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw25901; decide +kernel
    rw [ha]
    exact (canonical25901 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2488 + difference 3 1) (sourceB2488 + difference 1 3) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2488 + difference 3 1) (sourceB2488 + difference 1 3) sourceC2488) = raw34302 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34302; decide +kernel
    rw [ha]
    exact (canonical34302 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2488 + difference 3 2) (sourceB2488 + difference 2 3) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2488 + difference 3 2) (sourceB2488 + difference 2 3) sourceC2488) = raw34303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34303; decide +kernel
    rw [ha]
    exact (canonical34303 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2488 + difference 3 4) (sourceB2488 + difference 4 3) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2488 + difference 3 4) (sourceB2488 + difference 4 3) sourceC2488) = raw34304 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34304; decide +kernel
    rw [ha]
    exact (canonical34304 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2488 + difference 3 5) (sourceB2488 + difference 5 3) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2488 + difference 3 5) (sourceB2488 + difference 5 3) sourceC2488) = raw34305 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34305; decide +kernel
    rw [ha]
    exact (canonical34305 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2488 + difference 4 0) (sourceB2488 + difference 0 4) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA2488 + difference 4 0) (sourceB2488 + difference 0 4) sourceC2488) = raw25906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw25906; decide +kernel
    rw [ha]
    exact (canonical25906 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2488 + difference 4 1) (sourceB2488 + difference 1 4) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4688) := by
    have ha : (tripleCharges (sourceA2488 + difference 4 1) (sourceB2488 + difference 1 4) sourceC2488) = raw34306 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34306; decide +kernel
    rw [ha]
    exact (canonical34306 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2488 + difference 4 2) (sourceB2488 + difference 2 4) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4766) := by
    have ha : (tripleCharges (sourceA2488 + difference 4 2) (sourceB2488 + difference 2 4) sourceC2488) = raw34307 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34307; decide +kernel
    rw [ha]
    exact (canonical34307 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2488 + difference 4 3) (sourceB2488 + difference 3 4) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2488 + difference 4 3) (sourceB2488 + difference 3 4) sourceC2488) = raw34308 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34308; decide +kernel
    rw [ha]
    exact (canonical34308 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2488 + difference 4 5) (sourceB2488 + difference 5 4) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2488 + difference 4 5) (sourceB2488 + difference 5 4) sourceC2488) = raw34309 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34309; decide +kernel
    rw [ha]
    exact (canonical34309 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2488 + difference 5 0) (sourceB2488 + difference 0 5) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA2488 + difference 5 0) (sourceB2488 + difference 0 5) sourceC2488) = raw25911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw25911; decide +kernel
    rw [ha]
    exact (canonical25911 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2488 + difference 5 1) (sourceB2488 + difference 1 5) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4681) := by
    have ha : (tripleCharges (sourceA2488 + difference 5 1) (sourceB2488 + difference 1 5) sourceC2488) = raw34310 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34310; decide +kernel
    rw [ha]
    exact (canonical34310 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2488 + difference 5 2) (sourceB2488 + difference 2 5) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4760) := by
    have ha : (tripleCharges (sourceA2488 + difference 5 2) (sourceB2488 + difference 2 5) sourceC2488) = raw34311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34311; decide +kernel
    rw [ha]
    exact (canonical34311 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2488 + difference 5 3) (sourceB2488 + difference 3 5) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2488 + difference 5 3) (sourceB2488 + difference 3 5) sourceC2488) = raw34312 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34312; decide +kernel
    rw [ha]
    exact (canonical34312 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2488 + difference 5 4) (sourceB2488 + difference 4 5) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA2488 + difference 5 4) (sourceB2488 + difference 4 5) sourceC2488) = raw34313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34313; decide +kernel
    rw [ha]
    exact (canonical34313 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2488 sourceB2488 sourceC2488
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2488, Integer.Sparse.eval]
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

theorem reindexCheck2005 : Integer.Sparse.reindex keyMap MixedData.row2005 = numericRow2005 := by decide +kernel

theorem numericCheck2005 (x : Master → ℝ) : Integer.Sparse.eval numericRow2005 x =
    (4 : ℝ) * reducedSource2005 x := by
  norm_num [numericRow2005, reducedSource2005, Integer.Sparse.eval, Sparse.eval, nodeValue4084, nodeValue4341, nodeValue4346, nodeValue4349, nodeValue4354, nodeValue4498, nodeValue4676, nodeValue4681, nodeValue4684, nodeValue4688, nodeValue4760, nodeValue4763, nodeValue4766, nodeValue4801, nodeValue4804, nodeValue4810, nodeValue4831, nodeValue4834, nodeValue4835, nodeValue4839, nodeValue4841, nodeValue4846, nodeValue4894, nodeValue4895, nodeValue5228, nodeValue5241, nodeValue5258, nodeValue5259, nodeValue5274]
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

theorem reducedZero2005 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource2005 (mixedVector B) = 0 := by
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
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
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
  have h4676 : mixedVector B (Sum.inr 4676) = Sparse.eval nodeValue4676 (mixedVector B) := by
    change mixedMoment B node4676 node4676Labels = _
    exact sound4676 B hB hF
  have h4681 : mixedVector B (Sum.inr 4681) = Sparse.eval nodeValue4681 (mixedVector B) := by
    change mixedMoment B node4681 node4681Labels = _
    exact sound4681 B hB hF
  have h4684 : mixedVector B (Sum.inr 4684) = Sparse.eval nodeValue4684 (mixedVector B) := by
    change mixedMoment B node4684 node4684Labels = _
    exact sound4684 B hB hF
  have h4688 : mixedVector B (Sum.inr 4688) = Sparse.eval nodeValue4688 (mixedVector B) := by
    change mixedMoment B node4688 node4688Labels = _
    exact sound4688 B hB hF
  have h4760 : mixedVector B (Sum.inr 4760) = Sparse.eval nodeValue4760 (mixedVector B) := by
    change mixedMoment B node4760 node4760Labels = _
    exact sound4760 B hB hF
  have h4763 : mixedVector B (Sum.inr 4763) = Sparse.eval nodeValue4763 (mixedVector B) := by
    change mixedMoment B node4763 node4763Labels = _
    exact sound4763 B hB hF
  have h4766 : mixedVector B (Sum.inr 4766) = Sparse.eval nodeValue4766 (mixedVector B) := by
    change mixedMoment B node4766 node4766Labels = _
    exact sound4766 B hB hF
  have h4801 : mixedVector B (Sum.inr 4801) = Sparse.eval nodeValue4801 (mixedVector B) := by
    change mixedMoment B node4801 node4801Labels = _
    exact sound4801 B hB hF
  have h4804 : mixedVector B (Sum.inr 4804) = Sparse.eval nodeValue4804 (mixedVector B) := by
    change mixedMoment B node4804 node4804Labels = _
    exact sound4804 B hB hF
  have h4810 : mixedVector B (Sum.inr 4810) = Sparse.eval nodeValue4810 (mixedVector B) := by
    change mixedMoment B node4810 node4810Labels = _
    exact sound4810 B hB hF
  have h4831 : mixedVector B (Sum.inr 4831) = Sparse.eval nodeValue4831 (mixedVector B) := by
    change mixedMoment B node4831 node4831Labels = _
    exact sound4831 B hB hF
  have h4834 : mixedVector B (Sum.inr 4834) = Sparse.eval nodeValue4834 (mixedVector B) := by
    change mixedMoment B node4834 node4834Labels = _
    exact sound4834 B hB hF
  have h4835 : mixedVector B (Sum.inr 4835) = Sparse.eval nodeValue4835 (mixedVector B) := by
    change mixedMoment B node4835 node4835Labels = _
    exact sound4835 B hB hF
  have h4839 : mixedVector B (Sum.inr 4839) = Sparse.eval nodeValue4839 (mixedVector B) := by
    change mixedMoment B node4839 node4839Labels = _
    exact sound4839 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h4846 : mixedVector B (Sum.inr 4846) = Sparse.eval nodeValue4846 (mixedVector B) := by
    change mixedMoment B node4846 node4846Labels = _
    exact sound4846 B hB hF
  have h4894 : mixedVector B (Sum.inr 4894) = Sparse.eval nodeValue4894 (mixedVector B) := by
    change mixedMoment B node4894 node4894Labels = _
    exact sound4894 B hB hF
  have h4895 : mixedVector B (Sum.inr 4895) = Sparse.eval nodeValue4895 (mixedVector B) := by
    change mixedMoment B node4895 node4895Labels = _
    exact sound4895 B hB hF
  have h5228 : mixedVector B (Sum.inr 5228) = Sparse.eval nodeValue5228 (mixedVector B) := by
    change mixedMoment B node5228 node5228Labels = _
    exact sound5228 B hB hF
  have h5241 : mixedVector B (Sum.inr 5241) = Sparse.eval nodeValue5241 (mixedVector B) := by
    change mixedMoment B node5241 node5241Labels = _
    exact sound5241 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5274 : mixedVector B (Sum.inr 5274) = Sparse.eval nodeValue5274 (mixedVector B) := by
    change mixedMoment B node5274 node5274Labels = _
    exact sound5274 B hB hF
  simpa only [sourceForm2488, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4084, h4341, h4346, h4349, h4354, h4498, h4676, h4681, h4684, h4688, h4760, h4763, h4766, h4801, h4804, h4810, h4831, h4834, h4835, h4839, h4841, h4846, h4894, h4895, h5228, h5241, h5258, h5259, h5274, reducedSource2005] using sourceEq2488 B hB

theorem rowSound2005_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row2005 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck2005, numericCheck2005, reducedZero2005 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound2005_e_oai
