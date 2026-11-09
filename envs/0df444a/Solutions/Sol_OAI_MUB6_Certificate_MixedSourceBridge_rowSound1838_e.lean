-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:11:42.079783+00:00
-- url     : https://prove2.me/submissions/192aed75-a35a-4401-9c63-cfa808de4096

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E094
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E190
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

theorem canonical1317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1317 raw1317Labels = mixedMoment B node4515 node4515Labels := by
  calc
    mixedMoment B raw1317 raw1317Labels = mixedMoment B raw1317step0 raw1317step0Labels := by
      have ha : raw1317step0 = (fun i j => raw1317 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1317step0 raw1317; decide +kernel
      have hl : raw1317step0Labels = raw1317Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1317 raw1317Labels permutation32 permutation4
    mixedMoment B raw1317step0 raw1317step0Labels = mixedMoment B raw1317step1 raw1317step1Labels := by
      have ha : raw1317step1 = raw1317step0 := by apply Matrix.ext; unfold raw1317step1 raw1317step0; decide +kernel
      have hl : raw1317step0Labels = labelEmbedding7 ∘ raw1317step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1317step0 raw1317step0Labels raw1317step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4515 node4515Labels := by rfl

theorem canonical1318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1318 raw1318Labels = mixedMoment B node1099 node1099Labels := by
  calc
    mixedMoment B raw1318 raw1318Labels = mixedMoment B raw1318step0 raw1318step0Labels := by
      have ha : raw1318step0 = (fun i j => raw1318 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1318step0 raw1318; decide +kernel
      have hl : raw1318step0Labels = raw1318Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1318 raw1318Labels permutation32 permutation4
    _ = mixedMoment B node1099 node1099Labels := by rfl

theorem canonical1319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1319 raw1319Labels = mixedMoment B node3233 node3233Labels := by
  calc
    mixedMoment B raw1319 raw1319Labels = mixedMoment B raw1319step0 raw1319step0Labels := by
      have ha : raw1319step0 = (fun i j => raw1319 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1319step0 raw1319; decide +kernel
      have hl : raw1319step0Labels = raw1319Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1319 raw1319Labels permutation32 permutation6
    mixedMoment B raw1319step0 raw1319step0Labels = mixedMoment B raw1319step1 raw1319step1Labels := by
      have ha : raw1319step1 = -raw1319step0 := by apply Matrix.ext; change ∀ i j, raw1319step1 i j = -(raw1319step0 i j); unfold raw1319step1 raw1319step0; decide +kernel
      have hl : raw1319step1Labels = raw1319step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1319step1 raw1319step1Labels = mixedMoment B raw1319step2 raw1319step2Labels := by
      have ha : raw1319step2 = raw1319step1 := by apply Matrix.ext; unfold raw1319step2 raw1319step1; decide +kernel
      have hl : raw1319step1Labels = labelEmbedding1 ∘ raw1319step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1319step1 raw1319step1Labels raw1319step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3233 node3233Labels := by rfl

theorem canonical1332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1332 raw1332Labels = mixedMoment B node4520 node4520Labels := by
  calc
    mixedMoment B raw1332 raw1332Labels = mixedMoment B raw1332step0 raw1332step0Labels := by
      have ha : raw1332step0 = (fun i j => raw1332 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1332step0 raw1332; decide +kernel
      have hl : raw1332step0Labels = raw1332Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1332 raw1332Labels permutation8 permutation4
    mixedMoment B raw1332step0 raw1332step0Labels = mixedMoment B raw1332step1 raw1332step1Labels := by
      have ha : raw1332step1 = raw1332step0 := by apply Matrix.ext; unfold raw1332step1 raw1332step0; decide +kernel
      have hl : raw1332step0Labels = labelEmbedding7 ∘ raw1332step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1332step0 raw1332step0Labels raw1332step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4520 node4520Labels := by rfl

theorem canonical1333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1333 raw1333Labels = mixedMoment B node1104 node1104Labels := by
  calc
    mixedMoment B raw1333 raw1333Labels = mixedMoment B raw1333step0 raw1333step0Labels := by
      have ha : raw1333step0 = (fun i j => raw1333 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1333step0 raw1333; decide +kernel
      have hl : raw1333step0Labels = raw1333Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1333 raw1333Labels permutation8 permutation4
    _ = mixedMoment B node1104 node1104Labels := by rfl

theorem canonical1334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1334 raw1334Labels = mixedMoment B node3237 node3237Labels := by
  calc
    mixedMoment B raw1334 raw1334Labels = mixedMoment B raw1334step0 raw1334step0Labels := by
      have ha : raw1334step0 = (fun i j => raw1334 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1334step0 raw1334; decide +kernel
      have hl : raw1334step0Labels = raw1334Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1334 raw1334Labels permutation8 permutation6
    mixedMoment B raw1334step0 raw1334step0Labels = mixedMoment B raw1334step1 raw1334step1Labels := by
      have ha : raw1334step1 = -raw1334step0 := by apply Matrix.ext; change ∀ i j, raw1334step1 i j = -(raw1334step0 i j); unfold raw1334step1 raw1334step0; decide +kernel
      have hl : raw1334step1Labels = raw1334step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1334step1 raw1334step1Labels = mixedMoment B raw1334step2 raw1334step2Labels := by
      have ha : raw1334step2 = raw1334step1 := by apply Matrix.ext; unfold raw1334step2 raw1334step1; decide +kernel
      have hl : raw1334step1Labels = labelEmbedding1 ∘ raw1334step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1334step1 raw1334step1Labels raw1334step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3237 node3237Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1410 raw1410Labels = mixedMoment B node4575 node4575Labels := by
  calc
    mixedMoment B raw1410 raw1410Labels = mixedMoment B raw1410step0 raw1410step0Labels := by
      have ha : raw1410step0 = (fun i j => raw1410 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1410step0 raw1410; decide +kernel
      have hl : raw1410step0Labels = raw1410Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1410 raw1410Labels permutation8 permutation4
    mixedMoment B raw1410step0 raw1410step0Labels = mixedMoment B raw1410step1 raw1410step1Labels := by
      have ha : raw1410step1 = raw1410step0 := by apply Matrix.ext; unfold raw1410step1 raw1410step0; decide +kernel
      have hl : raw1410step0Labels = labelEmbedding7 ∘ raw1410step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1410step0 raw1410step0Labels raw1410step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4575 node4575Labels := by rfl

theorem canonical1411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1411 raw1411Labels = mixedMoment B node1193 node1193Labels := by
  calc
    mixedMoment B raw1411 raw1411Labels = mixedMoment B raw1411step0 raw1411step0Labels := by
      have ha : raw1411step0 = (fun i j => raw1411 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1411step0 raw1411; decide +kernel
      have hl : raw1411step0Labels = raw1411Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1411 raw1411Labels permutation8 permutation4
    _ = mixedMoment B node1193 node1193Labels := by rfl

theorem canonical1412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1412 raw1412Labels = mixedMoment B node3248 node3248Labels := by
  calc
    mixedMoment B raw1412 raw1412Labels = mixedMoment B raw1412step0 raw1412step0Labels := by
      have ha : raw1412step0 = (fun i j => raw1412 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1412step0 raw1412; decide +kernel
      have hl : raw1412step0Labels = raw1412Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1412 raw1412Labels permutation8 permutation6
    mixedMoment B raw1412step0 raw1412step0Labels = mixedMoment B raw1412step1 raw1412step1Labels := by
      have ha : raw1412step1 = -raw1412step0 := by apply Matrix.ext; change ∀ i j, raw1412step1 i j = -(raw1412step0 i j); unfold raw1412step1 raw1412step0; decide +kernel
      have hl : raw1412step1Labels = raw1412step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1412step1 raw1412step1Labels = mixedMoment B raw1412step2 raw1412step2Labels := by
      have ha : raw1412step2 = raw1412step1 := by apply Matrix.ext; unfold raw1412step2 raw1412step1; decide +kernel
      have hl : raw1412step1Labels = labelEmbedding1 ∘ raw1412step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1412step1 raw1412step1Labels raw1412step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3248 node3248Labels := by rfl

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

theorem canonical1863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1863 raw1863Labels = mixedMoment B node4913 node4913Labels := by
  calc
    mixedMoment B raw1863 raw1863Labels = mixedMoment B raw1863step0 raw1863step0Labels := by
      have ha : raw1863step0 = (fun i j => raw1863 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1863step0 raw1863; decide +kernel
      have hl : raw1863step0Labels = raw1863Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1863 raw1863Labels permutation32 permutation4
    mixedMoment B raw1863step0 raw1863step0Labels = mixedMoment B raw1863step1 raw1863step1Labels := by
      have ha : raw1863step1 = raw1863step0 := by apply Matrix.ext; unfold raw1863step1 raw1863step0; decide +kernel
      have hl : raw1863step0Labels = labelEmbedding7 ∘ raw1863step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1863step0 raw1863step0Labels raw1863step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4913 node4913Labels := by rfl

theorem canonical1864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1864 raw1864Labels = mixedMoment B node2306 node2306Labels := by
  calc
    mixedMoment B raw1864 raw1864Labels = mixedMoment B raw1864step0 raw1864step0Labels := by
      have ha : raw1864step0 = (fun i j => raw1864 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1864step0 raw1864; decide +kernel
      have hl : raw1864step0Labels = raw1864Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1864 raw1864Labels permutation32 permutation4
    _ = mixedMoment B node2306 node2306Labels := by rfl

theorem canonical1865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1865 raw1865Labels = mixedMoment B node3318 node3318Labels := by
  calc
    mixedMoment B raw1865 raw1865Labels = mixedMoment B raw1865step0 raw1865step0Labels := by
      have ha : raw1865step0 = (fun i j => raw1865 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1865step0 raw1865; decide +kernel
      have hl : raw1865step0Labels = raw1865Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1865 raw1865Labels permutation32 permutation6
    mixedMoment B raw1865step0 raw1865step0Labels = mixedMoment B raw1865step1 raw1865step1Labels := by
      have ha : raw1865step1 = -raw1865step0 := by apply Matrix.ext; change ∀ i j, raw1865step1 i j = -(raw1865step0 i j); unfold raw1865step1 raw1865step0; decide +kernel
      have hl : raw1865step1Labels = raw1865step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1865step1 raw1865step1Labels = mixedMoment B raw1865step2 raw1865step2Labels := by
      have ha : raw1865step2 = raw1865step1 := by apply Matrix.ext; unfold raw1865step2 raw1865step1; decide +kernel
      have hl : raw1865step1Labels = labelEmbedding1 ∘ raw1865step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1865step1 raw1865step1Labels raw1865step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3318 node3318Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1989 raw1989Labels = mixedMoment B node4985 node4985Labels := by
  calc
    mixedMoment B raw1989 raw1989Labels = mixedMoment B raw1989step0 raw1989step0Labels := by
      have ha : raw1989step0 = (fun i j => raw1989 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1989step0 raw1989; decide +kernel
      have hl : raw1989step0Labels = raw1989Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1989 raw1989Labels permutation152 permutation4
    mixedMoment B raw1989step0 raw1989step0Labels = mixedMoment B raw1989step1 raw1989step1Labels := by
      have ha : raw1989step1 = raw1989step0 := by apply Matrix.ext; unfold raw1989step1 raw1989step0; decide +kernel
      have hl : raw1989step0Labels = labelEmbedding7 ∘ raw1989step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1989step0 raw1989step0Labels raw1989step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4985 node4985Labels := by rfl

theorem canonical1990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1990 raw1990Labels = mixedMoment B node2370 node2370Labels := by
  calc
    mixedMoment B raw1990 raw1990Labels = mixedMoment B raw1990step0 raw1990step0Labels := by
      have ha : raw1990step0 = (fun i j => raw1990 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1990step0 raw1990; decide +kernel
      have hl : raw1990step0Labels = raw1990Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1990 raw1990Labels permutation152 permutation4
    _ = mixedMoment B node2370 node2370Labels := by rfl

theorem canonical1991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1991 raw1991Labels = mixedMoment B node3334 node3334Labels := by
  calc
    mixedMoment B raw1991 raw1991Labels = mixedMoment B raw1991step0 raw1991step0Labels := by
      have ha : raw1991step0 = (fun i j => raw1991 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1991step0 raw1991; decide +kernel
      have hl : raw1991step0Labels = raw1991Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1991 raw1991Labels permutation152 permutation6
    mixedMoment B raw1991step0 raw1991step0Labels = mixedMoment B raw1991step1 raw1991step1Labels := by
      have ha : raw1991step1 = -raw1991step0 := by apply Matrix.ext; change ∀ i j, raw1991step1 i j = -(raw1991step0 i j); unfold raw1991step1 raw1991step0; decide +kernel
      have hl : raw1991step1Labels = raw1991step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1991step1 raw1991step1Labels = mixedMoment B raw1991step2 raw1991step2Labels := by
      have ha : raw1991step2 = raw1991step1 := by apply Matrix.ext; unfold raw1991step2 raw1991step1; decide +kernel
      have hl : raw1991step1Labels = labelEmbedding1 ∘ raw1991step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1991step1 raw1991step1Labels raw1991step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3334 node3334Labels := by rfl

theorem canonical2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2025 raw2025Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw2025 raw2025Labels = mixedMoment B raw2025step0 raw2025step0Labels := by
      have ha : raw2025step0 = (fun i j => raw2025 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2025step0 raw2025; decide +kernel
      have hl : raw2025step0Labels = raw2025Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2025 raw2025Labels permutation32 permutation4
    mixedMoment B raw2025step0 raw2025step0Labels = mixedMoment B raw2025step1 raw2025step1Labels := by
      have ha : raw2025step1 = raw2025step0 := by apply Matrix.ext; unfold raw2025step1 raw2025step0; decide +kernel
      have hl : raw2025step0Labels = labelEmbedding7 ∘ raw2025step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2025step0 raw2025step0Labels raw2025step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

theorem canonical2026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2026 raw2026Labels = mixedMoment B node2400 node2400Labels := by
  calc
    mixedMoment B raw2026 raw2026Labels = mixedMoment B raw2026step0 raw2026step0Labels := by
      have ha : raw2026step0 = (fun i j => raw2026 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2026step0 raw2026; decide +kernel
      have hl : raw2026step0Labels = raw2026Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2026 raw2026Labels permutation32 permutation4
    _ = mixedMoment B node2400 node2400Labels := by rfl

theorem canonical2027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2027 raw2027Labels = mixedMoment B node3344 node3344Labels := by
  calc
    mixedMoment B raw2027 raw2027Labels = mixedMoment B raw2027step0 raw2027step0Labels := by
      have ha : raw2027step0 = (fun i j => raw2027 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2027step0 raw2027; decide +kernel
      have hl : raw2027step0Labels = raw2027Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2027 raw2027Labels permutation32 permutation6
    mixedMoment B raw2027step0 raw2027step0Labels = mixedMoment B raw2027step1 raw2027step1Labels := by
      have ha : raw2027step1 = -raw2027step0 := by apply Matrix.ext; change ∀ i j, raw2027step1 i j = -(raw2027step0 i j); unfold raw2027step1 raw2027step0; decide +kernel
      have hl : raw2027step1Labels = raw2027step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2027step1 raw2027step1Labels = mixedMoment B raw2027step2 raw2027step2Labels := by
      have ha : raw2027step2 = raw2027step1 := by apply Matrix.ext; unfold raw2027step2 raw2027step1; decide +kernel
      have hl : raw2027step1Labels = labelEmbedding1 ∘ raw2027step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2027step1 raw2027step1Labels raw2027step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3344 node3344Labels := by rfl

theorem canonical2031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2031 raw2031Labels = mixedMoment B node5021 node5021Labels := by
  calc
    mixedMoment B raw2031 raw2031Labels = mixedMoment B raw2031step0 raw2031step0Labels := by
      have ha : raw2031step0 = (fun i j => raw2031 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2031step0 raw2031; decide +kernel
      have hl : raw2031step0Labels = raw2031Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2031 raw2031Labels permutation8 permutation4
    mixedMoment B raw2031step0 raw2031step0Labels = mixedMoment B raw2031step1 raw2031step1Labels := by
      have ha : raw2031step1 = raw2031step0 := by apply Matrix.ext; unfold raw2031step1 raw2031step0; decide +kernel
      have hl : raw2031step0Labels = labelEmbedding7 ∘ raw2031step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2031step0 raw2031step0Labels raw2031step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5021 node5021Labels := by rfl

theorem canonical2032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2032 raw2032Labels = mixedMoment B node2407 node2407Labels := by
  calc
    mixedMoment B raw2032 raw2032Labels = mixedMoment B raw2032step0 raw2032step0Labels := by
      have ha : raw2032step0 = (fun i j => raw2032 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2032step0 raw2032; decide +kernel
      have hl : raw2032step0Labels = raw2032Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2032 raw2032Labels permutation8 permutation4
    _ = mixedMoment B node2407 node2407Labels := by rfl

theorem canonical2033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2033 raw2033Labels = mixedMoment B node3360 node3360Labels := by
  calc
    mixedMoment B raw2033 raw2033Labels = mixedMoment B raw2033step0 raw2033step0Labels := by
      have ha : raw2033step0 = (fun i j => raw2033 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2033step0 raw2033; decide +kernel
      have hl : raw2033step0Labels = raw2033Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2033 raw2033Labels permutation31 permutation6
    mixedMoment B raw2033step0 raw2033step0Labels = mixedMoment B raw2033step1 raw2033step1Labels := by
      have ha : raw2033step1 = raw2033step0 := by apply Matrix.ext; unfold raw2033step1 raw2033step0; decide +kernel
      have hl : raw2033step0Labels = labelEmbedding1 ∘ raw2033step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2033step0 raw2033step0Labels raw2033step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3360 node3360Labels := by rfl

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

theorem canonical2157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2157 raw2157Labels = mixedMoment B node5125 node5125Labels := by
  calc
    mixedMoment B raw2157 raw2157Labels = mixedMoment B raw2157step0 raw2157step0Labels := by
      have ha : raw2157step0 = (fun i j => raw2157 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2157step0 raw2157; decide +kernel
      have hl : raw2157step0Labels = raw2157Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2157 raw2157Labels permutation32 permutation4
    mixedMoment B raw2157step0 raw2157step0Labels = mixedMoment B raw2157step1 raw2157step1Labels := by
      have ha : raw2157step1 = raw2157step0 := by apply Matrix.ext; unfold raw2157step1 raw2157step0; decide +kernel
      have hl : raw2157step0Labels = labelEmbedding7 ∘ raw2157step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2157step0 raw2157step0Labels raw2157step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5125 node5125Labels := by rfl

theorem canonical2158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2158 raw2158Labels = mixedMoment B node2539 node2539Labels := by
  calc
    mixedMoment B raw2158 raw2158Labels = mixedMoment B raw2158step0 raw2158step0Labels := by
      have ha : raw2158step0 = (fun i j => raw2158 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2158step0 raw2158; decide +kernel
      have hl : raw2158step0Labels = raw2158Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2158 raw2158Labels permutation32 permutation4
    _ = mixedMoment B node2539 node2539Labels := by rfl

theorem canonical2159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2159 raw2159Labels = mixedMoment B node3372 node3372Labels := by
  calc
    mixedMoment B raw2159 raw2159Labels = mixedMoment B raw2159step0 raw2159step0Labels := by
      have ha : raw2159step0 = (fun i j => raw2159 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2159step0 raw2159; decide +kernel
      have hl : raw2159step0Labels = raw2159Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2159 raw2159Labels permutation38 permutation6
    mixedMoment B raw2159step0 raw2159step0Labels = mixedMoment B raw2159step1 raw2159step1Labels := by
      have ha : raw2159step1 = -raw2159step0 := by apply Matrix.ext; change ∀ i j, raw2159step1 i j = -(raw2159step0 i j); unfold raw2159step1 raw2159step0; decide +kernel
      have hl : raw2159step1Labels = raw2159step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2159step1 raw2159step1Labels = mixedMoment B raw2159step2 raw2159step2Labels := by
      have ha : raw2159step2 = raw2159step1 := by apply Matrix.ext; unfold raw2159step2 raw2159step1; decide +kernel
      have hl : raw2159step1Labels = labelEmbedding1 ∘ raw2159step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2159step1 raw2159step1Labels raw2159step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3372 node3372Labels := by rfl

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

theorem canonical2256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2256 raw2256Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw2256 raw2256Labels = mixedMoment B raw2256step0 raw2256step0Labels := by
      have ha : raw2256step0 = (fun i j => raw2256 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2256step0 raw2256; decide +kernel
      have hl : raw2256step0Labels = raw2256Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2256 raw2256Labels permutation8 permutation4
    mixedMoment B raw2256step0 raw2256step0Labels = mixedMoment B raw2256step1 raw2256step1Labels := by
      have ha : raw2256step1 = raw2256step0 := by apply Matrix.ext; unfold raw2256step1 raw2256step0; decide +kernel
      have hl : raw2256step0Labels = labelEmbedding7 ∘ raw2256step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2256step0 raw2256step0Labels raw2256step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

theorem canonical2257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2257 raw2257Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw2257 raw2257Labels = mixedMoment B raw2257step0 raw2257step0Labels := by
      have ha : raw2257step0 = (fun i j => raw2257 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2257step0 raw2257; decide +kernel
      have hl : raw2257step0Labels = raw2257Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2257 raw2257Labels permutation8 permutation4
    _ = mixedMoment B node2686 node2686Labels := by rfl

theorem canonical2258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2258 raw2258Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw2258 raw2258Labels = mixedMoment B raw2258step0 raw2258step0Labels := by
      have ha : raw2258step0 = (fun i j => raw2258 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2258step0 raw2258; decide +kernel
      have hl : raw2258step0Labels = raw2258Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2258 raw2258Labels permutation8 permutation6
    mixedMoment B raw2258step0 raw2258step0Labels = mixedMoment B raw2258step1 raw2258step1Labels := by
      have ha : raw2258step1 = -raw2258step0 := by apply Matrix.ext; change ∀ i j, raw2258step1 i j = -(raw2258step0 i j); unfold raw2258step1 raw2258step0; decide +kernel
      have hl : raw2258step1Labels = raw2258step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2258step1 raw2258step1Labels = mixedMoment B raw2258step2 raw2258step2Labels := by
      have ha : raw2258step2 = raw2258step1 := by apply Matrix.ext; unfold raw2258step2 raw2258step1; decide +kernel
      have hl : raw2258step1Labels = labelEmbedding1 ∘ raw2258step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2258step1 raw2258step1Labels raw2258step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3397 node3397Labels := by rfl

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

theorem canonical30888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30888 raw30888Labels = mixedMoment B node4089 node4089Labels := by
  calc
    mixedMoment B raw30888 raw30888Labels = mixedMoment B raw30888step0 raw30888step0Labels := by
      have hz : ∀ j, raw30888 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30888step0 = (fun i j => raw30888 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30888step0 raw30888; decide +kernel
      have hl : raw30888step0Labels = raw30888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30888 raw30888Labels permutation434 hz
    mixedMoment B raw30888step0 raw30888step0Labels = mixedMoment B raw30888step1 raw30888step1Labels := by
      have hz : ∀ j, raw30888step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30888step1 = (fun i j => raw30888step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30888step1 raw30888step0; decide +kernel
      have hl : raw30888step1Labels = raw30888step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30888step0 raw30888step0Labels permutation80 hz
    mixedMoment B raw30888step1 raw30888step1Labels = mixedMoment B raw30888step2 raw30888step2Labels := by
      have hz : ∀ i, raw30888step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw30888step2 = (fun i j => raw30888step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw30888step2 raw30888step1; decide +kernel
      have hl : raw30888step2Labels = (fun j => raw30888step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw30888step1 raw30888step1Labels permutation4 hz
    mixedMoment B raw30888step2 raw30888step2Labels = mixedMoment B raw30888step3 raw30888step3Labels := by
      have ha : raw30888step3 = raw30888step2 := by apply Matrix.ext; unfold raw30888step3 raw30888step2; decide +kernel
      have hl : raw30888step2Labels = labelEmbedding2 ∘ raw30888step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30888step2 raw30888step2Labels raw30888step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4089 node4089Labels := by rfl

theorem canonical30889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30889 raw30889Labels = mixedMoment B node5327 node5327Labels := by
  calc
    mixedMoment B raw30889 raw30889Labels = mixedMoment B raw30889step0 raw30889step0Labels := by
      have hz : ∀ j, raw30889 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30889step0 = (fun i j => raw30889 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30889step0 raw30889; decide +kernel
      have hl : raw30889step0Labels = raw30889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30889 raw30889Labels permutation434 hz
    mixedMoment B raw30889step0 raw30889step0Labels = mixedMoment B raw30889step1 raw30889step1Labels := by
      have ha : raw30889step1 = (fun i j => raw30889step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30889step1 raw30889step0; decide +kernel
      have hl : raw30889step1Labels = raw30889step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30889step0 raw30889step0Labels permutation127 permutation7
    mixedMoment B raw30889step1 raw30889step1Labels = mixedMoment B raw30889step2 raw30889step2Labels := by
      have ha : raw30889step2 = raw30889step1 := by apply Matrix.ext; unfold raw30889step2 raw30889step1; decide +kernel
      have hl : raw30889step1Labels = labelEmbedding10 ∘ raw30889step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30889step1 raw30889step1Labels raw30889step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5327 node5327Labels := by rfl

theorem canonical30890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30890 raw30890Labels = mixedMoment B node5327 node5327Labels := by
  calc
    mixedMoment B raw30890 raw30890Labels = mixedMoment B raw30890step0 raw30890step0Labels := by
      have hz : ∀ j, raw30890 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30890step0 = (fun i j => raw30890 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30890step0 raw30890; decide +kernel
      have hl : raw30890step0Labels = raw30890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30890 raw30890Labels permutation346 hz
    mixedMoment B raw30890step0 raw30890step0Labels = mixedMoment B raw30890step1 raw30890step1Labels := by
      have ha : raw30890step1 = (fun i j => raw30890step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30890step1 raw30890step0; decide +kernel
      have hl : raw30890step1Labels = raw30890step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30890step0 raw30890step0Labels permutation127 permutation7
    mixedMoment B raw30890step1 raw30890step1Labels = mixedMoment B raw30890step2 raw30890step2Labels := by
      have ha : raw30890step2 = raw30890step1 := by apply Matrix.ext; unfold raw30890step2 raw30890step1; decide +kernel
      have hl : raw30890step1Labels = labelEmbedding10 ∘ raw30890step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30890step1 raw30890step1Labels raw30890step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5327 node5327Labels := by rfl

theorem canonical30891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30891 raw30891Labels = mixedMoment B node5371 node5371Labels := by
  calc
    mixedMoment B raw30891 raw30891Labels = mixedMoment B raw30891step0 raw30891step0Labels := by
      have hz : ∀ j, raw30891 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30891step0 = (fun i j => raw30891 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30891step0 raw30891; decide +kernel
      have hl : raw30891step0Labels = raw30891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30891 raw30891Labels permutation434 hz
    mixedMoment B raw30891step0 raw30891step0Labels = mixedMoment B raw30891step1 raw30891step1Labels := by
      have hz : ∀ j, raw30891step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30891step1 = (fun i j => raw30891step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30891step1 raw30891step0; decide +kernel
      have hl : raw30891step1Labels = raw30891step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30891step0 raw30891step0Labels permutation80 hz
    mixedMoment B raw30891step1 raw30891step1Labels = mixedMoment B raw30891step2 raw30891step2Labels := by
      have ha : raw30891step2 = (fun i j => raw30891step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30891step2 raw30891step1; decide +kernel
      have hl : raw30891step2Labels = raw30891step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30891step1 raw30891step1Labels permutation31 permutation7
    mixedMoment B raw30891step2 raw30891step2Labels = mixedMoment B raw30891step3 raw30891step3Labels := by
      have ha : raw30891step3 = raw30891step2 := by apply Matrix.ext; unfold raw30891step3 raw30891step2; decide +kernel
      have hl : raw30891step2Labels = labelEmbedding10 ∘ raw30891step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30891step2 raw30891step2Labels raw30891step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5371 node5371Labels := by rfl

theorem canonical30892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30892 raw30892Labels = mixedMoment B node5371 node5371Labels := by
  calc
    mixedMoment B raw30892 raw30892Labels = mixedMoment B raw30892step0 raw30892step0Labels := by
      have hz : ∀ j, raw30892 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30892step0 = (fun i j => raw30892 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30892step0 raw30892; decide +kernel
      have hl : raw30892step0Labels = raw30892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30892 raw30892Labels permutation434 hz
    mixedMoment B raw30892step0 raw30892step0Labels = mixedMoment B raw30892step1 raw30892step1Labels := by
      have hz : ∀ j, raw30892step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30892step1 = (fun i j => raw30892step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30892step1 raw30892step0; decide +kernel
      have hl : raw30892step1Labels = raw30892step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30892step0 raw30892step0Labels permutation80 hz
    mixedMoment B raw30892step1 raw30892step1Labels = mixedMoment B raw30892step2 raw30892step2Labels := by
      have ha : raw30892step2 = (fun i j => raw30892step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30892step2 raw30892step1; decide +kernel
      have hl : raw30892step2Labels = raw30892step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30892step1 raw30892step1Labels permutation25 permutation7
    mixedMoment B raw30892step2 raw30892step2Labels = mixedMoment B raw30892step3 raw30892step3Labels := by
      have ha : raw30892step3 = raw30892step2 := by apply Matrix.ext; unfold raw30892step3 raw30892step2; decide +kernel
      have hl : raw30892step2Labels = labelEmbedding10 ∘ raw30892step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30892step2 raw30892step2Labels raw30892step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5371 node5371Labels := by rfl

theorem canonical30893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30893 raw30893Labels = mixedMoment B node4575 node4575Labels := by
  calc
    mixedMoment B raw30893 raw30893Labels = mixedMoment B raw30893step0 raw30893step0Labels := by
      have hz : ∀ j, raw30893 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30893step0 = (fun i j => raw30893 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30893step0 raw30893; decide +kernel
      have hl : raw30893step0Labels = raw30893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30893 raw30893Labels permutation434 hz
    mixedMoment B raw30893step0 raw30893step0Labels = mixedMoment B raw30893step1 raw30893step1Labels := by
      have hz : ∀ j, raw30893step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30893step1 = (fun i j => raw30893step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30893step1 raw30893step0; decide +kernel
      have hl : raw30893step1Labels = raw30893step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30893step0 raw30893step0Labels permutation80 hz
    _ = mixedMoment B node4575 node4575Labels := by rfl

theorem canonical30894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30894 raw30894Labels = mixedMoment B node5125 node5125Labels := by
  calc
    mixedMoment B raw30894 raw30894Labels = mixedMoment B raw30894step0 raw30894step0Labels := by
      have hz : ∀ j, raw30894 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30894step0 = (fun i j => raw30894 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30894step0 raw30894; decide +kernel
      have hl : raw30894step0Labels = raw30894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30894 raw30894Labels permutation434 hz
    mixedMoment B raw30894step0 raw30894step0Labels = mixedMoment B raw30894step1 raw30894step1Labels := by
      have ha : raw30894step1 = (fun i j => raw30894step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30894step1 raw30894step0; decide +kernel
      have hl : raw30894step1Labels = raw30894step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30894step0 raw30894step0Labels permutation38 permutation2
    _ = mixedMoment B node5125 node5125Labels := by rfl

theorem canonical30895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30895 raw30895Labels = mixedMoment B node5125 node5125Labels := by
  calc
    mixedMoment B raw30895 raw30895Labels = mixedMoment B raw30895step0 raw30895step0Labels := by
      have hz : ∀ j, raw30895 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30895step0 = (fun i j => raw30895 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30895step0 raw30895; decide +kernel
      have hl : raw30895step0Labels = raw30895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30895 raw30895Labels permutation346 hz
    mixedMoment B raw30895step0 raw30895step0Labels = mixedMoment B raw30895step1 raw30895step1Labels := by
      have ha : raw30895step1 = (fun i j => raw30895step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30895step1 raw30895step0; decide +kernel
      have hl : raw30895step1Labels = raw30895step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30895step0 raw30895step0Labels permutation38 permutation2
    _ = mixedMoment B node5125 node5125Labels := by rfl

theorem canonical30896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30896 raw30896Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw30896 raw30896Labels = mixedMoment B raw30896step0 raw30896step0Labels := by
      have hz : ∀ j, raw30896 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30896step0 = (fun i j => raw30896 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30896step0 raw30896; decide +kernel
      have hl : raw30896step0Labels = raw30896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30896 raw30896Labels permutation434 hz
    mixedMoment B raw30896step0 raw30896step0Labels = mixedMoment B raw30896step1 raw30896step1Labels := by
      have hz : ∀ j, raw30896step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30896step1 = (fun i j => raw30896step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30896step1 raw30896step0; decide +kernel
      have hl : raw30896step1Labels = raw30896step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30896step0 raw30896step0Labels permutation80 hz
    _ = mixedMoment B node5238 node5238Labels := by rfl

theorem canonical30897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30897 raw30897Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw30897 raw30897Labels = mixedMoment B raw30897step0 raw30897step0Labels := by
      have hz : ∀ j, raw30897 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30897step0 = (fun i j => raw30897 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30897step0 raw30897; decide +kernel
      have hl : raw30897step0Labels = raw30897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30897 raw30897Labels permutation434 hz
    mixedMoment B raw30897step0 raw30897step0Labels = mixedMoment B raw30897step1 raw30897step1Labels := by
      have hz : ∀ j, raw30897step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30897step1 = (fun i j => raw30897step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30897step1 raw30897step0; decide +kernel
      have hl : raw30897step1Labels = raw30897step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30897step0 raw30897step0Labels permutation80 hz
    mixedMoment B raw30897step1 raw30897step1Labels = mixedMoment B raw30897step2 raw30897step2Labels := by
      have ha : raw30897step2 = (fun i j => raw30897step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30897step2 raw30897step1; decide +kernel
      have hl : raw30897step2Labels = raw30897step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30897step1 raw30897step1Labels permutation9 permutation2
    _ = mixedMoment B node5238 node5238Labels := by rfl

theorem canonical30898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30898 raw30898Labels = mixedMoment B node4515 node4515Labels := by
  calc
    mixedMoment B raw30898 raw30898Labels = mixedMoment B raw30898step0 raw30898step0Labels := by
      have hz : ∀ j, raw30898 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30898step0 = (fun i j => raw30898 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30898step0 raw30898; decide +kernel
      have hl : raw30898step0Labels = raw30898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30898 raw30898Labels permutation434 hz
    _ = mixedMoment B node4515 node4515Labels := by rfl

theorem canonical30899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30899 raw30899Labels = mixedMoment B node4915 node4915Labels := by
  calc
    mixedMoment B raw30899 raw30899Labels = mixedMoment B raw30899step0 raw30899step0Labels := by
      have hz : ∀ j, raw30899 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30899step0 = (fun i j => raw30899 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30899step0 raw30899; decide +kernel
      have hl : raw30899step0Labels = raw30899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30899 raw30899Labels permutation434 hz
    _ = mixedMoment B node4915 node4915Labels := by rfl

theorem canonical30900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30900 raw30900Labels = mixedMoment B node4985 node4985Labels := by
  calc
    mixedMoment B raw30900 raw30900Labels = mixedMoment B raw30900step0 raw30900step0Labels := by
      have ha : raw30900step0 = (fun i j => raw30900 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30900step0 raw30900; decide +kernel
      have hl : raw30900step0Labels = raw30900Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30900 raw30900Labels permutation158 permutation2
    _ = mixedMoment B node4985 node4985Labels := by rfl

theorem canonical30901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30901 raw30901Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw30901 raw30901Labels = mixedMoment B raw30901step0 raw30901step0Labels := by
      have hz : ∀ j, raw30901 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30901step0 = (fun i j => raw30901 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30901step0 raw30901; decide +kernel
      have hl : raw30901step0Labels = raw30901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30901 raw30901Labels permutation434 hz
    _ = mixedMoment B node5015 node5015Labels := by rfl

theorem canonical30902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30902 raw30902Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw30902 raw30902Labels = mixedMoment B raw30902step0 raw30902step0Labels := by
      have hz : ∀ j, raw30902 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30902step0 = (fun i j => raw30902 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30902step0 raw30902; decide +kernel
      have hl : raw30902step0Labels = raw30902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30902 raw30902Labels permutation434 hz
    mixedMoment B raw30902step0 raw30902step0Labels = mixedMoment B raw30902step1 raw30902step1Labels := by
      have ha : raw30902step1 = (fun i j => raw30902step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30902step1 raw30902step0; decide +kernel
      have hl : raw30902step1Labels = raw30902step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30902step0 raw30902step0Labels permutation33 permutation2
    _ = mixedMoment B node5015 node5015Labels := by rfl

theorem canonical30903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30903 raw30903Labels = mixedMoment B node4515 node4515Labels := by
  calc
    mixedMoment B raw30903 raw30903Labels = mixedMoment B raw30903step0 raw30903step0Labels := by
      have hz : ∀ j, raw30903 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30903step0 = (fun i j => raw30903 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30903step0 raw30903; decide +kernel
      have hl : raw30903step0Labels = raw30903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30903 raw30903Labels permutation346 hz
    _ = mixedMoment B node4515 node4515Labels := by rfl

theorem canonical30904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30904 raw30904Labels = mixedMoment B node4915 node4915Labels := by
  calc
    mixedMoment B raw30904 raw30904Labels = mixedMoment B raw30904step0 raw30904step0Labels := by
      have hz : ∀ j, raw30904 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30904step0 = (fun i j => raw30904 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30904step0 raw30904; decide +kernel
      have hl : raw30904step0Labels = raw30904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30904 raw30904Labels permutation346 hz
    _ = mixedMoment B node4915 node4915Labels := by rfl

theorem canonical30905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30905 raw30905Labels = mixedMoment B node4985 node4985Labels := by
  calc
    _ = mixedMoment B node4985 node4985Labels := by rfl

theorem canonical30906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30906 raw30906Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw30906 raw30906Labels = mixedMoment B raw30906step0 raw30906step0Labels := by
      have hz : ∀ j, raw30906 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30906step0 = (fun i j => raw30906 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30906step0 raw30906; decide +kernel
      have hl : raw30906step0Labels = raw30906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30906 raw30906Labels permutation346 hz
    _ = mixedMoment B node5015 node5015Labels := by rfl

theorem canonical30907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30907 raw30907Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw30907 raw30907Labels = mixedMoment B raw30907step0 raw30907step0Labels := by
      have hz : ∀ j, raw30907 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30907step0 = (fun i j => raw30907 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30907step0 raw30907; decide +kernel
      have hl : raw30907step0Labels = raw30907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30907 raw30907Labels permutation346 hz
    mixedMoment B raw30907step0 raw30907step0Labels = mixedMoment B raw30907step1 raw30907step1Labels := by
      have ha : raw30907step1 = (fun i j => raw30907step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30907step1 raw30907step0; decide +kernel
      have hl : raw30907step1Labels = raw30907step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30907step0 raw30907step0Labels permutation33 permutation2
    _ = mixedMoment B node5015 node5015Labels := by rfl

theorem canonical30908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30908 raw30908Labels = mixedMoment B node4520 node4520Labels := by
  calc
    mixedMoment B raw30908 raw30908Labels = mixedMoment B raw30908step0 raw30908step0Labels := by
      have hz : ∀ j, raw30908 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30908step0 = (fun i j => raw30908 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30908step0 raw30908; decide +kernel
      have hl : raw30908step0Labels = raw30908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30908 raw30908Labels permutation434 hz
    mixedMoment B raw30908step0 raw30908step0Labels = mixedMoment B raw30908step1 raw30908step1Labels := by
      have hz : ∀ j, raw30908step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30908step1 = (fun i j => raw30908step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30908step1 raw30908step0; decide +kernel
      have hl : raw30908step1Labels = raw30908step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30908step0 raw30908step0Labels permutation80 hz
    mixedMoment B raw30908step1 raw30908step1Labels = mixedMoment B raw30908step2 raw30908step2Labels := by
      have ha : raw30908step2 = (fun i j => raw30908step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30908step2 raw30908step1; decide +kernel
      have hl : raw30908step2Labels = raw30908step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30908step1 raw30908step1Labels permutation9 permutation2
    _ = mixedMoment B node4520 node4520Labels := by rfl

theorem canonical30909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30909 raw30909Labels = mixedMoment B node4924 node4924Labels := by
  calc
    mixedMoment B raw30909 raw30909Labels = mixedMoment B raw30909step0 raw30909step0Labels := by
      have hz : ∀ j, raw30909 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30909step0 = (fun i j => raw30909 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30909step0 raw30909; decide +kernel
      have hl : raw30909step0Labels = raw30909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30909 raw30909Labels permutation434 hz
    mixedMoment B raw30909step0 raw30909step0Labels = mixedMoment B raw30909step1 raw30909step1Labels := by
      have hz : ∀ j, raw30909step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30909step1 = (fun i j => raw30909step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30909step1 raw30909step0; decide +kernel
      have hl : raw30909step1Labels = raw30909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30909step0 raw30909step0Labels permutation80 hz
    mixedMoment B raw30909step1 raw30909step1Labels = mixedMoment B raw30909step2 raw30909step2Labels := by
      have ha : raw30909step2 = (fun i j => raw30909step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30909step2 raw30909step1; decide +kernel
      have hl : raw30909step2Labels = raw30909step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30909step1 raw30909step1Labels permutation9 permutation2
    _ = mixedMoment B node4924 node4924Labels := by rfl

theorem canonical30910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30910 raw30910Labels = mixedMoment B node4913 node4913Labels := by
  calc
    mixedMoment B raw30910 raw30910Labels = mixedMoment B raw30910step0 raw30910step0Labels := by
      have hz : ∀ j, raw30910 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30910step0 = (fun i j => raw30910 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30910step0 raw30910; decide +kernel
      have hl : raw30910step0Labels = raw30910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30910 raw30910Labels permutation434 hz
    mixedMoment B raw30910step0 raw30910step0Labels = mixedMoment B raw30910step1 raw30910step1Labels := by
      have ha : raw30910step1 = (fun i j => raw30910step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30910step1 raw30910step0; decide +kernel
      have hl : raw30910step1Labels = raw30910step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30910step0 raw30910step0Labels permutation127 permutation2
    mixedMoment B raw30910step1 raw30910step1Labels = mixedMoment B raw30910step2 raw30910step2Labels := by
      have ha : raw30910step2 = -raw30910step1 := by apply Matrix.ext; change ∀ i j, raw30910step2 i j = -(raw30910step1 i j); unfold raw30910step2 raw30910step1; decide +kernel
      have hl : raw30910step2Labels = raw30910step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4913 node4913Labels := by rfl

theorem canonical30911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30911 raw30911Labels = mixedMoment B node4913 node4913Labels := by
  calc
    mixedMoment B raw30911 raw30911Labels = mixedMoment B raw30911step0 raw30911step0Labels := by
      have hz : ∀ j, raw30911 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30911step0 = (fun i j => raw30911 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30911step0 raw30911; decide +kernel
      have hl : raw30911step0Labels = raw30911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30911 raw30911Labels permutation346 hz
    mixedMoment B raw30911step0 raw30911step0Labels = mixedMoment B raw30911step1 raw30911step1Labels := by
      have ha : raw30911step1 = (fun i j => raw30911step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30911step1 raw30911step0; decide +kernel
      have hl : raw30911step1Labels = raw30911step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30911step0 raw30911step0Labels permutation127 permutation2
    mixedMoment B raw30911step1 raw30911step1Labels = mixedMoment B raw30911step2 raw30911step2Labels := by
      have ha : raw30911step2 = -raw30911step1 := by apply Matrix.ext; change ∀ i j, raw30911step2 i j = -(raw30911step1 i j); unfold raw30911step2 raw30911step1; decide +kernel
      have hl : raw30911step2Labels = raw30911step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4913 node4913Labels := by rfl

theorem canonical30912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30912 raw30912Labels = mixedMoment B node5021 node5021Labels := by
  calc
    mixedMoment B raw30912 raw30912Labels = mixedMoment B raw30912step0 raw30912step0Labels := by
      have hz : ∀ j, raw30912 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30912step0 = (fun i j => raw30912 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30912step0 raw30912; decide +kernel
      have hl : raw30912step0Labels = raw30912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30912 raw30912Labels permutation434 hz
    mixedMoment B raw30912step0 raw30912step0Labels = mixedMoment B raw30912step1 raw30912step1Labels := by
      have hz : ∀ j, raw30912step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30912step1 = (fun i j => raw30912step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30912step1 raw30912step0; decide +kernel
      have hl : raw30912step1Labels = raw30912step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30912step0 raw30912step0Labels permutation80 hz
    mixedMoment B raw30912step1 raw30912step1Labels = mixedMoment B raw30912step2 raw30912step2Labels := by
      have ha : raw30912step2 = (fun i j => raw30912step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30912step2 raw30912step1; decide +kernel
      have hl : raw30912step2Labels = raw30912step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30912step1 raw30912step1Labels permutation9 permutation2
    _ = mixedMoment B node5021 node5021Labels := by rfl

theorem canonical30913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30913 raw30913Labels = mixedMoment B node4520 node4520Labels := by
  calc
    mixedMoment B raw30913 raw30913Labels = mixedMoment B raw30913step0 raw30913step0Labels := by
      have hz : ∀ j, raw30913 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30913step0 = (fun i j => raw30913 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30913step0 raw30913; decide +kernel
      have hl : raw30913step0Labels = raw30913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30913 raw30913Labels permutation434 hz
    mixedMoment B raw30913step0 raw30913step0Labels = mixedMoment B raw30913step1 raw30913step1Labels := by
      have hz : ∀ j, raw30913step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30913step1 = (fun i j => raw30913step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30913step1 raw30913step0; decide +kernel
      have hl : raw30913step1Labels = raw30913step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30913step0 raw30913step0Labels permutation80 hz
    _ = mixedMoment B node4520 node4520Labels := by rfl

theorem canonical30914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30914 raw30914Labels = mixedMoment B node4924 node4924Labels := by
  calc
    mixedMoment B raw30914 raw30914Labels = mixedMoment B raw30914step0 raw30914step0Labels := by
      have hz : ∀ j, raw30914 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30914step0 = (fun i j => raw30914 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30914step0 raw30914; decide +kernel
      have hl : raw30914step0Labels = raw30914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30914 raw30914Labels permutation434 hz
    mixedMoment B raw30914step0 raw30914step0Labels = mixedMoment B raw30914step1 raw30914step1Labels := by
      have hz : ∀ j, raw30914step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30914step1 = (fun i j => raw30914step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30914step1 raw30914step0; decide +kernel
      have hl : raw30914step1Labels = raw30914step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30914step0 raw30914step0Labels permutation80 hz
    _ = mixedMoment B node4924 node4924Labels := by rfl

theorem canonical30915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30915 raw30915Labels = mixedMoment B node4913 node4913Labels := by
  calc
    mixedMoment B raw30915 raw30915Labels = mixedMoment B raw30915step0 raw30915step0Labels := by
      have hz : ∀ j, raw30915 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30915step0 = (fun i j => raw30915 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30915step0 raw30915; decide +kernel
      have hl : raw30915step0Labels = raw30915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30915 raw30915Labels permutation434 hz
    mixedMoment B raw30915step0 raw30915step0Labels = mixedMoment B raw30915step1 raw30915step1Labels := by
      have ha : raw30915step1 = (fun i j => raw30915step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30915step1 raw30915step0; decide +kernel
      have hl : raw30915step1Labels = raw30915step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30915step0 raw30915step0Labels permutation151 permutation2
    mixedMoment B raw30915step1 raw30915step1Labels = mixedMoment B raw30915step2 raw30915step2Labels := by
      have ha : raw30915step2 = -raw30915step1 := by apply Matrix.ext; change ∀ i j, raw30915step2 i j = -(raw30915step1 i j); unfold raw30915step2 raw30915step1; decide +kernel
      have hl : raw30915step2Labels = raw30915step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4913 node4913Labels := by rfl

theorem canonical30916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30916 raw30916Labels = mixedMoment B node4913 node4913Labels := by
  calc
    mixedMoment B raw30916 raw30916Labels = mixedMoment B raw30916step0 raw30916step0Labels := by
      have hz : ∀ j, raw30916 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30916step0 = (fun i j => raw30916 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30916step0 raw30916; decide +kernel
      have hl : raw30916step0Labels = raw30916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30916 raw30916Labels permutation346 hz
    mixedMoment B raw30916step0 raw30916step0Labels = mixedMoment B raw30916step1 raw30916step1Labels := by
      have ha : raw30916step1 = (fun i j => raw30916step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30916step1 raw30916step0; decide +kernel
      have hl : raw30916step1Labels = raw30916step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30916step0 raw30916step0Labels permutation151 permutation2
    mixedMoment B raw30916step1 raw30916step1Labels = mixedMoment B raw30916step2 raw30916step2Labels := by
      have ha : raw30916step2 = -raw30916step1 := by apply Matrix.ext; change ∀ i j, raw30916step2 i j = -(raw30916step1 i j); unfold raw30916step2 raw30916step1; decide +kernel
      have hl : raw30916step2Labels = raw30916step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4913 node4913Labels := by rfl

theorem canonical30917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30917 raw30917Labels = mixedMoment B node5021 node5021Labels := by
  calc
    mixedMoment B raw30917 raw30917Labels = mixedMoment B raw30917step0 raw30917step0Labels := by
      have hz : ∀ j, raw30917 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30917step0 = (fun i j => raw30917 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30917step0 raw30917; decide +kernel
      have hl : raw30917step0Labels = raw30917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30917 raw30917Labels permutation434 hz
    mixedMoment B raw30917step0 raw30917step0Labels = mixedMoment B raw30917step1 raw30917step1Labels := by
      have hz : ∀ j, raw30917step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30917step1 = (fun i j => raw30917step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30917step1 raw30917step0; decide +kernel
      have hl : raw30917step1Labels = raw30917step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30917step0 raw30917step0Labels permutation80 hz
    _ = mixedMoment B node5021 node5021Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4515 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4515 node4515Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1099 node1099Labels + mixedMoment B node3233 node3233Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1317 singletonSmall4515
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4515) = raw1317Labels := by decide +kernel
  rw [hl, canonical1317 B hB] at h
  have hc0 : mixedMoment B raw1317 (Fin.cases (0 : Fin 2) singletonSmall4515) =
      mixedMoment B node1099 node1099Labels := by
    have ha : raw1317 = raw1318 := by apply Matrix.ext; unfold raw1317 raw1318; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4515 = raw1318Labels := by decide +kernel
    rw [ha, hj, canonical1318 B hB]
  have hc1 : mixedMoment B raw1317 (Fin.cases (1 : Fin 2) singletonSmall4515) =
      mixedMoment B node3233 node3233Labels := by
    have ha : raw1317 = raw1319 := by apply Matrix.ext; unfold raw1317 raw1319; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4515 = raw1319Labels := by decide +kernel
    rw [ha, hj, canonical1319 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4520 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4520 node4520Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1104 node1104Labels + mixedMoment B node3237 node3237Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1332 singletonSmall4520
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4520) = raw1332Labels := by decide +kernel
  rw [hl, canonical1332 B hB] at h
  have hc0 : mixedMoment B raw1332 (Fin.cases (0 : Fin 2) singletonSmall4520) =
      mixedMoment B node1104 node1104Labels := by
    have ha : raw1332 = raw1333 := by apply Matrix.ext; unfold raw1332 raw1333; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4520 = raw1333Labels := by decide +kernel
    rw [ha, hj, canonical1333 B hB]
  have hc1 : mixedMoment B raw1332 (Fin.cases (1 : Fin 2) singletonSmall4520) =
      mixedMoment B node3237 node3237Labels := by
    have ha : raw1332 = raw1334 := by apply Matrix.ext; unfold raw1332 raw1334; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4520 = raw1334Labels := by decide +kernel
    rw [ha, hj, canonical1334 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4575 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4575 node4575Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1193 node1193Labels + mixedMoment B node3248 node3248Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1410 singletonSmall4575
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4575) = raw1410Labels := by decide +kernel
  rw [hl, canonical1410 B hB] at h
  have hc0 : mixedMoment B raw1410 (Fin.cases (0 : Fin 2) singletonSmall4575) =
      mixedMoment B node1193 node1193Labels := by
    have ha : raw1410 = raw1411 := by apply Matrix.ext; unfold raw1410 raw1411; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4575 = raw1411Labels := by decide +kernel
    rw [ha, hj, canonical1411 B hB]
  have hc1 : mixedMoment B raw1410 (Fin.cases (1 : Fin 2) singletonSmall4575) =
      mixedMoment B node3248 node3248Labels := by
    have ha : raw1410 = raw1412 := by apply Matrix.ext; unfold raw1410 raw1412; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4575 = raw1412Labels := by decide +kernel
    rw [ha, hj, canonical1412 B hB]
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

theorem singleton4913 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4913 node4913Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2306 node2306Labels + mixedMoment B node3318 node3318Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1863 singletonSmall4913
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4913) = raw1863Labels := by decide +kernel
  rw [hl, canonical1863 B hB] at h
  have hc0 : mixedMoment B raw1863 (Fin.cases (0 : Fin 2) singletonSmall4913) =
      mixedMoment B node2306 node2306Labels := by
    have ha : raw1863 = raw1864 := by apply Matrix.ext; unfold raw1863 raw1864; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4913 = raw1864Labels := by decide +kernel
    rw [ha, hj, canonical1864 B hB]
  have hc1 : mixedMoment B raw1863 (Fin.cases (1 : Fin 2) singletonSmall4913) =
      mixedMoment B node3318 node3318Labels := by
    have ha : raw1863 = raw1865 := by apply Matrix.ext; unfold raw1863 raw1865; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4913 = raw1865Labels := by decide +kernel
    rw [ha, hj, canonical1865 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4985 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4985 node4985Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2370 node2370Labels + mixedMoment B node3334 node3334Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1989 singletonSmall4985
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4985) = raw1989Labels := by decide +kernel
  rw [hl, canonical1989 B hB] at h
  have hc0 : mixedMoment B raw1989 (Fin.cases (0 : Fin 2) singletonSmall4985) =
      mixedMoment B node2370 node2370Labels := by
    have ha : raw1989 = raw1990 := by apply Matrix.ext; unfold raw1989 raw1990; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4985 = raw1990Labels := by decide +kernel
    rw [ha, hj, canonical1990 B hB]
  have hc1 : mixedMoment B raw1989 (Fin.cases (1 : Fin 2) singletonSmall4985) =
      mixedMoment B node3334 node3334Labels := by
    have ha : raw1989 = raw1991 := by apply Matrix.ext; unfold raw1989 raw1991; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4985 = raw1991Labels := by decide +kernel
    rw [ha, hj, canonical1991 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5015 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5015 node5015Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2400 node2400Labels + mixedMoment B node3344 node3344Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2025 singletonSmall5015
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5015) = raw2025Labels := by decide +kernel
  rw [hl, canonical2025 B hB] at h
  have hc0 : mixedMoment B raw2025 (Fin.cases (0 : Fin 2) singletonSmall5015) =
      mixedMoment B node2400 node2400Labels := by
    have ha : raw2025 = raw2026 := by apply Matrix.ext; unfold raw2025 raw2026; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5015 = raw2026Labels := by decide +kernel
    rw [ha, hj, canonical2026 B hB]
  have hc1 : mixedMoment B raw2025 (Fin.cases (1 : Fin 2) singletonSmall5015) =
      mixedMoment B node3344 node3344Labels := by
    have ha : raw2025 = raw2027 := by apply Matrix.ext; unfold raw2025 raw2027; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5015 = raw2027Labels := by decide +kernel
    rw [ha, hj, canonical2027 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5021 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5021 node5021Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2407 node2407Labels + mixedMoment B node3360 node3360Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2031 singletonSmall5021
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5021) = raw2031Labels := by decide +kernel
  rw [hl, canonical2031 B hB] at h
  have hc0 : mixedMoment B raw2031 (Fin.cases (0 : Fin 2) singletonSmall5021) =
      mixedMoment B node2407 node2407Labels := by
    have ha : raw2031 = raw2032 := by apply Matrix.ext; unfold raw2031 raw2032; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5021 = raw2032Labels := by decide +kernel
    rw [ha, hj, canonical2032 B hB]
  have hc1 : mixedMoment B raw2031 (Fin.cases (1 : Fin 2) singletonSmall5021) =
      mixedMoment B node3360 node3360Labels := by
    have ha : raw2031 = raw2033 := by apply Matrix.ext; unfold raw2031 raw2033; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5021 = raw2033Labels := by decide +kernel
    rw [ha, hj, canonical2033 B hB]
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

theorem singleton5125 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5125 node5125Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2539 node2539Labels + mixedMoment B node3372 node3372Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2157 singletonSmall5125
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5125) = raw2157Labels := by decide +kernel
  rw [hl, canonical2157 B hB] at h
  have hc0 : mixedMoment B raw2157 (Fin.cases (0 : Fin 2) singletonSmall5125) =
      mixedMoment B node2539 node2539Labels := by
    have ha : raw2157 = raw2158 := by apply Matrix.ext; unfold raw2157 raw2158; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5125 = raw2158Labels := by decide +kernel
    rw [ha, hj, canonical2158 B hB]
  have hc1 : mixedMoment B raw2157 (Fin.cases (1 : Fin 2) singletonSmall5125) =
      mixedMoment B node3372 node3372Labels := by
    have ha : raw2157 = raw2159 := by apply Matrix.ext; unfold raw2157 raw2159; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5125 = raw2159Labels := by decide +kernel
    rw [ha, hj, canonical2159 B hB]
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

theorem singleton5238 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5238 node5238Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2686 node2686Labels + mixedMoment B node3397 node3397Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2256 singletonSmall5238
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5238) = raw2256Labels := by decide +kernel
  rw [hl, canonical2256 B hB] at h
  have hc0 : mixedMoment B raw2256 (Fin.cases (0 : Fin 2) singletonSmall5238) =
      mixedMoment B node2686 node2686Labels := by
    have ha : raw2256 = raw2257 := by apply Matrix.ext; unfold raw2256 raw2257; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5238 = raw2257Labels := by decide +kernel
    rw [ha, hj, canonical2257 B hB]
  have hc1 : mixedMoment B raw2256 (Fin.cases (1 : Fin 2) singletonSmall5238) =
      mixedMoment B node3397 node3397Labels := by
    have ha : raw2256 = raw2258 := by apply Matrix.ext; unfold raw2256 raw2258; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5238 = raw2258Labels := by decide +kernel
    rw [ha, hj, canonical2258 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound1099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1099 node1099Labels = Sparse.eval nodeValue1099 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1099) = mixedMoment B node1099 node1099Labels := rfl
  simpa [nodeValue1099, Sparse.eval] using hc.symm

theorem sound1104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1104 node1104Labels = Sparse.eval nodeValue1104 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1104) = mixedMoment B node1104 node1104Labels := rfl
  simpa [nodeValue1104, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1193 node1193Labels = Sparse.eval nodeValue1193 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1193) = mixedMoment B node1193 node1193Labels := rfl
  simpa [nodeValue1193, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2306 node2306Labels = Sparse.eval nodeValue2306 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2306) = mixedMoment B node2306 node2306Labels := rfl
  simpa [nodeValue2306, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2370 node2370Labels = Sparse.eval nodeValue2370 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2370) = mixedMoment B node2370 node2370Labels := rfl
  simpa [nodeValue2370, Sparse.eval] using hc.symm

theorem sound2400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2400 node2400Labels = Sparse.eval nodeValue2400 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2400) = mixedMoment B node2400 node2400Labels := rfl
  simpa [nodeValue2400, Sparse.eval] using hc.symm

theorem sound2407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2407 node2407Labels = Sparse.eval nodeValue2407 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2407) = mixedMoment B node2407 node2407Labels := rfl
  simpa [nodeValue2407, Sparse.eval] using hc.symm

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

theorem sound2539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2539 node2539Labels = Sparse.eval nodeValue2539 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2539) = mixedMoment B node2539 node2539Labels := rfl
  simpa [nodeValue2539, Sparse.eval] using hc.symm

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

theorem sound2686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2686 node2686Labels = Sparse.eval nodeValue2686 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2686) = mixedMoment B node2686 node2686Labels := rfl
  simpa [nodeValue2686, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3233 node3233Labels = Sparse.eval nodeValue3233 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3233) = mixedMoment B node3233 node3233Labels := rfl
  simpa [nodeValue3233, Sparse.eval] using hc.symm

theorem sound3237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3237 node3237Labels = Sparse.eval nodeValue3237 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3237) = mixedMoment B node3237 node3237Labels := rfl
  simpa [nodeValue3237, Sparse.eval] using hc.symm

theorem sound3248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3248 node3248Labels = Sparse.eval nodeValue3248 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3248) = mixedMoment B node3248 node3248Labels := rfl
  simpa [nodeValue3248, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3318 node3318Labels = Sparse.eval nodeValue3318 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3318) = mixedMoment B node3318 node3318Labels := rfl
  simpa [nodeValue3318, Sparse.eval] using hc.symm

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

theorem sound3334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3334 node3334Labels = Sparse.eval nodeValue3334 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3334) = mixedMoment B node3334 node3334Labels := rfl
  simpa [nodeValue3334, Sparse.eval] using hc.symm

theorem sound3344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3344 node3344Labels = Sparse.eval nodeValue3344 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3344) = mixedMoment B node3344 node3344Labels := rfl
  simpa [nodeValue3344, Sparse.eval] using hc.symm

theorem sound3360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3360 node3360Labels = Sparse.eval nodeValue3360 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3360) = mixedMoment B node3360 node3360Labels := rfl
  simpa [nodeValue3360, Sparse.eval] using hc.symm

theorem sound3372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3372 node3372Labels = Sparse.eval nodeValue3372 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3372) = mixedMoment B node3372 node3372Labels := rfl
  simpa [nodeValue3372, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3397 node3397Labels = Sparse.eval nodeValue3397 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3397) = mixedMoment B node3397 node3397Labels := rfl
  simpa [nodeValue3397, Sparse.eval] using hc.symm

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

theorem sound4089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4089 node4089Labels = Sparse.eval nodeValue4089 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4089) = mixedMoment B node4089 node4089Labels := rfl
  simpa [nodeValue4089, Sparse.eval] using hc.symm

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

theorem sound4515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4515 node4515Labels = Sparse.eval nodeValue4515 (mixedVector B) := by
  have h := singleton4515 B _hB
  rw [sound1099 B _hB _hF, sound3233 B _hB _hF] at h
  norm_num [nodeValue4515, nodeValue1099, nodeValue3233, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4520 node4520Labels = Sparse.eval nodeValue4520 (mixedVector B) := by
  have h := singleton4520 B _hB
  rw [sound1104 B _hB _hF, sound3237 B _hB _hF] at h
  norm_num [nodeValue4520, nodeValue1104, nodeValue3237, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4575 node4575Labels = Sparse.eval nodeValue4575 (mixedVector B) := by
  have h := singleton4575 B _hB
  rw [sound1193 B _hB _hF, sound3248 B _hB _hF] at h
  norm_num [nodeValue4575, nodeValue1193, nodeValue3248, Sparse.eval] at h ⊢
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

theorem zero4915 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4915 node4915Labels = 0 := by
  exact mixedMoment_order_one B hB node4915 node4915Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4924 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4924 node4924Labels = 0 := by
  exact mixedMoment_order_one B hB node4924 node4924Labels 1
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

theorem sound4913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4913 node4913Labels = Sparse.eval nodeValue4913 (mixedVector B) := by
  have h := singleton4913 B _hB
  rw [sound2306 B _hB _hF, sound3318 B _hB _hF] at h
  norm_num [nodeValue4913, nodeValue2306, nodeValue3318, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4915 node4915Labels = Sparse.eval nodeValue4915 (mixedVector B) := by
  simpa only [nodeValue4915, Sparse.eval_nil] using zero4915 B _hB _hF

theorem sound4924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4924 node4924Labels = Sparse.eval nodeValue4924 (mixedVector B) := by
  simpa only [nodeValue4924, Sparse.eval_nil] using zero4924 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4985 node4985Labels = Sparse.eval nodeValue4985 (mixedVector B) := by
  have h := singleton4985 B _hB
  rw [sound2370 B _hB _hF, sound3334 B _hB _hF] at h
  norm_num [nodeValue4985, nodeValue2370, nodeValue3334, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5015 node5015Labels = Sparse.eval nodeValue5015 (mixedVector B) := by
  have h := singleton5015 B _hB
  rw [sound2400 B _hB _hF, sound3344 B _hB _hF] at h
  norm_num [nodeValue5015, nodeValue2400, nodeValue3344, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5021 node5021Labels = Sparse.eval nodeValue5021 (mixedVector B) := by
  have h := singleton5021 B _hB
  rw [sound2407 B _hB _hF, sound3360 B _hB _hF] at h
  norm_num [nodeValue5021, nodeValue2407, nodeValue3360, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5125 node5125Labels = Sparse.eval nodeValue5125 (mixedVector B) := by
  have h := singleton5125 B _hB
  rw [sound2539 B _hB _hF, sound3372 B _hB _hF] at h
  norm_num [nodeValue5125, nodeValue2539, nodeValue3372, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound5238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5238 node5238Labels = Sparse.eval nodeValue5238 (mixedVector B) := by
  have h := singleton5238 B _hB
  rw [sound2686 B _hB _hF, sound3397 B _hB _hF] at h
  norm_num [nodeValue5238, nodeValue2686, nodeValue3397, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5327 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5327 node5327Labels = 0 := by
  exact mixedMoment_order_one B hB node5327 node5327Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5371 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5371 node5371Labels = 0 := by
  exact mixedMoment_order_one B hB node5371 node5371Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5327 node5327Labels = Sparse.eval nodeValue5327 (mixedVector B) := by
  simpa only [nodeValue5327, Sparse.eval_nil] using zero5327 B _hB _hF

theorem sound5371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5371 node5371Labels = Sparse.eval nodeValue5371 (mixedVector B) := by
  simpa only [nodeValue5371, Sparse.eval_nil] using zero5371 B _hB _hF

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

theorem sourceEq2249 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2249 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2249 + difference 0 1) (sourceB2249 + difference 1 0) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (tripleCharges (sourceA2249 + difference 0 1) (sourceB2249 + difference 1 0) sourceC2249) = raw30888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30888; decide +kernel
    rw [ha]
    exact (canonical30888 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2249 + difference 0 2) (sourceB2249 + difference 2 0) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5327) := by
    have ha : (tripleCharges (sourceA2249 + difference 0 2) (sourceB2249 + difference 2 0) sourceC2249) = raw30889 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30889; decide +kernel
    rw [ha]
    exact (canonical30889 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2249 + difference 0 3) (sourceB2249 + difference 3 0) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5327) := by
    have ha : (tripleCharges (sourceA2249 + difference 0 3) (sourceB2249 + difference 3 0) sourceC2249) = raw30890 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30890; decide +kernel
    rw [ha]
    exact (canonical30890 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2249 + difference 0 4) (sourceB2249 + difference 4 0) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2249 + difference 0 4) (sourceB2249 + difference 4 0) sourceC2249) = raw30891 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30891; decide +kernel
    rw [ha]
    exact (canonical30891 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2249 + difference 0 5) (sourceB2249 + difference 5 0) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2249 + difference 0 5) (sourceB2249 + difference 5 0) sourceC2249) = raw30892 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30892; decide +kernel
    rw [ha]
    exact (canonical30892 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2249 + difference 1 0) (sourceB2249 + difference 0 1) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4575) := by
    have ha : (tripleCharges (sourceA2249 + difference 1 0) (sourceB2249 + difference 0 1) sourceC2249) = raw30893 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30893; decide +kernel
    rw [ha]
    exact (canonical30893 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2249 + difference 1 2) (sourceB2249 + difference 2 1) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5125) := by
    have ha : (tripleCharges (sourceA2249 + difference 1 2) (sourceB2249 + difference 2 1) sourceC2249) = raw30894 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30894; decide +kernel
    rw [ha]
    exact (canonical30894 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2249 + difference 1 3) (sourceB2249 + difference 3 1) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5125) := by
    have ha : (tripleCharges (sourceA2249 + difference 1 3) (sourceB2249 + difference 3 1) sourceC2249) = raw30895 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30895; decide +kernel
    rw [ha]
    exact (canonical30895 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2249 + difference 1 4) (sourceB2249 + difference 4 1) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2249 + difference 1 4) (sourceB2249 + difference 4 1) sourceC2249) = raw30896 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30896; decide +kernel
    rw [ha]
    exact (canonical30896 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2249 + difference 1 5) (sourceB2249 + difference 5 1) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2249 + difference 1 5) (sourceB2249 + difference 5 1) sourceC2249) = raw30897 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30897; decide +kernel
    rw [ha]
    exact (canonical30897 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2249 + difference 2 0) (sourceB2249 + difference 0 2) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4515) := by
    have ha : (tripleCharges (sourceA2249 + difference 2 0) (sourceB2249 + difference 0 2) sourceC2249) = raw30898 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30898; decide +kernel
    rw [ha]
    exact (canonical30898 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2249 + difference 2 1) (sourceB2249 + difference 1 2) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4915) := by
    have ha : (tripleCharges (sourceA2249 + difference 2 1) (sourceB2249 + difference 1 2) sourceC2249) = raw30899 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30899; decide +kernel
    rw [ha]
    exact (canonical30899 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2249 + difference 2 3) (sourceB2249 + difference 3 2) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4985) := by
    have ha : (tripleCharges (sourceA2249 + difference 2 3) (sourceB2249 + difference 3 2) sourceC2249) = raw30900 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30900; decide +kernel
    rw [ha]
    exact (canonical30900 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2249 + difference 2 4) (sourceB2249 + difference 4 2) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2249 + difference 2 4) (sourceB2249 + difference 4 2) sourceC2249) = raw30901 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30901; decide +kernel
    rw [ha]
    exact (canonical30901 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2249 + difference 2 5) (sourceB2249 + difference 5 2) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2249 + difference 2 5) (sourceB2249 + difference 5 2) sourceC2249) = raw30902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30902; decide +kernel
    rw [ha]
    exact (canonical30902 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2249 + difference 3 0) (sourceB2249 + difference 0 3) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4515) := by
    have ha : (tripleCharges (sourceA2249 + difference 3 0) (sourceB2249 + difference 0 3) sourceC2249) = raw30903 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30903; decide +kernel
    rw [ha]
    exact (canonical30903 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2249 + difference 3 1) (sourceB2249 + difference 1 3) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4915) := by
    have ha : (tripleCharges (sourceA2249 + difference 3 1) (sourceB2249 + difference 1 3) sourceC2249) = raw30904 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30904; decide +kernel
    rw [ha]
    exact (canonical30904 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2249 + difference 3 2) (sourceB2249 + difference 2 3) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4985) := by
    have ha : (tripleCharges (sourceA2249 + difference 3 2) (sourceB2249 + difference 2 3) sourceC2249) = raw30905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30905; decide +kernel
    rw [ha]
    exact (canonical30905 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2249 + difference 3 4) (sourceB2249 + difference 4 3) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2249 + difference 3 4) (sourceB2249 + difference 4 3) sourceC2249) = raw30906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30906; decide +kernel
    rw [ha]
    exact (canonical30906 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2249 + difference 3 5) (sourceB2249 + difference 5 3) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2249 + difference 3 5) (sourceB2249 + difference 5 3) sourceC2249) = raw30907 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30907; decide +kernel
    rw [ha]
    exact (canonical30907 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2249 + difference 4 0) (sourceB2249 + difference 0 4) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4520) := by
    have ha : (tripleCharges (sourceA2249 + difference 4 0) (sourceB2249 + difference 0 4) sourceC2249) = raw30908 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30908; decide +kernel
    rw [ha]
    exact (canonical30908 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2249 + difference 4 1) (sourceB2249 + difference 1 4) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4924) := by
    have ha : (tripleCharges (sourceA2249 + difference 4 1) (sourceB2249 + difference 1 4) sourceC2249) = raw30909 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30909; decide +kernel
    rw [ha]
    exact (canonical30909 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2249 + difference 4 2) (sourceB2249 + difference 2 4) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4913) := by
    have ha : (tripleCharges (sourceA2249 + difference 4 2) (sourceB2249 + difference 2 4) sourceC2249) = raw30910 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30910; decide +kernel
    rw [ha]
    exact (canonical30910 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2249 + difference 4 3) (sourceB2249 + difference 3 4) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4913) := by
    have ha : (tripleCharges (sourceA2249 + difference 4 3) (sourceB2249 + difference 3 4) sourceC2249) = raw30911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30911; decide +kernel
    rw [ha]
    exact (canonical30911 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2249 + difference 4 5) (sourceB2249 + difference 5 4) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5021) := by
    have ha : (tripleCharges (sourceA2249 + difference 4 5) (sourceB2249 + difference 5 4) sourceC2249) = raw30912 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30912; decide +kernel
    rw [ha]
    exact (canonical30912 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2249 + difference 5 0) (sourceB2249 + difference 0 5) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4520) := by
    have ha : (tripleCharges (sourceA2249 + difference 5 0) (sourceB2249 + difference 0 5) sourceC2249) = raw30913 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30913; decide +kernel
    rw [ha]
    exact (canonical30913 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2249 + difference 5 1) (sourceB2249 + difference 1 5) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4924) := by
    have ha : (tripleCharges (sourceA2249 + difference 5 1) (sourceB2249 + difference 1 5) sourceC2249) = raw30914 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30914; decide +kernel
    rw [ha]
    exact (canonical30914 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2249 + difference 5 2) (sourceB2249 + difference 2 5) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4913) := by
    have ha : (tripleCharges (sourceA2249 + difference 5 2) (sourceB2249 + difference 2 5) sourceC2249) = raw30915 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30915; decide +kernel
    rw [ha]
    exact (canonical30915 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2249 + difference 5 3) (sourceB2249 + difference 3 5) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4913) := by
    have ha : (tripleCharges (sourceA2249 + difference 5 3) (sourceB2249 + difference 3 5) sourceC2249) = raw30916 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30916; decide +kernel
    rw [ha]
    exact (canonical30916 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2249 + difference 5 4) (sourceB2249 + difference 4 5) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5021) := by
    have ha : (tripleCharges (sourceA2249 + difference 5 4) (sourceB2249 + difference 4 5) sourceC2249) = raw30917 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30917; decide +kernel
    rw [ha]
    exact (canonical30917 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2249 sourceB2249 sourceC2249
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2249, Integer.Sparse.eval]
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

theorem reindexCheck1838 : Integer.Sparse.reindex keyMap MixedData.row1838 = numericRow1838 := by decide +kernel

theorem numericCheck1838 (x : Master → ℝ) : Integer.Sparse.eval numericRow1838 x =
    (4 : ℝ) * reducedSource1838 x := by
  norm_num [numericRow1838, reducedSource1838, Integer.Sparse.eval, Sparse.eval, nodeValue4089, nodeValue4515, nodeValue4520, nodeValue4575, nodeValue4913, nodeValue4915, nodeValue4924, nodeValue4985, nodeValue5015, nodeValue5021, nodeValue5125, nodeValue5238, nodeValue5327, nodeValue5371]
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

theorem reducedZero1838 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1838 (mixedVector B) = 0 := by
  have h4089 : mixedVector B (Sum.inr 4089) = Sparse.eval nodeValue4089 (mixedVector B) := by
    change mixedMoment B node4089 node4089Labels = _
    exact sound4089 B hB hF
  have h4515 : mixedVector B (Sum.inr 4515) = Sparse.eval nodeValue4515 (mixedVector B) := by
    change mixedMoment B node4515 node4515Labels = _
    exact sound4515 B hB hF
  have h4520 : mixedVector B (Sum.inr 4520) = Sparse.eval nodeValue4520 (mixedVector B) := by
    change mixedMoment B node4520 node4520Labels = _
    exact sound4520 B hB hF
  have h4575 : mixedVector B (Sum.inr 4575) = Sparse.eval nodeValue4575 (mixedVector B) := by
    change mixedMoment B node4575 node4575Labels = _
    exact sound4575 B hB hF
  have h4913 : mixedVector B (Sum.inr 4913) = Sparse.eval nodeValue4913 (mixedVector B) := by
    change mixedMoment B node4913 node4913Labels = _
    exact sound4913 B hB hF
  have h4915 : mixedVector B (Sum.inr 4915) = Sparse.eval nodeValue4915 (mixedVector B) := by
    change mixedMoment B node4915 node4915Labels = _
    exact sound4915 B hB hF
  have h4924 : mixedVector B (Sum.inr 4924) = Sparse.eval nodeValue4924 (mixedVector B) := by
    change mixedMoment B node4924 node4924Labels = _
    exact sound4924 B hB hF
  have h4985 : mixedVector B (Sum.inr 4985) = Sparse.eval nodeValue4985 (mixedVector B) := by
    change mixedMoment B node4985 node4985Labels = _
    exact sound4985 B hB hF
  have h5015 : mixedVector B (Sum.inr 5015) = Sparse.eval nodeValue5015 (mixedVector B) := by
    change mixedMoment B node5015 node5015Labels = _
    exact sound5015 B hB hF
  have h5021 : mixedVector B (Sum.inr 5021) = Sparse.eval nodeValue5021 (mixedVector B) := by
    change mixedMoment B node5021 node5021Labels = _
    exact sound5021 B hB hF
  have h5125 : mixedVector B (Sum.inr 5125) = Sparse.eval nodeValue5125 (mixedVector B) := by
    change mixedMoment B node5125 node5125Labels = _
    exact sound5125 B hB hF
  have h5238 : mixedVector B (Sum.inr 5238) = Sparse.eval nodeValue5238 (mixedVector B) := by
    change mixedMoment B node5238 node5238Labels = _
    exact sound5238 B hB hF
  have h5327 : mixedVector B (Sum.inr 5327) = Sparse.eval nodeValue5327 (mixedVector B) := by
    change mixedMoment B node5327 node5327Labels = _
    exact sound5327 B hB hF
  have h5371 : mixedVector B (Sum.inr 5371) = Sparse.eval nodeValue5371 (mixedVector B) := by
    change mixedMoment B node5371 node5371Labels = _
    exact sound5371 B hB hF
  simpa only [sourceForm2249, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4089, h4515, h4520, h4575, h4913, h4915, h4924, h4985, h5015, h5021, h5125, h5238, h5327, h5371, reducedSource1838] using sourceEq2249 B hB

theorem rowSound1838_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1838 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1838, numericCheck1838, reducedZero1838 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838_e_oai
