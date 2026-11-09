-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:51:58.337445+00:00
-- url     : https://prove2.me/submissions/6fed3b35-316b-427b-a297-b0e866ba5b41

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
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
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

theorem canonical1338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1338 raw1338Labels = mixedMoment B node4522 node4522Labels := by
  calc
    mixedMoment B raw1338 raw1338Labels = mixedMoment B raw1338step0 raw1338step0Labels := by
      have ha : raw1338step0 = (fun i j => raw1338 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1338step0 raw1338; decide +kernel
      have hl : raw1338step0Labels = raw1338Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1338 raw1338Labels permutation152 permutation4
    mixedMoment B raw1338step0 raw1338step0Labels = mixedMoment B raw1338step1 raw1338step1Labels := by
      have ha : raw1338step1 = raw1338step0 := by apply Matrix.ext; unfold raw1338step1 raw1338step0; decide +kernel
      have hl : raw1338step0Labels = labelEmbedding7 ∘ raw1338step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1338step0 raw1338step0Labels raw1338step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4522 node4522Labels := by rfl

theorem canonical1339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1339 raw1339Labels = mixedMoment B node1106 node1106Labels := by
  calc
    mixedMoment B raw1339 raw1339Labels = mixedMoment B raw1339step0 raw1339step0Labels := by
      have ha : raw1339step0 = (fun i j => raw1339 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1339step0 raw1339; decide +kernel
      have hl : raw1339step0Labels = raw1339Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1339 raw1339Labels permutation152 permutation4
    _ = mixedMoment B node1106 node1106Labels := by rfl

theorem canonical1340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1340 raw1340Labels = mixedMoment B node3249 node3249Labels := by
  calc
    mixedMoment B raw1340 raw1340Labels = mixedMoment B raw1340step0 raw1340step0Labels := by
      have ha : raw1340step0 = (fun i j => raw1340 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1340step0 raw1340; decide +kernel
      have hl : raw1340step0Labels = raw1340Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1340 raw1340Labels permutation152 permutation6
    mixedMoment B raw1340step0 raw1340step0Labels = mixedMoment B raw1340step1 raw1340step1Labels := by
      have ha : raw1340step1 = -raw1340step0 := by apply Matrix.ext; change ∀ i j, raw1340step1 i j = -(raw1340step0 i j); unfold raw1340step1 raw1340step0; decide +kernel
      have hl : raw1340step1Labels = raw1340step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1340step1 raw1340step1Labels = mixedMoment B raw1340step2 raw1340step2Labels := by
      have ha : raw1340step2 = raw1340step1 := by apply Matrix.ext; unfold raw1340step2 raw1340step1; decide +kernel
      have hl : raw1340step1Labels = labelEmbedding1 ∘ raw1340step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1340step1 raw1340step1Labels raw1340step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3249 node3249Labels := by rfl

theorem canonical1350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1350 raw1350Labels = mixedMoment B node4526 node4526Labels := by
  calc
    mixedMoment B raw1350 raw1350Labels = mixedMoment B raw1350step0 raw1350step0Labels := by
      have ha : raw1350step0 = (fun i j => raw1350 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1350step0 raw1350; decide +kernel
      have hl : raw1350step0Labels = raw1350Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1350 raw1350Labels permutation32 permutation4
    mixedMoment B raw1350step0 raw1350step0Labels = mixedMoment B raw1350step1 raw1350step1Labels := by
      have ha : raw1350step1 = raw1350step0 := by apply Matrix.ext; unfold raw1350step1 raw1350step0; decide +kernel
      have hl : raw1350step0Labels = labelEmbedding7 ∘ raw1350step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1350step0 raw1350step0Labels raw1350step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4526 node4526Labels := by rfl

theorem canonical1351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1351 raw1351Labels = mixedMoment B node1110 node1110Labels := by
  calc
    mixedMoment B raw1351 raw1351Labels = mixedMoment B raw1351step0 raw1351step0Labels := by
      have ha : raw1351step0 = (fun i j => raw1351 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1351step0 raw1351; decide +kernel
      have hl : raw1351step0Labels = raw1351Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1351 raw1351Labels permutation32 permutation4
    _ = mixedMoment B node1110 node1110Labels := by rfl

theorem canonical1352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1352 raw1352Labels = mixedMoment B node3252 node3252Labels := by
  calc
    mixedMoment B raw1352 raw1352Labels = mixedMoment B raw1352step0 raw1352step0Labels := by
      have ha : raw1352step0 = (fun i j => raw1352 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1352step0 raw1352; decide +kernel
      have hl : raw1352step0Labels = raw1352Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1352 raw1352Labels permutation32 permutation6
    mixedMoment B raw1352step0 raw1352step0Labels = mixedMoment B raw1352step1 raw1352step1Labels := by
      have ha : raw1352step1 = -raw1352step0 := by apply Matrix.ext; change ∀ i j, raw1352step1 i j = -(raw1352step0 i j); unfold raw1352step1 raw1352step0; decide +kernel
      have hl : raw1352step1Labels = raw1352step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1352step1 raw1352step1Labels = mixedMoment B raw1352step2 raw1352step2Labels := by
      have ha : raw1352step2 = raw1352step1 := by apply Matrix.ext; unfold raw1352step2 raw1352step1; decide +kernel
      have hl : raw1352step1Labels = labelEmbedding1 ∘ raw1352step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1352step1 raw1352step1Labels raw1352step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3252 node3252Labels := by rfl

theorem canonical1359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1359 raw1359Labels = mixedMoment B node4539 node4539Labels := by
  calc
    mixedMoment B raw1359 raw1359Labels = mixedMoment B raw1359step0 raw1359step0Labels := by
      have ha : raw1359step0 = (fun i j => raw1359 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1359step0 raw1359; decide +kernel
      have hl : raw1359step0Labels = raw1359Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1359 raw1359Labels permutation32 permutation4
    mixedMoment B raw1359step0 raw1359step0Labels = mixedMoment B raw1359step1 raw1359step1Labels := by
      have ha : raw1359step1 = raw1359step0 := by apply Matrix.ext; unfold raw1359step1 raw1359step0; decide +kernel
      have hl : raw1359step0Labels = labelEmbedding7 ∘ raw1359step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1359step0 raw1359step0Labels raw1359step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4539 node4539Labels := by rfl

theorem canonical1360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1360 raw1360Labels = mixedMoment B node1124 node1124Labels := by
  calc
    mixedMoment B raw1360 raw1360Labels = mixedMoment B raw1360step0 raw1360step0Labels := by
      have ha : raw1360step0 = (fun i j => raw1360 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1360step0 raw1360; decide +kernel
      have hl : raw1360step0Labels = raw1360Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1360 raw1360Labels permutation32 permutation4
    _ = mixedMoment B node1124 node1124Labels := by rfl

theorem canonical1361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1361 raw1361Labels = mixedMoment B node3254 node3254Labels := by
  calc
    mixedMoment B raw1361 raw1361Labels = mixedMoment B raw1361step0 raw1361step0Labels := by
      have ha : raw1361step0 = (fun i j => raw1361 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1361step0 raw1361; decide +kernel
      have hl : raw1361step0Labels = raw1361Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1361 raw1361Labels permutation32 permutation6
    mixedMoment B raw1361step0 raw1361step0Labels = mixedMoment B raw1361step1 raw1361step1Labels := by
      have ha : raw1361step1 = -raw1361step0 := by apply Matrix.ext; change ∀ i j, raw1361step1 i j = -(raw1361step0 i j); unfold raw1361step1 raw1361step0; decide +kernel
      have hl : raw1361step1Labels = raw1361step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1361step1 raw1361step1Labels = mixedMoment B raw1361step2 raw1361step2Labels := by
      have ha : raw1361step2 = raw1361step1 := by apply Matrix.ext; unfold raw1361step2 raw1361step1; decide +kernel
      have hl : raw1361step1Labels = labelEmbedding1 ∘ raw1361step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1361step1 raw1361step1Labels raw1361step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3254 node3254Labels := by rfl

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

theorem canonical1419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1419 raw1419Labels = mixedMoment B node4586 node4586Labels := by
  calc
    mixedMoment B raw1419 raw1419Labels = mixedMoment B raw1419step0 raw1419step0Labels := by
      have ha : raw1419step0 = (fun i j => raw1419 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1419step0 raw1419; decide +kernel
      have hl : raw1419step0Labels = raw1419Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1419 raw1419Labels permutation32 permutation4
    mixedMoment B raw1419step0 raw1419step0Labels = mixedMoment B raw1419step1 raw1419step1Labels := by
      have ha : raw1419step1 = raw1419step0 := by apply Matrix.ext; unfold raw1419step1 raw1419step0; decide +kernel
      have hl : raw1419step0Labels = labelEmbedding7 ∘ raw1419step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1419step0 raw1419step0Labels raw1419step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4586 node4586Labels := by rfl

theorem canonical1420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1420 raw1420Labels = mixedMoment B node1205 node1205Labels := by
  calc
    mixedMoment B raw1420 raw1420Labels = mixedMoment B raw1420step0 raw1420step0Labels := by
      have ha : raw1420step0 = (fun i j => raw1420 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1420step0 raw1420; decide +kernel
      have hl : raw1420step0Labels = raw1420Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1420 raw1420Labels permutation32 permutation4
    _ = mixedMoment B node1205 node1205Labels := by rfl

theorem canonical1421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1421 raw1421Labels = mixedMoment B node3284 node3284Labels := by
  calc
    mixedMoment B raw1421 raw1421Labels = mixedMoment B raw1421step0 raw1421step0Labels := by
      have ha : raw1421step0 = (fun i j => raw1421 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1421step0 raw1421; decide +kernel
      have hl : raw1421step0Labels = raw1421Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1421 raw1421Labels permutation32 permutation6
    mixedMoment B raw1421step0 raw1421step0Labels = mixedMoment B raw1421step1 raw1421step1Labels := by
      have ha : raw1421step1 = -raw1421step0 := by apply Matrix.ext; change ∀ i j, raw1421step1 i j = -(raw1421step0 i j); unfold raw1421step1 raw1421step0; decide +kernel
      have hl : raw1421step1Labels = raw1421step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1421step1 raw1421step1Labels = mixedMoment B raw1421step2 raw1421step2Labels := by
      have ha : raw1421step2 = raw1421step1 := by apply Matrix.ext; unfold raw1421step2 raw1421step1; decide +kernel
      have hl : raw1421step1Labels = labelEmbedding1 ∘ raw1421step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1421step1 raw1421step1Labels raw1421step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3284 node3284Labels := by rfl

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

theorem canonical1833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1833 raw1833Labels = mixedMoment B node4902 node4902Labels := by
  calc
    mixedMoment B raw1833 raw1833Labels = mixedMoment B raw1833step0 raw1833step0Labels := by
      have ha : raw1833step0 = (fun i j => raw1833 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1833step0 raw1833; decide +kernel
      have hl : raw1833step0Labels = raw1833Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1833 raw1833Labels permutation152 permutation4
    mixedMoment B raw1833step0 raw1833step0Labels = mixedMoment B raw1833step1 raw1833step1Labels := by
      have ha : raw1833step1 = raw1833step0 := by apply Matrix.ext; unfold raw1833step1 raw1833step0; decide +kernel
      have hl : raw1833step0Labels = labelEmbedding7 ∘ raw1833step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1833step0 raw1833step0Labels raw1833step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4902 node4902Labels := by rfl

theorem canonical1834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1834 raw1834Labels = mixedMoment B node2295 node2295Labels := by
  calc
    mixedMoment B raw1834 raw1834Labels = mixedMoment B raw1834step0 raw1834step0Labels := by
      have ha : raw1834step0 = (fun i j => raw1834 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1834step0 raw1834; decide +kernel
      have hl : raw1834step0Labels = raw1834Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1834 raw1834Labels permutation152 permutation4
    _ = mixedMoment B node2295 node2295Labels := by rfl

theorem canonical1835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1835 raw1835Labels = mixedMoment B node3315 node3315Labels := by
  calc
    mixedMoment B raw1835 raw1835Labels = mixedMoment B raw1835step0 raw1835step0Labels := by
      have ha : raw1835step0 = (fun i j => raw1835 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1835step0 raw1835; decide +kernel
      have hl : raw1835step0Labels = raw1835Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1835 raw1835Labels permutation158 permutation6
    mixedMoment B raw1835step0 raw1835step0Labels = mixedMoment B raw1835step1 raw1835step1Labels := by
      have ha : raw1835step1 = -raw1835step0 := by apply Matrix.ext; change ∀ i j, raw1835step1 i j = -(raw1835step0 i j); unfold raw1835step1 raw1835step0; decide +kernel
      have hl : raw1835step1Labels = raw1835step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1835step1 raw1835step1Labels = mixedMoment B raw1835step2 raw1835step2Labels := by
      have ha : raw1835step2 = raw1835step1 := by apply Matrix.ext; unfold raw1835step2 raw1835step1; decide +kernel
      have hl : raw1835step1Labels = labelEmbedding1 ∘ raw1835step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1835step1 raw1835step1Labels raw1835step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3315 node3315Labels := by rfl

theorem canonical1848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1848 raw1848Labels = mixedMoment B node4907 node4907Labels := by
  calc
    mixedMoment B raw1848 raw1848Labels = mixedMoment B raw1848step0 raw1848step0Labels := by
      have ha : raw1848step0 = (fun i j => raw1848 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1848step0 raw1848; decide +kernel
      have hl : raw1848step0Labels = raw1848Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1848 raw1848Labels permutation32 permutation4
    mixedMoment B raw1848step0 raw1848step0Labels = mixedMoment B raw1848step1 raw1848step1Labels := by
      have ha : raw1848step1 = raw1848step0 := by apply Matrix.ext; unfold raw1848step1 raw1848step0; decide +kernel
      have hl : raw1848step0Labels = labelEmbedding7 ∘ raw1848step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1848step0 raw1848step0Labels raw1848step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4907 node4907Labels := by rfl

theorem canonical1849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1849 raw1849Labels = mixedMoment B node2300 node2300Labels := by
  calc
    mixedMoment B raw1849 raw1849Labels = mixedMoment B raw1849step0 raw1849step0Labels := by
      have ha : raw1849step0 = (fun i j => raw1849 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1849step0 raw1849; decide +kernel
      have hl : raw1849step0Labels = raw1849Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1849 raw1849Labels permutation32 permutation4
    _ = mixedMoment B node2300 node2300Labels := by rfl

theorem canonical1850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1850 raw1850Labels = mixedMoment B node3325 node3325Labels := by
  calc
    mixedMoment B raw1850 raw1850Labels = mixedMoment B raw1850step0 raw1850step0Labels := by
      have ha : raw1850step0 = (fun i j => raw1850 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1850step0 raw1850; decide +kernel
      have hl : raw1850step0Labels = raw1850Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1850 raw1850Labels permutation32 permutation6
    mixedMoment B raw1850step0 raw1850step0Labels = mixedMoment B raw1850step1 raw1850step1Labels := by
      have ha : raw1850step1 = -raw1850step0 := by apply Matrix.ext; change ∀ i j, raw1850step1 i j = -(raw1850step0 i j); unfold raw1850step1 raw1850step0; decide +kernel
      have hl : raw1850step1Labels = raw1850step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1850step1 raw1850step1Labels = mixedMoment B raw1850step2 raw1850step2Labels := by
      have ha : raw1850step2 = raw1850step1 := by apply Matrix.ext; unfold raw1850step2 raw1850step1; decide +kernel
      have hl : raw1850step1Labels = labelEmbedding1 ∘ raw1850step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1850step1 raw1850step1Labels raw1850step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3325 node3325Labels := by rfl

theorem canonical1887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1887 raw1887Labels = mixedMoment B node4926 node4926Labels := by
  calc
    mixedMoment B raw1887 raw1887Labels = mixedMoment B raw1887step0 raw1887step0Labels := by
      have ha : raw1887step0 = (fun i j => raw1887 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1887step0 raw1887; decide +kernel
      have hl : raw1887step0Labels = raw1887Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1887 raw1887Labels permutation152 permutation4
    mixedMoment B raw1887step0 raw1887step0Labels = mixedMoment B raw1887step1 raw1887step1Labels := by
      have ha : raw1887step1 = raw1887step0 := by apply Matrix.ext; unfold raw1887step1 raw1887step0; decide +kernel
      have hl : raw1887step0Labels = labelEmbedding7 ∘ raw1887step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1887step0 raw1887step0Labels raw1887step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4926 node4926Labels := by rfl

theorem canonical1888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1888 raw1888Labels = mixedMoment B node2316 node2316Labels := by
  calc
    mixedMoment B raw1888 raw1888Labels = mixedMoment B raw1888step0 raw1888step0Labels := by
      have ha : raw1888step0 = (fun i j => raw1888 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1888step0 raw1888; decide +kernel
      have hl : raw1888step0Labels = raw1888Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1888 raw1888Labels permutation152 permutation4
    _ = mixedMoment B node2316 node2316Labels := by rfl

theorem canonical1889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1889 raw1889Labels = mixedMoment B node3398 node3398Labels := by
  calc
    mixedMoment B raw1889 raw1889Labels = mixedMoment B raw1889step0 raw1889step0Labels := by
      have ha : raw1889step0 = (fun i j => raw1889 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1889step0 raw1889; decide +kernel
      have hl : raw1889step0Labels = raw1889Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1889 raw1889Labels permutation152 permutation6
    mixedMoment B raw1889step0 raw1889step0Labels = mixedMoment B raw1889step1 raw1889step1Labels := by
      have ha : raw1889step1 = -raw1889step0 := by apply Matrix.ext; change ∀ i j, raw1889step1 i j = -(raw1889step0 i j); unfold raw1889step1 raw1889step0; decide +kernel
      have hl : raw1889step1Labels = raw1889step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1889step1 raw1889step1Labels = mixedMoment B raw1889step2 raw1889step2Labels := by
      have ha : raw1889step2 = raw1889step1 := by apply Matrix.ext; unfold raw1889step2 raw1889step1; decide +kernel
      have hl : raw1889step1Labels = labelEmbedding1 ∘ raw1889step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1889step1 raw1889step1Labels raw1889step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3398 node3398Labels := by rfl

theorem canonical1899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1899 raw1899Labels = mixedMoment B node4937 node4937Labels := by
  calc
    mixedMoment B raw1899 raw1899Labels = mixedMoment B raw1899step0 raw1899step0Labels := by
      have ha : raw1899step0 = (fun i j => raw1899 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1899step0 raw1899; decide +kernel
      have hl : raw1899step0Labels = raw1899Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1899 raw1899Labels permutation32 permutation4
    mixedMoment B raw1899step0 raw1899step0Labels = mixedMoment B raw1899step1 raw1899step1Labels := by
      have ha : raw1899step1 = raw1899step0 := by apply Matrix.ext; unfold raw1899step1 raw1899step0; decide +kernel
      have hl : raw1899step0Labels = labelEmbedding7 ∘ raw1899step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1899step0 raw1899step0Labels raw1899step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4937 node4937Labels := by rfl

theorem canonical1900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1900 raw1900Labels = mixedMoment B node2329 node2329Labels := by
  calc
    mixedMoment B raw1900 raw1900Labels = mixedMoment B raw1900step0 raw1900step0Labels := by
      have ha : raw1900step0 = (fun i j => raw1900 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1900step0 raw1900; decide +kernel
      have hl : raw1900step0Labels = raw1900Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1900 raw1900Labels permutation32 permutation4
    _ = mixedMoment B node2329 node2329Labels := by rfl

theorem canonical1901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1901 raw1901Labels = mixedMoment B node3402 node3402Labels := by
  calc
    mixedMoment B raw1901 raw1901Labels = mixedMoment B raw1901step0 raw1901step0Labels := by
      have ha : raw1901step0 = (fun i j => raw1901 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1901step0 raw1901; decide +kernel
      have hl : raw1901step0Labels = raw1901Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1901 raw1901Labels permutation32 permutation6
    mixedMoment B raw1901step0 raw1901step0Labels = mixedMoment B raw1901step1 raw1901step1Labels := by
      have ha : raw1901step1 = -raw1901step0 := by apply Matrix.ext; change ∀ i j, raw1901step1 i j = -(raw1901step0 i j); unfold raw1901step1 raw1901step0; decide +kernel
      have hl : raw1901step1Labels = raw1901step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1901step1 raw1901step1Labels = mixedMoment B raw1901step2 raw1901step2Labels := by
      have ha : raw1901step2 = raw1901step1 := by apply Matrix.ext; unfold raw1901step2 raw1901step1; decide +kernel
      have hl : raw1901step1Labels = labelEmbedding1 ∘ raw1901step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1901step1 raw1901step1Labels raw1901step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3402 node3402Labels := by rfl

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

theorem canonical2013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2013 raw2013Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw2013 raw2013Labels = mixedMoment B raw2013step0 raw2013step0Labels := by
      have ha : raw2013step0 = (fun i j => raw2013 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2013step0 raw2013; decide +kernel
      have hl : raw2013step0Labels = raw2013Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2013 raw2013Labels permutation32 permutation4
    mixedMoment B raw2013step0 raw2013step0Labels = mixedMoment B raw2013step1 raw2013step1Labels := by
      have ha : raw2013step1 = raw2013step0 := by apply Matrix.ext; unfold raw2013step1 raw2013step0; decide +kernel
      have hl : raw2013step0Labels = labelEmbedding7 ∘ raw2013step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2013step0 raw2013step0Labels raw2013step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

theorem canonical2014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2014 raw2014Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw2014 raw2014Labels = mixedMoment B raw2014step0 raw2014step0Labels := by
      have ha : raw2014step0 = (fun i j => raw2014 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2014step0 raw2014; decide +kernel
      have hl : raw2014step0Labels = raw2014Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2014 raw2014Labels permutation32 permutation4
    _ = mixedMoment B node2385 node2385Labels := by rfl

theorem canonical2015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2015 raw2015Labels = mixedMoment B node3353 node3353Labels := by
  calc
    mixedMoment B raw2015 raw2015Labels = mixedMoment B raw2015step0 raw2015step0Labels := by
      have ha : raw2015step0 = (fun i j => raw2015 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2015step0 raw2015; decide +kernel
      have hl : raw2015step0Labels = raw2015Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2015 raw2015Labels permutation32 permutation6
    mixedMoment B raw2015step0 raw2015step0Labels = mixedMoment B raw2015step1 raw2015step1Labels := by
      have ha : raw2015step1 = -raw2015step0 := by apply Matrix.ext; change ∀ i j, raw2015step1 i j = -(raw2015step0 i j); unfold raw2015step1 raw2015step0; decide +kernel
      have hl : raw2015step1Labels = raw2015step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2015step1 raw2015step1Labels = mixedMoment B raw2015step2 raw2015step2Labels := by
      have ha : raw2015step2 = raw2015step1 := by apply Matrix.ext; unfold raw2015step2 raw2015step1; decide +kernel
      have hl : raw2015step1Labels = labelEmbedding1 ∘ raw2015step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2015step1 raw2015step1Labels raw2015step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3353 node3353Labels := by rfl

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

theorem canonical2049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2049 raw2049Labels = mixedMoment B node5032 node5032Labels := by
  calc
    mixedMoment B raw2049 raw2049Labels = mixedMoment B raw2049step0 raw2049step0Labels := by
      have ha : raw2049step0 = (fun i j => raw2049 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2049step0 raw2049; decide +kernel
      have hl : raw2049step0Labels = raw2049Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2049 raw2049Labels permutation152 permutation4
    mixedMoment B raw2049step0 raw2049step0Labels = mixedMoment B raw2049step1 raw2049step1Labels := by
      have ha : raw2049step1 = raw2049step0 := by apply Matrix.ext; unfold raw2049step1 raw2049step0; decide +kernel
      have hl : raw2049step0Labels = labelEmbedding7 ∘ raw2049step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2049step0 raw2049step0Labels raw2049step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5032 node5032Labels := by rfl

theorem canonical2050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2050 raw2050Labels = mixedMoment B node2424 node2424Labels := by
  calc
    mixedMoment B raw2050 raw2050Labels = mixedMoment B raw2050step0 raw2050step0Labels := by
      have ha : raw2050step0 = (fun i j => raw2050 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2050step0 raw2050; decide +kernel
      have hl : raw2050step0Labels = raw2050Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2050 raw2050Labels permutation152 permutation4
    _ = mixedMoment B node2424 node2424Labels := by rfl

theorem canonical2051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2051 raw2051Labels = mixedMoment B node3440 node3440Labels := by
  calc
    mixedMoment B raw2051 raw2051Labels = mixedMoment B raw2051step0 raw2051step0Labels := by
      have ha : raw2051step0 = (fun i j => raw2051 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2051step0 raw2051; decide +kernel
      have hl : raw2051step0Labels = raw2051Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2051 raw2051Labels permutation158 permutation6
    mixedMoment B raw2051step0 raw2051step0Labels = mixedMoment B raw2051step1 raw2051step1Labels := by
      have ha : raw2051step1 = -raw2051step0 := by apply Matrix.ext; change ∀ i j, raw2051step1 i j = -(raw2051step0 i j); unfold raw2051step1 raw2051step0; decide +kernel
      have hl : raw2051step1Labels = raw2051step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2051step1 raw2051step1Labels = mixedMoment B raw2051step2 raw2051step2Labels := by
      have ha : raw2051step2 = raw2051step1 := by apply Matrix.ext; unfold raw2051step2 raw2051step1; decide +kernel
      have hl : raw2051step1Labels = labelEmbedding1 ∘ raw2051step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2051step1 raw2051step1Labels raw2051step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3440 node3440Labels := by rfl

theorem canonical2082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2082 raw2082Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw2082 raw2082Labels = mixedMoment B raw2082step0 raw2082step0Labels := by
      have ha : raw2082step0 = (fun i j => raw2082 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2082step0 raw2082; decide +kernel
      have hl : raw2082step0Labels = raw2082Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2082 raw2082Labels permutation152 permutation4
    mixedMoment B raw2082step0 raw2082step0Labels = mixedMoment B raw2082step1 raw2082step1Labels := by
      have ha : raw2082step1 = raw2082step0 := by apply Matrix.ext; unfold raw2082step1 raw2082step0; decide +kernel
      have hl : raw2082step0Labels = labelEmbedding7 ∘ raw2082step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2082step0 raw2082step0Labels raw2082step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

theorem canonical2083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2083 raw2083Labels = mixedMoment B node2459 node2459Labels := by
  calc
    mixedMoment B raw2083 raw2083Labels = mixedMoment B raw2083step0 raw2083step0Labels := by
      have ha : raw2083step0 = (fun i j => raw2083 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2083step0 raw2083; decide +kernel
      have hl : raw2083step0Labels = raw2083Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2083 raw2083Labels permutation152 permutation4
    _ = mixedMoment B node2459 node2459Labels := by rfl

theorem canonical2084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2084 raw2084Labels = mixedMoment B node3429 node3429Labels := by
  calc
    mixedMoment B raw2084 raw2084Labels = mixedMoment B raw2084step0 raw2084step0Labels := by
      have ha : raw2084step0 = (fun i j => raw2084 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2084step0 raw2084; decide +kernel
      have hl : raw2084step0Labels = raw2084Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2084 raw2084Labels permutation152 permutation6
    mixedMoment B raw2084step0 raw2084step0Labels = mixedMoment B raw2084step1 raw2084step1Labels := by
      have ha : raw2084step1 = -raw2084step0 := by apply Matrix.ext; change ∀ i j, raw2084step1 i j = -(raw2084step0 i j); unfold raw2084step1 raw2084step0; decide +kernel
      have hl : raw2084step1Labels = raw2084step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2084step1 raw2084step1Labels = mixedMoment B raw2084step2 raw2084step2Labels := by
      have ha : raw2084step2 = raw2084step1 := by apply Matrix.ext; unfold raw2084step2 raw2084step1; decide +kernel
      have hl : raw2084step1Labels = labelEmbedding1 ∘ raw2084step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2084step1 raw2084step1Labels raw2084step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3429 node3429Labels := by rfl

theorem canonical2118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2118 raw2118Labels = mixedMoment B node5095 node5095Labels := by
  calc
    mixedMoment B raw2118 raw2118Labels = mixedMoment B raw2118step0 raw2118step0Labels := by
      have ha : raw2118step0 = (fun i j => raw2118 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2118step0 raw2118; decide +kernel
      have hl : raw2118step0Labels = raw2118Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2118 raw2118Labels permutation32 permutation4
    mixedMoment B raw2118step0 raw2118step0Labels = mixedMoment B raw2118step1 raw2118step1Labels := by
      have ha : raw2118step1 = raw2118step0 := by apply Matrix.ext; unfold raw2118step1 raw2118step0; decide +kernel
      have hl : raw2118step0Labels = labelEmbedding7 ∘ raw2118step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2118step0 raw2118step0Labels raw2118step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5095 node5095Labels := by rfl

theorem canonical2119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2119 raw2119Labels = mixedMoment B node2505 node2505Labels := by
  calc
    mixedMoment B raw2119 raw2119Labels = mixedMoment B raw2119step0 raw2119step0Labels := by
      have ha : raw2119step0 = (fun i j => raw2119 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2119step0 raw2119; decide +kernel
      have hl : raw2119step0Labels = raw2119Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2119 raw2119Labels permutation32 permutation4
    _ = mixedMoment B node2505 node2505Labels := by rfl

theorem canonical2120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2120 raw2120Labels = mixedMoment B node3448 node3448Labels := by
  calc
    mixedMoment B raw2120 raw2120Labels = mixedMoment B raw2120step0 raw2120step0Labels := by
      have ha : raw2120step0 = (fun i j => raw2120 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2120step0 raw2120; decide +kernel
      have hl : raw2120step0Labels = raw2120Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2120 raw2120Labels permutation32 permutation6
    mixedMoment B raw2120step0 raw2120step0Labels = mixedMoment B raw2120step1 raw2120step1Labels := by
      have ha : raw2120step1 = -raw2120step0 := by apply Matrix.ext; change ∀ i j, raw2120step1 i j = -(raw2120step0 i j); unfold raw2120step1 raw2120step0; decide +kernel
      have hl : raw2120step1Labels = raw2120step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2120step1 raw2120step1Labels = mixedMoment B raw2120step2 raw2120step2Labels := by
      have ha : raw2120step2 = raw2120step1 := by apply Matrix.ext; unfold raw2120step2 raw2120step1; decide +kernel
      have hl : raw2120step1Labels = labelEmbedding1 ∘ raw2120step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2120step1 raw2120step1Labels raw2120step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3448 node3448Labels := by rfl

theorem canonical2160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2160 raw2160Labels = mixedMoment B node5126 node5126Labels := by
  calc
    mixedMoment B raw2160 raw2160Labels = mixedMoment B raw2160step0 raw2160step0Labels := by
      have ha : raw2160step0 = (fun i j => raw2160 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2160step0 raw2160; decide +kernel
      have hl : raw2160step0Labels = raw2160Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2160 raw2160Labels permutation152 permutation4
    mixedMoment B raw2160step0 raw2160step0Labels = mixedMoment B raw2160step1 raw2160step1Labels := by
      have ha : raw2160step1 = raw2160step0 := by apply Matrix.ext; unfold raw2160step1 raw2160step0; decide +kernel
      have hl : raw2160step0Labels = labelEmbedding7 ∘ raw2160step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2160step0 raw2160step0Labels raw2160step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5126 node5126Labels := by rfl

theorem canonical2161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2161 raw2161Labels = mixedMoment B node2541 node2541Labels := by
  calc
    mixedMoment B raw2161 raw2161Labels = mixedMoment B raw2161step0 raw2161step0Labels := by
      have ha : raw2161step0 = (fun i j => raw2161 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2161step0 raw2161; decide +kernel
      have hl : raw2161step0Labels = raw2161Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2161 raw2161Labels permutation152 permutation4
    _ = mixedMoment B node2541 node2541Labels := by rfl

theorem canonical2162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2162 raw2162Labels = mixedMoment B node3487 node3487Labels := by
  calc
    mixedMoment B raw2162 raw2162Labels = mixedMoment B raw2162step0 raw2162step0Labels := by
      have ha : raw2162step0 = (fun i j => raw2162 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2162step0 raw2162; decide +kernel
      have hl : raw2162step0Labels = raw2162Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2162 raw2162Labels permutation182 permutation6
    mixedMoment B raw2162step0 raw2162step0Labels = mixedMoment B raw2162step1 raw2162step1Labels := by
      have ha : raw2162step1 = -raw2162step0 := by apply Matrix.ext; change ∀ i j, raw2162step1 i j = -(raw2162step0 i j); unfold raw2162step1 raw2162step0; decide +kernel
      have hl : raw2162step1Labels = raw2162step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2162step1 raw2162step1Labels = mixedMoment B raw2162step2 raw2162step2Labels := by
      have ha : raw2162step2 = raw2162step1 := by apply Matrix.ext; unfold raw2162step2 raw2162step1; decide +kernel
      have hl : raw2162step1Labels = labelEmbedding1 ∘ raw2162step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2162step1 raw2162step1Labels raw2162step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3487 node3487Labels := by rfl

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

theorem canonical2265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2265 raw2265Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw2265 raw2265Labels = mixedMoment B raw2265step0 raw2265step0Labels := by
      have ha : raw2265step0 = (fun i j => raw2265 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2265step0 raw2265; decide +kernel
      have hl : raw2265step0Labels = raw2265Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2265 raw2265Labels permutation32 permutation4
    mixedMoment B raw2265step0 raw2265step0Labels = mixedMoment B raw2265step1 raw2265step1Labels := by
      have ha : raw2265step1 = raw2265step0 := by apply Matrix.ext; unfold raw2265step1 raw2265step0; decide +kernel
      have hl : raw2265step0Labels = labelEmbedding7 ∘ raw2265step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2265step0 raw2265step0Labels raw2265step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

theorem canonical2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2266 raw2266Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw2266 raw2266Labels = mixedMoment B raw2266step0 raw2266step0Labels := by
      have ha : raw2266step0 = (fun i j => raw2266 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2266step0 raw2266; decide +kernel
      have hl : raw2266step0Labels = raw2266Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2266 raw2266Labels permutation32 permutation4
    _ = mixedMoment B node2705 node2705Labels := by rfl

theorem canonical2267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2267 raw2267Labels = mixedMoment B node3498 node3498Labels := by
  calc
    mixedMoment B raw2267 raw2267Labels = mixedMoment B raw2267step0 raw2267step0Labels := by
      have ha : raw2267step0 = (fun i j => raw2267 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2267step0 raw2267; decide +kernel
      have hl : raw2267step0Labels = raw2267Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2267 raw2267Labels permutation32 permutation6
    mixedMoment B raw2267step0 raw2267step0Labels = mixedMoment B raw2267step1 raw2267step1Labels := by
      have ha : raw2267step1 = -raw2267step0 := by apply Matrix.ext; change ∀ i j, raw2267step1 i j = -(raw2267step0 i j); unfold raw2267step1 raw2267step0; decide +kernel
      have hl : raw2267step1Labels = raw2267step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2267step1 raw2267step1Labels = mixedMoment B raw2267step2 raw2267step2Labels := by
      have ha : raw2267step2 = raw2267step1 := by apply Matrix.ext; unfold raw2267step2 raw2267step1; decide +kernel
      have hl : raw2267step1Labels = labelEmbedding1 ∘ raw2267step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2267step1 raw2267step1Labels raw2267step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3498 node3498Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30765 raw30765Labels = mixedMoment B node5327 node5327Labels := by
  calc
    mixedMoment B raw30765 raw30765Labels = mixedMoment B raw30765step0 raw30765step0Labels := by
      have hz : ∀ j, raw30765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30765step0 = (fun i j => raw30765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30765step0 raw30765; decide +kernel
      have hl : raw30765step0Labels = raw30765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30765 raw30765Labels permutation346 hz
    mixedMoment B raw30765step0 raw30765step0Labels = mixedMoment B raw30765step1 raw30765step1Labels := by
      have ha : raw30765step1 = (fun i j => raw30765step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30765step1 raw30765step0; decide +kernel
      have hl : raw30765step1Labels = raw30765step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30765step0 raw30765step0Labels permutation127 permutation2
    mixedMoment B raw30765step1 raw30765step1Labels = mixedMoment B raw30765step2 raw30765step2Labels := by
      have ha : raw30765step2 = -raw30765step1 := by apply Matrix.ext; change ∀ i j, raw30765step2 i j = -(raw30765step1 i j); unfold raw30765step2 raw30765step1; decide +kernel
      have hl : raw30765step2Labels = raw30765step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5327 node5327Labels := by rfl

theorem canonical30766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30766 raw30766Labels = mixedMoment B node5323 node5323Labels := by
  calc
    mixedMoment B raw30766 raw30766Labels = mixedMoment B raw30766step0 raw30766step0Labels := by
      have ha : raw30766step0 = (fun i j => raw30766 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30766step0 raw30766; decide +kernel
      have hl : raw30766step0Labels = raw30766Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30766 raw30766Labels permutation589 permutation2
    mixedMoment B raw30766step0 raw30766step0Labels = mixedMoment B raw30766step1 raw30766step1Labels := by
      have ha : raw30766step1 = -raw30766step0 := by apply Matrix.ext; change ∀ i j, raw30766step1 i j = -(raw30766step0 i j); unfold raw30766step1 raw30766step0; decide +kernel
      have hl : raw30766step1Labels = raw30766step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5323 node5323Labels := by rfl

theorem canonical30767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30767 raw30767Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw30767 raw30767Labels = mixedMoment B raw30767step0 raw30767step0Labels := by
      have hz : ∀ j, raw30767 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30767step0 = (fun i j => raw30767 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30767step0 raw30767; decide +kernel
      have hl : raw30767step0Labels = raw30767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30767 raw30767Labels permutation346 hz
    mixedMoment B raw30767step0 raw30767step0Labels = mixedMoment B raw30767step1 raw30767step1Labels := by
      have hz : ∀ i, raw30767step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw30767step1 = (fun i j => raw30767step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw30767step1 raw30767step0; decide +kernel
      have hl : raw30767step1Labels = (fun j => raw30767step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw30767step0 raw30767step0Labels permutation4 hz
    mixedMoment B raw30767step1 raw30767step1Labels = mixedMoment B raw30767step2 raw30767step2Labels := by
      have ha : raw30767step2 = (fun i j => raw30767step1 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30767step2 raw30767step1; decide +kernel
      have hl : raw30767step2Labels = raw30767step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30767step1 raw30767step1Labels permutation125 permutation0
    mixedMoment B raw30767step2 raw30767step2Labels = mixedMoment B raw30767step3 raw30767step3Labels := by
      have ha : raw30767step3 = -raw30767step2 := by apply Matrix.ext; change ∀ i j, raw30767step3 i j = -(raw30767step2 i j); unfold raw30767step3 raw30767step2; decide +kernel
      have hl : raw30767step3Labels = raw30767step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30767step3 raw30767step3Labels = mixedMoment B raw30767step4 raw30767step4Labels := by
      have ha : raw30767step4 = raw30767step3 := by apply Matrix.ext; unfold raw30767step4 raw30767step3; decide +kernel
      have hl : raw30767step3Labels = labelEmbedding2 ∘ raw30767step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30767step3 raw30767step3Labels raw30767step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical30768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30768 raw30768Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw30768 raw30768Labels = mixedMoment B raw30768step0 raw30768step0Labels := by
      have hz : ∀ j, raw30768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30768step0 = (fun i j => raw30768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30768step0 raw30768; decide +kernel
      have hl : raw30768step0Labels = raw30768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30768 raw30768Labels permutation346 hz
    mixedMoment B raw30768step0 raw30768step0Labels = mixedMoment B raw30768step1 raw30768step1Labels := by
      have ha : raw30768step1 = (fun i j => raw30768step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30768step1 raw30768step0; decide +kernel
      have hl : raw30768step1Labels = raw30768step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30768step0 raw30768step0Labels permutation151 permutation7
    mixedMoment B raw30768step1 raw30768step1Labels = mixedMoment B raw30768step2 raw30768step2Labels := by
      have ha : raw30768step2 = raw30768step1 := by apply Matrix.ext; unfold raw30768step2 raw30768step1; decide +kernel
      have hl : raw30768step1Labels = labelEmbedding10 ∘ raw30768step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30768step1 raw30768step1Labels raw30768step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5367 node5367Labels := by rfl

theorem canonical30769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30769 raw30769Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw30769 raw30769Labels = mixedMoment B raw30769step0 raw30769step0Labels := by
      have hz : ∀ j, raw30769 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30769step0 = (fun i j => raw30769 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30769step0 raw30769; decide +kernel
      have hl : raw30769step0Labels = raw30769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30769 raw30769Labels permutation346 hz
    mixedMoment B raw30769step0 raw30769step0Labels = mixedMoment B raw30769step1 raw30769step1Labels := by
      have ha : raw30769step1 = (fun i j => raw30769step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30769step1 raw30769step0; decide +kernel
      have hl : raw30769step1Labels = raw30769step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30769step0 raw30769step0Labels permutation127 permutation7
    mixedMoment B raw30769step1 raw30769step1Labels = mixedMoment B raw30769step2 raw30769step2Labels := by
      have ha : raw30769step2 = raw30769step1 := by apply Matrix.ext; unfold raw30769step2 raw30769step1; decide +kernel
      have hl : raw30769step1Labels = labelEmbedding10 ∘ raw30769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30769step1 raw30769step1Labels raw30769step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5367 node5367Labels := by rfl

theorem canonical30770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30770 raw30770Labels = mixedMoment B node4586 node4586Labels := by
  calc
    mixedMoment B raw30770 raw30770Labels = mixedMoment B raw30770step0 raw30770step0Labels := by
      have hz : ∀ j, raw30770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30770step0 = (fun i j => raw30770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30770step0 raw30770; decide +kernel
      have hl : raw30770step0Labels = raw30770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30770 raw30770Labels permutation346 hz
    _ = mixedMoment B node4586 node4586Labels := by rfl

theorem canonical30771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30771 raw30771Labels = mixedMoment B node5126 node5126Labels := by
  calc
    mixedMoment B raw30771 raw30771Labels = mixedMoment B raw30771step0 raw30771step0Labels := by
      have ha : raw30771step0 = (fun i j => raw30771 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30771step0 raw30771; decide +kernel
      have hl : raw30771step0Labels = raw30771Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30771 raw30771Labels permutation176 permutation2
    _ = mixedMoment B node5126 node5126Labels := by rfl

theorem canonical30772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30772 raw30772Labels = mixedMoment B node5063 node5063Labels := by
  calc
    mixedMoment B raw30772 raw30772Labels = mixedMoment B raw30772step0 raw30772step0Labels := by
      have hz : ∀ j, raw30772 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30772step0 = (fun i j => raw30772 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30772step0 raw30772; decide +kernel
      have hl : raw30772step0Labels = raw30772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30772 raw30772Labels permutation346 hz
    mixedMoment B raw30772step0 raw30772step0Labels = mixedMoment B raw30772step1 raw30772step1Labels := by
      have ha : raw30772step1 = (fun i j => raw30772step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30772step1 raw30772step0; decide +kernel
      have hl : raw30772step1Labels = raw30772step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30772step0 raw30772step0Labels permutation38 permutation2
    _ = mixedMoment B node5063 node5063Labels := by rfl

theorem canonical30773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30773 raw30773Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw30773 raw30773Labels = mixedMoment B raw30773step0 raw30773step0Labels := by
      have hz : ∀ j, raw30773 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30773step0 = (fun i j => raw30773 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30773step0 raw30773; decide +kernel
      have hl : raw30773step0Labels = raw30773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30773 raw30773Labels permutation346 hz
    _ = mixedMoment B node5248 node5248Labels := by rfl

theorem canonical30774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30774 raw30774Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw30774 raw30774Labels = mixedMoment B raw30774step0 raw30774step0Labels := by
      have hz : ∀ j, raw30774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30774step0 = (fun i j => raw30774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30774step0 raw30774; decide +kernel
      have hl : raw30774step0Labels = raw30774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30774 raw30774Labels permutation346 hz
    mixedMoment B raw30774step0 raw30774step0Labels = mixedMoment B raw30774step1 raw30774step1Labels := by
      have ha : raw30774step1 = (fun i j => raw30774step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30774step1 raw30774step0; decide +kernel
      have hl : raw30774step1Labels = raw30774step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30774step0 raw30774step0Labels permutation33 permutation2
    _ = mixedMoment B node5248 node5248Labels := by rfl

theorem canonical30775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30775 raw30775Labels = mixedMoment B node4522 node4522Labels := by
  calc
    mixedMoment B raw30775 raw30775Labels = mixedMoment B raw30775step0 raw30775step0Labels := by
      have ha : raw30775step0 = (fun i j => raw30775 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30775step0 raw30775; decide +kernel
      have hl : raw30775step0Labels = raw30775Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30775 raw30775Labels permutation158 permutation2
    _ = mixedMoment B node4522 node4522Labels := by rfl

theorem canonical30776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30776 raw30776Labels = mixedMoment B node4926 node4926Labels := by
  calc
    mixedMoment B raw30776 raw30776Labels = mixedMoment B raw30776step0 raw30776step0Labels := by
      have ha : raw30776step0 = (fun i j => raw30776 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30776step0 raw30776; decide +kernel
      have hl : raw30776step0Labels = raw30776Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30776 raw30776Labels permutation158 permutation2
    _ = mixedMoment B node4926 node4926Labels := by rfl

theorem canonical30777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30777 raw30777Labels = mixedMoment B node5025 node5025Labels := by
  calc
    mixedMoment B raw30777 raw30777Labels = mixedMoment B raw30777step0 raw30777step0Labels := by
      have ha : raw30777step0 = (fun i j => raw30777 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30777step0 raw30777; decide +kernel
      have hl : raw30777step0Labels = raw30777Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30777 raw30777Labels permutation158 permutation2
    _ = mixedMoment B node5025 node5025Labels := by rfl

theorem canonical30778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30778 raw30778Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw30778 raw30778Labels = mixedMoment B raw30778step0 raw30778step0Labels := by
      have ha : raw30778step0 = (fun i j => raw30778 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30778step0 raw30778; decide +kernel
      have hl : raw30778step0Labels = raw30778Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30778 raw30778Labels permutation158 permutation2
    _ = mixedMoment B node5056 node5056Labels := by rfl

theorem canonical30779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30779 raw30779Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw30779 raw30779Labels = mixedMoment B raw30779step0 raw30779step0Labels := by
      have ha : raw30779step0 = (fun i j => raw30779 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30779step0 raw30779; decide +kernel
      have hl : raw30779step0Labels = raw30779Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30779 raw30779Labels permutation159 permutation2
    _ = mixedMoment B node5056 node5056Labels := by rfl

theorem canonical30780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30780 raw30780Labels = mixedMoment B node4539 node4539Labels := by
  calc
    mixedMoment B raw30780 raw30780Labels = mixedMoment B raw30780step0 raw30780step0Labels := by
      have hz : ∀ j, raw30780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30780step0 = (fun i j => raw30780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30780step0 raw30780; decide +kernel
      have hl : raw30780step0Labels = raw30780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30780 raw30780Labels permutation346 hz
    _ = mixedMoment B node4539 node4539Labels := by rfl

theorem canonical30781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30781 raw30781Labels = mixedMoment B node4937 node4937Labels := by
  calc
    mixedMoment B raw30781 raw30781Labels = mixedMoment B raw30781step0 raw30781step0Labels := by
      have hz : ∀ j, raw30781 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30781step0 = (fun i j => raw30781 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30781step0 raw30781; decide +kernel
      have hl : raw30781step0Labels = raw30781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30781 raw30781Labels permutation346 hz
    _ = mixedMoment B node4937 node4937Labels := by rfl

theorem canonical30782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30782 raw30782Labels = mixedMoment B node5032 node5032Labels := by
  calc
    _ = mixedMoment B node5032 node5032Labels := by rfl

theorem canonical30783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30783 raw30783Labels = mixedMoment B node5095 node5095Labels := by
  calc
    mixedMoment B raw30783 raw30783Labels = mixedMoment B raw30783step0 raw30783step0Labels := by
      have hz : ∀ j, raw30783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30783step0 = (fun i j => raw30783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30783step0 raw30783; decide +kernel
      have hl : raw30783step0Labels = raw30783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30783 raw30783Labels permutation346 hz
    _ = mixedMoment B node5095 node5095Labels := by rfl

theorem canonical30784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30784 raw30784Labels = mixedMoment B node5095 node5095Labels := by
  calc
    mixedMoment B raw30784 raw30784Labels = mixedMoment B raw30784step0 raw30784step0Labels := by
      have hz : ∀ j, raw30784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30784step0 = (fun i j => raw30784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30784step0 raw30784; decide +kernel
      have hl : raw30784step0Labels = raw30784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30784 raw30784Labels permutation346 hz
    mixedMoment B raw30784step0 raw30784step0Labels = mixedMoment B raw30784step1 raw30784step1Labels := by
      have ha : raw30784step1 = (fun i j => raw30784step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30784step1 raw30784step0; decide +kernel
      have hl : raw30784step1Labels = raw30784step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30784step0 raw30784step0Labels permutation33 permutation2
    _ = mixedMoment B node5095 node5095Labels := by rfl

theorem canonical30785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30785 raw30785Labels = mixedMoment B node4526 node4526Labels := by
  calc
    mixedMoment B raw30785 raw30785Labels = mixedMoment B raw30785step0 raw30785step0Labels := by
      have hz : ∀ j, raw30785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30785step0 = (fun i j => raw30785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30785step0 raw30785; decide +kernel
      have hl : raw30785step0Labels = raw30785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30785 raw30785Labels permutation346 hz
    mixedMoment B raw30785step0 raw30785step0Labels = mixedMoment B raw30785step1 raw30785step1Labels := by
      have ha : raw30785step1 = (fun i j => raw30785step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30785step1 raw30785step0; decide +kernel
      have hl : raw30785step1Labels = raw30785step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30785step0 raw30785step0Labels permutation33 permutation2
    _ = mixedMoment B node4526 node4526Labels := by rfl

theorem canonical30786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30786 raw30786Labels = mixedMoment B node4907 node4907Labels := by
  calc
    mixedMoment B raw30786 raw30786Labels = mixedMoment B raw30786step0 raw30786step0Labels := by
      have hz : ∀ j, raw30786 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30786step0 = (fun i j => raw30786 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30786step0 raw30786; decide +kernel
      have hl : raw30786step0Labels = raw30786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30786 raw30786Labels permutation346 hz
    mixedMoment B raw30786step0 raw30786step0Labels = mixedMoment B raw30786step1 raw30786step1Labels := by
      have ha : raw30786step1 = (fun i j => raw30786step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30786step1 raw30786step0; decide +kernel
      have hl : raw30786step1Labels = raw30786step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30786step0 raw30786step0Labels permutation127 permutation2
    mixedMoment B raw30786step1 raw30786step1Labels = mixedMoment B raw30786step2 raw30786step2Labels := by
      have ha : raw30786step2 = -raw30786step1 := by apply Matrix.ext; change ∀ i j, raw30786step2 i j = -(raw30786step1 i j); unfold raw30786step2 raw30786step1; decide +kernel
      have hl : raw30786step2Labels = raw30786step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4907 node4907Labels := by rfl

theorem canonical30787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30787 raw30787Labels = mixedMoment B node4902 node4902Labels := by
  calc
    mixedMoment B raw30787 raw30787Labels = mixedMoment B raw30787step0 raw30787step0Labels := by
      have ha : raw30787step0 = (fun i j => raw30787 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30787step0 raw30787; decide +kernel
      have hl : raw30787step0Labels = raw30787Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30787 raw30787Labels permutation589 permutation2
    mixedMoment B raw30787step0 raw30787step0Labels = mixedMoment B raw30787step1 raw30787step1Labels := by
      have ha : raw30787step1 = -raw30787step0 := by apply Matrix.ext; change ∀ i j, raw30787step1 i j = -(raw30787step0 i j); unfold raw30787step1 raw30787step0; decide +kernel
      have hl : raw30787step1Labels = raw30787step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4902 node4902Labels := by rfl

theorem canonical30788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30788 raw30788Labels = mixedMoment B node4918 node4918Labels := by
  calc
    mixedMoment B raw30788 raw30788Labels = mixedMoment B raw30788step0 raw30788step0Labels := by
      have hz : ∀ j, raw30788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30788step0 = (fun i j => raw30788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30788step0 raw30788; decide +kernel
      have hl : raw30788step0Labels = raw30788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30788 raw30788Labels permutation346 hz
    mixedMoment B raw30788step0 raw30788step0Labels = mixedMoment B raw30788step1 raw30788step1Labels := by
      have ha : raw30788step1 = (fun i j => raw30788step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30788step1 raw30788step0; decide +kernel
      have hl : raw30788step1Labels = raw30788step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30788step0 raw30788step0Labels permutation125 permutation2
    mixedMoment B raw30788step1 raw30788step1Labels = mixedMoment B raw30788step2 raw30788step2Labels := by
      have ha : raw30788step2 = -raw30788step1 := by apply Matrix.ext; change ∀ i j, raw30788step2 i j = -(raw30788step1 i j); unfold raw30788step2 raw30788step1; decide +kernel
      have hl : raw30788step2Labels = raw30788step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4918 node4918Labels := by rfl

theorem canonical30789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30789 raw30789Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw30789 raw30789Labels = mixedMoment B raw30789step0 raw30789step0Labels := by
      have hz : ∀ j, raw30789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30789step0 = (fun i j => raw30789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30789step0 raw30789; decide +kernel
      have hl : raw30789step0Labels = raw30789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30789 raw30789Labels permutation346 hz
    mixedMoment B raw30789step0 raw30789step0Labels = mixedMoment B raw30789step1 raw30789step1Labels := by
      have ha : raw30789step1 = (fun i j => raw30789step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30789step1 raw30789step0; decide +kernel
      have hl : raw30789step1Labels = raw30789step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30789step0 raw30789step0Labels permutation127 permutation2
    mixedMoment B raw30789step1 raw30789step1Labels = mixedMoment B raw30789step2 raw30789step2Labels := by
      have ha : raw30789step2 = -raw30789step1 := by apply Matrix.ext; change ∀ i j, raw30789step2 i j = -(raw30789step1 i j); unfold raw30789step2 raw30789step1; decide +kernel
      have hl : raw30789step2Labels = raw30789step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5000 node5000Labels := by rfl

theorem canonical30790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30790 raw30790Labels = mixedMoment B node4526 node4526Labels := by
  calc
    mixedMoment B raw30790 raw30790Labels = mixedMoment B raw30790step0 raw30790step0Labels := by
      have hz : ∀ j, raw30790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30790step0 = (fun i j => raw30790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30790step0 raw30790; decide +kernel
      have hl : raw30790step0Labels = raw30790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30790 raw30790Labels permutation346 hz
    _ = mixedMoment B node4526 node4526Labels := by rfl

theorem canonical30791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30791 raw30791Labels = mixedMoment B node4907 node4907Labels := by
  calc
    mixedMoment B raw30791 raw30791Labels = mixedMoment B raw30791step0 raw30791step0Labels := by
      have hz : ∀ j, raw30791 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30791step0 = (fun i j => raw30791 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30791step0 raw30791; decide +kernel
      have hl : raw30791step0Labels = raw30791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30791 raw30791Labels permutation346 hz
    mixedMoment B raw30791step0 raw30791step0Labels = mixedMoment B raw30791step1 raw30791step1Labels := by
      have ha : raw30791step1 = (fun i j => raw30791step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30791step1 raw30791step0; decide +kernel
      have hl : raw30791step1Labels = raw30791step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30791step0 raw30791step0Labels permutation151 permutation2
    mixedMoment B raw30791step1 raw30791step1Labels = mixedMoment B raw30791step2 raw30791step2Labels := by
      have ha : raw30791step2 = -raw30791step1 := by apply Matrix.ext; change ∀ i j, raw30791step2 i j = -(raw30791step1 i j); unfold raw30791step2 raw30791step1; decide +kernel
      have hl : raw30791step2Labels = raw30791step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4907 node4907Labels := by rfl

theorem canonical30792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30792 raw30792Labels = mixedMoment B node4902 node4902Labels := by
  calc
    mixedMoment B raw30792 raw30792Labels = mixedMoment B raw30792step0 raw30792step0Labels := by
      have ha : raw30792step0 = (fun i j => raw30792 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30792step0 raw30792; decide +kernel
      have hl : raw30792step0Labels = raw30792Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30792 raw30792Labels permutation688 permutation2
    mixedMoment B raw30792step0 raw30792step0Labels = mixedMoment B raw30792step1 raw30792step1Labels := by
      have ha : raw30792step1 = -raw30792step0 := by apply Matrix.ext; change ∀ i j, raw30792step1 i j = -(raw30792step0 i j); unfold raw30792step1 raw30792step0; decide +kernel
      have hl : raw30792step1Labels = raw30792step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4902 node4902Labels := by rfl

theorem canonical30793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30793 raw30793Labels = mixedMoment B node4918 node4918Labels := by
  calc
    mixedMoment B raw30793 raw30793Labels = mixedMoment B raw30793step0 raw30793step0Labels := by
      have hz : ∀ j, raw30793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30793step0 = (fun i j => raw30793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30793step0 raw30793; decide +kernel
      have hl : raw30793step0Labels = raw30793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30793 raw30793Labels permutation346 hz
    mixedMoment B raw30793step0 raw30793step0Labels = mixedMoment B raw30793step1 raw30793step1Labels := by
      have ha : raw30793step1 = (fun i j => raw30793step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30793step1 raw30793step0; decide +kernel
      have hl : raw30793step1Labels = raw30793step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30793step0 raw30793step0Labels permutation149 permutation2
    mixedMoment B raw30793step1 raw30793step1Labels = mixedMoment B raw30793step2 raw30793step2Labels := by
      have ha : raw30793step2 = -raw30793step1 := by apply Matrix.ext; change ∀ i j, raw30793step2 i j = -(raw30793step1 i j); unfold raw30793step2 raw30793step1; decide +kernel
      have hl : raw30793step2Labels = raw30793step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4918 node4918Labels := by rfl

theorem canonical30794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30794 raw30794Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw30794 raw30794Labels = mixedMoment B raw30794step0 raw30794step0Labels := by
      have hz : ∀ j, raw30794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30794step0 = (fun i j => raw30794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30794step0 raw30794; decide +kernel
      have hl : raw30794step0Labels = raw30794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30794 raw30794Labels permutation346 hz
    mixedMoment B raw30794step0 raw30794step0Labels = mixedMoment B raw30794step1 raw30794step1Labels := by
      have ha : raw30794step1 = (fun i j => raw30794step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30794step1 raw30794step0; decide +kernel
      have hl : raw30794step1Labels = raw30794step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30794step0 raw30794step0Labels permutation151 permutation2
    mixedMoment B raw30794step1 raw30794step1Labels = mixedMoment B raw30794step2 raw30794step2Labels := by
      have ha : raw30794step2 = -raw30794step1 := by apply Matrix.ext; change ∀ i j, raw30794step2 i j = -(raw30794step1 i j); unfold raw30794step2 raw30794step1; decide +kernel
      have hl : raw30794step2Labels = raw30794step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5000 node5000Labels := by rfl

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

theorem singleton4522 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4522 node4522Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1106 node1106Labels + mixedMoment B node3249 node3249Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1338 singletonSmall4522
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4522) = raw1338Labels := by decide +kernel
  rw [hl, canonical1338 B hB] at h
  have hc0 : mixedMoment B raw1338 (Fin.cases (0 : Fin 2) singletonSmall4522) =
      mixedMoment B node1106 node1106Labels := by
    have ha : raw1338 = raw1339 := by apply Matrix.ext; unfold raw1338 raw1339; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4522 = raw1339Labels := by decide +kernel
    rw [ha, hj, canonical1339 B hB]
  have hc1 : mixedMoment B raw1338 (Fin.cases (1 : Fin 2) singletonSmall4522) =
      mixedMoment B node3249 node3249Labels := by
    have ha : raw1338 = raw1340 := by apply Matrix.ext; unfold raw1338 raw1340; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4522 = raw1340Labels := by decide +kernel
    rw [ha, hj, canonical1340 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4526 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4526 node4526Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1110 node1110Labels + mixedMoment B node3252 node3252Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1350 singletonSmall4526
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4526) = raw1350Labels := by decide +kernel
  rw [hl, canonical1350 B hB] at h
  have hc0 : mixedMoment B raw1350 (Fin.cases (0 : Fin 2) singletonSmall4526) =
      mixedMoment B node1110 node1110Labels := by
    have ha : raw1350 = raw1351 := by apply Matrix.ext; unfold raw1350 raw1351; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4526 = raw1351Labels := by decide +kernel
    rw [ha, hj, canonical1351 B hB]
  have hc1 : mixedMoment B raw1350 (Fin.cases (1 : Fin 2) singletonSmall4526) =
      mixedMoment B node3252 node3252Labels := by
    have ha : raw1350 = raw1352 := by apply Matrix.ext; unfold raw1350 raw1352; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4526 = raw1352Labels := by decide +kernel
    rw [ha, hj, canonical1352 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4539 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4539 node4539Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1124 node1124Labels + mixedMoment B node3254 node3254Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1359 singletonSmall4539
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4539) = raw1359Labels := by decide +kernel
  rw [hl, canonical1359 B hB] at h
  have hc0 : mixedMoment B raw1359 (Fin.cases (0 : Fin 2) singletonSmall4539) =
      mixedMoment B node1124 node1124Labels := by
    have ha : raw1359 = raw1360 := by apply Matrix.ext; unfold raw1359 raw1360; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4539 = raw1360Labels := by decide +kernel
    rw [ha, hj, canonical1360 B hB]
  have hc1 : mixedMoment B raw1359 (Fin.cases (1 : Fin 2) singletonSmall4539) =
      mixedMoment B node3254 node3254Labels := by
    have ha : raw1359 = raw1361 := by apply Matrix.ext; unfold raw1359 raw1361; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4539 = raw1361Labels := by decide +kernel
    rw [ha, hj, canonical1361 B hB]
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

theorem singleton4586 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4586 node4586Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1205 node1205Labels + mixedMoment B node3284 node3284Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1419 singletonSmall4586
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4586) = raw1419Labels := by decide +kernel
  rw [hl, canonical1419 B hB] at h
  have hc0 : mixedMoment B raw1419 (Fin.cases (0 : Fin 2) singletonSmall4586) =
      mixedMoment B node1205 node1205Labels := by
    have ha : raw1419 = raw1420 := by apply Matrix.ext; unfold raw1419 raw1420; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4586 = raw1420Labels := by decide +kernel
    rw [ha, hj, canonical1420 B hB]
  have hc1 : mixedMoment B raw1419 (Fin.cases (1 : Fin 2) singletonSmall4586) =
      mixedMoment B node3284 node3284Labels := by
    have ha : raw1419 = raw1421 := by apply Matrix.ext; unfold raw1419 raw1421; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4586 = raw1421Labels := by decide +kernel
    rw [ha, hj, canonical1421 B hB]
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

theorem singleton4902 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4902 node4902Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2295 node2295Labels + mixedMoment B node3315 node3315Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1833 singletonSmall4902
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4902) = raw1833Labels := by decide +kernel
  rw [hl, canonical1833 B hB] at h
  have hc0 : mixedMoment B raw1833 (Fin.cases (0 : Fin 2) singletonSmall4902) =
      mixedMoment B node2295 node2295Labels := by
    have ha : raw1833 = raw1834 := by apply Matrix.ext; unfold raw1833 raw1834; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4902 = raw1834Labels := by decide +kernel
    rw [ha, hj, canonical1834 B hB]
  have hc1 : mixedMoment B raw1833 (Fin.cases (1 : Fin 2) singletonSmall4902) =
      mixedMoment B node3315 node3315Labels := by
    have ha : raw1833 = raw1835 := by apply Matrix.ext; unfold raw1833 raw1835; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4902 = raw1835Labels := by decide +kernel
    rw [ha, hj, canonical1835 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4907 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4907 node4907Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2300 node2300Labels + mixedMoment B node3325 node3325Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1848 singletonSmall4907
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4907) = raw1848Labels := by decide +kernel
  rw [hl, canonical1848 B hB] at h
  have hc0 : mixedMoment B raw1848 (Fin.cases (0 : Fin 2) singletonSmall4907) =
      mixedMoment B node2300 node2300Labels := by
    have ha : raw1848 = raw1849 := by apply Matrix.ext; unfold raw1848 raw1849; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4907 = raw1849Labels := by decide +kernel
    rw [ha, hj, canonical1849 B hB]
  have hc1 : mixedMoment B raw1848 (Fin.cases (1 : Fin 2) singletonSmall4907) =
      mixedMoment B node3325 node3325Labels := by
    have ha : raw1848 = raw1850 := by apply Matrix.ext; unfold raw1848 raw1850; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4907 = raw1850Labels := by decide +kernel
    rw [ha, hj, canonical1850 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4926 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4926 node4926Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2316 node2316Labels + mixedMoment B node3398 node3398Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1887 singletonSmall4926
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4926) = raw1887Labels := by decide +kernel
  rw [hl, canonical1887 B hB] at h
  have hc0 : mixedMoment B raw1887 (Fin.cases (0 : Fin 2) singletonSmall4926) =
      mixedMoment B node2316 node2316Labels := by
    have ha : raw1887 = raw1888 := by apply Matrix.ext; unfold raw1887 raw1888; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4926 = raw1888Labels := by decide +kernel
    rw [ha, hj, canonical1888 B hB]
  have hc1 : mixedMoment B raw1887 (Fin.cases (1 : Fin 2) singletonSmall4926) =
      mixedMoment B node3398 node3398Labels := by
    have ha : raw1887 = raw1889 := by apply Matrix.ext; unfold raw1887 raw1889; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4926 = raw1889Labels := by decide +kernel
    rw [ha, hj, canonical1889 B hB]
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

theorem singleton4937 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4937 node4937Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2329 node2329Labels + mixedMoment B node3402 node3402Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1899 singletonSmall4937
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4937) = raw1899Labels := by decide +kernel
  rw [hl, canonical1899 B hB] at h
  have hc0 : mixedMoment B raw1899 (Fin.cases (0 : Fin 2) singletonSmall4937) =
      mixedMoment B node2329 node2329Labels := by
    have ha : raw1899 = raw1900 := by apply Matrix.ext; unfold raw1899 raw1900; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4937 = raw1900Labels := by decide +kernel
    rw [ha, hj, canonical1900 B hB]
  have hc1 : mixedMoment B raw1899 (Fin.cases (1 : Fin 2) singletonSmall4937) =
      mixedMoment B node3402 node3402Labels := by
    have ha : raw1899 = raw1901 := by apply Matrix.ext; unfold raw1899 raw1901; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4937 = raw1901Labels := by decide +kernel
    rw [ha, hj, canonical1901 B hB]
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

theorem singleton5000 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5000 node5000Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2385 node2385Labels + mixedMoment B node3353 node3353Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2013 singletonSmall5000
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5000) = raw2013Labels := by decide +kernel
  rw [hl, canonical2013 B hB] at h
  have hc0 : mixedMoment B raw2013 (Fin.cases (0 : Fin 2) singletonSmall5000) =
      mixedMoment B node2385 node2385Labels := by
    have ha : raw2013 = raw2014 := by apply Matrix.ext; unfold raw2013 raw2014; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5000 = raw2014Labels := by decide +kernel
    rw [ha, hj, canonical2014 B hB]
  have hc1 : mixedMoment B raw2013 (Fin.cases (1 : Fin 2) singletonSmall5000) =
      mixedMoment B node3353 node3353Labels := by
    have ha : raw2013 = raw2015 := by apply Matrix.ext; unfold raw2013 raw2015; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5000 = raw2015Labels := by decide +kernel
    rw [ha, hj, canonical2015 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5032 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5032 node5032Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2424 node2424Labels + mixedMoment B node3440 node3440Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2049 singletonSmall5032
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5032) = raw2049Labels := by decide +kernel
  rw [hl, canonical2049 B hB] at h
  have hc0 : mixedMoment B raw2049 (Fin.cases (0 : Fin 2) singletonSmall5032) =
      mixedMoment B node2424 node2424Labels := by
    have ha : raw2049 = raw2050 := by apply Matrix.ext; unfold raw2049 raw2050; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5032 = raw2050Labels := by decide +kernel
    rw [ha, hj, canonical2050 B hB]
  have hc1 : mixedMoment B raw2049 (Fin.cases (1 : Fin 2) singletonSmall5032) =
      mixedMoment B node3440 node3440Labels := by
    have ha : raw2049 = raw2051 := by apply Matrix.ext; unfold raw2049 raw2051; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5032 = raw2051Labels := by decide +kernel
    rw [ha, hj, canonical2051 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5056 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5056 node5056Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2459 node2459Labels + mixedMoment B node3429 node3429Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2082 singletonSmall5056
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5056) = raw2082Labels := by decide +kernel
  rw [hl, canonical2082 B hB] at h
  have hc0 : mixedMoment B raw2082 (Fin.cases (0 : Fin 2) singletonSmall5056) =
      mixedMoment B node2459 node2459Labels := by
    have ha : raw2082 = raw2083 := by apply Matrix.ext; unfold raw2082 raw2083; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5056 = raw2083Labels := by decide +kernel
    rw [ha, hj, canonical2083 B hB]
  have hc1 : mixedMoment B raw2082 (Fin.cases (1 : Fin 2) singletonSmall5056) =
      mixedMoment B node3429 node3429Labels := by
    have ha : raw2082 = raw2084 := by apply Matrix.ext; unfold raw2082 raw2084; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5056 = raw2084Labels := by decide +kernel
    rw [ha, hj, canonical2084 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5095 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5095 node5095Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2505 node2505Labels + mixedMoment B node3448 node3448Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2118 singletonSmall5095
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5095) = raw2118Labels := by decide +kernel
  rw [hl, canonical2118 B hB] at h
  have hc0 : mixedMoment B raw2118 (Fin.cases (0 : Fin 2) singletonSmall5095) =
      mixedMoment B node2505 node2505Labels := by
    have ha : raw2118 = raw2119 := by apply Matrix.ext; unfold raw2118 raw2119; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5095 = raw2119Labels := by decide +kernel
    rw [ha, hj, canonical2119 B hB]
  have hc1 : mixedMoment B raw2118 (Fin.cases (1 : Fin 2) singletonSmall5095) =
      mixedMoment B node3448 node3448Labels := by
    have ha : raw2118 = raw2120 := by apply Matrix.ext; unfold raw2118 raw2120; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5095 = raw2120Labels := by decide +kernel
    rw [ha, hj, canonical2120 B hB]
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

theorem singleton5126 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5126 node5126Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2541 node2541Labels + mixedMoment B node3487 node3487Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2160 singletonSmall5126
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5126) = raw2160Labels := by decide +kernel
  rw [hl, canonical2160 B hB] at h
  have hc0 : mixedMoment B raw2160 (Fin.cases (0 : Fin 2) singletonSmall5126) =
      mixedMoment B node2541 node2541Labels := by
    have ha : raw2160 = raw2161 := by apply Matrix.ext; unfold raw2160 raw2161; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5126 = raw2161Labels := by decide +kernel
    rw [ha, hj, canonical2161 B hB]
  have hc1 : mixedMoment B raw2160 (Fin.cases (1 : Fin 2) singletonSmall5126) =
      mixedMoment B node3487 node3487Labels := by
    have ha : raw2160 = raw2162 := by apply Matrix.ext; unfold raw2160 raw2162; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5126 = raw2162Labels := by decide +kernel
    rw [ha, hj, canonical2162 B hB]
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

theorem singleton5248 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5248 node5248Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2705 node2705Labels + mixedMoment B node3498 node3498Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2265 singletonSmall5248
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5248) = raw2265Labels := by decide +kernel
  rw [hl, canonical2265 B hB] at h
  have hc0 : mixedMoment B raw2265 (Fin.cases (0 : Fin 2) singletonSmall5248) =
      mixedMoment B node2705 node2705Labels := by
    have ha : raw2265 = raw2266 := by apply Matrix.ext; unfold raw2265 raw2266; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5248 = raw2266Labels := by decide +kernel
    rw [ha, hj, canonical2266 B hB]
  have hc1 : mixedMoment B raw2265 (Fin.cases (1 : Fin 2) singletonSmall5248) =
      mixedMoment B node3498 node3498Labels := by
    have ha : raw2265 = raw2267 := by apply Matrix.ext; unfold raw2265 raw2267; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5248 = raw2267Labels := by decide +kernel
    rw [ha, hj, canonical2267 B hB]
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

theorem sound1106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1106 node1106Labels = Sparse.eval nodeValue1106 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1106) = mixedMoment B node1106 node1106Labels := rfl
  simpa [nodeValue1106, Sparse.eval] using hc.symm

theorem sound1110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1110 node1110Labels = Sparse.eval nodeValue1110 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1110) = mixedMoment B node1110 node1110Labels := rfl
  simpa [nodeValue1110, Sparse.eval] using hc.symm

theorem sound1124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1124 node1124Labels = Sparse.eval nodeValue1124 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1124) = mixedMoment B node1124 node1124Labels := rfl
  simpa [nodeValue1124, Sparse.eval] using hc.symm

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

theorem sound1205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1205 node1205Labels = Sparse.eval nodeValue1205 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1205) = mixedMoment B node1205 node1205Labels := rfl
  simpa [nodeValue1205, Sparse.eval] using hc.symm

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

theorem sound2295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2295 node2295Labels = Sparse.eval nodeValue2295 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2295) = mixedMoment B node2295 node2295Labels := rfl
  simpa [nodeValue2295, Sparse.eval] using hc.symm

theorem sound2300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2300 node2300Labels = Sparse.eval nodeValue2300 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2300) = mixedMoment B node2300 node2300Labels := rfl
  simpa [nodeValue2300, Sparse.eval] using hc.symm

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

theorem sound2316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2316 node2316Labels = Sparse.eval nodeValue2316 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2316) = mixedMoment B node2316 node2316Labels := rfl
  simpa [nodeValue2316, Sparse.eval] using hc.symm

theorem sound2329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2329 node2329Labels = Sparse.eval nodeValue2329 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2329) = mixedMoment B node2329 node2329Labels := rfl
  simpa [nodeValue2329, Sparse.eval] using hc.symm

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

theorem sound2385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2385 node2385Labels = Sparse.eval nodeValue2385 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2385) = mixedMoment B node2385 node2385Labels := rfl
  simpa [nodeValue2385, Sparse.eval] using hc.symm

theorem sound2424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2424 node2424Labels = Sparse.eval nodeValue2424 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2424) = mixedMoment B node2424 node2424Labels := rfl
  simpa [nodeValue2424, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2459 node2459Labels = Sparse.eval nodeValue2459 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2459) = mixedMoment B node2459 node2459Labels := rfl
  simpa [nodeValue2459, Sparse.eval] using hc.symm

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

theorem sound2505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2505 node2505Labels = Sparse.eval nodeValue2505 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2505) = mixedMoment B node2505 node2505Labels := rfl
  simpa [nodeValue2505, Sparse.eval] using hc.symm

theorem sound2541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2541 node2541Labels = Sparse.eval nodeValue2541 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2541) = mixedMoment B node2541 node2541Labels := rfl
  simpa [nodeValue2541, Sparse.eval] using hc.symm

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

theorem sound2705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2705 node2705Labels = Sparse.eval nodeValue2705 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2705) = mixedMoment B node2705 node2705Labels := rfl
  simpa [nodeValue2705, Sparse.eval] using hc.symm

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

theorem sound3249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3249 node3249Labels = Sparse.eval nodeValue3249 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3249) = mixedMoment B node3249 node3249Labels := rfl
  simpa [nodeValue3249, Sparse.eval] using hc.symm

theorem sound3252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3252 node3252Labels = Sparse.eval nodeValue3252 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3252) = mixedMoment B node3252 node3252Labels := rfl
  simpa [nodeValue3252, Sparse.eval] using hc.symm

theorem sound3254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3254 node3254Labels = Sparse.eval nodeValue3254 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3254) = mixedMoment B node3254 node3254Labels := rfl
  simpa [nodeValue3254, Sparse.eval] using hc.symm

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

theorem sound3284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3284 node3284Labels = Sparse.eval nodeValue3284 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3284) = mixedMoment B node3284 node3284Labels := rfl
  simpa [nodeValue3284, Sparse.eval] using hc.symm

theorem sound3315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3315 node3315Labels = Sparse.eval nodeValue3315 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3315) = mixedMoment B node3315 node3315Labels := rfl
  simpa [nodeValue3315, Sparse.eval] using hc.symm

theorem sound3325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3325 node3325Labels = Sparse.eval nodeValue3325 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3325) = mixedMoment B node3325 node3325Labels := rfl
  simpa [nodeValue3325, Sparse.eval] using hc.symm

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

theorem sound3353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3353 node3353Labels = Sparse.eval nodeValue3353 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3353) = mixedMoment B node3353 node3353Labels := rfl
  simpa [nodeValue3353, Sparse.eval] using hc.symm

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

theorem sound3398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3398 node3398Labels = Sparse.eval nodeValue3398 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3398) = mixedMoment B node3398 node3398Labels := rfl
  simpa [nodeValue3398, Sparse.eval] using hc.symm

theorem sound3402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3402 node3402Labels = Sparse.eval nodeValue3402 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3402) = mixedMoment B node3402 node3402Labels := rfl
  simpa [nodeValue3402, Sparse.eval] using hc.symm

theorem sound3429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3429 node3429Labels = Sparse.eval nodeValue3429 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3429) = mixedMoment B node3429 node3429Labels := rfl
  simpa [nodeValue3429, Sparse.eval] using hc.symm

theorem sound3440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3440 node3440Labels = Sparse.eval nodeValue3440 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3440) = mixedMoment B node3440 node3440Labels := rfl
  simpa [nodeValue3440, Sparse.eval] using hc.symm

theorem sound3448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3448 node3448Labels = Sparse.eval nodeValue3448 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3448) = mixedMoment B node3448 node3448Labels := rfl
  simpa [nodeValue3448, Sparse.eval] using hc.symm

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

theorem sound3487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3487 node3487Labels = Sparse.eval nodeValue3487 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3487) = mixedMoment B node3487 node3487Labels := rfl
  simpa [nodeValue3487, Sparse.eval] using hc.symm

theorem sound3498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3498 node3498Labels = Sparse.eval nodeValue3498 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3498) = mixedMoment B node3498 node3498Labels := rfl
  simpa [nodeValue3498, Sparse.eval] using hc.symm

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

theorem sound4088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4088 node4088Labels = Sparse.eval nodeValue4088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4088) = mixedMoment B node4088 node4088Labels := rfl
  simpa [nodeValue4088, Sparse.eval] using hc.symm

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

theorem sound4522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4522 node4522Labels = Sparse.eval nodeValue4522 (mixedVector B) := by
  have h := singleton4522 B _hB
  rw [sound1106 B _hB _hF, sound3249 B _hB _hF] at h
  norm_num [nodeValue4522, nodeValue1106, nodeValue3249, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4526 node4526Labels = Sparse.eval nodeValue4526 (mixedVector B) := by
  have h := singleton4526 B _hB
  rw [sound1110 B _hB _hF, sound3252 B _hB _hF] at h
  norm_num [nodeValue4526, nodeValue1110, nodeValue3252, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4539 node4539Labels = Sparse.eval nodeValue4539 (mixedVector B) := by
  have h := singleton4539 B _hB
  rw [sound1124 B _hB _hF, sound3254 B _hB _hF] at h
  norm_num [nodeValue4539, nodeValue1124, nodeValue3254, Sparse.eval] at h ⊢
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

theorem sound4586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4586 node4586Labels = Sparse.eval nodeValue4586 (mixedVector B) := by
  have h := singleton4586 B _hB
  rw [sound1205 B _hB _hF, sound3284 B _hB _hF] at h
  norm_num [nodeValue4586, nodeValue1205, nodeValue3284, Sparse.eval] at h ⊢
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

theorem zero4918 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4918 node4918Labels = 0 := by
  exact mixedMoment_order_one B hB node4918 node4918Labels 1
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

theorem sound4902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4902 node4902Labels = Sparse.eval nodeValue4902 (mixedVector B) := by
  have h := singleton4902 B _hB
  rw [sound2295 B _hB _hF, sound3315 B _hB _hF] at h
  norm_num [nodeValue4902, nodeValue2295, nodeValue3315, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4907 node4907Labels = Sparse.eval nodeValue4907 (mixedVector B) := by
  have h := singleton4907 B _hB
  rw [sound2300 B _hB _hF, sound3325 B _hB _hF] at h
  norm_num [nodeValue4907, nodeValue2300, nodeValue3325, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4918 node4918Labels = Sparse.eval nodeValue4918 (mixedVector B) := by
  simpa only [nodeValue4918, Sparse.eval_nil] using zero4918 B _hB _hF

theorem sound4926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4926 node4926Labels = Sparse.eval nodeValue4926 (mixedVector B) := by
  have h := singleton4926 B _hB
  rw [sound2316 B _hB _hF, sound3398 B _hB _hF] at h
  norm_num [nodeValue4926, nodeValue2316, nodeValue3398, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4937 node4937Labels = Sparse.eval nodeValue4937 (mixedVector B) := by
  have h := singleton4937 B _hB
  rw [sound2329 B _hB _hF, sound3402 B _hB _hF] at h
  norm_num [nodeValue4937, nodeValue2329, nodeValue3402, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5025 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5025 node5025Labels = 0 := by
  exact mixedMoment_order_one B hB node5025 node5025Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound5000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5000 node5000Labels = Sparse.eval nodeValue5000 (mixedVector B) := by
  have h := singleton5000 B _hB
  rw [sound2385 B _hB _hF, sound3353 B _hB _hF] at h
  norm_num [nodeValue5000, nodeValue2385, nodeValue3353, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5025 node5025Labels = Sparse.eval nodeValue5025 (mixedVector B) := by
  simpa only [nodeValue5025, Sparse.eval_nil] using zero5025 B _hB _hF

theorem sound5032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5032 node5032Labels = Sparse.eval nodeValue5032 (mixedVector B) := by
  have h := singleton5032 B _hB
  rw [sound2424 B _hB _hF, sound3440 B _hB _hF] at h
  norm_num [nodeValue5032, nodeValue2424, nodeValue3440, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5063 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5063 node5063Labels = 0 := by
  exact mixedMoment_order_one B hB node5063 node5063Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5056 node5056Labels = Sparse.eval nodeValue5056 (mixedVector B) := by
  have h := singleton5056 B _hB
  rw [sound2459 B _hB _hF, sound3429 B _hB _hF] at h
  norm_num [nodeValue5056, nodeValue2459, nodeValue3429, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5063 node5063Labels = Sparse.eval nodeValue5063 (mixedVector B) := by
  simpa only [nodeValue5063, Sparse.eval_nil] using zero5063 B _hB _hF

theorem sound5095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5095 node5095Labels = Sparse.eval nodeValue5095 (mixedVector B) := by
  have h := singleton5095 B _hB
  rw [sound2505 B _hB _hF, sound3448 B _hB _hF] at h
  norm_num [nodeValue5095, nodeValue2505, nodeValue3448, Sparse.eval] at h ⊢
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

theorem sound5126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5126 node5126Labels = Sparse.eval nodeValue5126 (mixedVector B) := by
  have h := singleton5126 B _hB
  rw [sound2541 B _hB _hF, sound3487 B _hB _hF] at h
  norm_num [nodeValue5126, nodeValue2541, nodeValue3487, Sparse.eval] at h ⊢
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

theorem sound5248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5248 node5248Labels = Sparse.eval nodeValue5248 (mixedVector B) := by
  have h := singleton5248 B _hB
  rw [sound2705 B _hB _hF, sound3498 B _hB _hF] at h
  norm_num [nodeValue5248, nodeValue2705, nodeValue3498, Sparse.eval] at h ⊢
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

theorem zero5323 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5323 node5323Labels = 0 := by
  exact mixedMoment_order_one B hB node5323 node5323Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5327 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5327 node5327Labels = 0 := by
  exact mixedMoment_order_one B hB node5327 node5327Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero5367 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5367 node5367Labels = 0 := by
  exact mixedMoment_order_one B hB node5367 node5367Labels 1
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

theorem sound5323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5323 node5323Labels = Sparse.eval nodeValue5323 (mixedVector B) := by
  simpa only [nodeValue5323, Sparse.eval_nil] using zero5323 B _hB _hF

theorem sound5327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5327 node5327Labels = Sparse.eval nodeValue5327 (mixedVector B) := by
  simpa only [nodeValue5327, Sparse.eval_nil] using zero5327 B _hB _hF

theorem sound5367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5367 node5367Labels = Sparse.eval nodeValue5367 (mixedVector B) := by
  simpa only [nodeValue5367, Sparse.eval_nil] using zero5367 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources69
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2238 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2238 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2238 + difference 0 1) (sourceB2238 + difference 1 0) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5327) := by
    have ha : (tripleCharges (sourceA2238 + difference 0 1) (sourceB2238 + difference 1 0) sourceC2238) = raw30765 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30765; decide +kernel
    rw [ha]
    exact (canonical30765 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2238 + difference 0 2) (sourceB2238 + difference 2 0) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5323) := by
    have ha : (tripleCharges (sourceA2238 + difference 0 2) (sourceB2238 + difference 2 0) sourceC2238) = raw30766 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30766; decide +kernel
    rw [ha]
    exact (canonical30766 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2238 + difference 0 3) (sourceB2238 + difference 3 0) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2238 + difference 0 3) (sourceB2238 + difference 3 0) sourceC2238) = raw30767 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30767; decide +kernel
    rw [ha]
    exact (canonical30767 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2238 + difference 0 4) (sourceB2238 + difference 4 0) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2238 + difference 0 4) (sourceB2238 + difference 4 0) sourceC2238) = raw30768 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30768; decide +kernel
    rw [ha]
    exact (canonical30768 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2238 + difference 0 5) (sourceB2238 + difference 5 0) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2238 + difference 0 5) (sourceB2238 + difference 5 0) sourceC2238) = raw30769 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30769; decide +kernel
    rw [ha]
    exact (canonical30769 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2238 + difference 1 0) (sourceB2238 + difference 0 1) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4586) := by
    have ha : (tripleCharges (sourceA2238 + difference 1 0) (sourceB2238 + difference 0 1) sourceC2238) = raw30770 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30770; decide +kernel
    rw [ha]
    exact (canonical30770 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2238 + difference 1 2) (sourceB2238 + difference 2 1) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5126) := by
    have ha : (tripleCharges (sourceA2238 + difference 1 2) (sourceB2238 + difference 2 1) sourceC2238) = raw30771 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30771; decide +kernel
    rw [ha]
    exact (canonical30771 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2238 + difference 1 3) (sourceB2238 + difference 3 1) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5063) := by
    have ha : (tripleCharges (sourceA2238 + difference 1 3) (sourceB2238 + difference 3 1) sourceC2238) = raw30772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30772; decide +kernel
    rw [ha]
    exact (canonical30772 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2238 + difference 1 4) (sourceB2238 + difference 4 1) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2238 + difference 1 4) (sourceB2238 + difference 4 1) sourceC2238) = raw30773 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30773; decide +kernel
    rw [ha]
    exact (canonical30773 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2238 + difference 1 5) (sourceB2238 + difference 5 1) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2238 + difference 1 5) (sourceB2238 + difference 5 1) sourceC2238) = raw30774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30774; decide +kernel
    rw [ha]
    exact (canonical30774 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2238 + difference 2 0) (sourceB2238 + difference 0 2) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4522) := by
    have ha : (tripleCharges (sourceA2238 + difference 2 0) (sourceB2238 + difference 0 2) sourceC2238) = raw30775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30775; decide +kernel
    rw [ha]
    exact (canonical30775 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2238 + difference 2 1) (sourceB2238 + difference 1 2) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4926) := by
    have ha : (tripleCharges (sourceA2238 + difference 2 1) (sourceB2238 + difference 1 2) sourceC2238) = raw30776 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30776; decide +kernel
    rw [ha]
    exact (canonical30776 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2238 + difference 2 3) (sourceB2238 + difference 3 2) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5025) := by
    have ha : (tripleCharges (sourceA2238 + difference 2 3) (sourceB2238 + difference 3 2) sourceC2238) = raw30777 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30777; decide +kernel
    rw [ha]
    exact (canonical30777 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2238 + difference 2 4) (sourceB2238 + difference 4 2) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2238 + difference 2 4) (sourceB2238 + difference 4 2) sourceC2238) = raw30778 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30778; decide +kernel
    rw [ha]
    exact (canonical30778 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2238 + difference 2 5) (sourceB2238 + difference 5 2) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2238 + difference 2 5) (sourceB2238 + difference 5 2) sourceC2238) = raw30779 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30779; decide +kernel
    rw [ha]
    exact (canonical30779 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2238 + difference 3 0) (sourceB2238 + difference 0 3) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4539) := by
    have ha : (tripleCharges (sourceA2238 + difference 3 0) (sourceB2238 + difference 0 3) sourceC2238) = raw30780 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30780; decide +kernel
    rw [ha]
    exact (canonical30780 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2238 + difference 3 1) (sourceB2238 + difference 1 3) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4937) := by
    have ha : (tripleCharges (sourceA2238 + difference 3 1) (sourceB2238 + difference 1 3) sourceC2238) = raw30781 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30781; decide +kernel
    rw [ha]
    exact (canonical30781 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2238 + difference 3 2) (sourceB2238 + difference 2 3) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5032) := by
    have ha : (tripleCharges (sourceA2238 + difference 3 2) (sourceB2238 + difference 2 3) sourceC2238) = raw30782 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30782; decide +kernel
    rw [ha]
    exact (canonical30782 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2238 + difference 3 4) (sourceB2238 + difference 4 3) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA2238 + difference 3 4) (sourceB2238 + difference 4 3) sourceC2238) = raw30783 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30783; decide +kernel
    rw [ha]
    exact (canonical30783 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2238 + difference 3 5) (sourceB2238 + difference 5 3) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA2238 + difference 3 5) (sourceB2238 + difference 5 3) sourceC2238) = raw30784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30784; decide +kernel
    rw [ha]
    exact (canonical30784 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2238 + difference 4 0) (sourceB2238 + difference 0 4) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4526) := by
    have ha : (tripleCharges (sourceA2238 + difference 4 0) (sourceB2238 + difference 0 4) sourceC2238) = raw30785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30785; decide +kernel
    rw [ha]
    exact (canonical30785 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2238 + difference 4 1) (sourceB2238 + difference 1 4) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4907) := by
    have ha : (tripleCharges (sourceA2238 + difference 4 1) (sourceB2238 + difference 1 4) sourceC2238) = raw30786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30786; decide +kernel
    rw [ha]
    exact (canonical30786 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2238 + difference 4 2) (sourceB2238 + difference 2 4) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4902) := by
    have ha : (tripleCharges (sourceA2238 + difference 4 2) (sourceB2238 + difference 2 4) sourceC2238) = raw30787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30787; decide +kernel
    rw [ha]
    exact (canonical30787 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2238 + difference 4 3) (sourceB2238 + difference 3 4) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4918) := by
    have ha : (tripleCharges (sourceA2238 + difference 4 3) (sourceB2238 + difference 3 4) sourceC2238) = raw30788 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30788; decide +kernel
    rw [ha]
    exact (canonical30788 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2238 + difference 4 5) (sourceB2238 + difference 5 4) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA2238 + difference 4 5) (sourceB2238 + difference 5 4) sourceC2238) = raw30789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30789; decide +kernel
    rw [ha]
    exact (canonical30789 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2238 + difference 5 0) (sourceB2238 + difference 0 5) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4526) := by
    have ha : (tripleCharges (sourceA2238 + difference 5 0) (sourceB2238 + difference 0 5) sourceC2238) = raw30790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30790; decide +kernel
    rw [ha]
    exact (canonical30790 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2238 + difference 5 1) (sourceB2238 + difference 1 5) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4907) := by
    have ha : (tripleCharges (sourceA2238 + difference 5 1) (sourceB2238 + difference 1 5) sourceC2238) = raw30791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30791; decide +kernel
    rw [ha]
    exact (canonical30791 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2238 + difference 5 2) (sourceB2238 + difference 2 5) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4902) := by
    have ha : (tripleCharges (sourceA2238 + difference 5 2) (sourceB2238 + difference 2 5) sourceC2238) = raw30792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30792; decide +kernel
    rw [ha]
    exact (canonical30792 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2238 + difference 5 3) (sourceB2238 + difference 3 5) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4918) := by
    have ha : (tripleCharges (sourceA2238 + difference 5 3) (sourceB2238 + difference 3 5) sourceC2238) = raw30793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30793; decide +kernel
    rw [ha]
    exact (canonical30793 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2238 + difference 5 4) (sourceB2238 + difference 4 5) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA2238 + difference 5 4) (sourceB2238 + difference 4 5) sourceC2238) = raw30794 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30794; decide +kernel
    rw [ha]
    exact (canonical30794 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2238 sourceB2238 sourceC2238
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2238, Integer.Sparse.eval]
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

theorem reindexCheck1835 : Integer.Sparse.reindex keyMap MixedData.row1835 = numericRow1835 := by decide +kernel

theorem numericCheck1835 (x : Master → ℝ) : Integer.Sparse.eval numericRow1835 x =
    (4 : ℝ) * reducedSource1835 x := by
  norm_num [numericRow1835, reducedSource1835, Integer.Sparse.eval, Sparse.eval, nodeValue4088, nodeValue4522, nodeValue4526, nodeValue4539, nodeValue4586, nodeValue4902, nodeValue4907, nodeValue4918, nodeValue4926, nodeValue4937, nodeValue5000, nodeValue5025, nodeValue5032, nodeValue5056, nodeValue5063, nodeValue5095, nodeValue5126, nodeValue5248, nodeValue5323, nodeValue5327, nodeValue5367]
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

theorem reducedZero1835 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1835 (mixedVector B) = 0 := by
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  have h4522 : mixedVector B (Sum.inr 4522) = Sparse.eval nodeValue4522 (mixedVector B) := by
    change mixedMoment B node4522 node4522Labels = _
    exact sound4522 B hB hF
  have h4526 : mixedVector B (Sum.inr 4526) = Sparse.eval nodeValue4526 (mixedVector B) := by
    change mixedMoment B node4526 node4526Labels = _
    exact sound4526 B hB hF
  have h4539 : mixedVector B (Sum.inr 4539) = Sparse.eval nodeValue4539 (mixedVector B) := by
    change mixedMoment B node4539 node4539Labels = _
    exact sound4539 B hB hF
  have h4586 : mixedVector B (Sum.inr 4586) = Sparse.eval nodeValue4586 (mixedVector B) := by
    change mixedMoment B node4586 node4586Labels = _
    exact sound4586 B hB hF
  have h4902 : mixedVector B (Sum.inr 4902) = Sparse.eval nodeValue4902 (mixedVector B) := by
    change mixedMoment B node4902 node4902Labels = _
    exact sound4902 B hB hF
  have h4907 : mixedVector B (Sum.inr 4907) = Sparse.eval nodeValue4907 (mixedVector B) := by
    change mixedMoment B node4907 node4907Labels = _
    exact sound4907 B hB hF
  have h4918 : mixedVector B (Sum.inr 4918) = Sparse.eval nodeValue4918 (mixedVector B) := by
    change mixedMoment B node4918 node4918Labels = _
    exact sound4918 B hB hF
  have h4926 : mixedVector B (Sum.inr 4926) = Sparse.eval nodeValue4926 (mixedVector B) := by
    change mixedMoment B node4926 node4926Labels = _
    exact sound4926 B hB hF
  have h4937 : mixedVector B (Sum.inr 4937) = Sparse.eval nodeValue4937 (mixedVector B) := by
    change mixedMoment B node4937 node4937Labels = _
    exact sound4937 B hB hF
  have h5000 : mixedVector B (Sum.inr 5000) = Sparse.eval nodeValue5000 (mixedVector B) := by
    change mixedMoment B node5000 node5000Labels = _
    exact sound5000 B hB hF
  have h5025 : mixedVector B (Sum.inr 5025) = Sparse.eval nodeValue5025 (mixedVector B) := by
    change mixedMoment B node5025 node5025Labels = _
    exact sound5025 B hB hF
  have h5032 : mixedVector B (Sum.inr 5032) = Sparse.eval nodeValue5032 (mixedVector B) := by
    change mixedMoment B node5032 node5032Labels = _
    exact sound5032 B hB hF
  have h5056 : mixedVector B (Sum.inr 5056) = Sparse.eval nodeValue5056 (mixedVector B) := by
    change mixedMoment B node5056 node5056Labels = _
    exact sound5056 B hB hF
  have h5063 : mixedVector B (Sum.inr 5063) = Sparse.eval nodeValue5063 (mixedVector B) := by
    change mixedMoment B node5063 node5063Labels = _
    exact sound5063 B hB hF
  have h5095 : mixedVector B (Sum.inr 5095) = Sparse.eval nodeValue5095 (mixedVector B) := by
    change mixedMoment B node5095 node5095Labels = _
    exact sound5095 B hB hF
  have h5126 : mixedVector B (Sum.inr 5126) = Sparse.eval nodeValue5126 (mixedVector B) := by
    change mixedMoment B node5126 node5126Labels = _
    exact sound5126 B hB hF
  have h5248 : mixedVector B (Sum.inr 5248) = Sparse.eval nodeValue5248 (mixedVector B) := by
    change mixedMoment B node5248 node5248Labels = _
    exact sound5248 B hB hF
  have h5323 : mixedVector B (Sum.inr 5323) = Sparse.eval nodeValue5323 (mixedVector B) := by
    change mixedMoment B node5323 node5323Labels = _
    exact sound5323 B hB hF
  have h5327 : mixedVector B (Sum.inr 5327) = Sparse.eval nodeValue5327 (mixedVector B) := by
    change mixedMoment B node5327 node5327Labels = _
    exact sound5327 B hB hF
  have h5367 : mixedVector B (Sum.inr 5367) = Sparse.eval nodeValue5367 (mixedVector B) := by
    change mixedMoment B node5367 node5367Labels = _
    exact sound5367 B hB hF
  simpa only [sourceForm2238, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4088, h4522, h4526, h4539, h4586, h4902, h4907, h4918, h4926, h4937, h5000, h5025, h5032, h5056, h5063, h5095, h5126, h5248, h5323, h5327, h5367, reducedSource1835] using sourceEq2238 B hB

theorem rowSound1835_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1835 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1835, numericCheck1835, reducedZero1835 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835_e_oai
