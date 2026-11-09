-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:32:21.91572+00:00
-- url     : https://prove2.me/submissions/6618c9e2-55bc-4951-9df2-7e9259315dbe

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E187
import Definitions.Def_OAIQ106E097
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E190
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

theorem canonical1380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1380 raw1380Labels = mixedMoment B node4551 node4551Labels := by
  calc
    mixedMoment B raw1380 raw1380Labels = mixedMoment B raw1380step0 raw1380step0Labels := by
      have ha : raw1380step0 = (fun i j => raw1380 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1380step0 raw1380; decide +kernel
      have hl : raw1380step0Labels = raw1380Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1380 raw1380Labels permutation32 permutation4
    mixedMoment B raw1380step0 raw1380step0Labels = mixedMoment B raw1380step1 raw1380step1Labels := by
      have ha : raw1380step1 = raw1380step0 := by apply Matrix.ext; unfold raw1380step1 raw1380step0; decide +kernel
      have hl : raw1380step0Labels = labelEmbedding7 ∘ raw1380step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1380step0 raw1380step0Labels raw1380step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4551 node4551Labels := by rfl

theorem canonical1381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1381 raw1381Labels = mixedMoment B node1136 node1136Labels := by
  calc
    mixedMoment B raw1381 raw1381Labels = mixedMoment B raw1381step0 raw1381step0Labels := by
      have ha : raw1381step0 = (fun i j => raw1381 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1381step0 raw1381; decide +kernel
      have hl : raw1381step0Labels = raw1381Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1381 raw1381Labels permutation32 permutation4
    _ = mixedMoment B node1136 node1136Labels := by rfl

theorem canonical1382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1382 raw1382Labels = mixedMoment B node3273 node3273Labels := by
  calc
    mixedMoment B raw1382 raw1382Labels = mixedMoment B raw1382step0 raw1382step0Labels := by
      have ha : raw1382step0 = (fun i j => raw1382 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1382step0 raw1382; decide +kernel
      have hl : raw1382step0Labels = raw1382Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1382 raw1382Labels permutation32 permutation6
    mixedMoment B raw1382step0 raw1382step0Labels = mixedMoment B raw1382step1 raw1382step1Labels := by
      have ha : raw1382step1 = -raw1382step0 := by apply Matrix.ext; change ∀ i j, raw1382step1 i j = -(raw1382step0 i j); unfold raw1382step1 raw1382step0; decide +kernel
      have hl : raw1382step1Labels = raw1382step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1382step1 raw1382step1Labels = mixedMoment B raw1382step2 raw1382step2Labels := by
      have ha : raw1382step2 = raw1382step1 := by apply Matrix.ext; unfold raw1382step2 raw1382step1; decide +kernel
      have hl : raw1382step1Labels = labelEmbedding1 ∘ raw1382step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1382step1 raw1382step1Labels raw1382step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3273 node3273Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical139
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17850 raw17850Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw17850 raw17850Labels = mixedMoment B raw17850step0 raw17850step0Labels := by
      have hz : ∀ j, raw17850 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17850step0 = (fun i j => raw17850 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17850step0 raw17850; decide +kernel
      have hl : raw17850step0Labels = raw17850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17850 raw17850Labels permutation346 hz
    mixedMoment B raw17850step0 raw17850step0Labels = mixedMoment B raw17850step1 raw17850step1Labels := by
      have ha : raw17850step1 = (fun i j => raw17850step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17850step1 raw17850step0; decide +kernel
      have hl : raw17850step1Labels = raw17850step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17850step0 raw17850step0Labels permutation32 permutation3
    mixedMoment B raw17850step1 raw17850step1Labels = mixedMoment B raw17850step2 raw17850step2Labels := by
      have ha : raw17850step2 = raw17850step1 := by apply Matrix.ext; unfold raw17850step2 raw17850step1; decide +kernel
      have hl : raw17850step1Labels = labelEmbedding6 ∘ raw17850step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17850step1 raw17850step1Labels raw17850step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical17855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17855 raw17855Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw17855 raw17855Labels = mixedMoment B raw17855step0 raw17855step0Labels := by
      have ha : raw17855step0 = (fun i j => raw17855 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17855step0 raw17855; decide +kernel
      have hl : raw17855step0Labels = raw17855Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17855 raw17855Labels permutation160 permutation3
    mixedMoment B raw17855step0 raw17855step0Labels = mixedMoment B raw17855step1 raw17855step1Labels := by
      have ha : raw17855step1 = raw17855step0 := by apply Matrix.ext; unfold raw17855step1 raw17855step0; decide +kernel
      have hl : raw17855step0Labels = labelEmbedding6 ∘ raw17855step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17855step0 raw17855step0Labels raw17855step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

theorem canonical17860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17860 raw17860Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw17860 raw17860Labels = mixedMoment B raw17860step0 raw17860step0Labels := by
      have hz : ∀ j, raw17860 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17860step0 = (fun i j => raw17860 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17860step0 raw17860; decide +kernel
      have hl : raw17860step0Labels = raw17860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17860 raw17860Labels permutation346 hz
    mixedMoment B raw17860step0 raw17860step0Labels = mixedMoment B raw17860step1 raw17860step1Labels := by
      have ha : raw17860step1 = (fun i j => raw17860step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17860step1 raw17860step0; decide +kernel
      have hl : raw17860step1Labels = raw17860step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17860step0 raw17860step0Labels permutation34 permutation3
    mixedMoment B raw17860step1 raw17860step1Labels = mixedMoment B raw17860step2 raw17860step2Labels := by
      have ha : raw17860step2 = raw17860step1 := by apply Matrix.ext; unfold raw17860step2 raw17860step1; decide +kernel
      have hl : raw17860step1Labels = labelEmbedding6 ∘ raw17860step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17860step1 raw17860step1Labels raw17860step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

theorem canonical17865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17865 raw17865Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw17865 raw17865Labels = mixedMoment B raw17865step0 raw17865step0Labels := by
      have hz : ∀ j, raw17865 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17865step0 = (fun i j => raw17865 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17865step0 raw17865; decide +kernel
      have hl : raw17865step0Labels = raw17865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17865 raw17865Labels permutation346 hz
    mixedMoment B raw17865step0 raw17865step0Labels = mixedMoment B raw17865step1 raw17865step1Labels := by
      have ha : raw17865step1 = (fun i j => raw17865step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17865step1 raw17865step0; decide +kernel
      have hl : raw17865step1Labels = raw17865step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17865step0 raw17865step0Labels permutation33 permutation3
    mixedMoment B raw17865step1 raw17865step1Labels = mixedMoment B raw17865step2 raw17865step2Labels := by
      have ha : raw17865step2 = raw17865step1 := by apply Matrix.ext; unfold raw17865step2 raw17865step1; decide +kernel
      have hl : raw17865step1Labels = labelEmbedding6 ∘ raw17865step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17865step1 raw17865step1Labels raw17865step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

theorem canonical17871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17871 raw17871Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw17871 raw17871Labels = mixedMoment B raw17871step0 raw17871step0Labels := by
      have hz : ∀ j, raw17871 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17871step0 = (fun i j => raw17871 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17871step0 raw17871; decide +kernel
      have hl : raw17871step0Labels = raw17871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17871 raw17871Labels permutation346 hz
    mixedMoment B raw17871step0 raw17871step0Labels = mixedMoment B raw17871step1 raw17871step1Labels := by
      have ha : raw17871step1 = (fun i j => raw17871step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17871step1 raw17871step0; decide +kernel
      have hl : raw17871step1Labels = raw17871step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17871step0 raw17871step0Labels permutation150 permutation2
    mixedMoment B raw17871step1 raw17871step1Labels = mixedMoment B raw17871step2 raw17871step2Labels := by
      have ha : raw17871step2 = -raw17871step1 := by apply Matrix.ext; change ∀ i j, raw17871step2 i j = -(raw17871step1 i j); unfold raw17871step2 raw17871step1; decide +kernel
      have hl : raw17871step2Labels = raw17871step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5081 node5081Labels := by rfl

theorem canonical17872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17872 raw17872Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw17872 raw17872Labels = mixedMoment B raw17872step0 raw17872step0Labels := by
      have ha : raw17872step0 = (fun i j => raw17872 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17872step0 raw17872; decide +kernel
      have hl : raw17872step0Labels = raw17872Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17872 raw17872Labels permutation688 permutation2
    mixedMoment B raw17872step0 raw17872step0Labels = mixedMoment B raw17872step1 raw17872step1Labels := by
      have ha : raw17872step1 = -raw17872step0 := by apply Matrix.ext; change ∀ i j, raw17872step1 i j = -(raw17872step0 i j); unfold raw17872step1 raw17872step0; decide +kernel
      have hl : raw17872step1Labels = raw17872step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5073 node5073Labels := by rfl

theorem canonical17873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17873 raw17873Labels = mixedMoment B node5104 node5104Labels := by
  calc
    mixedMoment B raw17873 raw17873Labels = mixedMoment B raw17873step0 raw17873step0Labels := by
      have hz : ∀ j, raw17873 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17873step0 = (fun i j => raw17873 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17873step0 raw17873; decide +kernel
      have hl : raw17873step0Labels = raw17873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17873 raw17873Labels permutation346 hz
    mixedMoment B raw17873step0 raw17873step0Labels = mixedMoment B raw17873step1 raw17873step1Labels := by
      have ha : raw17873step1 = (fun i j => raw17873step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17873step1 raw17873step0; decide +kernel
      have hl : raw17873step1Labels = raw17873step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17873step0 raw17873step0Labels permutation149 permutation2
    mixedMoment B raw17873step1 raw17873step1Labels = mixedMoment B raw17873step2 raw17873step2Labels := by
      have ha : raw17873step2 = -raw17873step1 := by apply Matrix.ext; change ∀ i j, raw17873step2 i j = -(raw17873step1 i j); unfold raw17873step2 raw17873step1; decide +kernel
      have hl : raw17873step2Labels = raw17873step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5104 node5104Labels := by rfl

theorem canonical17874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17874 raw17874Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw17874 raw17874Labels = mixedMoment B raw17874step0 raw17874step0Labels := by
      have hz : ∀ j, raw17874 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17874step0 = (fun i j => raw17874 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17874step0 raw17874; decide +kernel
      have hl : raw17874step0Labels = raw17874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17874 raw17874Labels permutation346 hz
    mixedMoment B raw17874step0 raw17874step0Labels = mixedMoment B raw17874step1 raw17874step1Labels := by
      have ha : raw17874step1 = (fun i j => raw17874step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17874step1 raw17874step0; decide +kernel
      have hl : raw17874step1Labels = raw17874step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17874step0 raw17874step0Labels permutation151 permutation2
    mixedMoment B raw17874step1 raw17874step1Labels = mixedMoment B raw17874step2 raw17874step2Labels := by
      have ha : raw17874step2 = -raw17874step1 := by apply Matrix.ext; change ∀ i j, raw17874step2 i j = -(raw17874step1 i j); unfold raw17874step2 raw17874step1; decide +kernel
      have hl : raw17874step2Labels = raw17874step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5259 node5259Labels := by rfl

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

theorem canonical1917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1917 raw1917Labels = mixedMoment B node4948 node4948Labels := by
  calc
    mixedMoment B raw1917 raw1917Labels = mixedMoment B raw1917step0 raw1917step0Labels := by
      have ha : raw1917step0 = (fun i j => raw1917 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1917step0 raw1917; decide +kernel
      have hl : raw1917step0Labels = raw1917Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1917 raw1917Labels permutation32 permutation4
    mixedMoment B raw1917step0 raw1917step0Labels = mixedMoment B raw1917step1 raw1917step1Labels := by
      have ha : raw1917step1 = raw1917step0 := by apply Matrix.ext; unfold raw1917step1 raw1917step0; decide +kernel
      have hl : raw1917step0Labels = labelEmbedding7 ∘ raw1917step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1917step0 raw1917step0Labels raw1917step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4948 node4948Labels := by rfl

theorem canonical1918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1918 raw1918Labels = mixedMoment B node2339 node2339Labels := by
  calc
    mixedMoment B raw1918 raw1918Labels = mixedMoment B raw1918step0 raw1918step0Labels := by
      have ha : raw1918step0 = (fun i j => raw1918 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1918step0 raw1918; decide +kernel
      have hl : raw1918step0Labels = raw1918Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1918 raw1918Labels permutation32 permutation4
    _ = mixedMoment B node2339 node2339Labels := by rfl

theorem canonical1919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1919 raw1919Labels = mixedMoment B node3420 node3420Labels := by
  calc
    mixedMoment B raw1919 raw1919Labels = mixedMoment B raw1919step0 raw1919step0Labels := by
      have ha : raw1919step0 = (fun i j => raw1919 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1919step0 raw1919; decide +kernel
      have hl : raw1919step0Labels = raw1919Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1919 raw1919Labels permutation32 permutation6
    mixedMoment B raw1919step0 raw1919step0Labels = mixedMoment B raw1919step1 raw1919step1Labels := by
      have ha : raw1919step1 = -raw1919step0 := by apply Matrix.ext; change ∀ i j, raw1919step1 i j = -(raw1919step0 i j); unfold raw1919step1 raw1919step0; decide +kernel
      have hl : raw1919step1Labels = raw1919step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1919step1 raw1919step1Labels = mixedMoment B raw1919step2 raw1919step2Labels := by
      have ha : raw1919step2 = raw1919step1 := by apply Matrix.ext; unfold raw1919step2 raw1919step1; decide +kernel
      have hl : raw1919step1Labels = labelEmbedding1 ∘ raw1919step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1919step1 raw1919step1Labels raw1919step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3420 node3420Labels := by rfl

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

theorem canonical2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2058 raw2058Labels = mixedMoment B node5037 node5037Labels := by
  calc
    mixedMoment B raw2058 raw2058Labels = mixedMoment B raw2058step0 raw2058step0Labels := by
      have ha : raw2058step0 = (fun i j => raw2058 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2058step0 raw2058; decide +kernel
      have hl : raw2058step0Labels = raw2058Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2058 raw2058Labels permutation152 permutation4
    mixedMoment B raw2058step0 raw2058step0Labels = mixedMoment B raw2058step1 raw2058step1Labels := by
      have ha : raw2058step1 = raw2058step0 := by apply Matrix.ext; unfold raw2058step1 raw2058step0; decide +kernel
      have hl : raw2058step0Labels = labelEmbedding7 ∘ raw2058step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2058step0 raw2058step0Labels raw2058step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5037 node5037Labels := by rfl

theorem canonical2059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2059 raw2059Labels = mixedMoment B node2429 node2429Labels := by
  calc
    mixedMoment B raw2059 raw2059Labels = mixedMoment B raw2059step0 raw2059step0Labels := by
      have ha : raw2059step0 = (fun i j => raw2059 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2059step0 raw2059; decide +kernel
      have hl : raw2059step0Labels = raw2059Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2059 raw2059Labels permutation152 permutation4
    _ = mixedMoment B node2429 node2429Labels := by rfl

theorem canonical2060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2060 raw2060Labels = mixedMoment B node3455 node3455Labels := by
  calc
    mixedMoment B raw2060 raw2060Labels = mixedMoment B raw2060step0 raw2060step0Labels := by
      have ha : raw2060step0 = (fun i j => raw2060 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2060step0 raw2060; decide +kernel
      have hl : raw2060step0Labels = raw2060Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2060 raw2060Labels permutation152 permutation6
    mixedMoment B raw2060step0 raw2060step0Labels = mixedMoment B raw2060step1 raw2060step1Labels := by
      have ha : raw2060step1 = -raw2060step0 := by apply Matrix.ext; change ∀ i j, raw2060step1 i j = -(raw2060step0 i j); unfold raw2060step1 raw2060step0; decide +kernel
      have hl : raw2060step1Labels = raw2060step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2060step1 raw2060step1Labels = mixedMoment B raw2060step2 raw2060step2Labels := by
      have ha : raw2060step2 = raw2060step1 := by apply Matrix.ext; unfold raw2060step2 raw2060step1; decide +kernel
      have hl : raw2060step1Labels = labelEmbedding1 ∘ raw2060step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2060step1 raw2060step1Labels raw2060step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3455 node3455Labels := by rfl

theorem canonical2094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2094 raw2094Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw2094 raw2094Labels = mixedMoment B raw2094step0 raw2094step0Labels := by
      have ha : raw2094step0 = (fun i j => raw2094 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2094step0 raw2094; decide +kernel
      have hl : raw2094step0Labels = raw2094Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2094 raw2094Labels permutation152 permutation4
    mixedMoment B raw2094step0 raw2094step0Labels = mixedMoment B raw2094step1 raw2094step1Labels := by
      have ha : raw2094step1 = raw2094step0 := by apply Matrix.ext; unfold raw2094step1 raw2094step0; decide +kernel
      have hl : raw2094step0Labels = labelEmbedding7 ∘ raw2094step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2094step0 raw2094step0Labels raw2094step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

theorem canonical2095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2095 raw2095Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw2095 raw2095Labels = mixedMoment B raw2095step0 raw2095step0Labels := by
      have ha : raw2095step0 = (fun i j => raw2095 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2095step0 raw2095; decide +kernel
      have hl : raw2095step0Labels = raw2095Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2095 raw2095Labels permutation152 permutation4
    _ = mixedMoment B node2480 node2480Labels := by rfl

theorem canonical2096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2096 raw2096Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw2096 raw2096Labels = mixedMoment B raw2096step0 raw2096step0Labels := by
      have ha : raw2096step0 = (fun i j => raw2096 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2096step0 raw2096; decide +kernel
      have hl : raw2096step0Labels = raw2096Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2096 raw2096Labels permutation158 permutation6
    mixedMoment B raw2096step0 raw2096step0Labels = mixedMoment B raw2096step1 raw2096step1Labels := by
      have ha : raw2096step1 = -raw2096step0 := by apply Matrix.ext; change ∀ i j, raw2096step1 i j = -(raw2096step0 i j); unfold raw2096step1 raw2096step0; decide +kernel
      have hl : raw2096step1Labels = raw2096step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2096step1 raw2096step1Labels = mixedMoment B raw2096step2 raw2096step2Labels := by
      have ha : raw2096step2 = raw2096step1 := by apply Matrix.ext; unfold raw2096step2 raw2096step1; decide +kernel
      have hl : raw2096step1Labels = labelEmbedding1 ∘ raw2096step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2096step1 raw2096step1Labels raw2096step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

theorem canonical2103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2103 raw2103Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw2103 raw2103Labels = mixedMoment B raw2103step0 raw2103step0Labels := by
      have ha : raw2103step0 = (fun i j => raw2103 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2103step0 raw2103; decide +kernel
      have hl : raw2103step0Labels = raw2103Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2103 raw2103Labels permutation32 permutation4
    mixedMoment B raw2103step0 raw2103step0Labels = mixedMoment B raw2103step1 raw2103step1Labels := by
      have ha : raw2103step1 = raw2103step0 := by apply Matrix.ext; unfold raw2103step1 raw2103step0; decide +kernel
      have hl : raw2103step0Labels = labelEmbedding7 ∘ raw2103step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2103step0 raw2103step0Labels raw2103step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

theorem canonical2104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2104 raw2104Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw2104 raw2104Labels = mixedMoment B raw2104step0 raw2104step0Labels := by
      have ha : raw2104step0 = (fun i j => raw2104 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2104step0 raw2104; decide +kernel
      have hl : raw2104step0Labels = raw2104Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2104 raw2104Labels permutation32 permutation4
    _ = mixedMoment B node2485 node2485Labels := by rfl

theorem canonical2105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2105 raw2105Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw2105 raw2105Labels = mixedMoment B raw2105step0 raw2105step0Labels := by
      have ha : raw2105step0 = (fun i j => raw2105 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2105step0 raw2105; decide +kernel
      have hl : raw2105step0Labels = raw2105Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2105 raw2105Labels permutation32 permutation6
    mixedMoment B raw2105step0 raw2105step0Labels = mixedMoment B raw2105step1 raw2105step1Labels := by
      have ha : raw2105step1 = -raw2105step0 := by apply Matrix.ext; change ∀ i j, raw2105step1 i j = -(raw2105step0 i j); unfold raw2105step1 raw2105step0; decide +kernel
      have hl : raw2105step1Labels = raw2105step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2105step1 raw2105step1Labels = mixedMoment B raw2105step2 raw2105step2Labels := by
      have ha : raw2105step2 = raw2105step1 := by apply Matrix.ext; unfold raw2105step2 raw2105step1; decide +kernel
      have hl : raw2105step1Labels = labelEmbedding1 ∘ raw2105step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2105step1 raw2105step1Labels raw2105step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

theorem canonical2109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2109 raw2109Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw2109 raw2109Labels = mixedMoment B raw2109step0 raw2109step0Labels := by
      have ha : raw2109step0 = (fun i j => raw2109 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2109step0 raw2109; decide +kernel
      have hl : raw2109step0Labels = raw2109Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2109 raw2109Labels permutation32 permutation4
    mixedMoment B raw2109step0 raw2109step0Labels = mixedMoment B raw2109step1 raw2109step1Labels := by
      have ha : raw2109step1 = raw2109step0 := by apply Matrix.ext; unfold raw2109step1 raw2109step0; decide +kernel
      have hl : raw2109step0Labels = labelEmbedding7 ∘ raw2109step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2109step0 raw2109step0Labels raw2109step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

theorem canonical2110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2110 raw2110Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw2110 raw2110Labels = mixedMoment B raw2110step0 raw2110step0Labels := by
      have ha : raw2110step0 = (fun i j => raw2110 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2110step0 raw2110; decide +kernel
      have hl : raw2110step0Labels = raw2110Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2110 raw2110Labels permutation32 permutation4
    _ = mixedMoment B node2489 node2489Labels := by rfl

theorem canonical2111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2111 raw2111Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw2111 raw2111Labels = mixedMoment B raw2111step0 raw2111step0Labels := by
      have ha : raw2111step0 = (fun i j => raw2111 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2111step0 raw2111; decide +kernel
      have hl : raw2111step0Labels = raw2111Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2111 raw2111Labels permutation32 permutation6
    mixedMoment B raw2111step0 raw2111step0Labels = mixedMoment B raw2111step1 raw2111step1Labels := by
      have ha : raw2111step1 = -raw2111step0 := by apply Matrix.ext; change ∀ i j, raw2111step1 i j = -(raw2111step0 i j); unfold raw2111step1 raw2111step0; decide +kernel
      have hl : raw2111step1Labels = raw2111step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2111step1 raw2111step1Labels = mixedMoment B raw2111step2 raw2111step2Labels := by
      have ha : raw2111step2 = raw2111step1 := by apply Matrix.ext; unfold raw2111step2 raw2111step1; decide +kernel
      have hl : raw2111step1Labels = labelEmbedding1 ∘ raw2111step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2111step1 raw2111step1Labels raw2111step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3482 node3482Labels := by rfl

theorem canonical2175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2175 raw2175Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw2175 raw2175Labels = mixedMoment B raw2175step0 raw2175step0Labels := by
      have ha : raw2175step0 = (fun i j => raw2175 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2175step0 raw2175; decide +kernel
      have hl : raw2175step0Labels = raw2175Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2175 raw2175Labels permutation152 permutation5
    mixedMoment B raw2175step0 raw2175step0Labels = mixedMoment B raw2175step1 raw2175step1Labels := by
      have ha : raw2175step1 = raw2175step0 := by apply Matrix.ext; unfold raw2175step1 raw2175step0; decide +kernel
      have hl : raw2175step0Labels = labelEmbedding8 ∘ raw2175step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2175step0 raw2175step0Labels raw2175step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

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

theorem canonical2176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2176 raw2176Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw2176 raw2176Labels = mixedMoment B raw2176step0 raw2176step0Labels := by
      have ha : raw2176step0 = (fun i j => raw2176 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2176step0 raw2176; decide +kernel
      have hl : raw2176step0Labels = raw2176Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2176 raw2176Labels permutation154 permutation4
    _ = mixedMoment B node2924 node2924Labels := by rfl

theorem canonical2177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2177 raw2177Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw2177 raw2177Labels = mixedMoment B raw2177step0 raw2177step0Labels := by
      have ha : raw2177step0 = (fun i j => raw2177 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2177step0 raw2177; decide +kernel
      have hl : raw2177step0Labels = raw2177Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2177 raw2177Labels permutation162 permutation3
    mixedMoment B raw2177step0 raw2177step0Labels = mixedMoment B raw2177step1 raw2177step1Labels := by
      have ha : raw2177step1 = -raw2177step0 := by apply Matrix.ext; change ∀ i j, raw2177step1 i j = -(raw2177step0 i j); unfold raw2177step1 raw2177step0; decide +kernel
      have hl : raw2177step1Labels = raw2177step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2177step1 raw2177step1Labels = mixedMoment B raw2177step2 raw2177step2Labels := by
      have ha : raw2177step2 = raw2177step1 := by apply Matrix.ext; unfold raw2177step2 raw2177step1; decide +kernel
      have hl : raw2177step1Labels = labelEmbedding1 ∘ raw2177step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2177step1 raw2177step1Labels raw2177step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

theorem canonical2178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2178 raw2178Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw2178 raw2178Labels = mixedMoment B raw2178step0 raw2178step0Labels := by
      have ha : raw2178step0 = (fun i j => raw2178 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2178step0 raw2178; decide +kernel
      have hl : raw2178step0Labels = raw2178Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2178 raw2178Labels permutation32 permutation5
    mixedMoment B raw2178step0 raw2178step0Labels = mixedMoment B raw2178step1 raw2178step1Labels := by
      have ha : raw2178step1 = raw2178step0 := by apply Matrix.ext; unfold raw2178step1 raw2178step0; decide +kernel
      have hl : raw2178step0Labels = labelEmbedding8 ∘ raw2178step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2178step0 raw2178step0Labels raw2178step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

theorem canonical2179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2179 raw2179Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw2179 raw2179Labels = mixedMoment B raw2179step0 raw2179step0Labels := by
      have ha : raw2179step0 = (fun i j => raw2179 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2179step0 raw2179; decide +kernel
      have hl : raw2179step0Labels = raw2179Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2179 raw2179Labels permutation33 permutation4
    _ = mixedMoment B node2931 node2931Labels := by rfl

theorem canonical2180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2180 raw2180Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw2180 raw2180Labels = mixedMoment B raw2180step0 raw2180step0Labels := by
      have ha : raw2180step0 = (fun i j => raw2180 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2180step0 raw2180; decide +kernel
      have hl : raw2180step0Labels = raw2180Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2180 raw2180Labels permutation34 permutation3
    mixedMoment B raw2180step0 raw2180step0Labels = mixedMoment B raw2180step1 raw2180step1Labels := by
      have ha : raw2180step1 = -raw2180step0 := by apply Matrix.ext; change ∀ i j, raw2180step1 i j = -(raw2180step0 i j); unfold raw2180step1 raw2180step0; decide +kernel
      have hl : raw2180step1Labels = raw2180step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2180step1 raw2180step1Labels = mixedMoment B raw2180step2 raw2180step2Labels := by
      have ha : raw2180step2 = raw2180step1 := by apply Matrix.ext; unfold raw2180step2 raw2180step1; decide +kernel
      have hl : raw2180step1Labels = labelEmbedding1 ∘ raw2180step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2180step1 raw2180step1Labels raw2180step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

theorem canonical2202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2202 raw2202Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw2202 raw2202Labels = mixedMoment B raw2202step0 raw2202step0Labels := by
      have ha : raw2202step0 = (fun i j => raw2202 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2202step0 raw2202; decide +kernel
      have hl : raw2202step0Labels = raw2202Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2202 raw2202Labels permutation32 permutation5
    mixedMoment B raw2202step0 raw2202step0Labels = mixedMoment B raw2202step1 raw2202step1Labels := by
      have ha : raw2202step1 = raw2202step0 := by apply Matrix.ext; unfold raw2202step1 raw2202step0; decide +kernel
      have hl : raw2202step0Labels = labelEmbedding8 ∘ raw2202step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2202step0 raw2202step0Labels raw2202step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

theorem canonical2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2203 raw2203Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw2203 raw2203Labels = mixedMoment B raw2203step0 raw2203step0Labels := by
      have ha : raw2203step0 = (fun i j => raw2203 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2203step0 raw2203; decide +kernel
      have hl : raw2203step0Labels = raw2203Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2203 raw2203Labels permutation34 permutation4
    _ = mixedMoment B node2954 node2954Labels := by rfl

theorem canonical2204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2204 raw2204Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw2204 raw2204Labels = mixedMoment B raw2204step0 raw2204step0Labels := by
      have ha : raw2204step0 = (fun i j => raw2204 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2204step0 raw2204; decide +kernel
      have hl : raw2204step0Labels = raw2204Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2204 raw2204Labels permutation33 permutation3
    mixedMoment B raw2204step0 raw2204step0Labels = mixedMoment B raw2204step1 raw2204step1Labels := by
      have ha : raw2204step1 = -raw2204step0 := by apply Matrix.ext; change ∀ i j, raw2204step1 i j = -(raw2204step0 i j); unfold raw2204step1 raw2204step0; decide +kernel
      have hl : raw2204step1Labels = raw2204step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2204step1 raw2204step1Labels = mixedMoment B raw2204step2 raw2204step2Labels := by
      have ha : raw2204step2 = raw2204step1 := by apply Matrix.ext; unfold raw2204step2 raw2204step1; decide +kernel
      have hl : raw2204step1Labels = labelEmbedding1 ∘ raw2204step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2204step1 raw2204step1Labels raw2204step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

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

theorem canonical2289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2289 raw2289Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw2289 raw2289Labels = mixedMoment B raw2289step0 raw2289step0Labels := by
      have ha : raw2289step0 = (fun i j => raw2289 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2289step0 raw2289; decide +kernel
      have hl : raw2289step0Labels = raw2289Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2289 raw2289Labels permutation32 permutation5
    mixedMoment B raw2289step0 raw2289step0Labels = mixedMoment B raw2289step1 raw2289step1Labels := by
      have ha : raw2289step1 = raw2289step0 := by apply Matrix.ext; unfold raw2289step1 raw2289step0; decide +kernel
      have hl : raw2289step0Labels = labelEmbedding8 ∘ raw2289step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2289step0 raw2289step0Labels raw2289step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical2290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2290 raw2290Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw2290 raw2290Labels = mixedMoment B raw2290step0 raw2290step0Labels := by
      have ha : raw2290step0 = (fun i j => raw2290 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2290step0 raw2290; decide +kernel
      have hl : raw2290step0Labels = raw2290Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2290 raw2290Labels permutation32 permutation4
    _ = mixedMoment B node3077 node3077Labels := by rfl

theorem canonical2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2291 raw2291Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw2291 raw2291Labels = mixedMoment B raw2291step0 raw2291step0Labels := by
      have ha : raw2291step0 = (fun i j => raw2291 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2291step0 raw2291; decide +kernel
      have hl : raw2291step0Labels = raw2291Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2291 raw2291Labels permutation48 permutation3
    mixedMoment B raw2291step0 raw2291step0Labels = mixedMoment B raw2291step1 raw2291step1Labels := by
      have ha : raw2291step1 = -raw2291step0 := by apply Matrix.ext; change ∀ i j, raw2291step1 i j = -(raw2291step0 i j); unfold raw2291step1 raw2291step0; decide +kernel
      have hl : raw2291step1Labels = raw2291step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2291step1 raw2291step1Labels = mixedMoment B raw2291step2 raw2291step2Labels := by
      have ha : raw2291step2 = raw2291step1 := by apply Matrix.ext; unfold raw2291step2 raw2291step1; decide +kernel
      have hl : raw2291step1Labels = labelEmbedding1 ∘ raw2291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2291step1 raw2291step1Labels raw2291step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical217
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27862 raw27862Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw27862 raw27862Labels = mixedMoment B raw27862step0 raw27862step0Labels := by
      have hz : ∀ j, raw27862 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27862step0 = (fun i j => raw27862 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27862step0 raw27862; decide +kernel
      have hl : raw27862step0Labels = raw27862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27862 raw27862Labels permutation346 hz
    mixedMoment B raw27862step0 raw27862step0Labels = mixedMoment B raw27862step1 raw27862step1Labels := by
      have ha : raw27862step1 = (fun i j => raw27862step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27862step1 raw27862step0; decide +kernel
      have hl : raw27862step1Labels = raw27862step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27862step0 raw27862step0Labels permutation151 permutation2
    mixedMoment B raw27862step1 raw27862step1Labels = mixedMoment B raw27862step2 raw27862step2Labels := by
      have ha : raw27862step2 = -raw27862step1 := by apply Matrix.ext; change ∀ i j, raw27862step2 i j = -(raw27862step1 i j); unfold raw27862step2 raw27862step1; decide +kernel
      have hl : raw27862step2Labels = raw27862step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5410 node5410Labels := by rfl

theorem canonical27863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27863 raw27863Labels = mixedMoment B node4440 node4440Labels := by
  calc
    mixedMoment B raw27863 raw27863Labels = mixedMoment B raw27863step0 raw27863step0Labels := by
      have hz : ∀ j, raw27863 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27863step0 = (fun i j => raw27863 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27863step0 raw27863; decide +kernel
      have hl : raw27863step0Labels = raw27863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27863 raw27863Labels permutation346 hz
    mixedMoment B raw27863step0 raw27863step0Labels = mixedMoment B raw27863step1 raw27863step1Labels := by
      have ha : raw27863step1 = (fun i j => raw27863step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27863step1 raw27863step0; decide +kernel
      have hl : raw27863step1Labels = raw27863step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27863step0 raw27863step0Labels permutation32 permutation3
    mixedMoment B raw27863step1 raw27863step1Labels = mixedMoment B raw27863step2 raw27863step2Labels := by
      have ha : raw27863step2 = raw27863step1 := by apply Matrix.ext; unfold raw27863step2 raw27863step1; decide +kernel
      have hl : raw27863step1Labels = labelEmbedding6 ∘ raw27863step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27863step1 raw27863step1Labels raw27863step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4440 node4440Labels := by rfl

theorem canonical27864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27864 raw27864Labels = mixedMoment B node5065 node5065Labels := by
  calc
    mixedMoment B raw27864 raw27864Labels = mixedMoment B raw27864step0 raw27864step0Labels := by
      have ha : raw27864step0 = (fun i j => raw27864 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27864step0 raw27864; decide +kernel
      have hl : raw27864step0Labels = raw27864Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27864 raw27864Labels permutation676 permutation2
    mixedMoment B raw27864step0 raw27864step0Labels = mixedMoment B raw27864step1 raw27864step1Labels := by
      have ha : raw27864step1 = -raw27864step0 := by apply Matrix.ext; change ∀ i j, raw27864step1 i j = -(raw27864step0 i j); unfold raw27864step1 raw27864step0; decide +kernel
      have hl : raw27864step1Labels = raw27864step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5065 node5065Labels := by rfl

theorem canonical27865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27865 raw27865Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw27865 raw27865Labels = mixedMoment B raw27865step0 raw27865step0Labels := by
      have hz : ∀ j, raw27865 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27865step0 = (fun i j => raw27865 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27865step0 raw27865; decide +kernel
      have hl : raw27865step0Labels = raw27865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27865 raw27865Labels permutation346 hz
    mixedMoment B raw27865step0 raw27865step0Labels = mixedMoment B raw27865step1 raw27865step1Labels := by
      have ha : raw27865step1 = (fun i j => raw27865step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27865step1 raw27865step0; decide +kernel
      have hl : raw27865step1Labels = raw27865step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27865step0 raw27865step0Labels permutation149 permutation2
    mixedMoment B raw27865step1 raw27865step1Labels = mixedMoment B raw27865step2 raw27865step2Labels := by
      have ha : raw27865step2 = -raw27865step1 := by apply Matrix.ext; change ∀ i j, raw27865step2 i j = -(raw27865step1 i j); unfold raw27865step2 raw27865step1; decide +kernel
      have hl : raw27865step2Labels = raw27865step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5078 node5078Labels := by rfl

theorem canonical27866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27866 raw27866Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw27866 raw27866Labels = mixedMoment B raw27866step0 raw27866step0Labels := by
      have hz : ∀ j, raw27866 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27866step0 = (fun i j => raw27866 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27866step0 raw27866; decide +kernel
      have hl : raw27866step0Labels = raw27866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27866 raw27866Labels permutation346 hz
    mixedMoment B raw27866step0 raw27866step0Labels = mixedMoment B raw27866step1 raw27866step1Labels := by
      have ha : raw27866step1 = (fun i j => raw27866step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27866step1 raw27866step0; decide +kernel
      have hl : raw27866step1Labels = raw27866step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27866step0 raw27866step0Labels permutation149 permutation2
    mixedMoment B raw27866step1 raw27866step1Labels = mixedMoment B raw27866step2 raw27866step2Labels := by
      have ha : raw27866step2 = -raw27866step1 := by apply Matrix.ext; change ∀ i j, raw27866step2 i j = -(raw27866step1 i j); unfold raw27866step2 raw27866step1; decide +kernel
      have hl : raw27866step2Labels = raw27866step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5252 node5252Labels := by rfl

theorem canonical27867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27867 raw27867Labels = mixedMoment B node4327 node4327Labels := by
  calc
    mixedMoment B raw27867 raw27867Labels = mixedMoment B raw27867step0 raw27867step0Labels := by
      have ha : raw27867step0 = (fun i j => raw27867 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27867step0 raw27867; decide +kernel
      have hl : raw27867step0Labels = raw27867Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27867 raw27867Labels permutation160 permutation3
    mixedMoment B raw27867step0 raw27867step0Labels = mixedMoment B raw27867step1 raw27867step1Labels := by
      have ha : raw27867step1 = raw27867step0 := by apply Matrix.ext; unfold raw27867step1 raw27867step0; decide +kernel
      have hl : raw27867step0Labels = labelEmbedding6 ∘ raw27867step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27867step0 raw27867step0Labels raw27867step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4327 node4327Labels := by rfl

theorem canonical27868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27868 raw27868Labels = mixedMoment B node4930 node4930Labels := by
  calc
    mixedMoment B raw27868 raw27868Labels = mixedMoment B raw27868step0 raw27868step0Labels := by
      have ha : raw27868step0 = (fun i j => raw27868 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27868step0 raw27868; decide +kernel
      have hl : raw27868step0Labels = raw27868Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27868 raw27868Labels permutation160 permutation3
    mixedMoment B raw27868step0 raw27868step0Labels = mixedMoment B raw27868step1 raw27868step1Labels := by
      have ha : raw27868step1 = raw27868step0 := by apply Matrix.ext; unfold raw27868step1 raw27868step0; decide +kernel
      have hl : raw27868step0Labels = labelEmbedding6 ∘ raw27868step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27868step0 raw27868step0Labels raw27868step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4930 node4930Labels := by rfl

theorem canonical27869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27869 raw27869Labels = mixedMoment B node5037 node5037Labels := by
  calc
    mixedMoment B raw27869 raw27869Labels = mixedMoment B raw27869step0 raw27869step0Labels := by
      have ha : raw27869step0 = (fun i j => raw27869 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27869step0 raw27869; decide +kernel
      have hl : raw27869step0Labels = raw27869Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27869 raw27869Labels permutation680 permutation2
    mixedMoment B raw27869step0 raw27869step0Labels = mixedMoment B raw27869step1 raw27869step1Labels := by
      have ha : raw27869step1 = -raw27869step0 := by apply Matrix.ext; change ∀ i j, raw27869step1 i j = -(raw27869step0 i j); unfold raw27869step1 raw27869step0; decide +kernel
      have hl : raw27869step1Labels = raw27869step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5037 node5037Labels := by rfl

theorem canonical27870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27870 raw27870Labels = mixedMoment B node5128 node5128Labels := by
  calc
    mixedMoment B raw27870 raw27870Labels = mixedMoment B raw27870step0 raw27870step0Labels := by
      have ha : raw27870step0 = (fun i j => raw27870 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27870step0 raw27870; decide +kernel
      have hl : raw27870step0Labels = raw27870Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27870 raw27870Labels permutation646 permutation2
    mixedMoment B raw27870step0 raw27870step0Labels = mixedMoment B raw27870step1 raw27870step1Labels := by
      have ha : raw27870step1 = -raw27870step0 := by apply Matrix.ext; change ∀ i j, raw27870step1 i j = -(raw27870step0 i j); unfold raw27870step1 raw27870step0; decide +kernel
      have hl : raw27870step1Labels = raw27870step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5128 node5128Labels := by rfl

theorem canonical27871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27871 raw27871Labels = mixedMoment B node4347 node4347Labels := by
  calc
    mixedMoment B raw27871 raw27871Labels = mixedMoment B raw27871step0 raw27871step0Labels := by
      have hz : ∀ j, raw27871 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27871step0 = (fun i j => raw27871 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27871step0 raw27871; decide +kernel
      have hl : raw27871step0Labels = raw27871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27871 raw27871Labels permutation346 hz
    mixedMoment B raw27871step0 raw27871step0Labels = mixedMoment B raw27871step1 raw27871step1Labels := by
      have ha : raw27871step1 = (fun i j => raw27871step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27871step1 raw27871step0; decide +kernel
      have hl : raw27871step1Labels = raw27871step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27871step0 raw27871step0Labels permutation34 permutation3
    mixedMoment B raw27871step1 raw27871step1Labels = mixedMoment B raw27871step2 raw27871step2Labels := by
      have ha : raw27871step2 = raw27871step1 := by apply Matrix.ext; unfold raw27871step2 raw27871step1; decide +kernel
      have hl : raw27871step1Labels = labelEmbedding6 ∘ raw27871step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27871step1 raw27871step1Labels raw27871step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4347 node4347Labels := by rfl

theorem canonical27872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27872 raw27872Labels = mixedMoment B node4944 node4944Labels := by
  calc
    mixedMoment B raw27872 raw27872Labels = mixedMoment B raw27872step0 raw27872step0Labels := by
      have hz : ∀ j, raw27872 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27872step0 = (fun i j => raw27872 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27872step0 raw27872; decide +kernel
      have hl : raw27872step0Labels = raw27872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27872 raw27872Labels permutation346 hz
    mixedMoment B raw27872step0 raw27872step0Labels = mixedMoment B raw27872step1 raw27872step1Labels := by
      have ha : raw27872step1 = (fun i j => raw27872step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27872step1 raw27872step0; decide +kernel
      have hl : raw27872step1Labels = raw27872step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27872step0 raw27872step0Labels permutation34 permutation3
    mixedMoment B raw27872step1 raw27872step1Labels = mixedMoment B raw27872step2 raw27872step2Labels := by
      have ha : raw27872step2 = raw27872step1 := by apply Matrix.ext; unfold raw27872step2 raw27872step1; decide +kernel
      have hl : raw27872step1Labels = labelEmbedding6 ∘ raw27872step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27872step1 raw27872step1Labels raw27872step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4944 node4944Labels := by rfl

theorem canonical27873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27873 raw27873Labels = mixedMoment B node5034 node5034Labels := by
  calc
    mixedMoment B raw27873 raw27873Labels = mixedMoment B raw27873step0 raw27873step0Labels := by
      have ha : raw27873step0 = (fun i j => raw27873 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27873step0 raw27873; decide +kernel
      have hl : raw27873step0Labels = raw27873Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27873 raw27873Labels permutation178 permutation3
    mixedMoment B raw27873step0 raw27873step0Labels = mixedMoment B raw27873step1 raw27873step1Labels := by
      have ha : raw27873step1 = raw27873step0 := by apply Matrix.ext; unfold raw27873step1 raw27873step0; decide +kernel
      have hl : raw27873step0Labels = labelEmbedding6 ∘ raw27873step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27873step0 raw27873step0Labels raw27873step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5034 node5034Labels := by rfl

theorem canonical27874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27874 raw27874Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw27874 raw27874Labels = mixedMoment B raw27874step0 raw27874step0Labels := by
      have hz : ∀ j, raw27874 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27874step0 = (fun i j => raw27874 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27874step0 raw27874; decide +kernel
      have hl : raw27874step0Labels = raw27874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27874 raw27874Labels permutation346 hz
    mixedMoment B raw27874step0 raw27874step0Labels = mixedMoment B raw27874step1 raw27874step1Labels := by
      have ha : raw27874step1 = (fun i j => raw27874step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27874step1 raw27874step0; decide +kernel
      have hl : raw27874step1Labels = raw27874step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27874step0 raw27874step0Labels permutation34 permutation3
    mixedMoment B raw27874step1 raw27874step1Labels = mixedMoment B raw27874step2 raw27874step2Labels := by
      have ha : raw27874step2 = raw27874step1 := by apply Matrix.ext; unfold raw27874step2 raw27874step1; decide +kernel
      have hl : raw27874step1Labels = labelEmbedding6 ∘ raw27874step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27874step1 raw27874step1Labels raw27874step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5139 node5139Labels := by rfl

theorem canonical27875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27875 raw27875Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw27875 raw27875Labels = mixedMoment B raw27875step0 raw27875step0Labels := by
      have hz : ∀ j, raw27875 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27875step0 = (fun i j => raw27875 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27875step0 raw27875; decide +kernel
      have hl : raw27875step0Labels = raw27875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27875 raw27875Labels permutation346 hz
    mixedMoment B raw27875step0 raw27875step0Labels = mixedMoment B raw27875step1 raw27875step1Labels := by
      have ha : raw27875step1 = (fun i j => raw27875step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27875step1 raw27875step0; decide +kernel
      have hl : raw27875step1Labels = raw27875step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27875step0 raw27875step0Labels permutation32 permutation3
    mixedMoment B raw27875step1 raw27875step1Labels = mixedMoment B raw27875step2 raw27875step2Labels := by
      have ha : raw27875step2 = raw27875step1 := by apply Matrix.ext; unfold raw27875step2 raw27875step1; decide +kernel
      have hl : raw27875step1Labels = labelEmbedding6 ∘ raw27875step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27875step1 raw27875step1Labels raw27875step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4335 node4335Labels := by rfl

theorem canonical27876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27876 raw27876Labels = mixedMoment B node4935 node4935Labels := by
  calc
    mixedMoment B raw27876 raw27876Labels = mixedMoment B raw27876step0 raw27876step0Labels := by
      have hz : ∀ j, raw27876 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27876step0 = (fun i j => raw27876 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27876step0 raw27876; decide +kernel
      have hl : raw27876step0Labels = raw27876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27876 raw27876Labels permutation346 hz
    mixedMoment B raw27876step0 raw27876step0Labels = mixedMoment B raw27876step1 raw27876step1Labels := by
      have ha : raw27876step1 = (fun i j => raw27876step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27876step1 raw27876step0; decide +kernel
      have hl : raw27876step1Labels = raw27876step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27876step0 raw27876step0Labels permutation151 permutation2
    mixedMoment B raw27876step1 raw27876step1Labels = mixedMoment B raw27876step2 raw27876step2Labels := by
      have ha : raw27876step2 = -raw27876step1 := by apply Matrix.ext; change ∀ i j, raw27876step2 i j = -(raw27876step1 i j); unfold raw27876step2 raw27876step1; decide +kernel
      have hl : raw27876step2Labels = raw27876step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4935 node4935Labels := by rfl

theorem canonical27877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27877 raw27877Labels = mixedMoment B node4930 node4930Labels := by
  calc
    mixedMoment B raw27877 raw27877Labels = mixedMoment B raw27877step0 raw27877step0Labels := by
      have ha : raw27877step0 = (fun i j => raw27877 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27877step0 raw27877; decide +kernel
      have hl : raw27877step0Labels = raw27877Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27877 raw27877Labels permutation688 permutation2
    mixedMoment B raw27877step0 raw27877step0Labels = mixedMoment B raw27877step1 raw27877step1Labels := by
      have ha : raw27877step1 = -raw27877step0 := by apply Matrix.ext; change ∀ i j, raw27877step1 i j = -(raw27877step0 i j); unfold raw27877step1 raw27877step0; decide +kernel
      have hl : raw27877step1Labels = raw27877step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4930 node4930Labels := by rfl

theorem canonical27878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27878 raw27878Labels = mixedMoment B node4948 node4948Labels := by
  calc
    mixedMoment B raw27878 raw27878Labels = mixedMoment B raw27878step0 raw27878step0Labels := by
      have hz : ∀ j, raw27878 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27878step0 = (fun i j => raw27878 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27878step0 raw27878; decide +kernel
      have hl : raw27878step0Labels = raw27878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27878 raw27878Labels permutation346 hz
    mixedMoment B raw27878step0 raw27878step0Labels = mixedMoment B raw27878step1 raw27878step1Labels := by
      have ha : raw27878step1 = (fun i j => raw27878step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27878step1 raw27878step0; decide +kernel
      have hl : raw27878step1Labels = raw27878step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27878step0 raw27878step0Labels permutation149 permutation2
    mixedMoment B raw27878step1 raw27878step1Labels = mixedMoment B raw27878step2 raw27878step2Labels := by
      have ha : raw27878step2 = -raw27878step1 := by apply Matrix.ext; change ∀ i j, raw27878step2 i j = -(raw27878step1 i j); unfold raw27878step2 raw27878step1; decide +kernel
      have hl : raw27878step2Labels = raw27878step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4948 node4948Labels := by rfl

theorem canonical27879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27879 raw27879Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw27879 raw27879Labels = mixedMoment B raw27879step0 raw27879step0Labels := by
      have hz : ∀ j, raw27879 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27879step0 = (fun i j => raw27879 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27879step0 raw27879; decide +kernel
      have hl : raw27879step0Labels = raw27879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27879 raw27879Labels permutation346 hz
    mixedMoment B raw27879step0 raw27879step0Labels = mixedMoment B raw27879step1 raw27879step1Labels := by
      have ha : raw27879step1 = (fun i j => raw27879step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27879step1 raw27879step0; decide +kernel
      have hl : raw27879step1Labels = raw27879step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27879step0 raw27879step0Labels permutation32 permutation3
    mixedMoment B raw27879step1 raw27879step1Labels = mixedMoment B raw27879step2 raw27879step2Labels := by
      have ha : raw27879step2 = raw27879step1 := by apply Matrix.ext; unfold raw27879step2 raw27879step1; decide +kernel
      have hl : raw27879step1Labels = labelEmbedding6 ∘ raw27879step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27879step1 raw27879step1Labels raw27879step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4330 node4330Labels := by rfl

theorem canonical27880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27880 raw27880Labels = mixedMoment B node4535 node4535Labels := by
  calc
    mixedMoment B raw27880 raw27880Labels = mixedMoment B raw27880step0 raw27880step0Labels := by
      have hz : ∀ j, raw27880 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27880step0 = (fun i j => raw27880 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27880step0 raw27880; decide +kernel
      have hl : raw27880step0Labels = raw27880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27880 raw27880Labels permutation346 hz
    mixedMoment B raw27880step0 raw27880step0Labels = mixedMoment B raw27880step1 raw27880step1Labels := by
      have ha : raw27880step1 = (fun i j => raw27880step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27880step1 raw27880step0; decide +kernel
      have hl : raw27880step1Labels = raw27880step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27880step0 raw27880step0Labels permutation151 permutation2
    mixedMoment B raw27880step1 raw27880step1Labels = mixedMoment B raw27880step2 raw27880step2Labels := by
      have ha : raw27880step2 = -raw27880step1 := by apply Matrix.ext; change ∀ i j, raw27880step2 i j = -(raw27880step1 i j); unfold raw27880step2 raw27880step1; decide +kernel
      have hl : raw27880step2Labels = raw27880step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4535 node4535Labels := by rfl

theorem canonical27881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27881 raw27881Labels = mixedMoment B node4528 node4528Labels := by
  calc
    mixedMoment B raw27881 raw27881Labels = mixedMoment B raw27881step0 raw27881step0Labels := by
      have ha : raw27881step0 = (fun i j => raw27881 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27881step0 raw27881; decide +kernel
      have hl : raw27881step0Labels = raw27881Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27881 raw27881Labels permutation688 permutation2
    mixedMoment B raw27881step0 raw27881step0Labels = mixedMoment B raw27881step1 raw27881step1Labels := by
      have ha : raw27881step1 = -raw27881step0 := by apply Matrix.ext; change ∀ i j, raw27881step1 i j = -(raw27881step0 i j); unfold raw27881step1 raw27881step0; decide +kernel
      have hl : raw27881step1Labels = raw27881step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4528 node4528Labels := by rfl

theorem canonical27882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27882 raw27882Labels = mixedMoment B node4551 node4551Labels := by
  calc
    mixedMoment B raw27882 raw27882Labels = mixedMoment B raw27882step0 raw27882step0Labels := by
      have hz : ∀ j, raw27882 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27882step0 = (fun i j => raw27882 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27882step0 raw27882; decide +kernel
      have hl : raw27882step0Labels = raw27882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27882 raw27882Labels permutation346 hz
    mixedMoment B raw27882step0 raw27882step0Labels = mixedMoment B raw27882step1 raw27882step1Labels := by
      have ha : raw27882step1 = (fun i j => raw27882step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27882step1 raw27882step0; decide +kernel
      have hl : raw27882step1Labels = raw27882step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27882step0 raw27882step0Labels permutation149 permutation2
    mixedMoment B raw27882step1 raw27882step1Labels = mixedMoment B raw27882step2 raw27882step2Labels := by
      have ha : raw27882step2 = -raw27882step1 := by apply Matrix.ext; change ∀ i j, raw27882step2 i j = -(raw27882step1 i j); unfold raw27882step2 raw27882step1; decide +kernel
      have hl : raw27882step2Labels = raw27882step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4551 node4551Labels := by rfl

theorem canonical27883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27883 raw27883Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw27883 raw27883Labels = mixedMoment B raw27883step0 raw27883step0Labels := by
      have hz : ∀ j, raw27883 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27883step0 = (fun i j => raw27883 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27883step0 raw27883; decide +kernel
      have hl : raw27883step0Labels = raw27883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27883 raw27883Labels permutation346 hz
    mixedMoment B raw27883step0 raw27883step0Labels = mixedMoment B raw27883step1 raw27883step1Labels := by
      have ha : raw27883step1 = (fun i j => raw27883step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27883step1 raw27883step0; decide +kernel
      have hl : raw27883step1Labels = raw27883step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27883step0 raw27883step0Labels permutation145 permutation3
    mixedMoment B raw27883step1 raw27883step1Labels = mixedMoment B raw27883step2 raw27883step2Labels := by
      have ha : raw27883step2 = -raw27883step1 := by apply Matrix.ext; change ∀ i j, raw27883step2 i j = -(raw27883step1 i j); unfold raw27883step2 raw27883step1; decide +kernel
      have hl : raw27883step2Labels = raw27883step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27883step2 raw27883step2Labels = mixedMoment B raw27883step3 raw27883step3Labels := by
      have ha : raw27883step3 = raw27883step2 := by apply Matrix.ext; unfold raw27883step3 raw27883step2; decide +kernel
      have hl : raw27883step2Labels = labelEmbedding6 ∘ raw27883step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27883step2 raw27883step2Labels raw27883step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4591 node4591Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4551 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4551 node4551Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1136 node1136Labels + mixedMoment B node3273 node3273Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1380 singletonSmall4551
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4551) = raw1380Labels := by decide +kernel
  rw [hl, canonical1380 B hB] at h
  have hc0 : mixedMoment B raw1380 (Fin.cases (0 : Fin 2) singletonSmall4551) =
      mixedMoment B node1136 node1136Labels := by
    have ha : raw1380 = raw1381 := by apply Matrix.ext; unfold raw1380 raw1381; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4551 = raw1381Labels := by decide +kernel
    rw [ha, hj, canonical1381 B hB]
  have hc1 : mixedMoment B raw1380 (Fin.cases (1 : Fin 2) singletonSmall4551) =
      mixedMoment B node3273 node3273Labels := by
    have ha : raw1380 = raw1382 := by apply Matrix.ext; unfold raw1380 raw1382; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4551 = raw1382Labels := by decide +kernel
    rw [ha, hj, canonical1382 B hB]
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

theorem singleton4948 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4948 node4948Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2339 node2339Labels + mixedMoment B node3420 node3420Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1917 singletonSmall4948
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4948) = raw1917Labels := by decide +kernel
  rw [hl, canonical1917 B hB] at h
  have hc0 : mixedMoment B raw1917 (Fin.cases (0 : Fin 2) singletonSmall4948) =
      mixedMoment B node2339 node2339Labels := by
    have ha : raw1917 = raw1918 := by apply Matrix.ext; unfold raw1917 raw1918; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4948 = raw1918Labels := by decide +kernel
    rw [ha, hj, canonical1918 B hB]
  have hc1 : mixedMoment B raw1917 (Fin.cases (1 : Fin 2) singletonSmall4948) =
      mixedMoment B node3420 node3420Labels := by
    have ha : raw1917 = raw1919 := by apply Matrix.ext; unfold raw1917 raw1919; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4948 = raw1919Labels := by decide +kernel
    rw [ha, hj, canonical1919 B hB]
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

theorem singleton5037 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5037 node5037Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2429 node2429Labels + mixedMoment B node3455 node3455Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2058 singletonSmall5037
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5037) = raw2058Labels := by decide +kernel
  rw [hl, canonical2058 B hB] at h
  have hc0 : mixedMoment B raw2058 (Fin.cases (0 : Fin 2) singletonSmall5037) =
      mixedMoment B node2429 node2429Labels := by
    have ha : raw2058 = raw2059 := by apply Matrix.ext; unfold raw2058 raw2059; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5037 = raw2059Labels := by decide +kernel
    rw [ha, hj, canonical2059 B hB]
  have hc1 : mixedMoment B raw2058 (Fin.cases (1 : Fin 2) singletonSmall5037) =
      mixedMoment B node3455 node3455Labels := by
    have ha : raw2058 = raw2060 := by apply Matrix.ext; unfold raw2058 raw2060; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5037 = raw2060Labels := by decide +kernel
    rw [ha, hj, canonical2060 B hB]
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

theorem singleton5073 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5073 node5073Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2480 node2480Labels + mixedMoment B node3467 node3467Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2094 singletonSmall5073
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5073) = raw2094Labels := by decide +kernel
  rw [hl, canonical2094 B hB] at h
  have hc0 : mixedMoment B raw2094 (Fin.cases (0 : Fin 2) singletonSmall5073) =
      mixedMoment B node2480 node2480Labels := by
    have ha : raw2094 = raw2095 := by apply Matrix.ext; unfold raw2094 raw2095; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5073 = raw2095Labels := by decide +kernel
    rw [ha, hj, canonical2095 B hB]
  have hc1 : mixedMoment B raw2094 (Fin.cases (1 : Fin 2) singletonSmall5073) =
      mixedMoment B node3467 node3467Labels := by
    have ha : raw2094 = raw2096 := by apply Matrix.ext; unfold raw2094 raw2096; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5073 = raw2096Labels := by decide +kernel
    rw [ha, hj, canonical2096 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5078 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5078 node5078Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2485 node2485Labels + mixedMoment B node3481 node3481Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2103 singletonSmall5078
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5078) = raw2103Labels := by decide +kernel
  rw [hl, canonical2103 B hB] at h
  have hc0 : mixedMoment B raw2103 (Fin.cases (0 : Fin 2) singletonSmall5078) =
      mixedMoment B node2485 node2485Labels := by
    have ha : raw2103 = raw2104 := by apply Matrix.ext; unfold raw2103 raw2104; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5078 = raw2104Labels := by decide +kernel
    rw [ha, hj, canonical2104 B hB]
  have hc1 : mixedMoment B raw2103 (Fin.cases (1 : Fin 2) singletonSmall5078) =
      mixedMoment B node3481 node3481Labels := by
    have ha : raw2103 = raw2105 := by apply Matrix.ext; unfold raw2103 raw2105; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5078 = raw2105Labels := by decide +kernel
    rw [ha, hj, canonical2105 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5081 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5081 node5081Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2489 node2489Labels + mixedMoment B node3482 node3482Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2109 singletonSmall5081
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5081) = raw2109Labels := by decide +kernel
  rw [hl, canonical2109 B hB] at h
  have hc0 : mixedMoment B raw2109 (Fin.cases (0 : Fin 2) singletonSmall5081) =
      mixedMoment B node2489 node2489Labels := by
    have ha : raw2109 = raw2110 := by apply Matrix.ext; unfold raw2109 raw2110; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5081 = raw2110Labels := by decide +kernel
    rw [ha, hj, canonical2110 B hB]
  have hc1 : mixedMoment B raw2109 (Fin.cases (1 : Fin 2) singletonSmall5081) =
      mixedMoment B node3482 node3482Labels := by
    have ha : raw2109 = raw2111 := by apply Matrix.ext; unfold raw2109 raw2111; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5081 = raw2111Labels := by decide +kernel
    rw [ha, hj, canonical2111 B hB]
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

theorem singleton5149 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5149 node5149Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2924 node2924Labels + mixedMoment B node3605 node3605Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2175 singletonSmall5149
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5149) = raw2175Labels := by decide +kernel
  rw [hl, canonical2175 B hB] at h
  have hc0 : mixedMoment B raw2175 (Fin.cases (0 : Fin 2) singletonSmall5149) =
      mixedMoment B node2924 node2924Labels := by
    have ha : raw2175 = raw2176 := by apply Matrix.ext; unfold raw2175 raw2176; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5149 = raw2176Labels := by decide +kernel
    rw [ha, hj, canonical2176 B hB]
  have hc1 : mixedMoment B raw2175 (Fin.cases (1 : Fin 2) singletonSmall5149) =
      mixedMoment B node3605 node3605Labels := by
    have ha : raw2175 = raw2177 := by apply Matrix.ext; unfold raw2175 raw2177; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5149 = raw2177Labels := by decide +kernel
    rw [ha, hj, canonical2177 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5152 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5152 node5152Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2931 node2931Labels + mixedMoment B node3612 node3612Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2178 singletonSmall5152
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5152) = raw2178Labels := by decide +kernel
  rw [hl, canonical2178 B hB] at h
  have hc0 : mixedMoment B raw2178 (Fin.cases (0 : Fin 2) singletonSmall5152) =
      mixedMoment B node2931 node2931Labels := by
    have ha : raw2178 = raw2179 := by apply Matrix.ext; unfold raw2178 raw2179; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5152 = raw2179Labels := by decide +kernel
    rw [ha, hj, canonical2179 B hB]
  have hc1 : mixedMoment B raw2178 (Fin.cases (1 : Fin 2) singletonSmall5152) =
      mixedMoment B node3612 node3612Labels := by
    have ha : raw2178 = raw2180 := by apply Matrix.ext; unfold raw2178 raw2180; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5152 = raw2180Labels := by decide +kernel
    rw [ha, hj, canonical2180 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5170 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5170 node5170Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2954 node2954Labels + mixedMoment B node3606 node3606Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2202 singletonSmall5170
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5170) = raw2202Labels := by decide +kernel
  rw [hl, canonical2202 B hB] at h
  have hc0 : mixedMoment B raw2202 (Fin.cases (0 : Fin 2) singletonSmall5170) =
      mixedMoment B node2954 node2954Labels := by
    have ha : raw2202 = raw2203 := by apply Matrix.ext; unfold raw2202 raw2203; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5170 = raw2203Labels := by decide +kernel
    rw [ha, hj, canonical2203 B hB]
  have hc1 : mixedMoment B raw2202 (Fin.cases (1 : Fin 2) singletonSmall5170) =
      mixedMoment B node3606 node3606Labels := by
    have ha : raw2202 = raw2204 := by apply Matrix.ext; unfold raw2202 raw2204; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5170 = raw2204Labels := by decide +kernel
    rw [ha, hj, canonical2204 B hB]
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

theorem singleton5284 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5284 node5284Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3077 node3077Labels + mixedMoment B node3625 node3625Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2289 singletonSmall5284
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5284) = raw2289Labels := by decide +kernel
  rw [hl, canonical2289 B hB] at h
  have hc0 : mixedMoment B raw2289 (Fin.cases (0 : Fin 2) singletonSmall5284) =
      mixedMoment B node3077 node3077Labels := by
    have ha : raw2289 = raw2290 := by apply Matrix.ext; unfold raw2289 raw2290; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5284 = raw2290Labels := by decide +kernel
    rw [ha, hj, canonical2290 B hB]
  have hc1 : mixedMoment B raw2289 (Fin.cases (1 : Fin 2) singletonSmall5284) =
      mixedMoment B node3625 node3625Labels := by
    have ha : raw2289 = raw2291 := by apply Matrix.ext; unfold raw2289 raw2291; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5284 = raw2291Labels := by decide +kernel
    rw [ha, hj, canonical2291 B hB]
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

theorem sound1136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1136 node1136Labels = Sparse.eval nodeValue1136 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1136) = mixedMoment B node1136 node1136Labels := rfl
  simpa [nodeValue1136, Sparse.eval] using hc.symm

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

theorem sound2339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2339 node2339Labels = Sparse.eval nodeValue2339 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2339) = mixedMoment B node2339 node2339Labels := rfl
  simpa [nodeValue2339, Sparse.eval] using hc.symm

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

theorem sound2429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2429 node2429Labels = Sparse.eval nodeValue2429 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2429) = mixedMoment B node2429 node2429Labels := rfl
  simpa [nodeValue2429, Sparse.eval] using hc.symm

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

theorem sound2480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2480 node2480Labels = Sparse.eval nodeValue2480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2480) = mixedMoment B node2480 node2480Labels := rfl
  simpa [nodeValue2480, Sparse.eval] using hc.symm

theorem sound2485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2485 node2485Labels = Sparse.eval nodeValue2485 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2485) = mixedMoment B node2485 node2485Labels := rfl
  simpa [nodeValue2485, Sparse.eval] using hc.symm

theorem sound2489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2489 node2489Labels = Sparse.eval nodeValue2489 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2489) = mixedMoment B node2489 node2489Labels := rfl
  simpa [nodeValue2489, Sparse.eval] using hc.symm

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

theorem sound2723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2723 node2723Labels = Sparse.eval nodeValue2723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2723) = mixedMoment B node2723 node2723Labels := rfl
  simpa [nodeValue2723, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2924 node2924Labels = Sparse.eval nodeValue2924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2924) = mixedMoment B node2924 node2924Labels := rfl
  simpa [nodeValue2924, Sparse.eval] using hc.symm

theorem sound2931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2931 node2931Labels = Sparse.eval nodeValue2931 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2931) = mixedMoment B node2931 node2931Labels := rfl
  simpa [nodeValue2931, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2954 node2954Labels = Sparse.eval nodeValue2954 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2954) = mixedMoment B node2954 node2954Labels := rfl
  simpa [nodeValue2954, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3077 node3077Labels = Sparse.eval nodeValue3077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3077) = mixedMoment B node3077 node3077Labels := rfl
  simpa [nodeValue3077, Sparse.eval] using hc.symm

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

theorem sound3273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3273 node3273Labels = Sparse.eval nodeValue3273 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3273) = mixedMoment B node3273 node3273Labels := rfl
  simpa [nodeValue3273, Sparse.eval] using hc.symm

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

theorem sound3420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3420 node3420Labels = Sparse.eval nodeValue3420 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3420) = mixedMoment B node3420 node3420Labels := rfl
  simpa [nodeValue3420, Sparse.eval] using hc.symm

theorem sound3455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3455 node3455Labels = Sparse.eval nodeValue3455 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3455) = mixedMoment B node3455 node3455Labels := rfl
  simpa [nodeValue3455, Sparse.eval] using hc.symm

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

theorem sound3467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3467 node3467Labels = Sparse.eval nodeValue3467 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3467) = mixedMoment B node3467 node3467Labels := rfl
  simpa [nodeValue3467, Sparse.eval] using hc.symm

theorem sound3481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3481 node3481Labels = Sparse.eval nodeValue3481 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3481) = mixedMoment B node3481 node3481Labels := rfl
  simpa [nodeValue3481, Sparse.eval] using hc.symm

theorem sound3482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3482 node3482Labels = Sparse.eval nodeValue3482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3482) = mixedMoment B node3482 node3482Labels := rfl
  simpa [nodeValue3482, Sparse.eval] using hc.symm

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

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

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

theorem sound3605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3605 node3605Labels = Sparse.eval nodeValue3605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3605) = mixedMoment B node3605 node3605Labels := rfl
  simpa [nodeValue3605, Sparse.eval] using hc.symm

theorem sound3606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3606 node3606Labels = Sparse.eval nodeValue3606 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3606) = mixedMoment B node3606 node3606Labels := rfl
  simpa [nodeValue3606, Sparse.eval] using hc.symm

theorem sound3612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3612 node3612Labels = Sparse.eval nodeValue3612 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3612) = mixedMoment B node3612 node3612Labels := rfl
  simpa [nodeValue3612, Sparse.eval] using hc.symm

theorem sound3625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3625 node3625Labels = Sparse.eval nodeValue3625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3625) = mixedMoment B node3625 node3625Labels := rfl
  simpa [nodeValue3625, Sparse.eval] using hc.symm

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

theorem sound4330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4330 node4330Labels = Sparse.eval nodeValue4330 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4330) = mixedMoment B node4330 node4330Labels := rfl
  simpa [nodeValue4330, Sparse.eval] using hc.symm

theorem sound4335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4335 node4335Labels = Sparse.eval nodeValue4335 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4335) = mixedMoment B node4335 node4335Labels := rfl
  simpa [nodeValue4335, Sparse.eval] using hc.symm

theorem sound4347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4347 node4347Labels = Sparse.eval nodeValue4347 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4347) = mixedMoment B node4347 node4347Labels := rfl
  simpa [nodeValue4347, Sparse.eval] using hc.symm

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

theorem sound4440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4440 node4440Labels = Sparse.eval nodeValue4440 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4440) = mixedMoment B node4440 node4440Labels := rfl
  simpa [nodeValue4440, Sparse.eval] using hc.symm

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

theorem sound4528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4528 node4528Labels = Sparse.eval nodeValue4528 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4528) = mixedMoment B node4528 node4528Labels := rfl
  simpa [nodeValue4528, Sparse.eval] using hc.symm

theorem sound4535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4535 node4535Labels = Sparse.eval nodeValue4535 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4535) = mixedMoment B node4535 node4535Labels := rfl
  simpa [nodeValue4535, Sparse.eval] using hc.symm

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

theorem sound4551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4551 node4551Labels = Sparse.eval nodeValue4551 (mixedVector B) := by
  have h := singleton4551 B _hB
  rw [sound1136 B _hB _hF, sound3273 B _hB _hF] at h
  norm_num [nodeValue4551, nodeValue1136, nodeValue3273, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4591 node4591Labels = Sparse.eval nodeValue4591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4591) = mixedMoment B node4591 node4591Labels := rfl
  simpa [nodeValue4591, Sparse.eval] using hc.symm

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

theorem sound4930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4930 node4930Labels = Sparse.eval nodeValue4930 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4930) = mixedMoment B node4930 node4930Labels := rfl
  simpa [nodeValue4930, Sparse.eval] using hc.symm

theorem sound4935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4935 node4935Labels = Sparse.eval nodeValue4935 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4935) = mixedMoment B node4935 node4935Labels := rfl
  simpa [nodeValue4935, Sparse.eval] using hc.symm

theorem sound4944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4944 node4944Labels = Sparse.eval nodeValue4944 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4944) = mixedMoment B node4944 node4944Labels := rfl
  simpa [nodeValue4944, Sparse.eval] using hc.symm

theorem sound4948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4948 node4948Labels = Sparse.eval nodeValue4948 (mixedVector B) := by
  have h := singleton4948 B _hB
  rw [sound2339 B _hB _hF, sound3420 B _hB _hF] at h
  norm_num [nodeValue4948, nodeValue2339, nodeValue3420, Sparse.eval] at h ⊢
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

theorem sound5034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5034 node5034Labels = Sparse.eval nodeValue5034 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5034) = mixedMoment B node5034 node5034Labels := rfl
  simpa [nodeValue5034, Sparse.eval] using hc.symm

theorem sound5037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5037 node5037Labels = Sparse.eval nodeValue5037 (mixedVector B) := by
  have h := singleton5037 B _hB
  rw [sound2429 B _hB _hF, sound3455 B _hB _hF] at h
  norm_num [nodeValue5037, nodeValue2429, nodeValue3455, Sparse.eval] at h ⊢
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

theorem zero5104 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5104 node5104Labels = 0 := by
  exact mixedMoment_order_one B hB node5104 node5104Labels 1
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

theorem sound5065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5065 node5065Labels = Sparse.eval nodeValue5065 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5065) = mixedMoment B node5065 node5065Labels := rfl
  simpa [nodeValue5065, Sparse.eval] using hc.symm

theorem sound5073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5073 node5073Labels = Sparse.eval nodeValue5073 (mixedVector B) := by
  have h := singleton5073 B _hB
  rw [sound2480 B _hB _hF, sound3467 B _hB _hF] at h
  norm_num [nodeValue5073, nodeValue2480, nodeValue3467, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5078 node5078Labels = Sparse.eval nodeValue5078 (mixedVector B) := by
  have h := singleton5078 B _hB
  rw [sound2485 B _hB _hF, sound3481 B _hB _hF] at h
  norm_num [nodeValue5078, nodeValue2485, nodeValue3481, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5081 node5081Labels = Sparse.eval nodeValue5081 (mixedVector B) := by
  have h := singleton5081 B _hB
  rw [sound2489 B _hB _hF, sound3482 B _hB _hF] at h
  norm_num [nodeValue5081, nodeValue2489, nodeValue3482, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5104 node5104Labels = Sparse.eval nodeValue5104 (mixedVector B) := by
  simpa only [nodeValue5104, Sparse.eval_nil] using zero5104 B _hB _hF

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

theorem sound5128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5128 node5128Labels = Sparse.eval nodeValue5128 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5128) = mixedMoment B node5128 node5128Labels := rfl
  simpa [nodeValue5128, Sparse.eval] using hc.symm

theorem sound5139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5139 node5139Labels = Sparse.eval nodeValue5139 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5139) = mixedMoment B node5139 node5139Labels := rfl
  simpa [nodeValue5139, Sparse.eval] using hc.symm

theorem sound5149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5149 node5149Labels = Sparse.eval nodeValue5149 (mixedVector B) := by
  have h := singleton5149 B _hB
  rw [sound2924 B _hB _hF, sound3605 B _hB _hF] at h
  norm_num [nodeValue5149, nodeValue2924, nodeValue3605, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5152 node5152Labels = Sparse.eval nodeValue5152 (mixedVector B) := by
  have h := singleton5152 B _hB
  rw [sound2931 B _hB _hF, sound3612 B _hB _hF] at h
  norm_num [nodeValue5152, nodeValue2931, nodeValue3612, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5170 node5170Labels = Sparse.eval nodeValue5170 (mixedVector B) := by
  have h := singleton5170 B _hB
  rw [sound2954 B _hB _hF, sound3606 B _hB _hF] at h
  norm_num [nodeValue5170, nodeValue2954, nodeValue3606, Sparse.eval] at h ⊢
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

theorem sound5252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5252 node5252Labels = Sparse.eval nodeValue5252 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5252) = mixedMoment B node5252 node5252Labels := rfl
  simpa [nodeValue5252, Sparse.eval] using hc.symm

theorem sound5259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5259 node5259Labels = Sparse.eval nodeValue5259 (mixedVector B) := by
  have h := singleton5259 B _hB
  rw [sound2723 B _hB _hF, sound3544 B _hB _hF] at h
  norm_num [nodeValue5259, nodeValue2723, nodeValue3544, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5284 node5284Labels = Sparse.eval nodeValue5284 (mixedVector B) := by
  have h := singleton5284 B _hB
  rw [sound3077 B _hB _hF, sound3625 B _hB _hF] at h
  norm_num [nodeValue5284, nodeValue3077, nodeValue3625, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem zero5410 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5410 node5410Labels = 0 := by
  exact mixedMoment_order_one B hB node5410 node5410Labels 1
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

theorem sound5410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5410 node5410Labels = Sparse.eval nodeValue5410 (mixedVector B) := by
  simpa only [nodeValue5410, Sparse.eval_nil] using zero5410 B _hB _hF

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

theorem sourceEq1965 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1965 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1965 + difference 0 1) (sourceB1965 + difference 1 0) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA1965 + difference 0 1) (sourceB1965 + difference 1 0) sourceC1965) = raw17871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw17871; decide +kernel
    rw [ha]
    exact (canonical17871 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1965 + difference 0 2) (sourceB1965 + difference 2 0) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA1965 + difference 0 2) (sourceB1965 + difference 2 0) sourceC1965) = raw17872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw17872; decide +kernel
    rw [ha]
    exact (canonical17872 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1965 + difference 0 3) (sourceB1965 + difference 3 0) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA1965 + difference 0 3) (sourceB1965 + difference 3 0) sourceC1965) = raw17873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw17873; decide +kernel
    rw [ha]
    exact (canonical17873 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1965 + difference 0 4) (sourceB1965 + difference 4 0) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA1965 + difference 0 4) (sourceB1965 + difference 4 0) sourceC1965) = raw17874 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw17874; decide +kernel
    rw [ha]
    exact (canonical17874 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1965 + difference 0 5) (sourceB1965 + difference 5 0) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA1965 + difference 0 5) (sourceB1965 + difference 5 0) sourceC1965) = raw27862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27862; decide +kernel
    rw [ha]
    exact (canonical27862 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1965 + difference 1 0) (sourceB1965 + difference 0 1) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4440) := by
    have ha : (tripleCharges (sourceA1965 + difference 1 0) (sourceB1965 + difference 0 1) sourceC1965) = raw27863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27863; decide +kernel
    rw [ha]
    exact (canonical27863 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1965 + difference 1 2) (sourceB1965 + difference 2 1) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5065) := by
    have ha : (tripleCharges (sourceA1965 + difference 1 2) (sourceB1965 + difference 2 1) sourceC1965) = raw27864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27864; decide +kernel
    rw [ha]
    exact (canonical27864 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1965 + difference 1 3) (sourceB1965 + difference 3 1) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1965 + difference 1 3) (sourceB1965 + difference 3 1) sourceC1965) = raw27865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27865; decide +kernel
    rw [ha]
    exact (canonical27865 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1965 + difference 1 4) (sourceB1965 + difference 4 1) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA1965 + difference 1 4) (sourceB1965 + difference 4 1) sourceC1965) = raw27866 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27866; decide +kernel
    rw [ha]
    exact (canonical27866 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1965 + difference 1 5) (sourceB1965 + difference 5 1) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA1965 + difference 1 5) (sourceB1965 + difference 5 1) sourceC1965) = raw17850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw17850; decide +kernel
    rw [ha]
    exact (canonical17850 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1965 + difference 2 0) (sourceB1965 + difference 0 2) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4327) := by
    have ha : (tripleCharges (sourceA1965 + difference 2 0) (sourceB1965 + difference 0 2) sourceC1965) = raw27867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27867; decide +kernel
    rw [ha]
    exact (canonical27867 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1965 + difference 2 1) (sourceB1965 + difference 1 2) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4930) := by
    have ha : (tripleCharges (sourceA1965 + difference 2 1) (sourceB1965 + difference 1 2) sourceC1965) = raw27868 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27868; decide +kernel
    rw [ha]
    exact (canonical27868 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1965 + difference 2 3) (sourceB1965 + difference 3 2) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5037) := by
    have ha : (tripleCharges (sourceA1965 + difference 2 3) (sourceB1965 + difference 3 2) sourceC1965) = raw27869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27869; decide +kernel
    rw [ha]
    exact (canonical27869 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1965 + difference 2 4) (sourceB1965 + difference 4 2) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5128) := by
    have ha : (tripleCharges (sourceA1965 + difference 2 4) (sourceB1965 + difference 4 2) sourceC1965) = raw27870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27870; decide +kernel
    rw [ha]
    exact (canonical27870 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1965 + difference 2 5) (sourceB1965 + difference 5 2) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA1965 + difference 2 5) (sourceB1965 + difference 5 2) sourceC1965) = raw17855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw17855; decide +kernel
    rw [ha]
    exact (canonical17855 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1965 + difference 3 0) (sourceB1965 + difference 0 3) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4347) := by
    have ha : (tripleCharges (sourceA1965 + difference 3 0) (sourceB1965 + difference 0 3) sourceC1965) = raw27871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27871; decide +kernel
    rw [ha]
    exact (canonical27871 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1965 + difference 3 1) (sourceB1965 + difference 1 3) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4944) := by
    have ha : (tripleCharges (sourceA1965 + difference 3 1) (sourceB1965 + difference 1 3) sourceC1965) = raw27872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27872; decide +kernel
    rw [ha]
    exact (canonical27872 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1965 + difference 3 2) (sourceB1965 + difference 2 3) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5034) := by
    have ha : (tripleCharges (sourceA1965 + difference 3 2) (sourceB1965 + difference 2 3) sourceC1965) = raw27873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27873; decide +kernel
    rw [ha]
    exact (canonical27873 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1965 + difference 3 4) (sourceB1965 + difference 4 3) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA1965 + difference 3 4) (sourceB1965 + difference 4 3) sourceC1965) = raw27874 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27874; decide +kernel
    rw [ha]
    exact (canonical27874 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1965 + difference 3 5) (sourceB1965 + difference 5 3) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA1965 + difference 3 5) (sourceB1965 + difference 5 3) sourceC1965) = raw17860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw17860; decide +kernel
    rw [ha]
    exact (canonical17860 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1965 + difference 4 0) (sourceB1965 + difference 0 4) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA1965 + difference 4 0) (sourceB1965 + difference 0 4) sourceC1965) = raw27875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27875; decide +kernel
    rw [ha]
    exact (canonical27875 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1965 + difference 4 1) (sourceB1965 + difference 1 4) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4935) := by
    have ha : (tripleCharges (sourceA1965 + difference 4 1) (sourceB1965 + difference 1 4) sourceC1965) = raw27876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27876; decide +kernel
    rw [ha]
    exact (canonical27876 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1965 + difference 4 2) (sourceB1965 + difference 2 4) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4930) := by
    have ha : (tripleCharges (sourceA1965 + difference 4 2) (sourceB1965 + difference 2 4) sourceC1965) = raw27877 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27877; decide +kernel
    rw [ha]
    exact (canonical27877 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1965 + difference 4 3) (sourceB1965 + difference 3 4) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4948) := by
    have ha : (tripleCharges (sourceA1965 + difference 4 3) (sourceB1965 + difference 3 4) sourceC1965) = raw27878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27878; decide +kernel
    rw [ha]
    exact (canonical27878 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1965 + difference 4 5) (sourceB1965 + difference 5 4) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA1965 + difference 4 5) (sourceB1965 + difference 5 4) sourceC1965) = raw17865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw17865; decide +kernel
    rw [ha]
    exact (canonical17865 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1965 + difference 5 0) (sourceB1965 + difference 0 5) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1965 + difference 5 0) (sourceB1965 + difference 0 5) sourceC1965) = raw27879 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27879; decide +kernel
    rw [ha]
    exact (canonical27879 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1965 + difference 5 1) (sourceB1965 + difference 1 5) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4535) := by
    have ha : (tripleCharges (sourceA1965 + difference 5 1) (sourceB1965 + difference 1 5) sourceC1965) = raw27880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27880; decide +kernel
    rw [ha]
    exact (canonical27880 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1965 + difference 5 2) (sourceB1965 + difference 2 5) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4528) := by
    have ha : (tripleCharges (sourceA1965 + difference 5 2) (sourceB1965 + difference 2 5) sourceC1965) = raw27881 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27881; decide +kernel
    rw [ha]
    exact (canonical27881 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1965 + difference 5 3) (sourceB1965 + difference 3 5) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4551) := by
    have ha : (tripleCharges (sourceA1965 + difference 5 3) (sourceB1965 + difference 3 5) sourceC1965) = raw27882 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27882; decide +kernel
    rw [ha]
    exact (canonical27882 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1965 + difference 5 4) (sourceB1965 + difference 4 5) sourceC1965) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1965 + difference 5 4) (sourceB1965 + difference 4 5) sourceC1965) = raw27883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1965 sourceB1965 sourceC1965 difference raw27883; decide +kernel
    rw [ha]
    exact (canonical27883 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1965 sourceB1965 sourceC1965
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1965, Integer.Sparse.eval]
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

theorem reindexCheck1668 : Integer.Sparse.reindex keyMap MixedData.row1668 = numericRow1668 := by decide +kernel

theorem numericCheck1668 (x : Master → ℝ) : Integer.Sparse.eval numericRow1668 x =
    (4 : ℝ) * reducedSource1668 x := by
  norm_num [numericRow1668, reducedSource1668, Integer.Sparse.eval, Sparse.eval, nodeValue4327, nodeValue4330, nodeValue4335, nodeValue4347, nodeValue4440, nodeValue4528, nodeValue4535, nodeValue4551, nodeValue4591, nodeValue4930, nodeValue4935, nodeValue4944, nodeValue4948, nodeValue5034, nodeValue5037, nodeValue5065, nodeValue5073, nodeValue5078, nodeValue5081, nodeValue5104, nodeValue5128, nodeValue5139, nodeValue5149, nodeValue5152, nodeValue5170, nodeValue5252, nodeValue5259, nodeValue5284, nodeValue5410]
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

theorem reducedZero1668 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1668 (mixedVector B) = 0 := by
  have h4327 : mixedVector B (Sum.inr 4327) = Sparse.eval nodeValue4327 (mixedVector B) := by
    change mixedMoment B node4327 node4327Labels = _
    exact sound4327 B hB hF
  have h4330 : mixedVector B (Sum.inr 4330) = Sparse.eval nodeValue4330 (mixedVector B) := by
    change mixedMoment B node4330 node4330Labels = _
    exact sound4330 B hB hF
  have h4335 : mixedVector B (Sum.inr 4335) = Sparse.eval nodeValue4335 (mixedVector B) := by
    change mixedMoment B node4335 node4335Labels = _
    exact sound4335 B hB hF
  have h4347 : mixedVector B (Sum.inr 4347) = Sparse.eval nodeValue4347 (mixedVector B) := by
    change mixedMoment B node4347 node4347Labels = _
    exact sound4347 B hB hF
  have h4440 : mixedVector B (Sum.inr 4440) = Sparse.eval nodeValue4440 (mixedVector B) := by
    change mixedMoment B node4440 node4440Labels = _
    exact sound4440 B hB hF
  have h4528 : mixedVector B (Sum.inr 4528) = Sparse.eval nodeValue4528 (mixedVector B) := by
    change mixedMoment B node4528 node4528Labels = _
    exact sound4528 B hB hF
  have h4535 : mixedVector B (Sum.inr 4535) = Sparse.eval nodeValue4535 (mixedVector B) := by
    change mixedMoment B node4535 node4535Labels = _
    exact sound4535 B hB hF
  have h4551 : mixedVector B (Sum.inr 4551) = Sparse.eval nodeValue4551 (mixedVector B) := by
    change mixedMoment B node4551 node4551Labels = _
    exact sound4551 B hB hF
  have h4591 : mixedVector B (Sum.inr 4591) = Sparse.eval nodeValue4591 (mixedVector B) := by
    change mixedMoment B node4591 node4591Labels = _
    exact sound4591 B hB hF
  have h4930 : mixedVector B (Sum.inr 4930) = Sparse.eval nodeValue4930 (mixedVector B) := by
    change mixedMoment B node4930 node4930Labels = _
    exact sound4930 B hB hF
  have h4935 : mixedVector B (Sum.inr 4935) = Sparse.eval nodeValue4935 (mixedVector B) := by
    change mixedMoment B node4935 node4935Labels = _
    exact sound4935 B hB hF
  have h4944 : mixedVector B (Sum.inr 4944) = Sparse.eval nodeValue4944 (mixedVector B) := by
    change mixedMoment B node4944 node4944Labels = _
    exact sound4944 B hB hF
  have h4948 : mixedVector B (Sum.inr 4948) = Sparse.eval nodeValue4948 (mixedVector B) := by
    change mixedMoment B node4948 node4948Labels = _
    exact sound4948 B hB hF
  have h5034 : mixedVector B (Sum.inr 5034) = Sparse.eval nodeValue5034 (mixedVector B) := by
    change mixedMoment B node5034 node5034Labels = _
    exact sound5034 B hB hF
  have h5037 : mixedVector B (Sum.inr 5037) = Sparse.eval nodeValue5037 (mixedVector B) := by
    change mixedMoment B node5037 node5037Labels = _
    exact sound5037 B hB hF
  have h5065 : mixedVector B (Sum.inr 5065) = Sparse.eval nodeValue5065 (mixedVector B) := by
    change mixedMoment B node5065 node5065Labels = _
    exact sound5065 B hB hF
  have h5073 : mixedVector B (Sum.inr 5073) = Sparse.eval nodeValue5073 (mixedVector B) := by
    change mixedMoment B node5073 node5073Labels = _
    exact sound5073 B hB hF
  have h5078 : mixedVector B (Sum.inr 5078) = Sparse.eval nodeValue5078 (mixedVector B) := by
    change mixedMoment B node5078 node5078Labels = _
    exact sound5078 B hB hF
  have h5081 : mixedVector B (Sum.inr 5081) = Sparse.eval nodeValue5081 (mixedVector B) := by
    change mixedMoment B node5081 node5081Labels = _
    exact sound5081 B hB hF
  have h5104 : mixedVector B (Sum.inr 5104) = Sparse.eval nodeValue5104 (mixedVector B) := by
    change mixedMoment B node5104 node5104Labels = _
    exact sound5104 B hB hF
  have h5128 : mixedVector B (Sum.inr 5128) = Sparse.eval nodeValue5128 (mixedVector B) := by
    change mixedMoment B node5128 node5128Labels = _
    exact sound5128 B hB hF
  have h5139 : mixedVector B (Sum.inr 5139) = Sparse.eval nodeValue5139 (mixedVector B) := by
    change mixedMoment B node5139 node5139Labels = _
    exact sound5139 B hB hF
  have h5149 : mixedVector B (Sum.inr 5149) = Sparse.eval nodeValue5149 (mixedVector B) := by
    change mixedMoment B node5149 node5149Labels = _
    exact sound5149 B hB hF
  have h5152 : mixedVector B (Sum.inr 5152) = Sparse.eval nodeValue5152 (mixedVector B) := by
    change mixedMoment B node5152 node5152Labels = _
    exact sound5152 B hB hF
  have h5170 : mixedVector B (Sum.inr 5170) = Sparse.eval nodeValue5170 (mixedVector B) := by
    change mixedMoment B node5170 node5170Labels = _
    exact sound5170 B hB hF
  have h5252 : mixedVector B (Sum.inr 5252) = Sparse.eval nodeValue5252 (mixedVector B) := by
    change mixedMoment B node5252 node5252Labels = _
    exact sound5252 B hB hF
  have h5259 : mixedVector B (Sum.inr 5259) = Sparse.eval nodeValue5259 (mixedVector B) := by
    change mixedMoment B node5259 node5259Labels = _
    exact sound5259 B hB hF
  have h5284 : mixedVector B (Sum.inr 5284) = Sparse.eval nodeValue5284 (mixedVector B) := by
    change mixedMoment B node5284 node5284Labels = _
    exact sound5284 B hB hF
  have h5410 : mixedVector B (Sum.inr 5410) = Sparse.eval nodeValue5410 (mixedVector B) := by
    change mixedMoment B node5410 node5410Labels = _
    exact sound5410 B hB hF
  simpa only [sourceForm1965, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4327, h4330, h4335, h4347, h4440, h4528, h4535, h4551, h4591, h4930, h4935, h4944, h4948, h5034, h5037, h5065, h5073, h5078, h5081, h5104, h5128, h5139, h5149, h5152, h5170, h5252, h5259, h5284, h5410, reducedSource1668] using sourceEq1965 B hB

theorem rowSound1668_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1668 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1668, numericCheck1668, reducedZero1668 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668_e_oai
