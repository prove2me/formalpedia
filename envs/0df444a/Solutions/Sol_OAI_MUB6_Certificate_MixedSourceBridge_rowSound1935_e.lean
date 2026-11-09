-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:19:43.42761+00:00
-- url     : https://prove2.me/submissions/7fba1c31-83a4-439e-8c4c-cb6940750afd

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E095
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E191
import Definitions.Def_OAIQ106E101
import Definitions.Def_OAIQ106E106
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical1944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1944 raw1944Labels = mixedMoment B node4968 node4968Labels := by
  calc
    mixedMoment B raw1944 raw1944Labels = mixedMoment B raw1944step0 raw1944step0Labels := by
      have ha : raw1944step0 = (fun i j => raw1944 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1944step0 raw1944; decide +kernel
      have hl : raw1944step0Labels = raw1944Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1944 raw1944Labels permutation152 permutation5
    mixedMoment B raw1944step0 raw1944step0Labels = mixedMoment B raw1944step1 raw1944step1Labels := by
      have ha : raw1944step1 = raw1944step0 := by apply Matrix.ext; unfold raw1944step1 raw1944step0; decide +kernel
      have hl : raw1944step0Labels = labelEmbedding8 ∘ raw1944step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1944step0 raw1944step0Labels raw1944step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4968 node4968Labels := by rfl

theorem canonical1945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1945 raw1945Labels = mixedMoment B node2809 node2809Labels := by
  calc
    mixedMoment B raw1945 raw1945Labels = mixedMoment B raw1945step0 raw1945step0Labels := by
      have ha : raw1945step0 = (fun i j => raw1945 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1945step0 raw1945; decide +kernel
      have hl : raw1945step0Labels = raw1945Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1945 raw1945Labels permutation164 permutation4
    _ = mixedMoment B node2809 node2809Labels := by rfl

theorem canonical1946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1946 raw1946Labels = mixedMoment B node3587 node3587Labels := by
  calc
    mixedMoment B raw1946 raw1946Labels = mixedMoment B raw1946step0 raw1946step0Labels := by
      have ha : raw1946step0 = (fun i j => raw1946 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1946step0 raw1946; decide +kernel
      have hl : raw1946step0Labels = raw1946Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1946 raw1946Labels permutation152 permutation3
    mixedMoment B raw1946step0 raw1946step0Labels = mixedMoment B raw1946step1 raw1946step1Labels := by
      have ha : raw1946step1 = -raw1946step0 := by apply Matrix.ext; change ∀ i j, raw1946step1 i j = -(raw1946step0 i j); unfold raw1946step1 raw1946step0; decide +kernel
      have hl : raw1946step1Labels = raw1946step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1946step1 raw1946step1Labels = mixedMoment B raw1946step2 raw1946step2Labels := by
      have ha : raw1946step2 = raw1946step1 := by apply Matrix.ext; unfold raw1946step2 raw1946step1; decide +kernel
      have hl : raw1946step1Labels = labelEmbedding1 ∘ raw1946step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1946step1 raw1946step1Labels raw1946step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3587 node3587Labels := by rfl

theorem canonical1950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1950 raw1950Labels = mixedMoment B node4970 node4970Labels := by
  calc
    mixedMoment B raw1950 raw1950Labels = mixedMoment B raw1950step0 raw1950step0Labels := by
      have ha : raw1950step0 = (fun i j => raw1950 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1950step0 raw1950; decide +kernel
      have hl : raw1950step0Labels = raw1950Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1950 raw1950Labels permutation32 permutation5
    mixedMoment B raw1950step0 raw1950step0Labels = mixedMoment B raw1950step1 raw1950step1Labels := by
      have ha : raw1950step1 = raw1950step0 := by apply Matrix.ext; unfold raw1950step1 raw1950step0; decide +kernel
      have hl : raw1950step0Labels = labelEmbedding8 ∘ raw1950step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1950step0 raw1950step0Labels raw1950step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4970 node4970Labels := by rfl

theorem canonical1951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1951 raw1951Labels = mixedMoment B node2815 node2815Labels := by
  calc
    mixedMoment B raw1951 raw1951Labels = mixedMoment B raw1951step0 raw1951step0Labels := by
      have ha : raw1951step0 = (fun i j => raw1951 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1951step0 raw1951; decide +kernel
      have hl : raw1951step0Labels = raw1951Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1951 raw1951Labels permutation32 permutation4
    _ = mixedMoment B node2815 node2815Labels := by rfl

theorem canonical1952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1952 raw1952Labels = mixedMoment B node3588 node3588Labels := by
  calc
    mixedMoment B raw1952 raw1952Labels = mixedMoment B raw1952step0 raw1952step0Labels := by
      have ha : raw1952step0 = (fun i j => raw1952 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1952step0 raw1952; decide +kernel
      have hl : raw1952step0Labels = raw1952Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1952 raw1952Labels permutation32 permutation3
    mixedMoment B raw1952step0 raw1952step0Labels = mixedMoment B raw1952step1 raw1952step1Labels := by
      have ha : raw1952step1 = -raw1952step0 := by apply Matrix.ext; change ∀ i j, raw1952step1 i j = -(raw1952step0 i j); unfold raw1952step1 raw1952step0; decide +kernel
      have hl : raw1952step1Labels = raw1952step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1952step1 raw1952step1Labels = mixedMoment B raw1952step2 raw1952step2Labels := by
      have ha : raw1952step2 = raw1952step1 := by apply Matrix.ext; unfold raw1952step2 raw1952step1; decide +kernel
      have hl : raw1952step1Labels = labelEmbedding1 ∘ raw1952step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1952step1 raw1952step1Labels raw1952step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3588 node3588Labels := by rfl

theorem canonical1962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1962 raw1962Labels = mixedMoment B node4974 node4974Labels := by
  calc
    mixedMoment B raw1962 raw1962Labels = mixedMoment B raw1962step0 raw1962step0Labels := by
      have ha : raw1962step0 = (fun i j => raw1962 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw1962step0 raw1962; decide +kernel
      have hl : raw1962step0Labels = raw1962Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1962 raw1962Labels permutation32 permutation5
    mixedMoment B raw1962step0 raw1962step0Labels = mixedMoment B raw1962step1 raw1962step1Labels := by
      have ha : raw1962step1 = raw1962step0 := by apply Matrix.ext; unfold raw1962step1 raw1962step0; decide +kernel
      have hl : raw1962step0Labels = labelEmbedding8 ∘ raw1962step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1962step0 raw1962step0Labels raw1962step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4974 node4974Labels := by rfl

theorem canonical1963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1963 raw1963Labels = mixedMoment B node2818 node2818Labels := by
  calc
    mixedMoment B raw1963 raw1963Labels = mixedMoment B raw1963step0 raw1963step0Labels := by
      have ha : raw1963step0 = (fun i j => raw1963 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1963step0 raw1963; decide +kernel
      have hl : raw1963step0Labels = raw1963Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1963 raw1963Labels permutation32 permutation4
    _ = mixedMoment B node2818 node2818Labels := by rfl

theorem canonical1964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1964 raw1964Labels = mixedMoment B node3592 node3592Labels := by
  calc
    mixedMoment B raw1964 raw1964Labels = mixedMoment B raw1964step0 raw1964step0Labels := by
      have ha : raw1964step0 = (fun i j => raw1964 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1964step0 raw1964; decide +kernel
      have hl : raw1964step0Labels = raw1964Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1964 raw1964Labels permutation32 permutation3
    mixedMoment B raw1964step0 raw1964step0Labels = mixedMoment B raw1964step1 raw1964step1Labels := by
      have ha : raw1964step1 = -raw1964step0 := by apply Matrix.ext; change ∀ i j, raw1964step1 i j = -(raw1964step0 i j); unfold raw1964step1 raw1964step0; decide +kernel
      have hl : raw1964step1Labels = raw1964step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1964step1 raw1964step1Labels = mixedMoment B raw1964step2 raw1964step2Labels := by
      have ha : raw1964step2 = raw1964step1 := by apply Matrix.ext; unfold raw1964step2 raw1964step1; decide +kernel
      have hl : raw1964step1Labels = labelEmbedding1 ∘ raw1964step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1964step1 raw1964step1Labels raw1964step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3592 node3592Labels := by rfl

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

theorem canonical2226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2226 raw2226Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw2226 raw2226Labels = mixedMoment B raw2226step0 raw2226step0Labels := by
      have ha : raw2226step0 = (fun i j => raw2226 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2226step0 raw2226; decide +kernel
      have hl : raw2226step0Labels = raw2226Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2226 raw2226Labels permutation152 permutation5
    mixedMoment B raw2226step0 raw2226step0Labels = mixedMoment B raw2226step1 raw2226step1Labels := by
      have ha : raw2226step1 = raw2226step0 := by apply Matrix.ext; unfold raw2226step1 raw2226step0; decide +kernel
      have hl : raw2226step0Labels = labelEmbedding8 ∘ raw2226step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2226step0 raw2226step0Labels raw2226step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5202 node5202Labels := by rfl

theorem canonical2227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2227 raw2227Labels = mixedMoment B node2880 node2880Labels := by
  calc
    mixedMoment B raw2227 raw2227Labels = mixedMoment B raw2227step0 raw2227step0Labels := by
      have ha : raw2227step0 = (fun i j => raw2227 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2227step0 raw2227; decide +kernel
      have hl : raw2227step0Labels = raw2227Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2227 raw2227Labels permutation170 permutation4
    _ = mixedMoment B node2880 node2880Labels := by rfl

theorem canonical2228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2228 raw2228Labels = mixedMoment B node3617 node3617Labels := by
  calc
    mixedMoment B raw2228 raw2228Labels = mixedMoment B raw2228step0 raw2228step0Labels := by
      have ha : raw2228step0 = (fun i j => raw2228 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2228step0 raw2228; decide +kernel
      have hl : raw2228step0Labels = raw2228Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2228 raw2228Labels permutation184 permutation3
    mixedMoment B raw2228step0 raw2228step0Labels = mixedMoment B raw2228step1 raw2228step1Labels := by
      have ha : raw2228step1 = -raw2228step0 := by apply Matrix.ext; change ∀ i j, raw2228step1 i j = -(raw2228step0 i j); unfold raw2228step1 raw2228step0; decide +kernel
      have hl : raw2228step1Labels = raw2228step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2228step1 raw2228step1Labels = mixedMoment B raw2228step2 raw2228step2Labels := by
      have ha : raw2228step2 = raw2228step1 := by apply Matrix.ext; unfold raw2228step2 raw2228step1; decide +kernel
      have hl : raw2228step1Labels = labelEmbedding1 ∘ raw2228step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2228step1 raw2228step1Labels raw2228step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3617 node3617Labels := by rfl

theorem canonical2229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2229 raw2229Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw2229 raw2229Labels = mixedMoment B raw2229step0 raw2229step0Labels := by
      have ha : raw2229step0 = (fun i j => raw2229 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2229step0 raw2229; decide +kernel
      have hl : raw2229step0Labels = raw2229Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2229 raw2229Labels permutation32 permutation5
    mixedMoment B raw2229step0 raw2229step0Labels = mixedMoment B raw2229step1 raw2229step1Labels := by
      have ha : raw2229step1 = raw2229step0 := by apply Matrix.ext; unfold raw2229step1 raw2229step0; decide +kernel
      have hl : raw2229step0Labels = labelEmbedding8 ∘ raw2229step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2229step0 raw2229step0Labels raw2229step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5203 node5203Labels := by rfl

theorem canonical2230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2230 raw2230Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw2230 raw2230Labels = mixedMoment B raw2230step0 raw2230step0Labels := by
      have ha : raw2230step0 = (fun i j => raw2230 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2230step0 raw2230; decide +kernel
      have hl : raw2230step0Labels = raw2230Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2230 raw2230Labels permutation32 permutation4
    _ = mixedMoment B node2884 node2884Labels := by rfl

theorem canonical2231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2231 raw2231Labels = mixedMoment B node3621 node3621Labels := by
  calc
    mixedMoment B raw2231 raw2231Labels = mixedMoment B raw2231step0 raw2231step0Labels := by
      have ha : raw2231step0 = (fun i j => raw2231 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2231step0 raw2231; decide +kernel
      have hl : raw2231step0Labels = raw2231Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2231 raw2231Labels permutation40 permutation3
    mixedMoment B raw2231step0 raw2231step0Labels = mixedMoment B raw2231step1 raw2231step1Labels := by
      have ha : raw2231step1 = -raw2231step0 := by apply Matrix.ext; change ∀ i j, raw2231step1 i j = -(raw2231step0 i j); unfold raw2231step1 raw2231step0; decide +kernel
      have hl : raw2231step1Labels = raw2231step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2231step1 raw2231step1Labels = mixedMoment B raw2231step2 raw2231step2Labels := by
      have ha : raw2231step2 = raw2231step1 := by apply Matrix.ext; unfold raw2231step2 raw2231step1; decide +kernel
      have hl : raw2231step1Labels = labelEmbedding1 ∘ raw2231step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2231step1 raw2231step1Labels raw2231step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3621 node3621Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2583 raw2583Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw2583 raw2583Labels = mixedMoment B raw2583step0 raw2583step0Labels := by
      have ha : raw2583step0 = (fun i j => raw2583 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2583step0 raw2583; decide +kernel
      have hl : raw2583step0Labels = raw2583Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2583 raw2583Labels permutation152 permutation4
    mixedMoment B raw2583step0 raw2583step0Labels = mixedMoment B raw2583step1 raw2583step1Labels := by
      have ha : raw2583step1 = raw2583step0 := by apply Matrix.ext; unfold raw2583step1 raw2583step0; decide +kernel
      have hl : raw2583step0Labels = labelEmbedding7 ∘ raw2583step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2583step0 raw2583step0Labels raw2583step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

theorem canonical2584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2584 raw2584Labels = mixedMoment B node3945 node3945Labels := by
  calc
    mixedMoment B raw2584 raw2584Labels = mixedMoment B raw2584step0 raw2584step0Labels := by
      have ha : raw2584step0 = (fun i j => raw2584 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2584step0 raw2584; decide +kernel
      have hl : raw2584step0Labels = raw2584Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2584 raw2584Labels permutation152 permutation4
    _ = mixedMoment B node3945 node3945Labels := by rfl

theorem canonical2585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2585 raw2585Labels = mixedMoment B node3952 node3952Labels := by
  calc
    mixedMoment B raw2585 raw2585Labels = mixedMoment B raw2585step0 raw2585step0Labels := by
      have ha : raw2585step0 = (fun i j => raw2585 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2585step0 raw2585; decide +kernel
      have hl : raw2585step0Labels = raw2585Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2585 raw2585Labels permutation265 permutation6
    mixedMoment B raw2585step0 raw2585step0Labels = mixedMoment B raw2585step1 raw2585step1Labels := by
      have ha : raw2585step1 = -raw2585step0 := by apply Matrix.ext; change ∀ i j, raw2585step1 i j = -(raw2585step0 i j); unfold raw2585step1 raw2585step0; decide +kernel
      have hl : raw2585step1Labels = raw2585step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2585step1 raw2585step1Labels = mixedMoment B raw2585step2 raw2585step2Labels := by
      have ha : raw2585step2 = raw2585step1 := by apply Matrix.ext; unfold raw2585step2 raw2585step1; decide +kernel
      have hl : raw2585step1Labels = labelEmbedding1 ∘ raw2585step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2585step1 raw2585step1Labels raw2585step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3952 node3952Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical254
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32567 raw32567Labels = mixedMoment B node5369 node5369Labels := by
  calc
    mixedMoment B raw32567 raw32567Labels = mixedMoment B raw32567step0 raw32567step0Labels := by
      have hz : ∀ j, raw32567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32567step0 = (fun i j => raw32567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32567step0 raw32567; decide +kernel
      have hl : raw32567step0Labels = raw32567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32567 raw32567Labels permutation346 hz
    mixedMoment B raw32567step0 raw32567step0Labels = mixedMoment B raw32567step1 raw32567step1Labels := by
      have ha : raw32567step1 = (fun i j => raw32567step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32567step1 raw32567step0; decide +kernel
      have hl : raw32567step1Labels = raw32567step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32567step0 raw32567step0Labels permutation56 permutation2
    _ = mixedMoment B node5369 node5369Labels := by rfl

theorem canonical32568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32568 raw32568Labels = mixedMoment B node5469 node5469Labels := by
  calc
    _ = mixedMoment B node5469 node5469Labels := by rfl

theorem canonical32569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32569 raw32569Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw32569 raw32569Labels = mixedMoment B raw32569step0 raw32569step0Labels := by
      have hz : ∀ j, raw32569 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32569step0 = (fun i j => raw32569 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32569step0 raw32569; decide +kernel
      have hl : raw32569step0Labels = raw32569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32569 raw32569Labels permutation346 hz
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical32570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32570 raw32570Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw32570 raw32570Labels = mixedMoment B raw32570step0 raw32570step0Labels := by
      have hz : ∀ j, raw32570 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32570step0 = (fun i j => raw32570 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32570step0 raw32570; decide +kernel
      have hl : raw32570step0Labels = raw32570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32570 raw32570Labels permutation346 hz
    mixedMoment B raw32570step0 raw32570step0Labels = mixedMoment B raw32570step1 raw32570step1Labels := by
      have ha : raw32570step1 = (fun i j => raw32570step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32570step1 raw32570step0; decide +kernel
      have hl : raw32570step1Labels = raw32570step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32570step0 raw32570step0Labels permutation34 permutation2
    _ = mixedMoment B node5473 node5473Labels := by rfl

theorem canonical32571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32571 raw32571Labels = mixedMoment B node5474 node5474Labels := by
  calc
    mixedMoment B raw32571 raw32571Labels = mixedMoment B raw32571step0 raw32571step0Labels := by
      have hz : ∀ j, raw32571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32571step0 = (fun i j => raw32571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32571step0 raw32571; decide +kernel
      have hl : raw32571step0Labels = raw32571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32571 raw32571Labels permutation346 hz
    _ = mixedMoment B node5474 node5474Labels := by rfl

theorem canonical32572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32572 raw32572Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw32572 raw32572Labels = mixedMoment B raw32572step0 raw32572step0Labels := by
      have hz : ∀ j, raw32572 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32572step0 = (fun i j => raw32572 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32572step0 raw32572; decide +kernel
      have hl : raw32572step0Labels = raw32572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32572 raw32572Labels permutation346 hz
    mixedMoment B raw32572step0 raw32572step0Labels = mixedMoment B raw32572step1 raw32572step1Labels := by
      have ha : raw32572step1 = (fun i j => raw32572step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32572step1 raw32572step0; decide +kernel
      have hl : raw32572step1Labels = raw32572step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32572step0 raw32572step0Labels permutation32 permutation3
    mixedMoment B raw32572step1 raw32572step1Labels = mixedMoment B raw32572step2 raw32572step2Labels := by
      have ha : raw32572step2 = raw32572step1 := by apply Matrix.ext; unfold raw32572step2 raw32572step1; decide +kernel
      have hl : raw32572step1Labels = labelEmbedding6 ∘ raw32572step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32572step1 raw32572step1Labels raw32572step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4474 node4474Labels := by rfl

theorem canonical32573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32573 raw32573Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw32573 raw32573Labels = mixedMoment B raw32573step0 raw32573step0Labels := by
      have ha : raw32573step0 = (fun i j => raw32573 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32573step0 raw32573; decide +kernel
      have hl : raw32573step0Labels = raw32573Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32573 raw32573Labels permutation176 permutation3
    mixedMoment B raw32573step0 raw32573step0Labels = mixedMoment B raw32573step1 raw32573step1Labels := by
      have ha : raw32573step1 = raw32573step0 := by apply Matrix.ext; unfold raw32573step1 raw32573step0; decide +kernel
      have hl : raw32573step0Labels = labelEmbedding6 ∘ raw32573step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32573step0 raw32573step0Labels raw32573step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5085 node5085Labels := by rfl

theorem canonical32574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32574 raw32574Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw32574 raw32574Labels = mixedMoment B raw32574step0 raw32574step0Labels := by
      have hz : ∀ j, raw32574 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32574step0 = (fun i j => raw32574 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32574step0 raw32574; decide +kernel
      have hl : raw32574step0Labels = raw32574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32574 raw32574Labels permutation346 hz
    mixedMoment B raw32574step0 raw32574step0Labels = mixedMoment B raw32574step1 raw32574step1Labels := by
      have ha : raw32574step1 = (fun i j => raw32574step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32574step1 raw32574step0; decide +kernel
      have hl : raw32574step1Labels = raw32574step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32574step0 raw32574step0Labels permutation38 permutation3
    mixedMoment B raw32574step1 raw32574step1Labels = mixedMoment B raw32574step2 raw32574step2Labels := by
      have ha : raw32574step2 = raw32574step1 := by apply Matrix.ext; unfold raw32574step2 raw32574step1; decide +kernel
      have hl : raw32574step1Labels = labelEmbedding6 ∘ raw32574step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32574step1 raw32574step1Labels raw32574step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

theorem canonical32575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32575 raw32575Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw32575 raw32575Labels = mixedMoment B raw32575step0 raw32575step0Labels := by
      have hz : ∀ j, raw32575 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32575step0 = (fun i j => raw32575 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32575step0 raw32575; decide +kernel
      have hl : raw32575step0Labels = raw32575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32575 raw32575Labels permutation346 hz
    mixedMoment B raw32575step0 raw32575step0Labels = mixedMoment B raw32575step1 raw32575step1Labels := by
      have ha : raw32575step1 = (fun i j => raw32575step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32575step1 raw32575step0; decide +kernel
      have hl : raw32575step1Labels = raw32575step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32575step0 raw32575step0Labels permutation44 permutation3
    mixedMoment B raw32575step1 raw32575step1Labels = mixedMoment B raw32575step2 raw32575step2Labels := by
      have ha : raw32575step2 = raw32575step1 := by apply Matrix.ext; unfold raw32575step2 raw32575step1; decide +kernel
      have hl : raw32575step1Labels = labelEmbedding6 ∘ raw32575step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32575step1 raw32575step1Labels raw32575step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

theorem canonical32576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32576 raw32576Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw32576 raw32576Labels = mixedMoment B raw32576step0 raw32576step0Labels := by
      have hz : ∀ j, raw32576 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32576step0 = (fun i j => raw32576 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32576step0 raw32576; decide +kernel
      have hl : raw32576step0Labels = raw32576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32576 raw32576Labels permutation346 hz
    mixedMoment B raw32576step0 raw32576step0Labels = mixedMoment B raw32576step1 raw32576step1Labels := by
      have ha : raw32576step1 = (fun i j => raw32576step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32576step1 raw32576step0; decide +kernel
      have hl : raw32576step1Labels = raw32576step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32576step0 raw32576step0Labels permutation32 permutation3
    mixedMoment B raw32576step1 raw32576step1Labels = mixedMoment B raw32576step2 raw32576step2Labels := by
      have ha : raw32576step2 = raw32576step1 := by apply Matrix.ext; unfold raw32576step2 raw32576step1; decide +kernel
      have hl : raw32576step1Labels = labelEmbedding6 ∘ raw32576step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32576step1 raw32576step1Labels raw32576step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

theorem canonical32577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32577 raw32577Labels = mixedMoment B node4364 node4364Labels := by
  calc
    mixedMoment B raw32577 raw32577Labels = mixedMoment B raw32577step0 raw32577step0Labels := by
      have ha : raw32577step0 = (fun i j => raw32577 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32577step0 raw32577; decide +kernel
      have hl : raw32577step0Labels = raw32577Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32577 raw32577Labels permutation160 permutation3
    mixedMoment B raw32577step0 raw32577step0Labels = mixedMoment B raw32577step1 raw32577step1Labels := by
      have ha : raw32577step1 = raw32577step0 := by apply Matrix.ext; unfold raw32577step1 raw32577step0; decide +kernel
      have hl : raw32577step0Labels = labelEmbedding6 ∘ raw32577step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32577step0 raw32577step0Labels raw32577step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4364 node4364Labels := by rfl

theorem canonical32578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32578 raw32578Labels = mixedMoment B node4968 node4968Labels := by
  calc
    mixedMoment B raw32578 raw32578Labels = mixedMoment B raw32578step0 raw32578step0Labels := by
      have ha : raw32578step0 = (fun i j => raw32578 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32578step0 raw32578; decide +kernel
      have hl : raw32578step0Labels = raw32578Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32578 raw32578Labels permutation160 permutation3
    mixedMoment B raw32578step0 raw32578step0Labels = mixedMoment B raw32578step1 raw32578step1Labels := by
      have ha : raw32578step1 = raw32578step0 := by apply Matrix.ext; unfold raw32578step1 raw32578step0; decide +kernel
      have hl : raw32578step0Labels = labelEmbedding6 ∘ raw32578step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32578step0 raw32578step0Labels raw32578step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4968 node4968Labels := by rfl

theorem canonical32579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32579 raw32579Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw32579 raw32579Labels = mixedMoment B raw32579step0 raw32579step0Labels := by
      have ha : raw32579step0 = (fun i j => raw32579 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32579step0 raw32579; decide +kernel
      have hl : raw32579step0Labels = raw32579Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32579 raw32579Labels permutation160 permutation3
    mixedMoment B raw32579step0 raw32579step0Labels = mixedMoment B raw32579step1 raw32579step1Labels := by
      have ha : raw32579step1 = raw32579step0 := by apply Matrix.ext; unfold raw32579step1 raw32579step0; decide +kernel
      have hl : raw32579step0Labels = labelEmbedding6 ∘ raw32579step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32579step0 raw32579step0Labels raw32579step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5185 node5185Labels := by rfl

theorem canonical32580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32580 raw32580Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw32580 raw32580Labels = mixedMoment B raw32580step0 raw32580step0Labels := by
      have ha : raw32580step0 = (fun i j => raw32580 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32580step0 raw32580; decide +kernel
      have hl : raw32580step0Labels = raw32580Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32580 raw32580Labels permutation166 permutation3
    mixedMoment B raw32580step0 raw32580step0Labels = mixedMoment B raw32580step1 raw32580step1Labels := by
      have ha : raw32580step1 = raw32580step0 := by apply Matrix.ext; unfold raw32580step1 raw32580step0; decide +kernel
      have hl : raw32580step0Labels = labelEmbedding6 ∘ raw32580step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32580step0 raw32580step0Labels raw32580step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5185 node5185Labels := by rfl

theorem canonical32581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32581 raw32581Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw32581 raw32581Labels = mixedMoment B raw32581step0 raw32581step0Labels := by
      have ha : raw32581step0 = (fun i j => raw32581 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32581step0 raw32581; decide +kernel
      have hl : raw32581step0Labels = raw32581Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32581 raw32581Labels permutation161 permutation3
    mixedMoment B raw32581step0 raw32581step0Labels = mixedMoment B raw32581step1 raw32581step1Labels := by
      have ha : raw32581step1 = raw32581step0 := by apply Matrix.ext; unfold raw32581step1 raw32581step0; decide +kernel
      have hl : raw32581step0Labels = labelEmbedding6 ∘ raw32581step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32581step0 raw32581step0Labels raw32581step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5202 node5202Labels := by rfl

theorem canonical32582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32582 raw32582Labels = mixedMoment B node4369 node4369Labels := by
  calc
    mixedMoment B raw32582 raw32582Labels = mixedMoment B raw32582step0 raw32582step0Labels := by
      have hz : ∀ j, raw32582 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32582step0 = (fun i j => raw32582 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32582step0 raw32582; decide +kernel
      have hl : raw32582step0Labels = raw32582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32582 raw32582Labels permutation346 hz
    mixedMoment B raw32582step0 raw32582step0Labels = mixedMoment B raw32582step1 raw32582step1Labels := by
      have ha : raw32582step1 = (fun i j => raw32582step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32582step1 raw32582step0; decide +kernel
      have hl : raw32582step1Labels = raw32582step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32582step0 raw32582step0Labels permutation34 permutation3
    mixedMoment B raw32582step1 raw32582step1Labels = mixedMoment B raw32582step2 raw32582step2Labels := by
      have ha : raw32582step2 = raw32582step1 := by apply Matrix.ext; unfold raw32582step2 raw32582step1; decide +kernel
      have hl : raw32582step1Labels = labelEmbedding6 ∘ raw32582step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32582step1 raw32582step1Labels raw32582step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4369 node4369Labels := by rfl

theorem canonical32583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32583 raw32583Labels = mixedMoment B node4974 node4974Labels := by
  calc
    mixedMoment B raw32583 raw32583Labels = mixedMoment B raw32583step0 raw32583step0Labels := by
      have hz : ∀ j, raw32583 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32583step0 = (fun i j => raw32583 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32583step0 raw32583; decide +kernel
      have hl : raw32583step0Labels = raw32583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32583 raw32583Labels permutation346 hz
    mixedMoment B raw32583step0 raw32583step0Labels = mixedMoment B raw32583step1 raw32583step1Labels := by
      have ha : raw32583step1 = (fun i j => raw32583step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32583step1 raw32583step0; decide +kernel
      have hl : raw32583step1Labels = raw32583step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32583step0 raw32583step0Labels permutation34 permutation3
    mixedMoment B raw32583step1 raw32583step1Labels = mixedMoment B raw32583step2 raw32583step2Labels := by
      have ha : raw32583step2 = raw32583step1 := by apply Matrix.ext; unfold raw32583step2 raw32583step1; decide +kernel
      have hl : raw32583step1Labels = labelEmbedding6 ∘ raw32583step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32583step1 raw32583step1Labels raw32583step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4974 node4974Labels := by rfl

theorem canonical32584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32584 raw32584Labels = mixedMoment B node5043 node5043Labels := by
  calc
    mixedMoment B raw32584 raw32584Labels = mixedMoment B raw32584step0 raw32584step0Labels := by
      have ha : raw32584step0 = (fun i j => raw32584 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32584step0 raw32584; decide +kernel
      have hl : raw32584step0Labels = raw32584Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32584 raw32584Labels permutation178 permutation3
    mixedMoment B raw32584step0 raw32584step0Labels = mixedMoment B raw32584step1 raw32584step1Labels := by
      have ha : raw32584step1 = raw32584step0 := by apply Matrix.ext; unfold raw32584step1 raw32584step0; decide +kernel
      have hl : raw32584step0Labels = labelEmbedding6 ∘ raw32584step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32584step0 raw32584step0Labels raw32584step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5043 node5043Labels := by rfl

theorem canonical32585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32585 raw32585Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw32585 raw32585Labels = mixedMoment B raw32585step0 raw32585step0Labels := by
      have hz : ∀ j, raw32585 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32585step0 = (fun i j => raw32585 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32585step0 raw32585; decide +kernel
      have hl : raw32585step0Labels = raw32585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32585 raw32585Labels permutation346 hz
    mixedMoment B raw32585step0 raw32585step0Labels = mixedMoment B raw32585step1 raw32585step1Labels := by
      have ha : raw32585step1 = (fun i j => raw32585step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32585step1 raw32585step0; decide +kernel
      have hl : raw32585step1Labels = raw32585step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32585step0 raw32585step0Labels permutation34 permutation3
    mixedMoment B raw32585step1 raw32585step1Labels = mixedMoment B raw32585step2 raw32585step2Labels := by
      have ha : raw32585step2 = raw32585step1 := by apply Matrix.ext; unfold raw32585step2 raw32585step1; decide +kernel
      have hl : raw32585step1Labels = labelEmbedding6 ∘ raw32585step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32585step1 raw32585step1Labels raw32585step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5189 node5189Labels := by rfl

theorem canonical32586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32586 raw32586Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw32586 raw32586Labels = mixedMoment B raw32586step0 raw32586step0Labels := by
      have hz : ∀ j, raw32586 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32586step0 = (fun i j => raw32586 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32586step0 raw32586; decide +kernel
      have hl : raw32586step0Labels = raw32586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32586 raw32586Labels permutation346 hz
    mixedMoment B raw32586step0 raw32586step0Labels = mixedMoment B raw32586step1 raw32586step1Labels := by
      have ha : raw32586step1 = (fun i j => raw32586step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32586step1 raw32586step0; decide +kernel
      have hl : raw32586step1Labels = raw32586step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32586step0 raw32586step0Labels permutation35 permutation3
    mixedMoment B raw32586step1 raw32586step1Labels = mixedMoment B raw32586step2 raw32586step2Labels := by
      have ha : raw32586step2 = raw32586step1 := by apply Matrix.ext; unfold raw32586step2 raw32586step1; decide +kernel
      have hl : raw32586step1Labels = labelEmbedding6 ∘ raw32586step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32586step1 raw32586step1Labels raw32586step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5203 node5203Labels := by rfl

theorem canonical32587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32587 raw32587Labels = mixedMoment B node4369 node4369Labels := by
  calc
    mixedMoment B raw32587 raw32587Labels = mixedMoment B raw32587step0 raw32587step0Labels := by
      have hz : ∀ j, raw32587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32587step0 = (fun i j => raw32587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32587step0 raw32587; decide +kernel
      have hl : raw32587step0Labels = raw32587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32587 raw32587Labels permutation346 hz
    mixedMoment B raw32587step0 raw32587step0Labels = mixedMoment B raw32587step1 raw32587step1Labels := by
      have ha : raw32587step1 = (fun i j => raw32587step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32587step1 raw32587step0; decide +kernel
      have hl : raw32587step1Labels = raw32587step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32587step0 raw32587step0Labels permutation32 permutation3
    mixedMoment B raw32587step1 raw32587step1Labels = mixedMoment B raw32587step2 raw32587step2Labels := by
      have ha : raw32587step2 = raw32587step1 := by apply Matrix.ext; unfold raw32587step2 raw32587step1; decide +kernel
      have hl : raw32587step1Labels = labelEmbedding6 ∘ raw32587step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32587step1 raw32587step1Labels raw32587step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4369 node4369Labels := by rfl

theorem canonical32588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32588 raw32588Labels = mixedMoment B node4974 node4974Labels := by
  calc
    mixedMoment B raw32588 raw32588Labels = mixedMoment B raw32588step0 raw32588step0Labels := by
      have hz : ∀ j, raw32588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32588step0 = (fun i j => raw32588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32588step0 raw32588; decide +kernel
      have hl : raw32588step0Labels = raw32588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32588 raw32588Labels permutation346 hz
    mixedMoment B raw32588step0 raw32588step0Labels = mixedMoment B raw32588step1 raw32588step1Labels := by
      have ha : raw32588step1 = (fun i j => raw32588step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32588step1 raw32588step0; decide +kernel
      have hl : raw32588step1Labels = raw32588step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32588step0 raw32588step0Labels permutation32 permutation3
    mixedMoment B raw32588step1 raw32588step1Labels = mixedMoment B raw32588step2 raw32588step2Labels := by
      have ha : raw32588step2 = raw32588step1 := by apply Matrix.ext; unfold raw32588step2 raw32588step1; decide +kernel
      have hl : raw32588step1Labels = labelEmbedding6 ∘ raw32588step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32588step1 raw32588step1Labels raw32588step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4974 node4974Labels := by rfl

theorem canonical32589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32589 raw32589Labels = mixedMoment B node5043 node5043Labels := by
  calc
    mixedMoment B raw32589 raw32589Labels = mixedMoment B raw32589step0 raw32589step0Labels := by
      have ha : raw32589step0 = (fun i j => raw32589 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32589step0 raw32589; decide +kernel
      have hl : raw32589step0Labels = raw32589Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32589 raw32589Labels permutation176 permutation3
    mixedMoment B raw32589step0 raw32589step0Labels = mixedMoment B raw32589step1 raw32589step1Labels := by
      have ha : raw32589step1 = raw32589step0 := by apply Matrix.ext; unfold raw32589step1 raw32589step0; decide +kernel
      have hl : raw32589step0Labels = labelEmbedding6 ∘ raw32589step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32589step0 raw32589step0Labels raw32589step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5043 node5043Labels := by rfl

theorem canonical32590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32590 raw32590Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw32590 raw32590Labels = mixedMoment B raw32590step0 raw32590step0Labels := by
      have hz : ∀ j, raw32590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32590step0 = (fun i j => raw32590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32590step0 raw32590; decide +kernel
      have hl : raw32590step0Labels = raw32590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32590 raw32590Labels permutation346 hz
    mixedMoment B raw32590step0 raw32590step0Labels = mixedMoment B raw32590step1 raw32590step1Labels := by
      have ha : raw32590step1 = (fun i j => raw32590step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32590step1 raw32590step0; decide +kernel
      have hl : raw32590step1Labels = raw32590step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32590step0 raw32590step0Labels permutation32 permutation3
    mixedMoment B raw32590step1 raw32590step1Labels = mixedMoment B raw32590step2 raw32590step2Labels := by
      have ha : raw32590step2 = raw32590step1 := by apply Matrix.ext; unfold raw32590step2 raw32590step1; decide +kernel
      have hl : raw32590step1Labels = labelEmbedding6 ∘ raw32590step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32590step1 raw32590step1Labels raw32590step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5189 node5189Labels := by rfl

theorem canonical32591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32591 raw32591Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw32591 raw32591Labels = mixedMoment B raw32591step0 raw32591step0Labels := by
      have hz : ∀ j, raw32591 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32591step0 = (fun i j => raw32591 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32591step0 raw32591; decide +kernel
      have hl : raw32591step0Labels = raw32591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32591 raw32591Labels permutation346 hz
    mixedMoment B raw32591step0 raw32591step0Labels = mixedMoment B raw32591step1 raw32591step1Labels := by
      have ha : raw32591step1 = (fun i j => raw32591step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32591step1 raw32591step0; decide +kernel
      have hl : raw32591step1Labels = raw32591step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32591step0 raw32591step0Labels permutation33 permutation3
    mixedMoment B raw32591step1 raw32591step1Labels = mixedMoment B raw32591step2 raw32591step2Labels := by
      have ha : raw32591step2 = raw32591step1 := by apply Matrix.ext; unfold raw32591step2 raw32591step1; decide +kernel
      have hl : raw32591step1Labels = labelEmbedding6 ∘ raw32591step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32591step1 raw32591step1Labels raw32591step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5203 node5203Labels := by rfl

theorem canonical32592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32592 raw32592Labels = mixedMoment B node4365 node4365Labels := by
  calc
    mixedMoment B raw32592 raw32592Labels = mixedMoment B raw32592step0 raw32592step0Labels := by
      have hz : ∀ j, raw32592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32592step0 = (fun i j => raw32592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32592step0 raw32592; decide +kernel
      have hl : raw32592step0Labels = raw32592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32592 raw32592Labels permutation346 hz
    mixedMoment B raw32592step0 raw32592step0Labels = mixedMoment B raw32592step1 raw32592step1Labels := by
      have ha : raw32592step1 = (fun i j => raw32592step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32592step1 raw32592step0; decide +kernel
      have hl : raw32592step1Labels = raw32592step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32592step0 raw32592step0Labels permutation32 permutation3
    mixedMoment B raw32592step1 raw32592step1Labels = mixedMoment B raw32592step2 raw32592step2Labels := by
      have ha : raw32592step2 = raw32592step1 := by apply Matrix.ext; unfold raw32592step2 raw32592step1; decide +kernel
      have hl : raw32592step1Labels = labelEmbedding6 ∘ raw32592step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32592step1 raw32592step1Labels raw32592step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4365 node4365Labels := by rfl

theorem canonical32593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32593 raw32593Labels = mixedMoment B node4970 node4970Labels := by
  calc
    mixedMoment B raw32593 raw32593Labels = mixedMoment B raw32593step0 raw32593step0Labels := by
      have hz : ∀ j, raw32593 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32593step0 = (fun i j => raw32593 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32593step0 raw32593; decide +kernel
      have hl : raw32593step0Labels = raw32593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32593 raw32593Labels permutation346 hz
    mixedMoment B raw32593step0 raw32593step0Labels = mixedMoment B raw32593step1 raw32593step1Labels := by
      have ha : raw32593step1 = (fun i j => raw32593step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32593step1 raw32593step0; decide +kernel
      have hl : raw32593step1Labels = raw32593step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32593step0 raw32593step0Labels permutation32 permutation3
    mixedMoment B raw32593step1 raw32593step1Labels = mixedMoment B raw32593step2 raw32593step2Labels := by
      have ha : raw32593step2 = raw32593step1 := by apply Matrix.ext; unfold raw32593step2 raw32593step1; decide +kernel
      have hl : raw32593step1Labels = labelEmbedding6 ∘ raw32593step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32593step1 raw32593step1Labels raw32593step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4970 node4970Labels := by rfl

theorem canonical32594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32594 raw32594Labels = mixedMoment B node5041 node5041Labels := by
  calc
    mixedMoment B raw32594 raw32594Labels = mixedMoment B raw32594step0 raw32594step0Labels := by
      have ha : raw32594step0 = (fun i j => raw32594 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32594step0 raw32594; decide +kernel
      have hl : raw32594step0Labels = raw32594Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32594 raw32594Labels permutation176 permutation3
    mixedMoment B raw32594step0 raw32594step0Labels = mixedMoment B raw32594step1 raw32594step1Labels := by
      have ha : raw32594step1 = raw32594step0 := by apply Matrix.ext; unfold raw32594step1 raw32594step0; decide +kernel
      have hl : raw32594step0Labels = labelEmbedding6 ∘ raw32594step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32594step0 raw32594step0Labels raw32594step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5041 node5041Labels := by rfl

theorem canonical32595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32595 raw32595Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw32595 raw32595Labels = mixedMoment B raw32595step0 raw32595step0Labels := by
      have hz : ∀ j, raw32595 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32595step0 = (fun i j => raw32595 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32595step0 raw32595; decide +kernel
      have hl : raw32595step0Labels = raw32595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32595 raw32595Labels permutation346 hz
    mixedMoment B raw32595step0 raw32595step0Labels = mixedMoment B raw32595step1 raw32595step1Labels := by
      have ha : raw32595step1 = (fun i j => raw32595step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32595step1 raw32595step0; decide +kernel
      have hl : raw32595step1Labels = raw32595step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32595step0 raw32595step0Labels permutation151 permutation3
    mixedMoment B raw32595step1 raw32595step1Labels = mixedMoment B raw32595step2 raw32595step2Labels := by
      have ha : raw32595step2 = -raw32595step1 := by apply Matrix.ext; change ∀ i j, raw32595step2 i j = -(raw32595step1 i j); unfold raw32595step2 raw32595step1; decide +kernel
      have hl : raw32595step2Labels = raw32595step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32595step2 raw32595step2Labels = mixedMoment B raw32595step3 raw32595step3Labels := by
      have ha : raw32595step3 = raw32595step2 := by apply Matrix.ext; unfold raw32595step3 raw32595step2; decide +kernel
      have hl : raw32595step2Labels = labelEmbedding6 ∘ raw32595step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32595step2 raw32595step2Labels raw32595step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5147 node5147Labels := by rfl

theorem canonical32596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32596 raw32596Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw32596 raw32596Labels = mixedMoment B raw32596step0 raw32596step0Labels := by
      have hz : ∀ j, raw32596 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32596step0 = (fun i j => raw32596 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32596step0 raw32596; decide +kernel
      have hl : raw32596step0Labels = raw32596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32596 raw32596Labels permutation346 hz
    mixedMoment B raw32596step0 raw32596step0Labels = mixedMoment B raw32596step1 raw32596step1Labels := by
      have ha : raw32596step1 = (fun i j => raw32596step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32596step1 raw32596step0; decide +kernel
      have hl : raw32596step1Labels = raw32596step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32596step0 raw32596step0Labels permutation145 permutation3
    mixedMoment B raw32596step1 raw32596step1Labels = mixedMoment B raw32596step2 raw32596step2Labels := by
      have ha : raw32596step2 = -raw32596step1 := by apply Matrix.ext; change ∀ i j, raw32596step2 i j = -(raw32596step1 i j); unfold raw32596step2 raw32596step1; decide +kernel
      have hl : raw32596step2Labels = raw32596step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32596step2 raw32596step2Labels = mixedMoment B raw32596step3 raw32596step3Labels := by
      have ha : raw32596step3 = raw32596step2 := by apply Matrix.ext; unfold raw32596step3 raw32596step2; decide +kernel
      have hl : raw32596step2Labels = labelEmbedding6 ∘ raw32596step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32596step2 raw32596step2Labels raw32596step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5147 node5147Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4968 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4968 node4968Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2809 node2809Labels + mixedMoment B node3587 node3587Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1944 singletonSmall4968
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4968) = raw1944Labels := by decide +kernel
  rw [hl, canonical1944 B hB] at h
  have hc0 : mixedMoment B raw1944 (Fin.cases (0 : Fin 2) singletonSmall4968) =
      mixedMoment B node2809 node2809Labels := by
    have ha : raw1944 = raw1945 := by apply Matrix.ext; unfold raw1944 raw1945; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4968 = raw1945Labels := by decide +kernel
    rw [ha, hj, canonical1945 B hB]
  have hc1 : mixedMoment B raw1944 (Fin.cases (1 : Fin 2) singletonSmall4968) =
      mixedMoment B node3587 node3587Labels := by
    have ha : raw1944 = raw1946 := by apply Matrix.ext; unfold raw1944 raw1946; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4968 = raw1946Labels := by decide +kernel
    rw [ha, hj, canonical1946 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4970 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4970 node4970Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2815 node2815Labels + mixedMoment B node3588 node3588Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1950 singletonSmall4970
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4970) = raw1950Labels := by decide +kernel
  rw [hl, canonical1950 B hB] at h
  have hc0 : mixedMoment B raw1950 (Fin.cases (0 : Fin 2) singletonSmall4970) =
      mixedMoment B node2815 node2815Labels := by
    have ha : raw1950 = raw1951 := by apply Matrix.ext; unfold raw1950 raw1951; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4970 = raw1951Labels := by decide +kernel
    rw [ha, hj, canonical1951 B hB]
  have hc1 : mixedMoment B raw1950 (Fin.cases (1 : Fin 2) singletonSmall4970) =
      mixedMoment B node3588 node3588Labels := by
    have ha : raw1950 = raw1952 := by apply Matrix.ext; unfold raw1950 raw1952; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4970 = raw1952Labels := by decide +kernel
    rw [ha, hj, canonical1952 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4974 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4974 node4974Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2818 node2818Labels + mixedMoment B node3592 node3592Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1962 singletonSmall4974
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4974) = raw1962Labels := by decide +kernel
  rw [hl, canonical1962 B hB] at h
  have hc0 : mixedMoment B raw1962 (Fin.cases (0 : Fin 2) singletonSmall4974) =
      mixedMoment B node2818 node2818Labels := by
    have ha : raw1962 = raw1963 := by apply Matrix.ext; unfold raw1962 raw1963; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4974 = raw1963Labels := by decide +kernel
    rw [ha, hj, canonical1963 B hB]
  have hc1 : mixedMoment B raw1962 (Fin.cases (1 : Fin 2) singletonSmall4974) =
      mixedMoment B node3592 node3592Labels := by
    have ha : raw1962 = raw1964 := by apply Matrix.ext; unfold raw1962 raw1964; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4974 = raw1964Labels := by decide +kernel
    rw [ha, hj, canonical1964 B hB]
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

theorem singleton5202 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5202 node5202Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2880 node2880Labels + mixedMoment B node3617 node3617Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2226 singletonSmall5202
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5202) = raw2226Labels := by decide +kernel
  rw [hl, canonical2226 B hB] at h
  have hc0 : mixedMoment B raw2226 (Fin.cases (0 : Fin 2) singletonSmall5202) =
      mixedMoment B node2880 node2880Labels := by
    have ha : raw2226 = raw2227 := by apply Matrix.ext; unfold raw2226 raw2227; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5202 = raw2227Labels := by decide +kernel
    rw [ha, hj, canonical2227 B hB]
  have hc1 : mixedMoment B raw2226 (Fin.cases (1 : Fin 2) singletonSmall5202) =
      mixedMoment B node3617 node3617Labels := by
    have ha : raw2226 = raw2228 := by apply Matrix.ext; unfold raw2226 raw2228; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5202 = raw2228Labels := by decide +kernel
    rw [ha, hj, canonical2228 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton5203 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5203 node5203Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node2884 node2884Labels + mixedMoment B node3621 node3621Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2229 singletonSmall5203
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5203) = raw2229Labels := by decide +kernel
  rw [hl, canonical2229 B hB] at h
  have hc0 : mixedMoment B raw2229 (Fin.cases (0 : Fin 2) singletonSmall5203) =
      mixedMoment B node2884 node2884Labels := by
    have ha : raw2229 = raw2230 := by apply Matrix.ext; unfold raw2229 raw2230; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5203 = raw2230Labels := by decide +kernel
    rw [ha, hj, canonical2230 B hB]
  have hc1 : mixedMoment B raw2229 (Fin.cases (1 : Fin 2) singletonSmall5203) =
      mixedMoment B node3621 node3621Labels := by
    have ha : raw2229 = raw2231 := by apply Matrix.ext; unfold raw2229 raw2231; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5203 = raw2231Labels := by decide +kernel
    rw [ha, hj, canonical2231 B hB]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton5469 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node5469 node5469Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node3945 node3945Labels + mixedMoment B node3952 node3952Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw2583 singletonSmall5469
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall5469) = raw2583Labels := by decide +kernel
  rw [hl, canonical2583 B hB] at h
  have hc0 : mixedMoment B raw2583 (Fin.cases (0 : Fin 2) singletonSmall5469) =
      mixedMoment B node3945 node3945Labels := by
    have ha : raw2583 = raw2584 := by apply Matrix.ext; unfold raw2583 raw2584; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall5469 = raw2584Labels := by decide +kernel
    rw [ha, hj, canonical2584 B hB]
  have hc1 : mixedMoment B raw2583 (Fin.cases (1 : Fin 2) singletonSmall5469) =
      mixedMoment B node3952 node3952Labels := by
    have ha : raw2583 = raw2585 := by apply Matrix.ext; unfold raw2583 raw2585; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall5469 = raw2585Labels := by decide +kernel
    rw [ha, hj, canonical2585 B hB]
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

theorem zero5474 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5474 node5474Labels = 0 := by
  exact mixedMoment_order_one B hB node5474 node5474Labels 1
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

theorem sound2809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2809 node2809Labels = Sparse.eval nodeValue2809 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2809) = mixedMoment B node2809 node2809Labels := rfl
  simpa [nodeValue2809, Sparse.eval] using hc.symm

theorem sound2815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2815 node2815Labels = Sparse.eval nodeValue2815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2815) = mixedMoment B node2815 node2815Labels := rfl
  simpa [nodeValue2815, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2818 node2818Labels = Sparse.eval nodeValue2818 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2818) = mixedMoment B node2818 node2818Labels := rfl
  simpa [nodeValue2818, Sparse.eval] using hc.symm

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

theorem sound2880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2880 node2880Labels = Sparse.eval nodeValue2880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2880) = mixedMoment B node2880 node2880Labels := rfl
  simpa [nodeValue2880, Sparse.eval] using hc.symm

theorem sound2884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2884 node2884Labels = Sparse.eval nodeValue2884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2884) = mixedMoment B node2884 node2884Labels := rfl
  simpa [nodeValue2884, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3587 node3587Labels = Sparse.eval nodeValue3587 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3587) = mixedMoment B node3587 node3587Labels := rfl
  simpa [nodeValue3587, Sparse.eval] using hc.symm

theorem sound3588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3588 node3588Labels = Sparse.eval nodeValue3588 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3588) = mixedMoment B node3588 node3588Labels := rfl
  simpa [nodeValue3588, Sparse.eval] using hc.symm

theorem sound3592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3592 node3592Labels = Sparse.eval nodeValue3592 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3592) = mixedMoment B node3592 node3592Labels := rfl
  simpa [nodeValue3592, Sparse.eval] using hc.symm

theorem sound3617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3617 node3617Labels = Sparse.eval nodeValue3617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3617) = mixedMoment B node3617 node3617Labels := rfl
  simpa [nodeValue3617, Sparse.eval] using hc.symm

theorem sound3619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3619 node3619Labels = Sparse.eval nodeValue3619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3619) = mixedMoment B node3619 node3619Labels := rfl
  simpa [nodeValue3619, Sparse.eval] using hc.symm

theorem sound3621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3621 node3621Labels = Sparse.eval nodeValue3621 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3621) = mixedMoment B node3621 node3621Labels := rfl
  simpa [nodeValue3621, Sparse.eval] using hc.symm

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

theorem sound3945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3945 node3945Labels = Sparse.eval nodeValue3945 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3945) = mixedMoment B node3945 node3945Labels := rfl
  simpa [nodeValue3945, Sparse.eval] using hc.symm

theorem sound3952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3952 node3952Labels = Sparse.eval nodeValue3952 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3952) = mixedMoment B node3952 node3952Labels := rfl
  simpa [nodeValue3952, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4364 node4364Labels = Sparse.eval nodeValue4364 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4364) = mixedMoment B node4364 node4364Labels := rfl
  simpa [nodeValue4364, Sparse.eval] using hc.symm

theorem sound4365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4365 node4365Labels = Sparse.eval nodeValue4365 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4365) = mixedMoment B node4365 node4365Labels := rfl
  simpa [nodeValue4365, Sparse.eval] using hc.symm

theorem sound4369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4369 node4369Labels = Sparse.eval nodeValue4369 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4369) = mixedMoment B node4369 node4369Labels := rfl
  simpa [nodeValue4369, Sparse.eval] using hc.symm

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

theorem sound4474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4474 node4474Labels = Sparse.eval nodeValue4474 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4474) = mixedMoment B node4474 node4474Labels := rfl
  simpa [nodeValue4474, Sparse.eval] using hc.symm

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

theorem sound4968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4968 node4968Labels = Sparse.eval nodeValue4968 (mixedVector B) := by
  have h := singleton4968 B _hB
  rw [sound2809 B _hB _hF, sound3587 B _hB _hF] at h
  norm_num [nodeValue4968, nodeValue2809, nodeValue3587, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4970 node4970Labels = Sparse.eval nodeValue4970 (mixedVector B) := by
  have h := singleton4970 B _hB
  rw [sound2815 B _hB _hF, sound3588 B _hB _hF] at h
  norm_num [nodeValue4970, nodeValue2815, nodeValue3588, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4974 node4974Labels = Sparse.eval nodeValue4974 (mixedVector B) := by
  have h := singleton4974 B _hB
  rw [sound2818 B _hB _hF, sound3592 B _hB _hF] at h
  norm_num [nodeValue4974, nodeValue2818, nodeValue3592, Sparse.eval] at h ⊢
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

theorem sound5041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5041 node5041Labels = Sparse.eval nodeValue5041 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5041) = mixedMoment B node5041 node5041Labels := rfl
  simpa [nodeValue5041, Sparse.eval] using hc.symm

theorem sound5043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5043 node5043Labels = Sparse.eval nodeValue5043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5043) = mixedMoment B node5043 node5043Labels := rfl
  simpa [nodeValue5043, Sparse.eval] using hc.symm

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

theorem sound5085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5085 node5085Labels = Sparse.eval nodeValue5085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5085) = mixedMoment B node5085 node5085Labels := rfl
  simpa [nodeValue5085, Sparse.eval] using hc.symm

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

theorem sound5147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5147 node5147Labels = Sparse.eval nodeValue5147 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5147) = mixedMoment B node5147 node5147Labels := rfl
  simpa [nodeValue5147, Sparse.eval] using hc.symm

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

theorem sound5189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5189 node5189Labels = Sparse.eval nodeValue5189 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5189) = mixedMoment B node5189 node5189Labels := rfl
  simpa [nodeValue5189, Sparse.eval] using hc.symm

theorem sound5202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5202 node5202Labels = Sparse.eval nodeValue5202 (mixedVector B) := by
  have h := singleton5202 B _hB
  rw [sound2880 B _hB _hF, sound3617 B _hB _hF] at h
  norm_num [nodeValue5202, nodeValue2880, nodeValue3617, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound5203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5203 node5203Labels = Sparse.eval nodeValue5203 (mixedVector B) := by
  have h := singleton5203 B _hB
  rw [sound2884 B _hB _hF, sound3621 B _hB _hF] at h
  norm_num [nodeValue5203, nodeValue2884, nodeValue3621, Sparse.eval] at h ⊢
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

theorem sound5266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5266 node5266Labels = Sparse.eval nodeValue5266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5266) = mixedMoment B node5266 node5266Labels := rfl
  simpa [nodeValue5266, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero5369 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5369 node5369Labels = 0 := by
  exact mixedMoment_order_one B hB node5369 node5369Labels 1
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

theorem sound5369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5369 node5369Labels = Sparse.eval nodeValue5369 (mixedVector B) := by
  simpa only [nodeValue5369, Sparse.eval_nil] using zero5369 B _hB _hF

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

theorem sound5469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5469 node5469Labels = Sparse.eval nodeValue5469 (mixedVector B) := by
  have h := singleton5469 B _hB
  rw [sound3945 B _hB _hF, sound3952 B _hB _hF] at h
  norm_num [nodeValue5469, nodeValue3945, nodeValue3952, Sparse.eval] at h ⊢
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources74
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2382 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2382 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2382 + difference 0 1) (sourceB2382 + difference 1 0) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2382 + difference 0 1) (sourceB2382 + difference 1 0) sourceC2382) = raw32567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32567; decide +kernel
    rw [ha]
    exact (canonical32567 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2382 + difference 0 2) (sourceB2382 + difference 2 0) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA2382 + difference 0 2) (sourceB2382 + difference 2 0) sourceC2382) = raw32568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32568; decide +kernel
    rw [ha]
    exact (canonical32568 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2382 + difference 0 3) (sourceB2382 + difference 3 0) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA2382 + difference 0 3) (sourceB2382 + difference 3 0) sourceC2382) = raw32569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32569; decide +kernel
    rw [ha]
    exact (canonical32569 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2382 + difference 0 4) (sourceB2382 + difference 4 0) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA2382 + difference 0 4) (sourceB2382 + difference 4 0) sourceC2382) = raw32570 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32570; decide +kernel
    rw [ha]
    exact (canonical32570 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2382 + difference 0 5) (sourceB2382 + difference 5 0) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5474) := by
    have ha : (tripleCharges (sourceA2382 + difference 0 5) (sourceB2382 + difference 5 0) sourceC2382) = raw32571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32571; decide +kernel
    rw [ha]
    exact (canonical32571 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2382 + difference 1 0) (sourceB2382 + difference 0 1) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4474) := by
    have ha : (tripleCharges (sourceA2382 + difference 1 0) (sourceB2382 + difference 0 1) sourceC2382) = raw32572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32572; decide +kernel
    rw [ha]
    exact (canonical32572 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2382 + difference 1 2) (sourceB2382 + difference 2 1) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA2382 + difference 1 2) (sourceB2382 + difference 2 1) sourceC2382) = raw32573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32573; decide +kernel
    rw [ha]
    exact (canonical32573 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2382 + difference 1 3) (sourceB2382 + difference 3 1) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA2382 + difference 1 3) (sourceB2382 + difference 3 1) sourceC2382) = raw32574 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32574; decide +kernel
    rw [ha]
    exact (canonical32574 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2382 + difference 1 4) (sourceB2382 + difference 4 1) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA2382 + difference 1 4) (sourceB2382 + difference 4 1) sourceC2382) = raw32575 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32575; decide +kernel
    rw [ha]
    exact (canonical32575 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2382 + difference 1 5) (sourceB2382 + difference 5 1) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA2382 + difference 1 5) (sourceB2382 + difference 5 1) sourceC2382) = raw32576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32576; decide +kernel
    rw [ha]
    exact (canonical32576 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2382 + difference 2 0) (sourceB2382 + difference 0 2) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4364) := by
    have ha : (tripleCharges (sourceA2382 + difference 2 0) (sourceB2382 + difference 0 2) sourceC2382) = raw32577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32577; decide +kernel
    rw [ha]
    exact (canonical32577 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2382 + difference 2 1) (sourceB2382 + difference 1 2) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4968) := by
    have ha : (tripleCharges (sourceA2382 + difference 2 1) (sourceB2382 + difference 1 2) sourceC2382) = raw32578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32578; decide +kernel
    rw [ha]
    exact (canonical32578 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2382 + difference 2 3) (sourceB2382 + difference 3 2) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA2382 + difference 2 3) (sourceB2382 + difference 3 2) sourceC2382) = raw32579 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32579; decide +kernel
    rw [ha]
    exact (canonical32579 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2382 + difference 2 4) (sourceB2382 + difference 4 2) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA2382 + difference 2 4) (sourceB2382 + difference 4 2) sourceC2382) = raw32580 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32580; decide +kernel
    rw [ha]
    exact (canonical32580 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2382 + difference 2 5) (sourceB2382 + difference 5 2) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5202) := by
    have ha : (tripleCharges (sourceA2382 + difference 2 5) (sourceB2382 + difference 5 2) sourceC2382) = raw32581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32581; decide +kernel
    rw [ha]
    exact (canonical32581 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2382 + difference 3 0) (sourceB2382 + difference 0 3) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4369) := by
    have ha : (tripleCharges (sourceA2382 + difference 3 0) (sourceB2382 + difference 0 3) sourceC2382) = raw32582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32582; decide +kernel
    rw [ha]
    exact (canonical32582 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2382 + difference 3 1) (sourceB2382 + difference 1 3) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4974) := by
    have ha : (tripleCharges (sourceA2382 + difference 3 1) (sourceB2382 + difference 1 3) sourceC2382) = raw32583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32583; decide +kernel
    rw [ha]
    exact (canonical32583 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2382 + difference 3 2) (sourceB2382 + difference 2 3) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5043) := by
    have ha : (tripleCharges (sourceA2382 + difference 3 2) (sourceB2382 + difference 2 3) sourceC2382) = raw32584 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32584; decide +kernel
    rw [ha]
    exact (canonical32584 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2382 + difference 3 4) (sourceB2382 + difference 4 3) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA2382 + difference 3 4) (sourceB2382 + difference 4 3) sourceC2382) = raw32585 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32585; decide +kernel
    rw [ha]
    exact (canonical32585 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2382 + difference 3 5) (sourceB2382 + difference 5 3) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA2382 + difference 3 5) (sourceB2382 + difference 5 3) sourceC2382) = raw32586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32586; decide +kernel
    rw [ha]
    exact (canonical32586 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2382 + difference 4 0) (sourceB2382 + difference 0 4) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4369) := by
    have ha : (tripleCharges (sourceA2382 + difference 4 0) (sourceB2382 + difference 0 4) sourceC2382) = raw32587 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32587; decide +kernel
    rw [ha]
    exact (canonical32587 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2382 + difference 4 1) (sourceB2382 + difference 1 4) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4974) := by
    have ha : (tripleCharges (sourceA2382 + difference 4 1) (sourceB2382 + difference 1 4) sourceC2382) = raw32588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32588; decide +kernel
    rw [ha]
    exact (canonical32588 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2382 + difference 4 2) (sourceB2382 + difference 2 4) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5043) := by
    have ha : (tripleCharges (sourceA2382 + difference 4 2) (sourceB2382 + difference 2 4) sourceC2382) = raw32589 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32589; decide +kernel
    rw [ha]
    exact (canonical32589 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2382 + difference 4 3) (sourceB2382 + difference 3 4) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA2382 + difference 4 3) (sourceB2382 + difference 3 4) sourceC2382) = raw32590 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32590; decide +kernel
    rw [ha]
    exact (canonical32590 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2382 + difference 4 5) (sourceB2382 + difference 5 4) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA2382 + difference 4 5) (sourceB2382 + difference 5 4) sourceC2382) = raw32591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32591; decide +kernel
    rw [ha]
    exact (canonical32591 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2382 + difference 5 0) (sourceB2382 + difference 0 5) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4365) := by
    have ha : (tripleCharges (sourceA2382 + difference 5 0) (sourceB2382 + difference 0 5) sourceC2382) = raw32592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32592; decide +kernel
    rw [ha]
    exact (canonical32592 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2382 + difference 5 1) (sourceB2382 + difference 1 5) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4970) := by
    have ha : (tripleCharges (sourceA2382 + difference 5 1) (sourceB2382 + difference 1 5) sourceC2382) = raw32593 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32593; decide +kernel
    rw [ha]
    exact (canonical32593 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2382 + difference 5 2) (sourceB2382 + difference 2 5) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5041) := by
    have ha : (tripleCharges (sourceA2382 + difference 5 2) (sourceB2382 + difference 2 5) sourceC2382) = raw32594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32594; decide +kernel
    rw [ha]
    exact (canonical32594 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2382 + difference 5 3) (sourceB2382 + difference 3 5) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA2382 + difference 5 3) (sourceB2382 + difference 3 5) sourceC2382) = raw32595 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32595; decide +kernel
    rw [ha]
    exact (canonical32595 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2382 + difference 5 4) (sourceB2382 + difference 4 5) sourceC2382) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA2382 + difference 5 4) (sourceB2382 + difference 4 5) sourceC2382) = raw32596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2382 sourceB2382 sourceC2382 difference raw32596; decide +kernel
    rw [ha]
    exact (canonical32596 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2382 sourceB2382 sourceC2382
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2382, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic120
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1935 : Integer.Sparse.reindex keyMap MixedData.row1935 = numericRow1935 := by decide +kernel

theorem numericCheck1935 (x : Master → ℝ) : Integer.Sparse.eval numericRow1935 x =
    (4 : ℝ) * reducedSource1935 x := by
  norm_num [numericRow1935, reducedSource1935, Integer.Sparse.eval, Sparse.eval, nodeValue4364, nodeValue4365, nodeValue4369, nodeValue4474, nodeValue4968, nodeValue4970, nodeValue4974, nodeValue5041, nodeValue5043, nodeValue5085, nodeValue5147, nodeValue5185, nodeValue5189, nodeValue5202, nodeValue5203, nodeValue5266, nodeValue5301, nodeValue5369, nodeValue5469, nodeValue5473, nodeValue5474]
  ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows120
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1935 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1935 (mixedVector B) = 0 := by
  have h4364 : mixedVector B (Sum.inr 4364) = Sparse.eval nodeValue4364 (mixedVector B) := by
    change mixedMoment B node4364 node4364Labels = _
    exact sound4364 B hB hF
  have h4365 : mixedVector B (Sum.inr 4365) = Sparse.eval nodeValue4365 (mixedVector B) := by
    change mixedMoment B node4365 node4365Labels = _
    exact sound4365 B hB hF
  have h4369 : mixedVector B (Sum.inr 4369) = Sparse.eval nodeValue4369 (mixedVector B) := by
    change mixedMoment B node4369 node4369Labels = _
    exact sound4369 B hB hF
  have h4474 : mixedVector B (Sum.inr 4474) = Sparse.eval nodeValue4474 (mixedVector B) := by
    change mixedMoment B node4474 node4474Labels = _
    exact sound4474 B hB hF
  have h4968 : mixedVector B (Sum.inr 4968) = Sparse.eval nodeValue4968 (mixedVector B) := by
    change mixedMoment B node4968 node4968Labels = _
    exact sound4968 B hB hF
  have h4970 : mixedVector B (Sum.inr 4970) = Sparse.eval nodeValue4970 (mixedVector B) := by
    change mixedMoment B node4970 node4970Labels = _
    exact sound4970 B hB hF
  have h4974 : mixedVector B (Sum.inr 4974) = Sparse.eval nodeValue4974 (mixedVector B) := by
    change mixedMoment B node4974 node4974Labels = _
    exact sound4974 B hB hF
  have h5041 : mixedVector B (Sum.inr 5041) = Sparse.eval nodeValue5041 (mixedVector B) := by
    change mixedMoment B node5041 node5041Labels = _
    exact sound5041 B hB hF
  have h5043 : mixedVector B (Sum.inr 5043) = Sparse.eval nodeValue5043 (mixedVector B) := by
    change mixedMoment B node5043 node5043Labels = _
    exact sound5043 B hB hF
  have h5085 : mixedVector B (Sum.inr 5085) = Sparse.eval nodeValue5085 (mixedVector B) := by
    change mixedMoment B node5085 node5085Labels = _
    exact sound5085 B hB hF
  have h5147 : mixedVector B (Sum.inr 5147) = Sparse.eval nodeValue5147 (mixedVector B) := by
    change mixedMoment B node5147 node5147Labels = _
    exact sound5147 B hB hF
  have h5185 : mixedVector B (Sum.inr 5185) = Sparse.eval nodeValue5185 (mixedVector B) := by
    change mixedMoment B node5185 node5185Labels = _
    exact sound5185 B hB hF
  have h5189 : mixedVector B (Sum.inr 5189) = Sparse.eval nodeValue5189 (mixedVector B) := by
    change mixedMoment B node5189 node5189Labels = _
    exact sound5189 B hB hF
  have h5202 : mixedVector B (Sum.inr 5202) = Sparse.eval nodeValue5202 (mixedVector B) := by
    change mixedMoment B node5202 node5202Labels = _
    exact sound5202 B hB hF
  have h5203 : mixedVector B (Sum.inr 5203) = Sparse.eval nodeValue5203 (mixedVector B) := by
    change mixedMoment B node5203 node5203Labels = _
    exact sound5203 B hB hF
  have h5266 : mixedVector B (Sum.inr 5266) = Sparse.eval nodeValue5266 (mixedVector B) := by
    change mixedMoment B node5266 node5266Labels = _
    exact sound5266 B hB hF
  have h5301 : mixedVector B (Sum.inr 5301) = Sparse.eval nodeValue5301 (mixedVector B) := by
    change mixedMoment B node5301 node5301Labels = _
    exact sound5301 B hB hF
  have h5369 : mixedVector B (Sum.inr 5369) = Sparse.eval nodeValue5369 (mixedVector B) := by
    change mixedMoment B node5369 node5369Labels = _
    exact sound5369 B hB hF
  have h5469 : mixedVector B (Sum.inr 5469) = Sparse.eval nodeValue5469 (mixedVector B) := by
    change mixedMoment B node5469 node5469Labels = _
    exact sound5469 B hB hF
  have h5473 : mixedVector B (Sum.inr 5473) = Sparse.eval nodeValue5473 (mixedVector B) := by
    change mixedMoment B node5473 node5473Labels = _
    exact sound5473 B hB hF
  have h5474 : mixedVector B (Sum.inr 5474) = Sparse.eval nodeValue5474 (mixedVector B) := by
    change mixedMoment B node5474 node5474Labels = _
    exact sound5474 B hB hF
  simpa only [sourceForm2382, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4364, h4365, h4369, h4474, h4968, h4970, h4974, h5041, h5043, h5085, h5147, h5185, h5189, h5202, h5203, h5266, h5301, h5369, h5469, h5473, h5474, reducedSource1935] using sourceEq2382 B hB

theorem rowSound1935_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1935 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1935, numericCheck1935, reducedZero1935 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935_e_oai
