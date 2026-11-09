-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound75_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:34:13.792697+00:00
-- url     : https://prove2.me/submissions/e72d4934-1e3d-4bf6-9727-cbc8483fb3a7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E188
import Definitions.Def_OAIQ106E189
import Definitions.Def_OAIQ106E117
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Orthogonality
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

/-- The finite orthogonality contraction underlying equation (same-matrix). -/
theorem weighted_contraction {H : CMatrix} (hH : IsHadamard H)
    (u v : Coord → ℂ) (i : Coord) :
    (∑ j, (∑ k, u k * H i k * conj (H j k)) *
      (∑ l, v l * conj (H i l) * H j l)) =
      6 * ∑ k, u k * v k := by
  have hexpand :
      (∑ j, (∑ k, u k * H i k * conj (H j k)) *
        (∑ l, v l * conj (H i l) * H j l)) =
      ∑ l, ∑ k, (u k * v l * H i k * conj (H i l)) *
        (∑ j, conj (H j k) * H j l) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand]
  simp_rw [hH.column_orthogonal]
  have hunit (k : Coord) : H i k * conj (H i k) = 1 := by
    rw [Complex.mul_conj, hH.1]
    norm_num
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    u k * v k * H i k * conj (H i k) * 6 =
      6 * (u k * v k) * (H i k * conj (H i k)) := by ring
    _ = _ := by rw [hunit, mul_one]

theorem g_add_difference {H : CMatrix} (hH : IsHadamard H)
    (a : Charge) (i j : Coord) :
    g H (a + difference i j) = (6 : ℂ)⁻¹ *
      ∑ k, character (fun r => H r k) a * H i k * conj (H j k) := by
  simp only [g]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [character_add _ (fun r => unit_ne_zero (hH.1 r k)),
    character_difference _ (fun r => hH.1 r k)]
  ring

/-- Source Lemma (basic), equation (same-matrix), for arbitrary integral charges. -/
theorem same_matrix_identity {H : CMatrix} (hH : IsHadamard H)
    (a b : Charge) (i : Coord) :
    ∑ j, g H (a + difference i j) * g H (b + difference j i) = g H (a + b) := by
  simp_rw [g_add_difference hH]
  have hexpand :
      (∑ j, ((6 : ℂ)⁻¹ * ∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
        ((6 : ℂ)⁻¹ * ∑ l, character (fun r => H r l) b * H j l * conj (H i l))) =
      (6 : ℂ)⁻¹ * (6 : ℂ)⁻¹ *
        (∑ j, (∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
          (∑ l, character (fun r => H r l) b * conj (H i l) * H j l)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have he : (∑ l, character (fun r => H r l) b * H j l * conj (H i l)) =
        ∑ l, character (fun r => H r l) b * conj (H i l) * H j l := by
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [he]
    ring
  rw [hexpand, weighted_contraction hH]
  unfold g
  have hs : (∑ k, character (fun r => H r k) a * character (fun r => H r k) b) =
      ∑ k, character (fun r => H r k) (a + b) := by
    apply Finset.sum_congr rfl
    intro k _
    exact (character_add _ (fun r => unit_ne_zero (hH.1 r k)) a b).symm
  rw [hs]
  ring

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

theorem mixedIntegrand_two {l : ℕ} (B : Fin 7 → Basis) (a b : Charge)
    (s t : Fin l) (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
    mixedIntegrand B (doubleCharges a b) ![s, t] r ρ τ =
      g (sampledMatrix B r ρ (τ s)) a * g (sampledMatrix B r ρ (τ t)) b := by
  simp [mixedIntegrand, doubleCharges, Fin.prod_univ_succ, rowFourier, g, character, sampledMatrix]

theorem mixedMoment_same {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference i j) (b + difference j i) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  rw [same_matrix_identity (sampledMatrix_isHadamard B hB r ρ _) a b i]

theorem mixedMoment_same_reversed {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference j i) (b + difference i j) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  have h := same_matrix_identity (sampledMatrix_isHadamard B hB r ρ (τ s)) b a i
  simpa only [mul_comm, add_comm] using congrArg
    (fun z => (z * g (sampledMatrix B r ρ (τ u)) c).re) h

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

theorem canonical1284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1284 raw1284Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw1284 raw1284Labels = mixedMoment B raw1284step0 raw1284step0Labels := by
      have ha : raw1284step0 = (fun i j => raw1284 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1284step0 raw1284; decide +kernel
      have hl : raw1284step0Labels = raw1284Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1284 raw1284Labels permutation8 permutation4
    mixedMoment B raw1284step0 raw1284step0Labels = mixedMoment B raw1284step1 raw1284step1Labels := by
      have ha : raw1284step1 = raw1284step0 := by apply Matrix.ext; unfold raw1284step1 raw1284step0; decide +kernel
      have hl : raw1284step0Labels = labelEmbedding7 ∘ raw1284step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1284step0 raw1284step0Labels raw1284step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4490 node4490Labels := by rfl

theorem canonical1285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1285 raw1285Labels = mixedMoment B node1074 node1074Labels := by
  calc
    mixedMoment B raw1285 raw1285Labels = mixedMoment B raw1285step0 raw1285step0Labels := by
      have ha : raw1285step0 = (fun i j => raw1285 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1285step0 raw1285; decide +kernel
      have hl : raw1285step0Labels = raw1285Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1285 raw1285Labels permutation8 permutation4
    _ = mixedMoment B node1074 node1074Labels := by rfl

theorem canonical1286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1286 raw1286Labels = mixedMoment B node1650 node1650Labels := by
  calc
    mixedMoment B raw1286 raw1286Labels = mixedMoment B raw1286step0 raw1286step0Labels := by
      have ha : raw1286step0 = (fun i j => raw1286 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1286step0 raw1286; decide +kernel
      have hl : raw1286step0Labels = raw1286Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1286 raw1286Labels permutation8 permutation6
    mixedMoment B raw1286step0 raw1286step0Labels = mixedMoment B raw1286step1 raw1286step1Labels := by
      have ha : raw1286step1 = -raw1286step0 := by apply Matrix.ext; change ∀ i j, raw1286step1 i j = -(raw1286step0 i j); unfold raw1286step1 raw1286step0; decide +kernel
      have hl : raw1286step1Labels = raw1286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1286step1 raw1286step1Labels = mixedMoment B raw1286step2 raw1286step2Labels := by
      have ha : raw1286step2 = raw1286step1 := by apply Matrix.ext; unfold raw1286step2 raw1286step1; decide +kernel
      have hl : raw1286step1Labels = labelEmbedding1 ∘ raw1286step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1286step1 raw1286step1Labels raw1286step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1650 node1650Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19953 raw19953Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw19953 raw19953Labels = mixedMoment B raw19953step0 raw19953step0Labels := by
      have hz : ∀ j, raw19953 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19953step0 = (fun i j => raw19953 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19953step0 raw19953; decide +kernel
      have hl : raw19953step0Labels = raw19953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19953 raw19953Labels permutation520 hz
    mixedMoment B raw19953step0 raw19953step0Labels = mixedMoment B raw19953step1 raw19953step1Labels := by
      have hz : ∀ j, raw19953step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19953step1 = (fun i j => raw19953step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19953step1 raw19953step0; decide +kernel
      have hl : raw19953step1Labels = raw19953step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19953step0 raw19953step0Labels permutation104 hz
    mixedMoment B raw19953step1 raw19953step1Labels = mixedMoment B raw19953step2 raw19953step2Labels := by
      have hz : ∀ j, raw19953step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19953step2 = (fun i j => raw19953step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19953step2 raw19953step1; decide +kernel
      have hl : raw19953step2Labels = raw19953step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19953step1 raw19953step1Labels permutation20 hz
    mixedMoment B raw19953step2 raw19953step2Labels = mixedMoment B raw19953step3 raw19953step3Labels := by
      have hz : ∀ j, raw19953step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19953step3 = (fun i j => raw19953step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19953step3 raw19953step2; decide +kernel
      have hl : raw19953step3Labels = raw19953step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19953step2 raw19953step2Labels permutation4 hz
    _ = mixedMoment B node4085 node4085Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical157
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20099 raw20099Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw20099 raw20099Labels = mixedMoment B raw20099step0 raw20099step0Labels := by
      have hz : ∀ j, raw20099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20099step0 = (fun i j => raw20099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20099step0 raw20099; decide +kernel
      have hl : raw20099step0Labels = raw20099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099 raw20099Labels permutation434 hz
    mixedMoment B raw20099step0 raw20099step0Labels = mixedMoment B raw20099step1 raw20099step1Labels := by
      have hz : ∀ j, raw20099step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20099step1 = (fun i j => raw20099step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20099step1 raw20099step0; decide +kernel
      have hl : raw20099step1Labels = raw20099step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099step0 raw20099step0Labels permutation80 hz
    mixedMoment B raw20099step1 raw20099step1Labels = mixedMoment B raw20099step2 raw20099step2Labels := by
      have hz : ∀ j, raw20099step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20099step2 = (fun i j => raw20099step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20099step2 raw20099step1; decide +kernel
      have hl : raw20099step2Labels = raw20099step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099step1 raw20099step1Labels permutation14 hz
    mixedMoment B raw20099step2 raw20099step2Labels = mixedMoment B raw20099step3 raw20099step3Labels := by
      have ha : raw20099step3 = -raw20099step2 := by apply Matrix.ext; change ∀ i j, raw20099step3 i j = -(raw20099step2 i j); unfold raw20099step3 raw20099step2; decide +kernel
      have hl : raw20099step3Labels = raw20099step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21575 raw21575Labels = mixedMoment B node741 node741Labels := by
  calc
    mixedMoment B raw21575 raw21575Labels = mixedMoment B raw21575step0 raw21575step0Labels := by
      have hz : ∀ j, raw21575 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21575step0 = (fun i j => raw21575 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21575step0 raw21575; decide +kernel
      have hl : raw21575step0Labels = raw21575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21575 raw21575Labels permutation434 hz
    mixedMoment B raw21575step0 raw21575step0Labels = mixedMoment B raw21575step1 raw21575step1Labels := by
      have hz : ∀ j, raw21575step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21575step1 = (fun i j => raw21575step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21575step1 raw21575step0; decide +kernel
      have hl : raw21575step1Labels = raw21575step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21575step0 raw21575step0Labels permutation80 hz
    mixedMoment B raw21575step1 raw21575step1Labels = mixedMoment B raw21575step2 raw21575step2Labels := by
      have ha : raw21575step2 = (fun i j => raw21575step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21575step2 raw21575step1; decide +kernel
      have hl : raw21575step2Labels = raw21575step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21575step1 raw21575step1Labels permutation10 permutation4
    mixedMoment B raw21575step2 raw21575step2Labels = mixedMoment B raw21575step3 raw21575step3Labels := by
      have ha : raw21575step3 = -raw21575step2 := by apply Matrix.ext; change ∀ i j, raw21575step3 i j = -(raw21575step2 i j); unfold raw21575step3 raw21575step2; decide +kernel
      have hl : raw21575step3Labels = raw21575step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node741 node741Labels := by rfl

theorem canonical21578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21578 raw21578Labels = mixedMoment B node809 node809Labels := by
  calc
    mixedMoment B raw21578 raw21578Labels = mixedMoment B raw21578step0 raw21578step0Labels := by
      have hz : ∀ j, raw21578 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21578step0 = (fun i j => raw21578 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21578step0 raw21578; decide +kernel
      have hl : raw21578step0Labels = raw21578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21578 raw21578Labels permutation434 hz
    mixedMoment B raw21578step0 raw21578step0Labels = mixedMoment B raw21578step1 raw21578step1Labels := by
      have hz : ∀ j, raw21578step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21578step1 = (fun i j => raw21578step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21578step1 raw21578step0; decide +kernel
      have hl : raw21578step1Labels = raw21578step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21578step0 raw21578step0Labels permutation80 hz
    mixedMoment B raw21578step1 raw21578step1Labels = mixedMoment B raw21578step2 raw21578step2Labels := by
      have ha : raw21578step2 = (fun i j => raw21578step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21578step2 raw21578step1; decide +kernel
      have hl : raw21578step2Labels = raw21578step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21578step1 raw21578step1Labels permutation10 permutation4
    mixedMoment B raw21578step2 raw21578step2Labels = mixedMoment B raw21578step3 raw21578step3Labels := by
      have ha : raw21578step3 = -raw21578step2 := by apply Matrix.ext; change ∀ i j, raw21578step3 i j = -(raw21578step2 i j); unfold raw21578step3 raw21578step2; decide +kernel
      have hl : raw21578step3Labels = raw21578step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node809 node809Labels := by rfl

theorem canonical21631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21631 raw21631Labels = mixedMoment B node706 node706Labels := by
  calc
    mixedMoment B raw21631 raw21631Labels = mixedMoment B raw21631step0 raw21631step0Labels := by
      have hz : ∀ j, raw21631 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21631step0 = (fun i j => raw21631 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21631step0 raw21631; decide +kernel
      have hl : raw21631step0Labels = raw21631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21631 raw21631Labels permutation346 hz
    mixedMoment B raw21631step0 raw21631step0Labels = mixedMoment B raw21631step1 raw21631step1Labels := by
      have ha : raw21631step1 = (fun i j => raw21631step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21631step1 raw21631step0; decide +kernel
      have hl : raw21631step1Labels = raw21631step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21631step0 raw21631step0Labels permutation40 permutation4
    mixedMoment B raw21631step1 raw21631step1Labels = mixedMoment B raw21631step2 raw21631step2Labels := by
      have ha : raw21631step2 = -raw21631step1 := by apply Matrix.ext; change ∀ i j, raw21631step2 i j = -(raw21631step1 i j); unfold raw21631step2 raw21631step1; decide +kernel
      have hl : raw21631step2Labels = raw21631step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node706 node706Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21875 raw21875Labels = mixedMoment B node1085 node1085Labels := by
  calc
    mixedMoment B raw21875 raw21875Labels = mixedMoment B raw21875step0 raw21875step0Labels := by
      have hz : ∀ j, raw21875 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21875step0 = (fun i j => raw21875 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21875step0 raw21875; decide +kernel
      have hl : raw21875step0Labels = raw21875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21875 raw21875Labels permutation434 hz
    mixedMoment B raw21875step0 raw21875step0Labels = mixedMoment B raw21875step1 raw21875step1Labels := by
      have hz : ∀ j, raw21875step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21875step1 = (fun i j => raw21875step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21875step1 raw21875step0; decide +kernel
      have hl : raw21875step1Labels = raw21875step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21875step0 raw21875step0Labels permutation80 hz
    mixedMoment B raw21875step1 raw21875step1Labels = mixedMoment B raw21875step2 raw21875step2Labels := by
      have hz : ∀ j, raw21875step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21875step2 = (fun i j => raw21875step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21875step2 raw21875step1; decide +kernel
      have hl : raw21875step2Labels = raw21875step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21875step1 raw21875step1Labels permutation14 hz
    _ = mixedMoment B node1085 node1085Labels := by rfl

theorem canonical21876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21876 raw21876Labels = mixedMoment B node602 node602Labels := by
  calc
    mixedMoment B raw21876 raw21876Labels = mixedMoment B raw21876step0 raw21876step0Labels := by
      have hz : ∀ j, raw21876 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21876step0 = (fun i j => raw21876 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21876step0 raw21876; decide +kernel
      have hl : raw21876step0Labels = raw21876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21876 raw21876Labels permutation434 hz
    mixedMoment B raw21876step0 raw21876step0Labels = mixedMoment B raw21876step1 raw21876step1Labels := by
      have hz : ∀ j, raw21876step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21876step1 = (fun i j => raw21876step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21876step1 raw21876step0; decide +kernel
      have hl : raw21876step1Labels = raw21876step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21876step0 raw21876step0Labels permutation80 hz
    _ = mixedMoment B node602 node602Labels := by rfl

theorem canonical21880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21880 raw21880Labels = mixedMoment B node921 node921Labels := by
  calc
    mixedMoment B raw21880 raw21880Labels = mixedMoment B raw21880step0 raw21880step0Labels := by
      have hz : ∀ j, raw21880 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21880step0 = (fun i j => raw21880 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21880step0 raw21880; decide +kernel
      have hl : raw21880step0Labels = raw21880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21880 raw21880Labels permutation434 hz
    mixedMoment B raw21880step0 raw21880step0Labels = mixedMoment B raw21880step1 raw21880step1Labels := by
      have ha : raw21880step1 = (fun i j => raw21880step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21880step1 raw21880step0; decide +kernel
      have hl : raw21880step1Labels = raw21880step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21880step0 raw21880step0Labels permutation38 permutation2
    _ = mixedMoment B node921 node921Labels := by rfl

theorem canonical21881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21881 raw21881Labels = mixedMoment B node921 node921Labels := by
  calc
    mixedMoment B raw21881 raw21881Labels = mixedMoment B raw21881step0 raw21881step0Labels := by
      have hz : ∀ j, raw21881 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21881step0 = (fun i j => raw21881 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21881step0 raw21881; decide +kernel
      have hl : raw21881step0Labels = raw21881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21881 raw21881Labels permutation346 hz
    mixedMoment B raw21881step0 raw21881step0Labels = mixedMoment B raw21881step1 raw21881step1Labels := by
      have ha : raw21881step1 = (fun i j => raw21881step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21881step1 raw21881step0; decide +kernel
      have hl : raw21881step1Labels = raw21881step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21881step0 raw21881step0Labels permutation38 permutation2
    _ = mixedMoment B node921 node921Labels := by rfl

theorem canonical21882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21882 raw21882Labels = mixedMoment B node1085 node1085Labels := by
  calc
    mixedMoment B raw21882 raw21882Labels = mixedMoment B raw21882step0 raw21882step0Labels := by
      have hz : ∀ j, raw21882 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21882step0 = (fun i j => raw21882 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21882step0 raw21882; decide +kernel
      have hl : raw21882step0Labels = raw21882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21882 raw21882Labels permutation520 hz
    mixedMoment B raw21882step0 raw21882step0Labels = mixedMoment B raw21882step1 raw21882step1Labels := by
      have hz : ∀ j, raw21882step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21882step1 = (fun i j => raw21882step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21882step1 raw21882step0; decide +kernel
      have hl : raw21882step1Labels = raw21882step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21882step0 raw21882step0Labels permutation104 hz
    mixedMoment B raw21882step1 raw21882step1Labels = mixedMoment B raw21882step2 raw21882step2Labels := by
      have hz : ∀ j, raw21882step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21882step2 = (fun i j => raw21882step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21882step2 raw21882step1; decide +kernel
      have hl : raw21882step2Labels = raw21882step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21882step1 raw21882step1Labels permutation20 hz
    _ = mixedMoment B node1085 node1085Labels := by rfl

theorem canonical21883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21883 raw21883Labels = mixedMoment B node1080 node1080Labels := by
  calc
    mixedMoment B raw21883 raw21883Labels = mixedMoment B raw21883step0 raw21883step0Labels := by
      have hz : ∀ j, raw21883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21883step0 = (fun i j => raw21883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21883step0 raw21883; decide +kernel
      have hl : raw21883step0Labels = raw21883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21883 raw21883Labels permutation434 hz
    mixedMoment B raw21883step0 raw21883step0Labels = mixedMoment B raw21883step1 raw21883step1Labels := by
      have hz : ∀ j, raw21883step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21883step1 = (fun i j => raw21883step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21883step1 raw21883step0; decide +kernel
      have hl : raw21883step1Labels = raw21883step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21883step0 raw21883step0Labels permutation80 hz
    _ = mixedMoment B node1080 node1080Labels := by rfl

theorem canonical21884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21884 raw21884Labels = mixedMoment B node1010 node1010Labels := by
  calc
    mixedMoment B raw21884 raw21884Labels = mixedMoment B raw21884step0 raw21884step0Labels := by
      have hz : ∀ j, raw21884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21884step0 = (fun i j => raw21884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21884step0 raw21884; decide +kernel
      have hl : raw21884step0Labels = raw21884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21884 raw21884Labels permutation346 hz
    mixedMoment B raw21884step0 raw21884step0Labels = mixedMoment B raw21884step1 raw21884step1Labels := by
      have hz : ∀ j, raw21884step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21884step1 = (fun i j => raw21884step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21884step1 raw21884step0; decide +kernel
      have hl : raw21884step1Labels = raw21884step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21884step0 raw21884step0Labels permutation56 hz
    _ = mixedMoment B node1010 node1010Labels := by rfl

theorem canonical21885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21885 raw21885Labels = mixedMoment B node2004 node2004Labels := by
  calc
    mixedMoment B raw21885 raw21885Labels = mixedMoment B raw21885step0 raw21885step0Labels := by
      have hz : ∀ j, raw21885 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21885step0 = (fun i j => raw21885 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21885step0 raw21885; decide +kernel
      have hl : raw21885step0Labels = raw21885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21885 raw21885Labels permutation346 hz
    _ = mixedMoment B node2004 node2004Labels := by rfl

theorem canonical21886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21886 raw21886Labels = mixedMoment B node2004 node2004Labels := by
  calc
    mixedMoment B raw21886 raw21886Labels = mixedMoment B raw21886step0 raw21886step0Labels := by
      have hz : ∀ j, raw21886 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21886step0 = (fun i j => raw21886 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21886step0 raw21886; decide +kernel
      have hl : raw21886step0Labels = raw21886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21886 raw21886Labels permutation265 hz
    _ = mixedMoment B node2004 node2004Labels := by rfl

theorem canonical21887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21887 raw21887Labels = mixedMoment B node1951 node1951Labels := by
  calc
    mixedMoment B raw21887 raw21887Labels = mixedMoment B raw21887step0 raw21887step0Labels := by
      have hz : ∀ j, raw21887 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21887step0 = (fun i j => raw21887 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21887step0 raw21887; decide +kernel
      have hl : raw21887step0Labels = raw21887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21887 raw21887Labels permutation346 hz
    mixedMoment B raw21887step0 raw21887step0Labels = mixedMoment B raw21887step1 raw21887step1Labels := by
      have hz : ∀ j, raw21887step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21887step1 = (fun i j => raw21887step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21887step1 raw21887step0; decide +kernel
      have hl : raw21887step1Labels = raw21887step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21887step0 raw21887step0Labels permutation56 hz
    _ = mixedMoment B node1951 node1951Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical171
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21888 raw21888Labels = mixedMoment B node2222 node2222Labels := by
  calc
    mixedMoment B raw21888 raw21888Labels = mixedMoment B raw21888step0 raw21888step0Labels := by
      have hz : ∀ j, raw21888 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21888step0 = (fun i j => raw21888 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21888step0 raw21888; decide +kernel
      have hl : raw21888step0Labels = raw21888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21888 raw21888Labels permutation346 hz
    mixedMoment B raw21888step0 raw21888step0Labels = mixedMoment B raw21888step1 raw21888step1Labels := by
      have hz : ∀ j, raw21888step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21888step1 = (fun i j => raw21888step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21888step1 raw21888step0; decide +kernel
      have hl : raw21888step1Labels = raw21888step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21888step0 raw21888step0Labels permutation56 hz
    _ = mixedMoment B node2222 node2222Labels := by rfl

theorem canonical21889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21889 raw21889Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw21889 raw21889Labels = mixedMoment B raw21889step0 raw21889step0Labels := by
      have hz : ∀ j, raw21889 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21889step0 = (fun i j => raw21889 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21889step0 raw21889; decide +kernel
      have hl : raw21889step0Labels = raw21889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21889 raw21889Labels permutation346 hz
    mixedMoment B raw21889step0 raw21889step0Labels = mixedMoment B raw21889step1 raw21889step1Labels := by
      have hz : ∀ j, raw21889step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21889step1 = (fun i j => raw21889step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21889step1 raw21889step0; decide +kernel
      have hl : raw21889step1Labels = raw21889step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21889step0 raw21889step0Labels permutation56 hz
    _ = mixedMoment B node2230 node2230Labels := by rfl

theorem canonical21890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21890 raw21890Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw21890 raw21890Labels = mixedMoment B raw21890step0 raw21890step0Labels := by
      have hz : ∀ j, raw21890 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21890step0 = (fun i j => raw21890 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21890step0 raw21890; decide +kernel
      have hl : raw21890step0Labels = raw21890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21890 raw21890Labels permutation346 hz
    mixedMoment B raw21890step0 raw21890step0Labels = mixedMoment B raw21890step1 raw21890step1Labels := by
      have hz : ∀ j, raw21890step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21890step1 = (fun i j => raw21890step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21890step1 raw21890step0; decide +kernel
      have hl : raw21890step1Labels = raw21890step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21890step0 raw21890step0Labels permutation56 hz
    mixedMoment B raw21890step1 raw21890step1Labels = mixedMoment B raw21890step2 raw21890step2Labels := by
      have ha : raw21890step2 = (fun i j => raw21890step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21890step2 raw21890step1; decide +kernel
      have hl : raw21890step2Labels = raw21890step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21890step1 raw21890step1Labels permutation9 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical21891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21891 raw21891Labels = mixedMoment B node1001 node1001Labels := by
  calc
    mixedMoment B raw21891 raw21891Labels = mixedMoment B raw21891step0 raw21891step0Labels := by
      have hz : ∀ j, raw21891 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21891step0 = (fun i j => raw21891 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21891step0 raw21891; decide +kernel
      have hl : raw21891step0Labels = raw21891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21891 raw21891Labels permutation346 hz
    mixedMoment B raw21891step0 raw21891step0Labels = mixedMoment B raw21891step1 raw21891step1Labels := by
      have ha : raw21891step1 = (fun i j => raw21891step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21891step1 raw21891step0; decide +kernel
      have hl : raw21891step1Labels = raw21891step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21891step0 raw21891step0Labels permutation38 permutation2
    _ = mixedMoment B node1001 node1001Labels := by rfl

theorem canonical21892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21892 raw21892Labels = mixedMoment B node1001 node1001Labels := by
  calc
    mixedMoment B raw21892 raw21892Labels = mixedMoment B raw21892step0 raw21892step0Labels := by
      have hz : ∀ j, raw21892 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21892step0 = (fun i j => raw21892 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21892step0 raw21892; decide +kernel
      have hl : raw21892step0Labels = raw21892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21892 raw21892Labels permutation265 hz
    mixedMoment B raw21892step0 raw21892step0Labels = mixedMoment B raw21892step1 raw21892step1Labels := by
      have ha : raw21892step1 = (fun i j => raw21892step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21892step1 raw21892step0; decide +kernel
      have hl : raw21892step1Labels = raw21892step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21892step0 raw21892step0Labels permutation38 permutation2
    _ = mixedMoment B node1001 node1001Labels := by rfl

theorem canonical21893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21893 raw21893Labels = mixedMoment B node1076 node1076Labels := by
  calc
    mixedMoment B raw21893 raw21893Labels = mixedMoment B raw21893step0 raw21893step0Labels := by
      have hz : ∀ j, raw21893 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21893step0 = (fun i j => raw21893 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21893step0 raw21893; decide +kernel
      have hl : raw21893step0Labels = raw21893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21893 raw21893Labels permutation346 hz
    mixedMoment B raw21893step0 raw21893step0Labels = mixedMoment B raw21893step1 raw21893step1Labels := by
      have hz : ∀ j, raw21893step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21893step1 = (fun i j => raw21893step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21893step1 raw21893step0; decide +kernel
      have hl : raw21893step1Labels = raw21893step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21893step0 raw21893step0Labels permutation56 hz
    _ = mixedMoment B node1076 node1076Labels := by rfl

theorem canonical21894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21894 raw21894Labels = mixedMoment B node1012 node1012Labels := by
  calc
    mixedMoment B raw21894 raw21894Labels = mixedMoment B raw21894step0 raw21894step0Labels := by
      have hz : ∀ j, raw21894 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21894step0 = (fun i j => raw21894 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21894step0 raw21894; decide +kernel
      have hl : raw21894step0Labels = raw21894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21894 raw21894Labels permutation346 hz
    mixedMoment B raw21894step0 raw21894step0Labels = mixedMoment B raw21894step1 raw21894step1Labels := by
      have hz : ∀ j, raw21894step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21894step1 = (fun i j => raw21894step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21894step1 raw21894step0; decide +kernel
      have hl : raw21894step1Labels = raw21894step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21894step0 raw21894step0Labels permutation56 hz
    mixedMoment B raw21894step1 raw21894step1Labels = mixedMoment B raw21894step2 raw21894step2Labels := by
      have ha : raw21894step2 = (fun i j => raw21894step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21894step2 raw21894step1; decide +kernel
      have hl : raw21894step2Labels = raw21894step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21894step1 raw21894step1Labels permutation9 permutation2
    _ = mixedMoment B node1012 node1012Labels := by rfl

theorem canonical21895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21895 raw21895Labels = mixedMoment B node1009 node1009Labels := by
  calc
    mixedMoment B raw21895 raw21895Labels = mixedMoment B raw21895step0 raw21895step0Labels := by
      have hz : ∀ j, raw21895 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21895step0 = (fun i j => raw21895 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21895step0 raw21895; decide +kernel
      have hl : raw21895step0Labels = raw21895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21895 raw21895Labels permutation346 hz
    mixedMoment B raw21895step0 raw21895step0Labels = mixedMoment B raw21895step1 raw21895step1Labels := by
      have hz : ∀ j, raw21895step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21895step1 = (fun i j => raw21895step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21895step1 raw21895step0; decide +kernel
      have hl : raw21895step1Labels = raw21895step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21895step0 raw21895step0Labels permutation56 hz
    _ = mixedMoment B node1009 node1009Labels := by rfl

theorem canonical21896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21896 raw21896Labels = mixedMoment B node2003 node2003Labels := by
  calc
    mixedMoment B raw21896 raw21896Labels = mixedMoment B raw21896step0 raw21896step0Labels := by
      have hz : ∀ j, raw21896 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21896step0 = (fun i j => raw21896 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21896step0 raw21896; decide +kernel
      have hl : raw21896step0Labels = raw21896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21896 raw21896Labels permutation346 hz
    _ = mixedMoment B node2003 node2003Labels := by rfl

theorem canonical21897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21897 raw21897Labels = mixedMoment B node2003 node2003Labels := by
  calc
    mixedMoment B raw21897 raw21897Labels = mixedMoment B raw21897step0 raw21897step0Labels := by
      have hz : ∀ j, raw21897 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21897step0 = (fun i j => raw21897 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21897step0 raw21897; decide +kernel
      have hl : raw21897step0Labels = raw21897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21897 raw21897Labels permutation265 hz
    _ = mixedMoment B node2003 node2003Labels := by rfl

theorem canonical21898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21898 raw21898Labels = mixedMoment B node1950 node1950Labels := by
  calc
    mixedMoment B raw21898 raw21898Labels = mixedMoment B raw21898step0 raw21898step0Labels := by
      have hz : ∀ j, raw21898 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21898step0 = (fun i j => raw21898 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21898step0 raw21898; decide +kernel
      have hl : raw21898step0Labels = raw21898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21898 raw21898Labels permutation346 hz
    mixedMoment B raw21898step0 raw21898step0Labels = mixedMoment B raw21898step1 raw21898step1Labels := by
      have hz : ∀ j, raw21898step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21898step1 = (fun i j => raw21898step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21898step1 raw21898step0; decide +kernel
      have hl : raw21898step1Labels = raw21898step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21898step0 raw21898step0Labels permutation56 hz
    _ = mixedMoment B node1950 node1950Labels := by rfl

theorem canonical21899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21899 raw21899Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw21899 raw21899Labels = mixedMoment B raw21899step0 raw21899step0Labels := by
      have hz : ∀ j, raw21899 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21899step0 = (fun i j => raw21899 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21899step0 raw21899; decide +kernel
      have hl : raw21899step0Labels = raw21899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21899 raw21899Labels permutation346 hz
    mixedMoment B raw21899step0 raw21899step0Labels = mixedMoment B raw21899step1 raw21899step1Labels := by
      have hz : ∀ j, raw21899step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21899step1 = (fun i j => raw21899step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21899step1 raw21899step0; decide +kernel
      have hl : raw21899step1Labels = raw21899step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21899step0 raw21899step0Labels permutation56 hz
    _ = mixedMoment B node2218 node2218Labels := by rfl

theorem canonical21900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21900 raw21900Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw21900 raw21900Labels = mixedMoment B raw21900step0 raw21900step0Labels := by
      have hz : ∀ j, raw21900 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21900step0 = (fun i j => raw21900 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21900step0 raw21900; decide +kernel
      have hl : raw21900step0Labels = raw21900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21900 raw21900Labels permutation346 hz
    mixedMoment B raw21900step0 raw21900step0Labels = mixedMoment B raw21900step1 raw21900step1Labels := by
      have hz : ∀ j, raw21900step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21900step1 = (fun i j => raw21900step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21900step1 raw21900step0; decide +kernel
      have hl : raw21900step1Labels = raw21900step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21900step0 raw21900step0Labels permutation56 hz
    _ = mixedMoment B node2229 node2229Labels := by rfl

theorem canonical21901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21901 raw21901Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw21901 raw21901Labels = mixedMoment B raw21901step0 raw21901step0Labels := by
      have hz : ∀ j, raw21901 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21901step0 = (fun i j => raw21901 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21901step0 raw21901; decide +kernel
      have hl : raw21901step0Labels = raw21901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21901 raw21901Labels permutation346 hz
    mixedMoment B raw21901step0 raw21901step0Labels = mixedMoment B raw21901step1 raw21901step1Labels := by
      have hz : ∀ j, raw21901step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21901step1 = (fun i j => raw21901step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21901step1 raw21901step0; decide +kernel
      have hl : raw21901step1Labels = raw21901step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21901step0 raw21901step0Labels permutation56 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical21909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21909 raw21909Labels = mixedMoment B node1013 node1013Labels := by
  calc
    mixedMoment B raw21909 raw21909Labels = mixedMoment B raw21909step0 raw21909step0Labels := by
      have hz : ∀ j, raw21909 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21909step0 = (fun i j => raw21909 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21909step0 raw21909; decide +kernel
      have hl : raw21909step0Labels = raw21909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21909 raw21909Labels permutation346 hz
    mixedMoment B raw21909step0 raw21909step0Labels = mixedMoment B raw21909step1 raw21909step1Labels := by
      have hz : ∀ j, raw21909step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21909step1 = (fun i j => raw21909step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21909step1 raw21909step0; decide +kernel
      have hl : raw21909step1Labels = raw21909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21909step0 raw21909step0Labels permutation56 hz
    _ = mixedMoment B node1013 node1013Labels := by rfl

theorem canonical21910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21910 raw21910Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw21910 raw21910Labels = mixedMoment B raw21910step0 raw21910step0Labels := by
      have hz : ∀ j, raw21910 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21910step0 = (fun i j => raw21910 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21910step0 raw21910; decide +kernel
      have hl : raw21910step0Labels = raw21910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21910 raw21910Labels permutation346 hz
    mixedMoment B raw21910step0 raw21910step0Labels = mixedMoment B raw21910step1 raw21910step1Labels := by
      have ha : raw21910step1 = (fun i j => raw21910step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21910step1 raw21910step0; decide +kernel
      have hl : raw21910step1Labels = raw21910step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21910step0 raw21910step0Labels permutation38 permutation2
    _ = mixedMoment B node1000 node1000Labels := by rfl

theorem canonical21911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21911 raw21911Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw21911 raw21911Labels = mixedMoment B raw21911step0 raw21911step0Labels := by
      have hz : ∀ j, raw21911 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21911step0 = (fun i j => raw21911 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21911step0 raw21911; decide +kernel
      have hl : raw21911step0Labels = raw21911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21911 raw21911Labels permutation265 hz
    mixedMoment B raw21911step0 raw21911step0Labels = mixedMoment B raw21911step1 raw21911step1Labels := by
      have ha : raw21911step1 = (fun i j => raw21911step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21911step1 raw21911step0; decide +kernel
      have hl : raw21911step1Labels = raw21911step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21911step0 raw21911step0Labels permutation38 permutation2
    _ = mixedMoment B node1000 node1000Labels := by rfl

theorem canonical21912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21912 raw21912Labels = mixedMoment B node1075 node1075Labels := by
  calc
    mixedMoment B raw21912 raw21912Labels = mixedMoment B raw21912step0 raw21912step0Labels := by
      have hz : ∀ j, raw21912 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21912step0 = (fun i j => raw21912 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21912step0 raw21912; decide +kernel
      have hl : raw21912step0Labels = raw21912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21912 raw21912Labels permutation346 hz
    mixedMoment B raw21912step0 raw21912step0Labels = mixedMoment B raw21912step1 raw21912step1Labels := by
      have hz : ∀ j, raw21912step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21912step1 = (fun i j => raw21912step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21912step1 raw21912step0; decide +kernel
      have hl : raw21912step1Labels = raw21912step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21912step0 raw21912step0Labels permutation56 hz
    _ = mixedMoment B node1075 node1075Labels := by rfl

theorem canonical21918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21918 raw21918Labels = mixedMoment B node4738 node4738Labels := by
  calc
    mixedMoment B raw21918 raw21918Labels = mixedMoment B raw21918step0 raw21918step0Labels := by
      have hz : ∀ j, raw21918 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21918step0 = (fun i j => raw21918 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21918step0 raw21918; decide +kernel
      have hl : raw21918step0Labels = raw21918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21918 raw21918Labels permutation346 hz
    mixedMoment B raw21918step0 raw21918step0Labels = mixedMoment B raw21918step1 raw21918step1Labels := by
      have ha : raw21918step1 = (fun i j => raw21918step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21918step1 raw21918step0; decide +kernel
      have hl : raw21918step1Labels = raw21918step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21918step0 raw21918step0Labels permutation151 permutation2
    mixedMoment B raw21918step1 raw21918step1Labels = mixedMoment B raw21918step2 raw21918step2Labels := by
      have ha : raw21918step2 = -raw21918step1 := by apply Matrix.ext; change ∀ i j, raw21918step2 i j = -(raw21918step1 i j); unfold raw21918step2 raw21918step1; decide +kernel
      have hl : raw21918step2Labels = raw21918step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4738 node4738Labels := by rfl

theorem canonical21919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21919 raw21919Labels = mixedMoment B node4738 node4738Labels := by
  calc
    mixedMoment B raw21919 raw21919Labels = mixedMoment B raw21919step0 raw21919step0Labels := by
      have hz : ∀ j, raw21919 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21919step0 = (fun i j => raw21919 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21919step0 raw21919; decide +kernel
      have hl : raw21919step0Labels = raw21919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21919 raw21919Labels permutation265 hz
    mixedMoment B raw21919step0 raw21919step0Labels = mixedMoment B raw21919step1 raw21919step1Labels := by
      have ha : raw21919step1 = (fun i j => raw21919step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21919step1 raw21919step0; decide +kernel
      have hl : raw21919step1Labels = raw21919step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21919step0 raw21919step0Labels permutation151 permutation2
    mixedMoment B raw21919step1 raw21919step1Labels = mixedMoment B raw21919step2 raw21919step2Labels := by
      have ha : raw21919step2 = -raw21919step1 := by apply Matrix.ext; change ∀ i j, raw21919step2 i j = -(raw21919step1 i j); unfold raw21919step2 raw21919step1; decide +kernel
      have hl : raw21919step2Labels = raw21919step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4738 node4738Labels := by rfl

theorem canonical21920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21920 raw21920Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw21920 raw21920Labels = mixedMoment B raw21920step0 raw21920step0Labels := by
      have hz : ∀ j, raw21920 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21920step0 = (fun i j => raw21920 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21920step0 raw21920; decide +kernel
      have hl : raw21920step0Labels = raw21920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21920 raw21920Labels permutation346 hz
    mixedMoment B raw21920step0 raw21920step0Labels = mixedMoment B raw21920step1 raw21920step1Labels := by
      have hz : ∀ j, raw21920step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21920step1 = (fun i j => raw21920step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21920step1 raw21920step0; decide +kernel
      have hl : raw21920step1Labels = raw21920step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21920step0 raw21920step0Labels permutation56 hz
    mixedMoment B raw21920step1 raw21920step1Labels = mixedMoment B raw21920step2 raw21920step2Labels := by
      have hz : ∀ i, raw21920step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw21920step2 = (fun i j => raw21920step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw21920step2 raw21920step1; decide +kernel
      have hl : raw21920step2Labels = (fun j => raw21920step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw21920step1 raw21920step1Labels permutation4 hz
    mixedMoment B raw21920step2 raw21920step2Labels = mixedMoment B raw21920step3 raw21920step3Labels := by
      have ha : raw21920step3 = raw21920step2 := by apply Matrix.ext; unfold raw21920step3 raw21920step2; decide +kernel
      have hl : raw21920step2Labels = labelEmbedding2 ∘ raw21920step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21920step2 raw21920step2Labels raw21920step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical21921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21921 raw21921Labels = mixedMoment B node4837 node4837Labels := by
  calc
    mixedMoment B raw21921 raw21921Labels = mixedMoment B raw21921step0 raw21921step0Labels := by
      have hz : ∀ j, raw21921 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21921step0 = (fun i j => raw21921 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21921step0 raw21921; decide +kernel
      have hl : raw21921step0Labels = raw21921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21921 raw21921Labels permutation346 hz
    mixedMoment B raw21921step0 raw21921step0Labels = mixedMoment B raw21921step1 raw21921step1Labels := by
      have hz : ∀ j, raw21921step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21921step1 = (fun i j => raw21921step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21921step1 raw21921step0; decide +kernel
      have hl : raw21921step1Labels = raw21921step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21921step0 raw21921step0Labels permutation56 hz
    mixedMoment B raw21921step1 raw21921step1Labels = mixedMoment B raw21921step2 raw21921step2Labels := by
      have ha : raw21921step2 = (fun i j => raw21921step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21921step2 raw21921step1; decide +kernel
      have hl : raw21921step2Labels = raw21921step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21921step1 raw21921step1Labels permutation31 permutation7
    mixedMoment B raw21921step2 raw21921step2Labels = mixedMoment B raw21921step3 raw21921step3Labels := by
      have ha : raw21921step3 = raw21921step2 := by apply Matrix.ext; unfold raw21921step3 raw21921step2; decide +kernel
      have hl : raw21921step2Labels = labelEmbedding10 ∘ raw21921step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21921step2 raw21921step2Labels raw21921step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4837 node4837Labels := by rfl

theorem canonical21922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21922 raw21922Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw21922 raw21922Labels = mixedMoment B raw21922step0 raw21922step0Labels := by
      have hz : ∀ j, raw21922 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21922step0 = (fun i j => raw21922 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21922step0 raw21922; decide +kernel
      have hl : raw21922step0Labels = raw21922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21922 raw21922Labels permutation346 hz
    mixedMoment B raw21922step0 raw21922step0Labels = mixedMoment B raw21922step1 raw21922step1Labels := by
      have hz : ∀ j, raw21922step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21922step1 = (fun i j => raw21922step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21922step1 raw21922step0; decide +kernel
      have hl : raw21922step1Labels = raw21922step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21922step0 raw21922step0Labels permutation56 hz
    mixedMoment B raw21922step1 raw21922step1Labels = mixedMoment B raw21922step2 raw21922step2Labels := by
      have ha : raw21922step2 = (fun i j => raw21922step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21922step2 raw21922step1; decide +kernel
      have hl : raw21922step2Labels = raw21922step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21922step1 raw21922step1Labels permutation8 permutation7
    mixedMoment B raw21922step2 raw21922step2Labels = mixedMoment B raw21922step3 raw21922step3Labels := by
      have ha : raw21922step3 = -raw21922step2 := by apply Matrix.ext; change ∀ i j, raw21922step3 i j = -(raw21922step2 i j); unfold raw21922step3 raw21922step2; decide +kernel
      have hl : raw21922step3Labels = raw21922step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21922step3 raw21922step3Labels = mixedMoment B raw21922step4 raw21922step4Labels := by
      have ha : raw21922step4 = raw21922step3 := by apply Matrix.ext; unfold raw21922step4 raw21922step3; decide +kernel
      have hl : raw21922step3Labels = labelEmbedding10 ∘ raw21922step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21922step3 raw21922step3Labels raw21922step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4841 node4841Labels := by rfl

theorem canonical21923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21923 raw21923Labels = mixedMoment B node4140 node4140Labels := by
  calc
    mixedMoment B raw21923 raw21923Labels = mixedMoment B raw21923step0 raw21923step0Labels := by
      have hz : ∀ j, raw21923 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21923step0 = (fun i j => raw21923 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21923step0 raw21923; decide +kernel
      have hl : raw21923step0Labels = raw21923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21923 raw21923Labels permutation346 hz
    mixedMoment B raw21923step0 raw21923step0Labels = mixedMoment B raw21923step1 raw21923step1Labels := by
      have ha : raw21923step1 = (fun i j => raw21923step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21923step1 raw21923step0; decide +kernel
      have hl : raw21923step1Labels = raw21923step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21923step0 raw21923step0Labels permutation38 permutation2
    _ = mixedMoment B node4140 node4140Labels := by rfl

theorem canonical21924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21924 raw21924Labels = mixedMoment B node4320 node4320Labels := by
  calc
    mixedMoment B raw21924 raw21924Labels = mixedMoment B raw21924step0 raw21924step0Labels := by
      have ha : raw21924step0 = (fun i j => raw21924 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21924step0 raw21924; decide +kernel
      have hl : raw21924step0Labels = raw21924Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21924 raw21924Labels permutation182 permutation2
    _ = mixedMoment B node4320 node4320Labels := by rfl

theorem canonical21925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21925 raw21925Labels = mixedMoment B node4302 node4302Labels := by
  calc
    mixedMoment B raw21925 raw21925Labels = mixedMoment B raw21925step0 raw21925step0Labels := by
      have hz : ∀ j, raw21925 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21925step0 = (fun i j => raw21925 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21925step0 raw21925; decide +kernel
      have hl : raw21925step0Labels = raw21925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21925 raw21925Labels permutation346 hz
    mixedMoment B raw21925step0 raw21925step0Labels = mixedMoment B raw21925step1 raw21925step1Labels := by
      have ha : raw21925step1 = (fun i j => raw21925step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21925step1 raw21925step0; decide +kernel
      have hl : raw21925step1Labels = raw21925step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21925step0 raw21925step0Labels permutation38 permutation2
    _ = mixedMoment B node4302 node4302Labels := by rfl

theorem canonical21926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21926 raw21926Labels = mixedMoment B node4398 node4398Labels := by
  calc
    mixedMoment B raw21926 raw21926Labels = mixedMoment B raw21926step0 raw21926step0Labels := by
      have hz : ∀ j, raw21926 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21926step0 = (fun i j => raw21926 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21926step0 raw21926; decide +kernel
      have hl : raw21926step0Labels = raw21926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21926 raw21926Labels permutation346 hz
    mixedMoment B raw21926step0 raw21926step0Labels = mixedMoment B raw21926step1 raw21926step1Labels := by
      have ha : raw21926step1 = (fun i j => raw21926step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21926step1 raw21926step0; decide +kernel
      have hl : raw21926step1Labels = raw21926step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21926step0 raw21926step0Labels permutation40 permutation2
    _ = mixedMoment B node4398 node4398Labels := by rfl

theorem canonical21927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21927 raw21927Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw21927 raw21927Labels = mixedMoment B raw21927step0 raw21927step0Labels := by
      have hz : ∀ j, raw21927 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21927step0 = (fun i j => raw21927 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21927step0 raw21927; decide +kernel
      have hl : raw21927step0Labels = raw21927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21927 raw21927Labels permutation346 hz
    mixedMoment B raw21927step0 raw21927step0Labels = mixedMoment B raw21927step1 raw21927step1Labels := by
      have ha : raw21927step1 = (fun i j => raw21927step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21927step1 raw21927step0; decide +kernel
      have hl : raw21927step1Labels = raw21927step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21927step0 raw21927step0Labels permutation38 permutation2
    _ = mixedMoment B node4418 node4418Labels := by rfl

theorem canonical21928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21928 raw21928Labels = mixedMoment B node4140 node4140Labels := by
  calc
    mixedMoment B raw21928 raw21928Labels = mixedMoment B raw21928step0 raw21928step0Labels := by
      have hz : ∀ j, raw21928 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21928step0 = (fun i j => raw21928 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21928step0 raw21928; decide +kernel
      have hl : raw21928step0Labels = raw21928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21928 raw21928Labels permutation265 hz
    mixedMoment B raw21928step0 raw21928step0Labels = mixedMoment B raw21928step1 raw21928step1Labels := by
      have ha : raw21928step1 = (fun i j => raw21928step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21928step1 raw21928step0; decide +kernel
      have hl : raw21928step1Labels = raw21928step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21928step0 raw21928step0Labels permutation38 permutation2
    _ = mixedMoment B node4140 node4140Labels := by rfl

theorem canonical21929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21929 raw21929Labels = mixedMoment B node4320 node4320Labels := by
  calc
    mixedMoment B raw21929 raw21929Labels = mixedMoment B raw21929step0 raw21929step0Labels := by
      have ha : raw21929step0 = (fun i j => raw21929 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21929step0 raw21929; decide +kernel
      have hl : raw21929step0Labels = raw21929Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21929 raw21929Labels permutation158 permutation2
    _ = mixedMoment B node4320 node4320Labels := by rfl

theorem canonical21930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21930 raw21930Labels = mixedMoment B node4302 node4302Labels := by
  calc
    mixedMoment B raw21930 raw21930Labels = mixedMoment B raw21930step0 raw21930step0Labels := by
      have hz : ∀ j, raw21930 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21930step0 = (fun i j => raw21930 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21930step0 raw21930; decide +kernel
      have hl : raw21930step0Labels = raw21930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21930 raw21930Labels permutation265 hz
    mixedMoment B raw21930step0 raw21930step0Labels = mixedMoment B raw21930step1 raw21930step1Labels := by
      have ha : raw21930step1 = (fun i j => raw21930step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21930step1 raw21930step0; decide +kernel
      have hl : raw21930step1Labels = raw21930step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21930step0 raw21930step0Labels permutation38 permutation2
    _ = mixedMoment B node4302 node4302Labels := by rfl

theorem canonical21931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21931 raw21931Labels = mixedMoment B node4398 node4398Labels := by
  calc
    mixedMoment B raw21931 raw21931Labels = mixedMoment B raw21931step0 raw21931step0Labels := by
      have hz : ∀ j, raw21931 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21931step0 = (fun i j => raw21931 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21931step0 raw21931; decide +kernel
      have hl : raw21931step0Labels = raw21931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21931 raw21931Labels permutation265 hz
    mixedMoment B raw21931step0 raw21931step0Labels = mixedMoment B raw21931step1 raw21931step1Labels := by
      have ha : raw21931step1 = (fun i j => raw21931step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21931step1 raw21931step0; decide +kernel
      have hl : raw21931step1Labels = raw21931step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21931step0 raw21931step0Labels permutation40 permutation2
    _ = mixedMoment B node4398 node4398Labels := by rfl

theorem canonical21932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21932 raw21932Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw21932 raw21932Labels = mixedMoment B raw21932step0 raw21932step0Labels := by
      have hz : ∀ j, raw21932 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21932step0 = (fun i j => raw21932 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21932step0 raw21932; decide +kernel
      have hl : raw21932step0Labels = raw21932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21932 raw21932Labels permutation265 hz
    mixedMoment B raw21932step0 raw21932step0Labels = mixedMoment B raw21932step1 raw21932step1Labels := by
      have ha : raw21932step1 = (fun i j => raw21932step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21932step1 raw21932step0; decide +kernel
      have hl : raw21932step1Labels = raw21932step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21932step0 raw21932step0Labels permutation38 permutation2
    _ = mixedMoment B node4418 node4418Labels := by rfl

theorem canonical21933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21933 raw21933Labels = mixedMoment B node4166 node4166Labels := by
  calc
    mixedMoment B raw21933 raw21933Labels = mixedMoment B raw21933step0 raw21933step0Labels := by
      have hz : ∀ j, raw21933 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21933step0 = (fun i j => raw21933 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21933step0 raw21933; decide +kernel
      have hl : raw21933step0Labels = raw21933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21933 raw21933Labels permutation346 hz
    mixedMoment B raw21933step0 raw21933step0Labels = mixedMoment B raw21933step1 raw21933step1Labels := by
      have hz : ∀ j, raw21933step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21933step1 = (fun i j => raw21933step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21933step1 raw21933step0; decide +kernel
      have hl : raw21933step1Labels = raw21933step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21933step0 raw21933step0Labels permutation56 hz
    _ = mixedMoment B node4166 node4166Labels := by rfl

theorem canonical21934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21934 raw21934Labels = mixedMoment B node4338 node4338Labels := by
  calc
    mixedMoment B raw21934 raw21934Labels = mixedMoment B raw21934step0 raw21934step0Labels := by
      have hz : ∀ j, raw21934 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21934step0 = (fun i j => raw21934 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21934step0 raw21934; decide +kernel
      have hl : raw21934step0Labels = raw21934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21934 raw21934Labels permutation346 hz
    _ = mixedMoment B node4338 node4338Labels := by rfl

theorem canonical21935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21935 raw21935Labels = mixedMoment B node4338 node4338Labels := by
  calc
    mixedMoment B raw21935 raw21935Labels = mixedMoment B raw21935step0 raw21935step0Labels := by
      have hz : ∀ j, raw21935 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21935step0 = (fun i j => raw21935 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21935step0 raw21935; decide +kernel
      have hl : raw21935step0Labels = raw21935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21935 raw21935Labels permutation265 hz
    _ = mixedMoment B node4338 node4338Labels := by rfl

theorem canonical21936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21936 raw21936Labels = mixedMoment B node4454 node4454Labels := by
  calc
    mixedMoment B raw21936 raw21936Labels = mixedMoment B raw21936step0 raw21936step0Labels := by
      have hz : ∀ j, raw21936 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21936step0 = (fun i j => raw21936 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21936step0 raw21936; decide +kernel
      have hl : raw21936step0Labels = raw21936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21936 raw21936Labels permutation346 hz
    mixedMoment B raw21936step0 raw21936step0Labels = mixedMoment B raw21936step1 raw21936step1Labels := by
      have hz : ∀ j, raw21936step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21936step1 = (fun i j => raw21936step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21936step1 raw21936step0; decide +kernel
      have hl : raw21936step1Labels = raw21936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21936step0 raw21936step0Labels permutation56 hz
    mixedMoment B raw21936step1 raw21936step1Labels = mixedMoment B raw21936step2 raw21936step2Labels := by
      have ha : raw21936step2 = (fun i j => raw21936step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21936step2 raw21936step1; decide +kernel
      have hl : raw21936step2Labels = raw21936step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21936step1 raw21936step1Labels permutation10 permutation2
    _ = mixedMoment B node4454 node4454Labels := by rfl

theorem canonical21937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21937 raw21937Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw21937 raw21937Labels = mixedMoment B raw21937step0 raw21937step0Labels := by
      have hz : ∀ j, raw21937 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21937step0 = (fun i j => raw21937 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21937step0 raw21937; decide +kernel
      have hl : raw21937step0Labels = raw21937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21937 raw21937Labels permutation346 hz
    mixedMoment B raw21937step0 raw21937step0Labels = mixedMoment B raw21937step1 raw21937step1Labels := by
      have hz : ∀ j, raw21937step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21937step1 = (fun i j => raw21937step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21937step1 raw21937step0; decide +kernel
      have hl : raw21937step1Labels = raw21937step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21937step0 raw21937step0Labels permutation56 hz
    _ = mixedMoment B node4490 node4490Labels := by rfl

theorem canonical21938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21938 raw21938Labels = mixedMoment B node4147 node4147Labels := by
  calc
    mixedMoment B raw21938 raw21938Labels = mixedMoment B raw21938step0 raw21938step0Labels := by
      have hz : ∀ j, raw21938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21938step0 = (fun i j => raw21938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21938step0 raw21938; decide +kernel
      have hl : raw21938step0Labels = raw21938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21938 raw21938Labels permutation346 hz
    mixedMoment B raw21938step0 raw21938step0Labels = mixedMoment B raw21938step1 raw21938step1Labels := by
      have hz : ∀ j, raw21938step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21938step1 = (fun i j => raw21938step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21938step1 raw21938step0; decide +kernel
      have hl : raw21938step1Labels = raw21938step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21938step0 raw21938step0Labels permutation56 hz
    _ = mixedMoment B node4147 node4147Labels := by rfl

theorem canonical21939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21939 raw21939Labels = mixedMoment B node4324 node4324Labels := by
  calc
    mixedMoment B raw21939 raw21939Labels = mixedMoment B raw21939step0 raw21939step0Labels := by
      have hz : ∀ j, raw21939 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21939step0 = (fun i j => raw21939 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21939step0 raw21939; decide +kernel
      have hl : raw21939step0Labels = raw21939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21939 raw21939Labels permutation346 hz
    _ = mixedMoment B node4324 node4324Labels := by rfl

theorem canonical21940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21940 raw21940Labels = mixedMoment B node4324 node4324Labels := by
  calc
    mixedMoment B raw21940 raw21940Labels = mixedMoment B raw21940step0 raw21940step0Labels := by
      have hz : ∀ j, raw21940 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21940step0 = (fun i j => raw21940 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21940step0 raw21940; decide +kernel
      have hl : raw21940step0Labels = raw21940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21940 raw21940Labels permutation265 hz
    _ = mixedMoment B node4324 node4324Labels := by rfl

theorem canonical21941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21941 raw21941Labels = mixedMoment B node4317 node4317Labels := by
  calc
    mixedMoment B raw21941 raw21941Labels = mixedMoment B raw21941step0 raw21941step0Labels := by
      have hz : ∀ j, raw21941 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21941step0 = (fun i j => raw21941 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21941step0 raw21941; decide +kernel
      have hl : raw21941step0Labels = raw21941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21941 raw21941Labels permutation346 hz
    mixedMoment B raw21941step0 raw21941step0Labels = mixedMoment B raw21941step1 raw21941step1Labels := by
      have hz : ∀ j, raw21941step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21941step1 = (fun i j => raw21941step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21941step1 raw21941step0; decide +kernel
      have hl : raw21941step1Labels = raw21941step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21941step0 raw21941step0Labels permutation56 hz
    _ = mixedMoment B node4317 node4317Labels := by rfl

theorem canonical21942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21942 raw21942Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw21942 raw21942Labels = mixedMoment B raw21942step0 raw21942step0Labels := by
      have hz : ∀ j, raw21942 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21942step0 = (fun i j => raw21942 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21942step0 raw21942; decide +kernel
      have hl : raw21942step0Labels = raw21942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21942 raw21942Labels permutation346 hz
    mixedMoment B raw21942step0 raw21942step0Labels = mixedMoment B raw21942step1 raw21942step1Labels := by
      have hz : ∀ j, raw21942step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21942step1 = (fun i j => raw21942step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21942step1 raw21942step0; decide +kernel
      have hl : raw21942step1Labels = raw21942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21942step0 raw21942step0Labels permutation56 hz
    _ = mixedMoment B node4431 node4431Labels := by rfl

theorem canonical21943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21943 raw21943Labels = mixedMoment B node4146 node4146Labels := by
  calc
    mixedMoment B raw21943 raw21943Labels = mixedMoment B raw21943step0 raw21943step0Labels := by
      have hz : ∀ j, raw21943 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21943step0 = (fun i j => raw21943 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21943step0 raw21943; decide +kernel
      have hl : raw21943step0Labels = raw21943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21943 raw21943Labels permutation346 hz
    mixedMoment B raw21943step0 raw21943step0Labels = mixedMoment B raw21943step1 raw21943step1Labels := by
      have hz : ∀ j, raw21943step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21943step1 = (fun i j => raw21943step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21943step1 raw21943step0; decide +kernel
      have hl : raw21943step1Labels = raw21943step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21943step0 raw21943step0Labels permutation56 hz
    _ = mixedMoment B node4146 node4146Labels := by rfl

theorem canonical21944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21944 raw21944Labels = mixedMoment B node4289 node4289Labels := by
  calc
    mixedMoment B raw21944 raw21944Labels = mixedMoment B raw21944step0 raw21944step0Labels := by
      have hz : ∀ j, raw21944 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21944step0 = (fun i j => raw21944 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21944step0 raw21944; decide +kernel
      have hl : raw21944step0Labels = raw21944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21944 raw21944Labels permutation346 hz
    mixedMoment B raw21944step0 raw21944step0Labels = mixedMoment B raw21944step1 raw21944step1Labels := by
      have ha : raw21944step1 = (fun i j => raw21944step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21944step1 raw21944step0; decide +kernel
      have hl : raw21944step1Labels = raw21944step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21944step0 raw21944step0Labels permutation151 permutation2
    mixedMoment B raw21944step1 raw21944step1Labels = mixedMoment B raw21944step2 raw21944step2Labels := by
      have ha : raw21944step2 = -raw21944step1 := by apply Matrix.ext; change ∀ i j, raw21944step2 i j = -(raw21944step1 i j); unfold raw21944step2 raw21944step1; decide +kernel
      have hl : raw21944step2Labels = raw21944step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4289 node4289Labels := by rfl

theorem canonical21945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21945 raw21945Labels = mixedMoment B node4289 node4289Labels := by
  calc
    mixedMoment B raw21945 raw21945Labels = mixedMoment B raw21945step0 raw21945step0Labels := by
      have hz : ∀ j, raw21945 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21945step0 = (fun i j => raw21945 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21945step0 raw21945; decide +kernel
      have hl : raw21945step0Labels = raw21945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21945 raw21945Labels permutation265 hz
    mixedMoment B raw21945step0 raw21945step0Labels = mixedMoment B raw21945step1 raw21945step1Labels := by
      have ha : raw21945step1 = (fun i j => raw21945step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21945step1 raw21945step0; decide +kernel
      have hl : raw21945step1Labels = raw21945step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21945step0 raw21945step0Labels permutation151 permutation2
    mixedMoment B raw21945step1 raw21945step1Labels = mixedMoment B raw21945step2 raw21945step2Labels := by
      have ha : raw21945step2 = -raw21945step1 := by apply Matrix.ext; change ∀ i j, raw21945step2 i j = -(raw21945step1 i j); unfold raw21945step2 raw21945step1; decide +kernel
      have hl : raw21945step2Labels = raw21945step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4289 node4289Labels := by rfl

theorem canonical21946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21946 raw21946Labels = mixedMoment B node4312 node4312Labels := by
  calc
    mixedMoment B raw21946 raw21946Labels = mixedMoment B raw21946step0 raw21946step0Labels := by
      have hz : ∀ j, raw21946 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21946step0 = (fun i j => raw21946 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21946step0 raw21946; decide +kernel
      have hl : raw21946step0Labels = raw21946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21946 raw21946Labels permutation346 hz
    mixedMoment B raw21946step0 raw21946step0Labels = mixedMoment B raw21946step1 raw21946step1Labels := by
      have hz : ∀ j, raw21946step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21946step1 = (fun i j => raw21946step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21946step1 raw21946step0; decide +kernel
      have hl : raw21946step1Labels = raw21946step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21946step0 raw21946step0Labels permutation56 hz
    _ = mixedMoment B node4312 node4312Labels := by rfl

theorem canonical21947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21947 raw21947Labels = mixedMoment B node4405 node4405Labels := by
  calc
    mixedMoment B raw21947 raw21947Labels = mixedMoment B raw21947step0 raw21947step0Labels := by
      have hz : ∀ j, raw21947 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21947step0 = (fun i j => raw21947 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21947step0 raw21947; decide +kernel
      have hl : raw21947step0Labels = raw21947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21947 raw21947Labels permutation346 hz
    mixedMoment B raw21947step0 raw21947step0Labels = mixedMoment B raw21947step1 raw21947step1Labels := by
      have hz : ∀ j, raw21947step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21947step1 = (fun i j => raw21947step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21947step1 raw21947step0; decide +kernel
      have hl : raw21947step1Labels = raw21947step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21947step0 raw21947step0Labels permutation56 hz
    _ = mixedMoment B node4405 node4405Labels := by rfl

theorem canonical21948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21948 raw21948Labels = mixedMoment B node1911 node1911Labels := by
  calc
    mixedMoment B raw21948 raw21948Labels = mixedMoment B raw21948step0 raw21948step0Labels := by
      have hz : ∀ j, raw21948 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21948step0 = (fun i j => raw21948 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21948step0 raw21948; decide +kernel
      have hl : raw21948step0Labels = raw21948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21948 raw21948Labels permutation346 hz
    mixedMoment B raw21948step0 raw21948step0Labels = mixedMoment B raw21948step1 raw21948step1Labels := by
      have ha : raw21948step1 = (fun i j => raw21948step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21948step1 raw21948step0; decide +kernel
      have hl : raw21948step1Labels = raw21948step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21948step0 raw21948step0Labels permutation149 permutation7
    mixedMoment B raw21948step1 raw21948step1Labels = mixedMoment B raw21948step2 raw21948step2Labels := by
      have ha : raw21948step2 = raw21948step1 := by apply Matrix.ext; unfold raw21948step2 raw21948step1; decide +kernel
      have hl : raw21948step1Labels = labelEmbedding1 ∘ raw21948step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21948step1 raw21948step1Labels raw21948step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1911 node1911Labels := by rfl

theorem canonical21949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21949 raw21949Labels = mixedMoment B node1911 node1911Labels := by
  calc
    mixedMoment B raw21949 raw21949Labels = mixedMoment B raw21949step0 raw21949step0Labels := by
      have hz : ∀ j, raw21949 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21949step0 = (fun i j => raw21949 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21949step0 raw21949; decide +kernel
      have hl : raw21949step0Labels = raw21949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21949 raw21949Labels permutation265 hz
    mixedMoment B raw21949step0 raw21949step0Labels = mixedMoment B raw21949step1 raw21949step1Labels := by
      have ha : raw21949step1 = (fun i j => raw21949step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21949step1 raw21949step0; decide +kernel
      have hl : raw21949step1Labels = raw21949step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21949step0 raw21949step0Labels permutation149 permutation7
    mixedMoment B raw21949step1 raw21949step1Labels = mixedMoment B raw21949step2 raw21949step2Labels := by
      have ha : raw21949step2 = raw21949step1 := by apply Matrix.ext; unfold raw21949step2 raw21949step1; decide +kernel
      have hl : raw21949step1Labels = labelEmbedding1 ∘ raw21949step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21949step1 raw21949step1Labels raw21949step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1911 node1911Labels := by rfl

theorem canonical21950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21950 raw21950Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw21950 raw21950Labels = mixedMoment B raw21950step0 raw21950step0Labels := by
      have hz : ∀ j, raw21950 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21950step0 = (fun i j => raw21950 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21950step0 raw21950; decide +kernel
      have hl : raw21950step0Labels = raw21950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21950 raw21950Labels permutation346 hz
    mixedMoment B raw21950step0 raw21950step0Labels = mixedMoment B raw21950step1 raw21950step1Labels := by
      have hz : ∀ j, raw21950step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21950step1 = (fun i j => raw21950step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21950step1 raw21950step0; decide +kernel
      have hl : raw21950step1Labels = raw21950step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21950step0 raw21950step0Labels permutation56 hz
    mixedMoment B raw21950step1 raw21950step1Labels = mixedMoment B raw21950step2 raw21950step2Labels := by
      have hz : ∀ i, raw21950step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw21950step2 = (fun i j => raw21950step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw21950step2 raw21950step1; decide +kernel
      have hl : raw21950step2Labels = (fun j => raw21950step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw21950step1 raw21950step1Labels permutation4 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical21951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21951 raw21951Labels = mixedMoment B node2056 node2056Labels := by
  calc
    mixedMoment B raw21951 raw21951Labels = mixedMoment B raw21951step0 raw21951step0Labels := by
      have hz : ∀ j, raw21951 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21951step0 = (fun i j => raw21951 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21951step0 raw21951; decide +kernel
      have hl : raw21951step0Labels = raw21951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21951 raw21951Labels permutation346 hz
    mixedMoment B raw21951step0 raw21951step0Labels = mixedMoment B raw21951step1 raw21951step1Labels := by
      have hz : ∀ j, raw21951step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21951step1 = (fun i j => raw21951step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21951step1 raw21951step0; decide +kernel
      have hl : raw21951step1Labels = raw21951step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21951step0 raw21951step0Labels permutation56 hz
    mixedMoment B raw21951step1 raw21951step1Labels = mixedMoment B raw21951step2 raw21951step2Labels := by
      have ha : raw21951step2 = (fun i j => raw21951step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21951step2 raw21951step1; decide +kernel
      have hl : raw21951step2Labels = raw21951step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21951step1 raw21951step1Labels permutation31 permutation7
    mixedMoment B raw21951step2 raw21951step2Labels = mixedMoment B raw21951step3 raw21951step3Labels := by
      have ha : raw21951step3 = raw21951step2 := by apply Matrix.ext; unfold raw21951step3 raw21951step2; decide +kernel
      have hl : raw21951step2Labels = labelEmbedding1 ∘ raw21951step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21951step2 raw21951step2Labels raw21951step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2056 node2056Labels := by rfl

theorem canonical21952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21952 raw21952Labels = mixedMoment B node2060 node2060Labels := by
  calc
    mixedMoment B raw21952 raw21952Labels = mixedMoment B raw21952step0 raw21952step0Labels := by
      have hz : ∀ j, raw21952 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21952step0 = (fun i j => raw21952 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21952step0 raw21952; decide +kernel
      have hl : raw21952step0Labels = raw21952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21952 raw21952Labels permutation346 hz
    mixedMoment B raw21952step0 raw21952step0Labels = mixedMoment B raw21952step1 raw21952step1Labels := by
      have hz : ∀ j, raw21952step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21952step1 = (fun i j => raw21952step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21952step1 raw21952step0; decide +kernel
      have hl : raw21952step1Labels = raw21952step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21952step0 raw21952step0Labels permutation56 hz
    mixedMoment B raw21952step1 raw21952step1Labels = mixedMoment B raw21952step2 raw21952step2Labels := by
      have ha : raw21952step2 = (fun i j => raw21952step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21952step2 raw21952step1; decide +kernel
      have hl : raw21952step2Labels = raw21952step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21952step1 raw21952step1Labels permutation8 permutation7
    mixedMoment B raw21952step2 raw21952step2Labels = mixedMoment B raw21952step3 raw21952step3Labels := by
      have ha : raw21952step3 = -raw21952step2 := by apply Matrix.ext; change ∀ i j, raw21952step3 i j = -(raw21952step2 i j); unfold raw21952step3 raw21952step2; decide +kernel
      have hl : raw21952step3Labels = raw21952step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21952step3 raw21952step3Labels = mixedMoment B raw21952step4 raw21952step4Labels := by
      have ha : raw21952step4 = raw21952step3 := by apply Matrix.ext; unfold raw21952step4 raw21952step3; decide +kernel
      have hl : raw21952step3Labels = labelEmbedding1 ∘ raw21952step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21952step3 raw21952step3Labels raw21952step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2060 node2060Labels := by rfl

theorem canonical21953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21953 raw21953Labels = mixedMoment B node1489 node1489Labels := by
  calc
    mixedMoment B raw21953 raw21953Labels = mixedMoment B raw21953step0 raw21953step0Labels := by
      have hz : ∀ j, raw21953 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21953step0 = (fun i j => raw21953 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21953step0 raw21953; decide +kernel
      have hl : raw21953step0Labels = raw21953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21953 raw21953Labels permutation346 hz
    mixedMoment B raw21953step0 raw21953step0Labels = mixedMoment B raw21953step1 raw21953step1Labels := by
      have ha : raw21953step1 = (fun i j => raw21953step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21953step1 raw21953step0; decide +kernel
      have hl : raw21953step1Labels = raw21953step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21953step0 raw21953step0Labels permutation38 permutation7
    mixedMoment B raw21953step1 raw21953step1Labels = mixedMoment B raw21953step2 raw21953step2Labels := by
      have ha : raw21953step2 = -raw21953step1 := by apply Matrix.ext; change ∀ i j, raw21953step2 i j = -(raw21953step1 i j); unfold raw21953step2 raw21953step1; decide +kernel
      have hl : raw21953step2Labels = raw21953step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21953step2 raw21953step2Labels = mixedMoment B raw21953step3 raw21953step3Labels := by
      have ha : raw21953step3 = raw21953step2 := by apply Matrix.ext; unfold raw21953step3 raw21953step2; decide +kernel
      have hl : raw21953step2Labels = labelEmbedding1 ∘ raw21953step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21953step2 raw21953step2Labels raw21953step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1489 node1489Labels := by rfl

theorem canonical21954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21954 raw21954Labels = mixedMoment B node1586 node1586Labels := by
  calc
    mixedMoment B raw21954 raw21954Labels = mixedMoment B raw21954step0 raw21954step0Labels := by
      have ha : raw21954step0 = (fun i j => raw21954 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21954step0 raw21954; decide +kernel
      have hl : raw21954step0Labels = raw21954Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21954 raw21954Labels permutation206 permutation7
    mixedMoment B raw21954step0 raw21954step0Labels = mixedMoment B raw21954step1 raw21954step1Labels := by
      have ha : raw21954step1 = -raw21954step0 := by apply Matrix.ext; change ∀ i j, raw21954step1 i j = -(raw21954step0 i j); unfold raw21954step1 raw21954step0; decide +kernel
      have hl : raw21954step1Labels = raw21954step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21954step1 raw21954step1Labels = mixedMoment B raw21954step2 raw21954step2Labels := by
      have ha : raw21954step2 = raw21954step1 := by apply Matrix.ext; unfold raw21954step2 raw21954step1; decide +kernel
      have hl : raw21954step1Labels = labelEmbedding1 ∘ raw21954step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21954step1 raw21954step1Labels raw21954step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1586 node1586Labels := by rfl

theorem canonical21955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21955 raw21955Labels = mixedMoment B node1557 node1557Labels := by
  calc
    mixedMoment B raw21955 raw21955Labels = mixedMoment B raw21955step0 raw21955step0Labels := by
      have hz : ∀ j, raw21955 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21955step0 = (fun i j => raw21955 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21955step0 raw21955; decide +kernel
      have hl : raw21955step0Labels = raw21955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21955 raw21955Labels permutation346 hz
    mixedMoment B raw21955step0 raw21955step0Labels = mixedMoment B raw21955step1 raw21955step1Labels := by
      have ha : raw21955step1 = (fun i j => raw21955step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21955step1 raw21955step0; decide +kernel
      have hl : raw21955step1Labels = raw21955step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21955step0 raw21955step0Labels permutation38 permutation7
    mixedMoment B raw21955step1 raw21955step1Labels = mixedMoment B raw21955step2 raw21955step2Labels := by
      have ha : raw21955step2 = -raw21955step1 := by apply Matrix.ext; change ∀ i j, raw21955step2 i j = -(raw21955step1 i j); unfold raw21955step2 raw21955step1; decide +kernel
      have hl : raw21955step2Labels = raw21955step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21955step2 raw21955step2Labels = mixedMoment B raw21955step3 raw21955step3Labels := by
      have ha : raw21955step3 = raw21955step2 := by apply Matrix.ext; unfold raw21955step3 raw21955step2; decide +kernel
      have hl : raw21955step2Labels = labelEmbedding1 ∘ raw21955step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21955step2 raw21955step2Labels raw21955step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1557 node1557Labels := by rfl

theorem canonical21956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21956 raw21956Labels = mixedMoment B node1599 node1599Labels := by
  calc
    mixedMoment B raw21956 raw21956Labels = mixedMoment B raw21956step0 raw21956step0Labels := by
      have hz : ∀ j, raw21956 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21956step0 = (fun i j => raw21956 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21956step0 raw21956; decide +kernel
      have hl : raw21956step0Labels = raw21956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21956 raw21956Labels permutation346 hz
    mixedMoment B raw21956step0 raw21956step0Labels = mixedMoment B raw21956step1 raw21956step1Labels := by
      have ha : raw21956step1 = (fun i j => raw21956step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21956step1 raw21956step0; decide +kernel
      have hl : raw21956step1Labels = raw21956step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21956step0 raw21956step0Labels permutation38 permutation7
    mixedMoment B raw21956step1 raw21956step1Labels = mixedMoment B raw21956step2 raw21956step2Labels := by
      have ha : raw21956step2 = -raw21956step1 := by apply Matrix.ext; change ∀ i j, raw21956step2 i j = -(raw21956step1 i j); unfold raw21956step2 raw21956step1; decide +kernel
      have hl : raw21956step2Labels = raw21956step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21956step2 raw21956step2Labels = mixedMoment B raw21956step3 raw21956step3Labels := by
      have ha : raw21956step3 = raw21956step2 := by apply Matrix.ext; unfold raw21956step3 raw21956step2; decide +kernel
      have hl : raw21956step2Labels = labelEmbedding1 ∘ raw21956step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21956step2 raw21956step2Labels raw21956step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1599 node1599Labels := by rfl

theorem canonical21957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21957 raw21957Labels = mixedMoment B node1602 node1602Labels := by
  calc
    mixedMoment B raw21957 raw21957Labels = mixedMoment B raw21957step0 raw21957step0Labels := by
      have hz : ∀ j, raw21957 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21957step0 = (fun i j => raw21957 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21957step0 raw21957; decide +kernel
      have hl : raw21957step0Labels = raw21957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21957 raw21957Labels permutation346 hz
    mixedMoment B raw21957step0 raw21957step0Labels = mixedMoment B raw21957step1 raw21957step1Labels := by
      have ha : raw21957step1 = (fun i j => raw21957step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21957step1 raw21957step0; decide +kernel
      have hl : raw21957step1Labels = raw21957step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21957step0 raw21957step0Labels permutation38 permutation7
    mixedMoment B raw21957step1 raw21957step1Labels = mixedMoment B raw21957step2 raw21957step2Labels := by
      have ha : raw21957step2 = -raw21957step1 := by apply Matrix.ext; change ∀ i j, raw21957step2 i j = -(raw21957step1 i j); unfold raw21957step2 raw21957step1; decide +kernel
      have hl : raw21957step2Labels = raw21957step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21957step2 raw21957step2Labels = mixedMoment B raw21957step3 raw21957step3Labels := by
      have ha : raw21957step3 = raw21957step2 := by apply Matrix.ext; unfold raw21957step3 raw21957step2; decide +kernel
      have hl : raw21957step2Labels = labelEmbedding1 ∘ raw21957step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21957step2 raw21957step2Labels raw21957step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1602 node1602Labels := by rfl

theorem canonical21958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21958 raw21958Labels = mixedMoment B node1489 node1489Labels := by
  calc
    mixedMoment B raw21958 raw21958Labels = mixedMoment B raw21958step0 raw21958step0Labels := by
      have hz : ∀ j, raw21958 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21958step0 = (fun i j => raw21958 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21958step0 raw21958; decide +kernel
      have hl : raw21958step0Labels = raw21958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21958 raw21958Labels permutation265 hz
    mixedMoment B raw21958step0 raw21958step0Labels = mixedMoment B raw21958step1 raw21958step1Labels := by
      have ha : raw21958step1 = (fun i j => raw21958step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21958step1 raw21958step0; decide +kernel
      have hl : raw21958step1Labels = raw21958step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21958step0 raw21958step0Labels permutation38 permutation7
    mixedMoment B raw21958step1 raw21958step1Labels = mixedMoment B raw21958step2 raw21958step2Labels := by
      have ha : raw21958step2 = -raw21958step1 := by apply Matrix.ext; change ∀ i j, raw21958step2 i j = -(raw21958step1 i j); unfold raw21958step2 raw21958step1; decide +kernel
      have hl : raw21958step2Labels = raw21958step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21958step2 raw21958step2Labels = mixedMoment B raw21958step3 raw21958step3Labels := by
      have ha : raw21958step3 = raw21958step2 := by apply Matrix.ext; unfold raw21958step3 raw21958step2; decide +kernel
      have hl : raw21958step2Labels = labelEmbedding1 ∘ raw21958step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21958step2 raw21958step2Labels raw21958step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1489 node1489Labels := by rfl

theorem canonical21959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21959 raw21959Labels = mixedMoment B node1586 node1586Labels := by
  calc
    mixedMoment B raw21959 raw21959Labels = mixedMoment B raw21959step0 raw21959step0Labels := by
      have ha : raw21959step0 = (fun i j => raw21959 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21959step0 raw21959; decide +kernel
      have hl : raw21959step0Labels = raw21959Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21959 raw21959Labels permutation200 permutation7
    mixedMoment B raw21959step0 raw21959step0Labels = mixedMoment B raw21959step1 raw21959step1Labels := by
      have ha : raw21959step1 = -raw21959step0 := by apply Matrix.ext; change ∀ i j, raw21959step1 i j = -(raw21959step0 i j); unfold raw21959step1 raw21959step0; decide +kernel
      have hl : raw21959step1Labels = raw21959step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21959step1 raw21959step1Labels = mixedMoment B raw21959step2 raw21959step2Labels := by
      have ha : raw21959step2 = raw21959step1 := by apply Matrix.ext; unfold raw21959step2 raw21959step1; decide +kernel
      have hl : raw21959step1Labels = labelEmbedding1 ∘ raw21959step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21959step1 raw21959step1Labels raw21959step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1586 node1586Labels := by rfl

theorem canonical21960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21960 raw21960Labels = mixedMoment B node1557 node1557Labels := by
  calc
    mixedMoment B raw21960 raw21960Labels = mixedMoment B raw21960step0 raw21960step0Labels := by
      have hz : ∀ j, raw21960 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21960step0 = (fun i j => raw21960 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21960step0 raw21960; decide +kernel
      have hl : raw21960step0Labels = raw21960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21960 raw21960Labels permutation265 hz
    mixedMoment B raw21960step0 raw21960step0Labels = mixedMoment B raw21960step1 raw21960step1Labels := by
      have ha : raw21960step1 = (fun i j => raw21960step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21960step1 raw21960step0; decide +kernel
      have hl : raw21960step1Labels = raw21960step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21960step0 raw21960step0Labels permutation38 permutation7
    mixedMoment B raw21960step1 raw21960step1Labels = mixedMoment B raw21960step2 raw21960step2Labels := by
      have ha : raw21960step2 = -raw21960step1 := by apply Matrix.ext; change ∀ i j, raw21960step2 i j = -(raw21960step1 i j); unfold raw21960step2 raw21960step1; decide +kernel
      have hl : raw21960step2Labels = raw21960step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21960step2 raw21960step2Labels = mixedMoment B raw21960step3 raw21960step3Labels := by
      have ha : raw21960step3 = raw21960step2 := by apply Matrix.ext; unfold raw21960step3 raw21960step2; decide +kernel
      have hl : raw21960step2Labels = labelEmbedding1 ∘ raw21960step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21960step2 raw21960step2Labels raw21960step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1557 node1557Labels := by rfl

theorem canonical21961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21961 raw21961Labels = mixedMoment B node1599 node1599Labels := by
  calc
    mixedMoment B raw21961 raw21961Labels = mixedMoment B raw21961step0 raw21961step0Labels := by
      have hz : ∀ j, raw21961 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21961step0 = (fun i j => raw21961 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21961step0 raw21961; decide +kernel
      have hl : raw21961step0Labels = raw21961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21961 raw21961Labels permutation265 hz
    mixedMoment B raw21961step0 raw21961step0Labels = mixedMoment B raw21961step1 raw21961step1Labels := by
      have ha : raw21961step1 = (fun i j => raw21961step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21961step1 raw21961step0; decide +kernel
      have hl : raw21961step1Labels = raw21961step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21961step0 raw21961step0Labels permutation38 permutation7
    mixedMoment B raw21961step1 raw21961step1Labels = mixedMoment B raw21961step2 raw21961step2Labels := by
      have ha : raw21961step2 = -raw21961step1 := by apply Matrix.ext; change ∀ i j, raw21961step2 i j = -(raw21961step1 i j); unfold raw21961step2 raw21961step1; decide +kernel
      have hl : raw21961step2Labels = raw21961step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21961step2 raw21961step2Labels = mixedMoment B raw21961step3 raw21961step3Labels := by
      have ha : raw21961step3 = raw21961step2 := by apply Matrix.ext; unfold raw21961step3 raw21961step2; decide +kernel
      have hl : raw21961step2Labels = labelEmbedding1 ∘ raw21961step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21961step2 raw21961step2Labels raw21961step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1599 node1599Labels := by rfl

theorem canonical21962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21962 raw21962Labels = mixedMoment B node1602 node1602Labels := by
  calc
    mixedMoment B raw21962 raw21962Labels = mixedMoment B raw21962step0 raw21962step0Labels := by
      have hz : ∀ j, raw21962 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21962step0 = (fun i j => raw21962 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21962step0 raw21962; decide +kernel
      have hl : raw21962step0Labels = raw21962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21962 raw21962Labels permutation265 hz
    mixedMoment B raw21962step0 raw21962step0Labels = mixedMoment B raw21962step1 raw21962step1Labels := by
      have ha : raw21962step1 = (fun i j => raw21962step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21962step1 raw21962step0; decide +kernel
      have hl : raw21962step1Labels = raw21962step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21962step0 raw21962step0Labels permutation38 permutation7
    mixedMoment B raw21962step1 raw21962step1Labels = mixedMoment B raw21962step2 raw21962step2Labels := by
      have ha : raw21962step2 = -raw21962step1 := by apply Matrix.ext; change ∀ i j, raw21962step2 i j = -(raw21962step1 i j); unfold raw21962step2 raw21962step1; decide +kernel
      have hl : raw21962step2Labels = raw21962step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21962step2 raw21962step2Labels = mixedMoment B raw21962step3 raw21962step3Labels := by
      have ha : raw21962step3 = raw21962step2 := by apply Matrix.ext; unfold raw21962step3 raw21962step2; decide +kernel
      have hl : raw21962step2Labels = labelEmbedding1 ∘ raw21962step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21962step2 raw21962step2Labels raw21962step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1602 node1602Labels := by rfl

theorem canonical21963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21963 raw21963Labels = mixedMoment B node1499 node1499Labels := by
  calc
    mixedMoment B raw21963 raw21963Labels = mixedMoment B raw21963step0 raw21963step0Labels := by
      have hz : ∀ j, raw21963 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21963step0 = (fun i j => raw21963 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21963step0 raw21963; decide +kernel
      have hl : raw21963step0Labels = raw21963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21963 raw21963Labels permutation346 hz
    mixedMoment B raw21963step0 raw21963step0Labels = mixedMoment B raw21963step1 raw21963step1Labels := by
      have hz : ∀ j, raw21963step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21963step1 = (fun i j => raw21963step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21963step1 raw21963step0; decide +kernel
      have hl : raw21963step1Labels = raw21963step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21963step0 raw21963step0Labels permutation56 hz
    mixedMoment B raw21963step1 raw21963step1Labels = mixedMoment B raw21963step2 raw21963step2Labels := by
      have ha : raw21963step2 = (fun i j => raw21963step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21963step2 raw21963step1; decide +kernel
      have hl : raw21963step2Labels = raw21963step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21963step1 raw21963step1Labels permutation8 permutation7
    mixedMoment B raw21963step2 raw21963step2Labels = mixedMoment B raw21963step3 raw21963step3Labels := by
      have ha : raw21963step3 = -raw21963step2 := by apply Matrix.ext; change ∀ i j, raw21963step3 i j = -(raw21963step2 i j); unfold raw21963step3 raw21963step2; decide +kernel
      have hl : raw21963step3Labels = raw21963step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21963step3 raw21963step3Labels = mixedMoment B raw21963step4 raw21963step4Labels := by
      have ha : raw21963step4 = raw21963step3 := by apply Matrix.ext; unfold raw21963step4 raw21963step3; decide +kernel
      have hl : raw21963step3Labels = labelEmbedding1 ∘ raw21963step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21963step3 raw21963step3Labels raw21963step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1499 node1499Labels := by rfl

theorem canonical21964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21964 raw21964Labels = mixedMoment B node1633 node1633Labels := by
  calc
    mixedMoment B raw21964 raw21964Labels = mixedMoment B raw21964step0 raw21964step0Labels := by
      have hz : ∀ j, raw21964 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21964step0 = (fun i j => raw21964 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21964step0 raw21964; decide +kernel
      have hl : raw21964step0Labels = raw21964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21964 raw21964Labels permutation346 hz
    mixedMoment B raw21964step0 raw21964step0Labels = mixedMoment B raw21964step1 raw21964step1Labels := by
      have ha : raw21964step1 = (fun i j => raw21964step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21964step1 raw21964step0; decide +kernel
      have hl : raw21964step1Labels = raw21964step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21964step0 raw21964step0Labels permutation38 permutation7
    mixedMoment B raw21964step1 raw21964step1Labels = mixedMoment B raw21964step2 raw21964step2Labels := by
      have ha : raw21964step2 = -raw21964step1 := by apply Matrix.ext; change ∀ i j, raw21964step2 i j = -(raw21964step1 i j); unfold raw21964step2 raw21964step1; decide +kernel
      have hl : raw21964step2Labels = raw21964step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21964step2 raw21964step2Labels = mixedMoment B raw21964step3 raw21964step3Labels := by
      have ha : raw21964step3 = raw21964step2 := by apply Matrix.ext; unfold raw21964step3 raw21964step2; decide +kernel
      have hl : raw21964step2Labels = labelEmbedding1 ∘ raw21964step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21964step2 raw21964step2Labels raw21964step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1633 node1633Labels := by rfl

theorem canonical21965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21965 raw21965Labels = mixedMoment B node1633 node1633Labels := by
  calc
    mixedMoment B raw21965 raw21965Labels = mixedMoment B raw21965step0 raw21965step0Labels := by
      have hz : ∀ j, raw21965 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21965step0 = (fun i j => raw21965 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21965step0 raw21965; decide +kernel
      have hl : raw21965step0Labels = raw21965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21965 raw21965Labels permutation265 hz
    mixedMoment B raw21965step0 raw21965step0Labels = mixedMoment B raw21965step1 raw21965step1Labels := by
      have ha : raw21965step1 = (fun i j => raw21965step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21965step1 raw21965step0; decide +kernel
      have hl : raw21965step1Labels = raw21965step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21965step0 raw21965step0Labels permutation38 permutation7
    mixedMoment B raw21965step1 raw21965step1Labels = mixedMoment B raw21965step2 raw21965step2Labels := by
      have ha : raw21965step2 = -raw21965step1 := by apply Matrix.ext; change ∀ i j, raw21965step2 i j = -(raw21965step1 i j); unfold raw21965step2 raw21965step1; decide +kernel
      have hl : raw21965step2Labels = raw21965step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21965step2 raw21965step2Labels = mixedMoment B raw21965step3 raw21965step3Labels := by
      have ha : raw21965step3 = raw21965step2 := by apply Matrix.ext; unfold raw21965step3 raw21965step2; decide +kernel
      have hl : raw21965step2Labels = labelEmbedding1 ∘ raw21965step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21965step2 raw21965step2Labels raw21965step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1633 node1633Labels := by rfl

theorem canonical21966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21966 raw21966Labels = mixedMoment B node1647 node1647Labels := by
  calc
    mixedMoment B raw21966 raw21966Labels = mixedMoment B raw21966step0 raw21966step0Labels := by
      have hz : ∀ j, raw21966 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21966step0 = (fun i j => raw21966 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21966step0 raw21966; decide +kernel
      have hl : raw21966step0Labels = raw21966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21966 raw21966Labels permutation346 hz
    mixedMoment B raw21966step0 raw21966step0Labels = mixedMoment B raw21966step1 raw21966step1Labels := by
      have hz : ∀ j, raw21966step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21966step1 = (fun i j => raw21966step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21966step1 raw21966step0; decide +kernel
      have hl : raw21966step1Labels = raw21966step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21966step0 raw21966step0Labels permutation56 hz
    mixedMoment B raw21966step1 raw21966step1Labels = mixedMoment B raw21966step2 raw21966step2Labels := by
      have ha : raw21966step2 = (fun i j => raw21966step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21966step2 raw21966step1; decide +kernel
      have hl : raw21966step2Labels = raw21966step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21966step1 raw21966step1Labels permutation8 permutation7
    mixedMoment B raw21966step2 raw21966step2Labels = mixedMoment B raw21966step3 raw21966step3Labels := by
      have ha : raw21966step3 = -raw21966step2 := by apply Matrix.ext; change ∀ i j, raw21966step3 i j = -(raw21966step2 i j); unfold raw21966step3 raw21966step2; decide +kernel
      have hl : raw21966step3Labels = raw21966step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21966step3 raw21966step3Labels = mixedMoment B raw21966step4 raw21966step4Labels := by
      have ha : raw21966step4 = raw21966step3 := by apply Matrix.ext; unfold raw21966step4 raw21966step3; decide +kernel
      have hl : raw21966step3Labels = labelEmbedding1 ∘ raw21966step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21966step3 raw21966step3Labels raw21966step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1647 node1647Labels := by rfl

theorem canonical21967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21967 raw21967Labels = mixedMoment B node1650 node1650Labels := by
  calc
    mixedMoment B raw21967 raw21967Labels = mixedMoment B raw21967step0 raw21967step0Labels := by
      have hz : ∀ j, raw21967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21967step0 = (fun i j => raw21967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21967step0 raw21967; decide +kernel
      have hl : raw21967step0Labels = raw21967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21967 raw21967Labels permutation346 hz
    mixedMoment B raw21967step0 raw21967step0Labels = mixedMoment B raw21967step1 raw21967step1Labels := by
      have hz : ∀ j, raw21967step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21967step1 = (fun i j => raw21967step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21967step1 raw21967step0; decide +kernel
      have hl : raw21967step1Labels = raw21967step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21967step0 raw21967step0Labels permutation56 hz
    mixedMoment B raw21967step1 raw21967step1Labels = mixedMoment B raw21967step2 raw21967step2Labels := by
      have ha : raw21967step2 = (fun i j => raw21967step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21967step2 raw21967step1; decide +kernel
      have hl : raw21967step2Labels = raw21967step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21967step1 raw21967step1Labels permutation8 permutation7
    mixedMoment B raw21967step2 raw21967step2Labels = mixedMoment B raw21967step3 raw21967step3Labels := by
      have ha : raw21967step3 = -raw21967step2 := by apply Matrix.ext; change ∀ i j, raw21967step3 i j = -(raw21967step2 i j); unfold raw21967step3 raw21967step2; decide +kernel
      have hl : raw21967step3Labels = raw21967step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21967step3 raw21967step3Labels = mixedMoment B raw21967step4 raw21967step4Labels := by
      have ha : raw21967step4 = raw21967step3 := by apply Matrix.ext; unfold raw21967step4 raw21967step3; decide +kernel
      have hl : raw21967step3Labels = labelEmbedding1 ∘ raw21967step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21967step3 raw21967step3Labels raw21967step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1650 node1650Labels := by rfl

theorem canonical21968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21968 raw21968Labels = mixedMoment B node1495 node1495Labels := by
  calc
    mixedMoment B raw21968 raw21968Labels = mixedMoment B raw21968step0 raw21968step0Labels := by
      have hz : ∀ j, raw21968 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21968step0 = (fun i j => raw21968 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21968step0 raw21968; decide +kernel
      have hl : raw21968step0Labels = raw21968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21968 raw21968Labels permutation346 hz
    mixedMoment B raw21968step0 raw21968step0Labels = mixedMoment B raw21968step1 raw21968step1Labels := by
      have hz : ∀ j, raw21968step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21968step1 = (fun i j => raw21968step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21968step1 raw21968step0; decide +kernel
      have hl : raw21968step1Labels = raw21968step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21968step0 raw21968step0Labels permutation56 hz
    mixedMoment B raw21968step1 raw21968step1Labels = mixedMoment B raw21968step2 raw21968step2Labels := by
      have ha : raw21968step2 = (fun i j => raw21968step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21968step2 raw21968step1; decide +kernel
      have hl : raw21968step2Labels = raw21968step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21968step1 raw21968step1Labels permutation8 permutation7
    mixedMoment B raw21968step2 raw21968step2Labels = mixedMoment B raw21968step3 raw21968step3Labels := by
      have ha : raw21968step3 = -raw21968step2 := by apply Matrix.ext; change ∀ i j, raw21968step3 i j = -(raw21968step2 i j); unfold raw21968step3 raw21968step2; decide +kernel
      have hl : raw21968step3Labels = raw21968step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21968step3 raw21968step3Labels = mixedMoment B raw21968step4 raw21968step4Labels := by
      have ha : raw21968step4 = raw21968step3 := by apply Matrix.ext; unfold raw21968step4 raw21968step3; decide +kernel
      have hl : raw21968step3Labels = labelEmbedding1 ∘ raw21968step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21968step3 raw21968step3Labels raw21968step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1495 node1495Labels := by rfl

theorem canonical21969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21969 raw21969Labels = mixedMoment B node1590 node1590Labels := by
  calc
    mixedMoment B raw21969 raw21969Labels = mixedMoment B raw21969step0 raw21969step0Labels := by
      have hz : ∀ j, raw21969 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21969step0 = (fun i j => raw21969 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21969step0 raw21969; decide +kernel
      have hl : raw21969step0Labels = raw21969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21969 raw21969Labels permutation346 hz
    mixedMoment B raw21969step0 raw21969step0Labels = mixedMoment B raw21969step1 raw21969step1Labels := by
      have ha : raw21969step1 = (fun i j => raw21969step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21969step1 raw21969step0; decide +kernel
      have hl : raw21969step1Labels = raw21969step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21969step0 raw21969step0Labels permutation38 permutation7
    mixedMoment B raw21969step1 raw21969step1Labels = mixedMoment B raw21969step2 raw21969step2Labels := by
      have ha : raw21969step2 = -raw21969step1 := by apply Matrix.ext; change ∀ i j, raw21969step2 i j = -(raw21969step1 i j); unfold raw21969step2 raw21969step1; decide +kernel
      have hl : raw21969step2Labels = raw21969step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21969step2 raw21969step2Labels = mixedMoment B raw21969step3 raw21969step3Labels := by
      have ha : raw21969step3 = raw21969step2 := by apply Matrix.ext; unfold raw21969step3 raw21969step2; decide +kernel
      have hl : raw21969step2Labels = labelEmbedding1 ∘ raw21969step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21969step2 raw21969step2Labels raw21969step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1590 node1590Labels := by rfl

theorem canonical21970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21970 raw21970Labels = mixedMoment B node1590 node1590Labels := by
  calc
    mixedMoment B raw21970 raw21970Labels = mixedMoment B raw21970step0 raw21970step0Labels := by
      have hz : ∀ j, raw21970 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21970step0 = (fun i j => raw21970 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21970step0 raw21970; decide +kernel
      have hl : raw21970step0Labels = raw21970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21970 raw21970Labels permutation265 hz
    mixedMoment B raw21970step0 raw21970step0Labels = mixedMoment B raw21970step1 raw21970step1Labels := by
      have ha : raw21970step1 = (fun i j => raw21970step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21970step1 raw21970step0; decide +kernel
      have hl : raw21970step1Labels = raw21970step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21970step0 raw21970step0Labels permutation38 permutation7
    mixedMoment B raw21970step1 raw21970step1Labels = mixedMoment B raw21970step2 raw21970step2Labels := by
      have ha : raw21970step2 = -raw21970step1 := by apply Matrix.ext; change ∀ i j, raw21970step2 i j = -(raw21970step1 i j); unfold raw21970step2 raw21970step1; decide +kernel
      have hl : raw21970step2Labels = raw21970step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21970step2 raw21970step2Labels = mixedMoment B raw21970step3 raw21970step3Labels := by
      have ha : raw21970step3 = raw21970step2 := by apply Matrix.ext; unfold raw21970step3 raw21970step2; decide +kernel
      have hl : raw21970step2Labels = labelEmbedding1 ∘ raw21970step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21970step2 raw21970step2Labels raw21970step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1590 node1590Labels := by rfl

theorem canonical21971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21971 raw21971Labels = mixedMoment B node1576 node1576Labels := by
  calc
    mixedMoment B raw21971 raw21971Labels = mixedMoment B raw21971step0 raw21971step0Labels := by
      have hz : ∀ j, raw21971 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21971step0 = (fun i j => raw21971 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21971step0 raw21971; decide +kernel
      have hl : raw21971step0Labels = raw21971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21971 raw21971Labels permutation346 hz
    mixedMoment B raw21971step0 raw21971step0Labels = mixedMoment B raw21971step1 raw21971step1Labels := by
      have hz : ∀ j, raw21971step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21971step1 = (fun i j => raw21971step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21971step1 raw21971step0; decide +kernel
      have hl : raw21971step1Labels = raw21971step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21971step0 raw21971step0Labels permutation56 hz
    mixedMoment B raw21971step1 raw21971step1Labels = mixedMoment B raw21971step2 raw21971step2Labels := by
      have ha : raw21971step2 = (fun i j => raw21971step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21971step2 raw21971step1; decide +kernel
      have hl : raw21971step2Labels = raw21971step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21971step1 raw21971step1Labels permutation8 permutation7
    mixedMoment B raw21971step2 raw21971step2Labels = mixedMoment B raw21971step3 raw21971step3Labels := by
      have ha : raw21971step3 = -raw21971step2 := by apply Matrix.ext; change ∀ i j, raw21971step3 i j = -(raw21971step2 i j); unfold raw21971step3 raw21971step2; decide +kernel
      have hl : raw21971step3Labels = raw21971step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21971step3 raw21971step3Labels = mixedMoment B raw21971step4 raw21971step4Labels := by
      have ha : raw21971step4 = raw21971step3 := by apply Matrix.ext; unfold raw21971step4 raw21971step3; decide +kernel
      have hl : raw21971step3Labels = labelEmbedding1 ∘ raw21971step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21971step3 raw21971step3Labels raw21971step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1576 node1576Labels := by rfl

theorem canonical21972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21972 raw21972Labels = mixedMoment B node1627 node1627Labels := by
  calc
    mixedMoment B raw21972 raw21972Labels = mixedMoment B raw21972step0 raw21972step0Labels := by
      have hz : ∀ j, raw21972 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21972step0 = (fun i j => raw21972 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21972step0 raw21972; decide +kernel
      have hl : raw21972step0Labels = raw21972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21972 raw21972Labels permutation346 hz
    mixedMoment B raw21972step0 raw21972step0Labels = mixedMoment B raw21972step1 raw21972step1Labels := by
      have hz : ∀ j, raw21972step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21972step1 = (fun i j => raw21972step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21972step1 raw21972step0; decide +kernel
      have hl : raw21972step1Labels = raw21972step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21972step0 raw21972step0Labels permutation56 hz
    mixedMoment B raw21972step1 raw21972step1Labels = mixedMoment B raw21972step2 raw21972step2Labels := by
      have ha : raw21972step2 = (fun i j => raw21972step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21972step2 raw21972step1; decide +kernel
      have hl : raw21972step2Labels = raw21972step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21972step1 raw21972step1Labels permutation8 permutation7
    mixedMoment B raw21972step2 raw21972step2Labels = mixedMoment B raw21972step3 raw21972step3Labels := by
      have ha : raw21972step3 = -raw21972step2 := by apply Matrix.ext; change ∀ i j, raw21972step3 i j = -(raw21972step2 i j); unfold raw21972step3 raw21972step2; decide +kernel
      have hl : raw21972step3Labels = raw21972step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21972step3 raw21972step3Labels = mixedMoment B raw21972step4 raw21972step4Labels := by
      have ha : raw21972step4 = raw21972step3 := by apply Matrix.ext; unfold raw21972step4 raw21972step3; decide +kernel
      have hl : raw21972step3Labels = labelEmbedding1 ∘ raw21972step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21972step3 raw21972step3Labels raw21972step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1627 node1627Labels := by rfl

theorem canonical21973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21973 raw21973Labels = mixedMoment B node1494 node1494Labels := by
  calc
    mixedMoment B raw21973 raw21973Labels = mixedMoment B raw21973step0 raw21973step0Labels := by
      have hz : ∀ j, raw21973 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21973step0 = (fun i j => raw21973 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21973step0 raw21973; decide +kernel
      have hl : raw21973step0Labels = raw21973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21973 raw21973Labels permutation346 hz
    mixedMoment B raw21973step0 raw21973step0Labels = mixedMoment B raw21973step1 raw21973step1Labels := by
      have hz : ∀ j, raw21973step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21973step1 = (fun i j => raw21973step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21973step1 raw21973step0; decide +kernel
      have hl : raw21973step1Labels = raw21973step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21973step0 raw21973step0Labels permutation56 hz
    mixedMoment B raw21973step1 raw21973step1Labels = mixedMoment B raw21973step2 raw21973step2Labels := by
      have ha : raw21973step2 = (fun i j => raw21973step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21973step2 raw21973step1; decide +kernel
      have hl : raw21973step2Labels = raw21973step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21973step1 raw21973step1Labels permutation8 permutation7
    mixedMoment B raw21973step2 raw21973step2Labels = mixedMoment B raw21973step3 raw21973step3Labels := by
      have ha : raw21973step3 = -raw21973step2 := by apply Matrix.ext; change ∀ i j, raw21973step3 i j = -(raw21973step2 i j); unfold raw21973step3 raw21973step2; decide +kernel
      have hl : raw21973step3Labels = raw21973step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21973step3 raw21973step3Labels = mixedMoment B raw21973step4 raw21973step4Labels := by
      have ha : raw21973step4 = raw21973step3 := by apply Matrix.ext; unfold raw21973step4 raw21973step3; decide +kernel
      have hl : raw21973step3Labels = labelEmbedding1 ∘ raw21973step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21973step3 raw21973step3Labels raw21973step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1494 node1494Labels := by rfl

theorem canonical21974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21974 raw21974Labels = mixedMoment B node1555 node1555Labels := by
  calc
    mixedMoment B raw21974 raw21974Labels = mixedMoment B raw21974step0 raw21974step0Labels := by
      have hz : ∀ j, raw21974 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21974step0 = (fun i j => raw21974 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21974step0 raw21974; decide +kernel
      have hl : raw21974step0Labels = raw21974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21974 raw21974Labels permutation346 hz
    mixedMoment B raw21974step0 raw21974step0Labels = mixedMoment B raw21974step1 raw21974step1Labels := by
      have ha : raw21974step1 = (fun i j => raw21974step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21974step1 raw21974step0; decide +kernel
      have hl : raw21974step1Labels = raw21974step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21974step0 raw21974step0Labels permutation149 permutation7
    mixedMoment B raw21974step1 raw21974step1Labels = mixedMoment B raw21974step2 raw21974step2Labels := by
      have ha : raw21974step2 = raw21974step1 := by apply Matrix.ext; unfold raw21974step2 raw21974step1; decide +kernel
      have hl : raw21974step1Labels = labelEmbedding1 ∘ raw21974step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21974step1 raw21974step1Labels raw21974step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1555 node1555Labels := by rfl

theorem canonical21975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21975 raw21975Labels = mixedMoment B node1555 node1555Labels := by
  calc
    mixedMoment B raw21975 raw21975Labels = mixedMoment B raw21975step0 raw21975step0Labels := by
      have hz : ∀ j, raw21975 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21975step0 = (fun i j => raw21975 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21975step0 raw21975; decide +kernel
      have hl : raw21975step0Labels = raw21975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21975 raw21975Labels permutation265 hz
    mixedMoment B raw21975step0 raw21975step0Labels = mixedMoment B raw21975step1 raw21975step1Labels := by
      have ha : raw21975step1 = (fun i j => raw21975step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21975step1 raw21975step0; decide +kernel
      have hl : raw21975step1Labels = raw21975step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21975step0 raw21975step0Labels permutation149 permutation7
    mixedMoment B raw21975step1 raw21975step1Labels = mixedMoment B raw21975step2 raw21975step2Labels := by
      have ha : raw21975step2 = raw21975step1 := by apply Matrix.ext; unfold raw21975step2 raw21975step1; decide +kernel
      have hl : raw21975step1Labels = labelEmbedding1 ∘ raw21975step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21975step1 raw21975step1Labels raw21975step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1555 node1555Labels := by rfl

theorem canonical21976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21976 raw21976Labels = mixedMoment B node1574 node1574Labels := by
  calc
    mixedMoment B raw21976 raw21976Labels = mixedMoment B raw21976step0 raw21976step0Labels := by
      have hz : ∀ j, raw21976 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21976step0 = (fun i j => raw21976 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21976step0 raw21976; decide +kernel
      have hl : raw21976step0Labels = raw21976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21976 raw21976Labels permutation346 hz
    mixedMoment B raw21976step0 raw21976step0Labels = mixedMoment B raw21976step1 raw21976step1Labels := by
      have hz : ∀ j, raw21976step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21976step1 = (fun i j => raw21976step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21976step1 raw21976step0; decide +kernel
      have hl : raw21976step1Labels = raw21976step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21976step0 raw21976step0Labels permutation56 hz
    mixedMoment B raw21976step1 raw21976step1Labels = mixedMoment B raw21976step2 raw21976step2Labels := by
      have ha : raw21976step2 = (fun i j => raw21976step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21976step2 raw21976step1; decide +kernel
      have hl : raw21976step2Labels = raw21976step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21976step1 raw21976step1Labels permutation31 permutation7
    mixedMoment B raw21976step2 raw21976step2Labels = mixedMoment B raw21976step3 raw21976step3Labels := by
      have ha : raw21976step3 = raw21976step2 := by apply Matrix.ext; unfold raw21976step3 raw21976step2; decide +kernel
      have hl : raw21976step2Labels = labelEmbedding1 ∘ raw21976step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21976step2 raw21976step2Labels raw21976step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1574 node1574Labels := by rfl

theorem canonical21977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21977 raw21977Labels = mixedMoment B node1620 node1620Labels := by
  calc
    mixedMoment B raw21977 raw21977Labels = mixedMoment B raw21977step0 raw21977step0Labels := by
      have hz : ∀ j, raw21977 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21977step0 = (fun i j => raw21977 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21977step0 raw21977; decide +kernel
      have hl : raw21977step0Labels = raw21977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21977 raw21977Labels permutation346 hz
    mixedMoment B raw21977step0 raw21977step0Labels = mixedMoment B raw21977step1 raw21977step1Labels := by
      have hz : ∀ j, raw21977step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21977step1 = (fun i j => raw21977step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21977step1 raw21977step0; decide +kernel
      have hl : raw21977step1Labels = raw21977step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21977step0 raw21977step0Labels permutation56 hz
    mixedMoment B raw21977step1 raw21977step1Labels = mixedMoment B raw21977step2 raw21977step2Labels := by
      have ha : raw21977step2 = (fun i j => raw21977step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21977step2 raw21977step1; decide +kernel
      have hl : raw21977step2Labels = raw21977step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21977step1 raw21977step1Labels permutation31 permutation7
    mixedMoment B raw21977step2 raw21977step2Labels = mixedMoment B raw21977step3 raw21977step3Labels := by
      have ha : raw21977step3 = raw21977step2 := by apply Matrix.ext; unfold raw21977step3 raw21977step2; decide +kernel
      have hl : raw21977step2Labels = labelEmbedding1 ∘ raw21977step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21977step2 raw21977step2Labels raw21977step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1620 node1620Labels := by rfl

theorem canonical21978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21978 raw21978Labels = mixedMoment B node1911 node1911Labels := by
  calc
    mixedMoment B raw21978 raw21978Labels = mixedMoment B raw21978step0 raw21978step0Labels := by
      have hz : ∀ j, raw21978 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21978step0 = (fun i j => raw21978 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21978step0 raw21978; decide +kernel
      have hl : raw21978step0Labels = raw21978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21978 raw21978Labels permutation346 hz
    mixedMoment B raw21978step0 raw21978step0Labels = mixedMoment B raw21978step1 raw21978step1Labels := by
      have ha : raw21978step1 = (fun i j => raw21978step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21978step1 raw21978step0; decide +kernel
      have hl : raw21978step1Labels = raw21978step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21978step0 raw21978step0Labels permutation151 permutation2
    mixedMoment B raw21978step1 raw21978step1Labels = mixedMoment B raw21978step2 raw21978step2Labels := by
      have ha : raw21978step2 = -raw21978step1 := by apply Matrix.ext; change ∀ i j, raw21978step2 i j = -(raw21978step1 i j); unfold raw21978step2 raw21978step1; decide +kernel
      have hl : raw21978step2Labels = raw21978step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1911 node1911Labels := by rfl

theorem canonical21979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21979 raw21979Labels = mixedMoment B node1007 node1007Labels := by
  calc
    mixedMoment B raw21979 raw21979Labels = mixedMoment B raw21979step0 raw21979step0Labels := by
      have hz : ∀ j, raw21979 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21979step0 = (fun i j => raw21979 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21979step0 raw21979; decide +kernel
      have hl : raw21979step0Labels = raw21979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21979 raw21979Labels permutation346 hz
    mixedMoment B raw21979step0 raw21979step0Labels = mixedMoment B raw21979step1 raw21979step1Labels := by
      have hz : ∀ j, raw21979step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21979step1 = (fun i j => raw21979step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21979step1 raw21979step0; decide +kernel
      have hl : raw21979step1Labels = raw21979step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21979step0 raw21979step0Labels permutation56 hz
    _ = mixedMoment B node1007 node1007Labels := by rfl

theorem canonical21980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21980 raw21980Labels = mixedMoment B node898 node898Labels := by
  calc
    mixedMoment B raw21980 raw21980Labels = mixedMoment B raw21980step0 raw21980step0Labels := by
      have ha : raw21980step0 = (fun i j => raw21980 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21980step0 raw21980; decide +kernel
      have hl : raw21980step0Labels = raw21980Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21980 raw21980Labels permutation158 permutation2
    _ = mixedMoment B node898 node898Labels := by rfl

theorem canonical21981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21981 raw21981Labels = mixedMoment B node916 node916Labels := by
  calc
    mixedMoment B raw21981 raw21981Labels = mixedMoment B raw21981step0 raw21981step0Labels := by
      have hz : ∀ j, raw21981 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21981step0 = (fun i j => raw21981 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21981step0 raw21981; decide +kernel
      have hl : raw21981step0Labels = raw21981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21981 raw21981Labels permutation346 hz
    _ = mixedMoment B node916 node916Labels := by rfl

theorem canonical21982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21982 raw21982Labels = mixedMoment B node902 node902Labels := by
  calc
    mixedMoment B raw21982 raw21982Labels = mixedMoment B raw21982step0 raw21982step0Labels := by
      have hz : ∀ j, raw21982 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21982step0 = (fun i j => raw21982 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21982step0 raw21982; decide +kernel
      have hl : raw21982step0Labels = raw21982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21982 raw21982Labels permutation346 hz
    _ = mixedMoment B node902 node902Labels := by rfl

theorem canonical21983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21983 raw21983Labels = mixedMoment B node867 node867Labels := by
  calc
    mixedMoment B raw21983 raw21983Labels = mixedMoment B raw21983step0 raw21983step0Labels := by
      have hz : ∀ j, raw21983 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21983step0 = (fun i j => raw21983 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21983step0 raw21983; decide +kernel
      have hl : raw21983step0Labels = raw21983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21983 raw21983Labels permutation346 hz
    mixedMoment B raw21983step0 raw21983step0Labels = mixedMoment B raw21983step1 raw21983step1Labels := by
      have ha : raw21983step1 = (fun i j => raw21983step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21983step1 raw21983step0; decide +kernel
      have hl : raw21983step1Labels = raw21983step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21983step0 raw21983step0Labels permutation151 permutation2
    mixedMoment B raw21983step1 raw21983step1Labels = mixedMoment B raw21983step2 raw21983step2Labels := by
      have ha : raw21983step2 = -raw21983step1 := by apply Matrix.ext; change ∀ i j, raw21983step2 i j = -(raw21983step1 i j); unfold raw21983step2 raw21983step1; decide +kernel
      have hl : raw21983step2Labels = raw21983step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node867 node867Labels := by rfl

theorem canonical21984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21984 raw21984Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw21984 raw21984Labels = mixedMoment B raw21984step0 raw21984step0Labels := by
      have hz : ∀ j, raw21984 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21984step0 = (fun i j => raw21984 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21984step0 raw21984; decide +kernel
      have hl : raw21984step0Labels = raw21984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21984 raw21984Labels permutation346 hz
    mixedMoment B raw21984step0 raw21984step0Labels = mixedMoment B raw21984step1 raw21984step1Labels := by
      have hz : ∀ j, raw21984step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21984step1 = (fun i j => raw21984step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21984step1 raw21984step0; decide +kernel
      have hl : raw21984step1Labels = raw21984step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21984step0 raw21984step0Labels permutation56 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical22002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22002 raw22002Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw22002 raw22002Labels = mixedMoment B raw22002step0 raw22002step0Labels := by
      have hz : ∀ j, raw22002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22002step0 = (fun i j => raw22002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22002step0 raw22002; decide +kernel
      have hl : raw22002step0Labels = raw22002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22002 raw22002Labels permutation434 hz
    mixedMoment B raw22002step0 raw22002step0Labels = mixedMoment B raw22002step1 raw22002step1Labels := by
      have ha : raw22002step1 = (fun i j => raw22002step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22002step1 raw22002step0; decide +kernel
      have hl : raw22002step1Labels = raw22002step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22002step0 raw22002step0Labels permutation38 permutation2
    _ = mixedMoment B node1715 node1715Labels := by rfl

theorem canonical22003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22003 raw22003Labels = mixedMoment B node811 node811Labels := by
  calc
    mixedMoment B raw22003 raw22003Labels = mixedMoment B raw22003step0 raw22003step0Labels := by
      have hz : ∀ j, raw22003 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22003step0 = (fun i j => raw22003 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22003step0 raw22003; decide +kernel
      have hl : raw22003step0Labels = raw22003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22003 raw22003Labels permutation434 hz
    mixedMoment B raw22003step0 raw22003step0Labels = mixedMoment B raw22003step1 raw22003step1Labels := by
      have ha : raw22003step1 = (fun i j => raw22003step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22003step1 raw22003step0; decide +kernel
      have hl : raw22003step1Labels = raw22003step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22003step0 raw22003step0Labels permutation40 permutation2
    _ = mixedMoment B node811 node811Labels := by rfl

theorem canonical22004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22004 raw22004Labels = mixedMoment B node827 node827Labels := by
  calc
    mixedMoment B raw22004 raw22004Labels = mixedMoment B raw22004step0 raw22004step0Labels := by
      have hz : ∀ j, raw22004 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22004step0 = (fun i j => raw22004 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22004step0 raw22004; decide +kernel
      have hl : raw22004step0Labels = raw22004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22004 raw22004Labels permutation434 hz
    _ = mixedMoment B node827 node827Labels := by rfl

theorem canonical22005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22005 raw22005Labels = mixedMoment B node793 node793Labels := by
  calc
    mixedMoment B raw22005 raw22005Labels = mixedMoment B raw22005step0 raw22005step0Labels := by
      have ha : raw22005step0 = (fun i j => raw22005 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22005step0 raw22005; decide +kernel
      have hl : raw22005step0Labels = raw22005Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22005 raw22005Labels permutation176 permutation2
    _ = mixedMoment B node793 node793Labels := by rfl

theorem canonical22006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22006 raw22006Labels = mixedMoment B node796 node796Labels := by
  calc
    mixedMoment B raw22006 raw22006Labels = mixedMoment B raw22006step0 raw22006step0Labels := by
      have hz : ∀ j, raw22006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22006step0 = (fun i j => raw22006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22006step0 raw22006; decide +kernel
      have hl : raw22006step0Labels = raw22006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22006 raw22006Labels permutation434 hz
    mixedMoment B raw22006step0 raw22006step0Labels = mixedMoment B raw22006step1 raw22006step1Labels := by
      have ha : raw22006step1 = (fun i j => raw22006step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22006step1 raw22006step0; decide +kernel
      have hl : raw22006step1Labels = raw22006step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22006step0 raw22006step0Labels permutation39 permutation2
    _ = mixedMoment B node796 node796Labels := by rfl

theorem canonical22007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22007 raw22007Labels = mixedMoment B node795 node795Labels := by
  calc
    mixedMoment B raw22007 raw22007Labels = mixedMoment B raw22007step0 raw22007step0Labels := by
      have hz : ∀ j, raw22007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22007step0 = (fun i j => raw22007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22007step0 raw22007; decide +kernel
      have hl : raw22007step0Labels = raw22007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22007 raw22007Labels permutation434 hz
    mixedMoment B raw22007step0 raw22007step0Labels = mixedMoment B raw22007step1 raw22007step1Labels := by
      have ha : raw22007step1 = (fun i j => raw22007step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22007step1 raw22007step0; decide +kernel
      have hl : raw22007step1Labels = raw22007step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22007step0 raw22007step0Labels permutation38 permutation2
    _ = mixedMoment B node795 node795Labels := by rfl

theorem canonical22008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22008 raw22008Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw22008 raw22008Labels = mixedMoment B raw22008step0 raw22008step0Labels := by
      have hz : ∀ j, raw22008 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw22008step0 = (fun i j => raw22008 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw22008step0 raw22008; decide +kernel
      have hl : raw22008step0Labels = raw22008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22008 raw22008Labels permutation590 hz
    mixedMoment B raw22008step0 raw22008step0Labels = mixedMoment B raw22008step1 raw22008step1Labels := by
      have hz : ∀ j, raw22008step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22008step1 = (fun i j => raw22008step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22008step1 raw22008step0; decide +kernel
      have hl : raw22008step1Labels = raw22008step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22008step0 raw22008step0Labels permutation104 hz
    mixedMoment B raw22008step1 raw22008step1Labels = mixedMoment B raw22008step2 raw22008step2Labels := by
      have ha : raw22008step2 = (fun i j => raw22008step1 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22008step2 raw22008step1; decide +kernel
      have hl : raw22008step2Labels = raw22008step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22008step1 raw22008step1Labels permutation11 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical172
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22016 raw22016Labels = mixedMoment B node1740 node1740Labels := by
  calc
    mixedMoment B raw22016 raw22016Labels = mixedMoment B raw22016step0 raw22016step0Labels := by
      have hz : ∀ j, raw22016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22016step0 = (fun i j => raw22016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22016step0 raw22016; decide +kernel
      have hl : raw22016step0Labels = raw22016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22016 raw22016Labels permutation434 hz
    mixedMoment B raw22016step0 raw22016step0Labels = mixedMoment B raw22016step1 raw22016step1Labels := by
      have hz : ∀ j, raw22016step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22016step1 = (fun i j => raw22016step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22016step1 raw22016step0; decide +kernel
      have hl : raw22016step1Labels = raw22016step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22016step0 raw22016step0Labels permutation80 hz
    _ = mixedMoment B node1740 node1740Labels := by rfl

theorem canonical22017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22017 raw22017Labels = mixedMoment B node858 node858Labels := by
  calc
    mixedMoment B raw22017 raw22017Labels = mixedMoment B raw22017step0 raw22017step0Labels := by
      have hz : ∀ j, raw22017 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22017step0 = (fun i j => raw22017 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22017step0 raw22017; decide +kernel
      have hl : raw22017step0Labels = raw22017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22017 raw22017Labels permutation434 hz
    mixedMoment B raw22017step0 raw22017step0Labels = mixedMoment B raw22017step1 raw22017step1Labels := by
      have hz : ∀ j, raw22017step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22017step1 = (fun i j => raw22017step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22017step1 raw22017step0; decide +kernel
      have hl : raw22017step1Labels = raw22017step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22017step0 raw22017step0Labels permutation80 hz
    _ = mixedMoment B node858 node858Labels := by rfl

theorem canonical22018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22018 raw22018Labels = mixedMoment B node825 node825Labels := by
  calc
    mixedMoment B raw22018 raw22018Labels = mixedMoment B raw22018step0 raw22018step0Labels := by
      have hz : ∀ j, raw22018 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22018step0 = (fun i j => raw22018 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22018step0 raw22018; decide +kernel
      have hl : raw22018step0Labels = raw22018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22018 raw22018Labels permutation434 hz
    _ = mixedMoment B node825 node825Labels := by rfl

theorem canonical22019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22019 raw22019Labels = mixedMoment B node825 node825Labels := by
  calc
    mixedMoment B raw22019 raw22019Labels = mixedMoment B raw22019step0 raw22019step0Labels := by
      have hz : ∀ j, raw22019 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22019step0 = (fun i j => raw22019 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22019step0 raw22019; decide +kernel
      have hl : raw22019step0Labels = raw22019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22019 raw22019Labels permutation346 hz
    _ = mixedMoment B node825 node825Labels := by rfl

theorem canonical22020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22020 raw22020Labels = mixedMoment B node830 node830Labels := by
  calc
    mixedMoment B raw22020 raw22020Labels = mixedMoment B raw22020step0 raw22020step0Labels := by
      have hz : ∀ j, raw22020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22020step0 = (fun i j => raw22020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22020step0 raw22020; decide +kernel
      have hl : raw22020step0Labels = raw22020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22020 raw22020Labels permutation434 hz
    mixedMoment B raw22020step0 raw22020step0Labels = mixedMoment B raw22020step1 raw22020step1Labels := by
      have hz : ∀ j, raw22020step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22020step1 = (fun i j => raw22020step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22020step1 raw22020step0; decide +kernel
      have hl : raw22020step1Labels = raw22020step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22020step0 raw22020step0Labels permutation80 hz
    mixedMoment B raw22020step1 raw22020step1Labels = mixedMoment B raw22020step2 raw22020step2Labels := by
      have ha : raw22020step2 = (fun i j => raw22020step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22020step2 raw22020step1; decide +kernel
      have hl : raw22020step2Labels = raw22020step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22020step1 raw22020step1Labels permutation9 permutation2
    _ = mixedMoment B node830 node830Labels := by rfl

theorem canonical22021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22021 raw22021Labels = mixedMoment B node829 node829Labels := by
  calc
    mixedMoment B raw22021 raw22021Labels = mixedMoment B raw22021step0 raw22021step0Labels := by
      have hz : ∀ j, raw22021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22021step0 = (fun i j => raw22021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22021step0 raw22021; decide +kernel
      have hl : raw22021step0Labels = raw22021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22021 raw22021Labels permutation434 hz
    mixedMoment B raw22021step0 raw22021step0Labels = mixedMoment B raw22021step1 raw22021step1Labels := by
      have hz : ∀ j, raw22021step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22021step1 = (fun i j => raw22021step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22021step1 raw22021step0; decide +kernel
      have hl : raw22021step1Labels = raw22021step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22021step0 raw22021step0Labels permutation80 hz
    _ = mixedMoment B node829 node829Labels := by rfl

theorem canonical22022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22022 raw22022Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw22022 raw22022Labels = mixedMoment B raw22022step0 raw22022step0Labels := by
      have hz : ∀ j, raw22022 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw22022step0 = (fun i j => raw22022 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw22022step0 raw22022; decide +kernel
      have hl : raw22022step0Labels = raw22022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22022 raw22022Labels permutation590 hz
    mixedMoment B raw22022step0 raw22022step0Labels = mixedMoment B raw22022step1 raw22022step1Labels := by
      have hz : ∀ j, raw22022step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22022step1 = (fun i j => raw22022step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22022step1 raw22022step0; decide +kernel
      have hl : raw22022step1Labels = raw22022step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22022step0 raw22022step0Labels permutation104 hz
    mixedMoment B raw22022step1 raw22022step1Labels = mixedMoment B raw22022step2 raw22022step2Labels := by
      have hz : ∀ j, raw22022step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw22022step2 = (fun i j => raw22022step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw22022step2 raw22022step1; decide +kernel
      have hl : raw22022step2Labels = raw22022step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22022step1 raw22022step1Labels permutation20 hz
    _ = mixedMoment B node4071 node4071Labels := by rfl

theorem canonical22023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22023 raw22023Labels = mixedMoment B node828 node828Labels := by
  calc
    mixedMoment B raw22023 raw22023Labels = mixedMoment B raw22023step0 raw22023step0Labels := by
      have hz : ∀ j, raw22023 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22023step0 = (fun i j => raw22023 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22023step0 raw22023; decide +kernel
      have hl : raw22023step0Labels = raw22023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22023 raw22023Labels permutation434 hz
    mixedMoment B raw22023step0 raw22023step0Labels = mixedMoment B raw22023step1 raw22023step1Labels := by
      have hz : ∀ j, raw22023step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22023step1 = (fun i j => raw22023step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22023step1 raw22023step0; decide +kernel
      have hl : raw22023step1Labels = raw22023step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22023step0 raw22023step0Labels permutation80 hz
    _ = mixedMoment B node828 node828Labels := by rfl

theorem canonical22024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22024 raw22024Labels = mixedMoment B node1659 node1659Labels := by
  calc
    mixedMoment B raw22024 raw22024Labels = mixedMoment B raw22024step0 raw22024step0Labels := by
      have hz : ∀ j, raw22024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22024step0 = (fun i j => raw22024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22024step0 raw22024; decide +kernel
      have hl : raw22024step0Labels = raw22024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22024 raw22024Labels permutation434 hz
    mixedMoment B raw22024step0 raw22024step0Labels = mixedMoment B raw22024step1 raw22024step1Labels := by
      have hz : ∀ j, raw22024step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22024step1 = (fun i j => raw22024step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22024step1 raw22024step0; decide +kernel
      have hl : raw22024step1Labels = raw22024step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22024step0 raw22024step0Labels permutation80 hz
    _ = mixedMoment B node1659 node1659Labels := by rfl

theorem canonical22025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22025 raw22025Labels = mixedMoment B node1610 node1610Labels := by
  calc
    mixedMoment B raw22025 raw22025Labels = mixedMoment B raw22025step0 raw22025step0Labels := by
      have hz : ∀ j, raw22025 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22025step0 = (fun i j => raw22025 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22025step0 raw22025; decide +kernel
      have hl : raw22025step0Labels = raw22025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22025 raw22025Labels permutation434 hz
    mixedMoment B raw22025step0 raw22025step0Labels = mixedMoment B raw22025step1 raw22025step1Labels := by
      have ha : raw22025step1 = (fun i j => raw22025step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22025step1 raw22025step0; decide +kernel
      have hl : raw22025step1Labels = raw22025step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22025step0 raw22025step0Labels permutation38 permutation2
    _ = mixedMoment B node1610 node1610Labels := by rfl

theorem canonical22026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22026 raw22026Labels = mixedMoment B node1610 node1610Labels := by
  calc
    mixedMoment B raw22026 raw22026Labels = mixedMoment B raw22026step0 raw22026step0Labels := by
      have hz : ∀ j, raw22026 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22026step0 = (fun i j => raw22026 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22026step0 raw22026; decide +kernel
      have hl : raw22026step0Labels = raw22026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22026 raw22026Labels permutation346 hz
    mixedMoment B raw22026step0 raw22026step0Labels = mixedMoment B raw22026step1 raw22026step1Labels := by
      have ha : raw22026step1 = (fun i j => raw22026step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22026step1 raw22026step0; decide +kernel
      have hl : raw22026step1Labels = raw22026step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22026step0 raw22026step0Labels permutation38 permutation2
    _ = mixedMoment B node1610 node1610Labels := by rfl

theorem canonical22027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22027 raw22027Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw22027 raw22027Labels = mixedMoment B raw22027step0 raw22027step0Labels := by
      have hz : ∀ j, raw22027 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22027step0 = (fun i j => raw22027 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22027step0 raw22027; decide +kernel
      have hl : raw22027step0Labels = raw22027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22027 raw22027Labels permutation434 hz
    mixedMoment B raw22027step0 raw22027step0Labels = mixedMoment B raw22027step1 raw22027step1Labels := by
      have hz : ∀ j, raw22027step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22027step1 = (fun i j => raw22027step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22027step1 raw22027step0; decide +kernel
      have hl : raw22027step1Labels = raw22027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22027step0 raw22027step0Labels permutation80 hz
    mixedMoment B raw22027step1 raw22027step1Labels = mixedMoment B raw22027step2 raw22027step2Labels := by
      have ha : raw22027step2 = (fun i j => raw22027step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22027step2 raw22027step1; decide +kernel
      have hl : raw22027step2Labels = raw22027step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22027step1 raw22027step1Labels permutation10 permutation2
    _ = mixedMoment B node1716 node1716Labels := by rfl

theorem canonical22028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22028 raw22028Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw22028 raw22028Labels = mixedMoment B raw22028step0 raw22028step0Labels := by
      have hz : ∀ j, raw22028 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22028step0 = (fun i j => raw22028 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22028step0 raw22028; decide +kernel
      have hl : raw22028step0Labels = raw22028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22028 raw22028Labels permutation434 hz
    mixedMoment B raw22028step0 raw22028step0Labels = mixedMoment B raw22028step1 raw22028step1Labels := by
      have hz : ∀ j, raw22028step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22028step1 = (fun i j => raw22028step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22028step1 raw22028step0; decide +kernel
      have hl : raw22028step1Labels = raw22028step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22028step0 raw22028step0Labels permutation80 hz
    _ = mixedMoment B node1739 node1739Labels := by rfl

theorem canonical22029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22029 raw22029Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw22029 raw22029Labels = mixedMoment B raw22029step0 raw22029step0Labels := by
      have hz : ∀ j, raw22029 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22029step0 = (fun i j => raw22029 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22029step0 raw22029; decide +kernel
      have hl : raw22029step0Labels = raw22029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22029 raw22029Labels permutation434 hz
    mixedMoment B raw22029step0 raw22029step0Labels = mixedMoment B raw22029step1 raw22029step1Labels := by
      have hz : ∀ j, raw22029step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22029step1 = (fun i j => raw22029step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22029step1 raw22029step0; decide +kernel
      have hl : raw22029step1Labels = raw22029step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22029step0 raw22029step0Labels permutation80 hz
    mixedMoment B raw22029step1 raw22029step1Labels = mixedMoment B raw22029step2 raw22029step2Labels := by
      have ha : raw22029step2 = (fun i j => raw22029step1 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22029step2 raw22029step1; decide +kernel
      have hl : raw22029step2Labels = raw22029step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22029step1 raw22029step1Labels permutation11 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical22034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22034 raw22034Labels = mixedMoment B node856 node856Labels := by
  calc
    mixedMoment B raw22034 raw22034Labels = mixedMoment B raw22034step0 raw22034step0Labels := by
      have hz : ∀ j, raw22034 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22034step0 = (fun i j => raw22034 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22034step0 raw22034; decide +kernel
      have hl : raw22034step0Labels = raw22034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22034 raw22034Labels permutation434 hz
    mixedMoment B raw22034step0 raw22034step0Labels = mixedMoment B raw22034step1 raw22034step1Labels := by
      have hz : ∀ j, raw22034step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22034step1 = (fun i j => raw22034step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22034step1 raw22034step0; decide +kernel
      have hl : raw22034step1Labels = raw22034step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22034step0 raw22034step0Labels permutation80 hz
    mixedMoment B raw22034step1 raw22034step1Labels = mixedMoment B raw22034step2 raw22034step2Labels := by
      have ha : raw22034step2 = (fun i j => raw22034step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22034step2 raw22034step1; decide +kernel
      have hl : raw22034step2Labels = raw22034step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22034step1 raw22034step1Labels permutation10 permutation2
    _ = mixedMoment B node856 node856Labels := by rfl

theorem canonical22035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22035 raw22035Labels = mixedMoment B node824 node824Labels := by
  calc
    mixedMoment B raw22035 raw22035Labels = mixedMoment B raw22035step0 raw22035step0Labels := by
      have hz : ∀ j, raw22035 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22035step0 = (fun i j => raw22035 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22035step0 raw22035; decide +kernel
      have hl : raw22035step0Labels = raw22035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22035 raw22035Labels permutation434 hz
    _ = mixedMoment B node824 node824Labels := by rfl

theorem canonical22036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22036 raw22036Labels = mixedMoment B node824 node824Labels := by
  calc
    mixedMoment B raw22036 raw22036Labels = mixedMoment B raw22036step0 raw22036step0Labels := by
      have hz : ∀ j, raw22036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22036step0 = (fun i j => raw22036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22036step0 raw22036; decide +kernel
      have hl : raw22036step0Labels = raw22036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22036 raw22036Labels permutation346 hz
    _ = mixedMoment B node824 node824Labels := by rfl

theorem canonical22037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22037 raw22037Labels = mixedMoment B node831 node831Labels := by
  calc
    mixedMoment B raw22037 raw22037Labels = mixedMoment B raw22037step0 raw22037step0Labels := by
      have hz : ∀ j, raw22037 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22037step0 = (fun i j => raw22037 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22037step0 raw22037; decide +kernel
      have hl : raw22037step0Labels = raw22037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22037 raw22037Labels permutation434 hz
    mixedMoment B raw22037step0 raw22037step0Labels = mixedMoment B raw22037step1 raw22037step1Labels := by
      have hz : ∀ j, raw22037step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22037step1 = (fun i j => raw22037step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22037step1 raw22037step0; decide +kernel
      have hl : raw22037step1Labels = raw22037step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22037step0 raw22037step0Labels permutation80 hz
    _ = mixedMoment B node831 node831Labels := by rfl

theorem canonical22040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22040 raw22040Labels = mixedMoment B node815 node815Labels := by
  calc
    mixedMoment B raw22040 raw22040Labels = mixedMoment B raw22040step0 raw22040step0Labels := by
      have hz : ∀ j, raw22040 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22040step0 = (fun i j => raw22040 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22040step0 raw22040; decide +kernel
      have hl : raw22040step0Labels = raw22040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22040 raw22040Labels permutation434 hz
    mixedMoment B raw22040step0 raw22040step0Labels = mixedMoment B raw22040step1 raw22040step1Labels := by
      have hz : ∀ j, raw22040step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22040step1 = (fun i j => raw22040step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22040step1 raw22040step0; decide +kernel
      have hl : raw22040step1Labels = raw22040step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22040step0 raw22040step0Labels permutation80 hz
    mixedMoment B raw22040step1 raw22040step1Labels = mixedMoment B raw22040step2 raw22040step2Labels := by
      have ha : raw22040step2 = (fun i j => raw22040step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22040step2 raw22040step1; decide +kernel
      have hl : raw22040step2Labels = raw22040step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22040step1 raw22040step1Labels permutation10 permutation4
    mixedMoment B raw22040step2 raw22040step2Labels = mixedMoment B raw22040step3 raw22040step3Labels := by
      have ha : raw22040step3 = -raw22040step2 := by apply Matrix.ext; change ∀ i j, raw22040step3 i j = -(raw22040step2 i j); unfold raw22040step3 raw22040step2; decide +kernel
      have hl : raw22040step3Labels = raw22040step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node815 node815Labels := by rfl

theorem canonical22041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22041 raw22041Labels = mixedMoment B node826 node826Labels := by
  calc
    mixedMoment B raw22041 raw22041Labels = mixedMoment B raw22041step0 raw22041step0Labels := by
      have hz : ∀ j, raw22041 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22041step0 = (fun i j => raw22041 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22041step0 raw22041; decide +kernel
      have hl : raw22041step0Labels = raw22041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22041 raw22041Labels permutation434 hz
    mixedMoment B raw22041step0 raw22041step0Labels = mixedMoment B raw22041step1 raw22041step1Labels := by
      have hz : ∀ j, raw22041step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22041step1 = (fun i j => raw22041step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22041step1 raw22041step0; decide +kernel
      have hl : raw22041step1Labels = raw22041step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22041step0 raw22041step0Labels permutation80 hz
    _ = mixedMoment B node826 node826Labels := by rfl

theorem canonical22042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22042 raw22042Labels = mixedMoment B node1657 node1657Labels := by
  calc
    mixedMoment B raw22042 raw22042Labels = mixedMoment B raw22042step0 raw22042step0Labels := by
      have hz : ∀ j, raw22042 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22042step0 = (fun i j => raw22042 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22042step0 raw22042; decide +kernel
      have hl : raw22042step0Labels = raw22042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22042 raw22042Labels permutation434 hz
    mixedMoment B raw22042step0 raw22042step0Labels = mixedMoment B raw22042step1 raw22042step1Labels := by
      have hz : ∀ j, raw22042step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22042step1 = (fun i j => raw22042step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22042step1 raw22042step0; decide +kernel
      have hl : raw22042step1Labels = raw22042step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22042step0 raw22042step0Labels permutation80 hz
    _ = mixedMoment B node1657 node1657Labels := by rfl

theorem canonical22043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22043 raw22043Labels = mixedMoment B node1608 node1608Labels := by
  calc
    mixedMoment B raw22043 raw22043Labels = mixedMoment B raw22043step0 raw22043step0Labels := by
      have hz : ∀ j, raw22043 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22043step0 = (fun i j => raw22043 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22043step0 raw22043; decide +kernel
      have hl : raw22043step0Labels = raw22043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22043 raw22043Labels permutation434 hz
    mixedMoment B raw22043step0 raw22043step0Labels = mixedMoment B raw22043step1 raw22043step1Labels := by
      have ha : raw22043step1 = (fun i j => raw22043step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22043step1 raw22043step0; decide +kernel
      have hl : raw22043step1Labels = raw22043step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22043step0 raw22043step0Labels permutation38 permutation2
    _ = mixedMoment B node1608 node1608Labels := by rfl

theorem canonical22044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22044 raw22044Labels = mixedMoment B node1608 node1608Labels := by
  calc
    mixedMoment B raw22044 raw22044Labels = mixedMoment B raw22044step0 raw22044step0Labels := by
      have hz : ∀ j, raw22044 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22044step0 = (fun i j => raw22044 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22044step0 raw22044; decide +kernel
      have hl : raw22044step0Labels = raw22044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22044 raw22044Labels permutation346 hz
    mixedMoment B raw22044step0 raw22044step0Labels = mixedMoment B raw22044step1 raw22044step1Labels := by
      have ha : raw22044step1 = (fun i j => raw22044step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22044step1 raw22044step0; decide +kernel
      have hl : raw22044step1Labels = raw22044step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22044step0 raw22044step0Labels permutation38 permutation2
    _ = mixedMoment B node1608 node1608Labels := by rfl

theorem canonical22045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22045 raw22045Labels = mixedMoment B node1741 node1741Labels := by
  calc
    mixedMoment B raw22045 raw22045Labels = mixedMoment B raw22045step0 raw22045step0Labels := by
      have hz : ∀ j, raw22045 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22045step0 = (fun i j => raw22045 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22045step0 raw22045; decide +kernel
      have hl : raw22045step0Labels = raw22045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22045 raw22045Labels permutation520 hz
    mixedMoment B raw22045step0 raw22045step0Labels = mixedMoment B raw22045step1 raw22045step1Labels := by
      have hz : ∀ j, raw22045step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22045step1 = (fun i j => raw22045step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22045step1 raw22045step0; decide +kernel
      have hl : raw22045step1Labels = raw22045step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22045step0 raw22045step0Labels permutation104 hz
    mixedMoment B raw22045step1 raw22045step1Labels = mixedMoment B raw22045step2 raw22045step2Labels := by
      have hz : ∀ j, raw22045step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw22045step2 = (fun i j => raw22045step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw22045step2 raw22045step1; decide +kernel
      have hl : raw22045step2Labels = raw22045step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22045step1 raw22045step1Labels permutation20 hz
    _ = mixedMoment B node1741 node1741Labels := by rfl

theorem canonical22046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22046 raw22046Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw22046 raw22046Labels = mixedMoment B raw22046step0 raw22046step0Labels := by
      have hz : ∀ j, raw22046 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22046step0 = (fun i j => raw22046 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22046step0 raw22046; decide +kernel
      have hl : raw22046step0Labels = raw22046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22046 raw22046Labels permutation434 hz
    mixedMoment B raw22046step0 raw22046step0Labels = mixedMoment B raw22046step1 raw22046step1Labels := by
      have hz : ∀ j, raw22046step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22046step1 = (fun i j => raw22046step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22046step1 raw22046step0; decide +kernel
      have hl : raw22046step1Labels = raw22046step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22046step0 raw22046step0Labels permutation80 hz
    _ = mixedMoment B node1738 node1738Labels := by rfl

theorem canonical22047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22047 raw22047Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw22047 raw22047Labels = mixedMoment B raw22047step0 raw22047step0Labels := by
      have hz : ∀ j, raw22047 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22047step0 = (fun i j => raw22047 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22047step0 raw22047; decide +kernel
      have hl : raw22047step0Labels = raw22047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22047 raw22047Labels permutation520 hz
    mixedMoment B raw22047step0 raw22047step0Labels = mixedMoment B raw22047step1 raw22047step1Labels := by
      have hz : ∀ j, raw22047step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22047step1 = (fun i j => raw22047step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22047step1 raw22047step0; decide +kernel
      have hl : raw22047step1Labels = raw22047step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22047step0 raw22047step0Labels permutation104 hz
    mixedMoment B raw22047step1 raw22047step1Labels = mixedMoment B raw22047step2 raw22047step2Labels := by
      have hz : ∀ j, raw22047step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw22047step2 = (fun i j => raw22047step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw22047step2 raw22047step1; decide +kernel
      have hl : raw22047step2Labels = raw22047step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22047step1 raw22047step1Labels permutation20 hz
    _ = mixedMoment B node4071 node4071Labels := by rfl

theorem canonical22048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22048 raw22048Labels = mixedMoment B node555 node555Labels := by
  calc
    mixedMoment B raw22048 raw22048Labels = mixedMoment B raw22048step0 raw22048step0Labels := by
      have hz : ∀ j, raw22048 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22048step0 = (fun i j => raw22048 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22048step0 raw22048; decide +kernel
      have hl : raw22048step0Labels = raw22048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22048 raw22048Labels permutation434 hz
    mixedMoment B raw22048step0 raw22048step0Labels = mixedMoment B raw22048step1 raw22048step1Labels := by
      have hz : ∀ j, raw22048step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22048step1 = (fun i j => raw22048step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22048step1 raw22048step0; decide +kernel
      have hl : raw22048step1Labels = raw22048step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22048step0 raw22048step0Labels permutation80 hz
    mixedMoment B raw22048step1 raw22048step1Labels = mixedMoment B raw22048step2 raw22048step2Labels := by
      have ha : raw22048step2 = (fun i j => raw22048step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22048step2 raw22048step1; decide +kernel
      have hl : raw22048step2Labels = raw22048step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22048step1 raw22048step1Labels permutation10 permutation2
    _ = mixedMoment B node555 node555Labels := by rfl

theorem canonical22049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22049 raw22049Labels = mixedMoment B node715 node715Labels := by
  calc
    mixedMoment B raw22049 raw22049Labels = mixedMoment B raw22049step0 raw22049step0Labels := by
      have hz : ∀ j, raw22049 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22049step0 = (fun i j => raw22049 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22049step0 raw22049; decide +kernel
      have hl : raw22049step0Labels = raw22049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22049 raw22049Labels permutation434 hz
    mixedMoment B raw22049step0 raw22049step0Labels = mixedMoment B raw22049step1 raw22049step1Labels := by
      have ha : raw22049step1 = (fun i j => raw22049step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22049step1 raw22049step0; decide +kernel
      have hl : raw22049step1Labels = raw22049step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22049step0 raw22049step0Labels permutation40 permutation2
    _ = mixedMoment B node715 node715Labels := by rfl

theorem canonical22050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22050 raw22050Labels = mixedMoment B node715 node715Labels := by
  calc
    mixedMoment B raw22050 raw22050Labels = mixedMoment B raw22050step0 raw22050step0Labels := by
      have hz : ∀ j, raw22050 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22050step0 = (fun i j => raw22050 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22050step0 raw22050; decide +kernel
      have hl : raw22050step0Labels = raw22050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22050 raw22050Labels permutation346 hz
    mixedMoment B raw22050step0 raw22050step0Labels = mixedMoment B raw22050step1 raw22050step1Labels := by
      have ha : raw22050step1 = (fun i j => raw22050step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22050step1 raw22050step0; decide +kernel
      have hl : raw22050step1Labels = raw22050step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22050step0 raw22050step0Labels permutation40 permutation2
    _ = mixedMoment B node715 node715Labels := by rfl

theorem canonical22051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22051 raw22051Labels = mixedMoment B node859 node859Labels := by
  calc
    mixedMoment B raw22051 raw22051Labels = mixedMoment B raw22051step0 raw22051step0Labels := by
      have hz : ∀ j, raw22051 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22051step0 = (fun i j => raw22051 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22051step0 raw22051; decide +kernel
      have hl : raw22051step0Labels = raw22051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22051 raw22051Labels permutation520 hz
    mixedMoment B raw22051step0 raw22051step0Labels = mixedMoment B raw22051step1 raw22051step1Labels := by
      have hz : ∀ j, raw22051step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22051step1 = (fun i j => raw22051step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22051step1 raw22051step0; decide +kernel
      have hl : raw22051step1Labels = raw22051step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22051step0 raw22051step0Labels permutation104 hz
    mixedMoment B raw22051step1 raw22051step1Labels = mixedMoment B raw22051step2 raw22051step2Labels := by
      have hz : ∀ j, raw22051step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw22051step2 = (fun i j => raw22051step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw22051step2 raw22051step1; decide +kernel
      have hl : raw22051step2Labels = raw22051step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22051step1 raw22051step1Labels permutation20 hz
    _ = mixedMoment B node859 node859Labels := by rfl

theorem canonical22052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22052 raw22052Labels = mixedMoment B node852 node852Labels := by
  calc
    mixedMoment B raw22052 raw22052Labels = mixedMoment B raw22052step0 raw22052step0Labels := by
      have hz : ∀ j, raw22052 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22052step0 = (fun i j => raw22052 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22052step0 raw22052; decide +kernel
      have hl : raw22052step0Labels = raw22052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22052 raw22052Labels permutation434 hz
    mixedMoment B raw22052step0 raw22052step0Labels = mixedMoment B raw22052step1 raw22052step1Labels := by
      have hz : ∀ j, raw22052step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22052step1 = (fun i j => raw22052step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22052step1 raw22052step0; decide +kernel
      have hl : raw22052step1Labels = raw22052step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22052step0 raw22052step0Labels permutation80 hz
    mixedMoment B raw22052step1 raw22052step1Labels = mixedMoment B raw22052step2 raw22052step2Labels := by
      have ha : raw22052step2 = (fun i j => raw22052step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22052step2 raw22052step1; decide +kernel
      have hl : raw22052step2Labels = raw22052step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22052step1 raw22052step1Labels permutation10 permutation2
    _ = mixedMoment B node852 node852Labels := by rfl

theorem canonical22053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22053 raw22053Labels = mixedMoment B node823 node823Labels := by
  calc
    mixedMoment B raw22053 raw22053Labels = mixedMoment B raw22053step0 raw22053step0Labels := by
      have hz : ∀ j, raw22053 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22053step0 = (fun i j => raw22053 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22053step0 raw22053; decide +kernel
      have hl : raw22053step0Labels = raw22053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22053 raw22053Labels permutation434 hz
    _ = mixedMoment B node823 node823Labels := by rfl

theorem canonical22054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22054 raw22054Labels = mixedMoment B node823 node823Labels := by
  calc
    mixedMoment B raw22054 raw22054Labels = mixedMoment B raw22054step0 raw22054step0Labels := by
      have hz : ∀ j, raw22054 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22054step0 = (fun i j => raw22054 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22054step0 raw22054; decide +kernel
      have hl : raw22054step0Labels = raw22054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22054 raw22054Labels permutation346 hz
    _ = mixedMoment B node823 node823Labels := by rfl

theorem canonical22055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22055 raw22055Labels = mixedMoment B node830 node830Labels := by
  calc
    mixedMoment B raw22055 raw22055Labels = mixedMoment B raw22055step0 raw22055step0Labels := by
      have hz : ∀ j, raw22055 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22055step0 = (fun i j => raw22055 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22055step0 raw22055; decide +kernel
      have hl : raw22055step0Labels = raw22055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22055 raw22055Labels permutation434 hz
    mixedMoment B raw22055step0 raw22055step0Labels = mixedMoment B raw22055step1 raw22055step1Labels := by
      have hz : ∀ j, raw22055step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22055step1 = (fun i j => raw22055step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22055step1 raw22055step0; decide +kernel
      have hl : raw22055step1Labels = raw22055step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22055step0 raw22055step0Labels permutation80 hz
    _ = mixedMoment B node830 node830Labels := by rfl

theorem canonical22056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22056 raw22056Labels = mixedMoment B node546 node546Labels := by
  calc
    mixedMoment B raw22056 raw22056Labels = mixedMoment B raw22056step0 raw22056step0Labels := by
      have hz : ∀ j, raw22056 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22056step0 = (fun i j => raw22056 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22056step0 raw22056; decide +kernel
      have hl : raw22056step0Labels = raw22056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22056 raw22056Labels permutation434 hz
    mixedMoment B raw22056step0 raw22056step0Labels = mixedMoment B raw22056step1 raw22056step1Labels := by
      have hz : ∀ j, raw22056step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22056step1 = (fun i j => raw22056step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22056step1 raw22056step0; decide +kernel
      have hl : raw22056step1Labels = raw22056step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22056step0 raw22056step0Labels permutation80 hz
    mixedMoment B raw22056step1 raw22056step1Labels = mixedMoment B raw22056step2 raw22056step2Labels := by
      have ha : raw22056step2 = (fun i j => raw22056step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22056step2 raw22056step1; decide +kernel
      have hl : raw22056step2Labels = raw22056step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22056step1 raw22056step1Labels permutation10 permutation4
    mixedMoment B raw22056step2 raw22056step2Labels = mixedMoment B raw22056step3 raw22056step3Labels := by
      have ha : raw22056step3 = -raw22056step2 := by apply Matrix.ext; change ∀ i j, raw22056step3 i j = -(raw22056step2 i j); unfold raw22056step3 raw22056step2; decide +kernel
      have hl : raw22056step3Labels = raw22056step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node546 node546Labels := by rfl

theorem canonical22057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22057 raw22057Labels = mixedMoment B node706 node706Labels := by
  calc
    mixedMoment B raw22057 raw22057Labels = mixedMoment B raw22057step0 raw22057step0Labels := by
      have hz : ∀ j, raw22057 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22057step0 = (fun i j => raw22057 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22057step0 raw22057; decide +kernel
      have hl : raw22057step0Labels = raw22057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22057 raw22057Labels permutation434 hz
    mixedMoment B raw22057step0 raw22057step0Labels = mixedMoment B raw22057step1 raw22057step1Labels := by
      have ha : raw22057step1 = (fun i j => raw22057step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22057step1 raw22057step0; decide +kernel
      have hl : raw22057step1Labels = raw22057step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22057step0 raw22057step0Labels permutation40 permutation4
    mixedMoment B raw22057step1 raw22057step1Labels = mixedMoment B raw22057step2 raw22057step2Labels := by
      have ha : raw22057step2 = -raw22057step1 := by apply Matrix.ext; change ∀ i j, raw22057step2 i j = -(raw22057step1 i j); unfold raw22057step2 raw22057step1; decide +kernel
      have hl : raw22057step2Labels = raw22057step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node706 node706Labels := by rfl

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

theorem canonical759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw759 raw759Labels = mixedMoment B node4140 node4140Labels := by
  calc
    mixedMoment B raw759 raw759Labels = mixedMoment B raw759step0 raw759step0Labels := by
      have ha : raw759step0 = (fun i j => raw759 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw759step0 raw759; decide +kernel
      have hl : raw759step0Labels = raw759Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw759 raw759Labels permutation32 permutation4
    mixedMoment B raw759step0 raw759step0Labels = mixedMoment B raw759step1 raw759step1Labels := by
      have ha : raw759step1 = raw759step0 := by apply Matrix.ext; unfold raw759step1 raw759step0; decide +kernel
      have hl : raw759step0Labels = labelEmbedding7 ∘ raw759step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw759step0 raw759step0Labels raw759step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4140 node4140Labels := by rfl

theorem canonical760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw760 raw760Labels = mixedMoment B node568 node568Labels := by
  calc
    mixedMoment B raw760 raw760Labels = mixedMoment B raw760step0 raw760step0Labels := by
      have ha : raw760step0 = (fun i j => raw760 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw760step0 raw760; decide +kernel
      have hl : raw760step0Labels = raw760Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw760 raw760Labels permutation32 permutation4
    _ = mixedMoment B node568 node568Labels := by rfl

theorem canonical761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw761 raw761Labels = mixedMoment B node1489 node1489Labels := by
  calc
    mixedMoment B raw761 raw761Labels = mixedMoment B raw761step0 raw761step0Labels := by
      have ha : raw761step0 = (fun i j => raw761 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw761step0 raw761; decide +kernel
      have hl : raw761step0Labels = raw761Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw761 raw761Labels permutation32 permutation6
    mixedMoment B raw761step0 raw761step0Labels = mixedMoment B raw761step1 raw761step1Labels := by
      have ha : raw761step1 = -raw761step0 := by apply Matrix.ext; change ∀ i j, raw761step1 i j = -(raw761step0 i j); unfold raw761step1 raw761step0; decide +kernel
      have hl : raw761step1Labels = raw761step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw761step1 raw761step1Labels = mixedMoment B raw761step2 raw761step2Labels := by
      have ha : raw761step2 = raw761step1 := by apply Matrix.ext; unfold raw761step2 raw761step1; decide +kernel
      have hl : raw761step1Labels = labelEmbedding1 ∘ raw761step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw761step1 raw761step1Labels raw761step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1489 node1489Labels := by rfl

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

theorem canonical777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw777 raw777Labels = mixedMoment B node4146 node4146Labels := by
  calc
    mixedMoment B raw777 raw777Labels = mixedMoment B raw777step0 raw777step0Labels := by
      have ha : raw777step0 = (fun i j => raw777 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw777step0 raw777; decide +kernel
      have hl : raw777step0Labels = raw777Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw777 raw777Labels permutation8 permutation4
    mixedMoment B raw777step0 raw777step0Labels = mixedMoment B raw777step1 raw777step1Labels := by
      have ha : raw777step1 = raw777step0 := by apply Matrix.ext; unfold raw777step1 raw777step0; decide +kernel
      have hl : raw777step0Labels = labelEmbedding7 ∘ raw777step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw777step0 raw777step0Labels raw777step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4146 node4146Labels := by rfl

theorem canonical778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw778 raw778Labels = mixedMoment B node574 node574Labels := by
  calc
    mixedMoment B raw778 raw778Labels = mixedMoment B raw778step0 raw778step0Labels := by
      have ha : raw778step0 = (fun i j => raw778 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw778step0 raw778; decide +kernel
      have hl : raw778step0Labels = raw778Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw778 raw778Labels permutation8 permutation4
    _ = mixedMoment B node574 node574Labels := by rfl

theorem canonical779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw779 raw779Labels = mixedMoment B node1494 node1494Labels := by
  calc
    mixedMoment B raw779 raw779Labels = mixedMoment B raw779step0 raw779step0Labels := by
      have ha : raw779step0 = (fun i j => raw779 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw779step0 raw779; decide +kernel
      have hl : raw779step0Labels = raw779Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw779 raw779Labels permutation8 permutation6
    mixedMoment B raw779step0 raw779step0Labels = mixedMoment B raw779step1 raw779step1Labels := by
      have ha : raw779step1 = -raw779step0 := by apply Matrix.ext; change ∀ i j, raw779step1 i j = -(raw779step0 i j); unfold raw779step1 raw779step0; decide +kernel
      have hl : raw779step1Labels = raw779step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw779step1 raw779step1Labels = mixedMoment B raw779step2 raw779step2Labels := by
      have ha : raw779step2 = raw779step1 := by apply Matrix.ext; unfold raw779step2 raw779step1; decide +kernel
      have hl : raw779step1Labels = labelEmbedding1 ∘ raw779step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw779step1 raw779step1Labels raw779step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1494 node1494Labels := by rfl

theorem canonical780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw780 raw780Labels = mixedMoment B node4147 node4147Labels := by
  calc
    mixedMoment B raw780 raw780Labels = mixedMoment B raw780step0 raw780step0Labels := by
      have ha : raw780step0 = (fun i j => raw780 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw780step0 raw780; decide +kernel
      have hl : raw780step0Labels = raw780Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw780 raw780Labels permutation8 permutation4
    mixedMoment B raw780step0 raw780step0Labels = mixedMoment B raw780step1 raw780step1Labels := by
      have ha : raw780step1 = raw780step0 := by apply Matrix.ext; unfold raw780step1 raw780step0; decide +kernel
      have hl : raw780step0Labels = labelEmbedding7 ∘ raw780step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw780step0 raw780step0Labels raw780step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4147 node4147Labels := by rfl

theorem canonical781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw781 raw781Labels = mixedMoment B node575 node575Labels := by
  calc
    mixedMoment B raw781 raw781Labels = mixedMoment B raw781step0 raw781step0Labels := by
      have ha : raw781step0 = (fun i j => raw781 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw781step0 raw781; decide +kernel
      have hl : raw781step0Labels = raw781Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw781 raw781Labels permutation8 permutation4
    _ = mixedMoment B node575 node575Labels := by rfl

theorem canonical782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw782 raw782Labels = mixedMoment B node1495 node1495Labels := by
  calc
    mixedMoment B raw782 raw782Labels = mixedMoment B raw782step0 raw782step0Labels := by
      have ha : raw782step0 = (fun i j => raw782 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw782step0 raw782; decide +kernel
      have hl : raw782step0Labels = raw782Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw782 raw782Labels permutation8 permutation6
    mixedMoment B raw782step0 raw782step0Labels = mixedMoment B raw782step1 raw782step1Labels := by
      have ha : raw782step1 = -raw782step0 := by apply Matrix.ext; change ∀ i j, raw782step1 i j = -(raw782step0 i j); unfold raw782step1 raw782step0; decide +kernel
      have hl : raw782step1Labels = raw782step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw782step1 raw782step1Labels = mixedMoment B raw782step2 raw782step2Labels := by
      have ha : raw782step2 = raw782step1 := by apply Matrix.ext; unfold raw782step2 raw782step1; decide +kernel
      have hl : raw782step1Labels = labelEmbedding1 ∘ raw782step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw782step1 raw782step1Labels raw782step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1495 node1495Labels := by rfl

theorem canonical792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw792 raw792Labels = mixedMoment B node4166 node4166Labels := by
  calc
    mixedMoment B raw792 raw792Labels = mixedMoment B raw792step0 raw792step0Labels := by
      have ha : raw792step0 = (fun i j => raw792 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw792step0 raw792; decide +kernel
      have hl : raw792step0Labels = raw792Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw792 raw792Labels permutation8 permutation4
    mixedMoment B raw792step0 raw792step0Labels = mixedMoment B raw792step1 raw792step1Labels := by
      have ha : raw792step1 = raw792step0 := by apply Matrix.ext; unfold raw792step1 raw792step0; decide +kernel
      have hl : raw792step0Labels = labelEmbedding7 ∘ raw792step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw792step0 raw792step0Labels raw792step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4166 node4166Labels := by rfl

theorem canonical793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw793 raw793Labels = mixedMoment B node594 node594Labels := by
  calc
    mixedMoment B raw793 raw793Labels = mixedMoment B raw793step0 raw793step0Labels := by
      have ha : raw793step0 = (fun i j => raw793 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw793step0 raw793; decide +kernel
      have hl : raw793step0Labels = raw793Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw793 raw793Labels permutation8 permutation4
    _ = mixedMoment B node594 node594Labels := by rfl

theorem canonical794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw794 raw794Labels = mixedMoment B node1499 node1499Labels := by
  calc
    mixedMoment B raw794 raw794Labels = mixedMoment B raw794step0 raw794step0Labels := by
      have ha : raw794step0 = (fun i j => raw794 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw794step0 raw794; decide +kernel
      have hl : raw794step0Labels = raw794Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw794 raw794Labels permutation8 permutation6
    mixedMoment B raw794step0 raw794step0Labels = mixedMoment B raw794step1 raw794step1Labels := by
      have ha : raw794step1 = -raw794step0 := by apply Matrix.ext; change ∀ i j, raw794step1 i j = -(raw794step0 i j); unfold raw794step1 raw794step0; decide +kernel
      have hl : raw794step1Labels = raw794step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw794step1 raw794step1Labels = mixedMoment B raw794step2 raw794step2Labels := by
      have ha : raw794step2 = raw794step1 := by apply Matrix.ext; unfold raw794step2 raw794step1; decide +kernel
      have hl : raw794step1Labels = labelEmbedding1 ∘ raw794step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw794step1 raw794step1Labels raw794step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1499 node1499Labels := by rfl

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

theorem canonical1029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1029 raw1029Labels = mixedMoment B node4289 node4289Labels := by
  calc
    mixedMoment B raw1029 raw1029Labels = mixedMoment B raw1029step0 raw1029step0Labels := by
      have ha : raw1029step0 = (fun i j => raw1029 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1029step0 raw1029; decide +kernel
      have hl : raw1029step0Labels = raw1029Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1029 raw1029Labels permutation32 permutation4
    mixedMoment B raw1029step0 raw1029step0Labels = mixedMoment B raw1029step1 raw1029step1Labels := by
      have ha : raw1029step1 = raw1029step0 := by apply Matrix.ext; unfold raw1029step1 raw1029step0; decide +kernel
      have hl : raw1029step0Labels = labelEmbedding7 ∘ raw1029step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1029step0 raw1029step0Labels raw1029step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4289 node4289Labels := by rfl

theorem canonical1030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1030 raw1030Labels = mixedMoment B node867 node867Labels := by
  calc
    mixedMoment B raw1030 raw1030Labels = mixedMoment B raw1030step0 raw1030step0Labels := by
      have ha : raw1030step0 = (fun i j => raw1030 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1030step0 raw1030; decide +kernel
      have hl : raw1030step0Labels = raw1030Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1030 raw1030Labels permutation32 permutation4
    _ = mixedMoment B node867 node867Labels := by rfl

theorem canonical1031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1031 raw1031Labels = mixedMoment B node1555 node1555Labels := by
  calc
    mixedMoment B raw1031 raw1031Labels = mixedMoment B raw1031step0 raw1031step0Labels := by
      have ha : raw1031step0 = (fun i j => raw1031 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1031step0 raw1031; decide +kernel
      have hl : raw1031step0Labels = raw1031Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1031 raw1031Labels permutation34 permutation6
    mixedMoment B raw1031step0 raw1031step0Labels = mixedMoment B raw1031step1 raw1031step1Labels := by
      have ha : raw1031step1 = -raw1031step0 := by apply Matrix.ext; change ∀ i j, raw1031step1 i j = -(raw1031step0 i j); unfold raw1031step1 raw1031step0; decide +kernel
      have hl : raw1031step1Labels = raw1031step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1031step1 raw1031step1Labels = mixedMoment B raw1031step2 raw1031step2Labels := by
      have ha : raw1031step2 = raw1031step1 := by apply Matrix.ext; unfold raw1031step2 raw1031step1; decide +kernel
      have hl : raw1031step1Labels = labelEmbedding1 ∘ raw1031step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1031step1 raw1031step1Labels raw1031step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1555 node1555Labels := by rfl

theorem canonical1095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1095 raw1095Labels = mixedMoment B node4320 node4320Labels := by
  calc
    mixedMoment B raw1095 raw1095Labels = mixedMoment B raw1095step0 raw1095step0Labels := by
      have ha : raw1095step0 = (fun i j => raw1095 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1095step0 raw1095; decide +kernel
      have hl : raw1095step0Labels = raw1095Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1095 raw1095Labels permutation152 permutation4
    mixedMoment B raw1095step0 raw1095step0Labels = mixedMoment B raw1095step1 raw1095step1Labels := by
      have ha : raw1095step1 = raw1095step0 := by apply Matrix.ext; unfold raw1095step1 raw1095step0; decide +kernel
      have hl : raw1095step0Labels = labelEmbedding7 ∘ raw1095step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1095step0 raw1095step0Labels raw1095step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4320 node4320Labels := by rfl

theorem canonical1096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1096 raw1096Labels = mixedMoment B node898 node898Labels := by
  calc
    mixedMoment B raw1096 raw1096Labels = mixedMoment B raw1096step0 raw1096step0Labels := by
      have ha : raw1096step0 = (fun i j => raw1096 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1096step0 raw1096; decide +kernel
      have hl : raw1096step0Labels = raw1096Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1096 raw1096Labels permutation152 permutation4
    _ = mixedMoment B node898 node898Labels := by rfl

theorem canonical1097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1097 raw1097Labels = mixedMoment B node1586 node1586Labels := by
  calc
    mixedMoment B raw1097 raw1097Labels = mixedMoment B raw1097step0 raw1097step0Labels := by
      have ha : raw1097step0 = (fun i j => raw1097 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1097step0 raw1097; decide +kernel
      have hl : raw1097step0Labels = raw1097Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1097 raw1097Labels permutation176 permutation6
    mixedMoment B raw1097step0 raw1097step0Labels = mixedMoment B raw1097step1 raw1097step1Labels := by
      have ha : raw1097step1 = -raw1097step0 := by apply Matrix.ext; change ∀ i j, raw1097step1 i j = -(raw1097step0 i j); unfold raw1097step1 raw1097step0; decide +kernel
      have hl : raw1097step1Labels = raw1097step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1097step1 raw1097step1Labels = mixedMoment B raw1097step2 raw1097step2Labels := by
      have ha : raw1097step2 = raw1097step1 := by apply Matrix.ext; unfold raw1097step2 raw1097step1; decide +kernel
      have hl : raw1097step1Labels = labelEmbedding1 ∘ raw1097step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1097step1 raw1097step1Labels raw1097step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1586 node1586Labels := by rfl

theorem canonical1107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1107 raw1107Labels = mixedMoment B node4324 node4324Labels := by
  calc
    mixedMoment B raw1107 raw1107Labels = mixedMoment B raw1107step0 raw1107step0Labels := by
      have ha : raw1107step0 = (fun i j => raw1107 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1107step0 raw1107; decide +kernel
      have hl : raw1107step0Labels = raw1107Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1107 raw1107Labels permutation32 permutation4
    mixedMoment B raw1107step0 raw1107step0Labels = mixedMoment B raw1107step1 raw1107step1Labels := by
      have ha : raw1107step1 = raw1107step0 := by apply Matrix.ext; unfold raw1107step1 raw1107step0; decide +kernel
      have hl : raw1107step0Labels = labelEmbedding7 ∘ raw1107step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1107step0 raw1107step0Labels raw1107step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4324 node4324Labels := by rfl

theorem canonical1108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1108 raw1108Labels = mixedMoment B node902 node902Labels := by
  calc
    mixedMoment B raw1108 raw1108Labels = mixedMoment B raw1108step0 raw1108step0Labels := by
      have ha : raw1108step0 = (fun i j => raw1108 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1108step0 raw1108; decide +kernel
      have hl : raw1108step0Labels = raw1108Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1108 raw1108Labels permutation32 permutation4
    _ = mixedMoment B node902 node902Labels := by rfl

theorem canonical1109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1109 raw1109Labels = mixedMoment B node1590 node1590Labels := by
  calc
    mixedMoment B raw1109 raw1109Labels = mixedMoment B raw1109step0 raw1109step0Labels := by
      have ha : raw1109step0 = (fun i j => raw1109 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1109step0 raw1109; decide +kernel
      have hl : raw1109step0Labels = raw1109Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1109 raw1109Labels permutation38 permutation6
    mixedMoment B raw1109step0 raw1109step0Labels = mixedMoment B raw1109step1 raw1109step1Labels := by
      have ha : raw1109step1 = -raw1109step0 := by apply Matrix.ext; change ∀ i j, raw1109step1 i j = -(raw1109step0 i j); unfold raw1109step1 raw1109step0; decide +kernel
      have hl : raw1109step1Labels = raw1109step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1109step1 raw1109step1Labels = mixedMoment B raw1109step2 raw1109step2Labels := by
      have ha : raw1109step2 = raw1109step1 := by apply Matrix.ext; unfold raw1109step2 raw1109step1; decide +kernel
      have hl : raw1109step1Labels = labelEmbedding1 ∘ raw1109step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1109step1 raw1109step1Labels raw1109step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1590 node1590Labels := by rfl

theorem canonical1116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1116 raw1116Labels = mixedMoment B node4338 node4338Labels := by
  calc
    mixedMoment B raw1116 raw1116Labels = mixedMoment B raw1116step0 raw1116step0Labels := by
      have ha : raw1116step0 = (fun i j => raw1116 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1116step0 raw1116; decide +kernel
      have hl : raw1116step0Labels = raw1116Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1116 raw1116Labels permutation32 permutation4
    mixedMoment B raw1116step0 raw1116step0Labels = mixedMoment B raw1116step1 raw1116step1Labels := by
      have ha : raw1116step1 = raw1116step0 := by apply Matrix.ext; unfold raw1116step1 raw1116step0; decide +kernel
      have hl : raw1116step0Labels = labelEmbedding7 ∘ raw1116step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1116step0 raw1116step0Labels raw1116step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4338 node4338Labels := by rfl

theorem canonical1117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1117 raw1117Labels = mixedMoment B node916 node916Labels := by
  calc
    mixedMoment B raw1117 raw1117Labels = mixedMoment B raw1117step0 raw1117step0Labels := by
      have ha : raw1117step0 = (fun i j => raw1117 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1117step0 raw1117; decide +kernel
      have hl : raw1117step0Labels = raw1117Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1117 raw1117Labels permutation32 permutation4
    _ = mixedMoment B node916 node916Labels := by rfl

theorem canonical1118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1118 raw1118Labels = mixedMoment B node1633 node1633Labels := by
  calc
    mixedMoment B raw1118 raw1118Labels = mixedMoment B raw1118step0 raw1118step0Labels := by
      have ha : raw1118step0 = (fun i j => raw1118 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1118step0 raw1118; decide +kernel
      have hl : raw1118step0Labels = raw1118Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1118 raw1118Labels permutation38 permutation6
    mixedMoment B raw1118step0 raw1118step0Labels = mixedMoment B raw1118step1 raw1118step1Labels := by
      have ha : raw1118step1 = -raw1118step0 := by apply Matrix.ext; change ∀ i j, raw1118step1 i j = -(raw1118step0 i j); unfold raw1118step1 raw1118step0; decide +kernel
      have hl : raw1118step1Labels = raw1118step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1118step1 raw1118step1Labels = mixedMoment B raw1118step2 raw1118step2Labels := by
      have ha : raw1118step2 = raw1118step1 := by apply Matrix.ext; unfold raw1118step2 raw1118step1; decide +kernel
      have hl : raw1118step1Labels = labelEmbedding1 ∘ raw1118step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1118step1 raw1118step1Labels raw1118step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1633 node1633Labels := by rfl

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

theorem canonical1209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1209 raw1209Labels = mixedMoment B node4398 node4398Labels := by
  calc
    mixedMoment B raw1209 raw1209Labels = mixedMoment B raw1209step0 raw1209step0Labels := by
      have ha : raw1209step0 = (fun i j => raw1209 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1209step0 raw1209; decide +kernel
      have hl : raw1209step0Labels = raw1209Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1209 raw1209Labels permutation32 permutation4
    mixedMoment B raw1209step0 raw1209step0Labels = mixedMoment B raw1209step1 raw1209step1Labels := by
      have ha : raw1209step1 = raw1209step0 := by apply Matrix.ext; unfold raw1209step1 raw1209step0; decide +kernel
      have hl : raw1209step0Labels = labelEmbedding7 ∘ raw1209step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1209step0 raw1209step0Labels raw1209step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4398 node4398Labels := by rfl

theorem canonical1210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1210 raw1210Labels = mixedMoment B node979 node979Labels := by
  calc
    mixedMoment B raw1210 raw1210Labels = mixedMoment B raw1210step0 raw1210step0Labels := by
      have ha : raw1210step0 = (fun i j => raw1210 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1210step0 raw1210; decide +kernel
      have hl : raw1210step0Labels = raw1210Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1210 raw1210Labels permutation32 permutation4
    _ = mixedMoment B node979 node979Labels := by rfl

theorem canonical1211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1211 raw1211Labels = mixedMoment B node1599 node1599Labels := by
  calc
    mixedMoment B raw1211 raw1211Labels = mixedMoment B raw1211step0 raw1211step0Labels := by
      have ha : raw1211step0 = (fun i j => raw1211 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1211step0 raw1211; decide +kernel
      have hl : raw1211step0Labels = raw1211Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1211 raw1211Labels permutation34 permutation6
    mixedMoment B raw1211step0 raw1211step0Labels = mixedMoment B raw1211step1 raw1211step1Labels := by
      have ha : raw1211step1 = -raw1211step0 := by apply Matrix.ext; change ∀ i j, raw1211step1 i j = -(raw1211step0 i j); unfold raw1211step1 raw1211step0; decide +kernel
      have hl : raw1211step1Labels = raw1211step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1211step1 raw1211step1Labels = mixedMoment B raw1211step2 raw1211step2Labels := by
      have ha : raw1211step2 = raw1211step1 := by apply Matrix.ext; unfold raw1211step2 raw1211step1; decide +kernel
      have hl : raw1211step1Labels = labelEmbedding1 ∘ raw1211step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1211step1 raw1211step1Labels raw1211step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1599 node1599Labels := by rfl

theorem canonical1221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1221 raw1221Labels = mixedMoment B node4405 node4405Labels := by
  calc
    mixedMoment B raw1221 raw1221Labels = mixedMoment B raw1221step0 raw1221step0Labels := by
      have ha : raw1221step0 = (fun i j => raw1221 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1221step0 raw1221; decide +kernel
      have hl : raw1221step0Labels = raw1221Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1221 raw1221Labels permutation8 permutation4
    mixedMoment B raw1221step0 raw1221step0Labels = mixedMoment B raw1221step1 raw1221step1Labels := by
      have ha : raw1221step1 = raw1221step0 := by apply Matrix.ext; unfold raw1221step1 raw1221step0; decide +kernel
      have hl : raw1221step0Labels = labelEmbedding7 ∘ raw1221step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1221step0 raw1221step0Labels raw1221step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4405 node4405Labels := by rfl

theorem canonical1222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1222 raw1222Labels = mixedMoment B node986 node986Labels := by
  calc
    mixedMoment B raw1222 raw1222Labels = mixedMoment B raw1222step0 raw1222step0Labels := by
      have ha : raw1222step0 = (fun i j => raw1222 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1222step0 raw1222; decide +kernel
      have hl : raw1222step0Labels = raw1222Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1222 raw1222Labels permutation8 permutation4
    _ = mixedMoment B node986 node986Labels := by rfl

theorem canonical1223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1223 raw1223Labels = mixedMoment B node1620 node1620Labels := by
  calc
    mixedMoment B raw1223 raw1223Labels = mixedMoment B raw1223step0 raw1223step0Labels := by
      have ha : raw1223step0 = (fun i j => raw1223 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1223step0 raw1223; decide +kernel
      have hl : raw1223step0Labels = raw1223Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1223 raw1223Labels permutation31 permutation6
    mixedMoment B raw1223step0 raw1223step0Labels = mixedMoment B raw1223step1 raw1223step1Labels := by
      have ha : raw1223step1 = raw1223step0 := by apply Matrix.ext; unfold raw1223step1 raw1223step0; decide +kernel
      have hl : raw1223step0Labels = labelEmbedding1 ∘ raw1223step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1223step0 raw1223step0Labels raw1223step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1620 node1620Labels := by rfl

theorem canonical1227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1227 raw1227Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw1227 raw1227Labels = mixedMoment B raw1227step0 raw1227step0Labels := by
      have ha : raw1227step0 = (fun i j => raw1227 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1227step0 raw1227; decide +kernel
      have hl : raw1227step0Labels = raw1227Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1227 raw1227Labels permutation32 permutation4
    mixedMoment B raw1227step0 raw1227step0Labels = mixedMoment B raw1227step1 raw1227step1Labels := by
      have ha : raw1227step1 = raw1227step0 := by apply Matrix.ext; unfold raw1227step1 raw1227step0; decide +kernel
      have hl : raw1227step0Labels = labelEmbedding7 ∘ raw1227step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1227step0 raw1227step0Labels raw1227step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

theorem canonical1228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1228 raw1228Labels = mixedMoment B node999 node999Labels := by
  calc
    mixedMoment B raw1228 raw1228Labels = mixedMoment B raw1228step0 raw1228step0Labels := by
      have ha : raw1228step0 = (fun i j => raw1228 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1228step0 raw1228; decide +kernel
      have hl : raw1228step0Labels = raw1228Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1228 raw1228Labels permutation32 permutation4
    _ = mixedMoment B node999 node999Labels := by rfl

theorem canonical1229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1229 raw1229Labels = mixedMoment B node1602 node1602Labels := by
  calc
    mixedMoment B raw1229 raw1229Labels = mixedMoment B raw1229step0 raw1229step0Labels := by
      have ha : raw1229step0 = (fun i j => raw1229 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1229step0 raw1229; decide +kernel
      have hl : raw1229step0Labels = raw1229Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1229 raw1229Labels permutation32 permutation6
    mixedMoment B raw1229step0 raw1229step0Labels = mixedMoment B raw1229step1 raw1229step1Labels := by
      have ha : raw1229step1 = -raw1229step0 := by apply Matrix.ext; change ∀ i j, raw1229step1 i j = -(raw1229step0 i j); unfold raw1229step1 raw1229step0; decide +kernel
      have hl : raw1229step1Labels = raw1229step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1229step1 raw1229step1Labels = mixedMoment B raw1229step2 raw1229step2Labels := by
      have ha : raw1229step2 = raw1229step1 := by apply Matrix.ext; unfold raw1229step2 raw1229step1; decide +kernel
      have hl : raw1229step1Labels = labelEmbedding1 ∘ raw1229step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1229step1 raw1229step1Labels raw1229step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1602 node1602Labels := by rfl

theorem canonical1242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1242 raw1242Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw1242 raw1242Labels = mixedMoment B raw1242step0 raw1242step0Labels := by
      have ha : raw1242step0 = (fun i j => raw1242 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1242step0 raw1242; decide +kernel
      have hl : raw1242step0Labels = raw1242Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1242 raw1242Labels permutation8 permutation4
    mixedMoment B raw1242step0 raw1242step0Labels = mixedMoment B raw1242step1 raw1242step1Labels := by
      have ha : raw1242step1 = raw1242step0 := by apply Matrix.ext; unfold raw1242step1 raw1242step0; decide +kernel
      have hl : raw1242step0Labels = labelEmbedding7 ∘ raw1242step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1242step0 raw1242step0Labels raw1242step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4431 node4431Labels := by rfl

theorem canonical1243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1243 raw1243Labels = mixedMoment B node1012 node1012Labels := by
  calc
    mixedMoment B raw1243 raw1243Labels = mixedMoment B raw1243step0 raw1243step0Labels := by
      have ha : raw1243step0 = (fun i j => raw1243 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1243step0 raw1243; decide +kernel
      have hl : raw1243step0Labels = raw1243Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1243 raw1243Labels permutation8 permutation4
    _ = mixedMoment B node1012 node1012Labels := by rfl

theorem canonical1244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1244 raw1244Labels = mixedMoment B node1627 node1627Labels := by
  calc
    mixedMoment B raw1244 raw1244Labels = mixedMoment B raw1244step0 raw1244step0Labels := by
      have ha : raw1244step0 = (fun i j => raw1244 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1244step0 raw1244; decide +kernel
      have hl : raw1244step0Labels = raw1244Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1244 raw1244Labels permutation8 permutation6
    mixedMoment B raw1244step0 raw1244step0Labels = mixedMoment B raw1244step1 raw1244step1Labels := by
      have ha : raw1244step1 = -raw1244step0 := by apply Matrix.ext; change ∀ i j, raw1244step1 i j = -(raw1244step0 i j); unfold raw1244step1 raw1244step0; decide +kernel
      have hl : raw1244step1Labels = raw1244step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1244step1 raw1244step1Labels = mixedMoment B raw1244step2 raw1244step2Labels := by
      have ha : raw1244step2 = raw1244step1 := by apply Matrix.ext; unfold raw1244step2 raw1244step1; decide +kernel
      have hl : raw1244step1Labels = labelEmbedding1 ∘ raw1244step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1244step1 raw1244step1Labels raw1244step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1627 node1627Labels := by rfl

theorem canonical1251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1251 raw1251Labels = mixedMoment B node4454 node4454Labels := by
  calc
    mixedMoment B raw1251 raw1251Labels = mixedMoment B raw1251step0 raw1251step0Labels := by
      have ha : raw1251step0 = (fun i j => raw1251 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1251step0 raw1251; decide +kernel
      have hl : raw1251step0Labels = raw1251Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1251 raw1251Labels permutation8 permutation4
    mixedMoment B raw1251step0 raw1251step0Labels = mixedMoment B raw1251step1 raw1251step1Labels := by
      have ha : raw1251step1 = raw1251step0 := by apply Matrix.ext; unfold raw1251step1 raw1251step0; decide +kernel
      have hl : raw1251step0Labels = labelEmbedding7 ∘ raw1251step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1251step0 raw1251step0Labels raw1251step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4454 node4454Labels := by rfl

theorem canonical1252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1252 raw1252Labels = mixedMoment B node1037 node1037Labels := by
  calc
    mixedMoment B raw1252 raw1252Labels = mixedMoment B raw1252step0 raw1252step0Labels := by
      have ha : raw1252step0 = (fun i j => raw1252 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1252step0 raw1252; decide +kernel
      have hl : raw1252step0Labels = raw1252Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1252 raw1252Labels permutation8 permutation4
    _ = mixedMoment B node1037 node1037Labels := by rfl

theorem canonical1253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1253 raw1253Labels = mixedMoment B node1647 node1647Labels := by
  calc
    mixedMoment B raw1253 raw1253Labels = mixedMoment B raw1253step0 raw1253step0Labels := by
      have ha : raw1253step0 = (fun i j => raw1253 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1253step0 raw1253; decide +kernel
      have hl : raw1253step0Labels = raw1253Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1253 raw1253Labels permutation10 permutation6
    mixedMoment B raw1253step0 raw1253step0Labels = mixedMoment B raw1253step1 raw1253step1Labels := by
      have ha : raw1253step1 = -raw1253step0 := by apply Matrix.ext; change ∀ i j, raw1253step1 i j = -(raw1253step0 i j); unfold raw1253step1 raw1253step0; decide +kernel
      have hl : raw1253step1Labels = raw1253step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1253step1 raw1253step1Labels = mixedMoment B raw1253step2 raw1253step2Labels := by
      have ha : raw1253step2 = raw1253step1 := by apply Matrix.ext; unfold raw1253step2 raw1253step1; decide +kernel
      have hl : raw1253step1Labels = labelEmbedding1 ∘ raw1253step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1253step1 raw1253step1Labels raw1253step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1647 node1647Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_FiniteSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sum_fin_six {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
  ac_rfl

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

theorem singleton4140 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4140 node4140Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node568 node568Labels + mixedMoment B node1489 node1489Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw759 singletonSmall4140
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4140) = raw759Labels := by decide +kernel
  rw [hl, canonical759 B hB] at h
  have hc0 : mixedMoment B raw759 (Fin.cases (0 : Fin 2) singletonSmall4140) =
      mixedMoment B node568 node568Labels := by
    have ha : raw759 = raw760 := by apply Matrix.ext; unfold raw759 raw760; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4140 = raw760Labels := by decide +kernel
    rw [ha, hj, canonical760 B hB]
  have hc1 : mixedMoment B raw759 (Fin.cases (1 : Fin 2) singletonSmall4140) =
      mixedMoment B node1489 node1489Labels := by
    have ha : raw759 = raw761 := by apply Matrix.ext; unfold raw759 raw761; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4140 = raw761Labels := by decide +kernel
    rw [ha, hj, canonical761 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4146 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4146 node4146Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node574 node574Labels + mixedMoment B node1494 node1494Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw777 singletonSmall4146
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4146) = raw777Labels := by decide +kernel
  rw [hl, canonical777 B hB] at h
  have hc0 : mixedMoment B raw777 (Fin.cases (0 : Fin 2) singletonSmall4146) =
      mixedMoment B node574 node574Labels := by
    have ha : raw777 = raw778 := by apply Matrix.ext; unfold raw777 raw778; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4146 = raw778Labels := by decide +kernel
    rw [ha, hj, canonical778 B hB]
  have hc1 : mixedMoment B raw777 (Fin.cases (1 : Fin 2) singletonSmall4146) =
      mixedMoment B node1494 node1494Labels := by
    have ha : raw777 = raw779 := by apply Matrix.ext; unfold raw777 raw779; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4146 = raw779Labels := by decide +kernel
    rw [ha, hj, canonical779 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4147 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4147 node4147Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node575 node575Labels + mixedMoment B node1495 node1495Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw780 singletonSmall4147
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4147) = raw780Labels := by decide +kernel
  rw [hl, canonical780 B hB] at h
  have hc0 : mixedMoment B raw780 (Fin.cases (0 : Fin 2) singletonSmall4147) =
      mixedMoment B node575 node575Labels := by
    have ha : raw780 = raw781 := by apply Matrix.ext; unfold raw780 raw781; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4147 = raw781Labels := by decide +kernel
    rw [ha, hj, canonical781 B hB]
  have hc1 : mixedMoment B raw780 (Fin.cases (1 : Fin 2) singletonSmall4147) =
      mixedMoment B node1495 node1495Labels := by
    have ha : raw780 = raw782 := by apply Matrix.ext; unfold raw780 raw782; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4147 = raw782Labels := by decide +kernel
    rw [ha, hj, canonical782 B hB]
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

theorem singleton4166 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4166 node4166Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node594 node594Labels + mixedMoment B node1499 node1499Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw792 singletonSmall4166
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4166) = raw792Labels := by decide +kernel
  rw [hl, canonical792 B hB] at h
  have hc0 : mixedMoment B raw792 (Fin.cases (0 : Fin 2) singletonSmall4166) =
      mixedMoment B node594 node594Labels := by
    have ha : raw792 = raw793 := by apply Matrix.ext; unfold raw792 raw793; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4166 = raw793Labels := by decide +kernel
    rw [ha, hj, canonical793 B hB]
  have hc1 : mixedMoment B raw792 (Fin.cases (1 : Fin 2) singletonSmall4166) =
      mixedMoment B node1499 node1499Labels := by
    have ha : raw792 = raw794 := by apply Matrix.ext; unfold raw792 raw794; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4166 = raw794Labels := by decide +kernel
    rw [ha, hj, canonical794 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

end MUB6.Certificate.MixedSemantics

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

theorem singleton4289 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4289 node4289Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node867 node867Labels + mixedMoment B node1555 node1555Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1029 singletonSmall4289
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4289) = raw1029Labels := by decide +kernel
  rw [hl, canonical1029 B hB] at h
  have hc0 : mixedMoment B raw1029 (Fin.cases (0 : Fin 2) singletonSmall4289) =
      mixedMoment B node867 node867Labels := by
    have ha : raw1029 = raw1030 := by apply Matrix.ext; unfold raw1029 raw1030; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4289 = raw1030Labels := by decide +kernel
    rw [ha, hj, canonical1030 B hB]
  have hc1 : mixedMoment B raw1029 (Fin.cases (1 : Fin 2) singletonSmall4289) =
      mixedMoment B node1555 node1555Labels := by
    have ha : raw1029 = raw1031 := by apply Matrix.ext; unfold raw1029 raw1031; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4289 = raw1031Labels := by decide +kernel
    rw [ha, hj, canonical1031 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4320 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4320 node4320Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node898 node898Labels + mixedMoment B node1586 node1586Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1095 singletonSmall4320
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4320) = raw1095Labels := by decide +kernel
  rw [hl, canonical1095 B hB] at h
  have hc0 : mixedMoment B raw1095 (Fin.cases (0 : Fin 2) singletonSmall4320) =
      mixedMoment B node898 node898Labels := by
    have ha : raw1095 = raw1096 := by apply Matrix.ext; unfold raw1095 raw1096; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4320 = raw1096Labels := by decide +kernel
    rw [ha, hj, canonical1096 B hB]
  have hc1 : mixedMoment B raw1095 (Fin.cases (1 : Fin 2) singletonSmall4320) =
      mixedMoment B node1586 node1586Labels := by
    have ha : raw1095 = raw1097 := by apply Matrix.ext; unfold raw1095 raw1097; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4320 = raw1097Labels := by decide +kernel
    rw [ha, hj, canonical1097 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4324 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4324 node4324Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node902 node902Labels + mixedMoment B node1590 node1590Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1107 singletonSmall4324
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4324) = raw1107Labels := by decide +kernel
  rw [hl, canonical1107 B hB] at h
  have hc0 : mixedMoment B raw1107 (Fin.cases (0 : Fin 2) singletonSmall4324) =
      mixedMoment B node902 node902Labels := by
    have ha : raw1107 = raw1108 := by apply Matrix.ext; unfold raw1107 raw1108; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4324 = raw1108Labels := by decide +kernel
    rw [ha, hj, canonical1108 B hB]
  have hc1 : mixedMoment B raw1107 (Fin.cases (1 : Fin 2) singletonSmall4324) =
      mixedMoment B node1590 node1590Labels := by
    have ha : raw1107 = raw1109 := by apply Matrix.ext; unfold raw1107 raw1109; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4324 = raw1109Labels := by decide +kernel
    rw [ha, hj, canonical1109 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4338 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4338 node4338Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node916 node916Labels + mixedMoment B node1633 node1633Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1116 singletonSmall4338
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4338) = raw1116Labels := by decide +kernel
  rw [hl, canonical1116 B hB] at h
  have hc0 : mixedMoment B raw1116 (Fin.cases (0 : Fin 2) singletonSmall4338) =
      mixedMoment B node916 node916Labels := by
    have ha : raw1116 = raw1117 := by apply Matrix.ext; unfold raw1116 raw1117; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4338 = raw1117Labels := by decide +kernel
    rw [ha, hj, canonical1117 B hB]
  have hc1 : mixedMoment B raw1116 (Fin.cases (1 : Fin 2) singletonSmall4338) =
      mixedMoment B node1633 node1633Labels := by
    have ha : raw1116 = raw1118 := by apply Matrix.ext; unfold raw1116 raw1118; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4338 = raw1118Labels := by decide +kernel
    rw [ha, hj, canonical1118 B hB]
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

theorem singleton4398 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4398 node4398Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node979 node979Labels + mixedMoment B node1599 node1599Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1209 singletonSmall4398
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4398) = raw1209Labels := by decide +kernel
  rw [hl, canonical1209 B hB] at h
  have hc0 : mixedMoment B raw1209 (Fin.cases (0 : Fin 2) singletonSmall4398) =
      mixedMoment B node979 node979Labels := by
    have ha : raw1209 = raw1210 := by apply Matrix.ext; unfold raw1209 raw1210; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4398 = raw1210Labels := by decide +kernel
    rw [ha, hj, canonical1210 B hB]
  have hc1 : mixedMoment B raw1209 (Fin.cases (1 : Fin 2) singletonSmall4398) =
      mixedMoment B node1599 node1599Labels := by
    have ha : raw1209 = raw1211 := by apply Matrix.ext; unfold raw1209 raw1211; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4398 = raw1211Labels := by decide +kernel
    rw [ha, hj, canonical1211 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4405 node4405Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node986 node986Labels + mixedMoment B node1620 node1620Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1221 singletonSmall4405
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4405) = raw1221Labels := by decide +kernel
  rw [hl, canonical1221 B hB] at h
  have hc0 : mixedMoment B raw1221 (Fin.cases (0 : Fin 2) singletonSmall4405) =
      mixedMoment B node986 node986Labels := by
    have ha : raw1221 = raw1222 := by apply Matrix.ext; unfold raw1221 raw1222; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4405 = raw1222Labels := by decide +kernel
    rw [ha, hj, canonical1222 B hB]
  have hc1 : mixedMoment B raw1221 (Fin.cases (1 : Fin 2) singletonSmall4405) =
      mixedMoment B node1620 node1620Labels := by
    have ha : raw1221 = raw1223 := by apply Matrix.ext; unfold raw1221 raw1223; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4405 = raw1223Labels := by decide +kernel
    rw [ha, hj, canonical1223 B hB]
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

theorem singleton4418 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4418 node4418Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node999 node999Labels + mixedMoment B node1602 node1602Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1227 singletonSmall4418
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4418) = raw1227Labels := by decide +kernel
  rw [hl, canonical1227 B hB] at h
  have hc0 : mixedMoment B raw1227 (Fin.cases (0 : Fin 2) singletonSmall4418) =
      mixedMoment B node999 node999Labels := by
    have ha : raw1227 = raw1228 := by apply Matrix.ext; unfold raw1227 raw1228; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4418 = raw1228Labels := by decide +kernel
    rw [ha, hj, canonical1228 B hB]
  have hc1 : mixedMoment B raw1227 (Fin.cases (1 : Fin 2) singletonSmall4418) =
      mixedMoment B node1602 node1602Labels := by
    have ha : raw1227 = raw1229 := by apply Matrix.ext; unfold raw1227 raw1229; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4418 = raw1229Labels := by decide +kernel
    rw [ha, hj, canonical1229 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4431 node4431Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1012 node1012Labels + mixedMoment B node1627 node1627Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1242 singletonSmall4431
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4431) = raw1242Labels := by decide +kernel
  rw [hl, canonical1242 B hB] at h
  have hc0 : mixedMoment B raw1242 (Fin.cases (0 : Fin 2) singletonSmall4431) =
      mixedMoment B node1012 node1012Labels := by
    have ha : raw1242 = raw1243 := by apply Matrix.ext; unfold raw1242 raw1243; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4431 = raw1243Labels := by decide +kernel
    rw [ha, hj, canonical1243 B hB]
  have hc1 : mixedMoment B raw1242 (Fin.cases (1 : Fin 2) singletonSmall4431) =
      mixedMoment B node1627 node1627Labels := by
    have ha : raw1242 = raw1244 := by apply Matrix.ext; unfold raw1242 raw1244; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4431 = raw1244Labels := by decide +kernel
    rw [ha, hj, canonical1244 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4454 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4454 node4454Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1037 node1037Labels + mixedMoment B node1647 node1647Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1251 singletonSmall4454
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4454) = raw1251Labels := by decide +kernel
  rw [hl, canonical1251 B hB] at h
  have hc0 : mixedMoment B raw1251 (Fin.cases (0 : Fin 2) singletonSmall4454) =
      mixedMoment B node1037 node1037Labels := by
    have ha : raw1251 = raw1252 := by apply Matrix.ext; unfold raw1251 raw1252; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4454 = raw1252Labels := by decide +kernel
    rw [ha, hj, canonical1252 B hB]
  have hc1 : mixedMoment B raw1251 (Fin.cases (1 : Fin 2) singletonSmall4454) =
      mixedMoment B node1647 node1647Labels := by
    have ha : raw1251 = raw1253 := by apply Matrix.ext; unfold raw1251 raw1253; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4454 = raw1253Labels := by decide +kernel
    rw [ha, hj, canonical1253 B hB]
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

theorem singleton4490 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4490 node4490Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1074 node1074Labels + mixedMoment B node1650 node1650Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1284 singletonSmall4490
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4490) = raw1284Labels := by decide +kernel
  rw [hl, canonical1284 B hB] at h
  have hc0 : mixedMoment B raw1284 (Fin.cases (0 : Fin 2) singletonSmall4490) =
      mixedMoment B node1074 node1074Labels := by
    have ha : raw1284 = raw1285 := by apply Matrix.ext; unfold raw1284 raw1285; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4490 = raw1285Labels := by decide +kernel
    rw [ha, hj, canonical1285 B hB]
  have hc1 : mixedMoment B raw1284 (Fin.cases (1 : Fin 2) singletonSmall4490) =
      mixedMoment B node1650 node1650Labels := by
    have ha : raw1284 = raw1286 := by apply Matrix.ext; unfold raw1284 raw1286; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4490 = raw1286Labels := by decide +kernel
    rw [ha, hj, canonical1286 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

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

theorem sound706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node706 node706Labels = Sparse.eval nodeValue706 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 706) = mixedMoment B node706 node706Labels := rfl
  simpa [nodeValue706, Sparse.eval] using hc.symm

theorem sound715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node715 node715Labels = Sparse.eval nodeValue715 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 715) = mixedMoment B node715 node715Labels := rfl
  simpa [nodeValue715, Sparse.eval] using hc.symm

theorem sound741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node741 node741Labels = Sparse.eval nodeValue741 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 741) = mixedMoment B node741 node741Labels := rfl
  simpa [nodeValue741, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero809 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node809 node809Labels = 0 := by
  exact mixedMoment_order_one B hB node809 node809Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node793 node793Labels = Sparse.eval nodeValue793 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 793) = mixedMoment B node793 node793Labels := rfl
  simpa [nodeValue793, Sparse.eval] using hc.symm

theorem sound795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node795 node795Labels = Sparse.eval nodeValue795 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 795) = mixedMoment B node795 node795Labels := rfl
  simpa [nodeValue795, Sparse.eval] using hc.symm

theorem sound796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node796 node796Labels = Sparse.eval nodeValue796 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 796) = mixedMoment B node796 node796Labels := rfl
  simpa [nodeValue796, Sparse.eval] using hc.symm

theorem sound809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node809 node809Labels = Sparse.eval nodeValue809 (mixedVector B) := by
  simpa only [nodeValue809, Sparse.eval_nil] using zero809 B _hB _hF

theorem sound811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node811 node811Labels = Sparse.eval nodeValue811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 811) = mixedMoment B node811 node811Labels := rfl
  simpa [nodeValue811, Sparse.eval] using hc.symm

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

theorem sound824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node824 node824Labels = Sparse.eval nodeValue824 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 824) = mixedMoment B node824 node824Labels := rfl
  simpa [nodeValue824, Sparse.eval] using hc.symm

theorem sound825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node825 node825Labels = Sparse.eval nodeValue825 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 825) = mixedMoment B node825 node825Labels := rfl
  simpa [nodeValue825, Sparse.eval] using hc.symm

theorem sound826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node826 node826Labels = Sparse.eval nodeValue826 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 826) = mixedMoment B node826 node826Labels := rfl
  simpa [nodeValue826, Sparse.eval] using hc.symm

theorem sound827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node827 node827Labels = Sparse.eval nodeValue827 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 827) = mixedMoment B node827 node827Labels := rfl
  simpa [nodeValue827, Sparse.eval] using hc.symm

theorem sound828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node828 node828Labels = Sparse.eval nodeValue828 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 828) = mixedMoment B node828 node828Labels := rfl
  simpa [nodeValue828, Sparse.eval] using hc.symm

theorem sound829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node829 node829Labels = Sparse.eval nodeValue829 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 829) = mixedMoment B node829 node829Labels := rfl
  simpa [nodeValue829, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero852 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node852 node852Labels = 0 := by
  exact mixedMoment_order_one B hB node852 node852Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero856 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node856 node856Labels = 0 := by
  exact mixedMoment_order_one B hB node856 node856Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero859 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node859 node859Labels = 0 := by
  exact mixedMoment_order_one B hB node859 node859Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node852 node852Labels = Sparse.eval nodeValue852 (mixedVector B) := by
  simpa only [nodeValue852, Sparse.eval_nil] using zero852 B _hB _hF

theorem sound856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node856 node856Labels = Sparse.eval nodeValue856 (mixedVector B) := by
  simpa only [nodeValue856, Sparse.eval_nil] using zero856 B _hB _hF

theorem sound858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node858 node858Labels = Sparse.eval nodeValue858 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 858) = mixedMoment B node858 node858Labels := rfl
  simpa [nodeValue858, Sparse.eval] using hc.symm

theorem sound859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node859 node859Labels = Sparse.eval nodeValue859 (mixedVector B) := by
  simpa only [nodeValue859, Sparse.eval_nil] using zero859 B _hB _hF

theorem sound867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node867 node867Labels = Sparse.eval nodeValue867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 867) = mixedMoment B node867 node867Labels := rfl
  simpa [nodeValue867, Sparse.eval] using hc.symm

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

theorem sound898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node898 node898Labels = Sparse.eval nodeValue898 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 898) = mixedMoment B node898 node898Labels := rfl
  simpa [nodeValue898, Sparse.eval] using hc.symm

theorem sound902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node902 node902Labels = Sparse.eval nodeValue902 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 902) = mixedMoment B node902 node902Labels := rfl
  simpa [nodeValue902, Sparse.eval] using hc.symm

theorem sound916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node916 node916Labels = Sparse.eval nodeValue916 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 916) = mixedMoment B node916 node916Labels := rfl
  simpa [nodeValue916, Sparse.eval] using hc.symm

theorem sound921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node921 node921Labels = Sparse.eval nodeValue921 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 921) = mixedMoment B node921 node921Labels := rfl
  simpa [nodeValue921, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1007 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1007 node1007Labels = 0 := by
  exact mixedMoment_order_one B hB node1007 node1007Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1013 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1013 node1013Labels = 0 := by
  exact mixedMoment_order_one B hB node1013 node1013Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node979 node979Labels = Sparse.eval nodeValue979 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 979) = mixedMoment B node979 node979Labels := rfl
  simpa [nodeValue979, Sparse.eval] using hc.symm

theorem sound986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node986 node986Labels = Sparse.eval nodeValue986 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 986) = mixedMoment B node986 node986Labels := rfl
  simpa [nodeValue986, Sparse.eval] using hc.symm

theorem sound999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node999 node999Labels = Sparse.eval nodeValue999 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 999) = mixedMoment B node999 node999Labels := rfl
  simpa [nodeValue999, Sparse.eval] using hc.symm

theorem sound1000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1000 node1000Labels = Sparse.eval nodeValue1000 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1000) = mixedMoment B node1000 node1000Labels := rfl
  simpa [nodeValue1000, Sparse.eval] using hc.symm

theorem sound1001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1001 node1001Labels = Sparse.eval nodeValue1001 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1001) = mixedMoment B node1001 node1001Labels := rfl
  simpa [nodeValue1001, Sparse.eval] using hc.symm

theorem sound1007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1007 node1007Labels = Sparse.eval nodeValue1007 (mixedVector B) := by
  simpa only [nodeValue1007, Sparse.eval_nil] using zero1007 B _hB _hF

theorem sound1009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1009 node1009Labels = Sparse.eval nodeValue1009 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1009) = mixedMoment B node1009 node1009Labels := rfl
  simpa [nodeValue1009, Sparse.eval] using hc.symm

theorem sound1010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1010 node1010Labels = Sparse.eval nodeValue1010 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1010) = mixedMoment B node1010 node1010Labels := rfl
  simpa [nodeValue1010, Sparse.eval] using hc.symm

theorem sound1012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1012 node1012Labels = Sparse.eval nodeValue1012 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1012) = mixedMoment B node1012 node1012Labels := rfl
  simpa [nodeValue1012, Sparse.eval] using hc.symm

theorem sound1013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1013 node1013Labels = Sparse.eval nodeValue1013 (mixedVector B) := by
  simpa only [nodeValue1013, Sparse.eval_nil] using zero1013 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1085 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1085 node1085Labels = 0 := by
  exact mixedMoment_order_one B hB node1085 node1085Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1037 node1037Labels = Sparse.eval nodeValue1037 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1037) = mixedMoment B node1037 node1037Labels := rfl
  simpa [nodeValue1037, Sparse.eval] using hc.symm

theorem sound1074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1074 node1074Labels = Sparse.eval nodeValue1074 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1074) = mixedMoment B node1074 node1074Labels := rfl
  simpa [nodeValue1074, Sparse.eval] using hc.symm

theorem sound1075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1075 node1075Labels = Sparse.eval nodeValue1075 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1075) = mixedMoment B node1075 node1075Labels := rfl
  simpa [nodeValue1075, Sparse.eval] using hc.symm

theorem sound1076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1076 node1076Labels = Sparse.eval nodeValue1076 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1076) = mixedMoment B node1076 node1076Labels := rfl
  simpa [nodeValue1076, Sparse.eval] using hc.symm

theorem sound1080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1080 node1080Labels = Sparse.eval nodeValue1080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1080) = mixedMoment B node1080 node1080Labels := rfl
  simpa [nodeValue1080, Sparse.eval] using hc.symm

theorem sound1085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1085 node1085Labels = Sparse.eval nodeValue1085 (mixedVector B) := by
  simpa only [nodeValue1085, Sparse.eval_nil] using zero1085 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1489 node1489Labels = Sparse.eval nodeValue1489 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1489) = mixedMoment B node1489 node1489Labels := rfl
  simpa [nodeValue1489, Sparse.eval] using hc.symm

theorem sound1494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1494 node1494Labels = Sparse.eval nodeValue1494 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1494) = mixedMoment B node1494 node1494Labels := rfl
  simpa [nodeValue1494, Sparse.eval] using hc.symm

theorem sound1495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1495 node1495Labels = Sparse.eval nodeValue1495 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1495) = mixedMoment B node1495 node1495Labels := rfl
  simpa [nodeValue1495, Sparse.eval] using hc.symm

theorem sound1499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1499 node1499Labels = Sparse.eval nodeValue1499 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1499) = mixedMoment B node1499 node1499Labels := rfl
  simpa [nodeValue1499, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1557 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1557 node1557Labels = 0 := by
  exact mixedMoment_order_one B hB node1557 node1557Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1574 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1574 node1574Labels = 0 := by
  exact mixedMoment_order_one B hB node1574 node1574Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero1576 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1576 node1576Labels = 0 := by
  exact mixedMoment_order_one B hB node1576 node1576Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1555 node1555Labels = Sparse.eval nodeValue1555 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1555) = mixedMoment B node1555 node1555Labels := rfl
  simpa [nodeValue1555, Sparse.eval] using hc.symm

theorem sound1557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1557 node1557Labels = Sparse.eval nodeValue1557 (mixedVector B) := by
  simpa only [nodeValue1557, Sparse.eval_nil] using zero1557 B _hB _hF

theorem sound1574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1574 node1574Labels = Sparse.eval nodeValue1574 (mixedVector B) := by
  simpa only [nodeValue1574, Sparse.eval_nil] using zero1574 B _hB _hF

theorem sound1576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1576 node1576Labels = Sparse.eval nodeValue1576 (mixedVector B) := by
  simpa only [nodeValue1576, Sparse.eval_nil] using zero1576 B _hB _hF

theorem sound1586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1586 node1586Labels = Sparse.eval nodeValue1586 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1586) = mixedMoment B node1586 node1586Labels := rfl
  simpa [nodeValue1586, Sparse.eval] using hc.symm

theorem sound1590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1590 node1590Labels = Sparse.eval nodeValue1590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1590) = mixedMoment B node1590 node1590Labels := rfl
  simpa [nodeValue1590, Sparse.eval] using hc.symm

theorem sound1599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1599 node1599Labels = Sparse.eval nodeValue1599 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1599) = mixedMoment B node1599 node1599Labels := rfl
  simpa [nodeValue1599, Sparse.eval] using hc.symm

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

theorem sound1602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1602 node1602Labels = Sparse.eval nodeValue1602 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1602) = mixedMoment B node1602 node1602Labels := rfl
  simpa [nodeValue1602, Sparse.eval] using hc.symm

theorem sound1608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1608 node1608Labels = Sparse.eval nodeValue1608 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1608) = mixedMoment B node1608 node1608Labels := rfl
  simpa [nodeValue1608, Sparse.eval] using hc.symm

theorem sound1610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1610 node1610Labels = Sparse.eval nodeValue1610 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1610) = mixedMoment B node1610 node1610Labels := rfl
  simpa [nodeValue1610, Sparse.eval] using hc.symm

theorem sound1620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1620 node1620Labels = Sparse.eval nodeValue1620 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1620) = mixedMoment B node1620 node1620Labels := rfl
  simpa [nodeValue1620, Sparse.eval] using hc.symm

theorem sound1627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1627 node1627Labels = Sparse.eval nodeValue1627 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1627) = mixedMoment B node1627 node1627Labels := rfl
  simpa [nodeValue1627, Sparse.eval] using hc.symm

theorem sound1633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1633 node1633Labels = Sparse.eval nodeValue1633 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1633) = mixedMoment B node1633 node1633Labels := rfl
  simpa [nodeValue1633, Sparse.eval] using hc.symm

theorem sound1647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1647 node1647Labels = Sparse.eval nodeValue1647 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1647) = mixedMoment B node1647 node1647Labels := rfl
  simpa [nodeValue1647, Sparse.eval] using hc.symm

theorem sound1650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1650 node1650Labels = Sparse.eval nodeValue1650 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1650) = mixedMoment B node1650 node1650Labels := rfl
  simpa [nodeValue1650, Sparse.eval] using hc.symm

theorem sound1657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1657 node1657Labels = Sparse.eval nodeValue1657 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1657) = mixedMoment B node1657 node1657Labels := rfl
  simpa [nodeValue1657, Sparse.eval] using hc.symm

theorem sound1659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1659 node1659Labels = Sparse.eval nodeValue1659 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1659) = mixedMoment B node1659 node1659Labels := rfl
  simpa [nodeValue1659, Sparse.eval] using hc.symm

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

theorem sound1715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1715 node1715Labels = Sparse.eval nodeValue1715 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1715) = mixedMoment B node1715 node1715Labels := rfl
  simpa [nodeValue1715, Sparse.eval] using hc.symm

theorem sound1716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1716 node1716Labels = Sparse.eval nodeValue1716 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1716) = mixedMoment B node1716 node1716Labels := rfl
  simpa [nodeValue1716, Sparse.eval] using hc.symm

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

theorem sound1739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1739 node1739Labels = Sparse.eval nodeValue1739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1739) = mixedMoment B node1739 node1739Labels := rfl
  simpa [nodeValue1739, Sparse.eval] using hc.symm

theorem sound1740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1740 node1740Labels = Sparse.eval nodeValue1740 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1740) = mixedMoment B node1740 node1740Labels := rfl
  simpa [nodeValue1740, Sparse.eval] using hc.symm

theorem sound1741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1741 node1741Labels = Sparse.eval nodeValue1741 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1741) = mixedMoment B node1741 node1741Labels := rfl
  simpa [nodeValue1741, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1911 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1911 node1911Labels = 0 := by
  exact mixedMoment_order_one B hB node1911 node1911Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1911 node1911Labels = Sparse.eval nodeValue1911 (mixedVector B) := by
  simpa only [nodeValue1911, Sparse.eval_nil] using zero1911 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1950 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1950 node1950Labels = 0 := by
  exact mixedMoment_order_one B hB node1950 node1950Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound1950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1950 node1950Labels = Sparse.eval nodeValue1950 (mixedVector B) := by
  simpa only [nodeValue1950, Sparse.eval_nil] using zero1950 B _hB _hF

theorem sound1951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1951 node1951Labels = Sparse.eval nodeValue1951 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1951) = mixedMoment B node1951 node1951Labels := rfl
  simpa [nodeValue1951, Sparse.eval] using hc.symm

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

theorem sound2003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2003 node2003Labels = Sparse.eval nodeValue2003 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2003) = mixedMoment B node2003 node2003Labels := rfl
  simpa [nodeValue2003, Sparse.eval] using hc.symm

theorem sound2004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2004 node2004Labels = Sparse.eval nodeValue2004 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2004) = mixedMoment B node2004 node2004Labels := rfl
  simpa [nodeValue2004, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2056 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2056 node2056Labels = 0 := by
  exact mixedMoment_order_one B hB node2056 node2056Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2060 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2060 node2060Labels = 0 := by
  exact mixedMoment_order_one B hB node2060 node2060Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2056 node2056Labels = Sparse.eval nodeValue2056 (mixedVector B) := by
  simpa only [nodeValue2056, Sparse.eval_nil] using zero2056 B _hB _hF

theorem sound2060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2060 node2060Labels = Sparse.eval nodeValue2060 (mixedVector B) := by
  simpa only [nodeValue2060, Sparse.eval_nil] using zero2060 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2229 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2229 node2229Labels = 0 := by
  exact mixedMoment_order_one B hB node2229 node2229Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound2218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2218 node2218Labels = Sparse.eval nodeValue2218 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2218) = mixedMoment B node2218 node2218Labels := rfl
  simpa [nodeValue2218, Sparse.eval] using hc.symm

theorem sound2222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2222 node2222Labels = Sparse.eval nodeValue2222 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2222) = mixedMoment B node2222 node2222Labels := rfl
  simpa [nodeValue2222, Sparse.eval] using hc.symm

theorem sound2229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2229 node2229Labels = Sparse.eval nodeValue2229 (mixedVector B) := by
  simpa only [nodeValue2229, Sparse.eval_nil] using zero2229 B _hB _hF

theorem sound2230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2230 node2230Labels = Sparse.eval nodeValue2230 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2230) = mixedMoment B node2230 node2230Labels := rfl
  simpa [nodeValue2230, Sparse.eval] using hc.symm

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

theorem sound546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node546 node546Labels = Sparse.eval nodeValue546 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 546) = mixedMoment B node546 node546Labels := rfl
  simpa [nodeValue546, Sparse.eval] using hc.symm

theorem sound555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node555 node555Labels = Sparse.eval nodeValue555 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 555) = mixedMoment B node555 node555Labels := rfl
  simpa [nodeValue555, Sparse.eval] using hc.symm

theorem sound568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node568 node568Labels = Sparse.eval nodeValue568 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 568) = mixedMoment B node568 node568Labels := rfl
  simpa [nodeValue568, Sparse.eval] using hc.symm

theorem sound574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node574 node574Labels = Sparse.eval nodeValue574 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 574) = mixedMoment B node574 node574Labels := rfl
  simpa [nodeValue574, Sparse.eval] using hc.symm

theorem sound575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node575 node575Labels = Sparse.eval nodeValue575 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 575) = mixedMoment B node575 node575Labels := rfl
  simpa [nodeValue575, Sparse.eval] using hc.symm

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

theorem sound4069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4069 node4069Labels = Sparse.eval nodeValue4069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4069) = mixedMoment B node4069 node4069Labels := rfl
  simpa [nodeValue4069, Sparse.eval] using hc.symm

theorem sound4070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4070 node4070Labels = Sparse.eval nodeValue4070 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4070) = mixedMoment B node4070 node4070Labels := rfl
  simpa [nodeValue4070, Sparse.eval] using hc.symm

theorem sound4071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4071 node4071Labels = Sparse.eval nodeValue4071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4071) = mixedMoment B node4071 node4071Labels := rfl
  simpa [nodeValue4071, Sparse.eval] using hc.symm

theorem sound4081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4081 node4081Labels = Sparse.eval nodeValue4081 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4081) = mixedMoment B node4081 node4081Labels := rfl
  simpa [nodeValue4081, Sparse.eval] using hc.symm

theorem sound4082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4082 node4082Labels = Sparse.eval nodeValue4082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4082) = mixedMoment B node4082 node4082Labels := rfl
  simpa [nodeValue4082, Sparse.eval] using hc.symm

theorem sound4085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4085 node4085Labels = Sparse.eval nodeValue4085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4085) = mixedMoment B node4085 node4085Labels := rfl
  simpa [nodeValue4085, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node594 node594Labels = Sparse.eval nodeValue594 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 594) = mixedMoment B node594 node594Labels := rfl
  simpa [nodeValue594, Sparse.eval] using hc.symm

theorem sound602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node602 node602Labels = Sparse.eval nodeValue602 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 602) = mixedMoment B node602 node602Labels := rfl
  simpa [nodeValue602, Sparse.eval] using hc.symm

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

theorem sound4140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4140 node4140Labels = Sparse.eval nodeValue4140 (mixedVector B) := by
  have h := singleton4140 B _hB
  rw [sound568 B _hB _hF, sound1489 B _hB _hF] at h
  norm_num [nodeValue4140, nodeValue568, nodeValue1489, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4146 node4146Labels = Sparse.eval nodeValue4146 (mixedVector B) := by
  have h := singleton4146 B _hB
  rw [sound574 B _hB _hF, sound1494 B _hB _hF] at h
  norm_num [nodeValue4146, nodeValue574, nodeValue1494, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4147 node4147Labels = Sparse.eval nodeValue4147 (mixedVector B) := by
  have h := singleton4147 B _hB
  rw [sound575 B _hB _hF, sound1495 B _hB _hF] at h
  norm_num [nodeValue4147, nodeValue575, nodeValue1495, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4166 node4166Labels = Sparse.eval nodeValue4166 (mixedVector B) := by
  have h := singleton4166 B _hB
  rw [sound594 B _hB _hF, sound1499 B _hB _hF] at h
  norm_num [nodeValue4166, nodeValue594, nodeValue1499, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4302 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4302 node4302Labels = 0 := by
  exact mixedMoment_order_one B hB node4302 node4302Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4312 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4312 node4312Labels = 0 := by
  exact mixedMoment_order_one B hB node4312 node4312Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4317 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4317 node4317Labels = 0 := by
  exact mixedMoment_order_one B hB node4317 node4317Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4289 node4289Labels = Sparse.eval nodeValue4289 (mixedVector B) := by
  have h := singleton4289 B _hB
  rw [sound867 B _hB _hF, sound1555 B _hB _hF] at h
  norm_num [nodeValue4289, nodeValue867, nodeValue1555, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4302 node4302Labels = Sparse.eval nodeValue4302 (mixedVector B) := by
  simpa only [nodeValue4302, Sparse.eval_nil] using zero4302 B _hB _hF

theorem sound4312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4312 node4312Labels = Sparse.eval nodeValue4312 (mixedVector B) := by
  simpa only [nodeValue4312, Sparse.eval_nil] using zero4312 B _hB _hF

theorem sound4317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4317 node4317Labels = Sparse.eval nodeValue4317 (mixedVector B) := by
  simpa only [nodeValue4317, Sparse.eval_nil] using zero4317 B _hB _hF

theorem sound4320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4320 node4320Labels = Sparse.eval nodeValue4320 (mixedVector B) := by
  have h := singleton4320 B _hB
  rw [sound898 B _hB _hF, sound1586 B _hB _hF] at h
  norm_num [nodeValue4320, nodeValue898, nodeValue1586, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4324 node4324Labels = Sparse.eval nodeValue4324 (mixedVector B) := by
  have h := singleton4324 B _hB
  rw [sound902 B _hB _hF, sound1590 B _hB _hF] at h
  norm_num [nodeValue4324, nodeValue902, nodeValue1590, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4338 node4338Labels = Sparse.eval nodeValue4338 (mixedVector B) := by
  have h := singleton4338 B _hB
  rw [sound916 B _hB _hF, sound1633 B _hB _hF] at h
  norm_num [nodeValue4338, nodeValue916, nodeValue1633, Sparse.eval] at h ⊢
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

theorem sound4398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4398 node4398Labels = Sparse.eval nodeValue4398 (mixedVector B) := by
  have h := singleton4398 B _hB
  rw [sound979 B _hB _hF, sound1599 B _hB _hF] at h
  norm_num [nodeValue4398, nodeValue979, nodeValue1599, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4405 node4405Labels = Sparse.eval nodeValue4405 (mixedVector B) := by
  have h := singleton4405 B _hB
  rw [sound986 B _hB _hF, sound1620 B _hB _hF] at h
  norm_num [nodeValue4405, nodeValue986, nodeValue1620, Sparse.eval] at h ⊢
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

theorem sound4418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4418 node4418Labels = Sparse.eval nodeValue4418 (mixedVector B) := by
  have h := singleton4418 B _hB
  rw [sound999 B _hB _hF, sound1602 B _hB _hF] at h
  norm_num [nodeValue4418, nodeValue999, nodeValue1602, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4431 node4431Labels = Sparse.eval nodeValue4431 (mixedVector B) := by
  have h := singleton4431 B _hB
  rw [sound1012 B _hB _hF, sound1627 B _hB _hF] at h
  norm_num [nodeValue4431, nodeValue1012, nodeValue1627, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4454 node4454Labels = Sparse.eval nodeValue4454 (mixedVector B) := by
  have h := singleton4454 B _hB
  rw [sound1037 B _hB _hF, sound1647 B _hB _hF] at h
  norm_num [nodeValue4454, nodeValue1037, nodeValue1647, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4490 node4490Labels = Sparse.eval nodeValue4490 (mixedVector B) := by
  have h := singleton4490 B _hB
  rw [sound1074 B _hB _hF, sound1650 B _hB _hF] at h
  norm_num [nodeValue4490, nodeValue1074, nodeValue1650, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero4738 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4738 node4738Labels = 0 := by
  exact mixedMoment_order_one B hB node4738 node4738Labels 1
    (by decide +kernel) (by decide +kernel)

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

theorem sound4738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4738 node4738Labels = Sparse.eval nodeValue4738 (mixedVector B) := by
  simpa only [nodeValue4738, Sparse.eval_nil] using zero4738 B _hB _hF

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

theorem zero4837 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4837 node4837Labels = 0 := by
  exact mixedMoment_order_one B hB node4837 node4837Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero4841 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4841 node4841Labels = 0 := by
  exact mixedMoment_order_one B hB node4841 node4841Labels 1
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

theorem sound4837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4837 node4837Labels = Sparse.eval nodeValue4837 (mixedVector B) := by
  simpa only [nodeValue4837, Sparse.eval_nil] using zero4837 B _hB _hF

theorem sound4841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4841 node4841Labels = Sparse.eval nodeValue4841 (mixedVector B) := by
  simpa only [nodeValue4841, Sparse.eval_nil] using zero4841 B _hB _hF

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources43
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1390 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1390 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1390 + difference 1 0) (sourceB1390 + difference 0 1) sourceC1390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 602) := by
    have ha : (tripleCharges (sourceA1390 + difference 1 0) (sourceB1390 + difference 0 1) sourceC1390) = raw21876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1390 sourceB1390 sourceC1390 difference raw21876; decide +kernel
    rw [ha]
    exact (canonical21876 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1390 + difference 1 1) (sourceB1390 + difference 1 1) sourceC1390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1085) := by
    have ha : (tripleCharges (sourceA1390 + difference 1 1) (sourceB1390 + difference 1 1) sourceC1390) = raw21875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1390 sourceB1390 sourceC1390 difference raw21875; decide +kernel
    rw [ha]
    exact (canonical21875 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1390 + difference 1 2) (sourceB1390 + difference 2 1) sourceC1390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 921) := by
    have ha : (tripleCharges (sourceA1390 + difference 1 2) (sourceB1390 + difference 2 1) sourceC1390) = raw21880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1390 sourceB1390 sourceC1390 difference raw21880; decide +kernel
    rw [ha]
    exact (canonical21880 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1390 + difference 1 3) (sourceB1390 + difference 3 1) sourceC1390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 921) := by
    have ha : (tripleCharges (sourceA1390 + difference 1 3) (sourceB1390 + difference 3 1) sourceC1390) = raw21881 := by
      apply Matrix.ext; unfold tripleCharges sourceA1390 sourceB1390 sourceC1390 difference raw21881; decide +kernel
    rw [ha]
    exact (canonical21881 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1390 + difference 1 4) (sourceB1390 + difference 4 1) sourceC1390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1085) := by
    have ha : (tripleCharges (sourceA1390 + difference 1 4) (sourceB1390 + difference 4 1) sourceC1390) = raw21882 := by
      apply Matrix.ext; unfold tripleCharges sourceA1390 sourceB1390 sourceC1390 difference raw21882; decide +kernel
    rw [ha]
    exact (canonical21882 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1390 + difference 1 5) (sourceB1390 + difference 5 1) sourceC1390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1080) := by
    have ha : (tripleCharges (sourceA1390 + difference 1 5) (sourceB1390 + difference 5 1) sourceC1390) = raw21883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1390 sourceB1390 sourceC1390 difference raw21883; decide +kernel
    rw [ha]
    exact (canonical21883 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1390 + sourceB1390) sourceC1390) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA1390 + sourceB1390) sourceC1390) = raw19953 := by
      apply Matrix.ext; unfold doubleCharges sourceA1390 sourceB1390 sourceC1390 raw19953; decide +kernel
    rw [ha]
    exact (canonical19953 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1390 sourceB1390 sourceC1390
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1390, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1391 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1391 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1391 + difference 0 0) (sourceB1391 + difference 0 0) sourceC1391) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1010) := by
    have ha : (tripleCharges (sourceA1391 + difference 0 0) (sourceB1391 + difference 0 0) sourceC1391) = raw21884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1391 sourceB1391 sourceC1391 difference raw21884; decide +kernel
    rw [ha]
    exact (canonical21884 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1391 + difference 0 1) (sourceB1391 + difference 1 0) sourceC1391) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2004) := by
    have ha : (tripleCharges (sourceA1391 + difference 0 1) (sourceB1391 + difference 1 0) sourceC1391) = raw21885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1391 sourceB1391 sourceC1391 difference raw21885; decide +kernel
    rw [ha]
    exact (canonical21885 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1391 + difference 0 2) (sourceB1391 + difference 2 0) sourceC1391) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2004) := by
    have ha : (tripleCharges (sourceA1391 + difference 0 2) (sourceB1391 + difference 2 0) sourceC1391) = raw21886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1391 sourceB1391 sourceC1391 difference raw21886; decide +kernel
    rw [ha]
    exact (canonical21886 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1391 + difference 0 3) (sourceB1391 + difference 3 0) sourceC1391) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1951) := by
    have ha : (tripleCharges (sourceA1391 + difference 0 3) (sourceB1391 + difference 3 0) sourceC1391) = raw21887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1391 sourceB1391 sourceC1391 difference raw21887; decide +kernel
    rw [ha]
    exact (canonical21887 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1391 + difference 0 4) (sourceB1391 + difference 4 0) sourceC1391) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2222) := by
    have ha : (tripleCharges (sourceA1391 + difference 0 4) (sourceB1391 + difference 4 0) sourceC1391) = raw21888 := by
      apply Matrix.ext; unfold tripleCharges sourceA1391 sourceB1391 sourceC1391 difference raw21888; decide +kernel
    rw [ha]
    exact (canonical21888 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1391 + difference 0 5) (sourceB1391 + difference 5 0) sourceC1391) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA1391 + difference 0 5) (sourceB1391 + difference 5 0) sourceC1391) = raw21889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1391 sourceB1391 sourceC1391 difference raw21889; decide +kernel
    rw [ha]
    exact (canonical21889 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1391 + sourceB1391) sourceC1391) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1391 + sourceB1391) sourceC1391) = raw21890 := by
      apply Matrix.ext; unfold doubleCharges sourceA1391 sourceB1391 sourceC1391 raw21890; decide +kernel
    rw [ha]
    exact (canonical21890 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1391 sourceB1391 sourceC1391
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1391, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1392 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1392 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1392 + difference 0 5) (sourceB1392 + difference 5 0) sourceC1392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA1392 + difference 0 5) (sourceB1392 + difference 5 0) sourceC1392) = raw21889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1392 sourceB1392 sourceC1392 difference raw21889; decide +kernel
    rw [ha]
    exact (canonical21889 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1392 + difference 1 5) (sourceB1392 + difference 5 1) sourceC1392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1001) := by
    have ha : (tripleCharges (sourceA1392 + difference 1 5) (sourceB1392 + difference 5 1) sourceC1392) = raw21891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1392 sourceB1392 sourceC1392 difference raw21891; decide +kernel
    rw [ha]
    exact (canonical21891 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1392 + difference 2 5) (sourceB1392 + difference 5 2) sourceC1392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1001) := by
    have ha : (tripleCharges (sourceA1392 + difference 2 5) (sourceB1392 + difference 5 2) sourceC1392) = raw21892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1392 sourceB1392 sourceC1392 difference raw21892; decide +kernel
    rw [ha]
    exact (canonical21892 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1392 + difference 3 5) (sourceB1392 + difference 5 3) sourceC1392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1076) := by
    have ha : (tripleCharges (sourceA1392 + difference 3 5) (sourceB1392 + difference 5 3) sourceC1392) = raw21893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1392 sourceB1392 sourceC1392 difference raw21893; decide +kernel
    rw [ha]
    exact (canonical21893 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1392 + difference 4 5) (sourceB1392 + difference 5 4) sourceC1392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1012) := by
    have ha : (tripleCharges (sourceA1392 + difference 4 5) (sourceB1392 + difference 5 4) sourceC1392) = raw21894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1392 sourceB1392 sourceC1392 difference raw21894; decide +kernel
    rw [ha]
    exact (canonical21894 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1392 + difference 5 5) (sourceB1392 + difference 5 5) sourceC1392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1010) := by
    have ha : (tripleCharges (sourceA1392 + difference 5 5) (sourceB1392 + difference 5 5) sourceC1392) = raw21884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1392 sourceB1392 sourceC1392 difference raw21884; decide +kernel
    rw [ha]
    exact (canonical21884 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1392 + sourceB1392) sourceC1392) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1392 + sourceB1392) sourceC1392) = raw21890 := by
      apply Matrix.ext; unfold doubleCharges sourceA1392 sourceB1392 sourceC1392 raw21890; decide +kernel
    rw [ha]
    exact (canonical21890 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1392 sourceB1392 sourceC1392
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1392, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1393 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1393 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1393 + difference 0 0) (sourceB1393 + difference 0 0) sourceC1393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1009) := by
    have ha : (tripleCharges (sourceA1393 + difference 0 0) (sourceB1393 + difference 0 0) sourceC1393) = raw21895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1393 sourceB1393 sourceC1393 difference raw21895; decide +kernel
    rw [ha]
    exact (canonical21895 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1393 + difference 0 1) (sourceB1393 + difference 1 0) sourceC1393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2003) := by
    have ha : (tripleCharges (sourceA1393 + difference 0 1) (sourceB1393 + difference 1 0) sourceC1393) = raw21896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1393 sourceB1393 sourceC1393 difference raw21896; decide +kernel
    rw [ha]
    exact (canonical21896 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1393 + difference 0 2) (sourceB1393 + difference 2 0) sourceC1393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2003) := by
    have ha : (tripleCharges (sourceA1393 + difference 0 2) (sourceB1393 + difference 2 0) sourceC1393) = raw21897 := by
      apply Matrix.ext; unfold tripleCharges sourceA1393 sourceB1393 sourceC1393 difference raw21897; decide +kernel
    rw [ha]
    exact (canonical21897 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1393 + difference 0 3) (sourceB1393 + difference 3 0) sourceC1393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1950) := by
    have ha : (tripleCharges (sourceA1393 + difference 0 3) (sourceB1393 + difference 3 0) sourceC1393) = raw21898 := by
      apply Matrix.ext; unfold tripleCharges sourceA1393 sourceB1393 sourceC1393 difference raw21898; decide +kernel
    rw [ha]
    exact (canonical21898 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1393 + difference 0 4) (sourceB1393 + difference 4 0) sourceC1393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1393 + difference 0 4) (sourceB1393 + difference 4 0) sourceC1393) = raw21899 := by
      apply Matrix.ext; unfold tripleCharges sourceA1393 sourceB1393 sourceC1393 difference raw21899; decide +kernel
    rw [ha]
    exact (canonical21899 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1393 + difference 0 5) (sourceB1393 + difference 5 0) sourceC1393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA1393 + difference 0 5) (sourceB1393 + difference 5 0) sourceC1393) = raw21900 := by
      apply Matrix.ext; unfold tripleCharges sourceA1393 sourceB1393 sourceC1393 difference raw21900; decide +kernel
    rw [ha]
    exact (canonical21900 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1393 + sourceB1393) sourceC1393) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1393 + sourceB1393) sourceC1393) = raw21901 := by
      apply Matrix.ext; unfold doubleCharges sourceA1393 sourceB1393 sourceC1393 raw21901; decide +kernel
    rw [ha]
    exact (canonical21901 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1393 sourceB1393 sourceC1393
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1393, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1396 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1396 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1396 + difference 0 5) (sourceB1396 + difference 5 0) sourceC1396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA1396 + difference 0 5) (sourceB1396 + difference 5 0) sourceC1396) = raw21900 := by
      apply Matrix.ext; unfold tripleCharges sourceA1396 sourceB1396 sourceC1396 difference raw21900; decide +kernel
    rw [ha]
    exact (canonical21900 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1396 + difference 1 5) (sourceB1396 + difference 5 1) sourceC1396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1396 + difference 1 5) (sourceB1396 + difference 5 1) sourceC1396) = raw21910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1396 sourceB1396 sourceC1396 difference raw21910; decide +kernel
    rw [ha]
    exact (canonical21910 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1396 + difference 2 5) (sourceB1396 + difference 5 2) sourceC1396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1396 + difference 2 5) (sourceB1396 + difference 5 2) sourceC1396) = raw21911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1396 sourceB1396 sourceC1396 difference raw21911; decide +kernel
    rw [ha]
    exact (canonical21911 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1396 + difference 3 5) (sourceB1396 + difference 5 3) sourceC1396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1075) := by
    have ha : (tripleCharges (sourceA1396 + difference 3 5) (sourceB1396 + difference 5 3) sourceC1396) = raw21912 := by
      apply Matrix.ext; unfold tripleCharges sourceA1396 sourceB1396 sourceC1396 difference raw21912; decide +kernel
    rw [ha]
    exact (canonical21912 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1396 + difference 4 5) (sourceB1396 + difference 5 4) sourceC1396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1013) := by
    have ha : (tripleCharges (sourceA1396 + difference 4 5) (sourceB1396 + difference 5 4) sourceC1396) = raw21909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1396 sourceB1396 sourceC1396 difference raw21909; decide +kernel
    rw [ha]
    exact (canonical21909 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1396 + difference 5 5) (sourceB1396 + difference 5 5) sourceC1396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1009) := by
    have ha : (tripleCharges (sourceA1396 + difference 5 5) (sourceB1396 + difference 5 5) sourceC1396) = raw21895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1396 sourceB1396 sourceC1396 difference raw21895; decide +kernel
    rw [ha]
    exact (canonical21895 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1396 + sourceB1396) sourceC1396) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1396 + sourceB1396) sourceC1396) = raw21901 := by
      apply Matrix.ext; unfold doubleCharges sourceA1396 sourceB1396 sourceC1396 raw21901; decide +kernel
    rw [ha]
    exact (canonical21901 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1396 sourceB1396 sourceC1396
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1396, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1399 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1399 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1399 + difference 0 1) (sourceB1399 + difference 1 0) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4738) := by
    have ha : (tripleCharges (sourceA1399 + difference 0 1) (sourceB1399 + difference 1 0) sourceC1399) = raw21918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21918; decide +kernel
    rw [ha]
    exact (canonical21918 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1399 + difference 0 2) (sourceB1399 + difference 2 0) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4738) := by
    have ha : (tripleCharges (sourceA1399 + difference 0 2) (sourceB1399 + difference 2 0) sourceC1399) = raw21919 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21919; decide +kernel
    rw [ha]
    exact (canonical21919 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1399 + difference 0 3) (sourceB1399 + difference 3 0) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA1399 + difference 0 3) (sourceB1399 + difference 3 0) sourceC1399) = raw21920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21920; decide +kernel
    rw [ha]
    exact (canonical21920 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1399 + difference 0 4) (sourceB1399 + difference 4 0) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA1399 + difference 0 4) (sourceB1399 + difference 4 0) sourceC1399) = raw21921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21921; decide +kernel
    rw [ha]
    exact (canonical21921 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1399 + difference 0 5) (sourceB1399 + difference 5 0) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA1399 + difference 0 5) (sourceB1399 + difference 5 0) sourceC1399) = raw21922 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21922; decide +kernel
    rw [ha]
    exact (canonical21922 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1399 + difference 1 0) (sourceB1399 + difference 0 1) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4140) := by
    have ha : (tripleCharges (sourceA1399 + difference 1 0) (sourceB1399 + difference 0 1) sourceC1399) = raw21923 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21923; decide +kernel
    rw [ha]
    exact (canonical21923 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1399 + difference 1 2) (sourceB1399 + difference 2 1) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4320) := by
    have ha : (tripleCharges (sourceA1399 + difference 1 2) (sourceB1399 + difference 2 1) sourceC1399) = raw21924 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21924; decide +kernel
    rw [ha]
    exact (canonical21924 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1399 + difference 1 3) (sourceB1399 + difference 3 1) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4302) := by
    have ha : (tripleCharges (sourceA1399 + difference 1 3) (sourceB1399 + difference 3 1) sourceC1399) = raw21925 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21925; decide +kernel
    rw [ha]
    exact (canonical21925 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1399 + difference 1 4) (sourceB1399 + difference 4 1) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA1399 + difference 1 4) (sourceB1399 + difference 4 1) sourceC1399) = raw21926 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21926; decide +kernel
    rw [ha]
    exact (canonical21926 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1399 + difference 1 5) (sourceB1399 + difference 5 1) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1399 + difference 1 5) (sourceB1399 + difference 5 1) sourceC1399) = raw21927 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21927; decide +kernel
    rw [ha]
    exact (canonical21927 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1399 + difference 2 0) (sourceB1399 + difference 0 2) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4140) := by
    have ha : (tripleCharges (sourceA1399 + difference 2 0) (sourceB1399 + difference 0 2) sourceC1399) = raw21928 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21928; decide +kernel
    rw [ha]
    exact (canonical21928 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1399 + difference 2 1) (sourceB1399 + difference 1 2) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4320) := by
    have ha : (tripleCharges (sourceA1399 + difference 2 1) (sourceB1399 + difference 1 2) sourceC1399) = raw21929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21929; decide +kernel
    rw [ha]
    exact (canonical21929 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1399 + difference 2 3) (sourceB1399 + difference 3 2) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4302) := by
    have ha : (tripleCharges (sourceA1399 + difference 2 3) (sourceB1399 + difference 3 2) sourceC1399) = raw21930 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21930; decide +kernel
    rw [ha]
    exact (canonical21930 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1399 + difference 2 4) (sourceB1399 + difference 4 2) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA1399 + difference 2 4) (sourceB1399 + difference 4 2) sourceC1399) = raw21931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21931; decide +kernel
    rw [ha]
    exact (canonical21931 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1399 + difference 2 5) (sourceB1399 + difference 5 2) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1399 + difference 2 5) (sourceB1399 + difference 5 2) sourceC1399) = raw21932 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21932; decide +kernel
    rw [ha]
    exact (canonical21932 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1399 + difference 3 0) (sourceB1399 + difference 0 3) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4166) := by
    have ha : (tripleCharges (sourceA1399 + difference 3 0) (sourceB1399 + difference 0 3) sourceC1399) = raw21933 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21933; decide +kernel
    rw [ha]
    exact (canonical21933 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1399 + difference 3 1) (sourceB1399 + difference 1 3) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4338) := by
    have ha : (tripleCharges (sourceA1399 + difference 3 1) (sourceB1399 + difference 1 3) sourceC1399) = raw21934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21934; decide +kernel
    rw [ha]
    exact (canonical21934 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1399 + difference 3 2) (sourceB1399 + difference 2 3) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4338) := by
    have ha : (tripleCharges (sourceA1399 + difference 3 2) (sourceB1399 + difference 2 3) sourceC1399) = raw21935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21935; decide +kernel
    rw [ha]
    exact (canonical21935 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1399 + difference 3 4) (sourceB1399 + difference 4 3) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4454) := by
    have ha : (tripleCharges (sourceA1399 + difference 3 4) (sourceB1399 + difference 4 3) sourceC1399) = raw21936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21936; decide +kernel
    rw [ha]
    exact (canonical21936 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1399 + difference 3 5) (sourceB1399 + difference 5 3) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA1399 + difference 3 5) (sourceB1399 + difference 5 3) sourceC1399) = raw21937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21937; decide +kernel
    rw [ha]
    exact (canonical21937 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1399 + difference 4 0) (sourceB1399 + difference 0 4) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4147) := by
    have ha : (tripleCharges (sourceA1399 + difference 4 0) (sourceB1399 + difference 0 4) sourceC1399) = raw21938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21938; decide +kernel
    rw [ha]
    exact (canonical21938 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1399 + difference 4 1) (sourceB1399 + difference 1 4) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4324) := by
    have ha : (tripleCharges (sourceA1399 + difference 4 1) (sourceB1399 + difference 1 4) sourceC1399) = raw21939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21939; decide +kernel
    rw [ha]
    exact (canonical21939 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1399 + difference 4 2) (sourceB1399 + difference 2 4) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4324) := by
    have ha : (tripleCharges (sourceA1399 + difference 4 2) (sourceB1399 + difference 2 4) sourceC1399) = raw21940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21940; decide +kernel
    rw [ha]
    exact (canonical21940 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1399 + difference 4 3) (sourceB1399 + difference 3 4) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4317) := by
    have ha : (tripleCharges (sourceA1399 + difference 4 3) (sourceB1399 + difference 3 4) sourceC1399) = raw21941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21941; decide +kernel
    rw [ha]
    exact (canonical21941 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1399 + difference 4 5) (sourceB1399 + difference 5 4) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA1399 + difference 4 5) (sourceB1399 + difference 5 4) sourceC1399) = raw21942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21942; decide +kernel
    rw [ha]
    exact (canonical21942 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1399 + difference 5 0) (sourceB1399 + difference 0 5) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4146) := by
    have ha : (tripleCharges (sourceA1399 + difference 5 0) (sourceB1399 + difference 0 5) sourceC1399) = raw21943 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21943; decide +kernel
    rw [ha]
    exact (canonical21943 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1399 + difference 5 1) (sourceB1399 + difference 1 5) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4289) := by
    have ha : (tripleCharges (sourceA1399 + difference 5 1) (sourceB1399 + difference 1 5) sourceC1399) = raw21944 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21944; decide +kernel
    rw [ha]
    exact (canonical21944 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1399 + difference 5 2) (sourceB1399 + difference 2 5) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4289) := by
    have ha : (tripleCharges (sourceA1399 + difference 5 2) (sourceB1399 + difference 2 5) sourceC1399) = raw21945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21945; decide +kernel
    rw [ha]
    exact (canonical21945 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1399 + difference 5 3) (sourceB1399 + difference 3 5) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4312) := by
    have ha : (tripleCharges (sourceA1399 + difference 5 3) (sourceB1399 + difference 3 5) sourceC1399) = raw21946 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21946; decide +kernel
    rw [ha]
    exact (canonical21946 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1399 + difference 5 4) (sourceB1399 + difference 4 5) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA1399 + difference 5 4) (sourceB1399 + difference 4 5) sourceC1399) = raw21947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21947; decide +kernel
    rw [ha]
    exact (canonical21947 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1399 sourceB1399 sourceC1399
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1399, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1400 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1400 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1400 + difference 0 1) (sourceB1400 + difference 1 0) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1911) := by
    have ha : (tripleCharges (sourceA1400 + difference 0 1) (sourceB1400 + difference 1 0) sourceC1400) = raw21948 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21948; decide +kernel
    rw [ha]
    exact (canonical21948 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1400 + difference 0 2) (sourceB1400 + difference 2 0) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1911) := by
    have ha : (tripleCharges (sourceA1400 + difference 0 2) (sourceB1400 + difference 2 0) sourceC1400) = raw21949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21949; decide +kernel
    rw [ha]
    exact (canonical21949 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1400 + difference 0 3) (sourceB1400 + difference 3 0) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA1400 + difference 0 3) (sourceB1400 + difference 3 0) sourceC1400) = raw21950 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21950; decide +kernel
    rw [ha]
    exact (canonical21950 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1400 + difference 0 4) (sourceB1400 + difference 4 0) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2056) := by
    have ha : (tripleCharges (sourceA1400 + difference 0 4) (sourceB1400 + difference 4 0) sourceC1400) = raw21951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21951; decide +kernel
    rw [ha]
    exact (canonical21951 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1400 + difference 0 5) (sourceB1400 + difference 5 0) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2060) := by
    have ha : (tripleCharges (sourceA1400 + difference 0 5) (sourceB1400 + difference 5 0) sourceC1400) = raw21952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21952; decide +kernel
    rw [ha]
    exact (canonical21952 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1400 + difference 1 0) (sourceB1400 + difference 0 1) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1489) := by
    have ha : (tripleCharges (sourceA1400 + difference 1 0) (sourceB1400 + difference 0 1) sourceC1400) = raw21953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21953; decide +kernel
    rw [ha]
    exact (canonical21953 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1400 + difference 1 2) (sourceB1400 + difference 2 1) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1586) := by
    have ha : (tripleCharges (sourceA1400 + difference 1 2) (sourceB1400 + difference 2 1) sourceC1400) = raw21954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21954; decide +kernel
    rw [ha]
    exact (canonical21954 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1400 + difference 1 3) (sourceB1400 + difference 3 1) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1557) := by
    have ha : (tripleCharges (sourceA1400 + difference 1 3) (sourceB1400 + difference 3 1) sourceC1400) = raw21955 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21955; decide +kernel
    rw [ha]
    exact (canonical21955 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1400 + difference 1 4) (sourceB1400 + difference 4 1) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1599) := by
    have ha : (tripleCharges (sourceA1400 + difference 1 4) (sourceB1400 + difference 4 1) sourceC1400) = raw21956 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21956; decide +kernel
    rw [ha]
    exact (canonical21956 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1400 + difference 1 5) (sourceB1400 + difference 5 1) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1602) := by
    have ha : (tripleCharges (sourceA1400 + difference 1 5) (sourceB1400 + difference 5 1) sourceC1400) = raw21957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21957; decide +kernel
    rw [ha]
    exact (canonical21957 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1400 + difference 2 0) (sourceB1400 + difference 0 2) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1489) := by
    have ha : (tripleCharges (sourceA1400 + difference 2 0) (sourceB1400 + difference 0 2) sourceC1400) = raw21958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21958; decide +kernel
    rw [ha]
    exact (canonical21958 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1400 + difference 2 1) (sourceB1400 + difference 1 2) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1586) := by
    have ha : (tripleCharges (sourceA1400 + difference 2 1) (sourceB1400 + difference 1 2) sourceC1400) = raw21959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21959; decide +kernel
    rw [ha]
    exact (canonical21959 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1400 + difference 2 3) (sourceB1400 + difference 3 2) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1557) := by
    have ha : (tripleCharges (sourceA1400 + difference 2 3) (sourceB1400 + difference 3 2) sourceC1400) = raw21960 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21960; decide +kernel
    rw [ha]
    exact (canonical21960 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1400 + difference 2 4) (sourceB1400 + difference 4 2) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1599) := by
    have ha : (tripleCharges (sourceA1400 + difference 2 4) (sourceB1400 + difference 4 2) sourceC1400) = raw21961 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21961; decide +kernel
    rw [ha]
    exact (canonical21961 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1400 + difference 2 5) (sourceB1400 + difference 5 2) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1602) := by
    have ha : (tripleCharges (sourceA1400 + difference 2 5) (sourceB1400 + difference 5 2) sourceC1400) = raw21962 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21962; decide +kernel
    rw [ha]
    exact (canonical21962 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1400 + difference 3 0) (sourceB1400 + difference 0 3) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1499) := by
    have ha : (tripleCharges (sourceA1400 + difference 3 0) (sourceB1400 + difference 0 3) sourceC1400) = raw21963 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21963; decide +kernel
    rw [ha]
    exact (canonical21963 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1400 + difference 3 1) (sourceB1400 + difference 1 3) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1633) := by
    have ha : (tripleCharges (sourceA1400 + difference 3 1) (sourceB1400 + difference 1 3) sourceC1400) = raw21964 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21964; decide +kernel
    rw [ha]
    exact (canonical21964 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1400 + difference 3 2) (sourceB1400 + difference 2 3) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1633) := by
    have ha : (tripleCharges (sourceA1400 + difference 3 2) (sourceB1400 + difference 2 3) sourceC1400) = raw21965 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21965; decide +kernel
    rw [ha]
    exact (canonical21965 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1400 + difference 3 4) (sourceB1400 + difference 4 3) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1647) := by
    have ha : (tripleCharges (sourceA1400 + difference 3 4) (sourceB1400 + difference 4 3) sourceC1400) = raw21966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21966; decide +kernel
    rw [ha]
    exact (canonical21966 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1400 + difference 3 5) (sourceB1400 + difference 5 3) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1650) := by
    have ha : (tripleCharges (sourceA1400 + difference 3 5) (sourceB1400 + difference 5 3) sourceC1400) = raw21967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21967; decide +kernel
    rw [ha]
    exact (canonical21967 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1400 + difference 4 0) (sourceB1400 + difference 0 4) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1495) := by
    have ha : (tripleCharges (sourceA1400 + difference 4 0) (sourceB1400 + difference 0 4) sourceC1400) = raw21968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21968; decide +kernel
    rw [ha]
    exact (canonical21968 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1400 + difference 4 1) (sourceB1400 + difference 1 4) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1590) := by
    have ha : (tripleCharges (sourceA1400 + difference 4 1) (sourceB1400 + difference 1 4) sourceC1400) = raw21969 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21969; decide +kernel
    rw [ha]
    exact (canonical21969 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1400 + difference 4 2) (sourceB1400 + difference 2 4) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1590) := by
    have ha : (tripleCharges (sourceA1400 + difference 4 2) (sourceB1400 + difference 2 4) sourceC1400) = raw21970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21970; decide +kernel
    rw [ha]
    exact (canonical21970 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1400 + difference 4 3) (sourceB1400 + difference 3 4) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1576) := by
    have ha : (tripleCharges (sourceA1400 + difference 4 3) (sourceB1400 + difference 3 4) sourceC1400) = raw21971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21971; decide +kernel
    rw [ha]
    exact (canonical21971 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1400 + difference 4 5) (sourceB1400 + difference 5 4) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1627) := by
    have ha : (tripleCharges (sourceA1400 + difference 4 5) (sourceB1400 + difference 5 4) sourceC1400) = raw21972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21972; decide +kernel
    rw [ha]
    exact (canonical21972 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1400 + difference 5 0) (sourceB1400 + difference 0 5) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1494) := by
    have ha : (tripleCharges (sourceA1400 + difference 5 0) (sourceB1400 + difference 0 5) sourceC1400) = raw21973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21973; decide +kernel
    rw [ha]
    exact (canonical21973 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1400 + difference 5 1) (sourceB1400 + difference 1 5) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1555) := by
    have ha : (tripleCharges (sourceA1400 + difference 5 1) (sourceB1400 + difference 1 5) sourceC1400) = raw21974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21974; decide +kernel
    rw [ha]
    exact (canonical21974 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1400 + difference 5 2) (sourceB1400 + difference 2 5) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1555) := by
    have ha : (tripleCharges (sourceA1400 + difference 5 2) (sourceB1400 + difference 2 5) sourceC1400) = raw21975 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21975; decide +kernel
    rw [ha]
    exact (canonical21975 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1400 + difference 5 3) (sourceB1400 + difference 3 5) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1574) := by
    have ha : (tripleCharges (sourceA1400 + difference 5 3) (sourceB1400 + difference 3 5) sourceC1400) = raw21976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21976; decide +kernel
    rw [ha]
    exact (canonical21976 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1400 + difference 5 4) (sourceB1400 + difference 4 5) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1620) := by
    have ha : (tripleCharges (sourceA1400 + difference 5 4) (sourceB1400 + difference 4 5) sourceC1400) = raw21977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21977; decide +kernel
    rw [ha]
    exact (canonical21977 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1400 sourceB1400 sourceC1400
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1400, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1401 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1401 + difference 0 1) (sourceB1401 + difference 1 0) sourceC1401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1911) := by
    have ha : (tripleCharges (sourceA1401 + difference 0 1) (sourceB1401 + difference 1 0) sourceC1401) = raw21978 := by
      apply Matrix.ext; unfold tripleCharges sourceA1401 sourceB1401 sourceC1401 difference raw21978; decide +kernel
    rw [ha]
    exact (canonical21978 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1401 + difference 1 1) (sourceB1401 + difference 1 1) sourceC1401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1007) := by
    have ha : (tripleCharges (sourceA1401 + difference 1 1) (sourceB1401 + difference 1 1) sourceC1401) = raw21979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1401 sourceB1401 sourceC1401 difference raw21979; decide +kernel
    rw [ha]
    exact (canonical21979 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1401 + difference 2 1) (sourceB1401 + difference 1 2) sourceC1401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 898) := by
    have ha : (tripleCharges (sourceA1401 + difference 2 1) (sourceB1401 + difference 1 2) sourceC1401) = raw21980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1401 sourceB1401 sourceC1401 difference raw21980; decide +kernel
    rw [ha]
    exact (canonical21980 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1401 + difference 3 1) (sourceB1401 + difference 1 3) sourceC1401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 916) := by
    have ha : (tripleCharges (sourceA1401 + difference 3 1) (sourceB1401 + difference 1 3) sourceC1401) = raw21981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1401 sourceB1401 sourceC1401 difference raw21981; decide +kernel
    rw [ha]
    exact (canonical21981 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1401 + difference 4 1) (sourceB1401 + difference 1 4) sourceC1401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 902) := by
    have ha : (tripleCharges (sourceA1401 + difference 4 1) (sourceB1401 + difference 1 4) sourceC1401) = raw21982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1401 sourceB1401 sourceC1401 difference raw21982; decide +kernel
    rw [ha]
    exact (canonical21982 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1401 + difference 5 1) (sourceB1401 + difference 1 5) sourceC1401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 867) := by
    have ha : (tripleCharges (sourceA1401 + difference 5 1) (sourceB1401 + difference 1 5) sourceC1401) = raw21983 := by
      apply Matrix.ext; unfold tripleCharges sourceA1401 sourceB1401 sourceC1401 difference raw21983; decide +kernel
    rw [ha]
    exact (canonical21983 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1401 + sourceB1401) sourceC1401) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1401 + sourceB1401) sourceC1401) = raw21984 := by
      apply Matrix.ext; unfold doubleCharges sourceA1401 sourceB1401 sourceC1401 raw21984; decide +kernel
    rw [ha]
    exact (canonical21984 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1401 sourceB1401 sourceC1401
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1401, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1403 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1403 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1403 + difference 0 5) (sourceB1403 + difference 5 0) sourceC1403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1403 + difference 0 5) (sourceB1403 + difference 5 0) sourceC1403) = raw22002 := by
      apply Matrix.ext; unfold tripleCharges sourceA1403 sourceB1403 sourceC1403 difference raw22002; decide +kernel
    rw [ha]
    exact (canonical22002 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1403 + difference 1 5) (sourceB1403 + difference 5 1) sourceC1403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 811) := by
    have ha : (tripleCharges (sourceA1403 + difference 1 5) (sourceB1403 + difference 5 1) sourceC1403) = raw22003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1403 sourceB1403 sourceC1403 difference raw22003; decide +kernel
    rw [ha]
    exact (canonical22003 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1403 + difference 2 5) (sourceB1403 + difference 5 2) sourceC1403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 827) := by
    have ha : (tripleCharges (sourceA1403 + difference 2 5) (sourceB1403 + difference 5 2) sourceC1403) = raw22004 := by
      apply Matrix.ext; unfold tripleCharges sourceA1403 sourceB1403 sourceC1403 difference raw22004; decide +kernel
    rw [ha]
    exact (canonical22004 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1403 + difference 3 5) (sourceB1403 + difference 5 3) sourceC1403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 793) := by
    have ha : (tripleCharges (sourceA1403 + difference 3 5) (sourceB1403 + difference 5 3) sourceC1403) = raw22005 := by
      apply Matrix.ext; unfold tripleCharges sourceA1403 sourceB1403 sourceC1403 difference raw22005; decide +kernel
    rw [ha]
    exact (canonical22005 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1403 + difference 4 5) (sourceB1403 + difference 5 4) sourceC1403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 796) := by
    have ha : (tripleCharges (sourceA1403 + difference 4 5) (sourceB1403 + difference 5 4) sourceC1403) = raw22006 := by
      apply Matrix.ext; unfold tripleCharges sourceA1403 sourceB1403 sourceC1403 difference raw22006; decide +kernel
    rw [ha]
    exact (canonical22006 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1403 + difference 5 5) (sourceB1403 + difference 5 5) sourceC1403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 795) := by
    have ha : (tripleCharges (sourceA1403 + difference 5 5) (sourceB1403 + difference 5 5) sourceC1403) = raw22007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1403 sourceB1403 sourceC1403 difference raw22007; decide +kernel
    rw [ha]
    exact (canonical22007 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1403 + sourceB1403) sourceC1403) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1403 + sourceB1403) sourceC1403) = raw22008 := by
      apply Matrix.ext; unfold doubleCharges sourceA1403 sourceB1403 sourceC1403 raw22008; decide +kernel
    rw [ha]
    exact (canonical22008 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1403 sourceB1403 sourceC1403
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1403, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1405 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1405 + difference 0 5) (sourceB1405 + difference 5 0) sourceC1405) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA1405 + difference 0 5) (sourceB1405 + difference 5 0) sourceC1405) = raw22016 := by
      apply Matrix.ext; unfold tripleCharges sourceA1405 sourceB1405 sourceC1405 difference raw22016; decide +kernel
    rw [ha]
    exact (canonical22016 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1405 + difference 1 5) (sourceB1405 + difference 5 1) sourceC1405) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 858) := by
    have ha : (tripleCharges (sourceA1405 + difference 1 5) (sourceB1405 + difference 5 1) sourceC1405) = raw22017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1405 sourceB1405 sourceC1405 difference raw22017; decide +kernel
    rw [ha]
    exact (canonical22017 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1405 + difference 2 5) (sourceB1405 + difference 5 2) sourceC1405) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 825) := by
    have ha : (tripleCharges (sourceA1405 + difference 2 5) (sourceB1405 + difference 5 2) sourceC1405) = raw22018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1405 sourceB1405 sourceC1405 difference raw22018; decide +kernel
    rw [ha]
    exact (canonical22018 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1405 + difference 3 5) (sourceB1405 + difference 5 3) sourceC1405) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 825) := by
    have ha : (tripleCharges (sourceA1405 + difference 3 5) (sourceB1405 + difference 5 3) sourceC1405) = raw22019 := by
      apply Matrix.ext; unfold tripleCharges sourceA1405 sourceB1405 sourceC1405 difference raw22019; decide +kernel
    rw [ha]
    exact (canonical22019 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1405 + difference 4 5) (sourceB1405 + difference 5 4) sourceC1405) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 830) := by
    have ha : (tripleCharges (sourceA1405 + difference 4 5) (sourceB1405 + difference 5 4) sourceC1405) = raw22020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1405 sourceB1405 sourceC1405 difference raw22020; decide +kernel
    rw [ha]
    exact (canonical22020 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1405 + difference 5 5) (sourceB1405 + difference 5 5) sourceC1405) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 829) := by
    have ha : (tripleCharges (sourceA1405 + difference 5 5) (sourceB1405 + difference 5 5) sourceC1405) = raw22021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1405 sourceB1405 sourceC1405 difference raw22021; decide +kernel
    rw [ha]
    exact (canonical22021 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1405 + sourceB1405) sourceC1405) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1405 + sourceB1405) sourceC1405) = raw22022 := by
      apply Matrix.ext; unfold doubleCharges sourceA1405 sourceB1405 sourceC1405 raw22022; decide +kernel
    rw [ha]
    exact (canonical22022 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1405 sourceB1405 sourceC1405
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1405, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1406 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1406 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1406 + difference 0 0) (sourceB1406 + difference 0 0) sourceC1406) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 828) := by
    have ha : (tripleCharges (sourceA1406 + difference 0 0) (sourceB1406 + difference 0 0) sourceC1406) = raw22023 := by
      apply Matrix.ext; unfold tripleCharges sourceA1406 sourceB1406 sourceC1406 difference raw22023; decide +kernel
    rw [ha]
    exact (canonical22023 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1406 + difference 0 1) (sourceB1406 + difference 1 0) sourceC1406) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1659) := by
    have ha : (tripleCharges (sourceA1406 + difference 0 1) (sourceB1406 + difference 1 0) sourceC1406) = raw22024 := by
      apply Matrix.ext; unfold tripleCharges sourceA1406 sourceB1406 sourceC1406 difference raw22024; decide +kernel
    rw [ha]
    exact (canonical22024 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1406 + difference 0 2) (sourceB1406 + difference 2 0) sourceC1406) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1610) := by
    have ha : (tripleCharges (sourceA1406 + difference 0 2) (sourceB1406 + difference 2 0) sourceC1406) = raw22025 := by
      apply Matrix.ext; unfold tripleCharges sourceA1406 sourceB1406 sourceC1406 difference raw22025; decide +kernel
    rw [ha]
    exact (canonical22025 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1406 + difference 0 3) (sourceB1406 + difference 3 0) sourceC1406) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1610) := by
    have ha : (tripleCharges (sourceA1406 + difference 0 3) (sourceB1406 + difference 3 0) sourceC1406) = raw22026 := by
      apply Matrix.ext; unfold tripleCharges sourceA1406 sourceB1406 sourceC1406 difference raw22026; decide +kernel
    rw [ha]
    exact (canonical22026 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1406 + difference 0 4) (sourceB1406 + difference 4 0) sourceC1406) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA1406 + difference 0 4) (sourceB1406 + difference 4 0) sourceC1406) = raw22027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1406 sourceB1406 sourceC1406 difference raw22027; decide +kernel
    rw [ha]
    exact (canonical22027 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1406 + difference 0 5) (sourceB1406 + difference 5 0) sourceC1406) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1406 + difference 0 5) (sourceB1406 + difference 5 0) sourceC1406) = raw22028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1406 sourceB1406 sourceC1406 difference raw22028; decide +kernel
    rw [ha]
    exact (canonical22028 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1406 + sourceB1406) sourceC1406) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1406 + sourceB1406) sourceC1406) = raw22029 := by
      apply Matrix.ext; unfold doubleCharges sourceA1406 sourceB1406 sourceC1406 raw22029; decide +kernel
    rw [ha]
    exact (canonical22029 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1406 sourceB1406 sourceC1406
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1406, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources44
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1408 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1408 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1408 + difference 0 5) (sourceB1408 + difference 5 0) sourceC1408) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1408 + difference 0 5) (sourceB1408 + difference 5 0) sourceC1408) = raw22028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1408 sourceB1408 sourceC1408 difference raw22028; decide +kernel
    rw [ha]
    exact (canonical22028 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1408 + difference 1 5) (sourceB1408 + difference 5 1) sourceC1408) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 856) := by
    have ha : (tripleCharges (sourceA1408 + difference 1 5) (sourceB1408 + difference 5 1) sourceC1408) = raw22034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1408 sourceB1408 sourceC1408 difference raw22034; decide +kernel
    rw [ha]
    exact (canonical22034 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1408 + difference 2 5) (sourceB1408 + difference 5 2) sourceC1408) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 824) := by
    have ha : (tripleCharges (sourceA1408 + difference 2 5) (sourceB1408 + difference 5 2) sourceC1408) = raw22035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1408 sourceB1408 sourceC1408 difference raw22035; decide +kernel
    rw [ha]
    exact (canonical22035 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1408 + difference 3 5) (sourceB1408 + difference 5 3) sourceC1408) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 824) := by
    have ha : (tripleCharges (sourceA1408 + difference 3 5) (sourceB1408 + difference 5 3) sourceC1408) = raw22036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1408 sourceB1408 sourceC1408 difference raw22036; decide +kernel
    rw [ha]
    exact (canonical22036 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1408 + difference 4 5) (sourceB1408 + difference 5 4) sourceC1408) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 831) := by
    have ha : (tripleCharges (sourceA1408 + difference 4 5) (sourceB1408 + difference 5 4) sourceC1408) = raw22037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1408 sourceB1408 sourceC1408 difference raw22037; decide +kernel
    rw [ha]
    exact (canonical22037 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1408 + difference 5 5) (sourceB1408 + difference 5 5) sourceC1408) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 828) := by
    have ha : (tripleCharges (sourceA1408 + difference 5 5) (sourceB1408 + difference 5 5) sourceC1408) = raw22023 := by
      apply Matrix.ext; unfold tripleCharges sourceA1408 sourceB1408 sourceC1408 difference raw22023; decide +kernel
    rw [ha]
    exact (canonical22023 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1408 + sourceB1408) sourceC1408) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1408 + sourceB1408) sourceC1408) = raw22029 := by
      apply Matrix.ext; unfold doubleCharges sourceA1408 sourceB1408 sourceC1408 raw22029; decide +kernel
    rw [ha]
    exact (canonical22029 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1408 sourceB1408 sourceC1408
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1408, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1410 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1410 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1410 + difference 0 0) (sourceB1410 + difference 0 0) sourceC1410) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 826) := by
    have ha : (tripleCharges (sourceA1410 + difference 0 0) (sourceB1410 + difference 0 0) sourceC1410) = raw22041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1410 sourceB1410 sourceC1410 difference raw22041; decide +kernel
    rw [ha]
    exact (canonical22041 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1410 + difference 0 1) (sourceB1410 + difference 1 0) sourceC1410) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1657) := by
    have ha : (tripleCharges (sourceA1410 + difference 0 1) (sourceB1410 + difference 1 0) sourceC1410) = raw22042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1410 sourceB1410 sourceC1410 difference raw22042; decide +kernel
    rw [ha]
    exact (canonical22042 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1410 + difference 0 2) (sourceB1410 + difference 2 0) sourceC1410) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1608) := by
    have ha : (tripleCharges (sourceA1410 + difference 0 2) (sourceB1410 + difference 2 0) sourceC1410) = raw22043 := by
      apply Matrix.ext; unfold tripleCharges sourceA1410 sourceB1410 sourceC1410 difference raw22043; decide +kernel
    rw [ha]
    exact (canonical22043 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1410 + difference 0 3) (sourceB1410 + difference 3 0) sourceC1410) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1608) := by
    have ha : (tripleCharges (sourceA1410 + difference 0 3) (sourceB1410 + difference 3 0) sourceC1410) = raw22044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1410 sourceB1410 sourceC1410 difference raw22044; decide +kernel
    rw [ha]
    exact (canonical22044 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1410 + difference 0 4) (sourceB1410 + difference 4 0) sourceC1410) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1741) := by
    have ha : (tripleCharges (sourceA1410 + difference 0 4) (sourceB1410 + difference 4 0) sourceC1410) = raw22045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1410 sourceB1410 sourceC1410 difference raw22045; decide +kernel
    rw [ha]
    exact (canonical22045 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1410 + difference 0 5) (sourceB1410 + difference 5 0) sourceC1410) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1410 + difference 0 5) (sourceB1410 + difference 5 0) sourceC1410) = raw22046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1410 sourceB1410 sourceC1410 difference raw22046; decide +kernel
    rw [ha]
    exact (canonical22046 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1410 + sourceB1410) sourceC1410) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1410 + sourceB1410) sourceC1410) = raw22047 := by
      apply Matrix.ext; unfold doubleCharges sourceA1410 sourceB1410 sourceC1410 raw22047; decide +kernel
    rw [ha]
    exact (canonical22047 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1410 sourceB1410 sourceC1410
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1410, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1411 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1411 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1411 + difference 1 0) (sourceB1411 + difference 0 1) sourceC1411) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 555) := by
    have ha : (tripleCharges (sourceA1411 + difference 1 0) (sourceB1411 + difference 0 1) sourceC1411) = raw22048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1411 sourceB1411 sourceC1411 difference raw22048; decide +kernel
    rw [ha]
    exact (canonical22048 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1411 + difference 1 1) (sourceB1411 + difference 1 1) sourceC1411) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 826) := by
    have ha : (tripleCharges (sourceA1411 + difference 1 1) (sourceB1411 + difference 1 1) sourceC1411) = raw22041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1411 sourceB1411 sourceC1411 difference raw22041; decide +kernel
    rw [ha]
    exact (canonical22041 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1411 + difference 1 2) (sourceB1411 + difference 2 1) sourceC1411) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 715) := by
    have ha : (tripleCharges (sourceA1411 + difference 1 2) (sourceB1411 + difference 2 1) sourceC1411) = raw22049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1411 sourceB1411 sourceC1411 difference raw22049; decide +kernel
    rw [ha]
    exact (canonical22049 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1411 + difference 1 3) (sourceB1411 + difference 3 1) sourceC1411) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 715) := by
    have ha : (tripleCharges (sourceA1411 + difference 1 3) (sourceB1411 + difference 3 1) sourceC1411) = raw22050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1411 sourceB1411 sourceC1411 difference raw22050; decide +kernel
    rw [ha]
    exact (canonical22050 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1411 + difference 1 4) (sourceB1411 + difference 4 1) sourceC1411) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 859) := by
    have ha : (tripleCharges (sourceA1411 + difference 1 4) (sourceB1411 + difference 4 1) sourceC1411) = raw22051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1411 sourceB1411 sourceC1411 difference raw22051; decide +kernel
    rw [ha]
    exact (canonical22051 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1411 + difference 1 5) (sourceB1411 + difference 5 1) sourceC1411) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 852) := by
    have ha : (tripleCharges (sourceA1411 + difference 1 5) (sourceB1411 + difference 5 1) sourceC1411) = raw22052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1411 sourceB1411 sourceC1411 difference raw22052; decide +kernel
    rw [ha]
    exact (canonical22052 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1411 + sourceB1411) sourceC1411) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1411 + sourceB1411) sourceC1411) = raw22047 := by
      apply Matrix.ext; unfold doubleCharges sourceA1411 sourceB1411 sourceC1411 raw22047; decide +kernel
    rw [ha]
    exact (canonical22047 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1411 sourceB1411 sourceC1411
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1411, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1412 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1412 + difference 0 5) (sourceB1412 + difference 5 0) sourceC1412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1412 + difference 0 5) (sourceB1412 + difference 5 0) sourceC1412) = raw22046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1412 sourceB1412 sourceC1412 difference raw22046; decide +kernel
    rw [ha]
    exact (canonical22046 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1412 + difference 1 5) (sourceB1412 + difference 5 1) sourceC1412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 852) := by
    have ha : (tripleCharges (sourceA1412 + difference 1 5) (sourceB1412 + difference 5 1) sourceC1412) = raw22052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1412 sourceB1412 sourceC1412 difference raw22052; decide +kernel
    rw [ha]
    exact (canonical22052 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1412 + difference 2 5) (sourceB1412 + difference 5 2) sourceC1412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 823) := by
    have ha : (tripleCharges (sourceA1412 + difference 2 5) (sourceB1412 + difference 5 2) sourceC1412) = raw22053 := by
      apply Matrix.ext; unfold tripleCharges sourceA1412 sourceB1412 sourceC1412 difference raw22053; decide +kernel
    rw [ha]
    exact (canonical22053 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1412 + difference 3 5) (sourceB1412 + difference 5 3) sourceC1412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 823) := by
    have ha : (tripleCharges (sourceA1412 + difference 3 5) (sourceB1412 + difference 5 3) sourceC1412) = raw22054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1412 sourceB1412 sourceC1412 difference raw22054; decide +kernel
    rw [ha]
    exact (canonical22054 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1412 + difference 4 5) (sourceB1412 + difference 5 4) sourceC1412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 830) := by
    have ha : (tripleCharges (sourceA1412 + difference 4 5) (sourceB1412 + difference 5 4) sourceC1412) = raw22055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1412 sourceB1412 sourceC1412 difference raw22055; decide +kernel
    rw [ha]
    exact (canonical22055 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1412 + difference 5 5) (sourceB1412 + difference 5 5) sourceC1412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 826) := by
    have ha : (tripleCharges (sourceA1412 + difference 5 5) (sourceB1412 + difference 5 5) sourceC1412) = raw22041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1412 sourceB1412 sourceC1412 difference raw22041; decide +kernel
    rw [ha]
    exact (canonical22041 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1412 + sourceB1412) sourceC1412) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1412 + sourceB1412) sourceC1412) = raw22047 := by
      apply Matrix.ext; unfold doubleCharges sourceA1412 sourceB1412 sourceC1412 raw22047; decide +kernel
    rw [ha]
    exact (canonical22047 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1412 sourceB1412 sourceC1412
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1412, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1413 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1413 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1413 + difference 5 0) (sourceB1413 + difference 0 5) sourceC1413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 546) := by
    have ha : (tripleCharges (sourceA1413 + difference 5 0) (sourceB1413 + difference 0 5) sourceC1413) = raw22056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1413 sourceB1413 sourceC1413 difference raw22056; decide +kernel
    rw [ha]
    exact (canonical22056 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1413 + difference 5 1) (sourceB1413 + difference 1 5) sourceC1413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 809) := by
    have ha : (tripleCharges (sourceA1413 + difference 5 1) (sourceB1413 + difference 1 5) sourceC1413) = raw21578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1413 sourceB1413 sourceC1413 difference raw21578; decide +kernel
    rw [ha]
    exact (canonical21578 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1413 + difference 5 2) (sourceB1413 + difference 2 5) sourceC1413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 706) := by
    have ha : (tripleCharges (sourceA1413 + difference 5 2) (sourceB1413 + difference 2 5) sourceC1413) = raw22057 := by
      apply Matrix.ext; unfold tripleCharges sourceA1413 sourceB1413 sourceC1413 difference raw22057; decide +kernel
    rw [ha]
    exact (canonical22057 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1413 + difference 5 3) (sourceB1413 + difference 3 5) sourceC1413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 706) := by
    have ha : (tripleCharges (sourceA1413 + difference 5 3) (sourceB1413 + difference 3 5) sourceC1413) = raw21631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1413 sourceB1413 sourceC1413 difference raw21631; decide +kernel
    rw [ha]
    exact (canonical21631 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1413 + difference 5 4) (sourceB1413 + difference 4 5) sourceC1413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 741) := by
    have ha : (tripleCharges (sourceA1413 + difference 5 4) (sourceB1413 + difference 4 5) sourceC1413) = raw21575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1413 sourceB1413 sourceC1413 difference raw21575; decide +kernel
    rw [ha]
    exact (canonical21575 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1413 + difference 5 5) (sourceB1413 + difference 5 5) sourceC1413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 815) := by
    have ha : (tripleCharges (sourceA1413 + difference 5 5) (sourceB1413 + difference 5 5) sourceC1413) = raw22040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1413 sourceB1413 sourceC1413 difference raw22040; decide +kernel
    rw [ha]
    exact (canonical22040 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1413 + sourceB1413) sourceC1413) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1413 + sourceB1413) sourceC1413) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1413 sourceB1413 sourceC1413 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1413 sourceB1413 sourceC1413
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1413, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1200 : Integer.Sparse.reindex keyMap MixedData.row1200 = numericRow1200 := by decide +kernel

theorem numericCheck1200 (x : Master → ℝ) : Integer.Sparse.eval numericRow1200 x =
    (1 : ℝ) * reducedSource1200 x := by
  norm_num [numericRow1200, reducedSource1200, Integer.Sparse.eval, Sparse.eval, nodeValue602, nodeValue921, nodeValue1080, nodeValue1085, nodeValue4085]

theorem reindexCheck1201 : Integer.Sparse.reindex keyMap MixedData.row1201 = numericRow1201 := by decide +kernel

theorem numericCheck1201 (x : Master → ℝ) : Integer.Sparse.eval numericRow1201 x =
    (1 : ℝ) * reducedSource1201 x := by
  norm_num [numericRow1201, reducedSource1201, Integer.Sparse.eval, Sparse.eval, nodeValue1010, nodeValue1951, nodeValue2004, nodeValue2222, nodeValue2230, nodeValue4081]

theorem reindexCheck1202 : Integer.Sparse.reindex keyMap MixedData.row1202 = numericRow1202 := by decide +kernel

theorem numericCheck1202 (x : Master → ℝ) : Integer.Sparse.eval numericRow1202 x =
    (1 : ℝ) * reducedSource1202 x := by
  norm_num [numericRow1202, reducedSource1202, Integer.Sparse.eval, Sparse.eval, nodeValue1001, nodeValue1010, nodeValue1012, nodeValue1076, nodeValue2230, nodeValue4081]

theorem reindexCheck1203 : Integer.Sparse.reindex keyMap MixedData.row1203 = numericRow1203 := by decide +kernel

theorem numericCheck1203 (x : Master → ℝ) : Integer.Sparse.eval numericRow1203 x =
    (1 : ℝ) * reducedSource1203 x := by
  norm_num [numericRow1203, reducedSource1203, Integer.Sparse.eval, Sparse.eval, nodeValue1009, nodeValue1950, nodeValue2003, nodeValue2218, nodeValue2229, nodeValue4082]

theorem reindexCheck1204 : Integer.Sparse.reindex keyMap MixedData.row1204 = numericRow1204 := by decide +kernel

theorem numericCheck1204 (x : Master → ℝ) : Integer.Sparse.eval numericRow1204 x =
    (1 : ℝ) * reducedSource1204 x := by
  norm_num [numericRow1204, reducedSource1204, Integer.Sparse.eval, Sparse.eval, nodeValue1000, nodeValue1009, nodeValue1013, nodeValue1075, nodeValue2229, nodeValue4082]

theorem reindexCheck1205 : Integer.Sparse.reindex keyMap MixedData.row1205 = numericRow1205 := by decide +kernel

theorem numericCheck1205 (x : Master → ℝ) : Integer.Sparse.eval numericRow1205 x =
    (4 : ℝ) * reducedSource1205 x := by
  norm_num [numericRow1205, reducedSource1205, Integer.Sparse.eval, Sparse.eval, nodeValue4081, nodeValue4140, nodeValue4146, nodeValue4147, nodeValue4166, nodeValue4289, nodeValue4302, nodeValue4312, nodeValue4317, nodeValue4320, nodeValue4324, nodeValue4338, nodeValue4398, nodeValue4405, nodeValue4418, nodeValue4431, nodeValue4454, nodeValue4490, nodeValue4738, nodeValue4837, nodeValue4841]
  ring

theorem reindexCheck1206 : Integer.Sparse.reindex keyMap MixedData.row1206 = numericRow1206 := by decide +kernel

theorem numericCheck1206 (x : Master → ℝ) : Integer.Sparse.eval numericRow1206 x =
    (1 : ℝ) * reducedSource1206 x := by
  norm_num [numericRow1206, reducedSource1206, Integer.Sparse.eval, Sparse.eval, nodeValue1489, nodeValue1494, nodeValue1495, nodeValue1499, nodeValue1555, nodeValue1557, nodeValue1574, nodeValue1576, nodeValue1586, nodeValue1590, nodeValue1599, nodeValue1602, nodeValue1620, nodeValue1627, nodeValue1633, nodeValue1647, nodeValue1650, nodeValue1911, nodeValue2056, nodeValue2060, nodeValue4081]

theorem reindexCheck1207 : Integer.Sparse.reindex keyMap MixedData.row1207 = numericRow1207 := by decide +kernel

theorem numericCheck1207 (x : Master → ℝ) : Integer.Sparse.eval numericRow1207 x =
    (1 : ℝ) * reducedSource1207 x := by
  norm_num [numericRow1207, reducedSource1207, Integer.Sparse.eval, Sparse.eval, nodeValue867, nodeValue898, nodeValue902, nodeValue916, nodeValue1007, nodeValue1911, nodeValue4081]

theorem reindexCheck1208 : Integer.Sparse.reindex keyMap MixedData.row1208 = numericRow1208 := by decide +kernel

theorem numericCheck1208 (x : Master → ℝ) : Integer.Sparse.eval numericRow1208 x =
    (1 : ℝ) * reducedSource1208 x := by
  norm_num [numericRow1208, reducedSource1208, Integer.Sparse.eval, Sparse.eval, nodeValue793, nodeValue795, nodeValue796, nodeValue811, nodeValue827, nodeValue1715, nodeValue4069]

theorem reindexCheck1209 : Integer.Sparse.reindex keyMap MixedData.row1209 = numericRow1209 := by decide +kernel

theorem numericCheck1209 (x : Master → ℝ) : Integer.Sparse.eval numericRow1209 x =
    (1 : ℝ) * reducedSource1209 x := by
  norm_num [numericRow1209, reducedSource1209, Integer.Sparse.eval, Sparse.eval, nodeValue825, nodeValue829, nodeValue830, nodeValue858, nodeValue1740, nodeValue4071]

theorem reindexCheck1210 : Integer.Sparse.reindex keyMap MixedData.row1210 = numericRow1210 := by decide +kernel

theorem numericCheck1210 (x : Master → ℝ) : Integer.Sparse.eval numericRow1210 x =
    (1 : ℝ) * reducedSource1210 x := by
  norm_num [numericRow1210, reducedSource1210, Integer.Sparse.eval, Sparse.eval, nodeValue828, nodeValue1610, nodeValue1659, nodeValue1716, nodeValue1739, nodeValue4069]

theorem reindexCheck1211 : Integer.Sparse.reindex keyMap MixedData.row1211 = numericRow1211 := by decide +kernel

theorem numericCheck1211 (x : Master → ℝ) : Integer.Sparse.eval numericRow1211 x =
    (1 : ℝ) * reducedSource1211 x := by
  norm_num [numericRow1211, reducedSource1211, Integer.Sparse.eval, Sparse.eval, nodeValue824, nodeValue828, nodeValue831, nodeValue856, nodeValue1739, nodeValue4069]

theorem reindexCheck1212 : Integer.Sparse.reindex keyMap MixedData.row1212 = numericRow1212 := by decide +kernel

theorem numericCheck1212 (x : Master → ℝ) : Integer.Sparse.eval numericRow1212 x =
    (1 : ℝ) * reducedSource1212 x := by
  norm_num [numericRow1212, reducedSource1212, Integer.Sparse.eval, Sparse.eval, nodeValue826, nodeValue1608, nodeValue1657, nodeValue1738, nodeValue1741, nodeValue4071]

theorem reindexCheck1213 : Integer.Sparse.reindex keyMap MixedData.row1213 = numericRow1213 := by decide +kernel

theorem numericCheck1213 (x : Master → ℝ) : Integer.Sparse.eval numericRow1213 x =
    (1 : ℝ) * reducedSource1213 x := by
  norm_num [numericRow1213, reducedSource1213, Integer.Sparse.eval, Sparse.eval, nodeValue555, nodeValue715, nodeValue826, nodeValue852, nodeValue859, nodeValue4071]

theorem reindexCheck1214 : Integer.Sparse.reindex keyMap MixedData.row1214 = numericRow1214 := by decide +kernel

theorem numericCheck1214 (x : Master → ℝ) : Integer.Sparse.eval numericRow1214 x =
    (1 : ℝ) * reducedSource1214 x := by
  norm_num [numericRow1214, reducedSource1214, Integer.Sparse.eval, Sparse.eval, nodeValue823, nodeValue826, nodeValue830, nodeValue852, nodeValue1738, nodeValue4071]

theorem reindexCheck1215 : Integer.Sparse.reindex keyMap MixedData.row1215 = numericRow1215 := by decide +kernel

theorem numericCheck1215 (x : Master → ℝ) : Integer.Sparse.eval numericRow1215 x =
    (1 : ℝ) * reducedSource1215 x := by
  norm_num [numericRow1215, reducedSource1215, Integer.Sparse.eval, Sparse.eval, nodeValue546, nodeValue706, nodeValue741, nodeValue809, nodeValue815, nodeValue4070]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1200 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1200 (mixedVector B) = 0 := by
  have h602 : mixedVector B (Sum.inr 602) = Sparse.eval nodeValue602 (mixedVector B) := by
    change mixedMoment B node602 node602Labels = _
    exact sound602 B hB hF
  have h921 : mixedVector B (Sum.inr 921) = Sparse.eval nodeValue921 (mixedVector B) := by
    change mixedMoment B node921 node921Labels = _
    exact sound921 B hB hF
  have h1080 : mixedVector B (Sum.inr 1080) = Sparse.eval nodeValue1080 (mixedVector B) := by
    change mixedMoment B node1080 node1080Labels = _
    exact sound1080 B hB hF
  have h1085 : mixedVector B (Sum.inr 1085) = Sparse.eval nodeValue1085 (mixedVector B) := by
    change mixedMoment B node1085 node1085Labels = _
    exact sound1085 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1390, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h602, h921, h1080, h1085, h4085, reducedSource1200] using sourceEq1390 B hB

theorem rowSound1200 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1200 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1200, numericCheck1200, reducedZero1200 B hB hF, mul_zero]

theorem reducedZero1201 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1201 (mixedVector B) = 0 := by
  have h1010 : mixedVector B (Sum.inr 1010) = Sparse.eval nodeValue1010 (mixedVector B) := by
    change mixedMoment B node1010 node1010Labels = _
    exact sound1010 B hB hF
  have h1951 : mixedVector B (Sum.inr 1951) = Sparse.eval nodeValue1951 (mixedVector B) := by
    change mixedMoment B node1951 node1951Labels = _
    exact sound1951 B hB hF
  have h2004 : mixedVector B (Sum.inr 2004) = Sparse.eval nodeValue2004 (mixedVector B) := by
    change mixedMoment B node2004 node2004Labels = _
    exact sound2004 B hB hF
  have h2222 : mixedVector B (Sum.inr 2222) = Sparse.eval nodeValue2222 (mixedVector B) := by
    change mixedMoment B node2222 node2222Labels = _
    exact sound2222 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1391, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1010, h1951, h2004, h2222, h2230, h4081, reducedSource1201] using sourceEq1391 B hB

theorem rowSound1201 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1201 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1201, numericCheck1201, reducedZero1201 B hB hF, mul_zero]

theorem reducedZero1202 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1202 (mixedVector B) = 0 := by
  have h1001 : mixedVector B (Sum.inr 1001) = Sparse.eval nodeValue1001 (mixedVector B) := by
    change mixedMoment B node1001 node1001Labels = _
    exact sound1001 B hB hF
  have h1010 : mixedVector B (Sum.inr 1010) = Sparse.eval nodeValue1010 (mixedVector B) := by
    change mixedMoment B node1010 node1010Labels = _
    exact sound1010 B hB hF
  have h1012 : mixedVector B (Sum.inr 1012) = Sparse.eval nodeValue1012 (mixedVector B) := by
    change mixedMoment B node1012 node1012Labels = _
    exact sound1012 B hB hF
  have h1076 : mixedVector B (Sum.inr 1076) = Sparse.eval nodeValue1076 (mixedVector B) := by
    change mixedMoment B node1076 node1076Labels = _
    exact sound1076 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1392, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1001, h1010, h1012, h1076, h2230, h4081, reducedSource1202] using sourceEq1392 B hB

theorem rowSound1202 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1202 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1202, numericCheck1202, reducedZero1202 B hB hF, mul_zero]

theorem reducedZero1203 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1203 (mixedVector B) = 0 := by
  have h1009 : mixedVector B (Sum.inr 1009) = Sparse.eval nodeValue1009 (mixedVector B) := by
    change mixedMoment B node1009 node1009Labels = _
    exact sound1009 B hB hF
  have h1950 : mixedVector B (Sum.inr 1950) = Sparse.eval nodeValue1950 (mixedVector B) := by
    change mixedMoment B node1950 node1950Labels = _
    exact sound1950 B hB hF
  have h2003 : mixedVector B (Sum.inr 2003) = Sparse.eval nodeValue2003 (mixedVector B) := by
    change mixedMoment B node2003 node2003Labels = _
    exact sound2003 B hB hF
  have h2218 : mixedVector B (Sum.inr 2218) = Sparse.eval nodeValue2218 (mixedVector B) := by
    change mixedMoment B node2218 node2218Labels = _
    exact sound2218 B hB hF
  have h2229 : mixedVector B (Sum.inr 2229) = Sparse.eval nodeValue2229 (mixedVector B) := by
    change mixedMoment B node2229 node2229Labels = _
    exact sound2229 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1393, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1009, h1950, h2003, h2218, h2229, h4082, reducedSource1203] using sourceEq1393 B hB

theorem rowSound1203 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1203 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1203, numericCheck1203, reducedZero1203 B hB hF, mul_zero]

theorem reducedZero1204 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1204 (mixedVector B) = 0 := by
  have h1000 : mixedVector B (Sum.inr 1000) = Sparse.eval nodeValue1000 (mixedVector B) := by
    change mixedMoment B node1000 node1000Labels = _
    exact sound1000 B hB hF
  have h1009 : mixedVector B (Sum.inr 1009) = Sparse.eval nodeValue1009 (mixedVector B) := by
    change mixedMoment B node1009 node1009Labels = _
    exact sound1009 B hB hF
  have h1013 : mixedVector B (Sum.inr 1013) = Sparse.eval nodeValue1013 (mixedVector B) := by
    change mixedMoment B node1013 node1013Labels = _
    exact sound1013 B hB hF
  have h1075 : mixedVector B (Sum.inr 1075) = Sparse.eval nodeValue1075 (mixedVector B) := by
    change mixedMoment B node1075 node1075Labels = _
    exact sound1075 B hB hF
  have h2229 : mixedVector B (Sum.inr 2229) = Sparse.eval nodeValue2229 (mixedVector B) := by
    change mixedMoment B node2229 node2229Labels = _
    exact sound2229 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm1396, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1000, h1009, h1013, h1075, h2229, h4082, reducedSource1204] using sourceEq1396 B hB

theorem rowSound1204 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1204 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1204, numericCheck1204, reducedZero1204 B hB hF, mul_zero]

theorem reducedZero1205 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1205 (mixedVector B) = 0 := by
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  have h4140 : mixedVector B (Sum.inr 4140) = Sparse.eval nodeValue4140 (mixedVector B) := by
    change mixedMoment B node4140 node4140Labels = _
    exact sound4140 B hB hF
  have h4146 : mixedVector B (Sum.inr 4146) = Sparse.eval nodeValue4146 (mixedVector B) := by
    change mixedMoment B node4146 node4146Labels = _
    exact sound4146 B hB hF
  have h4147 : mixedVector B (Sum.inr 4147) = Sparse.eval nodeValue4147 (mixedVector B) := by
    change mixedMoment B node4147 node4147Labels = _
    exact sound4147 B hB hF
  have h4166 : mixedVector B (Sum.inr 4166) = Sparse.eval nodeValue4166 (mixedVector B) := by
    change mixedMoment B node4166 node4166Labels = _
    exact sound4166 B hB hF
  have h4289 : mixedVector B (Sum.inr 4289) = Sparse.eval nodeValue4289 (mixedVector B) := by
    change mixedMoment B node4289 node4289Labels = _
    exact sound4289 B hB hF
  have h4302 : mixedVector B (Sum.inr 4302) = Sparse.eval nodeValue4302 (mixedVector B) := by
    change mixedMoment B node4302 node4302Labels = _
    exact sound4302 B hB hF
  have h4312 : mixedVector B (Sum.inr 4312) = Sparse.eval nodeValue4312 (mixedVector B) := by
    change mixedMoment B node4312 node4312Labels = _
    exact sound4312 B hB hF
  have h4317 : mixedVector B (Sum.inr 4317) = Sparse.eval nodeValue4317 (mixedVector B) := by
    change mixedMoment B node4317 node4317Labels = _
    exact sound4317 B hB hF
  have h4320 : mixedVector B (Sum.inr 4320) = Sparse.eval nodeValue4320 (mixedVector B) := by
    change mixedMoment B node4320 node4320Labels = _
    exact sound4320 B hB hF
  have h4324 : mixedVector B (Sum.inr 4324) = Sparse.eval nodeValue4324 (mixedVector B) := by
    change mixedMoment B node4324 node4324Labels = _
    exact sound4324 B hB hF
  have h4338 : mixedVector B (Sum.inr 4338) = Sparse.eval nodeValue4338 (mixedVector B) := by
    change mixedMoment B node4338 node4338Labels = _
    exact sound4338 B hB hF
  have h4398 : mixedVector B (Sum.inr 4398) = Sparse.eval nodeValue4398 (mixedVector B) := by
    change mixedMoment B node4398 node4398Labels = _
    exact sound4398 B hB hF
  have h4405 : mixedVector B (Sum.inr 4405) = Sparse.eval nodeValue4405 (mixedVector B) := by
    change mixedMoment B node4405 node4405Labels = _
    exact sound4405 B hB hF
  have h4418 : mixedVector B (Sum.inr 4418) = Sparse.eval nodeValue4418 (mixedVector B) := by
    change mixedMoment B node4418 node4418Labels = _
    exact sound4418 B hB hF
  have h4431 : mixedVector B (Sum.inr 4431) = Sparse.eval nodeValue4431 (mixedVector B) := by
    change mixedMoment B node4431 node4431Labels = _
    exact sound4431 B hB hF
  have h4454 : mixedVector B (Sum.inr 4454) = Sparse.eval nodeValue4454 (mixedVector B) := by
    change mixedMoment B node4454 node4454Labels = _
    exact sound4454 B hB hF
  have h4490 : mixedVector B (Sum.inr 4490) = Sparse.eval nodeValue4490 (mixedVector B) := by
    change mixedMoment B node4490 node4490Labels = _
    exact sound4490 B hB hF
  have h4738 : mixedVector B (Sum.inr 4738) = Sparse.eval nodeValue4738 (mixedVector B) := by
    change mixedMoment B node4738 node4738Labels = _
    exact sound4738 B hB hF
  have h4837 : mixedVector B (Sum.inr 4837) = Sparse.eval nodeValue4837 (mixedVector B) := by
    change mixedMoment B node4837 node4837Labels = _
    exact sound4837 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  simpa only [sourceForm1399, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4081, h4140, h4146, h4147, h4166, h4289, h4302, h4312, h4317, h4320, h4324, h4338, h4398, h4405, h4418, h4431, h4454, h4490, h4738, h4837, h4841, reducedSource1205] using sourceEq1399 B hB

theorem rowSound1205 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1205 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1205, numericCheck1205, reducedZero1205 B hB hF, mul_zero]

theorem reducedZero1206 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1206 (mixedVector B) = 0 := by
  have h1489 : mixedVector B (Sum.inr 1489) = Sparse.eval nodeValue1489 (mixedVector B) := by
    change mixedMoment B node1489 node1489Labels = _
    exact sound1489 B hB hF
  have h1494 : mixedVector B (Sum.inr 1494) = Sparse.eval nodeValue1494 (mixedVector B) := by
    change mixedMoment B node1494 node1494Labels = _
    exact sound1494 B hB hF
  have h1495 : mixedVector B (Sum.inr 1495) = Sparse.eval nodeValue1495 (mixedVector B) := by
    change mixedMoment B node1495 node1495Labels = _
    exact sound1495 B hB hF
  have h1499 : mixedVector B (Sum.inr 1499) = Sparse.eval nodeValue1499 (mixedVector B) := by
    change mixedMoment B node1499 node1499Labels = _
    exact sound1499 B hB hF
  have h1555 : mixedVector B (Sum.inr 1555) = Sparse.eval nodeValue1555 (mixedVector B) := by
    change mixedMoment B node1555 node1555Labels = _
    exact sound1555 B hB hF
  have h1557 : mixedVector B (Sum.inr 1557) = Sparse.eval nodeValue1557 (mixedVector B) := by
    change mixedMoment B node1557 node1557Labels = _
    exact sound1557 B hB hF
  have h1574 : mixedVector B (Sum.inr 1574) = Sparse.eval nodeValue1574 (mixedVector B) := by
    change mixedMoment B node1574 node1574Labels = _
    exact sound1574 B hB hF
  have h1576 : mixedVector B (Sum.inr 1576) = Sparse.eval nodeValue1576 (mixedVector B) := by
    change mixedMoment B node1576 node1576Labels = _
    exact sound1576 B hB hF
  have h1586 : mixedVector B (Sum.inr 1586) = Sparse.eval nodeValue1586 (mixedVector B) := by
    change mixedMoment B node1586 node1586Labels = _
    exact sound1586 B hB hF
  have h1590 : mixedVector B (Sum.inr 1590) = Sparse.eval nodeValue1590 (mixedVector B) := by
    change mixedMoment B node1590 node1590Labels = _
    exact sound1590 B hB hF
  have h1599 : mixedVector B (Sum.inr 1599) = Sparse.eval nodeValue1599 (mixedVector B) := by
    change mixedMoment B node1599 node1599Labels = _
    exact sound1599 B hB hF
  have h1602 : mixedVector B (Sum.inr 1602) = Sparse.eval nodeValue1602 (mixedVector B) := by
    change mixedMoment B node1602 node1602Labels = _
    exact sound1602 B hB hF
  have h1620 : mixedVector B (Sum.inr 1620) = Sparse.eval nodeValue1620 (mixedVector B) := by
    change mixedMoment B node1620 node1620Labels = _
    exact sound1620 B hB hF
  have h1627 : mixedVector B (Sum.inr 1627) = Sparse.eval nodeValue1627 (mixedVector B) := by
    change mixedMoment B node1627 node1627Labels = _
    exact sound1627 B hB hF
  have h1633 : mixedVector B (Sum.inr 1633) = Sparse.eval nodeValue1633 (mixedVector B) := by
    change mixedMoment B node1633 node1633Labels = _
    exact sound1633 B hB hF
  have h1647 : mixedVector B (Sum.inr 1647) = Sparse.eval nodeValue1647 (mixedVector B) := by
    change mixedMoment B node1647 node1647Labels = _
    exact sound1647 B hB hF
  have h1650 : mixedVector B (Sum.inr 1650) = Sparse.eval nodeValue1650 (mixedVector B) := by
    change mixedMoment B node1650 node1650Labels = _
    exact sound1650 B hB hF
  have h1911 : mixedVector B (Sum.inr 1911) = Sparse.eval nodeValue1911 (mixedVector B) := by
    change mixedMoment B node1911 node1911Labels = _
    exact sound1911 B hB hF
  have h2056 : mixedVector B (Sum.inr 2056) = Sparse.eval nodeValue2056 (mixedVector B) := by
    change mixedMoment B node2056 node2056Labels = _
    exact sound2056 B hB hF
  have h2060 : mixedVector B (Sum.inr 2060) = Sparse.eval nodeValue2060 (mixedVector B) := by
    change mixedMoment B node2060 node2060Labels = _
    exact sound2060 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1400, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1489, h1494, h1495, h1499, h1555, h1557, h1574, h1576, h1586, h1590, h1599, h1602, h1620, h1627, h1633, h1647, h1650, h1911, h2056, h2060, h4081, reducedSource1206] using sourceEq1400 B hB

theorem rowSound1206 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1206 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1206, numericCheck1206, reducedZero1206 B hB hF, mul_zero]

theorem reducedZero1207 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1207 (mixedVector B) = 0 := by
  have h867 : mixedVector B (Sum.inr 867) = Sparse.eval nodeValue867 (mixedVector B) := by
    change mixedMoment B node867 node867Labels = _
    exact sound867 B hB hF
  have h898 : mixedVector B (Sum.inr 898) = Sparse.eval nodeValue898 (mixedVector B) := by
    change mixedMoment B node898 node898Labels = _
    exact sound898 B hB hF
  have h902 : mixedVector B (Sum.inr 902) = Sparse.eval nodeValue902 (mixedVector B) := by
    change mixedMoment B node902 node902Labels = _
    exact sound902 B hB hF
  have h916 : mixedVector B (Sum.inr 916) = Sparse.eval nodeValue916 (mixedVector B) := by
    change mixedMoment B node916 node916Labels = _
    exact sound916 B hB hF
  have h1007 : mixedVector B (Sum.inr 1007) = Sparse.eval nodeValue1007 (mixedVector B) := by
    change mixedMoment B node1007 node1007Labels = _
    exact sound1007 B hB hF
  have h1911 : mixedVector B (Sum.inr 1911) = Sparse.eval nodeValue1911 (mixedVector B) := by
    change mixedMoment B node1911 node1911Labels = _
    exact sound1911 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1401, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h867, h898, h902, h916, h1007, h1911, h4081, reducedSource1207] using sourceEq1401 B hB

theorem rowSound1207 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1207 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1207, numericCheck1207, reducedZero1207 B hB hF, mul_zero]

theorem reducedZero1208 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1208 (mixedVector B) = 0 := by
  have h793 : mixedVector B (Sum.inr 793) = Sparse.eval nodeValue793 (mixedVector B) := by
    change mixedMoment B node793 node793Labels = _
    exact sound793 B hB hF
  have h795 : mixedVector B (Sum.inr 795) = Sparse.eval nodeValue795 (mixedVector B) := by
    change mixedMoment B node795 node795Labels = _
    exact sound795 B hB hF
  have h796 : mixedVector B (Sum.inr 796) = Sparse.eval nodeValue796 (mixedVector B) := by
    change mixedMoment B node796 node796Labels = _
    exact sound796 B hB hF
  have h811 : mixedVector B (Sum.inr 811) = Sparse.eval nodeValue811 (mixedVector B) := by
    change mixedMoment B node811 node811Labels = _
    exact sound811 B hB hF
  have h827 : mixedVector B (Sum.inr 827) = Sparse.eval nodeValue827 (mixedVector B) := by
    change mixedMoment B node827 node827Labels = _
    exact sound827 B hB hF
  have h1715 : mixedVector B (Sum.inr 1715) = Sparse.eval nodeValue1715 (mixedVector B) := by
    change mixedMoment B node1715 node1715Labels = _
    exact sound1715 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1403, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h793, h795, h796, h811, h827, h1715, h4069, reducedSource1208] using sourceEq1403 B hB

theorem rowSound1208 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1208 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1208, numericCheck1208, reducedZero1208 B hB hF, mul_zero]

theorem reducedZero1209 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1209 (mixedVector B) = 0 := by
  have h825 : mixedVector B (Sum.inr 825) = Sparse.eval nodeValue825 (mixedVector B) := by
    change mixedMoment B node825 node825Labels = _
    exact sound825 B hB hF
  have h829 : mixedVector B (Sum.inr 829) = Sparse.eval nodeValue829 (mixedVector B) := by
    change mixedMoment B node829 node829Labels = _
    exact sound829 B hB hF
  have h830 : mixedVector B (Sum.inr 830) = Sparse.eval nodeValue830 (mixedVector B) := by
    change mixedMoment B node830 node830Labels = _
    exact sound830 B hB hF
  have h858 : mixedVector B (Sum.inr 858) = Sparse.eval nodeValue858 (mixedVector B) := by
    change mixedMoment B node858 node858Labels = _
    exact sound858 B hB hF
  have h1740 : mixedVector B (Sum.inr 1740) = Sparse.eval nodeValue1740 (mixedVector B) := by
    change mixedMoment B node1740 node1740Labels = _
    exact sound1740 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1405, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h825, h829, h830, h858, h1740, h4071, reducedSource1209] using sourceEq1405 B hB

theorem rowSound1209 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1209 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1209, numericCheck1209, reducedZero1209 B hB hF, mul_zero]

theorem reducedZero1210 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1210 (mixedVector B) = 0 := by
  have h828 : mixedVector B (Sum.inr 828) = Sparse.eval nodeValue828 (mixedVector B) := by
    change mixedMoment B node828 node828Labels = _
    exact sound828 B hB hF
  have h1610 : mixedVector B (Sum.inr 1610) = Sparse.eval nodeValue1610 (mixedVector B) := by
    change mixedMoment B node1610 node1610Labels = _
    exact sound1610 B hB hF
  have h1659 : mixedVector B (Sum.inr 1659) = Sparse.eval nodeValue1659 (mixedVector B) := by
    change mixedMoment B node1659 node1659Labels = _
    exact sound1659 B hB hF
  have h1716 : mixedVector B (Sum.inr 1716) = Sparse.eval nodeValue1716 (mixedVector B) := by
    change mixedMoment B node1716 node1716Labels = _
    exact sound1716 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1406, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h828, h1610, h1659, h1716, h1739, h4069, reducedSource1210] using sourceEq1406 B hB

theorem rowSound1210 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1210 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1210, numericCheck1210, reducedZero1210 B hB hF, mul_zero]

theorem reducedZero1211 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1211 (mixedVector B) = 0 := by
  have h824 : mixedVector B (Sum.inr 824) = Sparse.eval nodeValue824 (mixedVector B) := by
    change mixedMoment B node824 node824Labels = _
    exact sound824 B hB hF
  have h828 : mixedVector B (Sum.inr 828) = Sparse.eval nodeValue828 (mixedVector B) := by
    change mixedMoment B node828 node828Labels = _
    exact sound828 B hB hF
  have h831 : mixedVector B (Sum.inr 831) = Sparse.eval nodeValue831 (mixedVector B) := by
    change mixedMoment B node831 node831Labels = _
    exact sound831 B hB hF
  have h856 : mixedVector B (Sum.inr 856) = Sparse.eval nodeValue856 (mixedVector B) := by
    change mixedMoment B node856 node856Labels = _
    exact sound856 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1408, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h824, h828, h831, h856, h1739, h4069, reducedSource1211] using sourceEq1408 B hB

theorem rowSound1211 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1211 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1211, numericCheck1211, reducedZero1211 B hB hF, mul_zero]

theorem reducedZero1212 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1212 (mixedVector B) = 0 := by
  have h826 : mixedVector B (Sum.inr 826) = Sparse.eval nodeValue826 (mixedVector B) := by
    change mixedMoment B node826 node826Labels = _
    exact sound826 B hB hF
  have h1608 : mixedVector B (Sum.inr 1608) = Sparse.eval nodeValue1608 (mixedVector B) := by
    change mixedMoment B node1608 node1608Labels = _
    exact sound1608 B hB hF
  have h1657 : mixedVector B (Sum.inr 1657) = Sparse.eval nodeValue1657 (mixedVector B) := by
    change mixedMoment B node1657 node1657Labels = _
    exact sound1657 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h1741 : mixedVector B (Sum.inr 1741) = Sparse.eval nodeValue1741 (mixedVector B) := by
    change mixedMoment B node1741 node1741Labels = _
    exact sound1741 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1410, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h826, h1608, h1657, h1738, h1741, h4071, reducedSource1212] using sourceEq1410 B hB

theorem rowSound1212 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1212 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1212, numericCheck1212, reducedZero1212 B hB hF, mul_zero]

theorem reducedZero1213 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1213 (mixedVector B) = 0 := by
  have h555 : mixedVector B (Sum.inr 555) = Sparse.eval nodeValue555 (mixedVector B) := by
    change mixedMoment B node555 node555Labels = _
    exact sound555 B hB hF
  have h715 : mixedVector B (Sum.inr 715) = Sparse.eval nodeValue715 (mixedVector B) := by
    change mixedMoment B node715 node715Labels = _
    exact sound715 B hB hF
  have h826 : mixedVector B (Sum.inr 826) = Sparse.eval nodeValue826 (mixedVector B) := by
    change mixedMoment B node826 node826Labels = _
    exact sound826 B hB hF
  have h852 : mixedVector B (Sum.inr 852) = Sparse.eval nodeValue852 (mixedVector B) := by
    change mixedMoment B node852 node852Labels = _
    exact sound852 B hB hF
  have h859 : mixedVector B (Sum.inr 859) = Sparse.eval nodeValue859 (mixedVector B) := by
    change mixedMoment B node859 node859Labels = _
    exact sound859 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1411, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h555, h715, h826, h852, h859, h4071, reducedSource1213] using sourceEq1411 B hB

theorem rowSound1213 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1213 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1213, numericCheck1213, reducedZero1213 B hB hF, mul_zero]

theorem reducedZero1214 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1214 (mixedVector B) = 0 := by
  have h823 : mixedVector B (Sum.inr 823) = Sparse.eval nodeValue823 (mixedVector B) := by
    change mixedMoment B node823 node823Labels = _
    exact sound823 B hB hF
  have h826 : mixedVector B (Sum.inr 826) = Sparse.eval nodeValue826 (mixedVector B) := by
    change mixedMoment B node826 node826Labels = _
    exact sound826 B hB hF
  have h830 : mixedVector B (Sum.inr 830) = Sparse.eval nodeValue830 (mixedVector B) := by
    change mixedMoment B node830 node830Labels = _
    exact sound830 B hB hF
  have h852 : mixedVector B (Sum.inr 852) = Sparse.eval nodeValue852 (mixedVector B) := by
    change mixedMoment B node852 node852Labels = _
    exact sound852 B hB hF
  have h1738 : mixedVector B (Sum.inr 1738) = Sparse.eval nodeValue1738 (mixedVector B) := by
    change mixedMoment B node1738 node1738Labels = _
    exact sound1738 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1412, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h823, h826, h830, h852, h1738, h4071, reducedSource1214] using sourceEq1412 B hB

theorem rowSound1214 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1214 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1214, numericCheck1214, reducedZero1214 B hB hF, mul_zero]

theorem reducedZero1215 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1215 (mixedVector B) = 0 := by
  have h546 : mixedVector B (Sum.inr 546) = Sparse.eval nodeValue546 (mixedVector B) := by
    change mixedMoment B node546 node546Labels = _
    exact sound546 B hB hF
  have h706 : mixedVector B (Sum.inr 706) = Sparse.eval nodeValue706 (mixedVector B) := by
    change mixedMoment B node706 node706Labels = _
    exact sound706 B hB hF
  have h741 : mixedVector B (Sum.inr 741) = Sparse.eval nodeValue741 (mixedVector B) := by
    change mixedMoment B node741 node741Labels = _
    exact sound741 B hB hF
  have h809 : mixedVector B (Sum.inr 809) = Sparse.eval nodeValue809 (mixedVector B) := by
    change mixedMoment B node809 node809Labels = _
    exact sound809 B hB hF
  have h815 : mixedVector B (Sum.inr 815) = Sparse.eval nodeValue815 (mixedVector B) := by
    change mixedMoment B node815 node815Labels = _
    exact sound815 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1413, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h546, h706, h741, h809, h815, h4070, reducedSource1215] using sourceEq1413 B hB

theorem rowSound1215 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1215 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1215, numericCheck1215, reducedZero1215 B hB hF, mul_zero]

theorem sourceRowsAt1200 : MixedData.sourceRows (1200 : Fin 2425) =
    MixedData.row1200 := by decide +kernel

theorem sourceRowsAt1201 : MixedData.sourceRows (1201 : Fin 2425) =
    MixedData.row1201 := by decide +kernel

theorem sourceRowsAt1202 : MixedData.sourceRows (1202 : Fin 2425) =
    MixedData.row1202 := by decide +kernel

theorem sourceRowsAt1203 : MixedData.sourceRows (1203 : Fin 2425) =
    MixedData.row1203 := by decide +kernel

theorem sourceRowsAt1204 : MixedData.sourceRows (1204 : Fin 2425) =
    MixedData.row1204 := by decide +kernel

theorem sourceRowsAt1205 : MixedData.sourceRows (1205 : Fin 2425) =
    MixedData.row1205 := by decide +kernel

theorem sourceRowsAt1206 : MixedData.sourceRows (1206 : Fin 2425) =
    MixedData.row1206 := by decide +kernel

theorem sourceRowsAt1207 : MixedData.sourceRows (1207 : Fin 2425) =
    MixedData.row1207 := by decide +kernel

theorem sourceRowsAt1208 : MixedData.sourceRows (1208 : Fin 2425) =
    MixedData.row1208 := by decide +kernel

theorem sourceRowsAt1209 : MixedData.sourceRows (1209 : Fin 2425) =
    MixedData.row1209 := by decide +kernel

theorem sourceRowsAt1210 : MixedData.sourceRows (1210 : Fin 2425) =
    MixedData.row1210 := by decide +kernel

theorem sourceRowsAt1211 : MixedData.sourceRows (1211 : Fin 2425) =
    MixedData.row1211 := by decide +kernel

theorem sourceRowsAt1212 : MixedData.sourceRows (1212 : Fin 2425) =
    MixedData.row1212 := by decide +kernel

theorem sourceRowsAt1213 : MixedData.sourceRows (1213 : Fin 2425) =
    MixedData.row1213 := by decide +kernel

theorem sourceRowsAt1214 : MixedData.sourceRows (1214 : Fin 2425) =
    MixedData.row1214 := by decide +kernel

theorem sourceRowsAt1215 : MixedData.sourceRows (1215 : Fin 2425) =
    MixedData.row1215 := by decide +kernel

theorem chunkSound75_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 75) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1200 ∨ k.val = 1201 ∨ k.val = 1202 ∨ k.val = 1203 ∨ k.val = 1204 ∨ k.val = 1205 ∨ k.val = 1206 ∨ k.val = 1207 ∨ k.val = 1208 ∨ k.val = 1209 ∨ k.val = 1210 ∨ k.val = 1211 ∨ k.val = 1212 ∨ k.val = 1213 ∨ k.val = 1214 ∨ k.val = 1215 := by omega
  rcases heq with h1200 | h1201 | h1202 | h1203 | h1204 | h1205 | h1206 | h1207 | h1208 | h1209 | h1210 | h1211 | h1212 | h1213 | h1214 | h1215
  · have he : k = (1200 : Fin 2425) := Fin.ext h1200
    subst k
    rw [sourceRowsAt1200]
    exact rowSound1200 B hB hF
  · have he : k = (1201 : Fin 2425) := Fin.ext h1201
    subst k
    rw [sourceRowsAt1201]
    exact rowSound1201 B hB hF
  · have he : k = (1202 : Fin 2425) := Fin.ext h1202
    subst k
    rw [sourceRowsAt1202]
    exact rowSound1202 B hB hF
  · have he : k = (1203 : Fin 2425) := Fin.ext h1203
    subst k
    rw [sourceRowsAt1203]
    exact rowSound1203 B hB hF
  · have he : k = (1204 : Fin 2425) := Fin.ext h1204
    subst k
    rw [sourceRowsAt1204]
    exact rowSound1204 B hB hF
  · have he : k = (1205 : Fin 2425) := Fin.ext h1205
    subst k
    rw [sourceRowsAt1205]
    exact rowSound1205 B hB hF
  · have he : k = (1206 : Fin 2425) := Fin.ext h1206
    subst k
    rw [sourceRowsAt1206]
    exact rowSound1206 B hB hF
  · have he : k = (1207 : Fin 2425) := Fin.ext h1207
    subst k
    rw [sourceRowsAt1207]
    exact rowSound1207 B hB hF
  · have he : k = (1208 : Fin 2425) := Fin.ext h1208
    subst k
    rw [sourceRowsAt1208]
    exact rowSound1208 B hB hF
  · have he : k = (1209 : Fin 2425) := Fin.ext h1209
    subst k
    rw [sourceRowsAt1209]
    exact rowSound1209 B hB hF
  · have he : k = (1210 : Fin 2425) := Fin.ext h1210
    subst k
    rw [sourceRowsAt1210]
    exact rowSound1210 B hB hF
  · have he : k = (1211 : Fin 2425) := Fin.ext h1211
    subst k
    rw [sourceRowsAt1211]
    exact rowSound1211 B hB hF
  · have he : k = (1212 : Fin 2425) := Fin.ext h1212
    subst k
    rw [sourceRowsAt1212]
    exact rowSound1212 B hB hF
  · have he : k = (1213 : Fin 2425) := Fin.ext h1213
    subst k
    rw [sourceRowsAt1213]
    exact rowSound1213 B hB hF
  · have he : k = (1214 : Fin 2425) := Fin.ext h1214
    subst k
    rw [sourceRowsAt1214]
    exact rowSound1214 B hB hF
  · have he : k = (1215 : Fin 2425) := Fin.ext h1215
    subst k
    rw [sourceRowsAt1215]
    exact rowSound1215 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound75_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound75_e_oai
