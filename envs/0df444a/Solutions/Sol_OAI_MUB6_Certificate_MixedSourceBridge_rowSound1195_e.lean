-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound1195_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T20:47:40.791197+00:00
-- url     : https://prove2.me/submissions/0edc9fdd-cece-4a71-8e4e-d00853f087c0

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E184
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
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

theorem canonical1280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1280 raw1280Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw1280 raw1280Labels = mixedMoment B raw1280step0 raw1280step0Labels := by
      have ha : raw1280step0 = (fun i j => raw1280 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1280step0 raw1280; decide +kernel
      have hl : raw1280step0Labels = raw1280Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1280 raw1280Labels permutation2 permutation6
    mixedMoment B raw1280step0 raw1280step0Labels = mixedMoment B raw1280step1 raw1280step1Labels := by
      have ha : raw1280step1 = -raw1280step0 := by apply Matrix.ext; change ∀ i j, raw1280step1 i j = -(raw1280step0 i j); unfold raw1280step1 raw1280step0; decide +kernel
      have hl : raw1280step1Labels = raw1280step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1280step1 raw1280step1Labels = mixedMoment B raw1280step2 raw1280step2Labels := by
      have ha : raw1280step2 = raw1280step1 := by apply Matrix.ext; unfold raw1280step2 raw1280step1; decide +kernel
      have hl : raw1280step1Labels = labelEmbedding1 ∘ raw1280step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1280step1 raw1280step1Labels raw1280step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1752 node1752Labels := by rfl

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

theorem canonical21771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21771 raw21771Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw21771 raw21771Labels = mixedMoment B raw21771step0 raw21771step0Labels := by
      have hz : ∀ j, raw21771 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21771step0 = (fun i j => raw21771 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21771step0 raw21771; decide +kernel
      have hl : raw21771step0Labels = raw21771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21771 raw21771Labels permutation434 hz
    mixedMoment B raw21771step0 raw21771step0Labels = mixedMoment B raw21771step1 raw21771step1Labels := by
      have hz : ∀ j, raw21771step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21771step1 = (fun i j => raw21771step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21771step1 raw21771step0; decide +kernel
      have hl : raw21771step1Labels = raw21771step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21771step0 raw21771step0Labels permutation80 hz
    _ = mixedMoment B node4841 node4841Labels := by rfl

theorem canonical21772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21772 raw21772Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw21772 raw21772Labels = mixedMoment B raw21772step0 raw21772step0Labels := by
      have hz : ∀ j, raw21772 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21772step0 = (fun i j => raw21772 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21772step0 raw21772; decide +kernel
      have hl : raw21772step0Labels = raw21772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21772 raw21772Labels permutation434 hz
    mixedMoment B raw21772step0 raw21772step0Labels = mixedMoment B raw21772step1 raw21772step1Labels := by
      have hz : ∀ j, raw21772step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21772step1 = (fun i j => raw21772step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21772step1 raw21772step0; decide +kernel
      have hl : raw21772step1Labels = raw21772step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21772step0 raw21772step0Labels permutation56 hz
    _ = mixedMoment B node4841 node4841Labels := by rfl

theorem canonical21773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21773 raw21773Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw21773 raw21773Labels = mixedMoment B raw21773step0 raw21773step0Labels := by
      have hz : ∀ j, raw21773 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21773step0 = (fun i j => raw21773 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21773step0 raw21773; decide +kernel
      have hl : raw21773step0Labels = raw21773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21773 raw21773Labels permutation346 hz
    mixedMoment B raw21773step0 raw21773step0Labels = mixedMoment B raw21773step1 raw21773step1Labels := by
      have hz : ∀ j, raw21773step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21773step1 = (fun i j => raw21773step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21773step1 raw21773step0; decide +kernel
      have hl : raw21773step1Labels = raw21773step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21773step0 raw21773step0Labels permutation56 hz
    _ = mixedMoment B node4841 node4841Labels := by rfl

theorem canonical21774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21774 raw21774Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw21774 raw21774Labels = mixedMoment B raw21774step0 raw21774step0Labels := by
      have hz : ∀ j, raw21774 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21774step0 = (fun i j => raw21774 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21774step0 raw21774; decide +kernel
      have hl : raw21774step0Labels = raw21774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21774 raw21774Labels permutation434 hz
    mixedMoment B raw21774step0 raw21774step0Labels = mixedMoment B raw21774step1 raw21774step1Labels := by
      have hz : ∀ j, raw21774step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21774step1 = (fun i j => raw21774step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21774step1 raw21774step0; decide +kernel
      have hl : raw21774step1Labels = raw21774step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21774step0 raw21774step0Labels permutation80 hz
    mixedMoment B raw21774step1 raw21774step1Labels = mixedMoment B raw21774step2 raw21774step2Labels := by
      have hz : ∀ j, raw21774step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21774step2 = (fun i j => raw21774step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21774step2 raw21774step1; decide +kernel
      have hl : raw21774step2Labels = raw21774step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21774step1 raw21774step1Labels permutation14 hz
    _ = mixedMoment B node4897 node4897Labels := by rfl

theorem canonical21775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21775 raw21775Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw21775 raw21775Labels = mixedMoment B raw21775step0 raw21775step0Labels := by
      have hz : ∀ j, raw21775 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21775step0 = (fun i j => raw21775 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21775step0 raw21775; decide +kernel
      have hl : raw21775step0Labels = raw21775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21775 raw21775Labels permutation434 hz
    mixedMoment B raw21775step0 raw21775step0Labels = mixedMoment B raw21775step1 raw21775step1Labels := by
      have hz : ∀ j, raw21775step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21775step1 = (fun i j => raw21775step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21775step1 raw21775step0; decide +kernel
      have hl : raw21775step1Labels = raw21775step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21775step0 raw21775step0Labels permutation80 hz
    mixedMoment B raw21775step1 raw21775step1Labels = mixedMoment B raw21775step2 raw21775step2Labels := by
      have hz : ∀ j, raw21775step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21775step2 = (fun i j => raw21775step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21775step2 raw21775step1; decide +kernel
      have hl : raw21775step2Labels = raw21775step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21775step1 raw21775step1Labels permutation14 hz
    mixedMoment B raw21775step2 raw21775step2Labels = mixedMoment B raw21775step3 raw21775step3Labels := by
      have hz : ∀ i, raw21775step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw21775step3 = (fun i j => raw21775step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw21775step3 raw21775step2; decide +kernel
      have hl : raw21775step3Labels = (fun j => raw21775step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw21775step2 raw21775step2Labels permutation4 hz
    mixedMoment B raw21775step3 raw21775step3Labels = mixedMoment B raw21775step4 raw21775step4Labels := by
      have ha : raw21775step4 = raw21775step3 := by apply Matrix.ext; unfold raw21775step4 raw21775step3; decide +kernel
      have hl : raw21775step3Labels = labelEmbedding2 ∘ raw21775step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21775step3 raw21775step3Labels raw21775step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical21776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21776 raw21776Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw21776 raw21776Labels = mixedMoment B raw21776step0 raw21776step0Labels := by
      have hz : ∀ j, raw21776 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21776step0 = (fun i j => raw21776 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21776step0 raw21776; decide +kernel
      have hl : raw21776step0Labels = raw21776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21776 raw21776Labels permutation434 hz
    mixedMoment B raw21776step0 raw21776step0Labels = mixedMoment B raw21776step1 raw21776step1Labels := by
      have hz : ∀ j, raw21776step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21776step1 = (fun i j => raw21776step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21776step1 raw21776step0; decide +kernel
      have hl : raw21776step1Labels = raw21776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21776step0 raw21776step0Labels permutation80 hz
    _ = mixedMoment B node4177 node4177Labels := by rfl

theorem canonical21777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21777 raw21777Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw21777 raw21777Labels = mixedMoment B raw21777step0 raw21777step0Labels := by
      have hz : ∀ j, raw21777 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21777step0 = (fun i j => raw21777 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21777step0 raw21777; decide +kernel
      have hl : raw21777step0Labels = raw21777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21777 raw21777Labels permutation434 hz
    mixedMoment B raw21777step0 raw21777step0Labels = mixedMoment B raw21777step1 raw21777step1Labels := by
      have ha : raw21777step1 = (fun i j => raw21777step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21777step1 raw21777step0; decide +kernel
      have hl : raw21777step1Labels = raw21777step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21777step0 raw21777step0Labels permutation38 permutation2
    _ = mixedMoment B node4346 node4346Labels := by rfl

theorem canonical21778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21778 raw21778Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw21778 raw21778Labels = mixedMoment B raw21778step0 raw21778step0Labels := by
      have hz : ∀ j, raw21778 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21778step0 = (fun i j => raw21778 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21778step0 raw21778; decide +kernel
      have hl : raw21778step0Labels = raw21778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21778 raw21778Labels permutation346 hz
    mixedMoment B raw21778step0 raw21778step0Labels = mixedMoment B raw21778step1 raw21778step1Labels := by
      have ha : raw21778step1 = (fun i j => raw21778step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21778step1 raw21778step0; decide +kernel
      have hl : raw21778step1Labels = raw21778step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21778step0 raw21778step0Labels permutation38 permutation2
    _ = mixedMoment B node4346 node4346Labels := by rfl

theorem canonical21779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21779 raw21779Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw21779 raw21779Labels = mixedMoment B raw21779step0 raw21779step0Labels := by
      have hz : ∀ j, raw21779 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21779step0 = (fun i j => raw21779 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21779step0 raw21779; decide +kernel
      have hl : raw21779step0Labels = raw21779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21779 raw21779Labels permutation434 hz
    mixedMoment B raw21779step0 raw21779step0Labels = mixedMoment B raw21779step1 raw21779step1Labels := by
      have hz : ∀ j, raw21779step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21779step1 = (fun i j => raw21779step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21779step1 raw21779step0; decide +kernel
      have hl : raw21779step1Labels = raw21779step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21779step0 raw21779step0Labels permutation80 hz
    mixedMoment B raw21779step1 raw21779step1Labels = mixedMoment B raw21779step2 raw21779step2Labels := by
      have ha : raw21779step2 = (fun i j => raw21779step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21779step2 raw21779step1; decide +kernel
      have hl : raw21779step2Labels = raw21779step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21779step1 raw21779step1Labels permutation10 permutation2
    _ = mixedMoment B node4460 node4460Labels := by rfl

theorem canonical21780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21780 raw21780Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw21780 raw21780Labels = mixedMoment B raw21780step0 raw21780step0Labels := by
      have hz : ∀ j, raw21780 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21780step0 = (fun i j => raw21780 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21780step0 raw21780; decide +kernel
      have hl : raw21780step0Labels = raw21780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21780 raw21780Labels permutation434 hz
    mixedMoment B raw21780step0 raw21780step0Labels = mixedMoment B raw21780step1 raw21780step1Labels := by
      have hz : ∀ j, raw21780step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21780step1 = (fun i j => raw21780step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21780step1 raw21780step0; decide +kernel
      have hl : raw21780step1Labels = raw21780step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21780step0 raw21780step0Labels permutation80 hz
    _ = mixedMoment B node4498 node4498Labels := by rfl

theorem canonical21781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21781 raw21781Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw21781 raw21781Labels = mixedMoment B raw21781step0 raw21781step0Labels := by
      have hz : ∀ j, raw21781 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21781step0 = (fun i j => raw21781 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21781step0 raw21781; decide +kernel
      have hl : raw21781step0Labels = raw21781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21781 raw21781Labels permutation434 hz
    mixedMoment B raw21781step0 raw21781step0Labels = mixedMoment B raw21781step1 raw21781step1Labels := by
      have hz : ∀ j, raw21781step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21781step1 = (fun i j => raw21781step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21781step1 raw21781step0; decide +kernel
      have hl : raw21781step1Labels = raw21781step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21781step0 raw21781step0Labels permutation56 hz
    _ = mixedMoment B node4177 node4177Labels := by rfl

theorem canonical21782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21782 raw21782Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw21782 raw21782Labels = mixedMoment B raw21782step0 raw21782step0Labels := by
      have hz : ∀ j, raw21782 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21782step0 = (fun i j => raw21782 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21782step0 raw21782; decide +kernel
      have hl : raw21782step0Labels = raw21782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21782 raw21782Labels permutation434 hz
    _ = mixedMoment B node4346 node4346Labels := by rfl

theorem canonical21783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21783 raw21783Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw21783 raw21783Labels = mixedMoment B raw21783step0 raw21783step0Labels := by
      have hz : ∀ j, raw21783 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21783step0 = (fun i j => raw21783 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21783step0 raw21783; decide +kernel
      have hl : raw21783step0Labels = raw21783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21783 raw21783Labels permutation265 hz
    mixedMoment B raw21783step0 raw21783step0Labels = mixedMoment B raw21783step1 raw21783step1Labels := by
      have ha : raw21783step1 = (fun i j => raw21783step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21783step1 raw21783step0; decide +kernel
      have hl : raw21783step1Labels = raw21783step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21783step0 raw21783step0Labels permutation38 permutation2
    _ = mixedMoment B node4346 node4346Labels := by rfl

theorem canonical21784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21784 raw21784Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw21784 raw21784Labels = mixedMoment B raw21784step0 raw21784step0Labels := by
      have hz : ∀ j, raw21784 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21784step0 = (fun i j => raw21784 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21784step0 raw21784; decide +kernel
      have hl : raw21784step0Labels = raw21784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21784 raw21784Labels permutation434 hz
    mixedMoment B raw21784step0 raw21784step0Labels = mixedMoment B raw21784step1 raw21784step1Labels := by
      have hz : ∀ j, raw21784step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21784step1 = (fun i j => raw21784step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21784step1 raw21784step0; decide +kernel
      have hl : raw21784step1Labels = raw21784step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21784step0 raw21784step0Labels permutation56 hz
    mixedMoment B raw21784step1 raw21784step1Labels = mixedMoment B raw21784step2 raw21784step2Labels := by
      have ha : raw21784step2 = (fun i j => raw21784step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21784step2 raw21784step1; decide +kernel
      have hl : raw21784step2Labels = raw21784step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21784step1 raw21784step1Labels permutation10 permutation2
    _ = mixedMoment B node4460 node4460Labels := by rfl

theorem canonical21785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21785 raw21785Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw21785 raw21785Labels = mixedMoment B raw21785step0 raw21785step0Labels := by
      have hz : ∀ j, raw21785 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21785step0 = (fun i j => raw21785 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21785step0 raw21785; decide +kernel
      have hl : raw21785step0Labels = raw21785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21785 raw21785Labels permutation434 hz
    mixedMoment B raw21785step0 raw21785step0Labels = mixedMoment B raw21785step1 raw21785step1Labels := by
      have hz : ∀ j, raw21785step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21785step1 = (fun i j => raw21785step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21785step1 raw21785step0; decide +kernel
      have hl : raw21785step1Labels = raw21785step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21785step0 raw21785step0Labels permutation56 hz
    _ = mixedMoment B node4498 node4498Labels := by rfl

theorem canonical21786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21786 raw21786Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw21786 raw21786Labels = mixedMoment B raw21786step0 raw21786step0Labels := by
      have hz : ∀ j, raw21786 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21786step0 = (fun i j => raw21786 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21786step0 raw21786; decide +kernel
      have hl : raw21786step0Labels = raw21786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21786 raw21786Labels permutation346 hz
    mixedMoment B raw21786step0 raw21786step0Labels = mixedMoment B raw21786step1 raw21786step1Labels := by
      have hz : ∀ j, raw21786step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21786step1 = (fun i j => raw21786step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21786step1 raw21786step0; decide +kernel
      have hl : raw21786step1Labels = raw21786step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21786step0 raw21786step0Labels permutation56 hz
    _ = mixedMoment B node4177 node4177Labels := by rfl

theorem canonical21787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21787 raw21787Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw21787 raw21787Labels = mixedMoment B raw21787step0 raw21787step0Labels := by
      have hz : ∀ j, raw21787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21787step0 = (fun i j => raw21787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21787step0 raw21787; decide +kernel
      have hl : raw21787step0Labels = raw21787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21787 raw21787Labels permutation346 hz
    _ = mixedMoment B node4346 node4346Labels := by rfl

theorem canonical21788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21788 raw21788Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw21788 raw21788Labels = mixedMoment B raw21788step0 raw21788step0Labels := by
      have hz : ∀ j, raw21788 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21788step0 = (fun i j => raw21788 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21788step0 raw21788; decide +kernel
      have hl : raw21788step0Labels = raw21788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21788 raw21788Labels permutation265 hz
    _ = mixedMoment B node4346 node4346Labels := by rfl

theorem canonical21789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21789 raw21789Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw21789 raw21789Labels = mixedMoment B raw21789step0 raw21789step0Labels := by
      have hz : ∀ j, raw21789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21789step0 = (fun i j => raw21789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21789step0 raw21789; decide +kernel
      have hl : raw21789step0Labels = raw21789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21789 raw21789Labels permutation346 hz
    mixedMoment B raw21789step0 raw21789step0Labels = mixedMoment B raw21789step1 raw21789step1Labels := by
      have hz : ∀ j, raw21789step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21789step1 = (fun i j => raw21789step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21789step1 raw21789step0; decide +kernel
      have hl : raw21789step1Labels = raw21789step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21789step0 raw21789step0Labels permutation56 hz
    mixedMoment B raw21789step1 raw21789step1Labels = mixedMoment B raw21789step2 raw21789step2Labels := by
      have ha : raw21789step2 = (fun i j => raw21789step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21789step2 raw21789step1; decide +kernel
      have hl : raw21789step2Labels = raw21789step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21789step1 raw21789step1Labels permutation10 permutation2
    _ = mixedMoment B node4460 node4460Labels := by rfl

theorem canonical21790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21790 raw21790Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw21790 raw21790Labels = mixedMoment B raw21790step0 raw21790step0Labels := by
      have hz : ∀ j, raw21790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21790step0 = (fun i j => raw21790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21790step0 raw21790; decide +kernel
      have hl : raw21790step0Labels = raw21790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21790 raw21790Labels permutation346 hz
    mixedMoment B raw21790step0 raw21790step0Labels = mixedMoment B raw21790step1 raw21790step1Labels := by
      have hz : ∀ j, raw21790step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21790step1 = (fun i j => raw21790step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21790step1 raw21790step0; decide +kernel
      have hl : raw21790step1Labels = raw21790step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21790step0 raw21790step0Labels permutation56 hz
    _ = mixedMoment B node4498 node4498Labels := by rfl

theorem canonical21791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21791 raw21791Labels = mixedMoment B node4191 node4191Labels := by
  calc
    mixedMoment B raw21791 raw21791Labels = mixedMoment B raw21791step0 raw21791step0Labels := by
      have hz : ∀ j, raw21791 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21791step0 = (fun i j => raw21791 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21791step0 raw21791; decide +kernel
      have hl : raw21791step0Labels = raw21791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21791 raw21791Labels permutation434 hz
    mixedMoment B raw21791step0 raw21791step0Labels = mixedMoment B raw21791step1 raw21791step1Labels := by
      have hz : ∀ j, raw21791step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21791step1 = (fun i j => raw21791step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21791step1 raw21791step0; decide +kernel
      have hl : raw21791step1Labels = raw21791step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21791step0 raw21791step0Labels permutation80 hz
    mixedMoment B raw21791step1 raw21791step1Labels = mixedMoment B raw21791step2 raw21791step2Labels := by
      have hz : ∀ j, raw21791step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21791step2 = (fun i j => raw21791step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21791step2 raw21791step1; decide +kernel
      have hl : raw21791step2Labels = raw21791step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21791step1 raw21791step1Labels permutation14 hz
    _ = mixedMoment B node4191 node4191Labels := by rfl

theorem canonical21792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21792 raw21792Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw21792 raw21792Labels = mixedMoment B raw21792step0 raw21792step0Labels := by
      have hz : ∀ j, raw21792 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21792step0 = (fun i j => raw21792 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21792step0 raw21792; decide +kernel
      have hl : raw21792step0Labels = raw21792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21792 raw21792Labels permutation434 hz
    mixedMoment B raw21792step0 raw21792step0Labels = mixedMoment B raw21792step1 raw21792step1Labels := by
      have hz : ∀ j, raw21792step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21792step1 = (fun i j => raw21792step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21792step1 raw21792step0; decide +kernel
      have hl : raw21792step1Labels = raw21792step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21792step0 raw21792step0Labels permutation80 hz
    _ = mixedMoment B node4360 node4360Labels := by rfl

theorem canonical21793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21793 raw21793Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw21793 raw21793Labels = mixedMoment B raw21793step0 raw21793step0Labels := by
      have hz : ∀ j, raw21793 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21793step0 = (fun i j => raw21793 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21793step0 raw21793; decide +kernel
      have hl : raw21793step0Labels = raw21793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21793 raw21793Labels permutation434 hz
    mixedMoment B raw21793step0 raw21793step0Labels = mixedMoment B raw21793step1 raw21793step1Labels := by
      have hz : ∀ j, raw21793step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21793step1 = (fun i j => raw21793step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21793step1 raw21793step0; decide +kernel
      have hl : raw21793step1Labels = raw21793step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21793step0 raw21793step0Labels permutation56 hz
    _ = mixedMoment B node4360 node4360Labels := by rfl

theorem canonical21794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21794 raw21794Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw21794 raw21794Labels = mixedMoment B raw21794step0 raw21794step0Labels := by
      have hz : ∀ j, raw21794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21794step0 = (fun i j => raw21794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21794step0 raw21794; decide +kernel
      have hl : raw21794step0Labels = raw21794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21794 raw21794Labels permutation346 hz
    mixedMoment B raw21794step0 raw21794step0Labels = mixedMoment B raw21794step1 raw21794step1Labels := by
      have hz : ∀ j, raw21794step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21794step1 = (fun i j => raw21794step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21794step1 raw21794step0; decide +kernel
      have hl : raw21794step1Labels = raw21794step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21794step0 raw21794step0Labels permutation56 hz
    _ = mixedMoment B node4360 node4360Labels := by rfl

theorem canonical21795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21795 raw21795Labels = mixedMoment B node4511 node4511Labels := by
  calc
    mixedMoment B raw21795 raw21795Labels = mixedMoment B raw21795step0 raw21795step0Labels := by
      have hz : ∀ j, raw21795 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21795step0 = (fun i j => raw21795 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21795step0 raw21795; decide +kernel
      have hl : raw21795step0Labels = raw21795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21795 raw21795Labels permutation434 hz
    mixedMoment B raw21795step0 raw21795step0Labels = mixedMoment B raw21795step1 raw21795step1Labels := by
      have hz : ∀ j, raw21795step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21795step1 = (fun i j => raw21795step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21795step1 raw21795step0; decide +kernel
      have hl : raw21795step1Labels = raw21795step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21795step0 raw21795step0Labels permutation80 hz
    mixedMoment B raw21795step1 raw21795step1Labels = mixedMoment B raw21795step2 raw21795step2Labels := by
      have hz : ∀ j, raw21795step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21795step2 = (fun i j => raw21795step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21795step2 raw21795step1; decide +kernel
      have hl : raw21795step2Labels = raw21795step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21795step1 raw21795step1Labels permutation14 hz
    _ = mixedMoment B node4511 node4511Labels := by rfl

theorem canonical21796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21796 raw21796Labels = mixedMoment B node4187 node4187Labels := by
  calc
    mixedMoment B raw21796 raw21796Labels = mixedMoment B raw21796step0 raw21796step0Labels := by
      have hz : ∀ j, raw21796 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21796step0 = (fun i j => raw21796 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21796step0 raw21796; decide +kernel
      have hl : raw21796step0Labels = raw21796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21796 raw21796Labels permutation434 hz
    mixedMoment B raw21796step0 raw21796step0Labels = mixedMoment B raw21796step1 raw21796step1Labels := by
      have hz : ∀ j, raw21796step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21796step1 = (fun i j => raw21796step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21796step1 raw21796step0; decide +kernel
      have hl : raw21796step1Labels = raw21796step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21796step0 raw21796step0Labels permutation80 hz
    mixedMoment B raw21796step1 raw21796step1Labels = mixedMoment B raw21796step2 raw21796step2Labels := by
      have hz : ∀ j, raw21796step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21796step2 = (fun i j => raw21796step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21796step2 raw21796step1; decide +kernel
      have hl : raw21796step2Labels = raw21796step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21796step1 raw21796step1Labels permutation14 hz
    _ = mixedMoment B node4187 node4187Labels := by rfl

theorem canonical21797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21797 raw21797Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw21797 raw21797Labels = mixedMoment B raw21797step0 raw21797step0Labels := by
      have hz : ∀ j, raw21797 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21797step0 = (fun i j => raw21797 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21797step0 raw21797; decide +kernel
      have hl : raw21797step0Labels = raw21797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21797 raw21797Labels permutation434 hz
    mixedMoment B raw21797step0 raw21797step0Labels = mixedMoment B raw21797step1 raw21797step1Labels := by
      have hz : ∀ j, raw21797step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21797step1 = (fun i j => raw21797step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21797step1 raw21797step0; decide +kernel
      have hl : raw21797step1Labels = raw21797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21797step0 raw21797step0Labels permutation80 hz
    _ = mixedMoment B node4356 node4356Labels := by rfl

theorem canonical21798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21798 raw21798Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw21798 raw21798Labels = mixedMoment B raw21798step0 raw21798step0Labels := by
      have hz : ∀ j, raw21798 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21798step0 = (fun i j => raw21798 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21798step0 raw21798; decide +kernel
      have hl : raw21798step0Labels = raw21798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21798 raw21798Labels permutation434 hz
    mixedMoment B raw21798step0 raw21798step0Labels = mixedMoment B raw21798step1 raw21798step1Labels := by
      have hz : ∀ j, raw21798step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21798step1 = (fun i j => raw21798step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21798step1 raw21798step0; decide +kernel
      have hl : raw21798step1Labels = raw21798step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21798step0 raw21798step0Labels permutation56 hz
    _ = mixedMoment B node4356 node4356Labels := by rfl

theorem canonical21799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21799 raw21799Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw21799 raw21799Labels = mixedMoment B raw21799step0 raw21799step0Labels := by
      have hz : ∀ j, raw21799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21799step0 = (fun i j => raw21799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21799step0 raw21799; decide +kernel
      have hl : raw21799step0Labels = raw21799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21799 raw21799Labels permutation346 hz
    mixedMoment B raw21799step0 raw21799step0Labels = mixedMoment B raw21799step1 raw21799step1Labels := by
      have hz : ∀ j, raw21799step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21799step1 = (fun i j => raw21799step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21799step1 raw21799step0; decide +kernel
      have hl : raw21799step1Labels = raw21799step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21799step0 raw21799step0Labels permutation56 hz
    _ = mixedMoment B node4356 node4356Labels := by rfl

theorem canonical21800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21800 raw21800Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw21800 raw21800Labels = mixedMoment B raw21800step0 raw21800step0Labels := by
      have hz : ∀ j, raw21800 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21800step0 = (fun i j => raw21800 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21800step0 raw21800; decide +kernel
      have hl : raw21800step0Labels = raw21800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21800 raw21800Labels permutation434 hz
    mixedMoment B raw21800step0 raw21800step0Labels = mixedMoment B raw21800step1 raw21800step1Labels := by
      have hz : ∀ j, raw21800step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21800step1 = (fun i j => raw21800step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21800step1 raw21800step0; decide +kernel
      have hl : raw21800step1Labels = raw21800step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21800step0 raw21800step0Labels permutation80 hz
    mixedMoment B raw21800step1 raw21800step1Labels = mixedMoment B raw21800step2 raw21800step2Labels := by
      have hz : ∀ j, raw21800step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21800step2 = (fun i j => raw21800step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21800step2 raw21800step1; decide +kernel
      have hl : raw21800step2Labels = raw21800step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21800step1 raw21800step1Labels permutation14 hz
    _ = mixedMoment B node4468 node4468Labels := by rfl

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

theorem canonical813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw813 raw813Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw813 raw813Labels = mixedMoment B raw813step0 raw813step0Labels := by
      have ha : raw813step0 = (fun i j => raw813 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw813step0 raw813; decide +kernel
      have hl : raw813step0Labels = raw813Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw813 raw813Labels permutation8 permutation4
    mixedMoment B raw813step0 raw813step0Labels = mixedMoment B raw813step1 raw813step1Labels := by
      have ha : raw813step1 = raw813step0 := by apply Matrix.ext; unfold raw813step1 raw813step0; decide +kernel
      have hl : raw813step0Labels = labelEmbedding7 ∘ raw813step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw813step0 raw813step0Labels raw813step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4177 node4177Labels := by rfl

theorem canonical814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw814 raw814Labels = mixedMoment B node605 node605Labels := by
  calc
    mixedMoment B raw814 raw814Labels = mixedMoment B raw814step0 raw814step0Labels := by
      have ha : raw814step0 = (fun i j => raw814 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw814step0 raw814; decide +kernel
      have hl : raw814step0Labels = raw814Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw814 raw814Labels permutation8 permutation4
    _ = mixedMoment B node605 node605Labels := by rfl

theorem canonical815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw815 raw815Labels = mixedMoment B node1518 node1518Labels := by
  calc
    mixedMoment B raw815 raw815Labels = mixedMoment B raw815step0 raw815step0Labels := by
      have ha : raw815step0 = (fun i j => raw815 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw815step0 raw815; decide +kernel
      have hl : raw815step0Labels = raw815Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw815 raw815Labels permutation8 permutation6
    mixedMoment B raw815step0 raw815step0Labels = mixedMoment B raw815step1 raw815step1Labels := by
      have ha : raw815step1 = -raw815step0 := by apply Matrix.ext; change ∀ i j, raw815step1 i j = -(raw815step0 i j); unfold raw815step1 raw815step0; decide +kernel
      have hl : raw815step1Labels = raw815step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw815step1 raw815step1Labels = mixedMoment B raw815step2 raw815step2Labels := by
      have ha : raw815step2 = raw815step1 := by apply Matrix.ext; unfold raw815step2 raw815step1; decide +kernel
      have hl : raw815step1Labels = labelEmbedding1 ∘ raw815step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw815step1 raw815step1Labels raw815step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1518 node1518Labels := by rfl

theorem canonical834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw834 raw834Labels = mixedMoment B node4187 node4187Labels := by
  calc
    mixedMoment B raw834 raw834Labels = mixedMoment B raw834step0 raw834step0Labels := by
      have ha : raw834step0 = (fun i j => raw834 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw834step0 raw834; decide +kernel
      have hl : raw834step0Labels = raw834Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw834 raw834Labels permutation2 permutation4
    mixedMoment B raw834step0 raw834step0Labels = mixedMoment B raw834step1 raw834step1Labels := by
      have ha : raw834step1 = raw834step0 := by apply Matrix.ext; unfold raw834step1 raw834step0; decide +kernel
      have hl : raw834step0Labels = labelEmbedding7 ∘ raw834step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw834step0 raw834step0Labels raw834step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4187 node4187Labels := by rfl

theorem canonical835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw835 raw835Labels = mixedMoment B node615 node615Labels := by
  calc
    mixedMoment B raw835 raw835Labels = mixedMoment B raw835step0 raw835step0Labels := by
      have ha : raw835step0 = (fun i j => raw835 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw835step0 raw835; decide +kernel
      have hl : raw835step0Labels = raw835Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw835 raw835Labels permutation2 permutation4
    _ = mixedMoment B node615 node615Labels := by rfl

theorem canonical836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw836 raw836Labels = mixedMoment B node1537 node1537Labels := by
  calc
    mixedMoment B raw836 raw836Labels = mixedMoment B raw836step0 raw836step0Labels := by
      have ha : raw836step0 = (fun i j => raw836 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw836step0 raw836; decide +kernel
      have hl : raw836step0Labels = raw836Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw836 raw836Labels permutation2 permutation6
    mixedMoment B raw836step0 raw836step0Labels = mixedMoment B raw836step1 raw836step1Labels := by
      have ha : raw836step1 = -raw836step0 := by apply Matrix.ext; change ∀ i j, raw836step1 i j = -(raw836step0 i j); unfold raw836step1 raw836step0; decide +kernel
      have hl : raw836step1Labels = raw836step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw836step1 raw836step1Labels = mixedMoment B raw836step2 raw836step2Labels := by
      have ha : raw836step2 = raw836step1 := by apply Matrix.ext; unfold raw836step2 raw836step1; decide +kernel
      have hl : raw836step1Labels = labelEmbedding1 ∘ raw836step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw836step1 raw836step1Labels raw836step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1537 node1537Labels := by rfl

theorem canonical840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw840 raw840Labels = mixedMoment B node4191 node4191Labels := by
  calc
    mixedMoment B raw840 raw840Labels = mixedMoment B raw840step0 raw840step0Labels := by
      have ha : raw840step0 = (fun i j => raw840 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw840step0 raw840; decide +kernel
      have hl : raw840step0Labels = raw840Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw840 raw840Labels permutation2 permutation4
    mixedMoment B raw840step0 raw840step0Labels = mixedMoment B raw840step1 raw840step1Labels := by
      have ha : raw840step1 = raw840step0 := by apply Matrix.ext; unfold raw840step1 raw840step0; decide +kernel
      have hl : raw840step0Labels = labelEmbedding7 ∘ raw840step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw840step0 raw840step0Labels raw840step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4191 node4191Labels := by rfl

theorem canonical841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw841 raw841Labels = mixedMoment B node619 node619Labels := by
  calc
    mixedMoment B raw841 raw841Labels = mixedMoment B raw841step0 raw841step0Labels := by
      have ha : raw841step0 = (fun i j => raw841 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw841step0 raw841; decide +kernel
      have hl : raw841step0Labels = raw841Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw841 raw841Labels permutation2 permutation4
    _ = mixedMoment B node619 node619Labels := by rfl

theorem canonical842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw842 raw842Labels = mixedMoment B node1538 node1538Labels := by
  calc
    mixedMoment B raw842 raw842Labels = mixedMoment B raw842step0 raw842step0Labels := by
      have ha : raw842step0 = (fun i j => raw842 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw842step0 raw842; decide +kernel
      have hl : raw842step0Labels = raw842Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw842 raw842Labels permutation2 permutation6
    mixedMoment B raw842step0 raw842step0Labels = mixedMoment B raw842step1 raw842step1Labels := by
      have ha : raw842step1 = -raw842step0 := by apply Matrix.ext; change ∀ i j, raw842step1 i j = -(raw842step0 i j); unfold raw842step1 raw842step0; decide +kernel
      have hl : raw842step1Labels = raw842step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw842step1 raw842step1Labels = mixedMoment B raw842step2 raw842step2Labels := by
      have ha : raw842step2 = raw842step1 := by apply Matrix.ext; unfold raw842step2 raw842step1; decide +kernel
      have hl : raw842step1Labels = labelEmbedding1 ∘ raw842step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw842step1 raw842step1Labels raw842step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1538 node1538Labels := by rfl

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

theorem canonical1152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1152 raw1152Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw1152 raw1152Labels = mixedMoment B raw1152step0 raw1152step0Labels := by
      have ha : raw1152step0 = (fun i j => raw1152 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1152step0 raw1152; decide +kernel
      have hl : raw1152step0Labels = raw1152Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1152 raw1152Labels permutation8 permutation4
    mixedMoment B raw1152step0 raw1152step0Labels = mixedMoment B raw1152step1 raw1152step1Labels := by
      have ha : raw1152step1 = raw1152step0 := by apply Matrix.ext; unfold raw1152step1 raw1152step0; decide +kernel
      have hl : raw1152step0Labels = labelEmbedding7 ∘ raw1152step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1152step0 raw1152step0Labels raw1152step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4356 node4356Labels := by rfl

theorem canonical1153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1153 raw1153Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw1153 raw1153Labels = mixedMoment B raw1153step0 raw1153step0Labels := by
      have ha : raw1153step0 = (fun i j => raw1153 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1153step0 raw1153; decide +kernel
      have hl : raw1153step0Labels = raw1153Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1153 raw1153Labels permutation8 permutation4
    _ = mixedMoment B node934 node934Labels := by rfl

theorem canonical1154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1154 raw1154Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw1154 raw1154Labels = mixedMoment B raw1154step0 raw1154step0Labels := by
      have ha : raw1154step0 = (fun i j => raw1154 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1154step0 raw1154; decide +kernel
      have hl : raw1154step0Labels = raw1154Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1154 raw1154Labels permutation8 permutation6
    mixedMoment B raw1154step0 raw1154step0Labels = mixedMoment B raw1154step1 raw1154step1Labels := by
      have ha : raw1154step1 = -raw1154step0 := by apply Matrix.ext; change ∀ i j, raw1154step1 i j = -(raw1154step0 i j); unfold raw1154step1 raw1154step0; decide +kernel
      have hl : raw1154step1Labels = raw1154step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1154step1 raw1154step1Labels = mixedMoment B raw1154step2 raw1154step2Labels := by
      have ha : raw1154step2 = raw1154step1 := by apply Matrix.ext; unfold raw1154step2 raw1154step1; decide +kernel
      have hl : raw1154step1Labels = labelEmbedding1 ∘ raw1154step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1154step1 raw1154step1Labels raw1154step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

theorem canonical1158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1158 raw1158Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw1158 raw1158Labels = mixedMoment B raw1158step0 raw1158step0Labels := by
      have ha : raw1158step0 = (fun i j => raw1158 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1158step0 raw1158; decide +kernel
      have hl : raw1158step0Labels = raw1158Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1158 raw1158Labels permutation8 permutation4
    mixedMoment B raw1158step0 raw1158step0Labels = mixedMoment B raw1158step1 raw1158step1Labels := by
      have ha : raw1158step1 = raw1158step0 := by apply Matrix.ext; unfold raw1158step1 raw1158step0; decide +kernel
      have hl : raw1158step0Labels = labelEmbedding7 ∘ raw1158step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1158step0 raw1158step0Labels raw1158step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4360 node4360Labels := by rfl

theorem canonical1159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1159 raw1159Labels = mixedMoment B node938 node938Labels := by
  calc
    mixedMoment B raw1159 raw1159Labels = mixedMoment B raw1159step0 raw1159step0Labels := by
      have ha : raw1159step0 = (fun i j => raw1159 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1159step0 raw1159; decide +kernel
      have hl : raw1159step0Labels = raw1159Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1159 raw1159Labels permutation8 permutation4
    _ = mixedMoment B node938 node938Labels := by rfl

theorem canonical1160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1160 raw1160Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw1160 raw1160Labels = mixedMoment B raw1160step0 raw1160step0Labels := by
      have ha : raw1160step0 = (fun i j => raw1160 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1160step0 raw1160; decide +kernel
      have hl : raw1160step0Labels = raw1160Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1160 raw1160Labels permutation8 permutation6
    mixedMoment B raw1160step0 raw1160step0Labels = mixedMoment B raw1160step1 raw1160step1Labels := by
      have ha : raw1160step1 = -raw1160step0 := by apply Matrix.ext; change ∀ i j, raw1160step1 i j = -(raw1160step0 i j); unfold raw1160step1 raw1160step0; decide +kernel
      have hl : raw1160step1Labels = raw1160step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1160step1 raw1160step1Labels = mixedMoment B raw1160step2 raw1160step2Labels := by
      have ha : raw1160step2 = raw1160step1 := by apply Matrix.ext; unfold raw1160step2 raw1160step1; decide +kernel
      have hl : raw1160step1Labels = labelEmbedding1 ∘ raw1160step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1160step1 raw1160step1Labels raw1160step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1693 node1693Labels := by rfl

theorem canonical1263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1263 raw1263Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw1263 raw1263Labels = mixedMoment B raw1263step0 raw1263step0Labels := by
      have ha : raw1263step0 = (fun i j => raw1263 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1263step0 raw1263; decide +kernel
      have hl : raw1263step0Labels = raw1263Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1263 raw1263Labels permutation8 permutation4
    mixedMoment B raw1263step0 raw1263step0Labels = mixedMoment B raw1263step1 raw1263step1Labels := by
      have ha : raw1263step1 = raw1263step0 := by apply Matrix.ext; unfold raw1263step1 raw1263step0; decide +kernel
      have hl : raw1263step0Labels = labelEmbedding7 ∘ raw1263step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1263step0 raw1263step0Labels raw1263step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

theorem canonical1264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1264 raw1264Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw1264 raw1264Labels = mixedMoment B raw1264step0 raw1264step0Labels := by
      have ha : raw1264step0 = (fun i j => raw1264 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1264step0 raw1264; decide +kernel
      have hl : raw1264step0Labels = raw1264Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1264 raw1264Labels permutation8 permutation4
    _ = mixedMoment B node1043 node1043Labels := by rfl

theorem canonical1265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1265 raw1265Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw1265 raw1265Labels = mixedMoment B raw1265step0 raw1265step0Labels := by
      have ha : raw1265step0 = (fun i j => raw1265 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1265step0 raw1265; decide +kernel
      have hl : raw1265step0Labels = raw1265Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1265 raw1265Labels permutation10 permutation6
    mixedMoment B raw1265step0 raw1265step0Labels = mixedMoment B raw1265step1 raw1265step1Labels := by
      have ha : raw1265step1 = -raw1265step0 := by apply Matrix.ext; change ∀ i j, raw1265step1 i j = -(raw1265step0 i j); unfold raw1265step1 raw1265step0; decide +kernel
      have hl : raw1265step1Labels = raw1265step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1265step1 raw1265step1Labels = mixedMoment B raw1265step2 raw1265step2Labels := by
      have ha : raw1265step2 = raw1265step1 := by apply Matrix.ext; unfold raw1265step2 raw1265step1; decide +kernel
      have hl : raw1265step1Labels = labelEmbedding1 ∘ raw1265step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1265step1 raw1265step1Labels raw1265step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical1278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1278 raw1278Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw1278 raw1278Labels = mixedMoment B raw1278step0 raw1278step0Labels := by
      have ha : raw1278step0 = (fun i j => raw1278 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1278step0 raw1278; decide +kernel
      have hl : raw1278step0Labels = raw1278Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1278 raw1278Labels permutation2 permutation4
    mixedMoment B raw1278step0 raw1278step0Labels = mixedMoment B raw1278step1 raw1278step1Labels := by
      have ha : raw1278step1 = raw1278step0 := by apply Matrix.ext; unfold raw1278step1 raw1278step0; decide +kernel
      have hl : raw1278step0Labels = labelEmbedding7 ∘ raw1278step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1278step0 raw1278step0Labels raw1278step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

theorem canonical1279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1279 raw1279Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw1279 raw1279Labels = mixedMoment B raw1279step0 raw1279step0Labels := by
      have ha : raw1279step0 = (fun i j => raw1279 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1279step0 raw1279; decide +kernel
      have hl : raw1279step0Labels = raw1279Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1279 raw1279Labels permutation2 permutation4
    _ = mixedMoment B node1051 node1051Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singleton4177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4177 node4177Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node605 node605Labels + mixedMoment B node1518 node1518Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw813 singletonSmall4177
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4177) = raw813Labels := by decide +kernel
  rw [hl, canonical813 B hB] at h
  have hc0 : mixedMoment B raw813 (Fin.cases (0 : Fin 2) singletonSmall4177) =
      mixedMoment B node605 node605Labels := by
    have ha : raw813 = raw814 := by apply Matrix.ext; unfold raw813 raw814; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4177 = raw814Labels := by decide +kernel
    rw [ha, hj, canonical814 B hB]
  have hc1 : mixedMoment B raw813 (Fin.cases (1 : Fin 2) singletonSmall4177) =
      mixedMoment B node1518 node1518Labels := by
    have ha : raw813 = raw815 := by apply Matrix.ext; unfold raw813 raw815; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4177 = raw815Labels := by decide +kernel
    rw [ha, hj, canonical815 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4187 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4187 node4187Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node615 node615Labels + mixedMoment B node1537 node1537Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw834 singletonSmall4187
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4187) = raw834Labels := by decide +kernel
  rw [hl, canonical834 B hB] at h
  have hc0 : mixedMoment B raw834 (Fin.cases (0 : Fin 2) singletonSmall4187) =
      mixedMoment B node615 node615Labels := by
    have ha : raw834 = raw835 := by apply Matrix.ext; unfold raw834 raw835; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4187 = raw835Labels := by decide +kernel
    rw [ha, hj, canonical835 B hB]
  have hc1 : mixedMoment B raw834 (Fin.cases (1 : Fin 2) singletonSmall4187) =
      mixedMoment B node1537 node1537Labels := by
    have ha : raw834 = raw836 := by apply Matrix.ext; unfold raw834 raw836; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4187 = raw836Labels := by decide +kernel
    rw [ha, hj, canonical836 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4191 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4191 node4191Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node619 node619Labels + mixedMoment B node1538 node1538Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw840 singletonSmall4191
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4191) = raw840Labels := by decide +kernel
  rw [hl, canonical840 B hB] at h
  have hc0 : mixedMoment B raw840 (Fin.cases (0 : Fin 2) singletonSmall4191) =
      mixedMoment B node619 node619Labels := by
    have ha : raw840 = raw841 := by apply Matrix.ext; unfold raw840 raw841; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4191 = raw841Labels := by decide +kernel
    rw [ha, hj, canonical841 B hB]
  have hc1 : mixedMoment B raw840 (Fin.cases (1 : Fin 2) singletonSmall4191) =
      mixedMoment B node1538 node1538Labels := by
    have ha : raw840 = raw842 := by apply Matrix.ext; unfold raw840 raw842; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4191 = raw842Labels := by decide +kernel
    rw [ha, hj, canonical842 B hB]
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

theorem singleton4356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4356 node4356Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node934 node934Labels + mixedMoment B node1692 node1692Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1152 singletonSmall4356
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4356) = raw1152Labels := by decide +kernel
  rw [hl, canonical1152 B hB] at h
  have hc0 : mixedMoment B raw1152 (Fin.cases (0 : Fin 2) singletonSmall4356) =
      mixedMoment B node934 node934Labels := by
    have ha : raw1152 = raw1153 := by apply Matrix.ext; unfold raw1152 raw1153; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4356 = raw1153Labels := by decide +kernel
    rw [ha, hj, canonical1153 B hB]
  have hc1 : mixedMoment B raw1152 (Fin.cases (1 : Fin 2) singletonSmall4356) =
      mixedMoment B node1692 node1692Labels := by
    have ha : raw1152 = raw1154 := by apply Matrix.ext; unfold raw1152 raw1154; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4356 = raw1154Labels := by decide +kernel
    rw [ha, hj, canonical1154 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4360 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4360 node4360Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node938 node938Labels + mixedMoment B node1693 node1693Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1158 singletonSmall4360
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4360) = raw1158Labels := by decide +kernel
  rw [hl, canonical1158 B hB] at h
  have hc0 : mixedMoment B raw1158 (Fin.cases (0 : Fin 2) singletonSmall4360) =
      mixedMoment B node938 node938Labels := by
    have ha : raw1158 = raw1159 := by apply Matrix.ext; unfold raw1158 raw1159; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4360 = raw1159Labels := by decide +kernel
    rw [ha, hj, canonical1159 B hB]
  have hc1 : mixedMoment B raw1158 (Fin.cases (1 : Fin 2) singletonSmall4360) =
      mixedMoment B node1693 node1693Labels := by
    have ha : raw1158 = raw1160 := by apply Matrix.ext; unfold raw1158 raw1160; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4360 = raw1160Labels := by decide +kernel
    rw [ha, hj, canonical1160 B hB]
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

theorem singleton4460 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4460 node4460Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1043 node1043Labels + mixedMoment B node1725 node1725Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1263 singletonSmall4460
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4460) = raw1263Labels := by decide +kernel
  rw [hl, canonical1263 B hB] at h
  have hc0 : mixedMoment B raw1263 (Fin.cases (0 : Fin 2) singletonSmall4460) =
      mixedMoment B node1043 node1043Labels := by
    have ha : raw1263 = raw1264 := by apply Matrix.ext; unfold raw1263 raw1264; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4460 = raw1264Labels := by decide +kernel
    rw [ha, hj, canonical1264 B hB]
  have hc1 : mixedMoment B raw1263 (Fin.cases (1 : Fin 2) singletonSmall4460) =
      mixedMoment B node1725 node1725Labels := by
    have ha : raw1263 = raw1265 := by apply Matrix.ext; unfold raw1263 raw1265; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4460 = raw1265Labels := by decide +kernel
    rw [ha, hj, canonical1265 B hB]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero] at h
  rw [hc0, hc1] at h
  exact h

theorem singleton4468 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node4468 node4468Labels =
      -(4 : ℝ)⁻¹ * (mixedMoment B node1051 node1051Labels + mixedMoment B node1752 node1752Labels) := by
  have h := singleton_first (by decide : 2 < 6) B hB raw1278 singletonSmall4468
    (by decide +kernel) (by decide +kernel)
  have hl : Fin.cases 0 (Fin.succ ∘ singletonSmall4468) = raw1278Labels := by decide +kernel
  rw [hl, canonical1278 B hB] at h
  have hc0 : mixedMoment B raw1278 (Fin.cases (0 : Fin 2) singletonSmall4468) =
      mixedMoment B node1051 node1051Labels := by
    have ha : raw1278 = raw1279 := by apply Matrix.ext; unfold raw1278 raw1279; decide +kernel
    have hj : Fin.cases (0 : Fin 2) singletonSmall4468 = raw1279Labels := by decide +kernel
    rw [ha, hj, canonical1279 B hB]
  have hc1 : mixedMoment B raw1278 (Fin.cases (1 : Fin 2) singletonSmall4468) =
      mixedMoment B node1752 node1752Labels := by
    have ha : raw1278 = raw1280 := by apply Matrix.ext; unfold raw1278 raw1280; decide +kernel
    have hj : Fin.cases (1 : Fin 2) singletonSmall4468 = raw1280Labels := by decide +kernel
    rw [ha, hj, canonical1280 B hB]
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

theorem sound924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node924 node924Labels = Sparse.eval nodeValue924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 924) = mixedMoment B node924 node924Labels := rfl
  simpa [nodeValue924, Sparse.eval] using hc.symm

theorem sound934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node934 node934Labels = Sparse.eval nodeValue934 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 934) = mixedMoment B node934 node934Labels := rfl
  simpa [nodeValue934, Sparse.eval] using hc.symm

theorem sound938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node938 node938Labels = Sparse.eval nodeValue938 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 938) = mixedMoment B node938 node938Labels := rfl
  simpa [nodeValue938, Sparse.eval] using hc.symm

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

theorem sound1043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1043 node1043Labels = Sparse.eval nodeValue1043 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1043) = mixedMoment B node1043 node1043Labels := rfl
  simpa [nodeValue1043, Sparse.eval] using hc.symm

theorem sound1051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1051 node1051Labels = Sparse.eval nodeValue1051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1051) = mixedMoment B node1051 node1051Labels := rfl
  simpa [nodeValue1051, Sparse.eval] using hc.symm

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

theorem sound1518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1518 node1518Labels = Sparse.eval nodeValue1518 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1518) = mixedMoment B node1518 node1518Labels := rfl
  simpa [nodeValue1518, Sparse.eval] using hc.symm

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

theorem sound1537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1537 node1537Labels = Sparse.eval nodeValue1537 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1537) = mixedMoment B node1537 node1537Labels := rfl
  simpa [nodeValue1537, Sparse.eval] using hc.symm

theorem sound1538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1538 node1538Labels = Sparse.eval nodeValue1538 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1538) = mixedMoment B node1538 node1538Labels := rfl
  simpa [nodeValue1538, Sparse.eval] using hc.symm

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

theorem sound1674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1674 node1674Labels = Sparse.eval nodeValue1674 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1674) = mixedMoment B node1674 node1674Labels := rfl
  simpa [nodeValue1674, Sparse.eval] using hc.symm

theorem sound1692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1692 node1692Labels = Sparse.eval nodeValue1692 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1692) = mixedMoment B node1692 node1692Labels := rfl
  simpa [nodeValue1692, Sparse.eval] using hc.symm

theorem sound1693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1693 node1693Labels = Sparse.eval nodeValue1693 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1693) = mixedMoment B node1693 node1693Labels := rfl
  simpa [nodeValue1693, Sparse.eval] using hc.symm

theorem sound1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1725 node1725Labels = Sparse.eval nodeValue1725 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1725) = mixedMoment B node1725 node1725Labels := rfl
  simpa [nodeValue1725, Sparse.eval] using hc.symm

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

theorem sound1752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1752 node1752Labels = Sparse.eval nodeValue1752 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1752) = mixedMoment B node1752 node1752Labels := rfl
  simpa [nodeValue1752, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node605 node605Labels = Sparse.eval nodeValue605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 605) = mixedMoment B node605 node605Labels := rfl
  simpa [nodeValue605, Sparse.eval] using hc.symm

theorem sound615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node615 node615Labels = Sparse.eval nodeValue615 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 615) = mixedMoment B node615 node615Labels := rfl
  simpa [nodeValue615, Sparse.eval] using hc.symm

theorem sound619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node619 node619Labels = Sparse.eval nodeValue619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 619) = mixedMoment B node619 node619Labels := rfl
  simpa [nodeValue619, Sparse.eval] using hc.symm

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

theorem sound4177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4177 node4177Labels = Sparse.eval nodeValue4177 (mixedVector B) := by
  have h := singleton4177 B _hB
  rw [sound605 B _hB _hF, sound1518 B _hB _hF] at h
  norm_num [nodeValue4177, nodeValue605, nodeValue1518, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4187 node4187Labels = Sparse.eval nodeValue4187 (mixedVector B) := by
  have h := singleton4187 B _hB
  rw [sound615 B _hB _hF, sound1537 B _hB _hF] at h
  norm_num [nodeValue4187, nodeValue615, nodeValue1537, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4191 node4191Labels = Sparse.eval nodeValue4191 (mixedVector B) := by
  have h := singleton4191 B _hB
  rw [sound619 B _hB _hF, sound1538 B _hB _hF] at h
  norm_num [nodeValue4191, nodeValue619, nodeValue1538, Sparse.eval] at h ⊢
  linarith only [h]

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

theorem sound4346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4346 node4346Labels = Sparse.eval nodeValue4346 (mixedVector B) := by
  have h := singleton4346 B _hB
  rw [sound924 B _hB _hF, sound1674 B _hB _hF] at h
  norm_num [nodeValue4346, nodeValue924, nodeValue1674, Sparse.eval] at h ⊢
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

theorem sound4356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4356 node4356Labels = Sparse.eval nodeValue4356 (mixedVector B) := by
  have h := singleton4356 B _hB
  rw [sound934 B _hB _hF, sound1692 B _hB _hF] at h
  norm_num [nodeValue4356, nodeValue934, nodeValue1692, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4360 node4360Labels = Sparse.eval nodeValue4360 (mixedVector B) := by
  have h := singleton4360 B _hB
  rw [sound938 B _hB _hF, sound1693 B _hB _hF] at h
  norm_num [nodeValue4360, nodeValue938, nodeValue1693, Sparse.eval] at h ⊢
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

theorem sound4460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4460 node4460Labels = Sparse.eval nodeValue4460 (mixedVector B) := by
  have h := singleton4460 B _hB
  rw [sound1043 B _hB _hF, sound1725 B _hB _hF] at h
  norm_num [nodeValue4460, nodeValue1043, nodeValue1725, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound4468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4468 node4468Labels = Sparse.eval nodeValue4468 (mixedVector B) := by
  have h := singleton4468 B _hB
  rw [sound1051 B _hB _hF, sound1752 B _hB _hF] at h
  norm_num [nodeValue4468, nodeValue1051, nodeValue1752, Sparse.eval] at h ⊢
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

theorem sound4498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4498 node4498Labels = Sparse.eval nodeValue4498 (mixedVector B) := by
  simpa only [nodeValue4498, Sparse.eval_nil] using zero4498 B _hB _hF

theorem sound4511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4511 node4511Labels = Sparse.eval nodeValue4511 (mixedVector B) := by
  simpa only [nodeValue4511, Sparse.eval_nil] using zero4511 B _hB _hF

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

theorem sound4841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4841 node4841Labels = Sparse.eval nodeValue4841 (mixedVector B) := by
  simpa only [nodeValue4841, Sparse.eval_nil] using zero4841 B _hB _hF

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

theorem zero4897 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4897 node4897Labels = 0 := by
  exact mixedMoment_order_one B hB node4897 node4897Labels 1
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

theorem sound4897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4897 node4897Labels = Sparse.eval nodeValue4897 (mixedVector B) := by
  simpa only [nodeValue4897, Sparse.eval_nil] using zero4897 B _hB _hF

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

theorem sourceEq1385 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1385 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1385 + difference 0 1) (sourceB1385 + difference 1 0) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA1385 + difference 0 1) (sourceB1385 + difference 1 0) sourceC1385) = raw21771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21771; decide +kernel
    rw [ha]
    exact (canonical21771 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1385 + difference 0 2) (sourceB1385 + difference 2 0) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA1385 + difference 0 2) (sourceB1385 + difference 2 0) sourceC1385) = raw21772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21772; decide +kernel
    rw [ha]
    exact (canonical21772 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1385 + difference 0 3) (sourceB1385 + difference 3 0) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA1385 + difference 0 3) (sourceB1385 + difference 3 0) sourceC1385) = raw21773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21773; decide +kernel
    rw [ha]
    exact (canonical21773 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1385 + difference 0 4) (sourceB1385 + difference 4 0) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA1385 + difference 0 4) (sourceB1385 + difference 4 0) sourceC1385) = raw21774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21774; decide +kernel
    rw [ha]
    exact (canonical21774 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1385 + difference 0 5) (sourceB1385 + difference 5 0) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1385 + difference 0 5) (sourceB1385 + difference 5 0) sourceC1385) = raw21775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21775; decide +kernel
    rw [ha]
    exact (canonical21775 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1385 + difference 1 0) (sourceB1385 + difference 0 1) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4177) := by
    have ha : (tripleCharges (sourceA1385 + difference 1 0) (sourceB1385 + difference 0 1) sourceC1385) = raw21776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21776; decide +kernel
    rw [ha]
    exact (canonical21776 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1385 + difference 1 2) (sourceB1385 + difference 2 1) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1385 + difference 1 2) (sourceB1385 + difference 2 1) sourceC1385) = raw21777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21777; decide +kernel
    rw [ha]
    exact (canonical21777 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1385 + difference 1 3) (sourceB1385 + difference 3 1) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1385 + difference 1 3) (sourceB1385 + difference 3 1) sourceC1385) = raw21778 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21778; decide +kernel
    rw [ha]
    exact (canonical21778 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1385 + difference 1 4) (sourceB1385 + difference 4 1) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1385 + difference 1 4) (sourceB1385 + difference 4 1) sourceC1385) = raw21779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21779; decide +kernel
    rw [ha]
    exact (canonical21779 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1385 + difference 1 5) (sourceB1385 + difference 5 1) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1385 + difference 1 5) (sourceB1385 + difference 5 1) sourceC1385) = raw21780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21780; decide +kernel
    rw [ha]
    exact (canonical21780 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1385 + difference 2 0) (sourceB1385 + difference 0 2) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4177) := by
    have ha : (tripleCharges (sourceA1385 + difference 2 0) (sourceB1385 + difference 0 2) sourceC1385) = raw21781 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21781; decide +kernel
    rw [ha]
    exact (canonical21781 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1385 + difference 2 1) (sourceB1385 + difference 1 2) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1385 + difference 2 1) (sourceB1385 + difference 1 2) sourceC1385) = raw21782 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21782; decide +kernel
    rw [ha]
    exact (canonical21782 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1385 + difference 2 3) (sourceB1385 + difference 3 2) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1385 + difference 2 3) (sourceB1385 + difference 3 2) sourceC1385) = raw21783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21783; decide +kernel
    rw [ha]
    exact (canonical21783 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1385 + difference 2 4) (sourceB1385 + difference 4 2) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1385 + difference 2 4) (sourceB1385 + difference 4 2) sourceC1385) = raw21784 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21784; decide +kernel
    rw [ha]
    exact (canonical21784 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1385 + difference 2 5) (sourceB1385 + difference 5 2) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1385 + difference 2 5) (sourceB1385 + difference 5 2) sourceC1385) = raw21785 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21785; decide +kernel
    rw [ha]
    exact (canonical21785 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1385 + difference 3 0) (sourceB1385 + difference 0 3) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4177) := by
    have ha : (tripleCharges (sourceA1385 + difference 3 0) (sourceB1385 + difference 0 3) sourceC1385) = raw21786 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21786; decide +kernel
    rw [ha]
    exact (canonical21786 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1385 + difference 3 1) (sourceB1385 + difference 1 3) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1385 + difference 3 1) (sourceB1385 + difference 1 3) sourceC1385) = raw21787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21787; decide +kernel
    rw [ha]
    exact (canonical21787 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1385 + difference 3 2) (sourceB1385 + difference 2 3) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1385 + difference 3 2) (sourceB1385 + difference 2 3) sourceC1385) = raw21788 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21788; decide +kernel
    rw [ha]
    exact (canonical21788 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1385 + difference 3 4) (sourceB1385 + difference 4 3) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1385 + difference 3 4) (sourceB1385 + difference 4 3) sourceC1385) = raw21789 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21789; decide +kernel
    rw [ha]
    exact (canonical21789 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1385 + difference 3 5) (sourceB1385 + difference 5 3) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1385 + difference 3 5) (sourceB1385 + difference 5 3) sourceC1385) = raw21790 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21790; decide +kernel
    rw [ha]
    exact (canonical21790 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1385 + difference 4 0) (sourceB1385 + difference 0 4) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4191) := by
    have ha : (tripleCharges (sourceA1385 + difference 4 0) (sourceB1385 + difference 0 4) sourceC1385) = raw21791 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21791; decide +kernel
    rw [ha]
    exact (canonical21791 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1385 + difference 4 1) (sourceB1385 + difference 1 4) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA1385 + difference 4 1) (sourceB1385 + difference 1 4) sourceC1385) = raw21792 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21792; decide +kernel
    rw [ha]
    exact (canonical21792 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1385 + difference 4 2) (sourceB1385 + difference 2 4) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA1385 + difference 4 2) (sourceB1385 + difference 2 4) sourceC1385) = raw21793 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21793; decide +kernel
    rw [ha]
    exact (canonical21793 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1385 + difference 4 3) (sourceB1385 + difference 3 4) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA1385 + difference 4 3) (sourceB1385 + difference 3 4) sourceC1385) = raw21794 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21794; decide +kernel
    rw [ha]
    exact (canonical21794 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1385 + difference 4 5) (sourceB1385 + difference 5 4) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1385 + difference 4 5) (sourceB1385 + difference 5 4) sourceC1385) = raw21795 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21795; decide +kernel
    rw [ha]
    exact (canonical21795 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1385 + difference 5 0) (sourceB1385 + difference 0 5) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4187) := by
    have ha : (tripleCharges (sourceA1385 + difference 5 0) (sourceB1385 + difference 0 5) sourceC1385) = raw21796 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21796; decide +kernel
    rw [ha]
    exact (canonical21796 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1385 + difference 5 1) (sourceB1385 + difference 1 5) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1385 + difference 5 1) (sourceB1385 + difference 1 5) sourceC1385) = raw21797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21797; decide +kernel
    rw [ha]
    exact (canonical21797 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1385 + difference 5 2) (sourceB1385 + difference 2 5) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1385 + difference 5 2) (sourceB1385 + difference 2 5) sourceC1385) = raw21798 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21798; decide +kernel
    rw [ha]
    exact (canonical21798 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1385 + difference 5 3) (sourceB1385 + difference 3 5) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1385 + difference 5 3) (sourceB1385 + difference 3 5) sourceC1385) = raw21799 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21799; decide +kernel
    rw [ha]
    exact (canonical21799 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1385 + difference 5 4) (sourceB1385 + difference 4 5) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1385 + difference 5 4) (sourceB1385 + difference 4 5) sourceC1385) = raw21800 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21800; decide +kernel
    rw [ha]
    exact (canonical21800 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1385 sourceB1385 sourceC1385
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1385, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1195 : Integer.Sparse.reindex keyMap MixedData.row1195 = numericRow1195 := by decide +kernel

theorem numericCheck1195 (x : Master → ℝ) : Integer.Sparse.eval numericRow1195 x =
    (4 : ℝ) * reducedSource1195 x := by
  norm_num [numericRow1195, reducedSource1195, Integer.Sparse.eval, Sparse.eval, nodeValue4084, nodeValue4177, nodeValue4187, nodeValue4191, nodeValue4346, nodeValue4356, nodeValue4360, nodeValue4460, nodeValue4468, nodeValue4498, nodeValue4511, nodeValue4841, nodeValue4897] <;> ring

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1195 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1195 (mixedVector B) = 0 := by
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4177 : mixedVector B (Sum.inr 4177) = Sparse.eval nodeValue4177 (mixedVector B) := by
    change mixedMoment B node4177 node4177Labels = _
    exact sound4177 B hB hF
  have h4187 : mixedVector B (Sum.inr 4187) = Sparse.eval nodeValue4187 (mixedVector B) := by
    change mixedMoment B node4187 node4187Labels = _
    exact sound4187 B hB hF
  have h4191 : mixedVector B (Sum.inr 4191) = Sparse.eval nodeValue4191 (mixedVector B) := by
    change mixedMoment B node4191 node4191Labels = _
    exact sound4191 B hB hF
  have h4346 : mixedVector B (Sum.inr 4346) = Sparse.eval nodeValue4346 (mixedVector B) := by
    change mixedMoment B node4346 node4346Labels = _
    exact sound4346 B hB hF
  have h4356 : mixedVector B (Sum.inr 4356) = Sparse.eval nodeValue4356 (mixedVector B) := by
    change mixedMoment B node4356 node4356Labels = _
    exact sound4356 B hB hF
  have h4360 : mixedVector B (Sum.inr 4360) = Sparse.eval nodeValue4360 (mixedVector B) := by
    change mixedMoment B node4360 node4360Labels = _
    exact sound4360 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4468 : mixedVector B (Sum.inr 4468) = Sparse.eval nodeValue4468 (mixedVector B) := by
    change mixedMoment B node4468 node4468Labels = _
    exact sound4468 B hB hF
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
  have h4511 : mixedVector B (Sum.inr 4511) = Sparse.eval nodeValue4511 (mixedVector B) := by
    change mixedMoment B node4511 node4511Labels = _
    exact sound4511 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  simpa only [sourceForm1385, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4084, h4177, h4187, h4191, h4346, h4356, h4360, h4460, h4468, h4498, h4511, h4841, h4897, reducedSource1195] using sourceEq1385 B hB

theorem rowSound1195_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1195 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1195, numericCheck1195, reducedZero1195 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1195_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound1195_e_oai
